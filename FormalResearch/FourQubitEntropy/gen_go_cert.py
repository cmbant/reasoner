#!/usr/bin/env python3
"""Generate the Lean data for the GO (global overlap) certificate probe.

Run from the repository root:

    python3 FormalResearch/FourQubitEntropy/gen_go_cert.py --all [--out DIR]          # GOConst + GOData_0..9
    python3 FormalResearch/FourQubitEntropy/gen_go_cert.py [--blocks A:B] [--out DIR] [--ref] [--suffix S]

Input (QIprojects, read only; set QIPROJECTS to its root, default /home/user/QIprojects):
  ResearchNotes/QI/four_qubit_entropy/code/data/m4_global_overlap.json
  ResearchNotes/QI/four_qubit_entropy/code/orbit_certificate_polynomials.py   (sympy)

Output (default DIR = FormalResearch/FourQubitEntropy/GOProbe), byte-reproducible:
  GOData<suffix>.lean  the blocks A:B as `GOProbe.dataBlocks<suffix> : List GBlock`, plus the constants
  GOConst.lean    the constraint matrices `GOProbe.cons` (sparse integer polynomials, packed keys),
                  the signed Reynolds table `GOProbe.orbitTable` and the expected target `GOProbe.expected`
  GORef.lean      (with --ref) the reference projections of the chosen blocks, computed in Python with the
                  semantics of `verify_m4_global_overlap.py`; used to time slices of the check.

Nothing here is trusted: a wrong literal makes the Lean check fail.  Monomial keys are the paper's base-eight
exponent digits (variable i at bits 3i); total degree <= 6 makes products carry free.
"""
import argparse
import json
import os
import sys
from fractions import Fraction as F
from itertools import combinations, permutations

ROOT = os.environ.get('QIPROJECTS', '/home/user/QIprojects')
CODE = os.path.join(ROOT, 'ResearchNotes/QI/four_qubit_entropy/code')
sys.path.insert(0, CODE)
from orbit_certificate_polynomials import (  # noqa: E402
    PR, XS, ZERO, X, Y, n, Q, h0, e, defects, height_hessian, lower_frame, CHARS)

N = 19


def pack(m):
    assert len(m) == N and sum(m) <= 6
    return sum(a << (3 * i) for i, a in enumerate(m))


def terms(poly):
    return {pack(tuple(m[:N])): F(int(c.numerator), int(c.denominator)) for m, c in poly.items()}


def lint(v):
    return f'Int.ofNat (nat_lit {v})' if v >= 0 else f'Int.negSucc (nat_lit {-v - 1})'


def lnat(v):
    return f'(nat_lit {v})'


CHUNK = 48


class Emit:
    """Collects helper definitions: long lists are split into chunks of CHUNK elements, which the
    elaborator needs (list literals of thousands of elements exceed `maxRecDepth`)."""

    def __init__(self, prefix):
        self.prefix, self.count, self.defs = prefix, 0, []

    def lst(self, items, ty, per=4):
        if len(items) <= CHUNK:
            rows = [', '.join(items[i:i + per]) for i in range(0, len(items), per)]
            return '[' + ',\n    '.join(rows) + ']'
        parts = []
        for i in range(0, len(items), CHUNK):
            parts.append(self.lst(items[i:i + CHUNK], ty, per))
        # combine in groups so that the `++` nesting stays shallow
        while len(parts) > 1:
            parts = [self.helper(' ++ '.join(parts[i:i + 8]), ty) for i in range(0, len(parts), 8)]
        return parts[0]

    def helper(self, expr, ty):
        name = f'{self.prefix}_{self.count}'
        self.count += 1
        self.defs.append(f'private def {name} : {ty} :=\n  {expr}\n')
        return name


def llist(items, per=6):
    rows = [', '.join(items[i:i + per]) for i in range(0, len(items), per)]
    return '[' + ',\n    '.join(rows) + ']'


# ---------------------------------------------------------------- constraints
def build_constraints(data):
    H = height_hessian()
    md = data['map_den'] * 36
    rays = []
    for real, imag in data['rays']:
        a, b = [[[PR(F(*v)) for v in row] for row in M] for M in (real, imag)]
        nn, qq, rr, ww, tt = defects(a, b)
        assert nn == 6 and qq == 0 and ww == 0 and tt == 0
        re = (3 * sum((a[i][j] * X[i][j] for i in range(4) for j in range(4)), ZERO)
              + sum((b[i][j] * Y[i][j] for i in range(4) for j in range(4)), ZERO))
        im = sum((a[i][j] * Y[i][j] - b[i][j] * X[i][j] for i in range(4) for j in range(4)), ZERO)
        rays.append((h0 * h0 - re * re - 3 * im * im) / 36)
    cons, order = {}, []
    for block in data['blocks']:
        key = json.dumps(block['constraint'])
        if key in cons:
            continue
        tag, *args = block['constraint']
        if tag == 'sos':
            M = [[PR.one]]
        elif tag == 'fidelity':
            M = [[rays[args[0]]]]
        elif tag == 'lead':
            M = [[h0 * XS[0] / 6]]
        elif tag == 'excess':
            M = [[e / 6]]
        elif tag == 'height':
            M = [[n * h0 * z / 216 for z in row] for row in H]
        elif tag == 'imaginary':
            M = [[n * h0 * Y[i][j] / 36 for j in range(1, 4)] for i in range(1, 4)]
        elif tag == 'height_quadratic':
            M = [[h0 * z / 216 for z in row] for row in H]
        elif tag == 'imaginary_quadratic':
            M = [[h0 * Y[i][j] / 36 for j in range(1, 4)] for i in range(1, 4)]
        elif tag == 'procrustes':
            K = [[3 * X[i][j] if (j == 0 if args[0] == 0 else i == 0) else Y[i][j]
                  for j in range(4)] for i in range(4)]
            M = [[h0 * z / 216 for z in row] for row in K]
        elif tag == 'fidelity_floor':
            sr = (3 * sum((z * z for row in X for z in row), ZERO)
                  - sum((z * z for row in Y for z in row), ZERO))
            si = 2 * sum((a * b for row, rr in zip(X, Y) for a, b in zip(row, rr)), ZERO)
            ell = h0 * h0 - n
            M = [[(ell + sr) / 36, si / 36], [si / 36, (ell - sr) / 108]]
        elif tag == 'lower_quadratic':
            a, b, c, s = args
            M = [[h0 * z / 216 for z in row] for row in lower_frame(a, b, PR(F(*c)), PR(F(*s)))]
        else:
            raise ValueError(tag)
        scaled = []
        for row in M:
            prow = []
            for z in row:
                ent = []
                for mono, coef in sorted(terms(z).items()):
                    coef *= F(md, 36)
                    assert coef.denominator == 1
                    if coef:
                        ent.append((mono, coef.numerator))
                prow.append(ent)
            scaled.append(prow)
        cons[key] = scaled
        order.append(key)
    return cons, order, md, rays


# ------------------------------------------------------------------ orbits
def build_acts():
    acts, pairs = [], list(combinations(range(3), 2))
    for pp in permutations(range(3)):
        mi, sg = list(range(N)), [1] * N
        for j in range(3):
            for offset in (1, 4, 13, 16):
                mi[offset + j] = offset + pp[j]
        for k, (i, j) in enumerate(pairs):
            ii, jj = pp[i], pp[j]
            kk = pairs.index(tuple(sorted((ii, jj))))
            mi[7 + k], mi[10 + k], sg[10 + k] = 7 + kk, 10 + kk, 1 if ii < jj else -1
        acts.append((mi, sg))
    return acts


ACTS = build_acts()


def transform(m, act):
    mi, sg = act
    out, sign = 0, 1
    for i in range(N):
        a = (m >> (3 * i)) & 7
        out += a << (3 * mi[i])
        if a & 1:
            sign *= sg[i]
    return out, sign


def orbit_of(m):
    """(rep, sign) or None, exactly as in verify_m4_global_overlap.py."""
    ch = 0
    for i, c in enumerate(CHARS):
        if (m >> (3 * i)) & 1:
            ch ^= c
    if ch:
        return None
    values = {}
    for act in ACTS:
        mm, sign = transform(m, act)
        if mm in values and values[mm] != sign:
            return None
        values[mm] = sign
    rep = min(values)
    return {mm: (rep, sign * values[rep]) for mm, sign in values.items()}


def monomials(deg):
    def rec(i, left):
        if i == N - 1:
            yield (left,)
            return
        for a in range(left + 1):
            for rest in rec(i + 1, left - a):
                yield (a,) + rest
    return rec(0, deg)


def orbit_table():
    table = {}
    for mono in monomials(6):
        m = pack(mono)
        if m in table:
            continue
        o = orbit_of(m)
        if o:
            table.update(o)
    return table


# ---------------------------------------------------------------- the blocks
def block_lean(em, block, cid, ncomp, cd, bits, grid):
    size = len(block['basis'])
    basis = []
    for row in block['basis']:
        atoms = []
        for comp, num, den, inds in row:
            mm = [0] * N
            for i in inds:
                mm[i] += 1
            assert 6 % den == 0
            atoms.append(f'({lnat(comp)}, {lnat(pack(tuple(mm)))}, {lint(num * (6 // den))})')
        basis.append(em.lst(atoms, 'List (Nat × Nat × Int)'))
    factor = [em.lst([lint(v) for v in row], 'List Int') for row in block['factor']]
    resid, offset = [], 0
    cor = {int(i): int(c) for i, c in block['corrections']}
    corcols = []
    for j in range(size):
        col = block['residual_upper'][offset:offset + j + 1]
        resid.append(em.lst([lint(v) for v in col], 'List Int'))
        cc = [(i, cor[offset + i]) for i in range(j + 1) if offset + i in cor]
        corcols.append(em.lst([f'({lnat(i)}, {lint(v)})' for i, v in cc], 'List (Nat × Int)'))
        offset += j + 1
    assert offset == len(block['residual_upper']) and len(cor) == len(block['corrections'])
    assert all(0 <= k < offset for k in cor)
    return (f'GBlock.mk {lnat(cid)} {lnat(ncomp)} {lnat(size)}\n'
            f'  {em.lst(basis, "List (List (Nat × Nat × Int))", 1)}\n'
            f'  {em.lst(factor, "List (List Int)", 1)}\n'
            f'  {em.lst(resid, "List (List Int)", 1)}\n'
            f'  {em.lst(corcols, "List (List (Nat × Int))", 1)}')


def reference(data, cons, order, md, sel):
    """Python reference (semantics of verify_m4_global_overlap.py) for the blocks `sel`."""
    grid, cd, bits = data['grid'], data['correction_den'], data['factor_bits']
    accum, caccum = {}, {}
    sq = 1 << (2 * bits)
    for bi in sel:
        block = data['blocks'][bi]
        size = len(block['basis'])
        factor = block['factor']
        M = cons[json.dumps(block['constraint'])]
        cor = {int(i): int(c) for i, c in block['corrections']}
        basis = []
        for row in block['basis']:
            parsed = []
            for comp, num, den, inds in row:
                mm = [0] * N
                for i in inds:
                    mm[i] += 1
                parsed.append((comp, pack(tuple(mm)), num * (6 // den)))
            basis.append(parsed)
        offset = 0
        for j in range(size):
            for i in range(j + 1):
                dot = sum(a * b for a, b in zip(factor[i], factor[j]))
                value = (grid * dot + sq // 2) // sq + block['residual_upper'][offset]
                correction = cor.get(offset, 0)
                offset += 1
                value *= 1 if i == j else 2
                correction *= 1 if i == j else 2
                for ai, a, ca in basis[i]:
                    for bj, b, cb in basis[j]:
                        for m, c in M[ai][bj]:
                            assert sum(((a + b + m) >> (3 * t)) & 7 for t in range(N)) == 6
                            o = ORB.get(a + b + m)
                            if o is None:
                                continue
                            rep, sign = o
                            coeff = sign * c * ca * cb
                            accum[rep] = accum.get(rep, 0) + value * coeff
                            if correction:
                                caccum[rep] = caccum.get(rep, 0) + correction * coeff
    return ({k: v for k, v in accum.items() if v}, {k: v for k, v in caccum.items() if v})


def expected_target(data, md):
    grid = data['grid']
    sqsum = sum((z * z for z in XS[7:19]), ZERO)
    differences = sum(((XS[i] - XS[j]) ** 2 + (XS[i + 3] - XS[j + 3]) ** 2
                       for i, j in combinations(range(1, 4), 2)), ZERO)
    floor_term = F(1, 10 ** 7) * n * h0 * h0 * (5 * sqsum + 2 * differences) / 27
    axial = [XS[12], -XS[11], XS[10]]
    Lstar = lower_frame(-1, -1, PR(F(-1, 2)), PR(F(1, 2)))
    axial_term = F(794424, 10 ** 12) * n * h0 * sum(
        (axial[i] * Lstar[i][j] * axial[j] for i in range(3) for j in range(3)), ZERO) / 216
    target = terms((Q - n * n * e) / 36 - floor_term - axial_term)
    expected = {}
    for m, c in target.items():
        if not c:
            continue
        rep, sign = ORB[m]
        coeff = c * md * grid
        assert coeff.denominator == 1
        expected[rep] = expected.get(rep, 0) + sign * coeff.numerator
    return {k: v for k, v in expected.items() if v}


def main():
    global ORB
    ap = argparse.ArgumentParser()
    ap.add_argument('--blocks', default='0:277')
    ap.add_argument('--out', default='FormalResearch/FourQubitEntropy/GOProbe')
    ap.add_argument('--all', action='store_true', help='GOConst.lean and GOData_0..9.lean (all 277 blocks)')
    ap.add_argument('--ref', action='store_true')
    ap.add_argument('--suffix', default='', help='GOData<suffix>.lean defines dataBlocks<suffix>')
    ap.add_argument('--skip-const', action='store_true')
    args = ap.parse_args()
    data = json.load(open(os.path.join(CODE, 'data/m4_global_overlap.json')))
    cons, order, md, rays = build_constraints(data)
    cid = {k: i for i, k in enumerate(order)}
    ORB = orbit_table()
    os.makedirs(args.out, exist_ok=True)
    grid, cd, bits = data['grid'], data['correction_den'], data['factor_bits']
    hdr = '-- GENERATED by gen_go_cert.py; do not edit.\n'
    ns0 = ('import FormalResearch.FourQubitEntropy.GOProbe.Core\n\n'
           'namespace FormalResearch.FourQubitEntropy.GOProbe\n\nset_option maxRecDepth 100000\n\n')
    ns1 = '\nend FormalResearch.FourQubitEntropy.GOProbe\n'

    def write(name, em, body):
        with open(os.path.join(args.out, name), 'w') as f:
            f.write(hdr + ns0 + '\n'.join(em.defs) + '\n' + body + ns1)

    if not args.skip_const:
        em = Emit('c')
        mats = []
        for key in order:
            rows = []
            for row in cons[key]:
                ents = [em.lst([f'({lnat(m)}, {lint(c)})' for m, c in ent], 'SP') for ent in row]
                rows.append(em.lst(ents, 'List SP', 1))
            mats.append(em.helper(em.lst(rows, 'List (List SP)', 1), 'List (List SP)'))
        body = ('/-- The constraint matrices `M_c`: sparse integer polynomials in packed keys, scaled by\n'
                '`mapDen/36`. -/\ndef cons : List (List (List SP)) :=\n  ' + em.lst(mats, 'List (List (List SP))', 1) + '\n\n')
        items = [f'({lnat(m)}, {lnat(r)}, {lint(sg)})' for m, (r, sg) in sorted(ORB.items())]
        body += ('/-- Signed Reynolds table `(monomial, (orbit representative, sign))`, sorted by monomial, for the\n'
                 'degree-six monomials with trivial character and consistent signs. -/\n'
                 'def orbitTable : List (Nat × Nat × Int) :=\n  '
                 + em.lst(items, 'List (Nat × Nat × Int)', 3) + '\n\n')
        exp = expected_target(data, md)
        items = [f'({lnat(m)}, {lint(c)})' for m, c in sorted(exp.items())]
        body += ('/-- The expected projected target `(Q - n^2 e)/36 - R_sq - R_ax` times `mapDen * grid`. -/\n'
                 'def expected : SP :=\n  ' + em.lst(items, 'SP', 4) + '\n\n')
        body += (f'def gridC : Nat := {grid}\ndef corrDen : Nat := {cd}\ndef factorBits : Nat := {bits}\n'
                 f'def mapDen : Nat := {md}\n')
        write('GOConst.lean', em, body)
        print('const:', len(order), 'constraints', len(ORB), 'orbit-table entries', len(exp), 'expected keys')

    CUTS = [0, 3, 6, 8, 50, 90, 130, 170, 210, 250, 277]
    parts = ([(f'{a}:{b}', f'_{i}') for i, (a, b) in enumerate(zip(CUTS, CUTS[1:]))] if args.all
             else [(args.blocks, args.suffix)])
    for rng, suffix in parts:
        lo, hi = map(int, rng.split(':'))
        sel = list(range(lo, hi))
        em = Emit('d')
        bl = []
        for bi in sel:
            b = data['blocks'][bi]
            k = cid[json.dumps(b['constraint'])]
            bl.append(em.helper(block_lean(em, b, k, len(cons[json.dumps(b['constraint'])]), cd, bits, grid),
                                'GBlock'))
        body = (f'/-- Blocks {lo}:{hi} of the certificate. -/\ndef dataBlocks{suffix} : List GBlock :=\n  '
                + em.lst(bl, 'List GBlock', 1) + '\n')
        write(f'GOData{suffix}.lean', em, body)
    if args.ref and not args.all:
        base, corr = reference(data, cons, order, md, sel)
        em = Emit('r')
        body = ''
        for name, d in (('refBase', base), ('refCorr', corr)):
            items = [f'({lnat(m)}, {lint(c)})' for m, c in sorted(d.items())]
            body += f'def {name} : SP :=\n  ' + em.lst(items, 'SP', 4) + '\n\n'
        write('GORef.lean', em, body)
        print('ref:', len(base), len(corr))


if __name__ == '__main__':
    main()
