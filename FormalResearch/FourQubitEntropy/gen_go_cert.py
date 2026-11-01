#!/usr/bin/env python3
"""Generate the Lean data of the GO (global overlap) certificate.

Run from the repository root:

    python3 FormalResearch/FourQubitEntropy/gen_go_cert.py [--out DIR] [--part-bytes N]

Input (QIprojects, read only; set QIPROJECTS to its root, default /home/user/QIprojects):
  ResearchNotes/QI/four_qubit_entropy/code/data/m4_global_overlap.json
  ResearchNotes/QI/four_qubit_entropy/code/orbit_certificate_polynomials.py   (sympy)

Output (default DIR = FormalResearch/FourQubitEntropy/GOData), byte-reproducible, not committed:
  GOConst.lean     `cons` (the 64 constraint matrices M_c, sparse integer polynomials in packed keys, scaled
                   by map_den), `acts` (the 48 signed coordinate maps: 6 permutations of the lower indices
                   with their signs times the 8 sign changes of the lower coordinates), `lit` (the target
                   polynomial (Q - n^2 e)/36 - R_sq - R_ax times map_den*36*grid, an integer polynomial) and
                   the constants gridC, corrDen, factorBits
  GOData_<k>.lean  consecutive blocks, `dataBlocks_<k> : List GBlock`, each at most --part-bytes of text so
                   that elaboration stays below about 4 GB
  GOAll.lean       imports everything and defines `allBlocks`

Nothing here is trusted: the Lean `check` recomputes everything from this data, so a wrong literal makes
`check` false.  Monomial keys are base-256 exponent digits (variable i is digit i); the Lean checker verifies
that all degrees are far below 255, so products are carry free.
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
    return sum(a << (8 * i) for i, a in enumerate(m))


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


def acts_list():
    """The 48 signed coordinate maps `x_i -> sg_i x_{mi i}`: permutation part times the sign changes."""
    out = []
    for mi, sg in ACTS:
        for d in range(8):
            flip = [-1 if bin(d & CHARS[i]).count('1') % 2 else 1 for i in range(N)]
            out.append((list(mi), [a * b for a, b in zip(sg, flip)]))
    assert len({(tuple(a), tuple(b)) for a, b in out}) == 48
    return out


def lit_target(data, md):
    """`(Q - n^2 e)/36 - R_sq - R_ax` times `md * grid` (integer coefficients), sorted by key."""
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
    lit = {}
    for m, c in target.items():
        c = c * md * grid
        assert c.denominator == 1
        if c:
            lit[m] = c.numerator
    return sorted(lit.items())


def block_expr(em, block, cid):
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
    return (f'GBlock.mk {lnat(cid)}\n'
            f'  {em.lst(basis, "List (List (Nat × Nat × Int))", 1)}\n'
            f'  {em.lst(factor, "List (List Int)", 1)}\n'
            f'  {em.lst(resid, "List (List Int)", 1)}\n'
            f'  {em.lst(corcols, "List (List (Nat × Int))", 1)}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default='FormalResearch/FourQubitEntropy/GOData')
    ap.add_argument('--part-bytes', type=int, default=1800000)
    args = ap.parse_args()
    data = json.load(open(os.path.join(CODE, 'data/m4_global_overlap.json')))
    cons, order, md, rays = build_constraints(data)
    cid = {k: i for i, k in enumerate(order)}
    os.makedirs(args.out, exist_ok=True)
    grid, cd, bits = data['grid'], data['correction_den'], data['factor_bits']
    hdr = '-- GENERATED by gen_go_cert.py; do not edit.\n'
    ns0 = ('import FormalResearch.FourQubitEntropy.GOProbe.Block\n\n'
           'namespace FormalResearch.FourQubitEntropy.GOProbe\n\nset_option maxRecDepth 100000\n\n')
    ns1 = '\nend FormalResearch.FourQubitEntropy.GOProbe\n'

    def write(name, text, imports=None):
        with open(os.path.join(args.out, name), 'w') as f:
            f.write(hdr + (imports or ns0) + text + ns1)

    # constants
    em = Emit('c')
    mats = []
    for key in order:
        rows = []
        for row in cons[key]:
            ents = [em.lst([f'({lnat(m)}, {lint(c)})' for m, c in ent], 'SP') for ent in row]
            rows.append(em.lst(ents, 'List SP', 1))
        mats.append(em.helper(em.lst(rows, 'List (List SP)', 1), 'List (List SP)'))
    body = ('/-- The constraint matrices `M_c`: sparse integer polynomials in packed keys, scaled by the map\n'
            'denominator. -/\ndef cons : List (List (List SP)) :=\n  '
            + em.lst(mats, 'List (List (List SP))', 1) + '\n\n')
    acts = acts_list()
    items = ['(' + '[' + ', '.join(lnat(v) for v in mi) + '], [' + ', '.join(lint(v) for v in sg) + '])'
             for mi, sg in acts]
    body += ('/-- The 48 signed coordinate maps `x_i -> sg_i x_{mi i}` (lower signed permutations). -/\n'
             'def acts : List (List Nat × List Int) :=\n  ' + em.lst(items, 'List (List Nat × List Int)', 1) + '\n\n')
    lit = lit_target(data, md)
    items = [f'({lnat(m)}, {lint(c)})' for m, c in lit]
    body += ('/-- The target `(Q - n^2 e)/36 - R_sq - R_ax` times `mapDen * 36 * grid`. -/\n'
             'def lit : SP :=\n  ' + em.lst(items, 'SP', 4) + '\n\n')
    body += (f'def gridC : Nat := {grid}\ndef corrDen : Nat := {cd}\ndef factorBits : Nat := {bits}\n'
             f'def mapDen : Nat := {md}\n')
    write('GOConst.lean', '\n'.join(em.defs) + '\n' + body)
    print('const:', len(order), 'constraints', len(acts), 'acts', len(lit), 'lit terms')

    # blocks, packed into parts of bounded text size
    parts, cur, cur_len = [], [], 0
    for bi, b in enumerate(data['blocks']):
        em = Emit(f'b{bi}')
        name = em.helper(block_expr(em, b, cid[json.dumps(b['constraint'])]), 'GBlock')
        text = '\n'.join(em.defs)
        if cur and cur_len + len(text) > args.part_bytes:
            parts.append(cur)
            cur, cur_len = [], 0
        cur.append((name, text))
        cur_len += len(text)
    parts.append(cur)
    for k, part in enumerate(parts):
        em = Emit('l')
        lst = em.lst([nm for nm, _ in part], 'List GBlock', 1)
        write(f'GOData_{k}.lean', '\n'.join(t for _, t in part) + '\n' + '\n'.join(em.defs) + '\n'
              + f'def dataBlocks_{k} : List GBlock :=\n  {lst}\n')
    imps = ('import FormalResearch.FourQubitEntropy.GOData.GOConst\n'
            + ''.join(f'import FormalResearch.FourQubitEntropy.GOData.GOData_{k}\n' for k in range(len(parts)))
            + '\nnamespace FormalResearch.FourQubitEntropy.GOProbe\n\n')
    allb = ' ++ '.join(f'dataBlocks_{k}' for k in range(len(parts)))
    write('GOAll.lean', f'/-- All {len(data["blocks"])} blocks. -/\ndef allBlocks : List GBlock :=\n  {allb}\n',
          imports=imps)
    print('parts:', len(parts), [len(p) for p in parts])


if __name__ == '__main__':
    main()
