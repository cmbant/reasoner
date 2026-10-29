#!/usr/bin/env python3
"""Generate the `IdentityCert*.lean` files: the normal forms of the pieces of the sextic defect.

Run from the repository root:  python3 FormalResearch/FourQubitEntropy/gen_sextic_certificate.py

The pieces `F`, `n W₁`, `pairSum` and the four `resNorm0` terms of
`sexticDefect zSP wSP` (see `Generic.lean`) are expanded here, by a direct transcription of the
Lean definitions over integer-coefficient polynomials, into the sparse prime-key normal form of
`SparsePoly.lean`: a list of `(monomial key, coefficient)` sorted by key, where the key of a
monomial is the product of the primes of its variables (variable `i` has the `i`-th prime;
`z_{abcd}` is variable `8a+4b+2c+d`, `w_{abcd}` is variable `16 +` that).

The Lean kernel then checks `piece = literal` for each (one declaration per file) and that the
combination is zero. Nothing here is trusted: a wrong literal makes the kernel check fail.
The script also asserts that the combination vanishes in Python.
"""
import itertools, os, sys

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
          59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131]


class P:
    """Polynomial: dict from sorted tuple of variable indices to integer coefficient."""
    __slots__ = ['d']

    def __init__(s, d):
        s.d = d

    def __add__(s, o):
        r = dict(s.d)
        for k, v in o.d.items():
            r[k] = r.get(k, 0) + v
            if r[k] == 0:
                del r[k]
        return P(r)

    def __neg__(s):
        return P({k: -v for k, v in s.d.items()})

    def __sub__(s, o):
        return s + (-o)

    def __mul__(s, o):
        r = {}
        for k1, v1 in s.d.items():
            for k2, v2 in o.d.items():
                k = tuple(sorted(k1 + k2))
                r[k] = r.get(k, 0) + v1 * v2
        return P({k: v for k, v in r.items() if v})


def lit(k):
    return P({(): k}) if k else P({})


def vi(a, b, c, d):
    return 8 * a + 4 * b + 2 * c + d


z = {(a, b, c, d): P({(vi(a, b, c, d),): 1}) for a, b, c, d in itertools.product(range(2), repeat=4)}
w = {(a, b, c, d): P({(16 + vi(a, b, c, d),): 1}) for a, b, c, d in itertools.product(range(2), repeat=4)}
zz = lambda a, b, c, d: z[(a, b, c, d)]
ww = lambda a, b, c, d: w[(a, b, c, d)]


def sum2(f):
    return f(0) + f(1)


def sum4(f):
    return sum2(lambda a: sum2(lambda b: sum2(lambda c: sum2(lambda d: f(a, b, c, d)))))


def normG(z, w):
    return sum4(lambda a, b, c, d: z(a, b, c, d) * w(a, b, c, d))


def marg12(z, w):
    return lambda a, b, a2, b2: sum2(lambda c: sum2(lambda d: z(a, b, c, d) * w(a2, b2, c, d)))


def marg13(z, w):
    return lambda a, c, a2, c2: sum2(lambda b: sum2(lambda d: z(a, b, c, d) * w(a2, b, c2, d)))


def marg14(z, w):
    return lambda a, d, a2, d2: sum2(lambda b: sum2(lambda c: z(a, b, c, d) * w(a2, b, c, d2)))


def memo(M):
    c = {}

    def f(*k):
        if k not in c:
            c[k] = M(*k)
        return c[k]
    return f


def tr2(M):
    return sum2(lambda a: sum2(lambda b: sum2(lambda a2: sum2(lambda b2: M(a, b, a2, b2) * M(a2, b2, a, b)))))


def tr3(M):
    return sum2(lambda a: sum2(lambda b: sum2(lambda a2: sum2(lambda b2: sum2(lambda a3: sum2(
        lambda b3: M(a, b, a2, b2) * M(a2, b2, a3, b3) * M(a3, b3, a, b)))))))


def siteSwap(i, z):
    return [z, lambda a, b, c, d: z(b, a, c, d), lambda a, b, c, d: z(c, b, a, d),
            lambda a, b, c, d: z(d, b, c, a)][i]


def rho0(z, w):
    return memo(lambda a, a2: sum2(lambda b: sum2(lambda c: sum2(lambda d: z(a, b, c, d) * w(a2, b, c, d)))))


def trRho2(z, w):
    r = rho0(z, w)
    return sum2(lambda a: sum2(lambda a2: r(a, a2) * r(a2, a)))


n = normG(zz, ww)


def Fgen():
    M = [memo(m(zz, ww)) for m in (marg12, marg13, marg14)]
    P_ = tr2(M[0]) + tr2(M[1]) + tr2(M[2])
    T = tr3(M[0]) + tr3(M[1]) + tr3(M[2])
    return lit(17) * n * P_ - lit(12) * T - lit(12) * n * n * n


def W1():
    s = P({})
    for i in range(4):
        s = s + (lit(2) * trRho2(siteSwap(i, zz), siteSwap(i, ww)) - n * n)
    return s


def sgn(t):
    return 1 if t == 0 else -1


def ztil(w):
    return lambda t0, t1, t2, t3: lit(sgn(t0) * sgn(t1) * sgn(t2) * sgn(t3)) * w(1 - t0, 1 - t1, 1 - t2, 1 - t3)


def epsSum(f):
    return f(0, 1) - f(1, 0)


def resRaw(L, z, w, x0, y0, t0, o1, o2, o3):
    pick = lambda c, o, a: o if c == 0 else a
    cs = [(0, 0, 0)] if L else list(itertools.product(range(2), repeat=3))
    zt = ztil(w)
    acc = lit(0)
    for c in reversed(cs):
        acc = epsSum(lambda a1, t1: epsSum(lambda a2, t2: epsSum(lambda a3, t3:
            z(x0, pick(c[0], o1, a1), pick(c[1], o2, a2), pick(c[2], o3, a3))
            * z(y0, pick(1 - c[0], o1, a1), pick(1 - c[1], o2, a2), pick(1 - c[2], o3, a3))
            * zt(t0, t1, t2, t3)))) + acc
    return acc


def resSym(L, z, w, x, y, t, o1, o2, o3):
    return (resRaw(L, z, w, x, y, t, o1, o2, o3) + resRaw(L, z, w, x, t, y, o1, o2, o3)
            + resRaw(L, z, w, y, x, t, o1, o2, o3) + resRaw(L, z, w, y, t, x, o1, o2, o3)
            + resRaw(L, z, w, t, x, y, o1, o2, o3) + resRaw(L, z, w, t, y, x, o1, o2, o3))


def resTensor(z, w, *a):
    return resSym(False, z, w, *a) - lit(8) * resSym(True, z, w, *a)


def resSlot(z, w, x, y, t):
    return sum2(lambda o1: sum2(lambda o2: sum2(lambda o3:
        resTensor(z, w, x, y, t, o1, o2, o3) * resTensor(w, z, x, y, t, o1, o2, o3))))


def resNorm0(z, w):
    return (resSlot(z, w, 0, 0, 0) + lit(3) * resSlot(z, w, 0, 0, 1)
            + lit(3) * resSlot(z, w, 0, 1, 1) + resSlot(z, w, 1, 1, 1))


def actSite(s, z, w):
    r = rho0(siteSwap(s, z), siteSwap(s, w))
    if s == 0:
        return lambda a, b, c, d: sum2(lambda t: r(a, t) * z(t, b, c, d))
    if s == 1:
        return lambda a, b, c, d: sum2(lambda t: r(b, t) * z(a, t, c, d))
    if s == 2:
        return lambda a, b, c, d: sum2(lambda t: r(c, t) * z(a, b, t, d))
    return lambda a, b, c, d: sum2(lambda t: r(d, t) * z(a, b, c, t))


def pairNorm(i, j, z, w):
    ai, aj, bi, bj = actSite(i, z, w), actSite(j, z, w), actSite(i, w, z), actSite(j, w, z)
    return sum4(lambda a, b, c, d: (ai(a, b, c, d) - aj(a, b, c, d)) * (bi(a, b, c, d) - bj(a, b, c, d)))


def normal_form(p):
    out = []
    for m, c in p.d.items():
        k = 1
        for v in m:
            k *= PRIMES[v]
        out.append((k, c))
    out.sort()
    assert len({k for k, _ in out}) == len(out)
    return out


CHUNK = 64


def int_lit(c):
    """An `Int` as a raw constructor application: no instance resolution when elaborating, and the
    shortest term for the kernel."""
    return f'Int.ofNat (nat_lit {c})' if c >= 0 else f'Int.negSucc (nat_lit {-c - 1})'


def lean_defs(name, nf):
    """Lean source for the normal form `nf` as chunks of `CHUNK` terms (long list literals make the
    elaborator exceed its recursion and heartbeat limits) and their concatenation."""
    chunks = [nf[i:i + CHUNK] for i in range(0, len(nf), CHUNK)]
    out = []
    for j, ch in enumerate(chunks):
        items = [f'(nat_lit {k}, {int_lit(c)})' for k, c in ch]
        lines, cur = [], '  [ '
        for i, it in enumerate(items):
            tok = it + (',' if i + 1 < len(items) else ' ]')
            if len(cur) + len(tok) + 1 > 100:
                lines.append(cur.rstrip())
                cur = '    '
            cur += tok + ' '
        lines.append(cur.rstrip())
        out.append(f'private noncomputable def {name}_{j} : SP :=\n' + '\n'.join(lines) + '\n')
    names = [f'{name}_{j}' for j in range(len(chunks))]
    cat = 'catSP\n    [ ' + ',\n      '.join(', '.join(names[i:i + 4]) for i in range(0, len(names), 4)) + ' ]'
    return '\n'.join(out), cat


# name, Lean expression of the piece, Python value, one-line description
def pieces():
    F = Fgen()
    nW = n * W1()
    pr = P({})
    for i, j in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
        pr = pr + pairNorm(i, j, zz, ww)
    R = [resNorm0(siteSwap(i, zz), siteSwap(i, ww)) for i in range(4)]
    swap = ['zSP wSP'] + [f'(siteSwap {i} zSP) (siteSwap {i} wSP)' for i in (1, 2, 3)]
    out = [('F', 'Fgen zSP wSP', F, 'the moment expression `F`'),
           ('NW', 'normG zSP wSP * W1gen zSP wSP', nW, 'the product `n W₁`'),
           ('Pair', 'pairSum zSP wSP', pr, 'the pair sum `pairSum`')]
    for i in range(4):
        out.append((f'Res{i}', f'resNorm0 {swap[i]}', R[i],
                    f'the residual norm `resNorm0` for qubit {i}'))
    return out


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ps = pieces()
    vals = {name: p for name, _, p, _ in ps}
    A = lit(96) * vals['F'] - lit(72) * vals['NW'] - lit(144) * vals['Pair']
    S = vals['Res0'] + vals['Res1'] + vals['Res2'] + vals['Res3']
    assert not (A - S).d, 'the defect does not vanish'
    prev = 'IdentityVars'
    for name, expr, p, desc in ps:
        nf = normal_form(p)
        defs, cat = lean_defs(f'chunk{name}', nf)
        path = os.path.join(here, f'IdentityCert{name}.lean')
        with open(path, 'w') as f:
            f.write(f'''import FormalResearch.FourQubitEntropy.{prev}

/-!
# Normal form of {desc}

Generated by `gen_sextic_certificate.py` ({len(nf)} terms). The Lean kernel checks that
`{expr}` evaluates to this list; see `Identity.lean`. The `IdentityCert*.lean` files import one
another in a chain, only so that `lake` builds them one at a time: each needs several GB of kernel memory.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

{defs}
/-- Normal form of `{expr}`, as `(monomial key, coefficient)` pairs sorted by key. -/
noncomputable def sexticCert{name} : SP :=
  {cat}

/-- Kernel-checked: `{expr}` has the normal form `sexticCert{name}`. -/
theorem sexticCert{name}_eq : {expr} = sexticCert{name} :=
  eqSP_sound _ _ (by decide +kernel)

end FormalResearch.FourQubitEntropy
''')
        prev = f'IdentityCert{name}'
        print(path, len(nf))


if __name__ == '__main__':
    main()
