#!/usr/bin/env python3
"""Generate the `FlipGradientCert*.lean` files: normal forms of the pieces of the spin-flip gradient
identity `8 * H4dual z w = Rg z w + Rg w z` (see `FlipGradientGen.lean`).

Run from the repository root:
    python3 FormalResearch/FourQubitEntropy/gen_flipgrad_certificate.py

The pieces `H4dual zSP wSP` (the epsilon-part of `4F - 3 n W1` at `(z + eps ztilde, w + eps zhat)`),
`Ysum zSP wSP`, `Ysum wSP zSP`, `Spart zSP wSP`, `Spart wSP zSP` are expanded here, by a direct
transcription of the Lean definitions over integer-coefficient polynomials, into the sparse
prime-key normal form of `SparsePoly.lean` (same conventions as `gen_sextic_certificate.py`, whose
literal printer is reused). The Lean kernel checks `piece = literal` in one declaration per piece and
then that `8 * D - (Y + Y' + S + S')` computed from the literals is empty. Nothing here is trusted: a
wrong literal makes the kernel check fail. The script also asserts the identity in Python.
"""
import itertools, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_sextic_certificate import normal_form, lean_defs, PRIMES  # noqa: E402


class Q:
    """Polynomial with integer coefficients: dict from sorted tuple of variable indices."""
    __slots__ = ['d']

    def __init__(s, d):
        s.d = d

    @staticmethod
    def c(k):
        return Q({(): k}) if k else Q({})

    def __add__(s, o):
        if not isinstance(o, Q):
            o = Q.c(o)
        r = dict(s.d)
        for k, v in o.d.items():
            r[k] = r.get(k, 0) + v
            if r[k] == 0:
                del r[k]
        return Q(r)

    __radd__ = __add__

    def __neg__(s):
        return Q({k: -v for k, v in s.d.items()})

    def __sub__(s, o):
        if not isinstance(o, Q):
            o = Q.c(o)
        return s + (-o)

    def __rsub__(s, o):
        return Q.c(o) - s

    def __mul__(s, o):
        if not isinstance(o, Q):
            o = Q.c(o)
        r = {}
        for k1, v1 in s.d.items():
            for k2, v2 in o.d.items():
                k = tuple(sorted(k1 + k2))
                r[k] = r.get(k, 0) + v1 * v2
        return Q({k: v for k, v in r.items() if v})

    __rmul__ = __mul__


class Dual:
    """a + b eps, eps^2 = 0, over Q."""
    __slots__ = ['a', 'b']

    def __init__(s, a, b=None):
        s.a = a
        s.b = b if b is not None else Q({})

    @staticmethod
    def c(o):
        return o if isinstance(o, Dual) else Dual(Q.c(o), Q({}))

    def __add__(s, o):
        o = Dual.c(o)
        return Dual(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __neg__(s):
        return Dual(-s.a, -s.b)

    def __sub__(s, o):
        o = Dual.c(o)
        return Dual(s.a - o.a, s.b - o.b)

    def __rsub__(s, o):
        return Dual.c(o) - s

    def __mul__(s, o):
        o = Dual.c(o)
        return Dual(s.a * o.a, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__


def vi(a, b, c, d):
    return 8 * a + 4 * b + 2 * c + d


Z = {k: Q({(vi(*k),): 1}) for k in itertools.product(range(2), repeat=4)}
W = {k: Q({(16 + vi(*k),): 1}) for k in itertools.product(range(2), repeat=4)}
zz = lambda a, b, c, d: Z[(a, b, c, d)]
ww = lambda a, b, c, d: W[(a, b, c, d)]


def sum2(f):
    return f(0) + f(1)


def sum4(f):
    return sum2(lambda a: sum2(lambda b: sum2(lambda c: sum2(lambda d: f(a, b, c, d)))))


def sgn(t):
    return 1 if t == 0 else -1


def memo(M):
    c = {}

    def f(*k):
        if k not in c:
            c[k] = M(*k)
        return c[k]
    return f


def normG(z, w):
    return sum4(lambda a, b, c, d: z(a, b, c, d) * w(a, b, c, d))


def marg12(z, w):
    return lambda a, b, a2, b2: sum2(lambda c: sum2(lambda d: z(a, b, c, d) * w(a2, b2, c, d)))


def marg13(z, w):
    return lambda a, c, a2, c2: sum2(lambda b: sum2(lambda d: z(a, b, c, d) * w(a2, b, c2, d)))


def marg14(z, w):
    return lambda a, d, a2, d2: sum2(lambda b: sum2(lambda c: z(a, b, c, d) * w(a2, b, c, d2)))


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


def Fgen(z, w):
    n = normG(z, w)
    M = [memo(m(z, w)) for m in (marg12, marg13, marg14)]
    P_ = tr2(M[0]) + tr2(M[1]) + tr2(M[2])
    T = tr3(M[0]) + tr3(M[1]) + tr3(M[2])
    return 17 * n * P_ - 12 * T - 12 * n * n * n


def W1gen(z, w):
    n = normG(z, w)
    s = 0
    for i in range(4):
        s = s + (2 * trRho2(siteSwap(i, z), siteSwap(i, w)) - n * n)
    return s


def H4gen(z, w):
    return 4 * Fgen(z, w) - 3 * (normG(z, w) * W1gen(z, w))


def ztil(w):
    return lambda t0, t1, t2, t3: sgn(t0) * sgn(t1) * sgn(t2) * sgn(t3) * w(1 - t0, 1 - t1, 1 - t2, 1 - t3)


def spinFlipForm(z):
    return sum4(lambda a, b, c, d: sgn(a) * sgn(b) * sgn(c) * sgn(d) * (z(a, b, c, d) * z(1 - a, 1 - b, 1 - c, 1 - d)))


def epsSum(f):
    return f(0, 1) - f(1, 0)


def resRaw(L, z, w, x0, y0, t0, o1, o2, o3):
    pick = lambda c, o, a: o if c == 0 else a
    cs = [(0, 0, 0)] if L else list(itertools.product(range(2), repeat=3))
    zt = ztil(w)
    acc = 0
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
    return resSym(False, z, w, *a) - 8 * resSym(True, z, w, *a)


def Ysite0(z, w):
    tot = 0
    for o in itertools.product(range(2), repeat=3):
        sg = sgn(o[0]) * sgn(o[1]) * sgn(o[2])
        o1 = [1 - q for q in o]
        tot = tot + sg * (2 * (resTensor(z, w, 0, 0, 0, *o) * resTensor(z, w, 1, 1, 1, *o1))
                          - 6 * (resTensor(z, w, 0, 0, 1, *o) * resTensor(z, w, 0, 1, 1, *o1)))
    return tot


def Ysum(z, w):
    return sum((Ysite0(siteSwap(i, z), siteSwap(i, w)) for i in range(4)), Q({}))


def Spart(z, w):
    s, sb, N, W1 = spinFlipForm(z), spinFlipForm(w), normG(z, w), W1gen(z, w)
    return s * (64 * (N * N) + 56 * W1 - 64 * (s * sb))


def Pgen(z, w):
    return tr2(memo(marg12(z, w))) + tr2(memo(marg13(z, w))) + tr2(memo(marg14(z, w)))


def duals(z, w):
    zt, zh = ztil(w), ztil(z)
    Zd = lambda a, b, c, d: Dual(z(a, b, c, d), zt(a, b, c, d))
    Wd = lambda a, b, c, d: Dual(w(a, b, c, d), zh(a, b, c, d))
    return Zd, Wd


def block(name, z, w):
    Zd, Wd = duals(z, w)
    if name == 'N':
        return normG(Zd, Wd)
    if name == 'P':
        return Pgen(Zd, Wd)
    if name == 'W':
        return W1gen(Zd, Wd)
    m = {'T12': marg12, 'T13': marg13, 'T14': marg14}[name]
    return tr3(memo(m(Zd, Wd)))


def H4dual(z, w):
    Zd, Wd = duals(z, w)
    return H4gen(Zd, Wd).b


# generic Lean names of the blocks
BLOCKS = [('N', 'normG'), ('P', 'Pgen'), ('W', 'W1gen'), ('T12', 'T12gen'), ('T13', 'T13gen'), ('T14', 'T14gen')]
# files: (file suffix, description, list of (theorem stem, Lean expression, polynomial))
def pieces():
    out = []
    for nm, gen in BLOCKS:
        d = block(nm, zz, ww)
        for part in ('a', 'b'):
            expr = f'({gen} (dualZ zSP wSP) (dualW zSP wSP)).{part}'
            out.append((f'{nm}{part}', expr, getattr(d, part), f'the `{part}`-part of the block `{gen}` at the dual states'))
    for i in range(4):
        sw = lambda z, i=i: siteSwap(i, z)
        zl = 'zSP' if i == 0 else f'(siteSwap {i} zSP)'
        wl = 'wSP' if i == 0 else f'(siteSwap {i} wSP)'
        out.append((f'Y{i}', f'Ysite0 {zl} {wl}', Ysite0(siteSwap(i, zz), siteSwap(i, ww)),
                    f'the site-{i} pairing `Ysite0`'))
        out.append((f'Ys{i}', f'Ysite0 {wl} {zl}', Ysite0(siteSwap(i, ww), siteSwap(i, zz)),
                    f'the site-{i} pairing `Ysite0` with `z`, `w` exchanged'))
    S = Spart(zz, ww)
    Ss = Spart(ww, zz)
    out += [('S', 'Spart zSP wSP', S, 'the term `Spart`'),
            ('Ss', 'Spart wSP zSP', Ss, '`Spart` with `z`, `w` exchanged')]
    return out


# one file per group of pieces; a group is checked in separate declarations of one file
GROUPS = [('Small', ['Na', 'Nb', 'Pa', 'Pb', 'Wa', 'Wb']),
          ('T12', ['T12a', 'T12b']), ('T13', ['T13a', 'T13b']), ('T14', ['T14a', 'T14b']),
          ('Y0', ['Y0']), ('Y1', ['Y1']), ('Y2', ['Y2']), ('Y3', ['Y3']),
          ('Ys0', ['Ys0']), ('Ys1', ['Ys1']), ('Ys2', ['Ys2']), ('Ys3', ['Ys3']),
          ('S', ['S']), ('Ss', ['Ss'])]


def check_identity(vals):
    """8 * H4dual = Y + Ys + S + Ss, computed from the blocks and, independently, directly."""
    n_a, n_b = vals['Na'], vals['Nb']
    P_a, P_b = vals['Pa'], vals['Pb']
    W_a, W_b = vals['Wa'], vals['Wb']
    T_b = vals['T12b'] + vals['T13b'] + vals['T14b']
    Fb = 17 * (n_a * P_b + n_b * P_a) - 12 * T_b - 12 * (n_a * n_a * n_b + n_a * n_b * n_a + n_b * n_a * n_a)
    Hb = 4 * Fb - 3 * (n_a * W_b + n_b * W_a)
    Y = vals['Y0'] + vals['Y1'] + vals['Y2'] + vals['Y3']
    Ys = vals['Ys0'] + vals['Ys1'] + vals['Ys2'] + vals['Ys3']
    diff = 8 * Hb - (Y + Ys + vals['S'] + vals['Ss'])
    assert not diff.d, 'the flip-gradient identity does not hold'


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ps = pieces()
    vals = {name: p for name, _, p, _ in ps}
    check_identity(vals)
    info = {name: (expr, p, desc) for name, expr, p, desc in ps}
    prev = 'FlipGradientGen'
    for gname, names in GROUPS:
        path = os.path.join(here, f'FlipGradientCert{gname}.lean')
        body = ''
        total = 0
        for name in names:
            expr, p, desc = info[name]
            nf = normal_form(p)
            total += len(nf)
            defs, cat = lean_defs(f'chunkFG{name}', nf)
            body += f'''{defs}
/-- Normal form of `{expr}`, as `(monomial key, coefficient)` pairs sorted by key. -/
noncomputable def flipCert{name} : SP :=
  {cat}

/-- Kernel-checked: `{expr}` has the normal form `flipCert{name}`. -/
theorem flipCert{name}_eq : {expr} = flipCert{name} :=
  eqSP_sound _ _ (by decide +kernel)

'''
        with open(path, 'w') as f:
            f.write(f'''import FormalResearch.FourQubitEntropy.{prev}
import FormalResearch.FourQubitEntropy.IdentityVars

/-!
# Normal forms for the spin-flip gradient identity: {', '.join(names)}

Generated by `gen_flipgrad_certificate.py` ({total} terms in all). The Lean kernel checks that each
listed expression evaluates to its list; see `FlipGradient.lean`. The `FlipGradientCert*.lean` files import
one another in a chain, only so that `lake` builds them one at a time: each needs several GB of kernel memory.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

{body}end FormalResearch.FourQubitEntropy
''')
        prev = f'FlipGradientCert{gname}'
        print(path, total)


if __name__ == '__main__':
    main()
