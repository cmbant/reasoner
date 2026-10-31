#!/usr/bin/env python3
"""Generate RenyiFullSliverCells.lean: the Bernstein certificates of `lem:fqe-cluster-sliver`.

Polynomial inequalities (all coefficients exact rationals, checked in Lean by `ring` + `positivity`):

* slA_*:  for each of the four rows (chart S/B, sign -/+) of the paper table (ST), the polynomial
  `G_h(u,v,e,k) - (P(u,v) + e (A + B v))` has all tensor Bernstein coefficients >= 0 on the box
  `0<=u<=1/16, 0<=v<=1/20, 0<=e<=1/100, 13856/10^4<=k<=13857/10^4` (after `k^2 = 48/25`);
* slC_*:  the one-variable endpoint polynomial `P(u,V(u)) D(u)^2 + (5/2) Q(u) D(u)^2` on `[1/140, U]`;
* slQ: the identity  x^8 - Q(x^5) = (x-z)^2 (Z-x) S(x)  with S having positive coefficients.

Usage: python3 gen_sliver_cells.py > RenyiFullSliverCells.lean
"""
import itertools
import sympy as s

R = s.Rational
u, v, e, k = s.symbols('u v e k')
KLO, KHI = R(13856, 10000), R(13857, 10000)

ROWS = {
    'Sm': ('S', -1, (R(2, 125), R(7, 500), -R(571, 100), -R(33, 10), -R(281, 100), 6), (R(185, 100), 8)),
    'Sp': ('S', 1, (R(2, 125), R(7, 500), -6, R(69, 50), -R(103, 20), 0), (R(147, 100), 16)),
    'Bm': ('B', -1, (R(2, 125), R(19, 100), -6, 3, -5, 0), (R(1, 2), 0)),
    'Bp': ('B', 1, (R(2, 125), R(19, 100), -R(571, 100), -R(3, 2), -R(5, 2), 0), (R(1, 2), 0)),
}
AL, BE, GA, KK = R(35425, 10000), R(1872, 10000), R(11235, 10000), R(39005, 10000)


def lr(x):
    """Lean real literal for a sympy Rational."""
    x = R(x)
    if x.q == 1:
        return f"({x.p} : ℝ)" if x.p >= 0 else f"(-{-x.p} : ℝ)"
    return f"({x.p} / {x.q} : ℝ)" if x.p >= 0 else f"(-({-x.p} / {x.q}) : ℝ)"


def Gpoly(ch, sg):
    p = R(1, 2) - u + u * u + v / 2
    tau = (1 - u) if ch == 'S' else u
    t = R(1, 4) - 3 * u / 4 + 3 * u * u / 4 + R(3, 4) * tau * v
    X = R(1, 2) + e - p
    fc = -1 + 8 * e + 9 * p - 12 * t
    ff = fc + sg * k * X
    h2 = (R(113, 100) * v + R(3, 2) * u * v - R(3, 8) * v * v) if ch == 'S' else 3 * v
    hh = 1 + KK * u + R(12, 5) * u * u - h2
    return (1 + AL / 6 + 3 * BE / 2 - 5 * GA / 36 - hh - AL * (p - R(1, 3)) - BE * (17 * p - 12 * t - 4)
            + GA * (p * p - R(1, 9)) + AL * e + BE * ff - GA * (ff * ff + R(17, 2) * e + 2 * e * e) / 6
            - BE / 2 + GA / 24), X


def kreduce(expr):
    P = s.Poly(s.expand(expr), k)
    out = 0
    for (i,), c in P.terms():
        out += c * R(48, 25) ** (i // 2) * k ** (i % 2)
    return s.expand(out)


def bernstein(poly, vars_, boxes):
    """Tensor Bernstein coefficients of `poly` on the box; returns (degrees, {index: coeff})."""
    degs = [max(s.Poly(poly, x).degree(), 0) for x in vars_]
    ts = s.symbols('t0:%d' % len(vars_))
    sub = {x: lo + (hi - lo) * t for x, t, (lo, hi) in zip(vars_, ts, boxes)}
    Q = s.Poly(s.expand(poly.subs(sub, simultaneous=True)), *ts)
    out = {}
    for idx in itertools.product(*[range(n + 1) for n in degs]):
        tot = 0
        for j in itertools.product(*[range(i + 1) for i in idx]):
            a = Q.coeff_monomial(tuple(j))
            if a == 0:
                continue
            w = 1
            for ik, jk, nk in zip(idx, j, degs):
                w *= s.binomial(ik, jk) / s.binomial(nk, jk)
            tot += a * w
        out[idx] = tot
    return degs, out


def bern_sum(co, degs, names):
    terms = []
    for idx, c in co.items():
        assert c >= 0, (idx, c)
        if c == 0:
            continue
        fac = ' * '.join(f"({nm} ^ {i} * (1 - {nm}) ^ {n - i})" for nm, i, n in zip(names, idx, degs))
        bin_ = 1
        for i, n in zip(idx, degs):
            bin_ *= s.binomial(n, i)
        terms.append(f"{lr(c * bin_)} * {fac}")
    return ' +\n      '.join(terms)


def lpoly_expr(expr):
    P = s.Poly(s.expand(expr), u, v, e)
    return lpoly({m: co for m, co in P.terms()}, ['u', 'v', 'e'])


def lpoly(poly, vs):
    """Lean text of a polynomial given as {(i,j,..): coeff}."""
    terms = []
    for key, co in sorted(poly.items()):
        if co == 0:
            continue
        mon = ' * '.join(f"{nm} ^ {i}" for nm, i in zip(vs, key) if i > 0)
        terms.append(f"{lr(co)}" + (f" * {mon}" if mon else ''))
    return ' + '.join(terms) if terms else '0'


def cell_A(name):
    ch, sg, row, (A, B) = ROWS[name]
    G, X = Gpoly(ch, sg)
    a, b, c, d, f, g = row
    tgt = a * u + b * v + c * u * u + d * u * v + f * v * v + g * u * u * v + e * (A + B * v)
    D = kreduce(G - tgt)
    P = s.Poly(D, u, v, e, k)
    coef = {}
    for (i, j, l, m), co in P.terms():
        coef.setdefault((i, j, l), [R(0), R(0)])[m] += co
    low = {key: al + be * (KLO if be >= 0 else KHI) for key, (al, be) in coef.items()}
    D0 = {(i, j): co for (i, j, l), co in low.items() if l == 0}
    D1 = {(i, j): co for (i, j, l), co in low.items() if l == 1}
    rem = []   # nonnegative remainder terms
    for (i, j, l), (al, be) in coef.items():
        mon = f"u ^ {i} * v ^ {j} * e ^ {l}"
        if be > 0:
            rem.append(f"{lr(be)} * (k - 13856 / 10000) * ({mon})")
        elif be < 0:
            rem.append(f"{lr(-be)} * (13857 / 10000 - k) * ({mon})")
        if l == 2:
            co = low[(i, j, l)]
            assert co <= 0
            D1[(i, j)] = D1.get((i, j), R(0)) + co / 100
            rem.append(f"{lr(-co)} * (1 / 100 - e) * (u ^ {i} * v ^ {j} * e)")
    out = ""
    names = ['s1', 's2']
    thms = []
    for tag, Dp in (('0', D0), ('1', D1)):
        poly = sum(co * u ** i * v ** j for (i, j), co in Dp.items())
        degs, co = bernstein(s.expand(poly), [u, v], [(0, R(1, 16)), (0, R(1, 20))])
        bs = bern_sum(co, degs, names)
        text = lpoly(Dp, ['u', 'v'])
        thms.append(f"""
set_option maxHeartbeats 8000000 in
/-- Row `{name}`: the `ε`-free (`{tag}`) polynomial of the lower bound, Bernstein coefficients `≥ 0`. -/
theorem slA{tag}_{name} {{u v : ℝ}} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 20) :
    0 ≤ {text} := by
  obtain ⟨s1, hs1a, hs1b, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ u = s / 16 :=
    ⟨16 * u, by linarith, by linarith, by ring⟩
  obtain ⟨s2, hs2a, hs2b, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ v = s / 20 :=
    ⟨20 * v, by linarith, by linarith, by ring⟩
  have h1 : 0 ≤ 1 - s1 := by linarith
  have h2 : 0 ≤ 1 - s2 := by linarith
  have key : {lpoly(Dp, ['(s1 / 16)', '(s2 / 20)'])} =
      {bs} := by
    ring
  rw [key]
  positivity
""")
    c2 = s.expand(s.Poly(s.expand(G), k).coeff_monomial(k ** 2))
    rowlit = ' '.join(lr(x) for x in row)
    tau = '(1 - u)' if ch == 'S' else 'u'
    h2s = ("(113 / 100 * v + 3 / 2 * u * v - 3 / 8 * v ^ 2)" if ch == 'S' else "(3 * v)")
    remtxt = ' +\n      '.join(rem)
    thms.append(f"""
/-- Row `{name}` of (ST): `P + ε (A + B v) ≤ G_h` on the box (`G_h` is `G` with the entropy replaced by its
head/tail estimate). -/
theorem slA_{name} {{u v e k : ℝ}} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 20)
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 100) (hk0 : 13856 / 10000 ≤ k) (hk1 : k ≤ 13857 / 10000)
    (hk2 : k ^ 2 = 48 / 25) :
    slP {rowlit} u v + e * ({lr(A)} + {lr(B)} * v) ≤
      slG {tau} ({sg}) {h2s} u v e k := by
  have h0 := slA0_{name} hu0 hu1 hv0 hv1
  have h1 := slA1_{name} hu0 hu1 hv0 hv1
  have hk0' : 0 ≤ k - 13856 / 10000 := by linarith
  have hk1' : 0 ≤ 13857 / 10000 - k := by linarith
  have he1' : 0 ≤ 1 / 100 - e := by linarith
  have key : slG {tau} ({sg}) {h2s} u v e k - (slP {rowlit} u v + e * ({lr(A)} + {lr(B)} * v)) =
      ({lpoly(D0, ['u', 'v'])}) + e * ({lpoly(D1, ['u', 'v'])}) +
      ({remtxt}) := by
    unfold slG slP slp slt
    linear_combination ({lpoly_expr(c2)}) * hk2
  have hrem : 0 ≤ {remtxt} := by positivity
  have := mul_nonneg he0 h1
  nlinarith
""")
    return ''.join(thms)


# ---------------------------------------------------------------------------------------------
# endpoint v = V(u):  P(u, V(u)) + (5/2) Q(u) > 0  on [1/140, U]
Z = R(23, 40)
U = Z ** 5
z0 = R(2, 5)
u0 = z0 ** 5
KQ = (Z ** 8 - z0 ** 8 - R(8, 5) * z0 ** 3 * (U - u0)) / (U - u0) ** 2
LOW = R(1, 140)
x = s.Symbol('x')


def Qpoly(uu):
    return z0 ** 8 + R(8, 5) * z0 ** 3 * (uu - u0) + KQ * (uu - u0) ** 2


def cell_C(name):
    ch, sg, row, _ = ROWS[name]
    a, b, c, d, f, g = row
    Dn = R(26, 5) - 9 * u
    Vf = (R(3, 50) + R(7, 5) * (u - u * u)) / Dn
    P = a * u + b * Vf + c * u * u + d * u * Vf + f * Vf * Vf + g * u * u * Vf + R(5, 2) * Qpoly(u)
    poly = s.Poly(s.cancel(P * Dn * Dn), u).as_expr()
    degs, co = bernstein(poly, [u], [(LOW, U)])
    cmin = min(co.values())
    assert cmin > 0
    co2 = {i: c_ - cmin for i, c_ in co.items()}
    rowlit = ' '.join(lr(t) for t in row)
    n = degs[0]
    terms = ' +\n      '.join(f"{lr(c_ * s.binomial(n, i[0]))} * (s ^ {i[0]} * (1 - s) ^ {n - i[0]})" for i, c_ in co2.items() if c_ != 0)
    w = lr(U - LOW)
    uu = f"(1 / 140 + {w} * s)"
    Dd = f"(26 / 5 - 9 * {uu})"
    Nn = f"(3 / 50 + 7 / 5 * ({uu} - {uu} ^ 2))"
    coefv = (f"({lr(b)} * {Dd} + {lr(d)} * {uu} * {Dd} + {lr(f)} * (slV {uu} * {Dd} + {Nn}) "
             f"+ {lr(g)} * {uu} ^ 2 * {Dd})")
    return f"""
set_option maxHeartbeats 8000000 in
/-- Endpoint `v = V(u)` of the concave-in-`v` argument, row `{name}`. -/
theorem slC_{name} {{u : ℝ}} (h0 : 1 / 140 ≤ u) (h1 : u ≤ {lr(U)}) :
    0 < slP {rowlit} u (slV u) + 5 / 2 * slQ u := by
  have hUle : ({lr(U)} : ℝ) ≤ 1 / 10 := by norm_num
  obtain ⟨s, hs0, hs1, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ u = 1 / 140 + {w} * s :=
    ⟨(u - 1 / 140) / {w}, by apply div_nonneg <;> linarith [show (0 : ℝ) < {w} by norm_num],
      by rw [div_le_one (by norm_num)]; linarith, by field_simp; ring⟩
  have h1s : 0 ≤ 1 - s := by linarith
  have hD : 0 < {Dd} := by nlinarith
  have hV : slV {uu} * {Dd} = {Nn} := by
    unfold slV; exact div_mul_cancel₀ _ hD.ne'
  have key : (slP {rowlit} {uu} (slV {uu}) + 5 / 2 * slQ {uu}) * {Dd} ^ 2 =
      {lr(cmin)} +
      {terms} := by
    unfold slP slQ
    linear_combination {coefv} * hV
  have hpos : 0 < ({lr(cmin)} +
      {terms} : ℝ) := by positivity
  rw [← key] at hpos
  exact (mul_pos_iff_of_pos_right (by positivity)).1 hpos
"""


# ---------------------------------------------------------------------------------------------
# Hermite minorant:  x^8 - Q(x^5) = (x - z)^2 (Z - x) S(x),  S with positive coefficients
def cell_Q():
    h = x ** 8 - Qpoly(x ** 5)
    q, r = s.div(s.Poly(h, x), s.Poly((x - z0) ** 2 * (Z - x), x))
    assert r.is_zero and all(c_ > 0 for c_ in q.all_coeffs())
    sx = ' + '.join(f"{lr(c_)} * x ^ {i}" for i, c_ in enumerate(reversed(q.all_coeffs())))
    return f"""
/-- The Hermite minorant identity: `x^8 - Q(x^5) = (x - 2/5)^2 (23/40 - x) S(x)`, `S` with positive
coefficients. -/
theorem slQ_identity (x : ℝ) : x ^ 8 - slQ (x ^ 5) = (x - 2 / 5) ^ 2 * (23 / 40 - x) * ({sx}) := by
  unfold slQ
  ring

theorem slQ_S_nonneg {{x : ℝ}} (hx : 0 ≤ x) : 0 ≤ {sx} := by positivity
"""


HEADER = f"""import Mathlib

/-!
# Bernstein certificates for the cluster sliver (`lem:fqe-cluster-sliver`)

Paper E, `sup_renyi.tex`, proof of `lem:fqe-cluster-sliver` (generated by `gen_sliver_cells.py`; do not edit).

* `slG`: the polynomial lower bound of `G_±` (the entropy replaced by its head/tail estimate (SH), without the
  `(5/2) u^{{8/5}}` term), chart `S` (`τ = 1 - u`) or `B` (`τ = u`), sign `s = ±1`;
* `slA_*`: `G_h ≥ P + ε (A + B v)` for the four rows of the table (ST) on the box
  `u ≤ 1/16, v ≤ 1/20, ε ≤ 1/100, 13856/10^4 ≤ κ ≤ 13857/10^4`, `κ² = 48/25`
  (all tensor Bernstein coefficients are nonnegative; identity by `ring`);
* `slC_*`: the endpoint `v = V(u)` of the concave argument: `P(u, V(u)) + (5/2) Q(u) > 0` on `[1/140, (23/40)^5]`
  (one-variable Bernstein expansion with positive coefficients);
* `slQ_identity`: the Hermite minorant `x^8 ≥ Q(x^5)` on `[0, 23/40]`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

/-- `P(u,v) = a u + b v + c u² + d u v + f v² + g u² v` (the table (ST) polynomial without `c_s u^{{8/5}}`). -/
noncomputable def slP (a b c d f g u v : ℝ) : ℝ :=
  a * u + b * v + c * u ^ 2 + d * u * v + f * v ^ 2 + g * u ^ 2 * v

/-- `p = 1/2 - u + u² + v/2`. -/
noncomputable def slp (u v : ℝ) : ℝ := 1 / 2 - u + u ^ 2 + v / 2

/-- `t = 1/4 - 3u/4 + 3u²/4 + (3/4) τ v`. -/
noncomputable def slt (τ u v : ℝ) : ℝ := 1 / 4 - 3 / 4 * u + 3 / 4 * u ^ 2 + 3 / 4 * τ * v

/-- `G` with the entropy replaced by `1 + K u + (12/5) u² - h₂` (HT row `(3.5425, 0.1872, 1.1235)`). -/
noncomputable def slG (τ s h₂ u v e k : ℝ) : ℝ :=
  1 + (35425 / 10000) / 6 + 3 * (1872 / 10000) / 2 - 5 * (11235 / 10000) / 36
    - (1 + 39005 / 10000 * u + 12 / 5 * u ^ 2 - h₂)
    - (35425 / 10000) * (slp u v - 1 / 3) - (1872 / 10000) * (17 * slp u v - 12 * slt τ u v - 4)
    + (11235 / 10000) * (slp u v ^ 2 - 1 / 9)
    + ((35425 / 10000) * e
        + (1872 / 10000) * (-1 + 8 * e + 9 * slp u v - 12 * slt τ u v + s * k * (1 / 2 + e - slp u v))
        - (11235 / 10000) / 6 * ((-1 + 8 * e + 9 * slp u v - 12 * slt τ u v + s * k * (1 / 2 + e - slp u v)) ^ 2
          + 17 / 2 * e + 2 * e ^ 2))
    - ((1872 / 10000) / 2 - (11235 / 10000) / 24)

/-- `V(u) = (3/50 + (7/5)(u - u²)) / (26/5 - 9u)`. -/
noncomputable def slV (u : ℝ) : ℝ := (3 / 50 + 7 / 5 * (u - u ^ 2)) / (26 / 5 - 9 * u)

/-- The quadratic minorant `Q_{{Z,z}}` of `u^{{8/5}}`, `Z = 23/40`, `z = 2/5` (equation (SQ)). -/
noncomputable def slQ (u : ℝ) : ℝ :=
  {lr(z0 ** 8)} + 8 / 5 * {lr(z0 ** 3)} * (u - {lr(u0)}) + {lr(KQ)} * (u - {lr(u0)}) ^ 2
"""

FOOTER = """
end FormalResearch.FourQubitEntropy.RenyiFull
"""

if __name__ == '__main__':
    out = [HEADER]
    for nm in ROWS:
        out.append(cell_A(nm))
    out.append(cell_Q())
    for nm in ('Sm', 'Sp'):
        out.append(cell_C(nm))
    out.append(FOOTER)
    print(''.join(out))
