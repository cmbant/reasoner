module

public import FormalResearch.Special.AiryThm47Nonintegrability
public import FormalResearch.Special.AiryThm47Liouville
public import FormalResearch.Special.AiryThm47Band
public import FormalResearch.Special.AiryThm47Uniq
public import FormalResearch.Special.AiryThm47Exist
public import FormalResearch.Special.AiryThm47Zeros

/-!
# Theorem 4.7: Airy polynomial extremals (`SOFT_EDGE_THEOREMS.md`, Lemma 4.6 and Theorem 4.7)

For `N = P Ai + Q Ai'` with `(P, Q)` real polynomials, Hermite-Biehler, `Q ≠ 0`, `m = at47_m P Q = max (2 deg P + 1) (2 deg Q + 2)`,
`S = {t_1 > ⋯ > t_m}` the `m` largest zeros of `N` and `tm = t_m`:

* `at47_top_zeros_min` (`AiryThm47Zeros`): such `S`, `tm` exist (zeros of `N` are real, simple, unbounded below, bounded above, finite
  in bounded sets; one zero between consecutive zeros of `Ai` far to the left).
* `at47_existence` (`AiryThm47Exist`): `F = (-1)^m N²/∏(u - t_j)` is entire, integrable (decay `|x|^{-3/2}`), in the class of
  `airyPQ_hasSum_unc`, real, `≥ 0` on `(-∞, t_m]`, `F(t_j) = 0`, `∫F = 0`, `F ≢ 0`: admissible for `um = tm`.
* `at47_uniqueness` (`AiryThm47Uniq`): any admissible `f` (entire, class, real, `∫f ≤ 0`, `f(t_j) ≥ 0`, `f ≥ 0` on `(-∞, um]`, `um ≥ tm`)
  satisfies `f ∏(u - t_j) = c (-1)^m N²`, `c ≥ 0`, and `c = 0` if `um > tm`; `at47_no_admissible_above` (`AiryThm47Exist`): then `f = 0`.
  Together: `sup um = t_m`, extremal unique up to a positive factor.
* Ingredients: `at47_entire_polynomial_of_circle_bound` (Liouville with polynomial growth), `at47_not_integrable_poly_mul`
  (`p N²/∏ ∉ L¹` for `deg p ≥ 1`, via `at47_block_integral`), `at47_div_finset`, `at47_G_circle_bound`.

Not formalised: the converse part of Theorem 4.7 (the space `V_m`, uniqueness of `N ∈ V_m` vanishing at given `u_j`), and Lemma 4.6's
Prüfer monotonicity (only zero reality, simplicity and the quadrature are used).
-/
