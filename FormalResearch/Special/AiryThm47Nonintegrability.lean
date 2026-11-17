module

public import FormalResearch.Special.AiryPoly

/-!
# Degree bookkeeping for the non-integrability step in Theorem 4.7

This file records the denominator and degree count in `SOFT_EDGE_THEOREMS.md`, Theorem 4.7.  For
`N = P·Ai + Q·Ai'`, the prescribed number of factors is `max (2 deg P + 1) (2 deg Q + 2)`.
The analytic assertion that a nonconstant polynomial multiple of `N² / ∏(u-t_j)` is not in
`L¹(ℝ)` is `at47_not_integrable_poly_mul` in `AiryThm47Band` (proved there; this file holds only the bookkeeping).  The constant case is expected to have band decay
`|u|^(-3/2)`.  Numerical check (SciPy 1.17, double precision): for `P = Q = 1`, `m = 2`, and for
`P = u, Q = 1`, `m = 3`, the block integrals of `N(-s)²/s^m` over `[R,2R]` at
`R = 100, 400, 1600` are respectively `(0.00939155, 0.00467033, 0.00233183)` and
`(0.00939180, 0.00466990, 0.00233185)`; multiplying by `sqrt(R)` gives approximately
`0.0939, 0.0934, 0.0933`, consistent with `R^(-1/2)` mass on each block. `P = Q = 1` is
Hermite–Biehler; `P = u, Q = 1` is included as a comparison (its linear factor has a root in the
upper half-plane under the convention in `AiryPolyHB`).
-/

@[expose] public section

open Polynomial

namespace FormalResearch.Special

/-- The number of top zeros in the Theorem 4.7 extremal denominator. -/
noncomputable def at47_m (P Q : ℝ[X]) : ℕ := max (2 * P.natDegree + 1) (2 * Q.natDegree + 2)

/-- The product of the first `m` linear factors, represented as a real polynomial. -/
noncomputable def at47_zeroProduct (ts : ℕ → ℝ) (m : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range m, (Polynomial.X - Polynomial.C (ts (j + 1)))

lemma at47_m_ge_P (P Q : ℝ[X]) : 2 * P.natDegree + 1 ≤ at47_m P Q :=
  le_max_left _ _

lemma at47_m_ge_Q (P Q : ℝ[X]) : 2 * Q.natDegree + 2 ≤ at47_m P Q :=
  le_max_right _ _

end FormalResearch.Special
