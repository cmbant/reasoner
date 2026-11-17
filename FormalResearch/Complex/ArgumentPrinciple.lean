module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The argument principle on a circle

Generic complex analysis (no application content).  **Proved.**

Statement formalised (the argument principle for a disc, e.g. Ahlfors, *Complex Analysis*, §5.2; Conway,
*Functions of One Complex Variable*, V.3.4 with a circle as contour): let `f` be holomorphic on the open disc
`ball c R` and let `0 < r < R` (so `f` is holomorphic on a neighbourhood of the closed disc `closedBall c r`).  If `f`
has no zero on the circle `sphere c r`, then
`(2πi)⁻¹ ∮_{|z - c| = r} f'(z) / f(z) dz` is the number of zeros of `f` in `ball c r`, counted with
multiplicity (`analyticOrderNatAt`):

* `ArgPrinciple.zeroCount f c r`: the number of zeros of `f` in `ball c r` with multiplicity,
  `∑ᶠ z ∈ ball c r, analyticOrderNatAt f z`;
* `ArgPrinciple.zeros_finite`: if `f` is holomorphic on `ball c R` and not identically zero there then it has finitely
  many zeros in `closedBall c r` (`r < R`), so `zeroCount` is the honest count;
* `ArgPrinciple.circleIntegral_logDeriv`: the argument principle (headline).

Proof: induction on the number of zeros.  With no zero in `closedBall c r` the integrand is holomorphic on the disc and
Cauchy's theorem gives `0`; with a zero `a`, `f = (· - a) * dslope f a`, the order drops by one and the integrand splits
as `1 / (z - a) + g' / g`, whose first part integrates to `2πi` (`circleIntegral.integral_sub_inv_of_mem_ball`).

**Not formalised.** General contours and winding numbers, poles (the meromorphic argument principle `N - P`), and
the version on a general Jordan domain.  Mathlib has none of the argument principle, Rouché's theorem, Hurwitz's theorem
(only `TendstoLocallyUniformlyOn.differentiableOn` and `logDeriv_tendsto`), as of the pinned revision.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ArgPrinciple

/-- The number of zeros of `f` in the open disc `ball c r`, counted with multiplicity
(a finsum: it is the true count when `f` is holomorphic and not identically zero, see `zeros_finite`). -/
noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ z ∈ ball c r, analyticOrderNatAt f z

variable {f g : ℂ → ℂ} {c : ℂ} {r R : ℝ}

/-- A function holomorphic on a disc and non-zero at one point of it has finite analytic order everywhere on the disc. -/
lemma order_ne_top (hf : DifferentiableOn ℂ f (ball c R)) {w : ℂ} (hw : w ∈ ball c R) (hfw : f w ≠ 0)
    {z : ℂ} (hz : z ∈ ball c R) : analyticOrderAt f z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  refine han.analyticOrderAt_ne_top_of_isPreconnected (convex_ball c R).isPreconnected hw hz ?_
  rw [(han w hw).analyticOrderAt_eq_zero.mpr hfw]
  simp

/-- On the disc, the order of a non-trivial holomorphic function is non-zero exactly at its zeros. -/
lemma orderNat_ne_zero_iff (hf : DifferentiableOn ℂ f (ball c R)) {w : ℂ} (hw : w ∈ ball c R) (hfw : f w ≠ 0)
    {z : ℂ} (hz : z ∈ ball c R) : analyticOrderNatAt f z ≠ 0 ↔ f z = 0 := by
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hfin := order_ne_top hf hw hfw hz
  constructor
  · exact apply_eq_zero_of_analyticOrderNatAt_ne_zero
  · intro h0 h
    have h1 : analyticOrderAt f z = 0 := by
      unfold analyticOrderNatAt at h
      exact (ENat.toNat_eq_zero.mp h).resolve_right hfin
    rcases analyticOrderAt_eq_zero.mp h1 with h2 | h2
    · exact h2 (han z hz)
    · exact h2 h0

/-- A function holomorphic on `ball c R` and not identically zero has only finitely many zeros in each closed disc
`closedBall c r`, `r < R`. -/
theorem zeros_finite (hf : DifferentiableOn ℂ f (ball c R)) {w : ℂ} (hw : w ∈ ball c R) (hfw : f w ≠ 0)
    (hrR : r < R) : {z ∈ closedBall c r | f z = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, hxK, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall c r)
    (fun z hz => hz.1)
  have hxR : x ∈ ball c R := lt_of_le_of_lt (mem_closedBall.mp hxK) hrR
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ z in 𝓝[≠] x, f z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hx
    exact hx.mono fun z hz => hz.2
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball c R).isPreconnected hxR hfreq hw
  exact hfw this

end FormalResearch.ArgPrinciple
