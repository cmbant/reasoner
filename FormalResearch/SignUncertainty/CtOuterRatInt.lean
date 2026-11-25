module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Rational integrals `∫_0^∞ t²/((1+t²)(m²+t²)) dt = π/(2(m+1))`

Generic real analysis.  **Proved** (`m = 1` and `m > 1`), and `∫_0^∞ dt/(1+t²) = π/2`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

lemma hasDerivAt_arctan_div {m : ℝ} (hm : 0 < m) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan (t / m)) (m / (m ^ 2 + t ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / m) (1 / m) t := by
    simpa using (hasDerivAt_id t).div_const m
  have h2 := (Real.hasDerivAt_arctan (t / m)).comp t h1
  refine h2.congr_deriv ?_
  field_simp

lemma integrableOn_inv_one_add_sq : IntegrableOn (fun t : ℝ => 1 / (1 + t ^ 2)) (Ioi 0) :=
  (integrable_inv_one_add_sq.congr (Eventually.of_forall fun t => by simp [one_div])).integrableOn

lemma integral_inv_one_add_sq_Ioi : ∫ t in Ioi (0 : ℝ), 1 / (1 + t ^ 2) = π / 2 := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := fun x _ => by
    simpa using Real.hasDerivAt_arctan x
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hd integrableOn_inv_one_add_sq
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)
  rw [this]; simp

lemma integrableOn_rat {m : ℝ} (hm : 1 ≤ m) :
    IntegrableOn (fun t : ℝ => t ^ 2 / ((1 + t ^ 2) * (m ^ 2 + t ^ 2))) (Ioi 0) := by
  refine Integrable.mono' integrableOn_inv_one_add_sq ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_)
    exact Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  · filter_upwards with t
    have h1 : 0 < 1 + t ^ 2 := by positivity
    have h2 : 0 < m ^ 2 + t ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) h1]
    nlinarith [sq_nonneg t]

lemma integral_rat_one : ∫ t in Ioi (0 : ℝ), t ^ 2 / ((1 + t ^ 2) * (1 ^ 2 + t ^ 2)) = π / 4 := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => (Real.arctan t - t / (1 + t ^ 2)) / 2)
      (x ^ 2 / ((1 + x ^ 2) * (1 ^ 2 + x ^ 2))) x := by
    intro x _
    have h1 := Real.hasDerivAt_arctan x
    have h2 : HasDerivAt (fun t : ℝ => t / (1 + t ^ 2)) ((1 * (1 + x ^ 2) - x * (2 * x)) / (1 + x ^ 2) ^ 2) x := by
      have := (hasDerivAt_id x).div ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_pow 2 x)) (by simp only [Pi.add_apply]; positivity)
      refine this.congr_deriv ?_
      simp
    have := (h1.sub h2).div_const 2
    refine this.congr_deriv ?_
    have : (1 + x ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hlim : Tendsto (fun t : ℝ => (Real.arctan t - t / (1 + t ^ 2)) / 2) atTop (𝓝 (π / 4)) := by
    have h0 : Tendsto (fun t : ℝ => t / (1 + t ^ 2)) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
      · filter_upwards [eventually_gt_atTop 0] with t ht using by positivity
      · filter_upwards [eventually_gt_atTop 0] with t ht
        rw [div_le_iff₀ (by positivity)]
        have : t⁻¹ * (1 + t ^ 2) = t⁻¹ + t := by field_simp
        rw [this]
        have : 0 < t⁻¹ := by positivity
        linarith
    have := (((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)).sub h0).div_const 2
    convert this using 2; ring
  have hint := integrableOn_rat (m := 1) le_rfl
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  simpa using this

lemma integral_rat {m : ℝ} (hm : 1 < m) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 / ((1 + t ^ 2) * (m ^ 2 + t ^ 2)) = π / (2 * (m + 1)) := by
  have hm0 : 0 < m := by linarith
  have hm1 : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => (m * Real.arctan (t / m) - Real.arctan t) / (m ^ 2 - 1))
      (x ^ 2 / ((1 + x ^ 2) * (m ^ 2 + x ^ 2))) x := by
    intro x _
    have h1 := (hasDerivAt_arctan_div hm0 x).const_mul m
    have h2 := Real.hasDerivAt_arctan x
    have := (h1.sub h2).div_const (m ^ 2 - 1)
    refine this.congr_deriv ?_
    have : (1 + x ^ 2) ≠ 0 := by positivity
    have : (m ^ 2 + x ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hlim : Tendsto (fun t : ℝ => (m * Real.arctan (t / m) - Real.arctan t) / (m ^ 2 - 1)) atTop
      (𝓝 (π / (2 * (m + 1)))) := by
    have h1 : Tendsto (fun t : ℝ => Real.arctan (t / m)) atTop (𝓝 (π / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_div_const hm0)
    have h2 : Tendsto Real.arctan atTop (𝓝 (π / 2)) := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
    have := ((h1.const_mul m).sub h2).div_const (m ^ 2 - 1)
    convert this using 2
    field_simp
    have : m ^ 2 - 1 = (m - 1) * (m + 1) := by ring
    rw [this]
    field_simp
  have hint := integrableOn_rat hm.le
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  simpa using this

lemma integral_rat' {m : ℝ} (hm : 1 ≤ m) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 / ((1 + t ^ 2) * (m ^ 2 + t ^ 2)) = π / (2 * (m + 1)) := by
  rcases hm.eq_or_lt with h | h
  · rw [← h, integral_rat_one]; ring
  · exact integral_rat h

/-- info: 'FormalResearch.SignUncertainty.integral_rat'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_rat'

end FormalResearch.SignUncertainty
