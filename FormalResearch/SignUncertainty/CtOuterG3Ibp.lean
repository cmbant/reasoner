module

public import FormalResearch.SignUncertainty.CtOuterG3Main
public import FormalResearch.SignUncertainty.CtOuterP3

/-!
# `∫_0^∞ g cosh(πt)/sinh²(πt) dt = (1/π) ∫_0^∞ g'(t)/sinh(πt) dt`, and the value of `c_{3,1t2}`

**Proved** by one integration by parts on `(0, ∞)` (`g = 1 - (1-t²)/(1+t²)²`, `(1/(π sinh πt))' = -K̂`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma hasDerivAt_gC (t : ℝ) : HasDerivAt gC (gd t) t := by
  have h4 : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ 2) (2 * (1 + t ^ 2) * (2 * t)) t := by
    have := (((hasDerivAt_pow 2 t).const_add 1).pow 2)
    refine this.congr_deriv ?_
    simp
  have h1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_sub 1)
  have h2 := h1.div h4 (by positivity)
  have h3 := h2.const_sub 1
  have e : gC = fun s : ℝ => 1 - (1 - s ^ 2) / (1 + s ^ 2) ^ 2 := by funext s; rfl
  rw [e]
  refine h3.congr_deriv ?_
  unfold gd rG
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `v(t) = -1/(π sinh(πt))`, with `v' = K̂` on `t > 0`. -/
lemma hasDerivAt_negInvSinhPi {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => -(1 / (π * Real.sinh (π * s)))) (Khat t) t := by
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h2 : HasDerivAt (fun s : ℝ => Real.sinh (π * s)) (Real.cosh (π * t) * π) t :=
    hasDerivAt_sinh_pi t
  have h3 := ((hasDerivAt_const t π).mul h2)
  have hne : π * Real.sinh (π * t) ≠ 0 := by positivity
  have h4 := ((hasDerivAt_const t (1 : ℝ)).div h3 hne).neg
  refine h4.congr_deriv ?_
  unfold Khat
  have := Real.pi_pos.ne'
  field_simp
  simp
  ring

/-- **`∫_0^∞ g K̂ = (1/π) ∫_0^∞ g'(t)/sinh(πt) dt`.** -/
theorem integral_G_eq :
    ∫ t in Ioi (0 : ℝ), gC t * Khat t = (1 / π) * ∫ t in Ioi (0 : ℝ), gd t / Real.sinh (π * t) := by
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt gC (gd x) x := fun x _ => hasDerivAt_gC x
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => -(1 / (π * Real.sinh (π * s)))) (Khat x) x :=
    fun x hx => hasDerivAt_negInvSinhPi hx
  have hint1 : IntegrableOn (gC * Khat) (Ioi 0) := integrableOn_G
  have hint2 : IntegrableOn (gd * fun s : ℝ => -(1 / (π * Real.sinh (π * s)))) (Ioi 0) := by
    have := (integrableOn_gd_div_sinh.const_mul (-(1 / π)))
    refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    have hs : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by have : (0 : ℝ) < t := ht; positivity)).ne'
    have := Real.pi_pos.ne'
    field_simp
  have h0 : Tendsto (gC * fun s : ℝ => -(1 / (π * Real.sinh (π * s)))) (𝓝[>] 0) (𝓝 0) := by
    have hpi := Real.pi_pos
    have ha : Tendsto (fun t : ℝ => 4 / π ^ 2 * t) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => 4 / π ^ 2 * t) (𝓝 0) (𝓝 (4 / π ^ 2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    have ht0 : 0 < t := ht.1
    have hs : π * t ≤ Real.sinh (π * t) := Real.self_le_sinh_iff.mpr (by positivity)
    have hq := gC_quad t (by rw [abs_of_pos ht0]; exact ht.2.le)
    rw [abs_of_nonneg (gC_nonneg t)] at hq
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, norm_neg, abs_of_nonneg (gC_nonneg t)]
    have hsp : 0 < π * Real.sinh (π * t) := by positivity
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (π * Real.sinh (π * t)))]
    calc gC t * (1 / (π * Real.sinh (π * t))) ≤ (4 * t ^ 2) * (1 / (π * (π * t))) := by
          apply mul_le_mul hq _ (by positivity) (by positivity)
          apply one_div_le_one_div_of_le (by positivity)
          exact mul_le_mul_of_nonneg_left hs hpi.le
      _ = 4 / π ^ 2 * t := by field_simp
  have hinf : Tendsto (gC * fun s : ℝ => -(1 / (π * Real.sinh (π * s)))) atTop (𝓝 0) := by
    have hpi := Real.pi_pos
    have he : Tendsto (fun t : ℝ => Real.exp (-(π * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hpi)
    have ha : Tendsto (fun t : ℝ => 6 / π * Real.exp (-(π * t))) atTop (𝓝 0) := by
      simpa using he.const_mul (6 / π)
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht1
    have ht0 : 0 < t := by linarith
    have hsp : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
    have hy : 1 ≤ π * t := by nlinarith only [Real.pi_gt_three, ht1]
    have hinv := inv_sinh_le hy
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, norm_neg, abs_of_nonneg (gC_nonneg t)]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (π * Real.sinh (π * t)))]
    calc gC t * (1 / (π * Real.sinh (π * t))) ≤ 2 * (1 / (π * Real.sinh (π * t))) :=
          mul_le_mul_of_nonneg_right (gC_le t) (by positivity)
      _ = 2 / π * (1 / Real.sinh (π * t)) := by field_simp
      _ ≤ 2 / π * (3 * Real.exp (-(π * t))) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 6 / π * Real.exp (-(π * t)) := by ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint1 hint2 h0 hinf
  have e : ∫ x in Ioi (0 : ℝ), gd x * -(1 / (π * Real.sinh (π * x))) =
      -(1 / π) * ∫ x in Ioi (0 : ℝ), gd x / Real.sinh (π * x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have hs : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by have : (0 : ℝ) < t := ht; positivity)).ne'
    have := Real.pi_pos.ne'
    field_simp
  rw [e] at hibp
  linarith only [hibp]

/-- **`(π/3) G + 1/3 = ζ(3)/2`**, i.e. `c_{3,1t2} + 1/3 = ½ ζ(3)`. -/
theorem c3_1t2_value :
    π / 3 * (∫ t in Ioi (0 : ℝ), gC t * Khat t) + 1 / 3 = (riemannZeta 3).re / 2 := by
  rw [integral_G_eq, integral_gd_div_sinh]
  have := Real.pi_pos.ne'
  field_simp
  ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_G_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_G_eq

/-- info: 'FormalResearch.SignUncertainty.CtOuter.c3_1t2_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms c3_1t2_value

end FormalResearch.SignUncertainty.CtOuter
