module

public import FormalResearch.SignUncertainty.CtOuterP2
public import FormalResearch.SignUncertainty.CtOuterK
public import FormalResearch.SignUncertainty.CtOuterStrip

/-!
# `∫_0^∞ log(1+(y/π)²) cosh y/sinh² y dy = 2 log 2 - 1`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (2), "Evaluation of `a_{1t2}`"
(`a_{1t2} = -π∫_0^∞ log(1+t²) cosh(πt)/sinh²(πt) dt = 1 - 2 log 2`).  **Proved.**  Integration by parts reduces the
integral to `∫_0^∞ 2t/((1+t²) sinh πt) dt`, which `integral_t_mPrime_div` (Mittag-Leffler) evaluates.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `log(1 + (y/π)²)`. -/
noncomputable def ctU3 (y : ℝ) : ℝ := Real.log (1 + (y / π) ^ 2)

lemma hasDerivAt_ctU3 (y : ℝ) : HasDerivAt ctU3 (2 * y / (π ^ 2 + y ^ 2)) y := by
  have hpi := Real.pi_pos
  have h1 : HasDerivAt (fun y : ℝ => 1 + (y / π) ^ 2) (2 * (y / π) * (1 / π)) y := by
    have := ((hasDerivAt_id y).div_const π).pow 2
    simpa using (this.const_add 1)
  have h2 := h1.log (by positivity)
  refine h2.congr_deriv ?_
  field_simp

lemma ctU3_nonneg (y : ℝ) : 0 ≤ ctU3 y := Real.log_nonneg (by nlinarith [sq_nonneg (y / π)])

lemma ctU3_le_sq (y : ℝ) : ctU3 y ≤ y ^ 2 / 9 := by
  have hpi := Real.pi_gt_three
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (y / π) ^ 2 by positivity)
  unfold ctU3
  have : (y / π) ^ 2 ≤ y ^ 2 / 9 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg y) (by norm_num) (by nlinarith)
  linarith

lemma ctU3_le_lin {y : ℝ} (hy : 0 < y) : ctU3 y ≤ 2 * y := by
  have hpi := Real.pi_gt_three
  have h1 : 1 + (y / π) ^ 2 ≤ 1 + y ^ 2 := by
    have : (y / π) ^ 2 ≤ y ^ 2 := by
      rw [div_pow]; apply div_le_self (sq_nonneg y); nlinarith
    linarith
  unfold ctU3
  calc Real.log (1 + (y / π) ^ 2) ≤ Real.log (1 + y ^ 2) := Real.log_le_log (by positivity) h1
    _ ≤ 2 * |y| := log_one_add_sq_le y
    _ = 2 * y := by rw [abs_of_pos hy]

lemma cosh_div_sinh_sq_le {y : ℝ} (hy : 1 ≤ y) : Real.cosh y / Real.sinh y ^ 2 ≤ 6 * Real.exp (-y) := by
  have hy0 : 0 < y := by linarith
  have hs := Real.sinh_pos_iff.mpr hy0
  have h2 := cosh_le_two_sinh hy
  have h3 := exp_div_three_le_sinh hy
  have hE := Real.exp_pos y
  have e : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [div_le_iff₀ (by positivity)]
  calc Real.cosh y ≤ 2 * Real.sinh y := h2
    _ ≤ 6 * Real.exp (-y) * Real.sinh y ^ 2 := by
      rw [e]
      have : 1 ≤ 3 * Real.sinh y * (Real.exp y)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hE]; linarith
      nlinarith [mul_pos hs hs, inv_pos.mpr hE]

lemma inv_sinh_le {y : ℝ} (hy : 1 ≤ y) : 1 / Real.sinh y ≤ 3 * Real.exp (-y) := by
  have hy0 : 0 < y := by linarith
  have hs := Real.sinh_pos_iff.mpr hy0
  have h3 := exp_div_three_le_sinh hy
  have hE := Real.exp_pos y
  have e : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [e, div_le_iff₀ hs]
  have : Real.exp y ≤ 3 * Real.sinh y := by linarith
  calc (1 : ℝ) = (Real.exp y)⁻¹ * Real.exp y := by field_simp
    _ ≤ (Real.exp y)⁻¹ * (3 * Real.sinh y) := by gcongr
    _ = 3 * (Real.exp y)⁻¹ * Real.sinh y := by ring

lemma integrable_ctU3_mul : IntegrableOn (fun y : ℝ => ctU3 y * (Real.cosh y / Real.sinh y ^ 2)) (Ioi 0) := by
  refine integrableOn_Ioi_of_near_far (M := 1) (K := 72) ?_ ?_ ?_
  · refine ContinuousOn.mul (fun y _ => (hasDerivAt_ctU3 y).continuousAt.continuousWithinAt) (fun y hy => ?_)
    have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
    exact ((Real.continuous_cosh.continuousAt.div ((Real.continuous_sinh.continuousAt).pow 2)
      (pow_ne_zero 2 hs))).continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := hy.1
    have hs := Real.sinh_pos_iff.mpr hy0
    have h1 := sinh_gt_self hy0
    have hc := cosh_le_five_near hy0 hy.2
    have hcp := Real.cosh_pos y
    have hu := ctU3_nonneg y
    have hu2 := ctU3_le_sq y
    rw [abs_of_nonneg (by positivity)]
    have hsq : y ^ 2 ≤ Real.sinh y ^ 2 := by nlinarith
    calc ctU3 y * (Real.cosh y / Real.sinh y ^ 2) ≤ (y ^ 2 / 9) * (5 / y ^ 2) := by
          gcongr
      _ = 5 / 9 := by field_simp
      _ ≤ 1 := by norm_num
  · intro y hy
    have hy0 : 0 < y := by linarith
    have hu := ctU3_nonneg y
    have hu2 := ctU3_le_lin hy0
    have hcs := cosh_div_sinh_sq_le (by linarith : 1 ≤ y)
    have hk := pow_mul_exp_neg_le 1 hy0
    have hcp : 0 ≤ Real.cosh y / Real.sinh y ^ 2 := by
      have := Real.cosh_pos y; positivity
    rw [abs_of_nonneg (by positivity)]
    calc ctU3 y * (Real.cosh y / Real.sinh y ^ 2) ≤ (2 * y) * (6 * Real.exp (-y)) := by gcongr
      _ = 12 * (y ^ 1 * Real.exp (-y)) := by ring
      _ ≤ 12 * (((1 + 2).factorial : ℝ) / y ^ 2) := by gcongr
      _ = 72 / y ^ 2 := by norm_num [Nat.factorial]; ring

/-- `w₃(y) = 2y/((π²+y²) sinh y)`. -/
noncomputable def ctW3 (y : ℝ) : ℝ := 2 * y / ((π ^ 2 + y ^ 2) * Real.sinh y)

lemma ctW3_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ ctW3 y := by
  have := Real.sinh_pos_iff.mpr hy
  unfold ctW3; positivity

lemma integrable_ctW3 : IntegrableOn ctW3 (Ioi 0) := by
  have hpi := Real.pi_gt_three
  refine integrableOn_Ioi_of_near_far (M := 1) (K := 6) ?_ ?_ ?_
  · intro y hy
    have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
    have hq : (π ^ 2 + y ^ 2) * Real.sinh y ≠ 0 := mul_ne_zero (by positivity) hs
    unfold ctW3
    exact (ContinuousAt.div (f := fun y : ℝ => 2 * y) (g := fun y : ℝ => (π ^ 2 + y ^ 2) * Real.sinh y)
      (by fun_prop) (by fun_prop) hq).continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := hy.1
    have hs := Real.sinh_pos_iff.mpr hy0
    have h1 := sinh_gt_self hy0
    rw [abs_of_nonneg (ctW3_nonneg hy0)]
    unfold ctW3
    rw [div_le_iff₀ (by positivity)]
    have h9 : 9 ≤ π ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
    nlinarith [mul_le_mul h9 h1.le hy0.le (by positivity)]
  · intro y hy
    have hy0 : 0 < y := by linarith
    have hs := Real.sinh_pos_iff.mpr hy0
    have h1 := inv_sinh_le (by linarith : 1 ≤ y)
    have hk := pow_mul_exp_neg_le 0 hy0
    rw [abs_of_nonneg (ctW3_nonneg hy0)]
    have hfac : 2 * y / (π ^ 2 + y ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (y - π)]
    have e : ctW3 y = (2 * y / (π ^ 2 + y ^ 2)) * (1 / Real.sinh y) := by
      unfold ctW3; field_simp
    rw [e]
    calc (2 * y / (π ^ 2 + y ^ 2)) * (1 / Real.sinh y) ≤ 1 * (3 * Real.exp (-y)) := by
          gcongr
      _ = 3 * (y ^ 0 * Real.exp (-y)) := by ring
      _ ≤ 3 * (((0 + 2).factorial : ℝ) / y ^ 2) := by gcongr
      _ = 6 / y ^ 2 := by norm_num [Nat.factorial]; ring

lemma tendsto_u3v_nhdsGT :
    Tendsto (fun y : ℝ => ctU3 y * (-(Real.sinh y)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_nhdsWithin_of_tendsto_nhds (by
    simpa using ((continuous_id.div_const 9).tendsto (0 : ℝ)) : Tendsto (fun y : ℝ => y / 9) (𝓝 0) (𝓝 0)))
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with y hy
  have hy0 : 0 < y := hy.1
  have hs := Real.sinh_pos_iff.mpr hy0
  have h1 := sinh_gt_self hy0
  have hu := ctU3_nonneg y
  have hu2 := ctU3_le_sq y
  have key : ‖ctU3 y * (-(Real.sinh y)⁻¹)‖ = ctU3 y * (Real.sinh y)⁻¹ := by
    rw [Real.norm_eq_abs, mul_neg, abs_neg, abs_of_nonneg (mul_nonneg hu (inv_nonneg.2 hs.le))]
  rw [key, ← div_eq_mul_inv, div_le_iff₀ hs]
  nlinarith

lemma tendsto_u3v_atTop :
    Tendsto (fun y : ℝ => ctU3 y * (-(Real.sinh y)⁻¹)) atTop (𝓝 0) := by
  have ha : Tendsto (fun y : ℝ => 6 * (y ^ 1 * Real.exp (-y))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 6
  refine squeeze_zero_norm' ?_ ha
  filter_upwards [eventually_gt_atTop 1] with y hy
  have hy0 : 0 < y := by linarith
  have hs := Real.sinh_pos_iff.mpr hy0
  have hu := ctU3_nonneg y
  have hu2 := ctU3_le_lin hy0
  have h1 := inv_sinh_le hy.le
  have key : ‖ctU3 y * (-(Real.sinh y)⁻¹)‖ = ctU3 y * (1 / Real.sinh y) := by
    rw [Real.norm_eq_abs, mul_neg, abs_neg, one_div, abs_of_nonneg (mul_nonneg hu (inv_nonneg.2 hs.le))]
  rw [key]
  calc ctU3 y * (1 / Real.sinh y) ≤ (2 * y) * (3 * Real.exp (-y)) := by gcongr
    _ = 6 * (y ^ 1 * Real.exp (-y)) := by ring

/-- `∫_0^∞ log(1+(y/π)²) cosh y/sinh² y dy = ∫_0^∞ 2y/((π²+y²) sinh y) dy` (integration by parts). -/
theorem integral_ctU3_mul_eq :
    ∫ y in Ioi (0 : ℝ), ctU3 y * (Real.cosh y / Real.sinh y ^ 2) = ∫ y in Ioi (0 : ℝ), ctW3 y := by
  have hu : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt ctU3 (2 * y / (π ^ 2 + y ^ 2)) y := fun y _ => hasDerivAt_ctU3 y
  have hv : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -(Real.sinh y)⁻¹) (Real.cosh y / Real.sinh y ^ 2) y :=
    fun y hy => hasDerivAt_negInvSinh hy
  have huv' : IntegrableOn (ctU3 * fun y : ℝ => Real.cosh y / Real.sinh y ^ 2) (Ioi 0) := integrable_ctU3_mul
  have hu'v : IntegrableOn ((fun y : ℝ => 2 * y / (π ^ 2 + y ^ 2)) * fun y : ℝ => -(Real.sinh y)⁻¹) (Ioi 0) := by
    refine (integrable_ctW3.neg).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := hy
    simp only [Pi.mul_apply, Pi.neg_apply, ctW3]
    field_simp
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v
    (tendsto_u3v_nhdsGT : Tendsto (ctU3 * fun y : ℝ => -(Real.sinh y)⁻¹) (𝓝[>] 0) (𝓝 0))
    (tendsto_u3v_atTop : Tendsto (ctU3 * fun y : ℝ => -(Real.sinh y)⁻¹) atTop (𝓝 0))
  rw [h]
  have e2 : ∫ y in Ioi (0 : ℝ), (2 * y / (π ^ 2 + y ^ 2)) * -(Real.sinh y)⁻¹ =
      -∫ y in Ioi (0 : ℝ), ctW3 y := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : 0 < y := hy
    simp only [ctW3]
    field_simp
  rw [e2]; ring

/-- `K' = ∫_0^∞ 2y/((π²+y²) sinh y) dy = 2 log 2 - 1`. -/
theorem integral_ctW3 : ∫ y in Ioi (0 : ℝ), ctW3 y = 2 * Real.log 2 - 1 := by
  have hpi := Real.pi_pos
  have hsub := integral_comp_mul_left_Ioi' (E := ℝ) ctW3 0 hpi
  rw [mul_zero, smul_eq_mul] at hsub
  rw [← hsub]
  have hlog : (0 : ℝ) < 1 - Real.log 2 := by
    have := Real.log_two_lt_d9; linarith
  have hint : IntegrableOn (fun t : ℝ => t * mPrime t / (1 + t ^ 2)) (Ioi 0) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_t_mPrime_div]; positivity
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ctW3 (π * t) = (2 / π ^ 2) * (1 / (1 + t ^ 2) - t * mPrime t / (1 + t ^ 2)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hs : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    unfold ctW3 mPrime
    field_simp
    ring
  have e : ∫ t in Ioi (0 : ℝ), ctW3 (π * t) =
      ∫ t in Ioi (0 : ℝ), (2 / π ^ 2) * (1 / (1 + t ^ 2) - t * mPrime t / (1 + t ^ 2)) :=
    setIntegral_congr_fun measurableSet_Ioi hpt
  rw [e, integral_const_mul, integral_sub integrableOn_inv_one_add_sq hint, integral_inv_one_add_sq_Ioi,
    integral_t_mPrime_div]
  field_simp
  ring

/-- **`∫_0^∞ log(1+(y/π)²) cosh y/sinh² y dy = 2 log 2 - 1`.** -/
theorem integral_ctU3_mul : ∫ y in Ioi (0 : ℝ), ctU3 y * (Real.cosh y / Real.sinh y ^ 2) = 2 * Real.log 2 - 1 := by
  rw [integral_ctU3_mul_eq, integral_ctW3]

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_ctU3_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_ctU3_mul

end FormalResearch.SignUncertainty.CtOuter
