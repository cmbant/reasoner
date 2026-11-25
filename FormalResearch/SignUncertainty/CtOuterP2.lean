module

public import FormalResearch.SignUncertainty.CtOuterFrullani

/-!
# `∫_0^∞ log(y/sinh y) cosh y / sinh² y dy = -log 2`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (2) ("Evaluation of `a_mp`",
the integral `J_1`): integration by parts and the Frullani integral `integral_inv_mul_invSinh_sub`.  **Proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma ctCothSub_le_one {y : ℝ} (hy : 0 < y) : ctCothSub y ≤ 1 := by
  unfold ctCothSub
  have hs := Real.sinh_pos_iff.mpr hy
  have h1 := sinh_gt_self hy
  have e : Real.cosh y / Real.sinh y - 1 / y = (y * Real.cosh y - Real.sinh y) / (y * Real.sinh y) := by
    field_simp
  rw [e, div_le_one (by positivity)]
  have h2 : Real.cosh y - Real.sinh y = Real.exp (-y) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  have h3 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h4 : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
  nlinarith

lemma pow_mul_exp_neg_le (k : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ k * Real.exp (-y) ≤ ((k + 2).factorial : ℝ) / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp y hy.le (k + 2)
  have hE : 0 < Real.exp y := Real.exp_pos y
  have e : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [e, le_div_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h
  calc y ^ k * (Real.exp y)⁻¹ * y ^ 2 = y ^ (k + 2) * (Real.exp y)⁻¹ := by ring
    _ ≤ (k + 2).factorial * Real.exp y * (Real.exp y)⁻¹ := by
        have : y ^ (k + 2) ≤ (k + 2).factorial * Real.exp y := by
          have h' := h; rw [mul_comm] at h'; exact h'
        gcongr
    _ = (k + 2).factorial := by field_simp

lemma cosh_le_two_sinh {y : ℝ} (hy : 1 ≤ y) : Real.cosh y ≤ 2 * Real.sinh y := by
  have h2 : Real.cosh y - Real.sinh y = Real.exp (-y) := by rw [Real.cosh_eq, Real.sinh_eq]; ring
  have h3 : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  have h5 : Real.exp y / 3 ≤ Real.sinh y := exp_div_three_le_sinh hy
  have h6 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  linarith

/-- `-log(y/sinh y) = log(sinh y / y)`, bounds. -/
lemma neg_log_ratio_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ -Real.log (y / Real.sinh y) := by
  have hs := Real.sinh_pos_iff.mpr hy
  have h1 := sinh_gt_self hy
  rw [neg_nonneg]
  apply Real.log_nonpos (by positivity)
  rw [div_le_one hs]; exact h1.le

lemma neg_log_ratio_le_near {y : ℝ} (hy : 0 < y) (hy2 : y ≤ 2) : -Real.log (y / Real.sinh y) ≤ y ^ 2 / 4 := by
  have hs := Real.sinh_pos_iff.mpr hy
  have h2 := sinh_sub_le_cube hy hy2
  have : -Real.log (y / Real.sinh y) = Real.log (Real.sinh y / y) := by
    rw [← Real.log_inv, inv_div]
  rw [this]
  calc Real.log (Real.sinh y / y) ≤ Real.sinh y / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ ≤ y ^ 2 / 4 := by
        rw [show Real.sinh y / y - 1 = (Real.sinh y - y) / y by field_simp, div_le_iff₀ hy]
        nlinarith

lemma neg_log_ratio_le_self {y : ℝ} (hy : 0 < y) : -Real.log (y / Real.sinh y) ≤ y := by
  have hs := Real.sinh_pos_iff.mpr hy
  have h1 := sinh_lt_mul_cosh hy
  have : -Real.log (y / Real.sinh y) = Real.log (Real.sinh y / y) := by
    rw [← Real.log_inv, inv_div]
  rw [this, Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hy]
  have : Real.cosh y ≤ Real.exp y := by
    rw [Real.cosh_eq]; have := Real.exp_pos (-y)
    have h := Real.exp_le_exp.mpr (show -y ≤ y by linarith)
    linarith
  nlinarith

/-- `log(y / sinh y)`. -/
noncomputable def ctLogRatio (y : ℝ) : ℝ := Real.log (y / Real.sinh y)

lemma hasDerivAt_ctLogRatio {y : ℝ} (hy : 0 < y) :
    HasDerivAt ctLogRatio (1 / y - Real.cosh y / Real.sinh y) y := by
  have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
  have h1 : HasDerivAt (fun y : ℝ => y / Real.sinh y) ((1 * Real.sinh y - y * Real.cosh y) / Real.sinh y ^ 2) y :=
    (hasDerivAt_id y).div (Real.hasDerivAt_sinh y) hs
  have h2 := h1.log (div_ne_zero hy.ne' hs)
  refine h2.congr_deriv ?_
  field_simp

lemma hasDerivAt_negInvSinh {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => -(Real.sinh y)⁻¹) (Real.cosh y / Real.sinh y ^ 2) y := by
  have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
  have := ((Real.hasDerivAt_sinh y).inv hs).neg
  refine this.congr_deriv ?_
  field_simp

lemma continuousOn_ctLogRatio : ContinuousOn ctLogRatio (Ioi 0) := fun _ hy =>
  (hasDerivAt_ctLogRatio hy).continuousAt.continuousWithinAt

lemma cosh_le_five_near {y : ℝ} (hy0 : 0 < y) (hy2 : y ≤ 2) : Real.cosh y ≤ 5 := by
  have h2 : Real.cosh y - Real.sinh y = Real.exp (-y) := by rw [Real.cosh_eq, Real.sinh_eq]; ring
  have h3 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h4 : Real.sinh y ≤ Real.sinh 2 := Real.sinh_le_sinh.mpr hy2
  have := sinh_two_lt
  linarith

lemma integrable_ctLogRatio_mul : IntegrableOn (fun y : ℝ => ctLogRatio y * (Real.cosh y / Real.sinh y ^ 2)) (Ioi 0) := by
  refine integrableOn_Ioi_of_near_far (M := 5 / 4) (K := 36) ?_ ?_ ?_
  · exact continuousOn_ctLogRatio.mul (fun y hy => by
      have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
      exact ((Real.continuous_cosh.continuousAt.div ((Real.continuous_sinh.continuousAt).pow 2) (pow_ne_zero 2 hs))).continuousWithinAt)
  · intro y hy
    have hy0 : 0 < y := hy.1
    have hs := Real.sinh_pos_iff.mpr hy0
    have h1 := sinh_gt_self hy0
    have hu := neg_log_ratio_nonneg hy0
    have hu2 := neg_log_ratio_le_near hy0 hy.2
    have hc := cosh_le_five_near hy0 hy.2
    have hcp := Real.cosh_pos y
    rw [abs_mul, ctLogRatio, ← abs_neg, abs_of_nonneg hu, abs_of_pos (by positivity)]
    have hsq : y ^ 2 ≤ Real.sinh y ^ 2 := by nlinarith
    calc (-Real.log (y / Real.sinh y)) * (Real.cosh y / Real.sinh y ^ 2)
        ≤ (y ^ 2 / 4) * (5 / y ^ 2) := by
          gcongr
      _ = 5 / 4 := by field_simp
  · intro y hy
    have hy0 : 0 < y := by linarith
    have hs := Real.sinh_pos_iff.mpr hy0
    have hu := neg_log_ratio_nonneg hy0
    have hu2 := neg_log_ratio_le_self hy0
    have hcp := Real.cosh_pos y
    have h2 := cosh_le_two_sinh (by linarith : 1 ≤ y)
    have h3 := exp_div_three_le_sinh (by linarith : 1 ≤ y)
    rw [abs_mul, ctLogRatio, ← abs_neg, abs_of_nonneg hu, abs_of_pos (by positivity)]
    have hk := pow_mul_exp_neg_le 1 hy0
    have hcs : Real.cosh y / Real.sinh y ^ 2 ≤ 6 * Real.exp (-y) := by
      rw [div_le_iff₀ (by positivity)]
      have e : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
      have hE := Real.exp_pos y
      have : Real.exp y ≤ 3 * Real.sinh y := by linarith
      calc Real.cosh y ≤ 2 * Real.sinh y := h2
        _ ≤ 6 * Real.exp (-y) * Real.sinh y ^ 2 := by
          rw [e]
          have : 1 ≤ 3 * Real.sinh y * (Real.exp y)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ hE]; linarith
          nlinarith [mul_pos hs hs, inv_pos.mpr hE]
    calc (-Real.log (y / Real.sinh y)) * (Real.cosh y / Real.sinh y ^ 2)
        ≤ y * (6 * Real.exp (-y)) := by gcongr
      _ = 6 * (y ^ 1 * Real.exp (-y)) := by ring
      _ ≤ 6 * (((1 + 2).factorial : ℝ) / y ^ 2) := by gcongr
      _ = 36 / y ^ 2 := by norm_num [Nat.factorial]; ring

lemma integrable_ctCothSub_div_sinh : IntegrableOn (fun y : ℝ => ctCothSub y / Real.sinh y) (Ioi 0) := by
  refine integrableOn_Ioi_of_near_far (M := 1) (K := 6) ?_ ?_ ?_
  · exact ctCothSub_continuousOn.div Real.continuous_sinh.continuousOn
      (fun y hy => (Real.sinh_pos_iff.mpr hy).ne')
  · intro y hy
    have hy0 : 0 < y := hy.1
    have hs := Real.sinh_pos_iff.mpr hy0
    have h1 := sinh_gt_self hy0
    rw [abs_of_nonneg (div_nonneg (ctCothSub_nonneg hy0) hs.le), div_le_iff₀ hs]
    have := ctCothSub_le_self hy0
    linarith
  · intro y hy
    have hy0 : 0 < y := by linarith
    have hs := Real.sinh_pos_iff.mpr hy0
    have h3 := exp_div_three_le_sinh (by linarith : 1 ≤ y)
    rw [abs_of_nonneg (div_nonneg (ctCothSub_nonneg hy0) hs.le)]
    have hF := ctCothSub_le_one hy0
    have hk := pow_mul_exp_neg_le 0 hy0
    have hE := Real.exp_pos y
    have e : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
    calc ctCothSub y / Real.sinh y ≤ 1 / Real.sinh y := by gcongr
      _ ≤ 3 * Real.exp (-y) := by
          rw [e, div_le_iff₀ hs]
          have : 1 ≤ 3 * (Real.exp y)⁻¹ * Real.sinh y := by
            have : Real.exp y ≤ 3 * Real.sinh y := by linarith
            calc (1 : ℝ) = (Real.exp y)⁻¹ * Real.exp y := by field_simp
              _ ≤ (Real.exp y)⁻¹ * (3 * Real.sinh y) := by gcongr
              _ = 3 * (Real.exp y)⁻¹ * Real.sinh y := by ring
          linarith
      _ = 3 * (y ^ 0 * Real.exp (-y)) := by ring
      _ ≤ 3 * (((0 + 2).factorial : ℝ) / y ^ 2) := by gcongr
      _ = 6 / y ^ 2 := by norm_num [Nat.factorial]; ring

lemma tendsto_uv_zero_nhdsGT :
    Tendsto (fun y : ℝ => ctLogRatio y * (-(Real.sinh y)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_nhdsWithin_of_tendsto_nhds (by
    simpa using ((continuous_id.div_const 4).tendsto (0 : ℝ)) : Tendsto (fun y : ℝ => y / 4) (𝓝 0) (𝓝 0)))
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with y hy
  have hy0 : 0 < y := hy.1
  have hs := Real.sinh_pos_iff.mpr hy0
  have h1 := sinh_gt_self hy0
  have hu := neg_log_ratio_nonneg hy0
  have hu2 := neg_log_ratio_le_near hy0 hy.2
  have key : ‖ctLogRatio y * (-(Real.sinh y)⁻¹)‖ = (-Real.log (y / Real.sinh y)) * (Real.sinh y)⁻¹ := by
    have : ctLogRatio y * (-(Real.sinh y)⁻¹) = (-Real.log (y / Real.sinh y)) * (Real.sinh y)⁻¹ := by
      unfold ctLogRatio; ring
    rw [Real.norm_eq_abs, this, abs_of_nonneg (mul_nonneg hu (inv_nonneg.2 hs.le))]
  rw [key, ← div_eq_mul_inv, div_le_iff₀ hs]
  nlinarith

lemma tendsto_uv_zero_atTop :
    Tendsto (fun y : ℝ => ctLogRatio y * (-(Real.sinh y)⁻¹)) atTop (𝓝 0) := by
  have ha : Tendsto (fun y : ℝ => 3 * (y ^ 1 * Real.exp (-y))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 3
  refine squeeze_zero_norm' ?_ ha
  filter_upwards [eventually_gt_atTop 1] with y hy
  have hy0 : 0 < y := by linarith
  have hs := Real.sinh_pos_iff.mpr hy0
  have hu := neg_log_ratio_nonneg hy0
  have hu2 := neg_log_ratio_le_self hy0
  have h3 := exp_div_three_le_sinh hy.le
  have hE := Real.exp_pos y
  have e : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  have key : ‖ctLogRatio y * (-(Real.sinh y)⁻¹)‖ = (-Real.log (y / Real.sinh y)) * (Real.sinh y)⁻¹ := by
    have : ctLogRatio y * (-(Real.sinh y)⁻¹) = (-Real.log (y / Real.sinh y)) * (Real.sinh y)⁻¹ := by
      unfold ctLogRatio; ring
    rw [Real.norm_eq_abs, this, abs_of_nonneg (mul_nonneg hu (inv_nonneg.2 hs.le))]
  rw [key]
  calc (-Real.log (y / Real.sinh y)) * (Real.sinh y)⁻¹ ≤ y * (Real.sinh y)⁻¹ := by gcongr
    _ ≤ y * (3 * Real.exp (-y)) := by
        gcongr
        rw [e]
        have : Real.exp y ≤ 3 * Real.sinh y := by linarith
        rw [inv_le_comm₀ hs (by positivity), mul_inv, inv_inv]
        linarith
    _ = 3 * (y ^ 1 * Real.exp (-y)) := by ring

/-- `D(y) = 1/sinh y - 1/y`. -/
noncomputable def ctInvSinhSub (y : ℝ) : ℝ := 1 / Real.sinh y - 1 / y

lemma hasDerivAt_ctInvSinhSub {y : ℝ} (hy : 0 < y) :
    HasDerivAt ctInvSinhSub (1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2) y := by
  have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
  have h1 : HasDerivAt (fun y : ℝ => 1 / Real.sinh y) (-(Real.cosh y) / Real.sinh y ^ 2) y := by
    have := (hasDerivAt_const y (1 : ℝ)).div (Real.hasDerivAt_sinh y) hs
    refine this.congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / y ^ 2)) y := by
    have := (hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_id y) hy.ne'
    refine this.congr_deriv ?_
    simp only [id]; ring
  have := h1.sub h2
  refine this.congr_deriv ?_
  ring

lemma ctInvSinhSub_deriv_eq {y : ℝ} (hy : 0 < y) :
    1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2 = -(y⁻¹ * (1 / Real.sinh y - 1 / y)) - ctCothSub y / Real.sinh y := by
  have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy).ne'
  unfold ctCothSub
  field_simp
  ring

lemma ctInvSinhSub_tendsto_zero_nhdsGT : Tendsto ctInvSinhSub (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_nhdsWithin_of_tendsto_nhds (by
    simpa using ((continuous_id.div_const 4).tendsto (0 : ℝ)) : Tendsto (fun y : ℝ => y / 4) (𝓝 0) (𝓝 0)))
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with y hy
  rw [Real.norm_eq_abs]
  exact abs_invSinhSub_le_near hy.1 hy.2

lemma ctInvSinhSub_tendsto_zero_atTop : Tendsto ctInvSinhSub atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using tendsto_inv_atTop_zero (𝕜 := ℝ))
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [Real.norm_eq_abs]
  simpa [ctInvSinhSub, one_div] using abs_invSinhSub_le_far hy

lemma integrable_deriv_ctInvSinhSub :
    IntegrableOn (fun y : ℝ => 1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2) (Ioi 0) := by
  have := (integrable_inv_mul_invSinhSub.neg.add integrable_ctCothSub_div_sinh.neg)
  refine (IntegrableOn.congr_fun this ?_ measurableSet_Ioi)
  intro y hy
  simp only [Pi.add_apply, Pi.neg_apply]
  rw [ctInvSinhSub_deriv_eq hy]; ring

lemma integral_deriv_ctInvSinhSub :
    ∫ y in Ioi (0 : ℝ), (1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2) = 0 := by
  have hint := integrable_deriv_ctInvSinhSub
  have hcont : ContinuousWithinAt ctInvSinhSub (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h0 : ctInvSinhSub 0 = 0 := by simp [ctInvSinhSub]
    unfold ContinuousWithinAt
    rw [h0]
    exact ctInvSinhSub_tendsto_zero_nhdsGT
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x hx => hasDerivAt_ctInvSinhSub hx) hint
    ctInvSinhSub_tendsto_zero_atTop
  rw [this]; simp [ctInvSinhSub]

/-- **`J_1 = ∫_0^∞ log(y/sinh y) cosh y/sinh² y dy = -log 2`.** -/
theorem integral_log_ratio_mul_cosh_div_sinh_sq :
    ∫ y in Ioi (0 : ℝ), Real.log (y / Real.sinh y) * (Real.cosh y / Real.sinh y ^ 2) = -Real.log 2 := by
  have hu : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt ctLogRatio (1 / y - Real.cosh y / Real.sinh y) y :=
    fun y hy => hasDerivAt_ctLogRatio hy
  have hv : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => -(Real.sinh y)⁻¹) (Real.cosh y / Real.sinh y ^ 2) y :=
    fun y hy => hasDerivAt_negInvSinh hy
  have huv' : IntegrableOn ((ctLogRatio) * fun y : ℝ => Real.cosh y / Real.sinh y ^ 2) (Ioi 0) :=
    integrable_ctLogRatio_mul
  have hu'v : IntegrableOn ((fun y : ℝ => 1 / y - Real.cosh y / Real.sinh y) * fun y : ℝ => -(Real.sinh y)⁻¹) (Ioi 0) := by
    refine integrable_ctCothSub_div_sinh.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, ctCothSub]
    ring
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v
    (tendsto_uv_zero_nhdsGT : Tendsto (ctLogRatio * fun y : ℝ => -(Real.sinh y)⁻¹) (𝓝[>] 0) (𝓝 0))
    (tendsto_uv_zero_atTop : Tendsto (ctLogRatio * fun y : ℝ => -(Real.sinh y)⁻¹) atTop (𝓝 0))
  have e1 : ∫ y in Ioi (0 : ℝ), Real.log (y / Real.sinh y) * (Real.cosh y / Real.sinh y ^ 2) =
      ∫ y in Ioi (0 : ℝ), ctLogRatio y * (Real.cosh y / Real.sinh y ^ 2) := rfl
  rw [e1, h]
  have e2 : ∫ y in Ioi (0 : ℝ), (1 / y - Real.cosh y / Real.sinh y) * (-(Real.sinh y)⁻¹) =
      ∫ y in Ioi (0 : ℝ), ctCothSub y / Real.sinh y := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    simp only [ctCothSub]
    ring
  rw [e2]
  have e3 : ∫ y in Ioi (0 : ℝ), ctCothSub y / Real.sinh y =
      -(∫ y in Ioi (0 : ℝ), y⁻¹ * (1 / Real.sinh y - 1 / y)) -
        ∫ y in Ioi (0 : ℝ), (1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2) := by
    have := integral_sub (integrable_inv_mul_invSinhSub.neg) integrable_deriv_ctInvSinhSub
    have hneg : (∫ a in Ioi (0 : ℝ), (-fun y : ℝ => y⁻¹ * (1 / Real.sinh y - 1 / y)) a) =
        -∫ a in Ioi (0 : ℝ), a⁻¹ * (1 / Real.sinh a - 1 / a) := by
      simp only [Pi.neg_apply]; exact integral_neg _
    rw [hneg] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    simp only [Pi.neg_apply]
    have := ctInvSinhSub_deriv_eq hy
    linarith
  rw [e3, integral_deriv_ctInvSinhSub, integral_inv_mul_invSinh_sub]
  ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_log_ratio_mul_cosh_div_sinh_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_log_ratio_mul_cosh_div_sinh_sq

end FormalResearch.SignUncertainty.CtOuter
