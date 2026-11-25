module

public import FormalResearch.SignUncertainty.CtOuterSinhIneq
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `∫_0^∞ y⁻¹ (1/sinh y - 1/y) dy = -log 2` (Frullani), `ct:outer` (2), evaluation of `a_mp`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (2) ("Evaluation of `a_mp`":
`J_1 = ∫_0^∞ (1/y)(1/sinh y - 1/y) dy = -log 2`, via `1/sinh y = coth(y/2) - coth y` and Frullani's theorem).
**Proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `F(u) = coth u - 1/u`. -/
noncomputable def ctCothSub (u : ℝ) : ℝ := Real.cosh u / Real.sinh u - 1 / u

lemma ctCothSub_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ ctCothSub u := by
  unfold ctCothSub
  have hs := Real.sinh_pos_iff.mpr hu
  have h := sinh_lt_mul_cosh hu
  rw [sub_nonneg, div_le_div_iff₀ hu hs]
  linarith

lemma ctCothSub_le_self {u : ℝ} (hu : 0 < u) : ctCothSub u ≤ u := by
  unfold ctCothSub
  have hs := Real.sinh_pos_iff.mpr hu
  have h := mul_cosh_sub_sinh_le hu.le
  have e : Real.cosh u / Real.sinh u - 1 / u = (u * Real.cosh u - Real.sinh u) / (u * Real.sinh u) := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith

lemma ctCothSub_continuousOn : ContinuousOn ctCothSub (Ioi 0) := by
  intro u hu
  have hu' : 0 < u := hu
  have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.mpr hu').ne'
  unfold ctCothSub
  exact ((Real.continuous_cosh.continuousAt.div Real.continuous_sinh.continuousAt hs).sub
    (continuousAt_const.div continuousAt_id hu'.ne')).continuousWithinAt

lemma ctCothSub_tendsto_zero : Tendsto ctCothSub (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto (0 : ℝ)) : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u hu using ctCothSub_nonneg hu
  · filter_upwards [self_mem_nhdsWithin] with u hu using ctCothSub_le_self hu

lemma ctCothSub_tendsto_one : Tendsto ctCothSub atTop (𝓝 1) := by
  have hq : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h1 : Tendsto (fun u : ℝ => (1 + Real.exp (-(2 * u))) / (1 - Real.exp (-(2 * u)))) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hq).div ((tendsto_const_nhds (x := (1 : ℝ))).sub hq) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [add_zero, sub_zero, div_one] at this
    exact this
  have h2 : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero
  have h3 := h1.sub h2
  simp only [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  unfold ctCothSub
  congr 1
  have hq0 : Real.exp (-u) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.cosh_eq, Real.sinh_eq]
  have e : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hlt : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [e]
  have h4 : 1 - Real.exp (-u) * Real.exp (-u) ≠ 0 := by nlinarith [Real.exp_pos (-u)]
  have h5 : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have : Real.exp u = Real.exp (-u) := by linarith
    have := Real.exp_lt_exp.mpr (show -u < u by linarith)
    linarith
  rw [div_eq_div_iff h4 (by simpa using h5)]
  nlinarith [hE]

lemma ctCothSub_half_sub {y : ℝ} (hy : 0 < y) :
    ctCothSub (y / 2) - ctCothSub y = 1 / Real.sinh y - 1 / y := by
  unfold ctCothSub
  have hs : 0 < Real.sinh (y / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hc : 0 < Real.cosh (y / 2) := Real.cosh_pos _
  have h2 : Real.sinh y = 2 * Real.sinh (y / 2) * Real.cosh (y / 2) := by
    rw [← Real.sinh_two_mul]; congr 1; ring
  have h3 : Real.cosh y = Real.cosh (y / 2) ^ 2 + Real.sinh (y / 2) ^ 2 := by
    rw [← Real.cosh_two_mul]; congr 1; ring
  have h4 := Real.cosh_sq (y / 2)
  have hys : y ≠ 0 := hy.ne'
  rw [h3, h2]
  have e : 2 / y = 1 / (y / 2) := by field_simp
  field_simp
  nlinarith [h4]

/-- Integrability on `(0, ∞)` from a bound on `(0, 2]` and a `K/y²` bound on `(2, ∞)`. -/
lemma integrableOn_Ioi_of_near_far {f : ℝ → ℝ} (hcont : ContinuousOn f (Ioi 0)) {M K : ℝ}
    (hnear : ∀ y ∈ Ioc (0 : ℝ) 2, |f y| ≤ M) (hfar : ∀ y : ℝ, 2 < y → |f y| ≤ K / y ^ 2) :
    IntegrableOn f (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 2 ∪ Ioi 2 := by
    ext y; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h; by_cases h2 : y ≤ 2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (not_le.mp h2)
    · rintro (h | h)
      · exact h.1
      · linarith
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (integrableOn_const (C := M) (by simp)) ?_ ?_
    · exact (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      rw [Real.norm_eq_abs]; exact hnear y hy
  · have hint : IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul K
    refine Integrable.mono' hint ?_ ?_
    · exact (hcont.mono (fun y hy => lt_trans (by norm_num) hy)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Real.norm_eq_abs]
      refine (hfar y hy).trans (le_of_eq ?_)
      rw [Real.rpow_neg (by linarith [mem_Ioi.mp hy]), Real.rpow_two]
      ring

lemma abs_invSinhSub_le_near {y : ℝ} (hy0 : 0 < y) (hy2 : y ≤ 2) : |1 / Real.sinh y - 1 / y| ≤ y / 4 := by
  have hs := Real.sinh_pos_iff.mpr hy0
  have h1 := sinh_gt_self hy0
  have h2 := sinh_sub_le_cube hy0 hy2
  have e : 1 / Real.sinh y - 1 / y = -((Real.sinh y - y) / (y * Real.sinh y)) := by field_simp; ring
  rw [e, abs_neg, abs_of_nonneg (by apply div_nonneg <;> nlinarith)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hy0 hs]

lemma abs_invSinhSub_le_far {y : ℝ} (hy0 : 0 < y) : |1 / Real.sinh y - 1 / y| ≤ 1 / y := by
  have hs := Real.sinh_pos_iff.mpr hy0
  have h1 := sinh_gt_self hy0
  have h3 : 0 < 1 / y := by positivity
  have h4 : 0 < 1 / Real.sinh y := by positivity
  have h5 : 1 / Real.sinh y ≤ 1 / y := one_div_le_one_div_of_le hy0 h1.le
  rw [abs_le]
  constructor <;> linarith

lemma integrable_inv_mul_invSinhSub :
    IntegrableOn (fun y : ℝ => y⁻¹ * (1 / Real.sinh y - 1 / y)) (Ioi 0) := by
    refine integrableOn_Ioi_of_near_far (M := 1 / 4) (K := 1) ?_ ?_ ?_
    · intro y hy
      have hy' : 0 < y := hy
      have hs : Real.sinh y ≠ 0 := (Real.sinh_pos_iff.mpr hy').ne'
      exact ((continuousAt_inv₀ hy'.ne').mul ((continuousAt_const.div Real.continuous_sinh.continuousAt hs).sub
        (continuousAt_const.div continuousAt_id hy'.ne'))).continuousWithinAt
    · intro y hy
      have hy0 : 0 < y := hy.1
      rw [abs_mul, abs_inv, abs_of_pos hy0]
      have := abs_invSinhSub_le_near hy0 hy.2
      calc y⁻¹ * |1 / Real.sinh y - 1 / y| ≤ y⁻¹ * (y / 4) := by gcongr
        _ = 1 / 4 := by field_simp
    · intro y hy
      have hy0 : 0 < y := by linarith
      rw [abs_mul, abs_inv, abs_of_pos hy0]
      have := abs_invSinhSub_le_far hy0
      calc y⁻¹ * |1 / Real.sinh y - 1 / y| ≤ y⁻¹ * (1 / y) := by gcongr
        _ = 1 / y ^ 2 := by field_simp

/-- **Frullani evaluation:** `∫_0^∞ y⁻¹ (1/sinh y - 1/y) dy = -log 2`. -/
theorem integral_inv_mul_invSinh_sub : ∫ y in Ioi (0 : ℝ), y⁻¹ * (1 / Real.sinh y - 1 / y) = -Real.log 2 := by
  have hint := integrable_inv_mul_invSinhSub
  have hF := Frullani.integral_Ioi_eq (f := ctCothSub) (a := 1 / 2) (b := 1) (L := 0) (R := 1)
    (ctCothSub_continuousOn.locallyIntegrableOn measurableSet_Ioi) (by norm_num) (by norm_num)
    ctCothSub_tendsto_zero ctCothSub_tendsto_one (by
      refine hint.congr_fun (fun y hy => ?_) measurableSet_Ioi
      have hy0 : 0 < y := hy
      rw [smul_eq_mul, one_mul, show (1 / 2 : ℝ) * y = y / 2 by ring, ctCothSub_half_sub hy0])
  have e : ∫ y in Ioi (0 : ℝ), y⁻¹ • (ctCothSub (1 / 2 * y) - ctCothSub (1 * y)) =
      ∫ y in Ioi (0 : ℝ), y⁻¹ * (1 / Real.sinh y - 1 / y) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : 0 < y := hy
    simp only [smul_eq_mul, one_mul]
    rw [show (1 / 2 : ℝ) * y = y / 2 by ring, ctCothSub_half_sub hy0]
  rw [← e, hF]
  simp

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_inv_mul_invSinh_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_inv_mul_invSinh_sub

end FormalResearch.SignUncertainty.CtOuter
