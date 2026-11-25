module

public import FormalResearch.ModularBootstrap.Constants
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Slit-strip boundary geometry, Lemma E, Lemma S, deficit bound, Proposition M, and Theorem A

Formalizes `CFT/modular_bootstrap/paper/log_free_optimality.tex`:

1. **Slit-strip boundary geometry & fold involution (`sigmaStar`, `sigmaPlus`, `slitBoundaryMap`,
   `slitInv`, `invJacobian`):** `slitInv_mem_Ioo`, `slitInv_slitInv`, `slitInv_sigmaStar`,
   `slitBoundaryMap_slitInv`, `slitInv_sub_sigmaStar_eq`, distance ratio bounds,
   `hasDerivAt_slitBoundaryMap`, `invJacobian_le`.
2. **Upper half-plane Poisson kernel & Lemma E:** `poissonKernel`, `integral_poissonKernel`,
   `lemmaE_complex`, `lemmaE_real`.
3. **Lemma S (sharp slit harmonic-measure entropy bound):** `lemmaS_poisson_log_bound`,
   `lemmaS_poisson_log_unit_bound`, `lemmaS_complex`, `lemmaS_real`.
4. **Exact deficit lower bound (`slitDeficit`):** `arccos_ge_sqrt_two_mul_one_sub`,
   `one_sub_sinh_pi_ge`, `slitDeficit_ge_exact`, `slitDeficit_ge`.
5. **Proposition M, Theorem A, and non-vacuity:** `RealSliceData`, `PoissonJensenInput`,
   `FixedGapInput`, `WeaklyFeasibleTest`, `proposition_M`, `theorem_A`,
   `slitStrip_hypotheses_nonvacuous`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal Interval

namespace FormalResearch.ModularBootstrap

/-! ### Elementary numerical bounds and helper lemmas -/

private lemma sqrt_two_gt_1414 : (1.414 : ℝ) < √2 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.414)]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma sqrt_two_lt_1415 : √2 < (1.415 : ℝ) := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.415)]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma xiStar_gt_005 : (0.05 : ℝ) < xiStar := by
  unfold xiStar
  rw [lt_div_iff₀ Real.pi_pos, ← Real.sinh_lt_sinh, Real.sinh_arsinh]
  have hmono : Real.sinh (0.05 * π) < Real.sinh 0.16 :=
    Real.sinh_strictMono (by nlinarith [Real.pi_lt_d4])
  have hexp_neg : (0.84 : ℝ) ≤ Real.exp (-0.16) := by linarith [Real.add_one_le_exp (-0.16 : ℝ)]
  have hexp_pos : Real.exp (0.16 : ℝ) ≤ (1 - 0.16)⁻¹ := by
    have h1 : 1 - (0.16 : ℝ) ≤ (Real.exp 0.16)⁻¹ := by rw [← Real.exp_neg]; linarith
    exact (inv_inv (Real.exp 0.16)).symm.trans_le (inv_anti₀ (by norm_num) h1)
  have hsinh_ub : Real.sinh (0.16 : ℝ) < 1 := by
    rw [Real.sinh_eq]; norm_num at hexp_pos hexp_neg ⊢; linarith
  exact hmono.trans hsinh_ub

lemma xiStar_lt_one : xiStar < 1 := by
  unfold xiStar
  rw [div_lt_one Real.pi_pos, ← Real.sinh_lt_sinh, Real.sinh_arsinh]
  have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (8 : ℝ) < Real.exp 3 := by
    have h3 : (2 : ℝ) ^ 3 < Real.exp 1 ^ 3 := by gcongr
    have hexp3 : Real.exp 1 ^ 3 = Real.exp 3 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
    linarith
  have h3 : Real.exp 3 < Real.exp π := Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_d4])
  have h4 : Real.exp (-π) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  rw [Real.sinh_eq]; linarith

private lemma posLog_add_le_single {a c : ℝ} (ha : 0 ≤ a) :
    max 0 (a + c) ≤ a + max 0 c := by
  rcases le_total (a + c) 0 with h | h
  · rw [max_eq_left h]; linarith [le_max_left 0 c]
  · rw [max_eq_right h]; linarith [le_max_right 0 c]

private lemma posLog_mul_le_posLog_add {a b : ℝ} (ha : 0 ≤ a) :
    max 0 (Real.log (a * b)) ≤ max 0 (Real.log a) + max 0 (Real.log b) := by
  by_cases ha0 : a = 0
  · subst ha0; simp
  by_cases hb0 : b = 0
  · subst hb0; simp
  rw [Real.log_mul ha0 hb0]
  rcases le_total (Real.log a + Real.log b) 0 with h | h
  · rw [max_eq_left h]; exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_right h]; exact add_le_add (le_max_right _ _) (le_max_right _ _)

private lemma posLog_div_le_posLog_add {a b : ℝ} (ha : 0 ≤ a) :
    max 0 (Real.log (a / b)) ≤ max 0 (Real.log a) + max 0 (Real.log (1 / b)) := by
  rw [div_eq_mul_one_div]; exact posLog_mul_le_posLog_add ha

private lemma posLog_le_posLog_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    max 0 (Real.log a) ≤ max 0 (Real.log b) := by
  by_cases ha0 : a = 0
  · subst ha0; simp
  · exact max_le_max_left 0 (Real.log_le_log (lt_of_le_of_ne ha (Ne.symm ha0)) hab)

private lemma posLog_inv_abs_sub_le_abs_log (σ c : ℝ) :
    max 0 (Real.log (1 / |σ - c|)) ≤ |Real.log (σ - c)| := by
  by_cases hσ : σ = c
  · subst hσ; simp
  · rw [one_div, Real.log_inv, Real.log_abs]
    rcases le_total (-Real.log (σ - c)) 0 with h | h
    · rw [max_eq_left h]; exact abs_nonneg _
    · rw [max_eq_right h, ← abs_neg]; exact le_abs_self _

private lemma measurable_posLog_div_abs_sub (r c : ℝ) :
    Measurable (fun σ : ℝ => max 0 (Real.log (r / |σ - c|))) :=
  Measurable.max measurable_const (Real.measurable_log.comp
    (measurable_const.div (continuous_abs.measurable.comp (measurable_id.sub measurable_const))))

private lemma intervalIntegrable_abs_log_sub (c a b : ℝ) :
    IntervalIntegrable (fun σ => |Real.log (σ - c)|) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := a - c) (b := b - c)).comp_sub_right c
    eNorm_ne_top
  rw [sub_add_cancel, sub_add_cancel] at h
  exact h.abs

private lemma intervalIntegrable_posLog_inv_abs_sub (c a b : ℝ) :
    IntervalIntegrable (fun σ => max 0 (Real.log (1 / |σ - c|))) volume a b := by
  refine (intervalIntegrable_abs_log_sub c a b).mono_fun
    (measurable_posLog_div_abs_sub 1 c).aestronglyMeasurable ?_
  filter_upwards with σ
  rw [Real.norm_of_nonneg (le_max_left _ _), Real.norm_of_nonneg (abs_nonneg _)]
  exact posLog_inv_abs_sub_le_abs_log σ c

private lemma integrable_posLog_inv_abs_sub (c : ℝ) :
    Integrable (fun σ : ℝ => max 0 (Real.log (1 / |σ - c|))) := by
  have hi := (intervalIntegrable_posLog_inv_abs_sub c (c - 1) (c + 1)).1
  have hsupp : ∀ σ ∉ Ioc (c - 1) (c + 1), max 0 (Real.log (1 / |σ - c|)) = 0 := by
    intro σ hσ
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hσ
    have hge : 1 ≤ |σ - c| := by
      rcases hσ with h1 | h2
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge (abs_nonneg _)))
  have hind : Integrable ((Ioc (c - 1) (c + 1)).indicator
      (fun σ => max 0 (Real.log (1 / |σ - c|)))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hi
  refine hind.congr (Eventually.of_forall fun σ => ?_)
  by_cases hmem : σ ∈ Ioc (c - 1) (c + 1)
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem]; exact (hsupp σ hmem).symm

private lemma integral_posLog_inv_abs_sub_eq_two (c : ℝ) :
    ∫ σ : ℝ, max 0 (Real.log (1 / |σ - c|)) = 2 := by
  have hsplit := integral_add_compl (s := Ioc (c - 1) (c + 1)) measurableSet_Ioc
    (integrable_posLog_inv_abs_sub c)
  have hzero : ∫ σ in (Ioc (c - 1) (c + 1))ᶜ, max 0 (Real.log (1 / |σ - c|)) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => ?_
    rw [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hσ
    have hge : 1 ≤ |σ - c| := by
      rcases hσ with h1 | h2
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge (abs_nonneg _)))
  rw [hzero, add_zero, ← intervalIntegral.integral_of_le (by linarith : c - 1 ≤ c + 1)] at hsplit
  rw [← hsplit, intervalIntegral.integral_comp_sub_right (fun u => max 0 (Real.log (1 / |u|))) c]
  rw [show c - 1 - c = -1 by ring, show c + 1 - c = 1 by ring]
  have heq : EqOn (fun u : ℝ => max 0 (Real.log (1 / |u|))) (fun u => -Real.log u)
      (uIcc (-1 : ℝ) 1) := by
    intro u hu
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hu
    dsimp only
    by_cases hu0 : u = 0
    · subst hu0; simp
    · have hlog : 0 ≤ -Real.log u := by
        rw [← Real.log_abs, neg_nonneg]; exact Real.log_nonpos (abs_nonneg u) (abs_le.mpr hu)
      rw [one_div, Real.log_inv, Real.log_abs, max_eq_right hlog]
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_neg, integral_log]
  norm_num

private lemma setIntegral_posLog_inv_abs_sub_le (c : ℝ) (s : Set ℝ) :
    ∫ σ in s, max 0 (Real.log (1 / |σ - c|)) ≤ 2 := by
  calc ∫ σ in s, max 0 (Real.log (1 / |σ - c|))
      ≤ ∫ σ : ℝ, max 0 (Real.log (1 / |σ - c|)) :=
        setIntegral_le_integral (integrable_posLog_inv_abs_sub c)
          (Eventually.of_forall fun _ => le_max_left 0 _)
    _ = 2 := integral_posLog_inv_abs_sub_eq_two c

/-! ### Section 1: Slit-strip boundary geometry and fold involution -/

/-- Right-slit fold tip `σ_* = 1 - √2`. -/
noncomputable def sigmaStar : ℝ := 1 - Real.sqrt 2

/-- Left-slit fold tip `σ_+ = 1 + √2`. -/
noncomputable def sigmaPlus : ℝ := 1 + Real.sqrt 2

/-- Slit-strip boundary map `b(σ) = (2π)⁻¹ log((1 - σ) / ((-σ)(1 + σ)))`. -/
noncomputable def slitBoundaryMap (σ : ℝ) : ℝ :=
  (2 * π)⁻¹ * Real.log ((1 - σ) / ((-σ) * (1 + σ)))

/-- Right-slit fold involution `σ̃ = (1 + σ) / (σ - 1)` on `(-1, 0)`. -/
noncomputable def slitInv (σ : ℝ) : ℝ := (1 + σ) / (σ - 1)

/-- Left-slit fold involution `σ̃ = (σ + 1) / (σ - 1)` on `(1, ∞)`. -/
noncomputable def leftSlitInv (σ : ℝ) : ℝ := (σ + 1) / (σ - 1)

/-- Inverse Jacobian `J(σ) = 2π |σ(σ² - 1)| / (|σ - σ_*| |σ - σ_+|)`. -/
noncomputable def invJacobian (σ : ℝ) : ℝ :=
  2 * π * |σ * (σ ^ 2 - 1)| / (|σ - sigmaStar| * |σ - sigmaPlus|)

lemma sigmaStar_neg : sigmaStar < 0 := by unfold sigmaStar; linarith [sqrt_two_gt_1414]
lemma sigmaStar_gt_neg_half : (-0.42 : ℝ) < sigmaStar := by unfold sigmaStar; linarith [sqrt_two_lt_1415]
lemma sigmaStar_lt_neg_041 : sigmaStar < (-0.41 : ℝ) := by unfold sigmaStar; linarith [sqrt_two_gt_1414]
lemma sigmaPlus_gt_two : (2.41 : ℝ) < sigmaPlus := by unfold sigmaPlus; linarith [sqrt_two_gt_1414]
lemma sigmaPlus_lt_242 : sigmaPlus < (2.42 : ℝ) := by unfold sigmaPlus; linarith [sqrt_two_lt_1415]

lemma slitBoundaryMap_eq_leftBranch (σ : ℝ) :
    slitBoundaryMap σ = (2 * π)⁻¹ * Real.log ((σ - 1) / (σ * (σ + 1))) := by
  unfold slitBoundaryMap; congr 2
  rw [show 1 - σ = -(σ - 1) by ring, show (-σ) * (1 + σ) = -(σ * (σ + 1)) by ring, neg_div_neg_eq]

lemma slitBoundaryMap_sigmaStar : slitBoundaryMap sigmaStar = xiStar := by
  unfold slitBoundaryMap sigmaStar xiStar
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < √2 - 1 := by linarith [sqrt_two_gt_1414]
  have harg : (1 - (1 - √2)) / ((-(1 - √2)) * (1 + (1 - √2))) = (√2 + 1) ^ 2 := by
    have hden : (-(1 - √2)) * (1 + (1 - √2)) = √2 * (√2 - 1) ^ 2 := by nlinarith [hsq]
    rw [show 1 - (1 - √2) = √2 by ring, hden]
    have hne1 : √2 ≠ 0 := by positivity
    have hne2 : √2 - 1 ≠ 0 := hpos.ne'
    field_simp
    have hmul : (√2 - 1) * (√2 + 1) = 1 := by nlinarith [hsq]
    nlinarith [hmul]
  have harsinh : Real.arsinh 1 = Real.log (√2 + 1) := by
    rw [← Real.sinh_inj, Real.sinh_arsinh, Real.sinh_eq, Real.exp_log (by positivity),
      Real.exp_neg, Real.exp_log (by positivity)]
    have hinv : (√2 + 1)⁻¹ = √2 - 1 := inv_eq_of_mul_eq_one_right (by nlinarith [hsq])
    linarith
  rw [harg, Real.log_pow, Nat.cast_ofNat, harsinh]
  field_simp [Real.pi_pos.ne']

lemma slitInv_mem_Ioo {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0) : slitInv σ ∈ Ioo (-1) 0 := by
  rcases hσ with ⟨hm1, h0⟩
  have hden : σ - 1 < 0 := by linarith
  unfold slitInv
  refine ⟨?_, div_neg_of_pos_of_neg (by linarith) hden⟩
  rw [lt_div_iff_of_neg hden]; linarith

lemma slitInv_slitInv {σ : ℝ} (hσ : σ ≠ 1) : slitInv (slitInv σ) = σ := by
  unfold slitInv
  have h1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  have h2 : (1 + σ) / (σ - 1) - 1 ≠ 0 := by
    rw [div_sub_one h1]; exact div_ne_zero (by intro h; linarith) h1
  field_simp; ring

lemma slitInv_sigmaStar : slitInv sigmaStar = sigmaStar := by
  unfold slitInv sigmaStar
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : 1 - √2 - 1 ≠ 0 := by linarith [sqrt_two_gt_1414]
  field_simp; linarith

lemma slitBoundaryMap_slitInv {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0) :
    slitBoundaryMap (slitInv σ) = slitBoundaryMap σ := by
  unfold slitBoundaryMap slitInv
  have h1 : σ - 1 ≠ 0 := by linarith [hσ.2]
  have h2 : σ ≠ 0 := by linarith [hσ.2]
  have h3 : 1 + σ ≠ 0 := by linarith [hσ.1]
  rw [show 1 - (1 + σ) / (σ - 1) = -2 / (σ - 1) by field_simp [h1]; ring,
    show 1 + (1 + σ) / (σ - 1) = 2 * σ / (σ - 1) by field_simp [h1]; ring]
  congr 2; field_simp [h1, h2, h3]; ring

lemma slitInv_sub_sigmaStar_eq {σ : ℝ} (hσ : σ ≠ 1) :
    slitInv σ - sigmaStar = -√2 * (σ - sigmaStar) / (1 - σ) := by
  unfold slitInv sigmaStar
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  have h2 : 1 - σ ≠ 0 := sub_ne_zero.mpr hσ.symm
  field_simp; ring_nf; rw [hsq]; ring

lemma abs_slitInv_sub_sigmaStar_lower {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0) :
    |σ - sigmaStar| / √2 ≤ |slitInv σ - sigmaStar| := by
  rw [slitInv_sub_sigmaStar_eq (by linarith [hσ.2])]
  have h1s_pos : 0 < 1 - σ := by linarith [hσ.2]
  have h1s_lt : 1 - σ < 2 := by linarith [hσ.1]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < √2), abs_of_pos h1s_pos,
    div_le_div_iff₀ (by positivity) h1s_pos]
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc |σ - sigmaStar| * (1 - σ) ≤ |σ - sigmaStar| * 2 := by gcongr
    _ = |σ - sigmaStar| * (√2 * √2) := by rw [hsq]
    _ = √2 * |σ - sigmaStar| * √2 := by ring

lemma abs_slitInv_sub_sigmaStar_upper {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0) :
    |slitInv σ - sigmaStar| ≤ √2 * |σ - sigmaStar| := by
  rw [slitInv_sub_sigmaStar_eq (by linarith [hσ.2])]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < √2),
    abs_of_pos (by linarith [hσ.2] : 0 < 1 - σ)]
  exact div_le_self (by positivity) (by linarith [hσ.2])

lemma leftSlitInv_gt_one {σ : ℝ} (hσ : 1 < σ) : 1 < leftSlitInv σ := by
  unfold leftSlitInv; rw [lt_div_iff₀ (sub_pos.mpr hσ)]; linarith

lemma leftSlitInv_sigmaPlus : leftSlitInv sigmaPlus = sigmaPlus := by
  unfold leftSlitInv sigmaPlus
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : 1 + √2 - 1 ≠ 0 := by linarith [sqrt_two_gt_1414]
  field_simp; linarith

lemma leftSlitInv_sub_sigmaPlus_eq {σ : ℝ} (hσ : σ ≠ 1) :
    leftSlitInv σ - sigmaPlus = -√2 * (σ - sigmaPlus) / (σ - 1) := by
  unfold leftSlitInv sigmaPlus
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  field_simp; linarith

private lemma leftSlitInv_ratio {σ : ℝ} (hσ : 1 < σ) (hsp : σ ≠ sigmaPlus) :
    (leftSlitInv σ - 1) / |leftSlitInv σ - sigmaPlus| = √2 / |σ - sigmaPlus| := by
  rw [leftSlitInv_sub_sigmaPlus_eq hσ.ne']
  unfold leftSlitInv
  have hσ_sub : 0 < σ - 1 := sub_pos.mpr hσ
  rw [show (σ + 1) / (σ - 1) - 1 = 2 / (σ - 1) by field_simp [hσ_sub.ne']; ring]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < √2), abs_of_pos hσ_sub]
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne_sp : |σ - sigmaPlus| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hsp)
  field_simp [hσ_sub.ne', hne_sp]; linarith

lemma hasDerivAt_slitBoundaryMap {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0 \ {sigmaStar}) :
    HasDerivAt slitBoundaryMap
      (-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1))) σ := by
  have hIoo := hσ.1
  have h1ms : 0 < 1 - σ := by linarith [hIoo.2]
  have hms : 0 < -σ := by linarith [hIoo.2]
  have h1ps : 0 < 1 + σ := by linarith [hIoo.1]
  let f : ℝ → ℝ := fun τ => (2 * π)⁻¹ * (Real.log (1 - τ) - Real.log (-τ) - Real.log (1 + τ))
  have hev : slitBoundaryMap =ᶠ[𝓝 σ] f := by
    filter_upwards [(isOpen_Ioo.mem_nhds hIoo)] with τ hτ
    have ha : 0 < 1 - τ := by linarith [hτ.2]
    have hb : 0 < -τ := by linarith [hτ.2]
    have hc : 0 < 1 + τ := by linarith [hτ.1]
    unfold slitBoundaryMap; dsimp [f]
    rw [Real.log_div ha.ne' (mul_pos hb hc).ne', Real.log_mul hb.ne' hc.ne']; ring
  have hd1 : HasDerivAt (fun τ => Real.log (1 - τ)) ((-1) / (1 - σ)) σ :=
    ((Real.hasDerivAt_log h1ms.ne').comp σ ((hasDerivAt_id σ).const_sub 1)).congr_deriv (by ring)
  have hd2 : HasDerivAt (fun τ => Real.log (-τ)) ((-1) / (-σ)) σ :=
    ((Real.hasDerivAt_log hms.ne').comp σ (hasDerivAt_id σ).neg).congr_deriv (by ring)
  have hd3 : HasDerivAt (fun τ => Real.log (1 + τ)) (1 / (1 + σ)) σ :=
    ((Real.hasDerivAt_log h1ps.ne').comp σ ((hasDerivAt_id σ).const_add 1)).congr_deriv (by ring)
  have hdf : HasDerivAt f ((2 * π)⁻¹ * ((-1) / (1 - σ) - (-1) / (-σ) - 1 / (1 + σ))) σ :=
    ((hd1.sub hd2).sub hd3).const_mul (2 * π)⁻¹
  refine (hdf.congr_of_eventuallyEq hev).congr_deriv ?_
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hs0 : σ ≠ 0 := hIoo.2.ne
  have hs2 : σ ^ 2 - 1 ≠ 0 := by nlinarith [hIoo.1, hIoo.2]
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold sigmaStar sigmaPlus
  field_simp [h1ms.ne', hms.ne', h1ps.ne', hpi, hs0, hs2]
  ring_nf; rw [hsq]; ring

lemma invJacobian_le {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0 \ {sigmaStar}) :
    2 * π * |σ * (σ ^ 2 - 1)| / (|σ - sigmaStar| * |σ - sigmaPlus|) ≤ 2.61 / |σ - sigmaStar| := by
  rcases hσ with ⟨⟨hm1, h0⟩, hne⟩
  have hnum_le : |σ * (σ ^ 2 - 1)| ≤ 1 := by
    rw [abs_mul]
    have h1 : |σ| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |σ ^ 2 - 1| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    nlinarith [abs_nonneg σ, abs_nonneg (σ ^ 2 - 1)]
  have hplus_lb : (2.414 : ℝ) < |σ - sigmaPlus| := by
    rw [abs_of_neg (by linarith [sigmaPlus_gt_two])]
    unfold sigmaPlus; linarith [sqrt_two_gt_1414]
  have hstar_pos : 0 < |σ - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hplus_pos : 0 < |σ - sigmaPlus| := by linarith
  have hconst : 2 * π / |σ - sigmaPlus| ≤ 2.61 := by
    rw [div_le_iff₀ hplus_pos]; nlinarith [Real.pi_lt_d4]
  calc 2 * π * |σ * (σ ^ 2 - 1)| / (|σ - sigmaStar| * |σ - sigmaPlus|)
      ≤ 2 * π * 1 / (|σ - sigmaStar| * |σ - sigmaPlus|) := by gcongr
    _ = (2 * π / |σ - sigmaPlus|) / |σ - sigmaStar| := by ring
    _ ≤ 2.61 / |σ - sigmaStar| := by gcongr

private lemma invJacobian_le_of_Ioo {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0) :
    invJacobian σ ≤ 2.61 / |σ - sigmaStar| := by
  by_cases hne : σ = sigmaStar
  · subst hne; unfold invJacobian; simp
  · exact invJacobian_le ⟨hσ, hne⟩

private lemma invJacobian_nonneg (σ : ℝ) : 0 ≤ invJacobian σ := by
  unfold invJacobian; positivity

/-! ### Section 2: Upper half-plane Poisson kernel and Lemma E -/

/-- Upper half-plane Poisson kernel at `z = x + iy` evaluated at `σ ∈ ℝ`. -/
noncomputable def poissonKernel (x y σ : ℝ) : ℝ :=
  y / (π * ((σ - x) ^ 2 + y ^ 2))

/-- Edge preimage region `(-∞, -1) ∪ (0, 1)`. -/
def edgePreimage : Set ℝ := Iio (-1) ∪ Ioo 0 1

/-- Slit preimage region `(-1, 0) ∪ (1, ∞)`. -/
def slitPreimage : Set ℝ := Ioo (-1) 0 ∪ Ioi 1

/-- Harmonic measure mass carried by the slits. -/
noncomputable def slitMass (x y : ℝ) : ℝ :=
  ∫ σ in slitPreimage, poissonKernel x y σ

lemma poissonKernel_nonneg {x y : ℝ} (hy : 0 ≤ y) (σ : ℝ) : 0 ≤ poissonKernel x y σ := by
  unfold poissonKernel; positivity

lemma continuous_poissonKernel (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous (poissonKernel x y) := by
  unfold poissonKernel; refine continuous_const.div (by fun_prop) fun _ => by positivity

lemma poissonKernel_le_inv_pi_mul_y {x y : ℝ} (hy : 0 < y) (σ : ℝ) :
    poissonKernel x y σ ≤ 1 / (π * y) := by
  unfold poissonKernel
  rw [div_le_div_iff₀ (by positivity) (mul_pos Real.pi_pos hy)]
  nlinarith [Real.pi_pos, sq_nonneg (σ - x)]

lemma integrable_poissonKernel (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (poissonKernel x y) := by
  have heq : poissonKernel x y = fun σ => (π * y)⁻¹ * (1 + (y⁻¹ * (σ + (-x))) ^ 2)⁻¹ := by
    ext σ; unfold poissonKernel; field_simp [hy.ne', Real.pi_pos.ne']; ring
  rw [heq]
  exact ((integrable_inv_one_add_mul_sq (inv_ne_zero hy.ne')).comp_add_right (-x)).const_mul _

theorem integral_poissonKernel (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ σ : ℝ, poissonKernel x y σ = 1 := by
  have heq : poissonKernel x y = fun σ => (π * y)⁻¹ * (1 + (y⁻¹ * (σ + (-x))) ^ 2)⁻¹ := by
    ext σ; unfold poissonKernel; field_simp [hy.ne', Real.pi_pos.ne']; ring
  rw [heq, integral_const_mul, integral_add_right_eq_self (fun u : ℝ => (1 + (y⁻¹ * u) ^ 2)⁻¹) (-x),
    integral_univ_inv_one_add_mul_sq y⁻¹, abs_inv, abs_of_pos hy, div_inv_eq_mul]
  field_simp [hy.ne', Real.pi_pos.ne']

private lemma slitMass_le_one (x : ℝ) {y : ℝ} (hy : 0 < y) : slitMass x y ≤ 1 := by
  unfold slitMass
  calc ∫ σ in slitPreimage, poissonKernel x y σ
      ≤ ∫ σ : ℝ, poissonKernel x y σ :=
        setIntegral_le_integral (integrable_poissonKernel x hy)
          (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
    _ = 1 := integral_poissonKernel x hy

private lemma one_sub_slitMass_eq_edgeMass (x : ℝ) {y : ℝ} (hy : 0 < y) :
    1 - slitMass x y = ∫ σ in edgePreimage, poissonKernel x y σ := by
  have hint := integrable_poissonKernel x hy
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]
    intro σ h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (mem_Iio.mp h2) (not_lt_of_ge (mem_Ioo.mp h1).1.le)
    · exact absurd (mem_Ioo.mp h2).1 (not_lt_of_ge (mem_Ioo.mp h1).2.le)
    · exact absurd (mem_Iio.mp h2) (not_lt_of_ge (by linarith [mem_Ioi.mp h1]))
    · exact absurd (mem_Ioo.mp h2).2 (not_lt_of_ge (mem_Ioi.mp h1).le)
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hsub : (slitPreimage ∪ edgePreimage)ᶜ ⊆ ({-1, 0, 1} : Set ℝ) := by
      intro σ hσ
      simp only [mem_compl_iff, mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio,
        not_or, not_and, not_lt] at hσ
      rcases hσ with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      simp only [mem_insert_iff, mem_singleton_iff]
      by_cases hm1 : σ = -1
      · exact Or.inl hm1
      · have hgt : -1 < σ := lt_of_le_of_ne h3 (Ne.symm hm1)
        by_cases h0 : σ = 0
        · exact Or.inr (Or.inl h0)
        · exact Or.inr (Or.inr (le_antisymm h2 (h4 (lt_of_le_of_ne (h1 hgt) (Ne.symm h0)))))
    exact ae_eq_univ.mpr (measure_mono_null hsub (({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume))
  have htot : slitMass x y + ∫ σ in edgePreimage, poissonKernel x y σ = 1 := by
    unfold slitMass
    rw [← setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
        hint.integrableOn hint.integrableOn,
      setIntegral_congr_set hunion_ae, setIntegral_univ]
    exact integral_poissonKernel x hy
  linarith

private lemma integral_Ioi_inv_sub_sq {x a : ℝ} (hx : x < a) :
    IntegrableOn (fun σ : ℝ => ((σ - x) ^ 2)⁻¹) (Ioi a) ∧
      ∫ σ in Ioi a, ((σ - x) ^ 2)⁻¹ = (a - x)⁻¹ := by
  have hd : ∀ σ ∈ Ici a, HasDerivAt (fun t : ℝ => -(t - x)⁻¹) (((σ - x) ^ 2)⁻¹) σ := fun σ hσ =>
    (((hasDerivAt_id' σ).sub_const x).inv (by linarith [mem_Ici.mp hσ])).neg.congr_deriv (by ring)
  have htop : Tendsto (fun t : ℝ => -(t - x)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp (tendsto_id.atTop_add tendsto_const_nhds)).neg.trans (by simp)
  have hint := integrableOn_Ioi_deriv_of_nonneg' hd (fun _ _ => by positivity) htop
  refine ⟨hint, (integral_Ioi_of_hasDerivAt_of_tendsto' hd hint htop).trans (by ring)⟩

private lemma integral_Iic_inv_sub_sq {x a : ℝ} (ha : a < x) :
    IntegrableOn (fun σ : ℝ => ((σ - x) ^ 2)⁻¹) (Iic a) ∧
      ∫ σ in Iic a, ((σ - x) ^ 2)⁻¹ = (x - a)⁻¹ := by
  obtain ⟨hint_pos, hval_pos⟩ := integral_Ioi_inv_sub_sq (x := -x) (a := -a) (by linarith)
  have hint : IntegrableOn (fun σ : ℝ => ((σ - x) ^ 2)⁻¹) (Iic a) := by
    have h1 : IntegrableOn (fun σ : ℝ => ((-σ - -x) ^ 2)⁻¹) (Iio a) := by
      simpa only [neg_neg] using hint_pos.comp_neg_Iio
    exact (Iff.mpr integrableOn_Iic_iff_integrableOn_Iio h1).congr_fun
      (fun σ _ => by dsimp only; rw [show (-σ - -x) ^ 2 = (σ - x) ^ 2 by ring]) measurableSet_Iic
  have hval : ∫ σ in Iic a, ((σ - x) ^ 2)⁻¹ = (x - a)⁻¹ := by
    have heq : (∫ σ in Iic a, ((σ - x) ^ 2)⁻¹) = ∫ σ in Iic a, ((-σ - -x) ^ 2)⁻¹ :=
      setIntegral_congr_fun measurableSet_Iic fun σ _ =>
        by rw [show (-σ - -x) ^ 2 = (σ - x) ^ 2 by ring]
    rw [heq, integral_comp_neg_Iic a (fun u : ℝ => ((u - -x) ^ 2)⁻¹), hval_pos]
    ring_nf
  exact ⟨hint, hval⟩

/-- **Lemma E (complex neighbourhood).** For `z = x + iy` with `y > 0` and `|z - σ_*| ≤ 0.1`,
the harmonic mass of the strip edges satisfies `1 - m_b ≤ 2y / (0.3π)`. -/
theorem lemmaE_complex {x y : ℝ} (hy : 0 < y)
    (hz : ‖(x : ℂ) + y * I - (sigmaStar : ℂ)‖ ≤ 0.1) :
    1 - slitMass x y ≤ 2 * y / (0.3 * π) := by
  have hre : |x - sigmaStar| ≤ 0.1 := by
    simpa using (Complex.abs_re_le_norm ((x : ℂ) + y * I - (sigmaStar : ℂ))).trans hz
  have hx_lo : (-0.52 : ℝ) < x := by linarith [(abs_le.mp hre).1, sigmaStar_gt_neg_half]
  have hx_hi : x < (-0.31 : ℝ) := by linarith [(abs_le.mp hre).2, sigmaStar_lt_neg_041]
  have hint := integrable_poissonKernel x hy
  have hleft : ∫ σ in Iio (-1), poissonKernel x y σ ≤ y / (0.3 * π) := by
    rw [setIntegral_congr_set Iio_ae_eq_Iic]
    obtain ⟨hint_sq, hval_sq⟩ := integral_Iic_inv_sub_sq (by linarith : (-1 : ℝ) < x)
    have hmono : ∫ σ in Iic (-1), poissonKernel x y σ ≤
        ∫ σ in Iic (-1), (y / π) * ((σ - x) ^ 2)⁻¹ := by
      refine setIntegral_mono_on hint.integrableOn (hint_sq.const_mul _) measurableSet_Iic
        fun σ hσ => ?_
      unfold poissonKernel
      rw [show y / (π * ((σ - x) ^ 2 + y ^ 2)) = (y / π) * ((σ - x) ^ 2 + y ^ 2)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (sq_pos_of_ne_zero (by linarith [mem_Iic.mp hσ])) (by linarith [sq_nonneg y]))
        (by positivity)
    rw [integral_const_mul, hval_sq] at hmono
    refine hmono.trans ?_
    have : (x - (-1))⁻¹ ≤ (0.3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    calc (y / π) * (x - (-1))⁻¹ ≤ (y / π) * (0.3 : ℝ)⁻¹ := by gcongr
      _ = y / (0.3 * π) := by ring
  have hright : ∫ σ in Ioo 0 1, poissonKernel x y σ ≤ y / (0.3 * π) := by
    obtain ⟨hint_sq, hval_sq⟩ := integral_Ioi_inv_sub_sq (by linarith : x < 0)
    have h1 : ∫ σ in Ioo 0 1, poissonKernel x y σ ≤ ∫ σ in Ioi 0, poissonKernel x y σ :=
      setIntegral_mono_set hint.integrableOn
        (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ) Ioo_subset_Ioi_self.eventuallySubset
    have h2 : ∫ σ in Ioi 0, poissonKernel x y σ ≤ ∫ σ in Ioi 0, (y / π) * ((σ - x) ^ 2)⁻¹ := by
      refine setIntegral_mono_on hint.integrableOn (hint_sq.const_mul _) measurableSet_Ioi
        fun σ hσ => ?_
      unfold poissonKernel
      rw [show y / (π * ((σ - x) ^ 2 + y ^ 2)) = (y / π) * ((σ - x) ^ 2 + y ^ 2)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (sq_pos_of_ne_zero (by linarith [mem_Ioi.mp hσ])) (by linarith [sq_nonneg y]))
        (by positivity)
    rw [integral_const_mul, hval_sq] at h2
    refine (h1.trans h2).trans ?_
    have : (0 - x)⁻¹ ≤ (0.3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    calc (y / π) * (0 - x)⁻¹ ≤ (y / π) * (0.3 : ℝ)⁻¹ := by gcongr
      _ = y / (0.3 * π) := by ring
  have hdisj : Disjoint (Iio (-1 : ℝ)) (Ioo 0 1) :=
    Set.disjoint_left.mpr fun _ h1 h2 => by linarith [mem_Iio.mp h1, (mem_Ioo.mp h2).1]
  rw [one_sub_slitMass_eq_edgeMass x hy]
  unfold edgePreimage
  rw [setIntegral_union hdisj measurableSet_Ioo hint.integrableOn hint.integrableOn]
  linarith [show 2 * y / (0.3 * π) = y / (0.3 * π) + y / (0.3 * π) by ring]

private lemma realSlice_mem_ball {x y C_e C_y δ : ℝ}
    (hδ_pos : 0 < δ) (hy_pos : 0 < y)
    (hsmall : δ ≤ (0.1 / (2 * max 1 (max C_e C_y))) ^ 2)
    (hx : |x - sigmaStar| ≤ C_e * δ) (hy : y ≤ C_y * Real.sqrt δ) :
    ‖(x : ℂ) + (y : ℂ) * I - (sigmaStar : ℂ)‖ ≤ 0.1 := by
  let C0 : ℝ := max 1 (max C_e C_y)
  have hC0 : 1 ≤ C0 := le_max_left _ _
  have hsqrt_le : Real.sqrt δ ≤ 0.1 / (2 * C0) := by
    have := Real.sqrt_le_sqrt hsmall
    rwa [Real.sqrt_sq (by positivity)] at this
  have hδ_le_one : δ ≤ 1 := by
    have h05 : 0.1 / (2 * C0) ≤ 0.05 := by rw [div_le_iff₀ (by positivity)]; linarith
    have hsq : (0.1 / (2 * C0)) ^ 2 ≤ (0.05 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h05 2
    linarith
  have hδ_le_sqrt : δ ≤ Real.sqrt δ := by
    calc δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq hδ_pos.le).symm
      _ ≤ Real.sqrt δ := Real.sqrt_le_sqrt (by nlinarith)
  have hre : |x - sigmaStar| ≤ 0.05 := by
    have hCe0 : C_e ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
    calc |x - sigmaStar| ≤ C_e * δ := hx
      _ ≤ C0 * Real.sqrt δ := mul_le_mul hCe0 hδ_le_sqrt hδ_pos.le (by positivity)
      _ ≤ C0 * (0.1 / (2 * C0)) := by gcongr
      _ = 0.05 := by field_simp [show C0 ≠ 0 by linarith]; norm_num
  have him : |y| ≤ 0.05 := by
    have hCy0 : C_y ≤ C0 := (le_max_right _ _).trans (le_max_right _ _)
    rw [abs_of_pos hy_pos]
    calc y ≤ C_y * Real.sqrt δ := hy
      _ ≤ C0 * Real.sqrt δ := by gcongr
      _ ≤ C0 * (0.1 / (2 * C0)) := by gcongr
      _ = 0.05 := by field_simp [show C0 ≠ 0 by linarith]; norm_num
  have hsplit : (x : ℂ) + (y : ℂ) * I - (sigmaStar : ℂ) =
      ((x - sigmaStar : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
  rw [hsplit]
  calc ‖((x - sigmaStar : ℝ) : ℂ) + (y : ℂ) * I‖
      ≤ ‖((x - sigmaStar : ℝ) : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
    _ = |x - sigmaStar| + |y| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 0.05 + 0.05 := add_le_add hre him
    _ = 0.1 := by norm_num

/-- **Lemma E (real slice).** Given two-sided real-slice preimage bounds
`|xUHP δ - σ_*| ≤ C_e δ` and `c_y √δ ≤ yUHP δ ≤ C_y √δ` for `0 < δ ≤ ξ_*`,
the edge harmonic mass satisfies `1 - m ≤ C_E √δ`. -/
theorem lemmaE_real {xUHP yUHP : ℝ → ℝ} {C_e c_y C_y : ℝ}
    (_hCe : 0 ≤ C_e) (hcy : 0 < c_y) (_hCy : c_y ≤ C_y)
    (hx : ∀ δ ∈ Ioc 0 xiStar, |xUHP δ - sigmaStar| ≤ C_e * δ)
    (hy_lo : ∀ δ ∈ Ioc 0 xiStar, c_y * Real.sqrt δ ≤ yUHP δ)
    (hy_hi : ∀ δ ∈ Ioc 0 xiStar, yUHP δ ≤ C_y * Real.sqrt δ) :
    ∃ C_E : ℝ, 0 < C_E ∧
      ∀ δ ∈ Ioc 0 xiStar, 1 - slitMass (xUHP δ) (yUHP δ) ≤ C_E * Real.sqrt δ := by
  let C0 : ℝ := max 1 (max C_e C_y)
  let δ₁ : ℝ := (0.1 / (2 * C0)) ^ 2
  let C_E : ℝ := max (2 * C_y / (0.3 * π)) (2 * C0 / 0.1)
  have hCE_pos : 0 < C_E := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨C_E, hCE_pos, fun δ hδ => ?_⟩
  have hδ_pos : 0 < δ := hδ.1
  have hy_pos : 0 < yUHP δ := lt_of_lt_of_le (mul_pos hcy (Real.sqrt_pos.mpr hδ_pos)) (hy_lo δ hδ)
  by_cases hsmall : δ ≤ δ₁
  · have hz := realSlice_mem_ball hδ_pos hy_pos hsmall (hx δ hδ) (hy_hi δ hδ)
    calc 1 - slitMass (xUHP δ) (yUHP δ) ≤ 2 * yUHP δ / (0.3 * π) := lemmaE_complex hy_pos hz
      _ ≤ 2 * (C_y * Real.sqrt δ) / (0.3 * π) := by gcongr; exact hy_hi δ hδ
      _ = (2 * C_y / (0.3 * π)) * Real.sqrt δ := by ring
      _ ≤ C_E * Real.sqrt δ := by gcongr; exact le_max_left _ _
  · push Not at hsmall
    have hm_nn : 0 ≤ slitMass (xUHP δ) (yUHP δ) := by
      unfold slitMass
      exact setIntegral_nonneg (measurableSet_Ioo.union measurableSet_Ioi)
        fun σ _ => poissonKernel_nonneg hy_pos.le σ
    have hsqrt_ge : 0.1 / (2 * C0) ≤ Real.sqrt δ := by
      have hlt := Real.sqrt_le_sqrt hsmall.le
      rwa [Real.sqrt_sq (by positivity)] at hlt
    have hone_le : 1 ≤ (2 * C0 / 0.1) * Real.sqrt δ := by
      have hC0 : C0 ≠ 0 := by linarith [le_max_left (1 : ℝ) (max C_e C_y)]
      calc (1 : ℝ) = (2 * C0 / 0.1) * (0.1 / (2 * C0)) := by field_simp [hC0]
        _ ≤ (2 * C0 / 0.1) * Real.sqrt δ := by gcongr
    exact (by linarith : 1 - slitMass (xUHP δ) (yUHP δ) ≤ 1).trans
      (hone_le.trans (by gcongr; exact le_max_right _ _))

/-! ### Section 3: Lemma S (sharp entropy bound) -/

private lemma integrable_poissonKernel_mul_posLog_div (x y ρ : ℝ) (hy : 0 < y) (hρ : 0 < ρ) :
    Integrable (fun σ : ℝ => poissonKernel x y σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) := by
  let a := sigmaStar - ρ
  let b := sigmaStar + ρ
  let g : ℝ → ℝ := fun σ => (π * y)⁻¹ * (max 0 (Real.log ρ) + |Real.log (σ - sigmaStar)|)
  have hg_int : IntervalIntegrable g volume a b :=
    (intervalIntegrable_const.add (intervalIntegrable_abs_log_sub sigmaStar a b)).const_mul _
  have hg_ind : Integrable ((Icc a b).indicator g) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (by dsimp [a, b]; linarith)).1 hg_int)
  have hmeas : AEStronglyMeasurable
      (fun σ : ℝ => poissonKernel x y σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) volume :=
    ((continuous_poissonKernel x hy).measurable.mul
      (measurable_posLog_div_abs_sub ρ sigmaStar)).aestronglyMeasurable
  refine hg_ind.mono' hmeas (Eventually.of_forall fun σ => ?_)
  have hP_nn := poissonKernel_nonneg hy.le (x := x) σ
  have hL_nn : 0 ≤ max 0 (Real.log (ρ / |σ - sigmaStar|)) := le_max_left 0 _
  rw [Real.norm_of_nonneg (mul_nonneg hP_nn hL_nn)]
  by_cases hmem : σ ∈ Icc a b
  · rw [indicator_of_mem hmem]
    have hP_ub : poissonKernel x y σ ≤ (π * y)⁻¹ := by
      simpa [one_div] using poissonKernel_le_inv_pi_mul_y hy σ
    have hL_ub : max 0 (Real.log (ρ / |σ - sigmaStar|)) ≤
        max 0 (Real.log ρ) + |Real.log (σ - sigmaStar)| :=
      (posLog_div_le_posLog_add hρ.le).trans
        (add_le_add_right (posLog_inv_abs_sub_le_abs_log σ sigmaStar) _)
    exact mul_le_mul hP_ub hL_ub hL_nn (by positivity)
  · have hzero : max 0 (Real.log (ρ / |σ - sigmaStar|)) = 0 := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hmem
      have hge : ρ < |σ - sigmaStar| := by
        rcases hmem with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact max_eq_left (Real.log_nonpos (div_nonneg hρ.le (abs_nonneg _))
        ((div_le_one (hρ.trans hge)).mpr hge.le))
    rw [indicator_of_notMem hmem, hzero, mul_zero]

/-- Core shifted Cauchy log-singularity integral bound. -/
theorem lemmaS_poisson_log_bound {y e : ℝ} (hy : 0 < y) (_hρ : max y |e| ≤ 1) :
    ∫ σ : ℝ, poissonKernel (sigmaStar + e) y σ *
        max 0 (Real.log (max y |e| / |σ - sigmaStar|)) ≤
      (4 / π) * (1 + Real.log 2) + 3 := by
  let ρ : ℝ := max y |e|
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hy (le_max_left y |e|)
  let G : ℝ → ℝ := fun u => poissonKernel e y u * max 0 (Real.log (ρ / |u|))
  have hshift : (∫ σ : ℝ, poissonKernel (sigmaStar + e) y σ *
      max 0 (Real.log (ρ / |σ - sigmaStar|))) = ∫ u : ℝ, G u := by
    have heq : (fun σ : ℝ => poissonKernel (sigmaStar + e) y σ *
        max 0 (Real.log (ρ / |σ - sigmaStar|))) = fun σ => G (σ + (-sigmaStar)) := by
      ext σ; dsimp [G]; unfold poissonKernel; congr 2; ring_nf
    rw [heq, integral_add_right_eq_self G (-sigmaStar)]
  rw [hshift]
  have hint_G : Integrable G := by
    have heq : G = fun u => (fun σ => poissonKernel (sigmaStar + e) y σ *
        max 0 (Real.log (ρ / |σ - sigmaStar|))) (u + sigmaStar) := by
      ext u; dsimp [G]; unfold poissonKernel; congr 2 <;> ring_nf
    rw [heq]
    exact (integrable_poissonKernel_mul_posLog_div (sigmaStar + e) y ρ hy hρ_pos).comp_add_right
      sigmaStar
  rcases le_or_gt |e| y with hey | hey
  · have hρ_eq : ρ = y := max_eq_left hey
    have hP_le : ∀ u : ℝ, poissonKernel e y u ≤ 3 * poissonKernel 0 y u := by
      intro u; unfold poissonKernel
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have he_sq : e ^ 2 ≤ y ^ 2 := by nlinarith [abs_le.mp hey]
      have hu_sq : u ^ 2 ≤ 2 * (u - e) ^ 2 + 2 * y ^ 2 := by
        have : u ^ 2 ≤ 2 * (u - e) ^ 2 + 2 * e ^ 2 := by nlinarith [sq_nonneg (u - 2 * e)]
        linarith
      have h3 : u ^ 2 + y ^ 2 ≤ 3 * ((u - e) ^ 2 + y ^ 2) := by linarith [sq_nonneg (u - e)]
      calc y * (π * ((u - 0) ^ 2 + y ^ 2)) = y * π * (u ^ 2 + y ^ 2) := by ring
        _ ≤ y * π * (3 * ((u - e) ^ 2 + y ^ 2)) := by gcongr
        _ = 3 * y * (π * ((u - e) ^ 2 + y ^ 2)) := by ring
    let H : ℝ → ℝ := fun u => poissonKernel 0 y u * max 0 (Real.log (y / |u|))
    have hint_H : Integrable H := by
      have heq : H = fun u => (fun σ => poissonKernel sigmaStar y σ *
          max 0 (Real.log (y / |σ - sigmaStar|))) (u + sigmaStar) := by
        ext u; dsimp [H]; unfold poissonKernel; ring_nf
      rw [heq]
      exact (integrable_poissonKernel_mul_posLog_div sigmaStar y y hy hy).comp_add_right sigmaStar
    let f : ℝ → ℝ := fun t => (π * (t ^ 2 + 1))⁻¹ * max 0 (Real.log (1 / |t|))
    have hf_eq : ∀ t : ℝ, y * H (y * t) = f t := by
      intro t; dsimp [H, f]; unfold poissonKernel
      rw [abs_mul, abs_of_pos hy, sub_zero]
      have hlog_arg : y / (y * |t|) = 1 / |t| := by by_cases ht : t = 0 <;> [simp [ht]; field_simp]
      rw [hlog_arg]
      field_simp [hy.ne', Real.pi_pos.ne']
    have h2 : ∫ u : ℝ, H u = ∫ t : ℝ, f t := by
      have hscale := Measure.integral_comp_mul_left H y
      rw [abs_inv, abs_of_pos hy, smul_eq_mul] at hscale
      have hy_mul : y * ∫ x : ℝ, H (y * x) = ∫ u : ℝ, H u := by
        rw [hscale, ← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul]
      rw [← hy_mul, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hf_eq)
    have hint_f : Integrable f := by
      rw [show f = fun t => y * H (y * t) from funext fun t => (hf_eq t).symm]
      exact (hint_H.comp_mul_left' hy.ne').const_mul y
    have h3 : ∫ t : ℝ, f t ≤ 2 / π := by
      have hint_dom := (integrable_posLog_inv_abs_sub 0).const_mul π⁻¹
      have hint_dom' : Integrable (fun t => π⁻¹ * max 0 (Real.log (1 / |t|))) := by
        simpa only [sub_zero] using hint_dom
      have hle : ∫ t : ℝ, f t ≤ ∫ t : ℝ, π⁻¹ * max 0 (Real.log (1 / |t|)) := by
        refine integral_mono hint_f hint_dom' fun t => ?_
        dsimp [f]
        refine mul_le_mul_of_nonneg_right (inv_anti₀ Real.pi_pos ?_) (le_max_left 0 _)
        nlinarith [Real.pi_pos, sq_nonneg t]
      rw [integral_const_mul, show (∫ a : ℝ, max 0 (Real.log (1 / |a|))) = 2 by
        simpa only [sub_zero] using integral_posLog_inv_abs_sub_eq_two 0] at hle
      simpa [div_eq_mul_inv, mul_comm] using hle
    have h1 : ∫ u : ℝ, G u ≤ 3 * ∫ u : ℝ, H u := by
      rw [← integral_const_mul]
      refine integral_mono hint_G (hint_H.const_mul 3) fun u => ?_
      dsimp [G, H]; rw [hρ_eq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hP_le u) (le_max_left 0 _)
    have h6 : 3 * (2 / π) ≤ (4 / π) * (1 + Real.log 2) + 3 := by
      have h6_lt : 3 * (2 / π) < 3 := by
        rw [show 3 * (2 / π) = 6 / π by ring, div_lt_iff₀ Real.pi_pos]
        linarith [Real.pi_gt_d4]
      have h4_pos : 0 ≤ (4 / π) * (1 + Real.log 2) := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
      linarith
    linarith [mul_le_mul_of_nonneg_left (h2 ▸ h3) (by norm_num : (0 : ℝ) ≤ 3)]
  · have hρ_eq : ρ = |e| := max_eq_right hey.le
    have he_pos : 0 < |e| := hy.trans hey
    have hsupp : ∀ u ∉ Ioc (-|e|) |e|, G u = 0 := by
      intro u hu
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
      have hge : |e| ≤ |u| := by
        rcases hu with h1 | h2
        · rw [abs_of_nonpos (by linarith [abs_nonneg e] : u ≤ 0)]; linarith
        · rw [abs_of_pos (by linarith [abs_nonneg e] : 0 < u)]; linarith
      dsimp [G]; rw [hρ_eq, max_eq_left (Real.log_nonpos (by positivity)
        (div_le_one_of_le₀ hge (abs_nonneg u))), mul_zero]
    have hsplit : ∫ u : ℝ, G u = ∫ u in (-|e|)..|e|, G u := by
      have h := integral_add_compl (s := Ioc (-|e|) |e|) measurableSet_Ioc hint_G
      have hcompl : ∫ u in (Ioc (-|e|) |e|)ᶜ, G u = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun u hu => hsupp u hu
      rw [hcompl, add_zero, ← intervalIntegral.integral_of_le (by linarith)] at h
      exact h.symm
    have hG_int : ∀ a b : ℝ, IntervalIntegrable G volume a b := fun a b => hint_G.intervalIntegrable
    have hmid_eq : (∫ u in (-|e|)..|e|, G u) =
        (∫ u in (-|e|)..(-|e| / 2), G u) +
          ((∫ u in (-|e| / 2)..0, G u) + (∫ u in (0 : ℝ)..(|e| / 2), G u)) +
          (∫ u in (|e| / 2)..|e|, G u) := by
      have h12 := (intervalIntegral.integral_add_adjacent_intervals (hG_int (-|e| / 2) 0)
        (hG_int 0 (|e| / 2))).symm
      have h03 := (intervalIntegral.integral_add_adjacent_intervals (hG_int (-|e|) (-|e| / 2))
        (hG_int (-|e| / 2) (|e| / 2))).symm
      have h04 := (intervalIntegral.integral_add_adjacent_intervals (hG_int (-|e|) (|e| / 2))
        (hG_int (|e| / 2) |e|)).symm
      linarith
    have hP_mid : ∀ u : ℝ, |u| ≤ |e| / 2 → poissonKernel e y u ≤ 4 / (π * |e|) := by
      intro u hu; unfold poissonKernel
      have hdiff : |e| / 2 ≤ |u - e| := by
        have htri : |e| ≤ |u - e| + |u| := by
          calc |e| = |u - (u - e)| := by ring_nf
            _ ≤ |u| + |u - e| := abs_sub _ _
            _ = |u - e| + |u| := add_comm _ _
        linarith
      have hsq_diff : e ^ 2 / 4 ≤ (u - e) ^ 2 := by
        rw [← sq_abs (u - e), ← sq_abs e]; nlinarith [abs_nonneg (u - e), abs_nonneg e]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : y * (π * |e|) ≤ |e| * (π * |e|) := by gcongr
      have h2 : |e| * (π * |e|) = 4 * (π * (e ^ 2 / 4)) := by
        rw [mul_left_comm, ← sq, sq_abs]; ring
      have h3 : 4 * (π * (e ^ 2 / 4)) ≤ 4 * (π * ((u - e) ^ 2 + y ^ 2)) := by
        gcongr; linarith [sq_nonneg y]
      linarith
    have hlog_int : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => Real.log |e| - Real.log u)
        volume a b := fun _ _ =>
      intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
    have hhalf_val : ∫ u in (0 : ℝ)..(|e| / 2), (Real.log |e| - Real.log u) =
        (|e| / 2) * (1 + Real.log 2) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
        intervalIntegral.integral_const, smul_eq_mul, sub_zero, integral_log,
        zero_mul, sub_zero, add_zero, Real.log_div he_pos.ne' (by norm_num)]
      ring
    have hhalf_neg_val : ∫ u in (-|e| / 2)..0, (Real.log |e| - Real.log u) =
        (|e| / 2) * (1 + Real.log 2) := by
      have hcomp := intervalIntegral.integral_comp_neg (fun u : ℝ => Real.log |e| - Real.log u)
        (a := -(|e| / 2)) (b := 0)
      simp only [neg_zero, neg_neg] at hcomp
      have heq : ∫ u in (-|e| / 2)..0, (Real.log |e| - Real.log u) =
          ∫ u in (-|e| / 2)..0, (Real.log |e| - Real.log (-u)) :=
        intervalIntegral.integral_congr fun u _ => by rw [Real.log_neg_eq_log]
      rw [heq, show -|e| / 2 = -(|e| / 2) by ring, hcomp, hhalf_val]
    have hmid_pos : ∫ u in (0 : ℝ)..(|e| / 2), G u ≤
        (4 / (π * |e|)) * ((|e| / 2) * (1 + Real.log 2)) := by
      rw [← hhalf_val, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) (hG_int 0 (|e| / 2))
        ((hlog_int 0 (|e| / 2)).const_mul _) fun u hu => ?_
      dsimp [G]; rw [hρ_eq]
      have hlog_ge : 0 ≤ Real.log (|e| / |u|) :=
        Real.log_nonneg ((one_le_div (abs_pos.mpr hu.1.ne')).mpr (by rw [abs_of_pos hu.1]; linarith [hu.2]))
      have hlog_eq : max 0 (Real.log (|e| / |u|)) = Real.log |e| - Real.log u := by
        rw [max_eq_right hlog_ge, abs_of_pos hu.1, Real.log_div he_pos.ne' hu.1.ne']
      rw [← hlog_eq]
      exact mul_le_mul (hP_mid u (by rw [abs_of_pos hu.1]; exact hu.2.le)) le_rfl
        (le_max_left 0 _) (by positivity)
    have hmid_neg : ∫ u in (-|e| / 2)..0, G u ≤
        (4 / (π * |e|)) * ((|e| / 2) * (1 + Real.log 2)) := by
      rw [← hhalf_neg_val, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) (hG_int (-|e| / 2) 0)
        ((hlog_int (-|e| / 2) 0).const_mul _) fun u hu => ?_
      dsimp [G]; rw [hρ_eq]
      have hlog_ge : 0 ≤ Real.log (|e| / |u|) :=
        Real.log_nonneg ((one_le_div (abs_pos.mpr hu.2.ne)).mpr
          (by rw [abs_of_neg hu.2]; linarith [hu.1]))
      have hlog_eq : max 0 (Real.log (|e| / |u|)) = Real.log |e| - Real.log u := by
        rw [max_eq_right hlog_ge, Real.log_div he_pos.ne' (abs_pos.mpr hu.2.ne).ne', Real.log_abs u]
      rw [← hlog_eq]
      exact mul_le_mul (hP_mid u (by rw [abs_of_neg hu.2]; linarith [hu.1])) le_rfl
        (le_max_left 0 _) (by positivity)
    have hmid_tot : (∫ u in (-|e| / 2)..0, G u) + (∫ u in (0 : ℝ)..(|e| / 2), G u) ≤
        (4 / π) * (1 + Real.log 2) := by
      calc (∫ u in (-|e| / 2)..0, G u) + (∫ u in (0 : ℝ)..(|e| / 2), G u)
          ≤ 2 * ((4 / (π * |e|)) * ((|e| / 2) * (1 + Real.log 2))) := by linarith
        _ = (4 / π) * (1 + Real.log 2) := by field_simp [he_pos.ne']
    have hint_P := integrable_poissonKernel e hy
    have hleft_out : ∫ u in (-|e|)..(-|e| / 2), G u ≤
        Real.log 2 * ∫ u in Ioc (-|e|) (-|e| / 2), poissonKernel e y u := by
      rw [← intervalIntegral.integral_of_le (by linarith : -|e| ≤ -|e| / 2),
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by linarith) (hG_int (-|e|) (-|e| / 2))
        (hint_P.intervalIntegrable.const_mul _) fun u hu => ?_
      dsimp [G]; rw [hρ_eq, mul_comm (Real.log 2) _]
      refine mul_le_mul_of_nonneg_left ?_ (poissonKernel_nonneg hy.le u)
      have hu_neg : u < 0 := by linarith [hu.2]
      exact max_le (Real.log_nonneg (by norm_num)) (Real.log_le_log
        (div_pos he_pos (by rw [abs_of_neg hu_neg]; linarith))
        (by rw [abs_of_neg hu_neg, div_le_iff₀ (by linarith)]; linarith [hu.2]))
    have hright_out : ∫ u in (|e| / 2)..|e|, G u ≤
        Real.log 2 * ∫ u in Ioc (|e| / 2) |e|, poissonKernel e y u := by
      rw [← intervalIntegral.integral_of_le (by linarith : |e| / 2 ≤ |e|),
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by linarith) (hG_int (|e| / 2) |e|)
        (hint_P.intervalIntegrable.const_mul _) fun u hu => ?_
      dsimp [G]; rw [hρ_eq, mul_comm (Real.log 2) _]
      refine mul_le_mul_of_nonneg_left ?_ (poissonKernel_nonneg hy.le u)
      have hu_pos : 0 < u := by linarith [hu.1]
      exact max_le (Real.log_nonneg (by norm_num)) (Real.log_le_log
        (div_pos he_pos (by rw [abs_of_pos hu_pos]; exact hu_pos))
        (by rw [abs_of_pos hu_pos, div_le_iff₀ hu_pos]; linarith [hu.1]))
    have hdisj_out : Disjoint (Ioc (-|e|) (-|e| / 2)) (Ioc (|e| / 2) |e|) :=
      Set.disjoint_left.mpr fun _ h1 h2 => by linarith [(mem_Ioc.mp h1).2, (mem_Ioc.mp h2).1]
    have hsum_P : (∫ u in Ioc (-|e|) (-|e| / 2), poissonKernel e y u) +
        (∫ u in Ioc (|e| / 2) |e|, poissonKernel e y u) ≤ 1 := by
      rw [← setIntegral_union hdisj_out measurableSet_Ioc hint_P.integrableOn hint_P.integrableOn]
      calc ∫ u in Ioc (-|e|) (-|e| / 2) ∪ Ioc (|e| / 2) |e|, poissonKernel e y u
          ≤ ∫ u : ℝ, poissonKernel e y u :=
            setIntegral_le_integral hint_P (Eventually.of_forall fun u => poissonKernel_nonneg hy.le u)
        _ = 1 := integral_poissonKernel e hy
    have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hout_tot : (∫ u in (-|e|)..(-|e| / 2), G u) + (∫ u in (|e| / 2)..|e|, G u) ≤ 3 := by
      calc (∫ u in (-|e|)..(-|e| / 2), G u) + (∫ u in (|e| / 2)..|e|, G u)
          ≤ Real.log 2 * ((∫ u in Ioc (-|e|) (-|e| / 2), poissonKernel e y u) +
              (∫ u in Ioc (|e| / 2) |e|, poissonKernel e y u)) := by linarith
        _ ≤ Real.log 2 * 1 := by gcongr
        _ ≤ 3 := by linarith [Real.log_two_lt_d9]
    rw [hsplit, hmid_eq]
    linarith

/-- Unit-numerator shifted Cauchy log-singularity bound deduced from `lemmaS_poisson_log_bound`. -/
theorem lemmaS_poisson_log_unit_bound {y e : ℝ} (hy : 0 < y) (hρ : max y |e| ≤ 1) :
    ∫ σ : ℝ, poissonKernel (sigmaStar + e) y σ * max 0 (Real.log (1 / |σ - sigmaStar|)) ≤
      Real.log (1 / ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖) +
        ((4 / π) * (1 + Real.log 2) + 3 + Real.log √2) := by
  let ρ : ℝ := max y |e|
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hy (le_max_left y |e|)
  have hlog_inv_ρ : 0 ≤ Real.log (1 / ρ) := Real.log_nonneg ((one_le_div hρ_pos).mpr hρ)
  have hint_unit := integrable_poissonKernel_mul_posLog_div (sigmaStar + e) y 1 hy one_pos
  have hint_ρ := integrable_poissonKernel_mul_posLog_div (sigmaStar + e) y ρ hy hρ_pos
  have hint_const : Integrable (fun σ : ℝ => poissonKernel (sigmaStar + e) y σ * Real.log (1 / ρ)) :=
    (integrable_poissonKernel (sigmaStar + e) hy).mul_const _
  have hmono : ∫ σ : ℝ, poissonKernel (sigmaStar + e) y σ * max 0 (Real.log (1 / |σ - sigmaStar|)) ≤
      ∫ σ : ℝ, poissonKernel (sigmaStar + e) y σ * Real.log (1 / ρ) +
        poissonKernel (sigmaStar + e) y σ * max 0 (Real.log (ρ / |σ - sigmaStar|)) := by
    refine integral_mono hint_unit (hint_const.add hint_ρ) fun σ => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (poissonKernel_nonneg hy.le σ)
    by_cases hσ : σ = sigmaStar
    · subst hσ; simpa [one_div] using hlog_inv_ρ
    · have habs_pos : 0 < |σ - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hσ)
      rw [show 1 / |σ - sigmaStar| = (1 / ρ) * (ρ / |σ - sigmaStar|) by
          field_simp [hρ_pos.ne', habs_pos.ne'],
        Real.log_mul (one_div_pos.mpr hρ_pos).ne' (div_pos hρ_pos habs_pos).ne']
      exact posLog_add_le_single hlog_inv_ρ
  rw [integral_add hint_const hint_ρ, integral_mul_const, integral_poissonKernel (sigmaStar + e) hy,
    one_mul] at hmono
  have hnorm_eq : (sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ) = (e : ℂ) + y * I := by ring
  have hnorm_pos : 0 < ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖ := by
    rw [hnorm_eq]
    have h := Complex.abs_im_le_norm ((e : ℂ) + y * I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, abs_of_pos hy] at h
    exact hy.trans_le h
  have hnorm_le : ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖ ≤ √2 * ρ := by
    rw [hnorm_eq]
    simpa [ρ, max_comm, abs_of_pos hy] using Complex.norm_le_sqrt_two_mul_max ((e : ℂ) + y * I)
  have hinv_ρ_le : Real.log (1 / ρ) ≤
      Real.log (1 / ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖) + Real.log √2 := by
    have hle : 1 / ρ ≤ √2 / ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖ := by
      rw [div_le_div_iff₀ hρ_pos hnorm_pos, one_mul]; exact hnorm_le
    calc Real.log (1 / ρ)
        ≤ Real.log (√2 / ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖) :=
          Real.log_le_log (one_div_pos.mpr hρ_pos) hle
      _ = Real.log (1 / ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖ * √2) := by ring_nf
      _ = Real.log (1 / ‖(sigmaStar + e : ℂ) + y * I - (sigmaStar : ℂ)‖) + Real.log √2 :=
          Real.log_mul (one_div_pos.mpr hnorm_pos).ne' (by positivity)
  linarith [lemmaS_poisson_log_bound hy hρ]

/-- Right-slit harmonic-measure density pulled back to `(-1, 0)`. -/
noncomputable def rightSlitDensity (x y σ : ℝ) : ℝ :=
  poissonKernel x y σ * invJacobian σ + poissonKernel x y (slitInv σ) * invJacobian (slitInv σ)

/-- Left-slit harmonic-measure density pulled back to `(1, ∞)`. -/
noncomputable def leftSlitDensity (x y σ : ℝ) : ℝ :=
  poissonKernel x y σ * invJacobian σ +
    poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ)

/-- Right-slit contribution to the slit harmonic-measure entropy `S(b)`. -/
noncomputable def rightSlitEntropy (x y : ℝ) : ℝ :=
  ∫ σ in Ioo (-1) 0, poissonKernel x y σ * max 0 (Real.log (rightSlitDensity x y σ))

/-- Left-slit contribution to the slit harmonic-measure entropy `S(b)`. -/
noncomputable def leftSlitEntropy (x y : ℝ) : ℝ :=
  ∫ σ in Ioi 1, poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))

/-- Total slit harmonic-measure entropy `S(b) = ∫_{|x̃| ≥ ξ_*} ω' log⁺ ω' d x̃`. -/
noncomputable def slitEntropy (x y : ℝ) : ℝ :=
  rightSlitEntropy x y + leftSlitEntropy x y

private lemma measurable_invJacobian : Measurable invJacobian := by unfold invJacobian; fun_prop

private lemma measurable_rightSlitDensity (x y : ℝ) : Measurable (rightSlitDensity x y) := by
  unfold rightSlitDensity poissonKernel slitInv
  have := measurable_invJacobian; fun_prop (disch := measurability)

private lemma measurable_leftSlitDensity (x y : ℝ) : Measurable (leftSlitDensity x y) := by
  unfold leftSlitDensity poissonKernel leftSlitInv
  have := measurable_invJacobian; fun_prop (disch := measurability)

private lemma rightSlitDensity_nonneg (x : ℝ) {y : ℝ} (hy : 0 ≤ y) (σ : ℝ) :
    0 ≤ rightSlitDensity x y σ := by
  unfold rightSlitDensity
  exact add_nonneg (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg _))
    (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg _))

private lemma leftSlitDensity_nonneg (x : ℝ) {y : ℝ} (hy : 0 ≤ y) (σ : ℝ) :
    0 ≤ leftSlitDensity x y σ := by
  unfold leftSlitDensity
  exact add_nonneg (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg _))
    (mul_nonneg (poissonKernel_nonneg hy _) (invJacobian_nonneg _))

lemma slitEntropy_nonneg (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ slitEntropy x y :=
  add_nonneg
    (setIntegral_nonneg measurableSet_Ioo fun _ _ =>
      mul_nonneg (poissonKernel_nonneg hy _) (le_max_left 0 _))
    (setIntegral_nonneg measurableSet_Ioi fun _ _ =>
      mul_nonneg (poissonKernel_nonneg hy _) (le_max_left 0 _))

private lemma rightSlitDensity_le {x y σ : ℝ} (hy : 0 < y) (hσ : σ ∈ Ioo (-1) 0) :
    rightSlitDensity x y σ ≤ (2.61 * (1 + √2) / (π * y)) / |σ - sigmaStar| := by
  by_cases hne : σ = sigmaStar
  · subst hne; unfold rightSlitDensity; rw [slitInv_sigmaStar]; unfold invJacobian; simp
  · unfold rightSlitDensity
    have hP1 := poissonKernel_le_inv_pi_mul_y (x := x) hy σ
    have hP2 := poissonKernel_le_inv_pi_mul_y (x := x) hy (slitInv σ)
    have hJ1 := invJacobian_le_of_Ioo hσ
    have hJ2 : invJacobian (slitInv σ) ≤ 2.61 * √2 / |σ - sigmaStar| := by
      have hstar : 0 < |σ - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hne)
      calc invJacobian (slitInv σ) ≤ 2.61 / |slitInv σ - sigmaStar| :=
            invJacobian_le_of_Ioo (slitInv_mem_Ioo hσ)
        _ ≤ 2.61 / (|σ - sigmaStar| / √2) := by gcongr; exact abs_slitInv_sub_sigmaStar_lower hσ
        _ = 2.61 * √2 / |σ - sigmaStar| := by rw [div_div_eq_mul_div]
    calc poissonKernel x y σ * invJacobian σ +
          poissonKernel x y (slitInv σ) * invJacobian (slitInv σ)
        ≤ (1 / (π * y)) * (2.61 / |σ - sigmaStar|) +
            (1 / (π * y)) * (2.61 * √2 / |σ - sigmaStar|) := by
          gcongr <;> exact invJacobian_nonneg _
      _ = (2.61 * (1 + √2) / (π * y)) / |σ - sigmaStar| := by ring

private lemma integrableOn_rightSlitEntropy (x : ℝ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn
      (fun σ => poissonKernel x y σ * max 0 (Real.log (rightSlitDensity x y σ))) (Ioo (-1) 0) := by
  let C0 : ℝ := 2.61 * (1 + √2) / (π * y)
  let dom : ℝ → ℝ := fun σ => (π * y)⁻¹ * (max 0 (Real.log C0) + max 0 (Real.log (1 / |σ - sigmaStar|)))
  have hdom_on : IntegrableOn dom (Ioo (-1) 0) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 0)).1
      ((intervalIntegrable_const.add
        (intervalIntegrable_posLog_inv_abs_sub sigmaStar (-1) 0)).const_mul _)).mono_set
      Ioo_subset_Ioc_self
  have hmeas : AEStronglyMeasurable
      (fun σ => poissonKernel x y σ * max 0 (Real.log (rightSlitDensity x y σ)))
      (volume.restrict (Ioo (-1) 0)) :=
    ((continuous_poissonKernel x hy).measurable.mul
      (Measurable.max measurable_const (Real.measurable_log.comp
        (measurable_rightSlitDensity x y)))).aestronglyMeasurable
  refine hdom_on.mono' hmeas ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun σ hσ => ?_))
  rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hy.le σ) (le_max_left 0 _))]
  have hP_ub : poissonKernel x y σ ≤ (π * y)⁻¹ := by
    simpa [one_div] using poissonKernel_le_inv_pi_mul_y hy σ
  have hL_ub := (posLog_le_posLog_of_nonneg (rightSlitDensity_nonneg x hy.le σ)
    (rightSlitDensity_le hy hσ)).trans (posLog_div_le_posLog_add (by positivity : 0 ≤ C0))
  exact mul_le_mul hP_ub hL_ub (le_max_left 0 _) (by positivity)

private lemma invJacobian_gt_one_le {σ : ℝ} (hσ : 1 < σ) :
    invJacobian σ ≤ 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by
  by_cases hp : σ = sigmaPlus
  · subst hp; unfold invJacobian; simp
  · unfold invJacobian
    have hstar : 0 < σ - sigmaStar := by linarith [sigmaStar_neg]
    rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)), abs_of_pos hstar,
      show σ ^ 2 - 1 = (σ - 1) * (σ + 1) by ring]
    have h1 : σ + 1 ≤ 2 * σ := by linarith
    have h2 : σ / (σ - sigmaStar) ≤ 1 := (div_le_one hstar).mpr (by linarith [sigmaStar_neg])
    have hplus_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hp)
    have hsplit : 2 * π * (σ * ((σ - 1) * (σ + 1))) / ((σ - sigmaStar) * |σ - sigmaPlus|) =
        (σ / (σ - sigmaStar)) * (2 * π * (σ - 1) * (σ + 1) / |σ - sigmaPlus|) := by
      field_simp [hstar.ne', hplus_pos.ne']
    rw [hsplit]
    calc (σ / (σ - sigmaStar)) * (2 * π * (σ - 1) * (σ + 1) / |σ - sigmaPlus|)
        ≤ 1 * (2 * π * (σ - 1) * (2 * σ) / |σ - sigmaPlus|) := by gcongr
      _ = 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by ring

private lemma leftSlitDensity_compact_bound {x y R y_min y_max : ℝ}
    (_hR : 0 ≤ R) (hy_lo : 0 < y_min) (hy_lo_le : y_min ≤ y) (hy_hi : y ≤ y_max)
    (hx : |x - sigmaStar| ≤ R) :
    let B : ℝ := 2 * (R + 1) + 3
    let C_far : ℝ := 32 * y_max + 16 * √2 / y_min
    let C_near : ℝ := (4 * B ^ 2 + 4 * √2 * B) / y_min + 32 * y_max * B
    (∀ σ ∈ Ioi B, leftSlitDensity x y σ ≤ C_far) ∧
      (∀ σ ∈ Ioc 1 B, leftSlitDensity x y σ ≤ C_near / |σ - sigmaPlus|) := by
  intro B C_far C_near
  have hy : 0 < y := hy_lo.trans_le hy_lo_le
  have hy_max_pos : 0 < y_max := hy.trans_le hy_hi
  have hx_abs : |x| ≤ R + 1 := by
    have h1 : |sigmaStar| < 1 :=
      abs_lt.mpr ⟨by linarith [sigmaStar_gt_neg_half], by linarith [sigmaStar_neg]⟩
    calc |x| = |(x - sigmaStar) + sigmaStar| := by ring_nf
      _ ≤ |x - sigmaStar| + |sigmaStar| := abs_add_le _ _
      _ ≤ R + 1 := by linarith
  have hB_ge : 3 ≤ B := by dsimp [B]; linarith
  have htau_tail : ∀ τ : ℝ, B ≤ τ →
      poissonKernel x y τ * invJacobian τ ≤ 32 * y_max := by
    intro τ hτ
    have hτ_pos : 0 < τ := by linarith
    have hτ_sub_x : τ / 2 ≤ τ - x := by
      have hx_le : x ≤ R + 1 := (abs_le.mp hx_abs).2
      dsimp [B] at hτ; linarith
    have hP : poissonKernel x y τ ≤ 4 * y_max / (π * τ ^ 2) := by
      unfold poissonKernel
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : τ ^ 2 ≤ 4 * (τ - x) ^ 2 := by nlinarith
      have h1 : y * (π * τ ^ 2) ≤ 4 * y_max * (π * (τ - x) ^ 2) := by
        have hpi := Real.pi_pos
        calc y * (π * τ ^ 2) ≤ y_max * (π * τ ^ 2) := by gcongr
          _ ≤ y_max * (π * (4 * (τ - x) ^ 2)) := by gcongr
          _ = 4 * y_max * (π * (τ - x) ^ 2) := by ring
      linarith [mul_nonneg (by positivity : 0 ≤ 4 * y_max) (mul_nonneg Real.pi_pos.le (sq_nonneg y))]
    have hJ := invJacobian_gt_one_le (by linarith : 1 < τ)
    have hsp : 0.5 ≤ |τ - sigmaPlus| := by
      rw [abs_of_pos (by linarith [sigmaPlus_lt_242])]
      linarith [sigmaPlus_lt_242]
    calc poissonKernel x y τ * invJacobian τ
        ≤ (4 * y_max / (π * τ ^ 2)) * (4 * π * τ * (τ - 1) / |τ - sigmaPlus|) :=
          mul_le_mul hP hJ (invJacobian_nonneg τ) (by positivity)
      _ = 16 * y_max * ((τ - 1) / τ) / |τ - sigmaPlus| := by
          field_simp [Real.pi_pos.ne', hτ_pos.ne']; ring
      _ ≤ 16 * y_max * 1 / 0.5 := by gcongr; rw [div_le_one hτ_pos]; linarith
      _ = 32 * y_max := by ring
  have hinv_near : ∀ (σ M : ℝ), 1 < σ → leftSlitInv σ ≤ M →
      poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ) ≤
        4 * √2 * M / (y_min * |σ - sigmaPlus|) := by
    intro σ M hσ1 hτM
    by_cases hsp : σ = sigmaPlus
    · subst hsp; rw [leftSlitInv_sigmaPlus]; unfold invJacobian; simp
    · let τ := leftSlitInv σ
      have hτ1 : 1 < τ := leftSlitInv_gt_one hσ1
      have hP : poissonKernel x y τ ≤ 1 / (π * y_min) :=
        (poissonKernel_le_inv_pi_mul_y hy τ).trans
          (one_div_le_one_div_of_le (mul_pos Real.pi_pos hy_lo)
            (mul_le_mul_of_nonneg_left hy_lo_le Real.pi_pos.le))
      have hJ : invJacobian τ ≤ 4 * π * M * (τ - 1) / |τ - sigmaPlus| :=
        (invJacobian_gt_one_le hτ1).trans (by gcongr)
      calc poissonKernel x y τ * invJacobian τ
          ≤ (1 / (π * y_min)) * (4 * π * M * (τ - 1) / |τ - sigmaPlus|) :=
            mul_le_mul hP hJ (invJacobian_nonneg τ) (by positivity)
        _ = (4 * M / y_min) * ((τ - 1) / |τ - sigmaPlus|) := by
            field_simp [Real.pi_pos.ne', hy_lo.ne']
        _ = (4 * M / y_min) * (√2 / |σ - sigmaPlus|) := by rw [leftSlitInv_ratio hσ1 hsp]
        _ = 4 * √2 * M / (y_min * |σ - sigmaPlus|) := by ring
  constructor
  · intro σ hσ
    have hσB : B < σ := mem_Ioi.mp hσ
    have hτ_le2 : leftSlitInv σ ≤ 2 := by
      unfold leftSlitInv; rw [div_le_iff₀ (by linarith)]; linarith
    have hsp : 0.5 ≤ |σ - sigmaPlus| := by
      rw [abs_of_pos (by linarith [sigmaPlus_lt_242])]; linarith [sigmaPlus_lt_242]
    have h2 : poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ) ≤
        16 * √2 / y_min := by
      refine (hinv_near σ 2 (by linarith) hτ_le2).trans ?_
      calc 4 * √2 * 2 / (y_min * |σ - sigmaPlus|) ≤ 4 * √2 * 2 / (y_min * 0.5) := by gcongr
        _ = 16 * √2 / y_min := by ring
    unfold leftSlitDensity
    exact add_le_add (htau_tail σ hσB.le) h2
  · intro σ hσ
    rcases mem_Ioc.mp hσ with ⟨hσ1, hσB⟩
    by_cases hsp : σ = sigmaPlus
    · subst hsp; unfold leftSlitDensity; rw [leftSlitInv_sigmaPlus]; unfold invJacobian; simp
    · have hsp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hsp)
      have hsp_le_B : |σ - sigmaPlus| ≤ B :=
        abs_le.mpr ⟨by linarith [sigmaPlus_gt_two, sigmaPlus_lt_242],
          by linarith [sigmaPlus_gt_two, sigmaPlus_lt_242]⟩
      have hP1 : poissonKernel x y σ ≤ 1 / (π * y_min) :=
        (poissonKernel_le_inv_pi_mul_y hy σ).trans
          (one_div_le_one_div_of_le (mul_pos Real.pi_pos hy_lo)
            (mul_le_mul_of_nonneg_left hy_lo_le Real.pi_pos.le))
      have hJ1 : invJacobian σ ≤ 4 * π * B ^ 2 / |σ - sigmaPlus| := by
        refine (invJacobian_gt_one_le hσ1).trans ?_
        have hmul : σ * (σ - 1) ≤ B ^ 2 := by nlinarith
        rw [show 4 * π * σ * (σ - 1) / |σ - sigmaPlus| =
          4 * π * (σ * (σ - 1)) / |σ - sigmaPlus| by ring]
        gcongr
      have h1 : poissonKernel x y σ * invJacobian σ ≤ 4 * B ^ 2 / (y_min * |σ - sigmaPlus|) := by
        calc poissonKernel x y σ * invJacobian σ
            ≤ (1 / (π * y_min)) * (4 * π * B ^ 2 / |σ - sigmaPlus|) :=
              mul_le_mul hP1 hJ1 (invJacobian_nonneg σ) (by positivity)
          _ = 4 * B ^ 2 / (y_min * |σ - sigmaPlus|) := by field_simp [Real.pi_pos.ne', hy_lo.ne']
      have h2 : poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ) ≤
          (4 * √2 * B / y_min + 32 * y_max * B) / |σ - sigmaPlus| := by
        rcases le_or_gt (leftSlitInv σ) B with hτB | hτB
        · refine (hinv_near σ B hσ1 hτB).trans ?_
          rw [show 4 * √2 * B / (y_min * |σ - sigmaPlus|) =
            (4 * √2 * B / y_min) / |σ - sigmaPlus| by ring]
          gcongr; linarith [show 0 ≤ 32 * y_max * B by positivity]
        · have hle := htau_tail (leftSlitInv σ) hτB.le
          have hle' : 32 * y_max ≤ 32 * y_max * B / |σ - sigmaPlus| := by
            rw [le_div_iff₀ hsp_pos]; nlinarith
          refine hle.trans (hle'.trans ?_)
          gcongr; linarith [show 0 ≤ 4 * √2 * B / y_min by positivity]
      unfold leftSlitDensity
      calc poissonKernel x y σ * invJacobian σ +
            poissonKernel x y (leftSlitInv σ) * invJacobian (leftSlitInv σ)
          ≤ 4 * B ^ 2 / (y_min * |σ - sigmaPlus|) +
              (4 * √2 * B / y_min + 32 * y_max * B) / |σ - sigmaPlus| := add_le_add h1 h2
        _ = C_near / |σ - sigmaPlus| := by dsimp [C_near]; ring

private lemma leftSlitEntropy_integrable_and_le {x y R y_min y_max : ℝ}
    (hR : 0 ≤ R) (hy_lo : 0 < y_min) (hy_lo_le : y_min ≤ y) (hy_hi : y ≤ y_max)
    (hx : |x - sigmaStar| ≤ R) :
    let B : ℝ := 2 * (R + 1) + 3
    let C_far : ℝ := 32 * y_max + 16 * √2 / y_min
    let C_near : ℝ := (4 * B ^ 2 + 4 * √2 * B) / y_min + 32 * y_max * B
    IntegrableOn (fun σ => poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ)))
        (Ioi 1) ∧
      leftSlitEntropy x y ≤
        max (max 0 (Real.log C_far)) (max 0 (Real.log C_near)) + 2 / (π * y_min) := by
  intro B C_far C_near
  have hy : 0 < y := hy_lo.trans_le hy_lo_le
  have hy_max_pos : 0 < y_max := hy.trans_le hy_hi
  have hB_pos : 0 < B := by dsimp [B]; linarith
  have h1B : 1 ≤ B := by dsimp [B]; linarith
  have hCnear_nn : 0 ≤ C_near := by dsimp [C_near]; positivity
  obtain ⟨hfar, hnear⟩ := leftSlitDensity_compact_bound hR hy_lo hy_lo_le hy_hi hx
  let M_const : ℝ := max (max 0 (Real.log C_far)) (max 0 (Real.log C_near))
  have hint_P := integrable_poissonKernel x hy
  have hmeas_main : Measurable (fun σ => poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))) :=
    (continuous_poissonKernel x hy).measurable.mul
      (Measurable.max measurable_const (Real.measurable_log.comp (measurable_leftSlitDensity x y)))
  have hint_far : IntegrableOn
      (fun σ => poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))) (Ioi B) := by
    refine (hint_P.integrableOn.mul_const M_const).mono' hmeas_main.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun σ hσ => ?_))
    rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hy.le σ) (le_max_left 0 _))]
    exact mul_le_mul_of_nonneg_left
      ((posLog_le_posLog_of_nonneg (leftSlitDensity_nonneg x hy.le σ) (hfar σ hσ)).trans
        (le_max_left _ _)) (poissonKernel_nonneg hy.le σ)
  let dom_near : ℝ → ℝ := fun σ =>
    poissonKernel x y σ * M_const + (π * y_min)⁻¹ * max 0 (Real.log (1 / |σ - sigmaPlus|))
  have hdom_near_on : IntegrableOn dom_near (Ioc 1 B) :=
    (hint_P.integrableOn.mul_const M_const).add
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1B).1
        ((intervalIntegrable_posLog_inv_abs_sub sigmaPlus 1 B).const_mul _))
  have hnear_dom : ∀ σ ∈ Ioc 1 B,
      poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ)) ≤ dom_near σ := by
    intro σ hσ
    have hP_ub : poissonKernel x y σ ≤ (π * y_min)⁻¹ := by
      have h1 := (poissonKernel_le_inv_pi_mul_y (x := x) hy σ).trans
        (one_div_le_one_div_of_le (mul_pos Real.pi_pos hy_lo)
          (mul_le_mul_of_nonneg_left hy_lo_le Real.pi_pos.le))
      rwa [one_div] at h1
    have hL_ub : max 0 (Real.log (leftSlitDensity x y σ)) ≤
        M_const + max 0 (Real.log (1 / |σ - sigmaPlus|)) := by
      refine (posLog_le_posLog_of_nonneg (leftSlitDensity_nonneg x hy.le σ) (hnear σ hσ)).trans ?_
      refine (posLog_div_le_posLog_add hCnear_nn).trans ?_
      gcongr; exact le_max_right _ _
    dsimp [dom_near]
    calc poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))
        ≤ poissonKernel x y σ * (M_const + max 0 (Real.log (1 / |σ - sigmaPlus|))) :=
          mul_le_mul_of_nonneg_left hL_ub (poissonKernel_nonneg hy.le σ)
      _ = poissonKernel x y σ * M_const +
            poissonKernel x y σ * max 0 (Real.log (1 / |σ - sigmaPlus|)) := by ring
      _ ≤ poissonKernel x y σ * M_const +
            (π * y_min)⁻¹ * max 0 (Real.log (1 / |σ - sigmaPlus|)) := by gcongr
  have hint_near : IntegrableOn
      (fun σ => poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))) (Ioc 1 B) := by
    refine hdom_near_on.mono' hmeas_main.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun σ hσ => ?_))
    rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hy.le σ) (le_max_left 0 _))]
    exact hnear_dom σ hσ
  have hunion : Ioc 1 B ∪ Ioi B = Ioi 1 := Ioc_union_Ioi_eq_Ioi h1B
  have hint_all : IntegrableOn
      (fun σ => poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))) (Ioi 1) :=
    hunion ▸ hint_near.union hint_far
  refine ⟨hint_all, ?_⟩
  unfold leftSlitEntropy
  rw [← hunion, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_near hint_far]
  have hI_near : ∫ σ in Ioc 1 B, poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ)) ≤
      ∫ σ in Ioc 1 B, dom_near σ :=
    setIntegral_mono_on hint_near hdom_near_on measurableSet_Ioc hnear_dom
  have hI_far : ∫ σ in Ioi B, poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ)) ≤
      ∫ σ in Ioi B, poissonKernel x y σ * M_const :=
    setIntegral_mono_on hint_far (hint_P.integrableOn.mul_const M_const) measurableSet_Ioi
      fun σ hσ => mul_le_mul_of_nonneg_left ((posLog_le_posLog_of_nonneg
        (leftSlitDensity_nonneg x hy.le σ) (hfar σ hσ)).trans (le_max_left _ _))
        (poissonKernel_nonneg hy.le σ)
  have hdom_split : ∫ σ in Ioc 1 B, dom_near σ =
      (∫ σ in Ioc 1 B, poissonKernel x y σ * M_const) +
        (π * y_min)⁻¹ * ∫ σ in Ioc 1 B, max 0 (Real.log (1 / |σ - sigmaPlus|)) := by
    dsimp [dom_near]
    rw [integral_add (hint_P.integrableOn.mul_const M_const)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1B).1
          ((intervalIntegrable_posLog_inv_abs_sub sigmaPlus 1 B).const_mul _)),
      integral_const_mul]
  have hlog_piece : ∫ σ in Ioc 1 B, max 0 (Real.log (1 / |σ - sigmaPlus|)) ≤ 2 :=
    setIntegral_posLog_inv_abs_sub_le sigmaPlus (Ioc 1 B)
  have hP_sum : (∫ σ in Ioc 1 B, poissonKernel x y σ * M_const) +
      (∫ σ in Ioi B, poissonKernel x y σ * M_const) ≤ M_const := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint_P.integrableOn.mul_const M_const) (hint_P.integrableOn.mul_const M_const),
      hunion, integral_mul_const]
    have hM_nn : 0 ≤ M_const := le_trans (le_max_left 0 _) (le_max_left _ _)
    calc (∫ σ in Ioi 1, poissonKernel x y σ) * M_const
        ≤ (∫ σ : ℝ, poissonKernel x y σ) * M_const :=
          mul_le_mul_of_nonneg_right (setIntegral_le_integral hint_P
            (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)) hM_nn
      _ = M_const := by rw [integral_poissonKernel x hy, one_mul]
  calc (∫ σ in Ioc 1 B, poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))) +
        (∫ σ in Ioi B, poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ)))
      ≤ (∫ σ in Ioc 1 B, dom_near σ) + (∫ σ in Ioi B, poissonKernel x y σ * M_const) :=
        add_le_add hI_near hI_far
    _ = ((∫ σ in Ioc 1 B, poissonKernel x y σ * M_const) +
          (∫ σ in Ioi B, poissonKernel x y σ * M_const)) +
          (π * y_min)⁻¹ * ∫ σ in Ioc 1 B, max 0 (Real.log (1 / |σ - sigmaPlus|)) := by
        rw [hdom_split]; ring
    _ ≤ M_const + (π * y_min)⁻¹ * 2 := by gcongr
    _ = M_const + 2 / (π * y_min) := by ring

/-- Explicit uniform constant in `lemmaS_complex`. -/
noncomputable def slitEntropyComplexConst : ℝ :=
  Real.log (2.61 * (1 + √2) / π) + (4 / π) * (1 + Real.log 2) + 5 + Real.log √2

lemma slitEntropyComplexConst_nonneg : 0 ≤ slitEntropyComplexConst := by
  unfold slitEntropyComplexConst
  have h1 : 1 ≤ 2.61 * (1 + √2) / π := by
    rw [one_le_div Real.pi_pos]; nlinarith [Real.pi_lt_d4, sqrt_two_gt_1414]
  have h2 := Real.log_nonneg h1
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h4 := Real.log_nonneg (by linarith [sqrt_two_gt_1414] : (1 : ℝ) ≤ √2)
  positivity

/-- **Lemma S (a), complex neighbourhood.** For `0 < y` and `|z - σ_*| ≤ 0.1`,
`S(b) ≤ log(1/y) + log(1/|z - σ_*|) + C`. -/
theorem lemmaS_complex {x y : ℝ} (hy : 0 < y)
    (hz : ‖(x : ℂ) + y * I - (sigmaStar : ℂ)‖ ≤ 0.1) :
    slitEntropy x y ≤
      Real.log (1 / y) + Real.log (1 / ‖(x : ℂ) + y * I - (sigmaStar : ℂ)‖) +
        slitEntropyComplexConst := by
  let e : ℝ := x - sigmaStar
  have hx_eq : x = sigmaStar + e := by dsimp [e]; ring
  have hre : |e| ≤ 0.1 := by
    simpa [e] using (Complex.abs_re_le_norm ((x : ℂ) + y * I - (sigmaStar : ℂ))).trans hz
  have him : y ≤ 0.1 := by
    simpa [abs_of_pos hy] using
      (Complex.abs_im_le_norm ((x : ℂ) + y * I - (sigmaStar : ℂ))).trans hz
  have hρ_le : max y |e| ≤ 1 := by linarith [max_le him hre]
  have hx_le_neg : x ≤ -0.31 := by linarith [(abs_le.mp hre).2, sigmaStar_lt_neg_041]
  have hleft : leftSlitEntropy x y ≤ 2 := by
    have hP_tail : ∀ τ : ℝ, 1 < τ → poissonKernel x y τ ≤ y / (π * τ ^ 2) := by
      intro τ hτ; unfold poissonKernel
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : τ ^ 2 ≤ (τ - x) ^ 2 := by nlinarith
      have hpi := Real.pi_pos
      have h1 : y * (π * τ ^ 2) ≤ y * (π * (τ - x) ^ 2) := by gcongr
      linarith [mul_nonneg hy.le (mul_nonneg hpi.le (sq_nonneg y))]
    have hleft_dens : ∀ σ : ℝ, 1 < σ → leftSlitDensity x y σ ≤ 1 / |σ - sigmaPlus| := by
      intro σ hσ1
      by_cases hsp : σ = sigmaPlus
      · subst hsp; unfold leftSlitDensity; rw [leftSlitInv_sigmaPlus]; unfold invJacobian; simp
      · have h1 : poissonKernel x y σ * invJacobian σ ≤ 4 * y / |σ - sigmaPlus| := by
          calc poissonKernel x y σ * invJacobian σ
              ≤ (y / (π * σ ^ 2)) * (4 * π * σ * (σ - 1) / |σ - sigmaPlus|) :=
                mul_le_mul (hP_tail σ hσ1) (invJacobian_gt_one_le hσ1) (invJacobian_nonneg _)
                  (by positivity)
            _ = 4 * y * ((σ - 1) / σ) / |σ - sigmaPlus| := by
                field_simp [Real.pi_pos.ne', show σ ≠ 0 by linarith]
            _ ≤ 4 * y * 1 / |σ - sigmaPlus| := by gcongr; rw [div_le_one (by linarith)]; linarith
            _ = 4 * y / |σ - sigmaPlus| := by ring
        let τ := leftSlitInv σ
        have hτ1 : 1 < τ := leftSlitInv_gt_one hσ1
        have h2 : poissonKernel x y τ * invJacobian τ ≤ 4 * √2 * y / |σ - sigmaPlus| := by
          calc poissonKernel x y τ * invJacobian τ
              ≤ (y / (π * τ ^ 2)) * (4 * π * τ * (τ - 1) / |τ - sigmaPlus|) :=
                mul_le_mul (hP_tail τ hτ1) (invJacobian_gt_one_le hτ1) (invJacobian_nonneg _)
                  (by positivity)
            _ = (4 * y / τ) * ((τ - 1) / |τ - sigmaPlus|) := by
                field_simp [Real.pi_pos.ne', show τ ≠ 0 by linarith]
            _ ≤ (4 * y / 1) * (√2 / |σ - sigmaPlus|) := by
                rw [leftSlitInv_ratio hσ1 hsp]; gcongr
            _ = 4 * √2 * y / |σ - sigmaPlus| := by ring
        have hcoeff : (4 + 4 * √2) * y ≤ 1 := by
          have : 4 + 4 * √2 ≤ 10 := by linarith [sqrt_two_lt_1415]
          nlinarith
        unfold leftSlitDensity
        calc poissonKernel x y σ * invJacobian σ + poissonKernel x y τ * invJacobian τ
            ≤ ((4 + 4 * √2) * y) / |σ - sigmaPlus| := by linarith [show 4 * y / |σ - sigmaPlus| +
              4 * √2 * y / |σ - sigmaPlus| = ((4 + 4 * √2) * y) / |σ - sigmaPlus| by ring]
          _ ≤ 1 / |σ - sigmaPlus| := by gcongr
    have hint_left := (leftSlitEntropy_integrable_and_le (x := x) (y := y)
      (R := 0.1) (y_min := y) (y_max := y) (by norm_num) hy le_rfl le_rfl hre).1
    have hint_sp : IntegrableOn (fun σ => max 0 (Real.log (1 / |σ - sigmaPlus|))) (Ioi 1) :=
      (integrable_posLog_inv_abs_sub sigmaPlus).integrableOn
    have hmono : leftSlitEntropy x y ≤
        ∫ σ in Ioi 1, max 0 (Real.log (1 / |σ - sigmaPlus|)) := by
      unfold leftSlitEntropy
      refine setIntegral_mono_on hint_left hint_sp measurableSet_Ioi fun σ hσ => ?_
      have hP_le1 : poissonKernel x y σ ≤ 1 := by
        rcases le_or_gt σ 2 with hle | hgt
        · unfold poissonKernel
          rw [div_le_one (by positivity)]
          have h1 : 1 ≤ (σ - x) ^ 2 := by nlinarith [mem_Ioi.mp hσ]
          nlinarith [Real.pi_gt_d4, sq_nonneg y]
        · exact (hP_tail σ (mem_Ioi.mp hσ)).trans (by
            rw [div_le_one (by positivity)]
            have : 1 ≤ σ ^ 2 := by nlinarith
            nlinarith [Real.pi_gt_d4])
      calc poissonKernel x y σ * max 0 (Real.log (leftSlitDensity x y σ))
          ≤ 1 * max 0 (Real.log (1 / |σ - sigmaPlus|)) :=
            mul_le_mul hP_le1 (posLog_le_posLog_of_nonneg (leftSlitDensity_nonneg x hy.le σ)
              (hleft_dens σ (mem_Ioi.mp hσ))) (le_max_left 0 _) zero_le_one
        _ = max 0 (Real.log (1 / |σ - sigmaPlus|)) := one_mul _
    exact hmono.trans (setIntegral_posLog_inv_abs_sub_le sigmaPlus (Ioi 1))
  let K_R : ℝ := 2.61 * (1 + √2) / π
  have hKR_gt1 : 1 < K_R := by
    dsimp [K_R]; rw [one_lt_div Real.pi_pos]; nlinarith [Real.pi_lt_d4, sqrt_two_gt_1414]
  have hlogKR_nn : 0 ≤ Real.log K_R := Real.log_nonneg hKR_gt1.le
  have hlog_invy_nn : 0 ≤ Real.log (1 / y) := Real.log_nonneg ((one_le_div hy).mpr (by linarith))
  have hint_P := integrable_poissonKernel x hy
  have hint_unit := integrable_poissonKernel_mul_posLog_div x y 1 hy one_pos
  have hint_right := integrableOn_rightSlitEntropy x hy
  have hright : rightSlitEntropy x y ≤ Real.log K_R + Real.log (1 / y) +
      ∫ σ : ℝ, poissonKernel (sigmaStar + e) y σ * max 0 (Real.log (1 / |σ - sigmaStar|)) := by
    unfold rightSlitEntropy
    let dom : ℝ → ℝ := fun σ =>
      poissonKernel x y σ * (Real.log K_R + Real.log (1 / y)) +
        poissonKernel x y σ * max 0 (Real.log (1 / |σ - sigmaStar|))
    have hint_dom : Integrable dom := (hint_P.mul_const _).add hint_unit
    have h1 : ∫ σ in Ioo (-1) 0, poissonKernel x y σ * max 0 (Real.log (rightSlitDensity x y σ)) ≤
        ∫ σ in Ioo (-1) 0, dom σ := by
      refine setIntegral_mono_on hint_right hint_dom.integrableOn measurableSet_Ioo fun σ hσ => ?_
      have hdens : rightSlitDensity x y σ ≤ K_R * (1 / y) / |σ - sigmaStar| :=
        (rightSlitDensity_le hy hσ).trans_eq (by dsimp [K_R]; ring)
      have hL_le : max 0 (Real.log (rightSlitDensity x y σ)) ≤
          Real.log K_R + Real.log (1 / y) + max 0 (Real.log (1 / |σ - sigmaStar|)) := by
        refine (posLog_le_posLog_of_nonneg (rightSlitDensity_nonneg x hy.le σ) hdens).trans ?_
        by_cases hσ_star : σ = sigmaStar
        · subst hσ_star; simpa [one_div] using add_nonneg hlogKR_nn hlog_invy_nn
        · rw [div_eq_mul_one_div, Real.log_mul (mul_pos (zero_lt_one.trans hKR_gt1)
              (one_div_pos.mpr hy)).ne' (one_div_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hσ_star))).ne',
            Real.log_mul (zero_lt_one.trans hKR_gt1).ne' (one_div_pos.mpr hy).ne']
          exact posLog_add_le_single (add_nonneg hlogKR_nn hlog_invy_nn)
      dsimp [dom]; rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hL_le (poissonKernel_nonneg hy.le σ)
    have h2 : ∫ σ in Ioo (-1) 0, dom σ ≤ ∫ σ : ℝ, dom σ :=
      setIntegral_le_integral hint_dom (Eventually.of_forall fun σ =>
        add_nonneg (mul_nonneg (poissonKernel_nonneg hy.le σ) (add_nonneg hlogKR_nn hlog_invy_nn))
          (mul_nonneg (poissonKernel_nonneg hy.le σ) (le_max_left 0 _)))
    have h3 : ∫ σ : ℝ, dom σ = (Real.log K_R + Real.log (1 / y)) +
        ∫ σ : ℝ, poissonKernel (sigmaStar + e) y σ * max 0 (Real.log (1 / |σ - sigmaStar|)) := by
      dsimp [dom]
      rw [integral_add (hint_P.mul_const _) hint_unit, integral_mul_const,
        integral_poissonKernel x hy, one_mul, ← hx_eq]
    exact h1.trans (h2.trans h3.le)
  have hunit := lemmaS_poisson_log_unit_bound hy hρ_le
  have hx_cast : (x : ℂ) = (sigmaStar : ℂ) + (e : ℂ) := by rw [hx_eq]; push_cast; rfl
  rw [← hx_eq, ← hx_cast] at hunit
  rw [← hx_eq] at hright
  dsimp [K_R] at hright
  unfold slitEntropy slitEntropyComplexConst
  linarith

/-- **Lemma S (b), real slice.** Given two-sided real-slice preimage bounds
`|xUHP δ - σ_*| ≤ C_e δ` and `c_y √δ ≤ yUHP δ ≤ C_y √δ` for `0 < δ ≤ ξ_*`,
`S(x) ≤ 2 log(1/y) + C ≤ log(1/δ) + C'`. -/
theorem lemmaS_real {xUHP yUHP : ℝ → ℝ} {C_e c_y C_y : ℝ}
    (hCe : 0 ≤ C_e) (hcy : 0 < c_y) (hCy : c_y ≤ C_y)
    (hx : ∀ δ ∈ Ioc 0 xiStar, |xUHP δ - sigmaStar| ≤ C_e * δ)
    (hy_lo : ∀ δ ∈ Ioc 0 xiStar, c_y * Real.sqrt δ ≤ yUHP δ)
    (hy_hi : ∀ δ ∈ Ioc 0 xiStar, yUHP δ ≤ C_y * Real.sqrt δ) :
    ∃ C C' : ℝ, ∀ δ ∈ Ioc 0 xiStar,
      slitEntropy (xUHP δ) (yUHP δ) ≤ 2 * Real.log (1 / yUHP δ) + C ∧
        2 * Real.log (1 / yUHP δ) + C ≤ Real.log (1 / δ) + C' := by
  let C0 : ℝ := max 1 (max C_e C_y)
  let δ₁ : ℝ := (0.1 / (2 * C0)) ^ 2
  have hδ₁_pos : 0 < δ₁ := by positivity
  let y_min : ℝ := c_y * Real.sqrt δ₁
  let y_max : ℝ := C_y * Real.sqrt xiStar
  let R : ℝ := C_e * xiStar
  have hy_min_pos : 0 < y_min := mul_pos hcy (Real.sqrt_pos.mpr hδ₁_pos)
  have hy_max_pos : 0 < y_max := mul_pos (hcy.trans_le hCy) (Real.sqrt_pos.mpr xiStar_pos)
  let B : ℝ := 2 * (R + 1) + 3
  let C_far : ℝ := 32 * y_max + 16 * √2 / y_min
  let C_near : ℝ := (4 * B ^ 2 + 4 * √2 * B) / y_min + 32 * y_max * B
  let C_right : ℝ := max 0 (Real.log (2.61 * (1 + √2) / (π * y_min))) + 2 / (π * y_min)
  let C_left : ℝ := max (max 0 (Real.log C_far)) (max 0 (Real.log C_near)) + 2 / (π * y_min)
  let C : ℝ := max slitEntropyComplexConst (C_right + C_left + 2 * max 0 (Real.log y_max))
  refine ⟨C, C - 2 * Real.log c_y, fun δ hδ => ?_⟩
  have hδ_pos : 0 < δ := hδ.1
  have hy_pos : 0 < yUHP δ := lt_of_lt_of_le (mul_pos hcy (Real.sqrt_pos.mpr hδ_pos)) (hy_lo δ hδ)
  have hpart1 : slitEntropy (xUHP δ) (yUHP δ) ≤ 2 * Real.log (1 / yUHP δ) + C := by
    by_cases hsmall : δ ≤ δ₁
    · have hz := realSlice_mem_ball hδ_pos hy_pos hsmall (hx δ hδ) (hy_hi δ hδ)
      have hc := lemmaS_complex hy_pos hz
      have hy_le_norm : yUHP δ ≤ ‖(xUHP δ : ℂ) + (yUHP δ : ℂ) * I - (sigmaStar : ℂ)‖ := by
        have him_eq : Complex.im ((xUHP δ : ℂ) + (yUHP δ : ℂ) * I - (sigmaStar : ℂ)) = yUHP δ := by
          simp
        simpa [him_eq, abs_of_pos hy_pos] using
          Complex.abs_im_le_norm ((xUHP δ : ℂ) + (yUHP δ : ℂ) * I - (sigmaStar : ℂ))
      have hlog_norm : Real.log (1 / ‖(xUHP δ : ℂ) + (yUHP δ : ℂ) * I - (sigmaStar : ℂ)‖) ≤
          Real.log (1 / yUHP δ) :=
        Real.log_le_log (one_div_pos.mpr (hy_pos.trans_le hy_le_norm))
          (one_div_le_one_div_of_le hy_pos hy_le_norm)
      linarith [le_max_left slitEntropyComplexConst (C_right + C_left + 2 * max 0 (Real.log y_max))]
    · push Not at hsmall
      have hy_lo_δ : y_min ≤ yUHP δ :=
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsmall.le) hcy.le).trans (hy_lo δ hδ)
      have hy_hi_δ : yUHP δ ≤ y_max :=
        (hy_hi δ hδ).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδ.2) (hcy.trans_le hCy).le)
      have hre_δ : |xUHP δ - sigmaStar| ≤ R :=
        (hx δ hδ).trans (mul_le_mul_of_nonneg_left hδ.2 hCe)
      have hleft_le :=
        (leftSlitEntropy_integrable_and_le (mul_nonneg hCe xiStar_pos.le) hy_min_pos hy_lo_δ
          hy_hi_δ hre_δ).2
      have hright_le : rightSlitEntropy (xUHP δ) (yUHP δ) ≤ C_right := by
        let C0_r : ℝ := 2.61 * (1 + √2) / (π * y_min)
        have hint_P := integrable_poissonKernel (xUHP δ) hy_pos
        have hint_r := integrableOn_rightSlitEntropy (xUHP δ) hy_pos
        let dom : ℝ → ℝ := fun σ =>
          poissonKernel (xUHP δ) (yUHP δ) σ * max 0 (Real.log C0_r) +
            (π * y_min)⁻¹ * max 0 (Real.log (1 / |σ - sigmaStar|))
        have hdom_on : IntegrableOn dom (Ioo (-1) 0) :=
          (hint_P.integrableOn.mul_const _).add
            ((integrable_posLog_inv_abs_sub sigmaStar).integrableOn.const_mul _)
        have h1 : rightSlitEntropy (xUHP δ) (yUHP δ) ≤ ∫ σ in Ioo (-1) 0, dom σ := by
          unfold rightSlitEntropy
          refine setIntegral_mono_on hint_r hdom_on measurableSet_Ioo fun σ hσ => ?_
          have hP_ub : poissonKernel (xUHP δ) (yUHP δ) σ ≤ (π * y_min)⁻¹ := by
            have h1 := (poissonKernel_le_inv_pi_mul_y (x := xUHP δ) hy_pos σ).trans
              (one_div_le_one_div_of_le (mul_pos Real.pi_pos hy_min_pos)
                (mul_le_mul_of_nonneg_left hy_lo_δ Real.pi_pos.le))
            rwa [one_div] at h1
          have hdens : rightSlitDensity (xUHP δ) (yUHP δ) σ ≤ C0_r / |σ - sigmaStar| :=
            (rightSlitDensity_le hy_pos hσ).trans (by dsimp [C0_r]; gcongr)
          have hL_le := (posLog_le_posLog_of_nonneg (rightSlitDensity_nonneg _ hy_pos.le σ)
            hdens).trans (posLog_div_le_posLog_add (by positivity : 0 ≤ C0_r))
          dsimp [dom]
          calc poissonKernel (xUHP δ) (yUHP δ) σ *
                  max 0 (Real.log (rightSlitDensity (xUHP δ) (yUHP δ) σ))
              ≤ poissonKernel (xUHP δ) (yUHP δ) σ *
                  (max 0 (Real.log C0_r) + max 0 (Real.log (1 / |σ - sigmaStar|))) :=
                mul_le_mul_of_nonneg_left hL_le (poissonKernel_nonneg hy_pos.le σ)
            _ = poissonKernel (xUHP δ) (yUHP δ) σ * max 0 (Real.log C0_r) +
                  poissonKernel (xUHP δ) (yUHP δ) σ * max 0 (Real.log (1 / |σ - sigmaStar|)) := by ring
            _ ≤ poissonKernel (xUHP δ) (yUHP δ) σ * max 0 (Real.log C0_r) +
                  (π * y_min)⁻¹ * max 0 (Real.log (1 / |σ - sigmaStar|)) := by gcongr
        have hdom_split : ∫ σ in Ioo (-1) 0, dom σ =
            (∫ σ in Ioo (-1) 0, poissonKernel (xUHP δ) (yUHP δ) σ * max 0 (Real.log C0_r)) +
              (π * y_min)⁻¹ * ∫ σ in Ioo (-1) 0, max 0 (Real.log (1 / |σ - sigmaStar|)) := by
          dsimp [dom]
          rw [integral_add (hint_P.integrableOn.mul_const _)
              ((integrable_posLog_inv_abs_sub sigmaStar).integrableOn.const_mul _),
            integral_const_mul]
        have hP_le1 : ∫ σ in Ioo (-1) 0,
            poissonKernel (xUHP δ) (yUHP δ) σ * max 0 (Real.log C0_r) ≤ max 0 (Real.log C0_r) := by
          rw [integral_mul_const]
          calc (∫ σ in Ioo (-1) 0, poissonKernel (xUHP δ) (yUHP δ) σ) * max 0 (Real.log C0_r)
              ≤ (∫ σ : ℝ, poissonKernel (xUHP δ) (yUHP δ) σ) * max 0 (Real.log C0_r) :=
                mul_le_mul_of_nonneg_right (setIntegral_le_integral hint_P
                  (Eventually.of_forall fun σ => poissonKernel_nonneg hy_pos.le σ)) (le_max_left 0 _)
            _ = max 0 (Real.log C0_r) := by rw [integral_poissonKernel _ hy_pos, one_mul]
        have hlog_le2 := setIntegral_posLog_inv_abs_sub_le sigmaStar (Ioo (-1) 0)
        calc rightSlitEntropy (xUHP δ) (yUHP δ) ≤ ∫ σ in Ioo (-1) 0, dom σ := h1
          _ ≤ max 0 (Real.log C0_r) + (π * y_min)⁻¹ * 2 := by rw [hdom_split]; gcongr
          _ = C_right := by dsimp [C_right, C0_r]; ring
      have hlog_y_lb : -max 0 (Real.log y_max) ≤ Real.log (1 / yUHP δ) := by
        have h1 : Real.log (1 / y_max) ≤ Real.log (1 / yUHP δ) :=
          Real.log_le_log (one_div_pos.mpr hy_max_pos) (one_div_le_one_div_of_le hy_pos hy_hi_δ)
        rw [one_div, Real.log_inv] at h1
        linarith [le_max_right 0 (Real.log y_max)]
      have hS_le : slitEntropy (xUHP δ) (yUHP δ) ≤ C_right + C_left :=
        add_le_add hright_le hleft_le
      linarith [le_max_right slitEntropyComplexConst (C_right + C_left + 2 * max 0 (Real.log y_max))]
  have hpart2 : 2 * Real.log (1 / yUHP δ) + C ≤ Real.log (1 / δ) + (C - 2 * Real.log c_y) := by
    have hsq_le : c_y ^ 2 * δ ≤ yUHP δ ^ 2 := by
      have := hy_lo δ hδ
      nlinarith [mul_nonneg hcy.le (Real.sqrt_nonneg δ), Real.sq_sqrt hδ_pos.le]
    have hlog_sq : 2 * Real.log (1 / yUHP δ) = Real.log (1 / yUHP δ ^ 2) := by
      rw [show (2 : ℝ) * Real.log (1 / yUHP δ) = ((2 : ℕ) : ℝ) * Real.log (1 / yUHP δ) by norm_num,
        ← Real.log_pow, one_div_pow]
    have hlog_ub : Real.log (1 / yUHP δ ^ 2) ≤ Real.log (1 / (c_y ^ 2 * δ)) :=
      Real.log_le_log (one_div_pos.mpr (pow_pos hy_pos 2))
        (one_div_le_one_div_of_le (mul_pos (pow_pos hcy 2) hδ_pos) hsq_le)
    have hsplit : Real.log (1 / (c_y ^ 2 * δ)) = Real.log (1 / δ) - 2 * Real.log c_y := by
      rw [show 1 / (c_y ^ 2 * δ) = (1 / δ) * (c_y ^ 2)⁻¹ by ring,
        Real.log_mul (one_div_pos.mpr hδ_pos).ne' (inv_pos.mpr (pow_pos hcy 2)).ne',
        Real.log_inv, Real.log_pow]
      norm_num; ring
    linarith
  exact ⟨hpart1, hpart2⟩

/-! ### Section 4: Exact deficit lower bound -/

/-- Exact slit-strip deficit `κ(δ) = (4/3) ∫_{ξ_* - δ}^{ξ_*} arccos(sinh(π s)) ds`. -/
noncomputable def slitDeficit (δ : ℝ) : ℝ :=
  (4 / 3 : ℝ) * ∫ s in (xiStar - δ)..xiStar, Real.arccos (Real.sinh (π * s))

/-- Elementary trigonometric lower bound `√(2(1 - v)) ≤ arccos v` for `0 ≤ v ≤ 1`. -/
theorem arccos_ge_sqrt_two_mul_one_sub {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.sqrt (2 * (1 - v)) ≤ Real.arccos v := by
  let θ : ℝ := Real.arccos v
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg v
  have hθpi : θ ≤ π := Real.arccos_le_pi v
  have hcos : Real.cos θ = v := Real.cos_arccos (by linarith) hv1
  have h1c : 1 - v = 2 * Real.sin (θ / 2) ^ 2 := by
    conv_lhs => rw [← hcos, show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsin_le : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le (by linarith)
  have hsq : 2 * (1 - v) ≤ θ ^ 2 := by
    rw [h1c]; have := pow_le_pow_left₀ hsin_nn hsin_le 2; linarith
  exact Real.sqrt_le_iff.mpr ⟨hθ0, hsq⟩

/-- Elementary hyperbolic slope bound `π u ≤ 1 - sinh(π (ξ_* - u))` for `0 ≤ u`. -/
theorem one_sub_sinh_pi_ge {u : ℝ} (hu : 0 ≤ u) :
    π * u ≤ 1 - Real.sinh (π * (xiStar - u)) := by
  let f : ℝ → ℝ := fun t => 1 - Real.sinh (π * (xiStar - t)) - π * t
  have hf0 : f 0 = 0 := by
    dsimp [f]; rw [sub_zero, mul_zero, sub_zero, sinh_pi_mul_xiStar, sub_self]
  have hd : ∀ t : ℝ, HasDerivAt f (π * Real.cosh (π * (xiStar - t)) - π) t := by
    intro t
    have hlin : HasDerivAt (fun s => π * (xiStar - s)) (-π) t := by
      have hsub : HasDerivAt (fun s => xiStar - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub xiStar
      exact (hsub.const_mul π).congr_deriv (by ring)
    have hsinh := (Real.hasDerivAt_sinh _).comp t hlin
    have hlin2 : HasDerivAt (fun s => π * s) π t := by simpa using (hasDerivAt_id t).const_mul π
    exact (((hasDerivAt_const t (1 : ℝ)).sub hsinh).sub hlin2).congr_deriv (by ring)
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) fun t _ => ?_
    rw [(hd t).deriv]; nlinarith [Real.one_le_cosh (π * (xiStar - t)), Real.pi_pos]
  have hle : f 0 ≤ f u := hmono le_rfl hu hu
  rw [hf0] at hle; dsimp [f] at hle; linarith

/-- Exact prefactor deficit lower bound `(8/9) √(2π) δ^{3/2} ≤ κ(δ)` for `0 ≤ δ ≤ ξ_*`. -/
theorem slitDeficit_ge_exact {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ xiStar) :
    (8 / 9 : ℝ) * Real.sqrt (2 * π) * δ ^ ((3 : ℝ) / 2) ≤ slitDeficit δ := by
  have hsub : ∫ s in (xiStar - δ)..xiStar, Real.arccos (Real.sinh (π * s)) =
      ∫ u in (0 : ℝ)..δ, Real.arccos (Real.sinh (π * (xiStar - u))) := by
    rw [intervalIntegral.integral_comp_sub_left (fun s => Real.arccos (Real.sinh (π * s))) xiStar]
    simp
  have hlhs_int : IntervalIntegrable (fun u : ℝ => Real.sqrt (2 * π) * u ^ (1 / 2 : ℝ))
      volume 0 δ :=
    (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num))).intervalIntegrable 0 δ
  have hrhs_int : IntervalIntegrable (fun u : ℝ => Real.arccos (Real.sinh (π * (xiStar - u))))
      volume 0 δ :=
    (Real.continuous_arccos.comp (Real.continuous_sinh.comp (by fun_prop))).intervalIntegrable 0 δ
  have hmono : ∫ u in (0 : ℝ)..δ, Real.sqrt (2 * π) * u ^ (1 / 2 : ℝ) ≤
      ∫ u in (0 : ℝ)..δ, Real.arccos (Real.sinh (π * (xiStar - u))) := by
    refine intervalIntegral.integral_mono_on hδ0 hlhs_int hrhs_int fun u hu => ?_
    have hv0 : 0 ≤ Real.sinh (π * (xiStar - u)) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le (by linarith [hu.2]))
    have hv1 : Real.sinh (π * (xiStar - u)) ≤ 1 := by
      calc Real.sinh (π * (xiStar - u)) ≤ Real.sinh (π * xiStar) :=
            Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left (by linarith [hu.1]) Real.pi_pos.le)
        _ = 1 := sinh_pi_mul_xiStar
    have h1 : Real.sqrt (2 * π) * u ^ (1 / 2 : ℝ) = Real.sqrt (2 * (π * u)) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity), mul_assoc]
    exact h1.trans_le ((Real.sqrt_le_sqrt (by linarith [one_sub_sinh_pi_ge hu.1])).trans
      (arccos_ge_sqrt_two_mul_one_sub hv0 hv1))
  have hval : ∫ u in (0 : ℝ)..δ, Real.sqrt (2 * π) * u ^ (1 / 2 : ℝ) =
      (2 / 3 : ℝ) * Real.sqrt (2 * π) * δ ^ ((3 : ℝ) / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      Real.zero_rpow (by norm_num), sub_zero, show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num]
    ring
  unfold slitDeficit; rw [hsub]
  calc (8 / 9 : ℝ) * Real.sqrt (2 * π) * δ ^ ((3 : ℝ) / 2)
      = (4 / 3 : ℝ) * ∫ u in (0 : ℝ)..δ, Real.sqrt (2 * π) * u ^ (1 / 2 : ℝ) := by rw [hval]; ring
    _ ≤ (4 / 3 : ℝ) * ∫ u in (0 : ℝ)..δ, Real.arccos (Real.sinh (π * (xiStar - u))) := by gcongr

/-- Numerical deficit lower bound `2.228 δ^{3/2} ≤ κ(δ)` for `0 ≤ δ ≤ ξ_*`. -/
theorem slitDeficit_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ xiStar) :
    (2.228 : ℝ) * δ ^ ((3 : ℝ) / 2) ≤ slitDeficit δ := by
  have hsqrt : (2.5065 : ℝ) ≤ Real.sqrt (2 * π) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.5065)]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_d4])
  exact (mul_le_mul_of_nonneg_right (by linarith : (2.228 : ℝ) ≤ (8 / 9 : ℝ) * Real.sqrt (2 * π))
    (Real.rpow_nonneg hδ0 _)).trans (slitDeficit_ge_exact hδ0 hδ1)

private lemma slitDeficit_mono {δ₁ δ₂ : ℝ} (h1 : 0 ≤ δ₁) (h12 : δ₁ ≤ δ₂) (_h2 : δ₂ ≤ xiStar) :
    slitDeficit δ₁ ≤ slitDeficit δ₂ := by
  unfold slitDeficit; gcongr
  have hint : IntervalIntegrable (fun s : ℝ => Real.arccos (Real.sinh (π * s)))
      volume (xiStar - δ₂) xiStar :=
    (Real.continuous_arccos.comp (Real.continuous_sinh.comp (by fun_prop))).intervalIntegrable _ _
  have hI1 : uIcc (xiStar - δ₂) (xiStar - δ₁) ⊆ uIcc (xiStar - δ₂) xiStar := by
    rw [uIcc_of_le (by linarith : xiStar - δ₂ ≤ xiStar - δ₁),
      uIcc_of_le (by linarith : xiStar - δ₂ ≤ xiStar)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hI2 : uIcc (xiStar - δ₁) xiStar ⊆ uIcc (xiStar - δ₂) xiStar := by
    rw [uIcc_of_le (by linarith : xiStar - δ₁ ≤ xiStar),
      uIcc_of_le (by linarith : xiStar - δ₂ ≤ xiStar)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hsub := intervalIntegral.integral_add_adjacent_intervals (hint.mono_set hI1)
    (hint.mono_set hI2)
  have hnn : 0 ≤ ∫ s in (xiStar - δ₂)..(xiStar - δ₁), Real.arccos (Real.sinh (π * s)) :=
    intervalIntegral.integral_nonneg (by linarith) fun s _ => Real.arccos_nonneg _
  linarith

/-! ### Section 5: Proposition M, Theorem A, and non-vacuity -/

/-- Real-slice preimage coordinates `z(ξ_* - δ) = xUHP δ + i yUHP δ` for `δ ∈ (0, ξ_*]`. -/
structure RealSliceData where
  xUHP : ℝ → ℝ
  yUHP : ℝ → ℝ
  C_e : ℝ
  c_y : ℝ
  C_y : ℝ
  hC_e : 0 ≤ C_e
  hc_y : 0 < c_y
  hC_y : c_y ≤ C_y
  re_bound : ∀ δ ∈ Ioc 0 xiStar, |xUHP δ - sigmaStar| ≤ C_e * δ
  im_lower : ∀ δ ∈ Ioc 0 xiStar, c_y * Real.sqrt δ ≤ yUHP δ
  im_upper : ∀ δ ∈ Ioc 0 xiStar, yUHP δ ≤ C_y * Real.sqrt δ

/-- Slit harmonic mass `m(x)` at `x ∈ [0, ξ_*)`. -/
noncomputable def RealSliceData.slitMassAt (rs : RealSliceData) (x : ℝ) : ℝ :=
  slitMass (rs.xUHP (xiStar - x)) (rs.yUHP (xiStar - x))

/-- Slit harmonic-measure entropy `S(x)` at `x ∈ [0, ξ_*)`. -/
noncomputable def RealSliceData.slitEntropyAt (rs : RealSliceData) (x : ℝ) : ℝ :=
  slitEntropy (rs.xUHP (xiStar - x)) (rs.yUHP (xiStar - x))

/-- Upstream strip Poisson--Jensen and `(G-deficit)` parameters (uniform across tests). -/
structure PoissonJensenInput where
  rs : RealSliceData
  c_PJ : ℝ
  C_PJ : ℝ
  C_K : ℝ
  U : ℝ → ℝ
  hc_PJ : 1 ≤ c_PJ
  hC_K : 0 < C_K
  g_deficit : ∀ x ∈ Ico 0 xiStar, U x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x)

/-- Upstream fixed-gap deep-lobe exponential decay parameters at `x₀ = 0.05`. -/
structure FixedGapInput where
  c_deep : ℝ
  C_deep : ℝ
  κ_deep : ℝ
  hc_deep : 1 ≤ c_deep
  hC_deep : 0 ≤ C_deep
  hκ_deep : 0 < κ_deep

/-- Weakly feasible test function `g` at central charge shift `c' = c - 1`. -/
structure WeaklyFeasibleTest (pj : PoissonJensenInput) (fg : FixedGapInput) (c' : ℝ) where
  g : ℝ → ℝ
  V : ℝ → ℝ
  K_a : ℝ → ℝ
  M : ℝ
  t₁ : ℝ
  hM_pos : 0 < M
  ht₁_nonneg : 0 ≤ t₁
  hg_cont : ContinuousOn g (Ici 0)
  hV_cont : ContinuousOn V (Ici 0)
  hV_nonneg : ∀ t ≥ 0, 0 ≤ V t
  hM_int : IntegrableOn (fun t => |g t| * V t) (Ioi 0)
  hM_eq : ∫ t in Ioi 0, |g t| * V t = M
  hV_le_two_Ka : ∀ x ∈ Icc (0.05 : ℝ) xiStar, V (c' * x ^ 2 / 3) ≤ 2 * K_a (c' * x ^ 2 / 3)
  hKa_ub : ∀ x ∈ Icc (0.05 : ℝ) xiStar,
    K_a (c' * x ^ 2 / 3) ≤ pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) / Real.sqrt c'
  hPJ : ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
    Real.log |g (c' * x ^ 2 / 3)| ≤ c' * pj.U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
      (5 / 2 : ℝ) * (1 - pj.rs.slitMassAt x) * Real.log c' + pj.rs.slitEntropyAt x + pj.C_PJ
  hDeepLobe : fg.c_deep ≤ c' →
    ∫ t in (0 : ℝ)..(c' * (0.05 : ℝ) ^ 2 / 3), |g t| * V t ≤
      fg.C_deep * Real.exp (-fg.κ_deep * c') * M
  hHalfMass : M / 2 ≤ ∫ t in (0 : ℝ)..t₁, |g t| * V t

/-- **Proposition M (majorant at the Airy scale).** Substituting Lemma E(b) and Lemma S(b)
into the analytic strip Poisson--Jensen estimate yields the log-free Airy-scale majorant. -/
theorem proposition_M (rs : RealSliceData) {c_PJ C_PJ : ℝ} (hc_PJ : 1 ≤ c_PJ) :
    ∃ C_M1 C_M2 : ℝ, 0 ≤ C_M1 ∧
      ∀ {c' M : ℝ} {U g : ℝ → ℝ}, c_PJ ≤ c' → 0 < M →
        (∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
          Real.log |g (c' * x ^ 2 / 3)| ≤ c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
            (5 / 2 : ℝ) * (1 - rs.slitMassAt x) * Real.log c' + rs.slitEntropyAt x + C_PJ) →
        ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
          Real.log |g (c' * x ^ 2 / 3)| ≤ c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
            C_M1 * Real.sqrt (xiStar - x) * Real.log c' + Real.log (1 / (xiStar - x)) + C_M2 := by
  obtain ⟨C_E, _, hE⟩ := lemmaE_real rs.hC_e rs.hc_y rs.hC_y rs.re_bound rs.im_lower rs.im_upper
  obtain ⟨_, C_S', hS⟩ := lemmaS_real rs.hC_e rs.hc_y rs.hC_y rs.re_bound rs.im_lower rs.im_upper
  refine ⟨(5 / 2 : ℝ) * C_E, C_S' + C_PJ, by positivity, fun {c' M U g} hc' _ hPJ x hx hne => ?_⟩
  have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg (hc_PJ.trans hc')
  have hδ : xiStar - x ∈ Ioc 0 xiStar := ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
  have hm_raw : 1 - rs.slitMassAt x ≤ C_E * Real.sqrt (xiStar - x) := hE (xiStar - x) hδ
  have hm_term : (5 / 2 : ℝ) * (1 - rs.slitMassAt x) * Real.log c' ≤
      (5 / 2 : ℝ) * C_E * Real.sqrt (xiStar - x) * Real.log c' :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_raw (by norm_num)) hlogc'_nn).trans_eq
      (by ring)
  have hS_ub : rs.slitEntropyAt x ≤ Real.log (1 / (xiStar - x)) + C_S' :=
    (hS (xiStar - x) hδ).1.trans (hS (xiStar - x) hδ).2
  linarith [hPJ x hx hne]

private lemma proposition_M_exp {C_M1 C_M2 c' M : ℝ} {U g : ℝ → ℝ}
    (hc' : 0 < c') (hM : 0 < M)
    (hprop : ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
      Real.log |g (c' * x ^ 2 / 3)| ≤ c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
        C_M1 * Real.sqrt (xiStar - x) * Real.log c' + Real.log (1 / (xiStar - x)) + C_M2)
    {x : ℝ} (hx : x ∈ Ico 0 xiStar) :
    |g (c' * x ^ 2 / 3)| ≤
      M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
        Real.exp (c' * U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2) := by
  by_cases h0 : g (c' * x ^ 2 / 3) = 0
  · rw [h0, abs_zero]; have := sub_pos.mpr hx.2; positivity
  · have hexp := Real.exp_le_exp.mpr (hprop x hx h0)
    rw [Real.exp_log (abs_pos.mpr h0)] at hexp
    have hδ_pos := sub_pos.mpr hx.2
    refine hexp.trans_eq ?_
    rw [show c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
          C_M1 * Real.sqrt (xiStar - x) * Real.log c' + Real.log (1 / (xiStar - x)) + C_M2 =
        (Real.log M + Real.log c' * (-(1 / 2 : ℝ)) + Real.log (1 / (xiStar - x))) +
          (c' * U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hM,
      Real.exp_log (one_div_pos.mpr hδ_pos), ← Real.rpow_def_of_pos hc']

private lemma airy_tail_integral_bound (pj : PoissonJensenInput) (fg : FixedGapInput)
    {C_M1 C_M2 c' lam0 : ℝ} (test : WeaklyFeasibleTest pj fg c')
    (hCM1_nn : 0 ≤ C_M1) (hc'_ge1 : 1 ≤ c')
    (hc'_log : (max 1 (6 * C_M1)) ^ 6 ≤ c') (hlam0_ge1 : 1 ≤ lam0)
    (hprop : ∀ x ∈ Ico 0 xiStar,
      |test.g (c' * x ^ 2 / 3)| ≤
        test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
          Real.exp (c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2))
    (hCpref_lt : (2 * pj.C_K * Real.exp C_M2) * Real.exp (-lam0) < 1 / 4)
    (hδ_c_lt : lam0 * c' ^ (-(2 / 3 : ℝ)) < xiStar - 0.05) :
    ∫ t in (c' * (0.05 : ℝ) ^ 2 / 3)..(c' * (xiStar - lam0 * c' ^ (-(2 / 3 : ℝ))) ^ 2 / 3),
      |test.g t| * test.V t < test.M / 4 := by
  have hc'_pos : 0 < c' := zero_lt_one.trans_le hc'_ge1
  have hlam0_pos : 0 < lam0 := zero_lt_one.trans_le hlam0_ge1
  let δ₀ : ℝ := xiStar - 0.05
  let δ_c : ℝ := lam0 * c' ^ (-(2 / 3 : ℝ))
  have hδ_c_pos : 0 < δ_c := mul_pos hlam0_pos (Real.rpow_pos_of_pos hc'_pos _)
  have hδ_c_lt_δ₀ : δ_c < δ₀ := hδ_c_lt
  have hx_c_gt : (0.05 : ℝ) < xiStar - δ_c := by dsimp [δ₀, δ_c] at hδ_c_lt_δ₀ ⊢; linarith
  let C_pref : ℝ := 2 * pj.C_K * Real.exp C_M2
  have hC_pref_pos : 0 < C_pref := mul_pos (mul_pos two_pos pj.hC_K) (Real.exp_pos C_M2)
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 / 3 : ℝ) * c' * x
  have hcov := intervalIntegral.integral_comp_mul_deriv'
    (fun x _ => (((hasDerivAt_pow 2 x).const_mul c').div_const 3).congr_deriv (by dsimp [φ']; ring))
    (by dsimp [φ']; fun_prop : ContinuousOn φ' (uIcc (0.05 : ℝ) (xiStar - δ_c)))
    (((test.hg_cont.abs).mul test.hV_cont).mono
      (by rintro t ⟨x, _, rfl⟩; exact mem_Ici.mpr (by dsimp [φ]; positivity)))
  have hφ_eq : ∫ t in (c' * (0.05 : ℝ) ^ 2 / 3)..(c' * (xiStar - δ_c) ^ 2 / 3),
      |test.g t| * test.V t =
      ∫ x in (0.05 : ℝ)..(xiStar - δ_c),
        |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x) := by
    simpa [φ, φ'] using hcov.symm
  have hint_x : IntervalIntegrable
      (fun x => |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x))
      volume 0.05 (xiStar - δ_c) :=
    ((((test.hg_cont.comp (by fun_prop) fun x _ => mem_Ici.mpr (by positivity)).abs).mul
      (test.hV_cont.comp (by fun_prop) fun x _ => mem_Ici.mpr (by positivity))).mul
      (by fun_prop)).intervalIntegrable_of_Icc hx_c_gt.le
  let F_x : ℝ → ℝ := fun x =>
    C_pref * test.M * (xiStar - x)⁻¹ *
      Real.exp (-2.228 * c' * (xiStar - x) ^ ((3 : ℝ) / 2) +
        C_M1 * Real.sqrt (xiStar - x) * Real.log c')
  let F_δ : ℝ → ℝ := fun δ =>
    C_pref * test.M * δ⁻¹ *
      Real.exp (-2.228 * c' * δ ^ ((3 : ℝ) / 2) + C_M1 * Real.sqrt δ * Real.log c')
  have hint_Fδ : IntervalIntegrable F_δ volume δ_c δ₀ := by
    have hcont1 : ContinuousOn (fun δ : ℝ => C_pref * test.M * δ⁻¹) (Icc δ_c δ₀) :=
      continuousOn_const.mul (continuousOn_id.inv₀ fun δ hδ => (lt_of_lt_of_le hδ_c_pos hδ.1).ne')
    have hcont2 : ContinuousOn (fun δ : ℝ => -2.228 * c' * δ ^ ((3 : ℝ) / 2)) (Icc δ_c δ₀) :=
      continuousOn_const.mul
        (continuousOn_id.rpow_const fun δ hδ => Or.inl (lt_of_lt_of_le hδ_c_pos hδ.1).ne')
    have hcont3 : ContinuousOn (fun δ : ℝ => C_M1 * Real.sqrt δ * Real.log c') (Icc δ_c δ₀) :=
      ((continuous_const.mul Real.continuous_sqrt).mul continuous_const).continuousOn
    exact (hcont1.mul (hcont2.add hcont3).rexp).intervalIntegrable_of_Icc hδ_c_lt_δ₀.le
  have hsub_δ : ∫ x in (0.05 : ℝ)..(xiStar - δ_c), F_x x = ∫ δ in δ_c..δ₀, F_δ δ := by
    change ∫ x in (0.05 : ℝ)..(xiStar - δ_c), F_δ (xiStar - x) = ∫ δ in δ_c..δ₀, F_δ δ
    rw [intervalIntegral.integral_comp_sub_left F_δ xiStar, sub_sub_cancel,
      show xiStar - (0.05 : ℝ) = δ₀ by rfl]
  have hint_Fx : IntervalIntegrable F_x volume 0.05 (xiStar - δ_c) := by
    have h := (hint_Fδ.comp_sub_left xiStar).symm
    dsimp [δ₀] at h
    rw [sub_sub_cancel] at h
    exact h
  have hmono_x : ∫ x in (0.05 : ℝ)..(xiStar - δ_c),
      |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x) ≤
      ∫ x in (0.05 : ℝ)..(xiStar - δ_c), F_x x := by
    refine intervalIntegral.integral_mono_on hx_c_gt.le hint_x hint_Fx fun x hx => ?_
    have hx_Ico : x ∈ Ico 0 xiStar := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hx_Icc : x ∈ Icc (0.05 : ℝ) xiStar := ⟨hx.1, by linarith [hx.2]⟩
    have hδ_pos := sub_pos.mpr hx_Ico.2
    have hG_ub := hprop x hx_Ico
    have hV_ub : test.V (c' * x ^ 2 / 3) ≤
        2 * pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ)) := by
      calc test.V (c' * x ^ 2 / 3) ≤ 2 * test.K_a (c' * x ^ 2 / 3) := test.hV_le_two_Ka x hx_Icc
        _ ≤ 2 * (pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) / Real.sqrt c') := by
            gcongr; exact test.hKa_ub x hx_Icc
        _ = 2 * pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hc'_pos.le]; ring
    have hdt_nn : 0 ≤ (2 / 3 : ℝ) * c' * x :=
      mul_nonneg (mul_nonneg (by norm_num) hc'_pos.le) (by linarith [hx.1])
    have hdt_ub : (2 / 3 : ℝ) * c' * x ≤ c' := by
      have hx1 : x ≤ 1 := by linarith [hx_Ico.2, xiStar_lt_one]
      calc (2 / 3 : ℝ) * c' * x ≤ (2 / 3 : ℝ) * c' * 1 := by gcongr
        _ ≤ c' := by linarith
    have hG_nn : 0 ≤ test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
        Real.exp (c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2) :=
      mul_nonneg (mul_nonneg (mul_nonneg test.hM_pos.le (Real.rpow_nonneg hc'_pos.le _))
        (one_div_nonneg.mpr hδ_pos.le)) (Real.exp_pos _).le
    have hGV := mul_le_mul hG_ub hV_ub (test.hV_nonneg _ (by positivity)) hG_nn
    have hV_rhs_nn : 0 ≤ 2 * pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg two_pos.le pj.hC_K.le) (Real.exp_pos _).le)
        (Real.rpow_nonneg hc'_pos.le _)
    have hGdt := mul_le_mul hGV hdt_ub hdt_nn (mul_nonneg hG_nn hV_rhs_nn)
    have hpow_cancel : c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) * c' = 1 := by
      rw [← Real.rpow_add hc'_pos]; norm_num
      rw [Real.rpow_neg_one, inv_mul_cancel₀ hc'_pos.ne']
    have hdef_ub : c' * (pj.U x + (2 * π / 3) * x) ≤ -2.228 * c' * (xiStar - x) ^ ((3 : ℝ) / 2) :=
      (mul_le_mul_of_nonneg_left
        ((pj.g_deficit x hx_Ico).trans (neg_le_neg (slitDeficit_ge hδ_pos.le (by linarith [hx.1]))))
        hc'_pos.le).trans_eq (by ring)
    have hprod_eq : (test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
          Real.exp (c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2)) *
          (2 * pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ))) * c' =
        C_pref * test.M * (xiStar - x)⁻¹ *
          Real.exp (c' * (pj.U x + (2 * π / 3) * x) +
            C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
      rw [show c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c' + C_M2 =
          (c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') + C_M2 by ring,
        Real.exp_add]
      have hexp_mul : Real.exp (c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
          Real.exp (c' * ((2 * π / 3) * x)) =
          Real.exp (c' * (pj.U x + (2 * π / 3) * x) +
            C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
        rw [← Real.exp_add]; congr 1; ring
      calc (test.M * c' ^ (-(1 / 2 : ℝ)) * (1 / (xiStar - x)) *
              (Real.exp (c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
                Real.exp C_M2)) *
              (2 * pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) * c' ^ (-(1 / 2 : ℝ))) * c'
          = (2 * pj.C_K * Real.exp C_M2) * test.M * (xiStar - x)⁻¹ *
              (c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) * c') *
              (Real.exp (c' * pj.U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
                Real.exp (c' * ((2 * π / 3) * x))) := by ring
        _ = C_pref * test.M * (xiStar - x)⁻¹ *
              Real.exp (c' * (pj.U x + (2 * π / 3) * x) +
                C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
            rw [hpow_cancel, mul_one, hexp_mul]
    refine hGdt.trans (hprod_eq.le.trans ?_)
    have hpref_nn : 0 ≤ C_pref * test.M * (xiStar - x)⁻¹ :=
      mul_nonneg (mul_nonneg hC_pref_pos.le test.hM_pos.le) (inv_nonneg.mpr hδ_pos.le)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by gcongr)) hpref_nn
  let s : ℝ := c' ^ (-(2 / 3 : ℝ))
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hc'_pos _
  let B_lam : ℝ := δ₀ / s
  have hlam0_le_B : lam0 ≤ B_lam := by dsimp [B_lam, s]; rw [le_div_iff₀ hs_pos]; exact hδ_c_lt_δ₀.le
  have hscale_lam : ∫ δ in δ_c..δ₀, F_δ δ = s * ∫ l in lam0..B_lam, F_δ (s * l) := by
    have h := intervalIntegral.integral_comp_mul_left F_δ hs_pos.ne' (a := lam0) (b := B_lam)
    rw [show s * lam0 = δ_c by dsimp [δ_c, s]; ring,
      show s * B_lam = δ₀ by dsimp [B_lam]; exact mul_div_cancel₀ _ hs_pos.ne'] at h
    rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs_pos.ne', one_mul]
  have hlog_cancel : C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤ 1 := by
    have hc'_16 : max 1 (6 * C_M1) ≤ c' ^ ((1 : ℝ) / 6) := by
      have := Real.rpow_le_rpow (by positivity) hc'_log (by norm_num : (0 : ℝ) ≤ 1 / 6)
      rwa [← Real.rpow_natCast (max 1 (6 * C_M1)) 6, ← Real.rpow_mul (by positivity),
        show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num, Real.rpow_one] at this
    have hlog_le : Real.log c' ≤ 6 * c' ^ ((1 : ℝ) / 6) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (1 / 6))
      rw [Real.log_rpow hc'_pos] at h1; linarith
    have hpow_comb : c' ^ (-(1 / 3 : ℝ)) * c' ^ ((1 : ℝ) / 6) = (c' ^ ((1 : ℝ) / 6))⁻¹ := by
      rw [← Real.rpow_add hc'_pos, ← Real.rpow_neg hc'_pos.le]; norm_num
    calc C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c'
        ≤ C_M1 * c' ^ (-(1 / 3 : ℝ)) * (6 * c' ^ ((1 : ℝ) / 6)) := by gcongr
      _ = (6 * C_M1) * (c' ^ ((1 : ℝ) / 6))⁻¹ := by rw [← hpow_comb]; ring
      _ ≤ (c' ^ ((1 : ℝ) / 6)) * (c' ^ ((1 : ℝ) / 6))⁻¹ := by
          gcongr; exact (le_max_right 1 (6 * C_M1)).trans hc'_16
      _ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hc'_pos _).ne'
  have hint_sFδ : IntervalIntegrable (fun l => s * F_δ (s * l)) volume lam0 B_lam := by
    have hcomp := hint_Fδ.comp_mul_left (c := s) eNorm_ne_top eNorm_ne_top
    rw [show δ_c / s = lam0 by dsimp [δ_c, s]; exact mul_div_cancel_right₀ _ hs_pos.ne'] at hcomp
    exact hcomp.const_mul s
  have hmono_lam : ∫ l in lam0..B_lam, s * F_δ (s * l) ≤
      ∫ l in lam0..B_lam, C_pref * test.M * Real.exp (-l) := by
    refine intervalIntegral.integral_mono_on hlam0_le_B hint_sFδ
      ((Continuous.intervalIntegrable (by fun_prop) _ _).const_mul _) fun l hl => ?_
    have hl_ge1 : 1 ≤ l := hlam0_ge1.trans hl.1
    have hl_pos : 0 < l := zero_lt_one.trans_le hl_ge1
    have hcancel_1 : s * (s * l)⁻¹ = l⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs_pos.ne', one_mul]
    have hcancel_2 : c' * (s * l) ^ ((3 : ℝ) / 2) = l ^ ((3 : ℝ) / 2) := by
      rw [Real.mul_rpow hs_pos.le hl_pos.le]; dsimp [s]
      rw [← Real.rpow_mul hc'_pos.le, show (-(2 / 3 : ℝ)) * (3 / 2) = -1 by norm_num,
        ← mul_assoc, Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne', one_mul]
    have hcancel_3 : Real.sqrt (s * l) = c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l := by
      rw [Real.sqrt_mul hs_pos.le, Real.sqrt_eq_rpow]; dsimp [s]
      rw [← Real.rpow_mul hc'_pos.le]; norm_num
    have hCM1_ub : C_M1 * Real.sqrt (s * l) * Real.log c' ≤ Real.sqrt l := by
      rw [hcancel_3]
      calc C_M1 * (c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l) * Real.log c'
          = (C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c') * Real.sqrt l := by ring
        _ ≤ 1 * Real.sqrt l := by gcongr
        _ = Real.sqrt l := one_mul _
    have hsqrt_le_l : Real.sqrt l ≤ l := by
      calc Real.sqrt l ≤ Real.sqrt (l ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = l := Real.sqrt_sq hl_pos.le
    have hl_le_32 : l ≤ l ^ ((3 : ℝ) / 2) := by
      calc l = l ^ (1 : ℝ) := (Real.rpow_one l).symm
        _ ≤ l ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hl_ge1 (by norm_num)
    have hexp_arg : -2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
        C_M1 * Real.sqrt (s * l) * Real.log c' ≤ -l := by
      rw [show -2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) = -2.228 * (c' * (s * l) ^ ((3 : ℝ) / 2)) by ring,
        hcancel_2]
      linarith
    dsimp [F_δ]
    calc s * (C_pref * test.M * (s * l)⁻¹ *
            Real.exp (-2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
              C_M1 * Real.sqrt (s * l) * Real.log c'))
        = C_pref * test.M * (s * (s * l)⁻¹) *
            Real.exp (-2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
              C_M1 * Real.sqrt (s * l) * Real.log c') := by ring
      _ ≤ C_pref * test.M * 1 * Real.exp (-l) := by
          rw [hcancel_1]
          have hCM_nn : 0 ≤ C_pref * test.M := mul_nonneg hC_pref_pos.le test.hM_pos.le
          exact mul_le_mul (mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hl_ge1) hCM_nn)
            (Real.exp_le_exp.mpr hexp_arg) (Real.exp_pos _).le (mul_nonneg hCM_nn zero_le_one)
      _ = C_pref * test.M * Real.exp (-l) := by ring
  have hexp_int_ub : ∫ l in lam0..B_lam, Real.exp (-l) ≤ Real.exp (-lam0) := by
    have hd : ∀ l ∈ uIcc lam0 B_lam, HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-l)) l :=
      fun l _ => ((Real.hasDerivAt_exp _).comp l (hasDerivAt_neg l)).neg.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    linarith [Real.exp_pos (-B_lam)]
  calc ∫ t in (c' * (0.05 : ℝ) ^ 2 / 3)..(c' * (xiStar - δ_c) ^ 2 / 3), |test.g t| * test.V t
      = ∫ x in (0.05 : ℝ)..(xiStar - δ_c),
          |test.g (c' * x ^ 2 / 3)| * test.V (c' * x ^ 2 / 3) * ((2 / 3 : ℝ) * c' * x) := hφ_eq
    _ ≤ ∫ x in (0.05 : ℝ)..(xiStar - δ_c), F_x x := hmono_x
    _ = ∫ δ in δ_c..δ₀, F_δ δ := hsub_δ
    _ = ∫ l in lam0..B_lam, s * F_δ (s * l) := by
        rw [hscale_lam, intervalIntegral.integral_const_mul]
    _ ≤ ∫ l in lam0..B_lam, C_pref * test.M * Real.exp (-l) := hmono_lam
    _ = C_pref * test.M * ∫ l in lam0..B_lam, Real.exp (-l) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ C_pref * test.M * Real.exp (-lam0) :=
        mul_le_mul_of_nonneg_left hexp_int_ub (mul_nonneg hC_pref_pos.le test.hM_pos.le)
    _ = (C_pref * Real.exp (-lam0)) * test.M := by ring
    _ < (1 / 4 : ℝ) * test.M := mul_lt_mul_of_pos_right hCpref_lt test.hM_pos
    _ = test.M / 4 := by ring

/-- **Theorem A (sharp Airy-scale gap bound).** There exist absolute constants `C_A > 0` and
`c_A ≥ 1` (depending only on the uniform analytic bounds) such that for all `c' ≥ c_A` and every
weakly feasible test `g`, `t₁(g) ≥ ξ̄ c' - C_A c'^{1/3}`. -/
theorem theorem_A (pj : PoissonJensenInput) (fg : FixedGapInput) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 1 ≤ c_A ∧
      ∀ {c' : ℝ}, c_A ≤ c' →
        ∀ test : WeaklyFeasibleTest pj fg c',
          xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ test.t₁ := by
  obtain ⟨C_M1, C_M2, hCM1_nn, hpropM⟩ := proposition_M pj.rs (C_PJ := pj.C_PJ) pj.hc_PJ
  let C_pref : ℝ := 2 * pj.C_K * Real.exp C_M2
  have hC_pref_pos : 0 < C_pref := mul_pos (mul_pos two_pos pj.hC_K) (Real.exp_pos C_M2)
  let lam0 : ℝ := max 1 (Real.log (4 * C_pref) + 1)
  have hlam0_ge1 : 1 ≤ lam0 := le_max_left _ _
  have hlam0_pos : 0 < lam0 := zero_lt_one.trans_le hlam0_ge1
  let δ₀ : ℝ := xiStar - 0.05
  have hδ₀_pos : 0 < δ₀ := sub_pos.mpr xiStar_gt_005
  let c_A : ℝ := max (max 1 pj.c_PJ) (max ((max 1 (6 * C_M1)) ^ 6)
    (max ((lam0 / δ₀) ^ ((3 : ℝ) / 2) + 1)
      (max fg.c_deep (Real.log (4 * fg.C_deep + 1) / fg.κ_deep + 1))))
  let C_A : ℝ := (2 * xiStar / 3) * lam0
  have hCA_pos : 0 < C_A := mul_pos (div_pos (mul_pos two_pos xiStar_pos) (by norm_num)) hlam0_pos
  have hcA_ge1 : 1 ≤ c_A := le_trans (le_max_left 1 pj.c_PJ) (le_max_left _ _)
  refine ⟨C_A, c_A, hCA_pos, hcA_ge1, fun {c'} hc' test => ?_⟩
  have hc'_ge1 : 1 ≤ c' := hcA_ge1.trans hc'
  have hc'_pos : 0 < c' := zero_lt_one.trans_le hc'_ge1
  have hc'_PJ : pj.c_PJ ≤ c' := (le_max_right 1 pj.c_PJ).trans ((le_max_left _ _).trans hc')
  have hc'_log : (max 1 (6 * C_M1)) ^ 6 ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hc'_delta : (lam0 / δ₀) ^ ((3 : ℝ) / 2) + 1 ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc'_deep : max fg.c_deep (Real.log (4 * fg.C_deep + 1) / fg.κ_deep + 1) ≤ c' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  let δ_c : ℝ := lam0 * c' ^ (-(2 / 3 : ℝ))
  have hδ_c_lt_δ₀ : δ_c < δ₀ := by
    have h2 : ((lam0 / δ₀) ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) < c' ^ ((2 : ℝ) / 3) :=
      Real.rpow_lt_rpow (by positivity) (by linarith) (by norm_num)
    rw [← Real.rpow_mul (div_pos hlam0_pos hδ₀_pos).le, show (3 : ℝ) / 2 * (2 / 3) = 1 by norm_num,
      Real.rpow_one, div_lt_iff₀ hδ₀_pos] at h2
    dsimp [δ_c]
    rw [Real.rpow_neg hc'_pos.le, ← div_eq_mul_inv, div_lt_iff₀ (Real.rpow_pos_of_pos hc'_pos _)]
    linarith
  let t₀ : ℝ := c' * (0.05 : ℝ) ^ 2 / 3
  let t_c : ℝ := c' * (xiStar - δ_c) ^ 2 / 3
  have ht₀_nn : 0 ≤ t₀ := by positivity
  have ht₀_le_tc : t₀ ≤ t_c := by
    have h05 : (0.05 : ℝ) ≤ xiStar - δ_c := by dsimp [δ₀] at hδ_c_lt_δ₀; linarith
    dsimp [t₀, t_c]; have : (0.05 : ℝ) ^ 2 ≤ (xiStar - δ_c) ^ 2 := by nlinarith
    gcongr
  have htc_nonneg : 0 ≤ t_c := ht₀_nn.trans ht₀_le_tc
  have htc_ge_xiBar : xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ t_c := by
    have hpow : δ_c * c' = lam0 * c' ^ ((1 : ℝ) / 3) := by
      dsimp [δ_c]; rw [mul_assoc, ← Real.rpow_add_one hc'_pos.ne']; norm_num
    have hsq_nn : 0 ≤ c' * δ_c ^ 2 / 3 := by positivity
    unfold xiBar; dsimp [t_c, C_A]
    calc xiStar ^ 2 / 3 * c' - 2 * xiStar / 3 * lam0 * c' ^ ((1 : ℝ) / 3)
        = xiStar ^ 2 / 3 * c' - (2 * xiStar / 3) * (δ_c * c') := by rw [hpow]; ring
      _ ≤ xiStar ^ 2 / 3 * c' - (2 * xiStar / 3) * (δ_c * c') + c' * δ_c ^ 2 / 3 := by linarith
      _ = c' * (xiStar - δ_c) ^ 2 / 3 := by ring
  have hdeep_lt : ∫ t in (0 : ℝ)..t₀, |test.g t| * test.V t < test.M / 4 := by
    have h1 := test.hDeepLobe ((le_max_left _ _).trans hc'_deep)
    change ∫ t in (0 : ℝ)..t₀, |test.g t| * test.V t ≤
      fg.C_deep * Real.exp (-fg.κ_deep * c') * test.M at h1
    have h2 : fg.C_deep * Real.exp (-fg.κ_deep * c') < 1 / 4 := by
      have hk := (le_max_right _ _).trans hc'_deep
      have hmul : Real.log (4 * fg.C_deep + 1) + fg.κ_deep ≤ fg.κ_deep * c' := by
        have := mul_le_mul_of_nonneg_left hk fg.hκ_deep.le
        rwa [mul_add, mul_div_cancel₀ _ fg.hκ_deep.ne', mul_one] at this
      have hexp : 4 * fg.C_deep + 1 < Real.exp (fg.κ_deep * c') := by
        have := Real.exp_lt_exp.mpr
          (by linarith [fg.hκ_deep] : Real.log (4 * fg.C_deep + 1) < fg.κ_deep * c')
        rwa [Real.exp_log (by linarith [fg.hC_deep])] at this
      rw [show -fg.κ_deep * c' = -(fg.κ_deep * c') by ring, Real.exp_neg,
        mul_inv_lt_iff₀ (Real.exp_pos _)]
      linarith [fg.hC_deep]
    linarith [mul_lt_mul_of_pos_right h2 test.hM_pos]
  have hCpref_exp_lt : C_pref * Real.exp (-lam0) < 1 / 4 := by
    have hgt : Real.log (4 * C_pref) < lam0 := by linarith [le_max_right (1 : ℝ) (Real.log (4 * C_pref) + 1)]
    have hexp : 4 * C_pref < Real.exp lam0 := by
      have := Real.exp_lt_exp.mpr hgt; rwa [Real.exp_log (by positivity)] at this
    rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _)]; linarith
  have hairy_lt : ∫ t in t₀..t_c, |test.g t| * test.V t < test.M / 4 :=
    airy_tail_integral_bound pj fg test hCM1_nn hc'_ge1 hc'_log hlam0_ge1
      (fun x hx => proposition_M_exp hc'_pos test.hM_pos (hpropM hc'_PJ test.hM_pos test.hPJ) hx)
      hCpref_exp_lt hδ_c_lt_δ₀
  have htot_lt : ∫ t in (0 : ℝ)..t_c, |test.g t| * test.V t < test.M / 2 := by
    have hcont : ContinuousOn (fun t => |test.g t| * test.V t) (Icc 0 t_c) :=
      ((test.hg_cont.abs).mul test.hV_cont).mono fun t ht => mem_Ici.mpr ht.1
    have hi : IntervalIntegrable (fun t => |test.g t| * test.V t) volume 0 t_c :=
      hcont.intervalIntegrable_of_Icc htc_nonneg
    have h1 := hi.mono_set (by
      rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ t₀), uIcc_of_le (by linarith : (0 : ℝ) ≤ t_c)]
      exact Icc_subset_Icc le_rfl ht₀_le_tc)
    have h2 := hi.mono_set (by
      rw [uIcc_of_le (by linarith : t₀ ≤ t_c), uIcc_of_le (by linarith : (0 : ℝ) ≤ t_c)]
      exact Icc_subset_Icc ht₀_nn le_rfl)
    have hadj := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith
  have htc_lt_t1 : t_c < test.t₁ := by
    by_contra hle; push Not at hle
    have hcont : ContinuousOn (fun t => |test.g t| * test.V t) (Icc 0 t_c) :=
      ((test.hg_cont.abs).mul test.hV_cont).mono fun t ht => mem_Ici.mpr ht.1
    have hle_int : ∫ t in (0 : ℝ)..test.t₁, |test.g t| * test.V t ≤
        ∫ t in (0 : ℝ)..t_c, |test.g t| * test.V t := by
      rw [intervalIntegral.integral_of_le test.ht₁_nonneg, intervalIntegral.integral_of_le htc_nonneg]
      exact setIntegral_mono_set
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le htc_nonneg).1
          (hcont.intervalIntegrable_of_Icc htc_nonneg))
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht =>
          mul_nonneg (abs_nonneg _) (test.hV_nonneg t ht.1.le)))
        (Ioc_subset_Ioc_right hle).eventuallySubset
    linarith [test.hHalfMass]
  exact htc_ge_xiBar.trans htc_lt_t1.le

/-- **Non-vacuity sanity theorem:** exhibits explicit, non-trivial data satisfying
`PoissonJensenInput`, `FixedGapInput`, and `WeaklyFeasibleTest pj fg c'` for every `c' ≥ pj.c_PJ`. -/
theorem slitStrip_hypotheses_nonvacuous :
    ∃ (pj : PoissonJensenInput) (fg : FixedGapInput),
      ∀ c' : ℝ, pj.c_PJ ≤ c' → Nonempty (WeaklyFeasibleTest pj fg c') := by
  let rs : RealSliceData :=
    { xUHP := fun _ => sigmaStar, yUHP := Real.sqrt, C_e := 0, c_y := 1, C_y := 1
      hC_e := le_rfl, hc_y := zero_lt_one, hC_y := le_rfl
      re_bound := fun _ _ => by simp, im_lower := fun _ _ => by rw [one_mul]
      im_upper := fun _ _ => by rw [one_mul] }
  let U : ℝ → ℝ := fun x => -(2 * π / 3) * x - slitDeficit (xiStar - x)
  let pj : PoissonJensenInput :=
    { rs := rs, c_PJ := 1, C_PJ := Real.log 3, C_K := 1, U := U
      hc_PJ := le_rfl, hC_K := zero_lt_one, g_deficit := fun x _ => by dsimp [U]; linarith }
  let δ₀ : ℝ := xiStar - 0.05
  have hδ₀_pos : 0 < δ₀ := sub_pos.mpr xiStar_gt_005
  have hκ_pos : 0 < slitDeficit δ₀ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hδ₀_pos _))
      (slitDeficit_ge hδ₀_pos.le (by dsimp [δ₀]; linarith))
  let fg : FixedGapInput :=
    { c_deep := 1, C_deep := 1, κ_deep := slitDeficit δ₀,
      hc_deep := le_rfl, hC_deep := zero_le_one, hκ_deep := hκ_pos }
  refine ⟨pj, fg, fun c' hc' => ?_⟩
  have hc'_pos : 0 < c' := zero_lt_one.trans_le hc'
  let T₀ : ℝ := c' * xiStar ^ 2 / 3
  let T₁ : ℝ := c' * (xiStar + 1) ^ 2 / 3
  have hT₀_pos : 0 < T₀ := by have := xiStar_pos; dsimp [T₀]; positivity
  have hT₀_lt_T₁ : T₀ < T₁ := by
    dsimp [T₀, T₁]; have : xiStar ^ 2 < (xiStar + 1) ^ 2 := by nlinarith [xiStar_pos]
    gcongr
  let V : ℝ → ℝ := fun t => Real.exp (c' * ((2 * π / 3) * Real.sqrt (3 * t / c'))) / Real.sqrt c'
  let W : ℝ → ℝ := fun t => slitDeficit (max 0 (xiStar - Real.sqrt (3 * t / c')))
  let g : ℝ → ℝ := fun t =>
    Real.exp (-c' * ((2 * π / 3) * Real.sqrt (3 * t / c')) - c' * W t - max 0 (t - T₁)) /
      Real.sqrt c'
  have hW_cont : Continuous W := by
    dsimp [W, slitDeficit]
    refine Continuous.const_mul ?_ _
    let F_int : ℝ → ℝ := fun a => ∫ s in (0 : ℝ)..a, Real.arccos (Real.sinh (π * s))
    have hint_arc : ∀ a b : ℝ, IntervalIntegrable (fun s => Real.arccos (Real.sinh (π * s)))
        volume a b := fun a b =>
      (Real.continuous_arccos.comp (Real.continuous_sinh.comp (by fun_prop))).intervalIntegrable a b
    have hsplit : ∀ δ : ℝ, ∫ s in (xiStar - δ)..xiStar, Real.arccos (Real.sinh (π * s)) =
        F_int xiStar - F_int (xiStar - δ) := fun δ => by
      dsimp [F_int]
      linarith [intervalIntegral.integral_add_adjacent_intervals (hint_arc 0 (xiStar - δ))
        (hint_arc (xiStar - δ) xiStar)]
    simp_rw [hsplit]
    exact continuous_const.sub ((intervalIntegral.continuous_primitive hint_arc 0).comp
      (continuous_const.sub (continuous_const.max
        (continuous_const.sub ((continuous_const.mul continuous_id).div_const c').sqrt))))
  have hg_cont : ContinuousOn g (Ici 0) :=
    (Continuous.rexp (((continuous_const.mul (continuous_const.mul
      (((continuous_const.mul continuous_id).div_const c').sqrt))).sub
      (continuous_const.mul hW_cont)).sub
      (continuous_const.max (continuous_id.sub continuous_const)))).div_const _ |>.continuousOn
  have hV_cont : ContinuousOn V (Ici 0) := by dsimp [V]; fun_prop
  have hV_nonneg : ∀ t ≥ 0, 0 ≤ V t := fun t _ => by dsimp [V]; positivity
  have hprod_eq : ∀ t : ℝ, |g t| * V t = c'⁻¹ * Real.exp (-c' * W t - max 0 (t - T₁)) := by
    intro t
    rw [abs_of_pos (by dsimp [g]; positivity : 0 < g t)]
    dsimp [g, V]
    have hsq : Real.sqrt c' * Real.sqrt c' = c' := Real.mul_self_sqrt hc'_pos.le
    rw [div_mul_div_comm, hsq, ← Real.exp_add]
    rw [show (-c' * (2 * π / 3 * Real.sqrt (3 * t / c')) - c' * W t - max 0 (t - T₁) +
      c' * (2 * π / 3 * Real.sqrt (3 * t / c'))) = -c' * W t - max 0 (t - T₁) by ring]
    ring
  have hprod_tail : ∀ t : ℝ, T₁ ≤ t → |g t| * V t = c'⁻¹ * Real.exp (T₁ - t) := by
    intro t ht; rw [hprod_eq t]
    have hge : xiStar ≤ Real.sqrt (3 * t / c') := by
      have harg : xiStar ^ 2 ≤ 3 * t / c' := by
        rw [le_div_iff₀ hc'_pos]; dsimp [T₀] at hT₀_lt_T₁; linarith [hT₀_lt_T₁.le.trans ht]
      simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_le_sqrt harg
    have hW0 : W t = 0 := by dsimp [W]; rw [max_eq_left (sub_nonpos.mpr hge)]; unfold slitDeficit; simp
    rw [hW0, mul_zero, zero_sub, max_eq_right (sub_nonneg.mpr ht)]; congr 2; ring
  have hint_tail : IntegrableOn (fun t => |g t| * V t) (Ioi T₁) :=
    IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T₁).const_mul (c'⁻¹ * Real.exp T₁))
      (fun t ht => by
        rw [hprod_tail t (mem_Ioi.mp ht).le, mul_assoc, ← Real.exp_add]; congr 2; ring)
      measurableSet_Ioi
  have hint_all : IntegrableOn (fun t => |g t| * V t) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (le_trans hT₀_pos.le hT₀_lt_T₁.le)]
    exact (((hg_cont.abs.mul hV_cont).mono fun t (ht : t ∈ Icc (0 : ℝ) _) => mem_Ici.mpr ht.1).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self).union hint_tail
  let M : ℝ := ∫ t in Ioi 0, |g t| * V t
  have hmid_val : ∫ t in T₀..T₁, |g t| * V t = (2 * xiStar + 1) / 3 := by
    have heq : EqOn (fun t => |g t| * V t) (fun _ => c'⁻¹) (uIcc T₀ T₁) := by
      intro t ht
      rw [uIcc_of_le hT₀_lt_T₁.le, mem_Icc] at ht
      dsimp only; rw [hprod_eq t]
      have hge : xiStar ≤ Real.sqrt (3 * t / c') := by
        have harg : xiStar ^ 2 ≤ 3 * t / c' := by rw [le_div_iff₀ hc'_pos]; dsimp [T₀] at ht; linarith
        simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_le_sqrt harg
      have hW0 : W t = 0 := by dsimp [W]; rw [max_eq_left (sub_nonpos.mpr hge)]; unfold slitDeficit; simp
      rw [hW0, mul_zero, zero_sub, max_eq_left (sub_nonpos.mpr ht.2), neg_zero, Real.exp_zero, mul_one]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const, smul_eq_mul]
    dsimp [T₀, T₁]; field_simp [hc'_pos.ne']; ring
  have hM_lb : 1 / 3 < M := by
    have hsub : Ioc T₀ T₁ ⊆ Ioi 0 := Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hT₀_pos.le)
    have hle : ∫ t in Ioc T₀ T₁, |g t| * V t ≤ M :=
      setIntegral_mono_set hint_all (Eventually.of_forall fun t =>
        mul_nonneg (abs_nonneg _) (by dsimp [V]; positivity)) hsub.eventuallySubset
    rw [← intervalIntegral.integral_of_le hT₀_lt_T₁.le, hmid_val] at hle
    linarith [xiStar_pos]
  let t₁ : ℝ := T₁ + 2
  have ht₁_pos : 0 < t₁ := by dsimp [t₁]; linarith
  have ht₁_tail_val : ∫ t in Ioi t₁, |g t| * V t = c'⁻¹ * Real.exp (-2) := by
    have heq : EqOn (fun t => |g t| * V t) (fun t => (c'⁻¹ * Real.exp T₁) * Real.exp (-1 * t))
        (Ioi t₁) := fun t ht => by
      dsimp only; rw [hprod_tail t (by dsimp [t₁] at ht; linarith [mem_Ioi.mp ht]), mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
      integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) t₁, neg_one_mul]
    calc c'⁻¹ * Real.exp T₁ * (-Real.exp (-t₁) / -1)
        = c'⁻¹ * (Real.exp T₁ * Real.exp (-t₁)) := by ring
      _ = c'⁻¹ * Real.exp (T₁ - t₁) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ = c'⁻¹ * Real.exp (-2) := by rw [show T₁ - t₁ = -2 by dsimp [t₁]; ring]
  have hhalf : M / 2 ≤ ∫ t in (0 : ℝ)..t₁, |g t| * V t := by
    have hsplit : (∫ t in Ioc 0 t₁, |g t| * V t) + (∫ t in Ioi t₁, |g t| * V t) = M := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hint_all.mono_set Ioc_subset_Ioi_self) (hint_all.mono_set (Ioi_subset_Ioi ht₁_pos.le)),
        Ioc_union_Ioi_eq_Ioi ht₁_pos.le]
    rw [intervalIntegral.integral_of_le ht₁_pos.le]
    have hexp2 : Real.exp (-2 : ℝ) < 1 / 6 := by
      have h27 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h729 : (7.29 : ℝ) < Real.exp 2 := by
        have h3 : (2.7 : ℝ) ^ 2 < Real.exp 1 ^ 2 := by gcongr
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)]; linarith
    have htail_lt : c'⁻¹ * Real.exp (-2) < M / 2 := by
      calc c'⁻¹ * Real.exp (-2) ≤ 1 * Real.exp (-2) :=
            mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hc') (Real.exp_pos _).le
        _ < 1 / 6 := by linarith
        _ < M / 2 := by linarith
    linarith
  have hsqrt_x : ∀ x : ℝ, 0 ≤ x → Real.sqrt (3 * (c' * x ^ 2 / 3) / c') = x := fun x hx => by
    rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp [hc'_pos.ne'] ]
    exact Real.sqrt_sq hx
  refine ⟨⟨g, V, V, M, t₁, lt_trans (by positivity) hM_lb, ht₁_pos.le, hg_cont, hV_cont, hV_nonneg,
    hint_all, rfl, fun x _ => by linarith [hV_nonneg (c' * x ^ 2 / 3) (by positivity)], ?_, ?_, ?_, hhalf⟩⟩
  · intro x hx; dsimp [V]; rw [hsqrt_x x (by linarith [hx.1]), one_mul]
  · intro x hx _
    have hT_le : c' * x ^ 2 / 3 ≤ T₁ := by
      dsimp [T₁]; have : x ^ 2 ≤ (xiStar + 1) ^ 2 := by nlinarith [hx.1, hx.2]
      gcongr
    have hW_eq : W (c' * x ^ 2 / 3) = slitDeficit (xiStar - x) := by
      dsimp [W]; rw [hsqrt_x x hx.1, max_eq_right (sub_nonneg.mpr hx.2.le)]
    rw [abs_of_pos (by dsimp [g]; positivity : 0 < g (c' * x ^ 2 / 3))]
    dsimp [g]
    rw [hsqrt_x x hx.1, hW_eq, max_eq_left (sub_nonpos.mpr hT_le), sub_zero,
      Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr hc'_pos).ne', Real.log_exp,
      Real.sqrt_eq_rpow, Real.log_rpow hc'_pos]
    have hlogM : 0 ≤ Real.log M + Real.log 3 := by
      rw [← Real.log_mul (lt_trans (by positivity) hM_lb).ne' (by norm_num)]
      exact Real.log_nonneg (by linarith)
    have hm_nn : 0 ≤ (5 / 2 : ℝ) * (1 - pj.rs.slitMassAt x) * Real.log c' :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr
        (slitMass_le_one _ (Real.sqrt_pos.mpr (sub_pos.mpr hx.2))))) (Real.log_nonneg hc')
    have hs_nn : 0 ≤ pj.rs.slitEntropyAt x := slitEntropy_nonneg _ (Real.sqrt_nonneg _)
    have hcU : c' * pj.U x = -c' * (2 * π / 3 * x) - c' * slitDeficit (xiStar - x) := by
      change c' * (-(2 * π / 3) * x - slitDeficit (xiStar - x)) = _
      ring
    have hCPJ : pj.C_PJ = Real.log 3 := rfl
    rw [hcU, hCPJ]
    linarith
  · intro _
    let t₀ : ℝ := c' * (0.05 : ℝ) ^ 2 / 3
    have hle : ∀ t ∈ Icc 0 t₀, |g t| * V t ≤ c'⁻¹ * Real.exp (-fg.κ_deep * c') := by
      intro t ht; rw [hprod_eq t]
      have hx_le : Real.sqrt (3 * t / c') ≤ 0.05 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0.05)]
        exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ hc'_pos]; dsimp [t₀] at ht; linarith [ht.2])
      have hW_ge : fg.κ_deep ≤ W t := by
        dsimp [W, fg]
        rw [max_eq_right (by dsimp [δ₀] at *; linarith)]
        exact slitDeficit_mono hδ₀_pos.le (by dsimp [δ₀]; linarith)
          (by linarith [Real.sqrt_nonneg (3 * t / c')])
      have : -c' * W t - max 0 (t - T₁) ≤ -fg.κ_deep * c' := by
        nlinarith [le_max_left 0 (t - T₁), hc'_pos]
      gcongr
    have hint_t₀ : IntervalIntegrable (fun t => |g t| * V t) volume 0 t₀ :=
      ((hg_cont.abs.mul hV_cont).mono fun t (ht : t ∈ Icc (0 : ℝ) _) => mem_Ici.mpr ht.1).intervalIntegrable_of_Icc
        (by dsimp [t₀]; positivity)
    calc ∫ t in (0 : ℝ)..t₀, |g t| * V t
        ≤ ∫ _t in (0 : ℝ)..t₀, c'⁻¹ * Real.exp (-fg.κ_deep * c') :=
          intervalIntegral.integral_mono_on (by dsimp [t₀]; positivity) hint_t₀
            intervalIntegrable_const hle
      _ = ((0.05 : ℝ) ^ 2 / 3) * Real.exp (-fg.κ_deep * c') := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
          dsimp [t₀]; field_simp [hc'_pos.ne']
      _ ≤ (1 / 3 : ℝ) * Real.exp (-fg.κ_deep * c') := by gcongr; norm_num
      _ ≤ fg.C_deep * Real.exp (-fg.κ_deep * c') * M :=
          (mul_le_mul_of_nonneg_right hM_lb.le (Real.exp_pos _).le).trans_eq (by
            change _ = (1 : ℝ) * _ * _; ring)

/-! ### Axiom checks for all headline theorems -/

/-- info: 'FormalResearch.ModularBootstrap.slitBoundaryMap_slitInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitBoundaryMap_slitInv

/-- info: 'FormalResearch.ModularBootstrap.invJacobian_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.invJacobian_le

/-- info: 'FormalResearch.ModularBootstrap.lemmaE_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.lemmaE_complex

/-- info: 'FormalResearch.ModularBootstrap.lemmaE_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.lemmaE_real

/-- info: 'FormalResearch.ModularBootstrap.lemmaS_poisson_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.lemmaS_poisson_log_bound

/-- info: 'FormalResearch.ModularBootstrap.lemmaS_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.lemmaS_complex

/-- info: 'FormalResearch.ModularBootstrap.lemmaS_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.lemmaS_real

/-- info: 'FormalResearch.ModularBootstrap.slitDeficit_ge_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitDeficit_ge_exact

/-- info: 'FormalResearch.ModularBootstrap.slitDeficit_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitDeficit_ge

/-- info: 'FormalResearch.ModularBootstrap.proposition_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.proposition_M

/-- info: 'FormalResearch.ModularBootstrap.theorem_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.theorem_A

/-- info: 'FormalResearch.ModularBootstrap.slitStrip_hypotheses_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitStrip_hypotheses_nonvacuous

end FormalResearch.ModularBootstrap
