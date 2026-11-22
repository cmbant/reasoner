module

public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Poisson--Jensen inequality on the upper half-plane

Generic complex-analysis module for the upper half-plane `{z : ℂ | 0 < z.im}`:

* `cayleyAt`: the Cayley map `w ↦ x₀ + i y₀ (1 + w)/(1 - w)` sending the unit disc `ball 0 1`
  conformally onto the upper half-plane with `0 ↦ z₀ = x₀ + i y₀`.
* `halfPlane_poissonJensen`: if `F` is holomorphic and bounded (`‖F z‖ ≤ M`) on `{0 < z.im}` and
  tends to `F_bdy σ` along `{0 < z.im}` for Lebesgue-a.e. `σ ∈ ℝ`, then for any `z₀` with
  `0 < z₀.im` and `F z₀ ≠ 0`:
  1. `σ ↦ Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ` is integrable on `ℝ`;
  2. `Real.log ‖F z₀‖ ≤ ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ`.

The proof transports `F` via `cayleyAt z₀` to the unit disc, applies Mathlib's
`AnalyticOnNhd.circleAverage_log_norm` on concentric circles `|w| = r_n ↑ 1`, and passes to the
limit using Fatou's lemma (`lintegral_liminf_le`) on the nonnegative discrepancy
`log M - log ‖F(cayleyAt z₀ (r_n e^{iθ}))‖`, which simultaneously handles boundary zeros,
boundary discontinuities on a null set, and `L¹` integrability of `log ‖F_bdy‖ * P_{z₀}`.
-/

@[expose] public section

open Real Complex Metric MeasureTheory Set Filter Topology MeromorphicOn
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.PoissonJensen

/-! ### 1. Cayley map centered at `z₀ ∈ ℍ` -/

/-- The Cayley map `w ↦ x₀ + i y₀ (1 + w)/(1 - w)` sending `ball 0 1` to `{0 < z.im}` with
`0 ↦ z₀`. -/
noncomputable def cayleyAt (z₀ w : ℂ) : ℂ :=
  (z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I * ((1 + w) / (1 - w))

lemma cayleyAt_zero (z₀ : ℂ) : cayleyAt z₀ 0 = z₀ := by
  unfold cayleyAt
  simp [Complex.re_add_im]

lemma one_sub_ne_zero_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this, mem_ball, dist_zero_right, norm_one] at hw
  exact lt_irrefl 1 hw

lemma div_one_add_one_sub_re {w : ℂ} (_hw : 1 - w ≠ 0) :
    ((1 + w) / (1 - w)).re = (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  rw [Complex.div_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_add]
  ring

lemma cayleyAt_im {z₀ w : ℂ} (hw : 1 - w ≠ 0) :
    (cayleyAt z₀ w).im = z₀.im * (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  unfold cayleyAt
  have h1 : (((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I * ((1 + w) / (1 - w)))).im =
      z₀.im * ((1 + w) / (1 - w)).re := by
    simp [Complex.mul_im]
  rw [h1, div_one_add_one_sub_re hw]
  ring

lemma cayleyAt_im_pos {z₀ w : ℂ} (hz₀ : 0 < z₀.im) (hw : w ∈ ball (0 : ℂ) 1) :
    0 < (cayleyAt z₀ w).im := by
  have hd := one_sub_ne_zero_of_mem_ball hw
  rw [cayleyAt_im hd]
  have hw1 : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
  have hnum : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hden : 0 < ‖1 - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  positivity

lemma differentiableOn_cayleyAt (z₀ : ℂ) :
    DifferentiableOn ℂ (cayleyAt z₀) (ball 0 1) := by
  intro w hw
  unfold cayleyAt
  have hd := one_sub_ne_zero_of_mem_ball hw
  exact ((differentiableAt_const _).add ((differentiableAt_const _).mul
    (((differentiableAt_const _).add differentiableAt_id).div
      ((differentiableAt_const _).sub differentiableAt_id) hd))).differentiableWithinAt

lemma cayleyAt_circle_beta (z₀ : ℂ) {β : ℝ} (hβ : β ∈ Ioo (-(π / 2)) (π / 2)) :
    1 - circleMap 0 1 (2 * β + π) ≠ 0 ∧
      cayleyAt z₀ (circleMap 0 1 (2 * β + π)) = ((z₀.re + z₀.im * Real.tan β : ℝ) : ℂ) := by
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo hβ
  have hcm : circleMap 0 1 (2 * β + π) =
      ((-Real.cos (2 * β) : ℝ) : ℂ) + ((-Real.sin (2 * β) : ℝ) : ℂ) * Complex.I := by
    rw [circleMap, zero_add, Complex.ofReal_one, one_mul,
      show ((2 * β + π : ℝ) : ℂ) * Complex.I = (((2 * β + π : ℝ) : ℂ) * Complex.I) from rfl,
      Complex.exp_mul_I]
    have hcos : Complex.cos ((2 * β + π : ℝ) : ℂ) = ((-Real.cos (2 * β) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cos, Real.cos_add_pi]
    have hsin : Complex.sin ((2 * β + π : ℝ) : ℂ) = ((-Real.sin (2 * β) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sin, Real.sin_add_pi]
    rw [hcos, hsin]
  have hpyC : (Real.sin β : ℂ) ^ 2 + (Real.cos β : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq β
  have hcR : (Real.cos (2 * β) : ℂ) = 2 * (Real.cos β : ℂ) ^ 2 - 1 := by
    exact_mod_cast Real.cos_two_mul β
  have hsR : (Real.sin (2 * β) : ℂ) = 2 * (Real.sin β : ℂ) * (Real.cos β : ℂ) := by
    exact_mod_cast Real.sin_two_mul β
  have hd_val : 1 - circleMap 0 1 (2 * β + π) =
      2 * (Real.cos β : ℂ) * ((Real.cos β : ℂ) + Complex.I * (Real.sin β : ℂ)) := by
    rw [hcm, Complex.ofReal_neg, Complex.ofReal_neg, hcR, hsR]
    ring
  have hunit_ne : (Real.cos β : ℂ) + Complex.I * (Real.sin β : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.zero_re] at this
    linarith
  have hd_ne : 1 - circleMap 0 1 (2 * β + π) ≠ 0 := by
    rw [hd_val]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')) hunit_ne
  refine ⟨hd_ne, ?_⟩
  have hnum_val : 1 + circleMap 0 1 (2 * β + π) =
      2 * (Real.sin β : ℂ) * ((Real.sin β : ℂ) - Complex.I * (Real.cos β : ℂ)) := by
    rw [hcm, Complex.ofReal_neg, Complex.ofReal_neg, hcR, hsR]
    linear_combination -2 * hpyC
  have hI_mul : Complex.I * ((Real.sin β : ℂ) - Complex.I * (Real.cos β : ℂ)) =
      (Real.cos β : ℂ) + Complex.I * (Real.sin β : ℂ) := by
    rw [mul_sub, ← mul_assoc, Complex.I_mul_I]
    ring
  have hratio : Complex.I * ((1 + circleMap 0 1 (2 * β + π)) / (1 - circleMap 0 1 (2 * β + π))) =
      ((Real.tan β : ℝ) : ℂ) := by
    rw [hnum_val, hd_val, Real.tan_eq_sin_div_cos]
    have hcC : (Real.cos β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    calc Complex.I * (2 * (Real.sin β : ℂ) * ((Real.sin β : ℂ) - Complex.I * (Real.cos β : ℂ)) /
          (2 * (Real.cos β : ℂ) * ((Real.cos β : ℂ) + Complex.I * (Real.sin β : ℂ))))
        = (2 * (Real.sin β : ℂ) * (Complex.I * ((Real.sin β : ℂ) - Complex.I * (Real.cos β : ℂ)))) /
            (2 * (Real.cos β : ℂ) * ((Real.cos β : ℂ) + Complex.I * (Real.sin β : ℂ))) := by ring
      _ = (2 * (Real.sin β : ℂ) * ((Real.cos β : ℂ) + Complex.I * (Real.sin β : ℂ))) /
            (2 * (Real.cos β : ℂ) * ((Real.cos β : ℂ) + Complex.I * (Real.sin β : ℂ))) := by rw [hI_mul]
      _ = (Real.sin β : ℂ) / (Real.cos β : ℂ) := by
          rw [mul_div_mul_right _ _ hunit_ne, mul_div_mul_left _ _ two_ne_zero]
      _ = ((Real.sin β / Real.cos β : ℝ) : ℂ) := by push_cast; rfl
  unfold cayleyAt
  rw [mul_assoc, hratio]
  push_cast; ring

/-! ### 2. Change of variables between `ℝ` (with `poissonKernel`) and `(0, 2π)` -/

private lemma beta_param_integral_eq {z₀ : ℂ} (hz₀ : 0 < z₀.im) (f : ℝ → ℝ) :
    ∫ σ : ℝ, f σ * poissonKernel z₀.re z₀.im σ =
      (2 * π)⁻¹ * ∫ θ in Ioo 0 (2 * π),
        f (z₀.re + z₀.im * Real.tan ((θ - π) / 2)) := by
  let φ : ℝ → ℝ := fun β => z₀.re + z₀.im * Real.tan β
  let φ' : ℝ → ℝ := fun β => z₀.im / Real.cos β ^ 2
  have himg : φ '' Ioo (-(π / 2)) (π / 2) = univ := by
    ext σ
    simp only [mem_image, mem_Ioo, mem_univ, iff_true, φ]
    have hmem : (σ - z₀.re) / z₀.im ∈ Real.tan '' Ioo (-(π / 2)) (π / 2) := by
      rw [Real.image_tan_Ioo]; trivial
    obtain ⟨β, hβ, htan⟩ := hmem
    refine ⟨β, hβ, ?_⟩
    rw [htan]
    field_simp [hz₀.ne']
    ring
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := φ) (f' := φ')
    measurableSet_Ioo
    (fun β hβ => by
      have hc := (Real.cos_pos_of_mem_Ioo hβ).ne'
      have hd := (Real.hasDerivAt_tan hc).const_mul z₀.im |>.const_add z₀.re
      exact hd.congr_deriv (by dsimp [φ']; ring) |>.hasDerivWithinAt)
    (fun β₁ hβ₁ β₂ hβ₂ heq => by
      have h1 : Real.tan β₁ = Real.tan β₂ := by
        dsimp [φ] at heq
        exact mul_left_cancel₀ hz₀.ne' (by linarith)
      exact Real.strictMonoOn_tan.injOn hβ₁ hβ₂ h1)
    (fun σ => f σ * poissonKernel z₀.re z₀.im σ)
  rw [himg, Measure.restrict_univ] at hcov
  have hsimp : ∫ β in Ioo (-(π / 2)) (π / 2),
      |φ' β| • (f (φ β) * poissonKernel z₀.re z₀.im (φ β)) =
      π⁻¹ * ∫ β in Ioo (-(π / 2)) (π / 2), f (φ β) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun β hβ => ?_
    have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo hβ
    have hc2 : 0 < Real.cos β ^ 2 := sq_pos_of_pos hc
    have hφ' : 0 < φ' β := div_pos hz₀ hc2
    rw [abs_of_pos hφ', smul_eq_mul]
    have hP : φ' β * poissonKernel z₀.re z₀.im (φ β) = π⁻¹ := by
      unfold poissonKernel
      dsimp [φ, φ']
      have htan : Real.tan β ^ 2 + 1 = (Real.cos β ^ 2)⁻¹ := by
        rw [Real.tan_eq_sin_div_cos, div_pow]
        have hpy : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
        field_simp [hc.ne']
        linarith
      have hden : (z₀.re + z₀.im * Real.tan β - z₀.re) ^ 2 + z₀.im ^ 2 =
          z₀.im ^ 2 * (Real.tan β ^ 2 + 1) := by ring
      rw [hden, htan]
      field_simp [hz₀.ne', hc.ne', Real.pi_pos.ne']
    calc φ' β * (f (φ β) * poissonKernel z₀.re z₀.im (φ β))
        = f (φ β) * (φ' β * poissonKernel z₀.re z₀.im (φ β)) := by ring
      _ = π⁻¹ * f (φ β) := by rw [hP]; ring
  rw [hcov, hsimp]
  let ψ : ℝ → ℝ := fun β => 2 * β + π
  have hψ_img : ψ '' Ioo (-(π / 2)) (π / 2) = Ioo 0 (2 * π) := by
    ext θ; simp only [mem_image, mem_Ioo, ψ]
    constructor
    · rintro ⟨β, ⟨h1, h2⟩, rfl⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; refine ⟨(θ - π) / 2, ⟨by linarith, by linarith⟩, by ring⟩
  have hψ_cov := integral_image_eq_integral_abs_deriv_smul
    (s := Ioo (-(π / 2)) (π / 2)) (f := ψ) (f' := fun _ => 2)
    measurableSet_Ioo
    (fun β _ => (((hasDerivAt_id β).const_mul 2).add_const π).congr_deriv (by ring) |>.hasDerivWithinAt)
    (fun β₁ _ β₂ _ heq => by dsimp [ψ] at heq; linarith)
    (fun θ => f (z₀.re + z₀.im * Real.tan ((θ - π) / 2)))
  rw [hψ_img] at hψ_cov
  have hψ_eq : ∫ θ in Ioo 0 (2 * π), f (z₀.re + z₀.im * Real.tan ((θ - π) / 2)) =
      2 * ∫ β in Ioo (-(π / 2)) (π / 2), f (φ β) := by
    rw [hψ_cov, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun β _ => ?_
    rw [abs_of_pos two_pos, smul_eq_mul]
    dsimp [φ, ψ]
    have heq_arg : (2 * β + π - π) / 2 = β := by ring
    rw [heq_arg]
  rw [hψ_eq]
  have hpi := Real.pi_pos.ne'
  field_simp

private lemma beta_param_integrable_iff {z₀ : ℂ} (hz₀ : 0 < z₀.im) (f : ℝ → ℝ) :
    Integrable (fun σ : ℝ => f σ * poissonKernel z₀.re z₀.im σ) ↔
      IntegrableOn (fun θ : ℝ => f (z₀.re + z₀.im * Real.tan ((θ - π) / 2))) (Ioo 0 (2 * π)) := by
  let φ : ℝ → ℝ := fun β => z₀.re + z₀.im * Real.tan β
  let φ' : ℝ → ℝ := fun β => z₀.im / Real.cos β ^ 2
  have himg : φ '' Ioo (-(π / 2)) (π / 2) = univ := by
    ext σ; simp only [mem_image, mem_Ioo, mem_univ, iff_true, φ]
    have hmem : (σ - z₀.re) / z₀.im ∈ Real.tan '' Ioo (-(π / 2)) (π / 2) := by
      rw [Real.image_tan_Ioo]; trivial
    obtain ⟨β, hβ, htan⟩ := hmem
    refine ⟨β, hβ, ?_⟩; rw [htan]; field_simp [hz₀.ne']; ring
  have hcov := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := φ) (f' := φ')
    measurableSet_Ioo
    (fun β hβ => by
      have hc := (Real.cos_pos_of_mem_Ioo hβ).ne'
      have hd := (Real.hasDerivAt_tan hc).const_mul z₀.im |>.const_add z₀.re
      exact hd.congr_deriv (by dsimp [φ']; ring) |>.hasDerivWithinAt)
    (fun β₁ hβ₁ β₂ hβ₂ heq => by
      have h1 : Real.tan β₁ = Real.tan β₂ := by
        dsimp [φ] at heq; exact mul_left_cancel₀ hz₀.ne' (by linarith)
      exact Real.strictMonoOn_tan.injOn hβ₁ hβ₂ h1)
    (fun σ => f σ * poissonKernel z₀.re z₀.im σ)
  rw [himg, integrableOn_univ] at hcov
  have hcongr : IntegrableOn (fun β : ℝ => |φ' β| • (f (φ β) * poissonKernel z₀.re z₀.im (φ β)))
      (Ioo (-(π / 2)) (π / 2)) ↔
      IntegrableOn (fun β : ℝ => π⁻¹ * f (φ β)) (Ioo (-(π / 2)) (π / 2)) := by
    refine integrableOn_congr_fun (fun β hβ => ?_) measurableSet_Ioo
    have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo hβ
    have hφ' : 0 < φ' β := div_pos hz₀ (sq_pos_of_pos hc)
    rw [abs_of_pos hφ', smul_eq_mul]
    have hP : φ' β * poissonKernel z₀.re z₀.im (φ β) = π⁻¹ := by
      unfold poissonKernel; dsimp [φ, φ']
      have htan : Real.tan β ^ 2 + 1 = (Real.cos β ^ 2)⁻¹ := by
        rw [Real.tan_eq_sin_div_cos, div_pow]
        have hpy : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
        field_simp [hc.ne']; linarith
      have hden : (z₀.re + z₀.im * Real.tan β - z₀.re) ^ 2 + z₀.im ^ 2 =
          z₀.im ^ 2 * (Real.tan β ^ 2 + 1) := by ring
      rw [hden, htan]; field_simp [hz₀.ne', hc.ne', Real.pi_pos.ne']
    calc φ' β * (f (φ β) * poissonKernel z₀.re z₀.im (φ β))
        = f (φ β) * (φ' β * poissonKernel z₀.re z₀.im (φ β)) := by ring
      _ = π⁻¹ * f (φ β) := by rw [hP]; ring
  rw [hcov, hcongr, IntegrableOn,
    integrable_const_mul_iff (Ne.isUnit (inv_ne_zero Real.pi_pos.ne'))]
  let ψ : ℝ → ℝ := fun β => 2 * β + π
  have hψ_img : ψ '' Ioo (-(π / 2)) (π / 2) = Ioo 0 (2 * π) := by
    ext θ; simp only [mem_image, mem_Ioo, ψ]
    constructor
    · rintro ⟨β, ⟨h1, h2⟩, rfl⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; refine ⟨(θ - π) / 2, ⟨by linarith, by linarith⟩, by ring⟩
  have hψ_cov := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioo (-(π / 2)) (π / 2)) (f := ψ) (f' := fun _ => 2)
    measurableSet_Ioo
    (fun β _ => (((hasDerivAt_id β).const_mul 2).add_const π).congr_deriv (by ring) |>.hasDerivWithinAt)
    (fun β₁ _ β₂ _ heq => by dsimp [ψ] at heq; linarith)
    (fun θ => f (z₀.re + z₀.im * Real.tan ((θ - π) / 2)))
  rw [hψ_img] at hψ_cov
  rw [hψ_cov]
  have hcongr2 : IntegrableOn (fun β : ℝ => |(2 : ℝ)| • f (z₀.re + z₀.im * Real.tan ((ψ β - π) / 2)))
      (Ioo (-(π / 2)) (π / 2)) ↔
      IntegrableOn (fun β : ℝ => 2 * f (φ β)) (Ioo (-(π / 2)) (π / 2)) := by
    refine integrableOn_congr_fun (fun β _ => ?_) measurableSet_Ioo
    rw [abs_of_pos two_pos, smul_eq_mul]
    dsimp [φ, ψ]
    have heq_arg : (2 * β + π - π) / 2 = β := by ring
    rw [heq_arg]
  rw [hcongr2, IntegrableOn, integrable_const_mul_iff (Ne.isUnit two_ne_zero)]

private lemma ae_pullback_theta {z₀ : ℂ} (hz₀ : 0 < z₀.im) {P : ℝ → Prop}
    (hP : ∀ᵐ σ : ℝ ∂volume, P σ) :
    ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo 0 (2 * π))),
      P (z₀.re + z₀.im * Real.tan ((θ - π) / 2)) := by
  let S : Set ℝ := {σ : ℝ | ¬ P σ}
  have hS0 : volume S = 0 := ae_iff.mp hP
  have h1 : Integrable (fun σ : ℝ => S.indicator (fun _ => (1 : ℝ)) σ * poissonKernel z₀.re z₀.im σ) := by
    refine (integrable_zero ℝ ℝ volume).congr ?_
    have hS_ae : S =ᵐ[volume] (∅ : Set ℝ) := ae_eq_empty.mpr hS0
    filter_upwards [hP] with σ hσ
    have hnot : σ ∉ S := fun h => h hσ
    simp [Set.indicator_of_notMem hnot]
  have h2 := (beta_param_integrable_iff hz₀ (S.indicator (fun _ => (1 : ℝ)))).mp h1
  have hval := beta_param_integral_eq hz₀ (S.indicator (fun _ => (1 : ℝ)))
  have hzero1 : ∫ σ : ℝ, S.indicator (fun _ => (1 : ℝ)) σ * poissonKernel z₀.re z₀.im σ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hP] with σ hσ
    have hnot : σ ∉ S := fun h => h hσ
    simp [Set.indicator_of_notMem hnot]
  rw [hzero1] at hval
  have h2pi : (2 * π)⁻¹ ≠ 0 := inv_ne_zero (by positivity [Real.pi_pos])
  have hzero2 : ∫ θ in Ioo 0 (2 * π),
      S.indicator (fun _ => (1 : ℝ)) (z₀.re + z₀.im * Real.tan ((θ - π) / 2)) = 0 := by
    rcases mul_eq_zero.mp hval.symm with h | h
    · exact absurd h h2pi
    · exact h
  have hae0 : (fun θ : ℝ => S.indicator (fun _ => (1 : ℝ)) (z₀.re + z₀.im * Real.tan ((θ - π) / 2))) =ᵐ[volume.restrict (Ioo 0 (2 * π))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun θ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) h2).mp hzero2
  filter_upwards [hae0] with θ hθ
  by_contra hnot
  have hmem : z₀.re + z₀.im * Real.tan ((θ - π) / 2) ∈ S := hnot
  simp [Set.indicator_of_mem hmem] at hθ

/-! ### 3. Half-plane Poisson--Jensen inequality -/

/-- **Poisson--Jensen inequality on the upper half-plane `{z : ℂ | 0 < z.im}`** for a bounded
holomorphic function `F` with boundary values `F_bdy` a.e. on `ℝ`. -/
theorem halfPlane_poissonJensen {F : ℂ → ℂ} {F_bdy : ℝ → ℂ} {M : ℝ} (_hM : 0 < M)
    (hF_diff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hF_bd : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ M)
    (hF_bdy : ∀ᵐ σ : ℝ ∂volume, Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (F_bdy σ)))
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hFz₀ : F z₀ ≠ 0) :
    Integrable (fun σ : ℝ => Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ) ∧
      Real.log ‖F z₀‖ ≤ ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ := by
  let h : ℂ → ℂ := fun w => F (cayleyAt z₀ w)
  have hh_diff : DifferentiableOn ℂ h (ball 0 1) := by
    refine hF_diff.comp (differentiableOn_cayleyAt z₀) ?_
    intro w hw; exact cayleyAt_im_pos hz₀ hw
  have hh_an : AnalyticOnNhd ℂ h (ball 0 1) := hh_diff.analyticOnNhd isOpen_ball
  have hh0 : h 0 ≠ 0 := by simpa [h, cayleyAt_zero] using hFz₀
  have hh_bd : ∀ w ∈ ball (0 : ℂ) 1, ‖h w‖ ≤ M := fun w hw => hF_bd _ (cayleyAt_im_pos hz₀ hw)
  -- Sequence of radii `r_n = 1 - 1 / (n + 2) ↑ 1`
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hr_pos : ∀ n : ℕ, 0 < r n := fun n => by
    dsimp [r]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hr_lt : ∀ n : ℕ, r n < 1 := fun n => by
    dsimp [r]; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity]
  have hr_tendsto : Tendsto r atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [r] using tendsto_const_nhds.sub h0
  -- Jensen on `closedBall 0 (r n)`
  have hjensen_r : ∀ n : ℕ,
      Real.log ‖h 0‖ ≤ circleAverage (Real.log ‖h ·‖) 0 (r n) := fun n => by
    have hsub : closedBall (0 : ℂ) |r n| ⊆ ball 0 1 := by
      rw [abs_of_pos (hr_pos n)]
      exact closedBall_subset_ball (hr_lt n)
    have hh_sub : AnalyticOnNhd ℂ h (closedBall 0 |r n|) := hh_an.mono hsub
    have hform := hh_sub.circleAverage_log_norm (hr_pos n).ne' hh0
    have hsum_nn : 0 ≤ ∑ᶠ u, (divisor h (closedBall 0 |r n|) u : ℝ) *
        Real.log (|r n| * ‖(0 : ℂ) - u‖⁻¹) := by
      refine finsum_nonneg fun u => ?_
      by_cases hu : u ∈ (divisor h (closedBall 0 |r n|)).support
      · have hDnn : 0 ≤ divisor h (closedBall 0 |r n|) u :=
          hh_sub.divisor_nonneg u
        have hu_mem : u ∈ closedBall (0 : ℂ) |r n| :=
          (divisor h (closedBall 0 |r n|)).supportWithinDomain hu
        have hu_ne : u ≠ 0 := by
          intro h0; subst h0
          have hdiv0 := divisor_apply hh_sub.meromorphicOn (by simp : (0 : ℂ) ∈ closedBall 0 |r n|)
          have hord : analyticOrderAt h 0 = 0 :=
            (hh_sub 0 (by simp)).analyticOrderAt_eq_zero.2 hh0
          rw [Function.mem_support, hdiv0, (hh_sub 0 (by simp)).meromorphicOrderAt_eq, hord] at hu
          exact hu (by simp)
        have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
        have hle : ‖u‖ ≤ |r n| := by simpa using hu_mem
        have harg : 1 ≤ |r n| * ‖(0 : ℂ) - u‖⁻¹ := by
          rw [zero_sub, norm_neg, ← div_eq_mul_inv, one_le_div hnorm_pos]
          exact hle
        exact mul_nonneg (Int.cast_nonneg_iff.mpr hDnn) (Real.log_nonneg harg)
      · have h0 : MeromorphicOn.divisor h (closedBall 0 |r n|) u = 0 := by
          by_contra hne; exact hu hne
        simp [h0]
    have hlog_eq : ∑ᶠ u, (MeromorphicOn.divisor h (closedBall 0 |r n|) u : ℝ) *
          Real.log (r n * ‖(0 : ℂ) - u‖⁻¹) =
        ∑ᶠ u, (MeromorphicOn.divisor h (closedBall 0 |r n|) u : ℝ) *
          Real.log (|r n| * ‖(0 : ℂ) - u‖⁻¹) := by
      rw [abs_of_pos (hr_pos n)]
    linarith [hform, hlog_eq, hsum_nn]
  -- Define `φ_n θ = ENNReal.ofReal (log M - log ‖h (circleMap 0 (r n) θ)‖)` (with `⊤` at zeros)
  let σ : ℝ → ℝ := fun θ => z₀.re + z₀.im * Real.tan ((θ - π) / 2)
  let g : ℕ → ℝ → ℝ≥0∞ := fun n θ =>
    if h (circleMap 0 (r n) θ) = 0 then ⊤
    else ENNReal.ofReal (Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖)
  have hpi := Real.pi_pos
  -- Each `g n` has finite lintegral bounded by `2π (log M - log ‖h 0‖)`
  have hg_lint : ∀ n : ℕ,
      ∫⁻ θ in Ioo 0 (2 * π), g n θ ≤ ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖h 0‖)) := by
    intro n
    have hsub : closedBall (0 : ℂ) |r n| ⊆ ball 0 1 := by
      rw [abs_of_pos (hr_pos n)]
      exact closedBall_subset_ball (hr_lt n)
    have hci : CircleIntegrable (Real.log ‖h ·‖) 0 (r n) :=
      ((hh_an.mono hsub).mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    have hint_diff : IntervalIntegrable (fun θ : ℝ => Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖)
        volume 0 (2 * π) :=
      intervalIntegrable_const.sub hci
    have hint_Ioo : IntegrableOn (fun θ : ℝ => Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖)
        (Ioo 0 (2 * π)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 hint_diff).mono_set
        Ioo_subset_Ioc_self
    -- Finitely many zeros on `closedBall 0 (r n)`
    have hfin_zeros : {θ ∈ Ioo 0 (2 * π) | h (circleMap 0 (r n) θ) = 0}.Finite := by
      have hdiv_fin : (MeromorphicOn.divisor h (closedBall 0 |r n|)).support.Finite :=
        (MeromorphicOn.divisor h (closedBall 0 |r n|)).finiteSupport (isCompact_closedBall _ _)
      have hord_ne : ∀ u : closedBall (0 : ℂ) |r n|, meromorphicOrderAt h u ≠ ⊤ := by
        intro ⟨u, hu⟩
        have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) |r n| := by simp
        refine (hh_an.mono hsub).meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
          (convex_closedBall _ _).isPreconnected h0mem hu ?_
        rw [((hh_an.mono hsub) 0 h0mem).meromorphicOrderAt_eq,
          ((hh_an.mono hsub) 0 h0mem).analyticOrderAt_eq_zero.2 hh0]
        simp
      have hinj : InjOn (circleMap 0 (r n)) (Ioo 0 (2 * π)) := fun θ₁ hθ₁ θ₂ hθ₂ heq => by
        simp only [circleMap, zero_add] at heq
        have hrC : ((r n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr_pos n).ne'
        have hexp : Complex.exp ((θ₁ : ℂ) * Complex.I) = Complex.exp ((θ₂ : ℂ) * Complex.I) :=
          mul_left_cancel₀ hrC heq
        obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
        have hk' : (θ₁ : ℂ) * Complex.I = (θ₂ : ℂ) * Complex.I + k * (2 * π * Complex.I) := hk
        have hre_mul := congrArg Complex.im hk'
        simp at hre_mul
        have hlt1 : θ₁ - θ₂ < 2 * π := by linarith [hθ₁.2, hθ₂.1]
        have hlt2 : -(2 * π) < θ₁ - θ₂ := by linarith [hθ₁.1, hθ₂.2]
        have hk0 : k = 0 := by
          have : -(2 * π) < (k : ℝ) * (2 * π) ∧ (k : ℝ) * (2 * π) < 2 * π := by
            constructor <;> linarith
          have hk1 : -1 < (k : ℝ) := by nlinarith
          have hk2 : (k : ℝ) < 1 := by nlinarith
          have : -1 < k := by exact_mod_cast hk1
          have : k < 1 := by exact_mod_cast hk2
          omega
        rw [hk0] at hre_mul; simp at hre_mul; linarith
      refine Set.Finite.of_finite_image (hdiv_fin.subset ?_) (hinj.mono fun θ hθ => hθ.1)
      rintro _ ⟨θ, ⟨hθ, hz⟩, rfl⟩
      have hmem : circleMap 0 (r n) θ ∈ closedBall (0 : ℂ) |r n| := by
        simp [mem_closedBall, dist_zero_right, norm_circleMap_zero]
      rw [Function.mem_support, divisor_apply (hh_an.mono hsub).meromorphicOn hmem,
        ((hh_an.mono hsub) _ hmem).meromorphicOrderAt_eq]
      have hne_top : analyticOrderAt h (circleMap 0 (r n) θ) ≠ ⊤ := by
        have := hord_ne ⟨_, hmem⟩
        rw [((hh_an.mono hsub) _ hmem).meromorphicOrderAt_eq] at this
        simpa using this
      rcases ENat.ne_top_iff_exists.mp hne_top with ⟨m, hm⟩
      have hm_pos : 0 < m := by
        by_contra hm0
        have hm0' : m = 0 := by omega
        subst hm0'
        have hord0 : analyticOrderAt h (circleMap 0 (r n) θ) = 0 := hm.symm
        exact (((hh_an.mono hsub) _ hmem).analyticOrderAt_eq_zero.mp hord0) hz
      intro h0
      rw [← hm] at h0
      simp at h0
      omega
    have hnull : volume {θ ∈ Ioo 0 (2 * π) | h (circleMap 0 (r n) θ) = 0} = 0 :=
      hfin_zeros.measure_zero volume
    have hae_ne : ∀ᵐ θ ∂(volume.restrict (Ioo 0 (2 * π))), h (circleMap 0 (r n) θ) ≠ 0 := by
      have hae_univ : ∀ᵐ θ ∂volume, θ ∉ {θ ∈ Ioo 0 (2 * π) | h (circleMap 0 (r n) θ) = 0} := by
        rw [ae_iff]
        refine measure_mono_null (fun θ h => by simpa [and_assoc] using h) hnull
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hae_univ] with θ hθ hnot h0
      exact hnot ⟨hθ, h0⟩
    have hae_eq : g n =ᵐ[volume.restrict (Ioo 0 (2 * π))]
        fun θ => ENNReal.ofReal (Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖) := by
      filter_upwards [hae_ne] with θ hne
      simp [g, hne]
    rw [lintegral_congr_ae hae_eq]
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 (2 * π))]
        fun θ => Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hae_ne] with θ _ hne
      simp only [Pi.zero_apply]
      have hmem : circleMap 0 (r n) θ ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
        exact hr_lt n
      have hpos : 0 < ‖h (circleMap 0 (r n) θ)‖ := norm_pos_iff.mpr hne
      linarith [Real.log_le_log hpos (hh_bd _ hmem)]
    rw [← ofReal_integral_eq_lintegral_ofReal hint_Ioo hnn]
    apply ENNReal.ofReal_le_ofReal
    have hint_eq : ∫ θ in Ioo 0 (2 * π), (Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖) =
        2 * π * (Real.log M - circleAverage (Real.log ‖h ·‖) 0 (r n)) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity),
        intervalIntegral.integral_sub intervalIntegrable_const hci, intervalIntegral.integral_const,
        smul_eq_mul, sub_zero]
      have hca : circleAverage (Real.log ‖h ·‖) 0 (r n) =
          (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h (circleMap 0 (r n) θ)‖ := by
        rw [Real.circleAverage_def, smul_eq_mul]
      rw [hca]
      have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hint_eq]
    gcongr
    exact hjensen_r n
  -- Fatou's lemma on `g n`
  have hg_meas : ∀ n : ℕ, Measurable (g n) := fun n => by
    have hh_cont : Continuous (fun θ : ℝ => h (circleMap 0 (r n) θ)) := by
      refine continuous_iff_continuousAt.mpr fun θ => ?_
      have hmem : circleMap 0 (r n) θ ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
        exact hr_lt n
      exact (hh_an _ hmem).continuousAt.comp (continuous_circleMap 0 (r n)).continuousAt
    refine Measurable.ite (measurableSet_eq_fun hh_cont.measurable measurable_const)
      measurable_const ?_
    exact ENNReal.measurable_ofReal.comp (measurable_const.sub (Real.measurable_log.comp hh_cont.norm.measurable))
  have hfatou : ∫⁻ θ in Ioo 0 (2 * π), Filter.liminf (fun n => g n θ) atTop ≤
      ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖h 0‖)) := by
    refine (lintegral_liminf_le hg_meas).trans ?_
    exact Filter.liminf_le_of_frequently_le (Eventually.of_forall hg_lint).frequently
  -- Boundary values of `h(circleMap 0 (r n) θ)` a.e. on `Ioo 0 (2 * π)`
  have hlim_ae : ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo 0 (2 * π))),
      Tendsto (fun n : ℕ => h (circleMap 0 (r n) θ)) atTop (𝓝 (F_bdy (σ θ))) := by
    have hpull := ae_pullback_theta hz₀ hF_bdy
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hpull] with θ hθ htend
    set β : ℝ := (θ - π) / 2
    have hβ : β ∈ Ioo (-(π / 2)) (π / 2) := ⟨by dsimp [β]; linarith [hθ.1], by dsimp [β]; linarith [hθ.2]⟩
    have hθ_eq : θ = 2 * β + π := by dsimp [β]; ring
    obtain ⟨hd_ne, hcay⟩ := cayleyAt_circle_beta z₀ hβ
    rw [← hθ_eq] at hcay hd_ne
    have h_cay_cont : ContinuousAt (cayleyAt z₀) (circleMap 0 1 θ) := by
      unfold cayleyAt
      refine ContinuousAt.add continuousAt_const (ContinuousAt.mul continuousAt_const ?_)
      exact (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id) hd_ne
    have h_cay_tend : Tendsto (cayleyAt z₀) (𝓝[ball 0 1] (circleMap 0 1 θ))
        (𝓝[{z : ℂ | 0 < z.im}] (σ θ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · rw [← hcay]; exact h_cay_cont.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        exact cayleyAt_im_pos hz₀ hw
    have h_h_tend : Tendsto h (𝓝[ball 0 1] (circleMap 0 1 θ)) (𝓝 (F_bdy (σ θ))) :=
      htend.comp h_cay_tend
    have h_seq : Tendsto (fun n : ℕ => circleMap 0 (r n) θ) atTop (𝓝[ball 0 1] (circleMap 0 1 θ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous (fun ρ : ℝ => circleMap 0 ρ θ) := by
          simp only [circleMap]; fun_prop
        simpa [Function.comp_def] using (hc.tendsto 1).comp hr_tendsto
      · refine Eventually.of_forall fun n => ?_
        rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
        exact hr_lt n
    exact h_h_tend.comp h_seq
  -- From `hfatou`, `F_bdy (σ θ) ≠ 0` a.e. and `liminf (g n θ) = ENNReal.ofReal (log M - log ‖F_bdy (σ θ)‖)`
  have hfin_liminf : ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo 0 (2 * π))),
      Filter.liminf (fun n => g n θ) atTop < ⊤ :=
    ae_lt_top (Measurable.liminf hg_meas) (hfatou.trans_lt ENNReal.ofReal_lt_top).ne
  have hFbdy_ne : ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo 0 (2 * π))), F_bdy (σ θ) ≠ 0 := by
    filter_upwards [hlim_ae, hfin_liminf] with θ htend hlt h0
    rw [h0] at htend
    have hnorm0 : Tendsto (fun n : ℕ => ‖h (circleMap 0 (r n) θ)‖) atTop (𝓝 0) := by
      simpa using htend.norm
    have htop : Tendsto (fun n : ℕ => g n θ) atTop (𝓝 ⊤) := by
      rw [ENNReal.tendsto_nhds_top_iff_nnreal]
      intro N
      have hbd : ∀ᶠ n in atTop, ‖h (circleMap 0 (r n) θ)‖ < Real.exp (Real.log M - (N : ℝ)) :=
        hnorm0.eventually (gt_mem_nhds (Real.exp_pos _))
      filter_upwards [hbd] with n hn
      by_cases hzn : h (circleMap 0 (r n) θ) = 0
      · simp [g, hzn]
      · simp only [g, hzn, ↓reduceIte]
        have hpos : 0 < ‖h (circleMap 0 (r n) θ)‖ := norm_pos_iff.mpr hzn
        have hlog : Real.log ‖h (circleMap 0 (r n) θ)‖ < Real.log M - (N : ℝ) :=
          (Real.log_lt_iff_lt_exp hpos).mpr hn
        have hN : (N : ℝ) < Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖ := by linarith
        exact ENNReal.coe_lt_coe.mpr (by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by linarith [NNReal.coe_nonneg N])]
          exact hN)
    exact hlt.ne (htop.liminf_eq)
  have hlim_eq : ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo 0 (2 * π))),
      Filter.liminf (fun n => g n θ) atTop =
        ENNReal.ofReal (Real.log M - Real.log ‖F_bdy (σ θ)‖) := by
    filter_upwards [hlim_ae, hFbdy_ne] with θ htend hne
    have hev : ∀ᶠ n in atTop, h (circleMap 0 (r n) θ) ≠ 0 :=
      htend.eventually_ne hne
    have htend_g : Tendsto (fun n : ℕ => g n θ) atTop
        (𝓝 (ENNReal.ofReal (Real.log M - Real.log ‖F_bdy (σ θ)‖))) := by
      have htend_val : Tendsto (fun n : ℕ =>
          ENNReal.ofReal (Real.log M - Real.log ‖h (circleMap 0 (r n) θ)‖)) atTop
          (𝓝 (ENNReal.ofReal (Real.log M - Real.log ‖F_bdy (σ θ)‖))) := by
        refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
        exact tendsto_const_nhds.sub ((Real.continuousAt_log (norm_ne_zero_iff.mpr hne)).tendsto.comp htend.norm)
      refine htend_val.congr' ?_
      filter_upwards [hev] with n hn
      simp [g, hn]
    exact htend_g.liminf_eq
  have hFbdy_le : ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo 0 (2 * π))),
      ‖F_bdy (σ θ)‖ ≤ M := by
    filter_upwards [hlim_ae] with θ htend
    refine le_of_tendsto htend.norm (Eventually.of_forall fun n => ?_)
    refine hh_bd _ ?_
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
    exact hr_lt n
  have hdiff_nn : ∀ᵐ θ : ℝ ∂(volume.restrict (Ioo 0 (2 * π))),
      0 ≤ Real.log M - Real.log ‖F_bdy (σ θ)‖ := by
    filter_upwards [hFbdy_ne, hFbdy_le] with θ hne hle
    linarith [Real.log_le_log (norm_pos_iff.mpr hne) hle]
  -- Measurability of `θ ↦ F_bdy (σ θ)`
  have hF_meas_Ioo : AEStronglyMeasurable (fun θ => F_bdy (σ θ)) (volume.restrict (Ioo 0 (2 * π))) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => ?_) hlim_ae
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hmem : circleMap 0 (r n) θ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (hr_pos n)]
      exact hr_lt n
    exact (hh_an _ hmem).continuousAt.comp (continuous_circleMap 0 (r n)).continuousAt
  have hdiff_meas : AEStronglyMeasurable (fun θ => Real.log M - Real.log ‖F_bdy (σ θ)‖)
      (volume.restrict (Ioo 0 (2 * π))) :=
    aestronglyMeasurable_const.sub
      (Real.measurable_log.comp_aemeasurable hF_meas_Ioo.norm.aemeasurable).aestronglyMeasurable
  have hdiff_lint : ∫⁻ θ in Ioo 0 (2 * π),
      ENNReal.ofReal (Real.log M - Real.log ‖F_bdy (σ θ)‖) ≤
      ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖h 0‖)) := by
    rw [← lintegral_congr_ae hlim_eq]
    exact hfatou
  have hdiff_int : IntegrableOn (fun θ => Real.log M - Real.log ‖F_bdy (σ θ)‖) (Ioo 0 (2 * π)) := by
    refine ⟨hdiff_meas, ?_⟩
    rw [HasFiniteIntegral]
    have hcongr : (fun θ => ‖Real.log M - Real.log ‖F_bdy (σ θ)‖‖ₑ) =ᵐ[volume.restrict (Ioo 0 (2 * π))]
        fun θ => ENNReal.ofReal (Real.log M - Real.log ‖F_bdy (σ θ)‖) := by
      filter_upwards [hdiff_nn] with θ hnn
      rw [← ofReal_norm, Real.norm_of_nonneg hnn]
    rw [lintegral_congr_ae hcongr]
    exact hdiff_lint.trans_lt ENNReal.ofReal_lt_top
  have hdiff_le : ∫ θ in Ioo 0 (2 * π), (Real.log M - Real.log ‖F_bdy (σ θ)‖) ≤
      2 * π * (Real.log M - Real.log ‖h 0‖) := by
    have h1 : ENNReal.ofReal (∫ θ in Ioo 0 (2 * π), (Real.log M - Real.log ‖F_bdy (σ θ)‖)) ≤
        ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖h 0‖)) := by
      rwa [ofReal_integral_eq_lintegral_ofReal hdiff_int hdiff_nn]
    have hM_ge : 0 ≤ 2 * π * (Real.log M - Real.log ‖h 0‖) := by
      have h0_pos : 0 < ‖h 0‖ := norm_pos_iff.mpr hh0
      have h0_le : ‖h 0‖ ≤ M := hh_bd 0 (by simp)
      have := Real.log_le_log h0_pos h0_le
      nlinarith
    exact (ENNReal.ofReal_le_ofReal_iff hM_ge).mp h1
  have hconst_int : IntegrableOn (fun _ : ℝ => Real.log M) (Ioo 0 (2 * π)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hlog_int_Ioo : IntegrableOn (fun θ => Real.log ‖F_bdy (σ θ)‖) (Ioo 0 (2 * π)) := by
    have heq : (fun θ => Real.log ‖F_bdy (σ θ)‖) =
        fun θ => Real.log M - (Real.log M - Real.log ‖F_bdy (σ θ)‖) := by
      ext θ; ring
    rw [heq]
    exact hconst_int.sub hdiff_int
  have hlog_ge_Ioo : Real.log ‖F z₀‖ ≤ (2 * π)⁻¹ * ∫ θ in Ioo 0 (2 * π), Real.log ‖F_bdy (σ θ)‖ := by
    have hsub_int : ∫ θ in Ioo 0 (2 * π), (Real.log M - Real.log ‖F_bdy (σ θ)‖) =
        2 * π * Real.log M - ∫ θ in Ioo 0 (2 * π), Real.log ‖F_bdy (σ θ)‖ := by
      rw [integral_sub hconst_int hlog_int_Ioo, setIntegral_const, Real.volume_real_Ioo_of_le (by positivity),
        sub_zero, smul_eq_mul]
    rw [hsub_int] at hdiff_le
    have hle' : 2 * π * Real.log ‖F z₀‖ ≤ ∫ θ in Ioo 0 (2 * π), Real.log ‖F_bdy (σ θ)‖ := by
      have : h 0 = F z₀ := by simp [h, cayleyAt_zero]
      rw [this] at hdiff_le
      linarith
    calc Real.log ‖F z₀‖ = (2 * π)⁻¹ * (2 * π * Real.log ‖F z₀‖) := by
          field_simp [hpi.ne']
      _ ≤ (2 * π)⁻¹ * ∫ θ in Ioo 0 (2 * π), Real.log ‖F_bdy (σ θ)‖ := by gcongr
  refine ⟨(beta_param_integrable_iff hz₀ (fun s => Real.log ‖F_bdy s‖)).mpr hlog_int_Ioo, ?_⟩
  rw [beta_param_integral_eq hz₀ (fun s => Real.log ‖F_bdy s‖)]
  exact hlog_ge_Ioo

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.halfPlane_poissonJensen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.halfPlane_poissonJensen

end FormalResearch.ModularBootstrap.PoissonJensen
