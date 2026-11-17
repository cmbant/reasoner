module

public import FormalResearch.Special.AiryPwsConverseMain
public import FormalResearch.Special.AiryFourier

/-!
# The twist turns Airy translates into plane waves

For `Im ζ > 0` and every real `τ`, the Fourier transform of the Airy translate `Φ_τ(u) = Ai(k(u+τ))`
(`airyPhi`, `k = 2^{2/3}`) is `k⁻¹ e^{iζ³/12} e^{iζτ}` (`airyFhat_airyPhi`), i.e. its twisted transform is the
plane wave `F̃_{Φ_τ}(ζ) = e^{iζτ}` (`airyFtilde_airyPhi`).  This is the "Since `∫ Ai(x)e^{-iωx}dx = e^{iω³/3}`" step of
Theorem 3.1 of `CFT/notes/general_theorems.tex`; it follows from the tilted Laplace transform
`integral_airyAi_mul_exp_complex` (`AiryFourier`), by a dilation and a translation.

**Not formalised** here: the same identity at real `ζ` (a conditionally convergent integral).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma airyPhiK_cube : airyPhiK ^ 3 = 4 := by
  unfold airyPhiK
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem airyFhat_airyPhi {ζ : ℂ} (hζ : 0 < ζ.im) (τ : ℝ) :
    airyFhat (airyPhi τ) ζ = ((airyPhiK : ℂ))⁻¹ * cexp (I * ζ ^ 3 / 12) * cexp (I * ζ * τ) := by
  have hk := airyPhiK_pos
  have hk0 : (airyPhiK : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  set a : ℂ := ((airyPhiK⁻¹ : ℝ) : ℂ) * (-(I * ζ)) with ha
  have hre : 0 < a.re := by
    rw [ha, Complex.re_ofReal_mul]
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_neg]
    positivity
  have hak : a * (airyPhiK : ℂ) = -(I * ζ) := by
    rw [ha]; push_cast; field_simp
  set G : ℝ → ℂ := fun x => (airyAi x : ℂ) * cexp (a * x) with hG
  have hGint : ∫ x : ℝ, G x = cexp (a ^ 3 / 3) := integral_airyAi_mul_exp_complex hre
  have e1 : ∀ u : ℝ, airyPhi τ (u : ℂ) * cexp (-(I * ζ * (u : ℂ))) = cexp (I * ζ * τ) * G (airyPhiK * (u + τ)) := by
    intro u
    unfold airyPhi
    have h1 : (airyPhiK : ℂ) * ((u : ℂ) + (τ : ℂ)) = ((airyPhiK * (u + τ) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, airyAiC_ofReal, hG]
    simp only
    have h2 : cexp (a * ((airyPhiK * (u + τ) : ℝ) : ℂ)) = cexp (-(I * ζ * (u : ℂ))) * cexp (-(I * ζ * τ)) := by
      rw [← Complex.exp_add]; congr 1
      push_cast
      linear_combination ((u : ℂ) + τ) * hak
    rw [h2]
    have h3 : cexp (I * ζ * τ) * cexp (-(I * ζ * τ)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    linear_combination -((airyAi (airyPhiK * (u + τ)) : ℂ) * cexp (-(I * ζ * (u : ℂ)))) * h3
  unfold airyFhat
  simp_rw [e1]
  rw [integral_const_mul]
  have e2 : ∫ u : ℝ, G (airyPhiK * (u + τ)) = ∫ u : ℝ, G (airyPhiK * u) := by
    have := integral_add_right_eq_self (μ := volume) (fun u : ℝ => G (airyPhiK * u)) τ
    simpa using this
  rw [e2, Measure.integral_comp_mul_left G airyPhiK, hGint, abs_inv, abs_of_pos hk, Complex.real_smul]
  have e3 : cexp (a ^ 3 / 3) = cexp (I * ζ ^ 3 / 12) := by
    congr 1
    have hk3 : (airyPhiK : ℂ) ^ 3 = 4 := by exact_mod_cast airyPhiK_cube
    have : a ^ 3 * (airyPhiK : ℂ) ^ 3 = (-(I * ζ)) ^ 3 := by rw [← mul_pow, hak]
    rw [hk3] at this
    have h4 : a ^ 3 = (-(I * ζ)) ^ 3 / 4 := by rw [← this]; ring
    rw [h4]
    have : (-(I * ζ)) ^ 3 = I * ζ ^ 3 := by
      have hI : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
      rw [neg_pow, mul_pow, hI]; ring
    rw [this]; ring
  rw [e3]
  push_cast
  ring

/-- **The twist turns Airy translates into plane waves**: `F̃_{Φ_τ}(ζ) = e^{iζτ}` for `Im ζ > 0`. -/
theorem airyFtilde_airyPhi {ζ : ℂ} (hζ : 0 < ζ.im) (τ : ℝ) :
    airyFtilde (airyPhi τ) ζ = cexp (I * ζ * τ) := by
  have hk0 : (airyPhiK : ℂ) ≠ 0 := by exact_mod_cast airyPhiK_pos.ne'
  unfold airyFtilde
  rw [airyFhat_airyPhi hζ τ]
  have e : cexp (-(I * ζ ^ 3 / 12)) * cexp (I * ζ ^ 3 / 12) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination ((airyPhiK : ℂ) * (airyPhiK : ℂ)⁻¹ * cexp (I * ζ * τ)) * e +
    cexp (I * ζ * τ) * (mul_inv_cancel₀ hk0)

/-- info: 'FormalResearch.Special.airyFtilde_airyPhi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyFtilde_airyPhi

end FormalResearch.Special
