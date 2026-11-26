module

public import FormalResearch.SignUncertainty.UctBumpE0

/-!
# Fourier inversion for the derivatives of a bump profile: `τ^k` multipliers (F2a, `uct:bump-weighted`)

`fourier_inversion_general`: `(c/2π) ∫ e^{icLτ} ĝ(icτ) dτ = g(L)` for a continuous integrable `g` with integrable line transform.
`tau_pow_inversion`: for a bump profile `B`, `∫ τ^k e^{icLτ} B̂(icτ) dτ = (2π/c) (i c)^{-k} B^{(k)}(L)` (inversion applied to `B^{(k)}`, whose
transform is `(icτ)^k B̂(icτ)`).

Class: proved, no hypotheses beyond the stated integrability.
-/

@[expose] public section

open MeasureTheory Set Filter Topology FourierTransform
open scoped Real

namespace FormalResearch.SignUncertainty

theorem fourier_inversion_general {g : ℝ → ℝ} (hfi : Integrable fun x : ℝ => (g x : ℂ)) (hfc : Continuous g) {c : ℝ}
    (hc : 0 < c) (hint : Integrable fun τ : ℝ => bumpLaplace g ((c : ℂ) * ((τ : ℂ) * Complex.I))) (L : ℝ) :
    ((c / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
      bumpLaplace g ((c : ℂ) * ((τ : ℂ) * Complex.I)) = (g L : ℂ) := by
  set f : ℝ → ℂ := fun x => (g x : ℂ) with hf
  have hfc' : Continuous f := Complex.continuous_ofReal.comp hfc
  set R : ℝ := 2 * Real.pi / c with hR
  have hR0 : R ≠ 0 := by positivity
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hF : ∀ w : ℝ, 𝓕 f w = bumpLaplace g ((c : ℂ) * (((w * R : ℝ) : ℂ) * Complex.I)) := by
    intro w
    rw [hf, fourier_bump_eq]
    congr 1
    rw [hR]
    push_cast
    field_simp
  have hFi : Integrable (𝓕 f) := by
    have := hint.comp_mul_right' hR0
    refine this.congr (ae_of_all _ fun w => ?_)
    simp only [hF]
  have hinv := hfc'.fourierInv_fourier_eq hfi hFi
  have h1 := congrFun hinv L
  rw [Real.fourierInv_eq'] at h1
  simp only [hF, smul_eq_mul] at h1
  have h2 : ∫ w : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ w L) * Complex.I) *
      bumpLaplace g ((c : ℂ) * (((w * R : ℝ) : ℂ) * Complex.I)) =
      ∫ w : ℝ, (fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace g ((c : ℂ) * ((τ : ℂ) * Complex.I))) (w * R) := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only []
    congr 2
    rw [hR]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    field_simp
  rw [h2, Measure.integral_comp_mul_right (fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace g ((c : ℂ) * ((τ : ℂ) * Complex.I))) R] at h1
  have hRinv : |R⁻¹| = c / (2 * Real.pi) := by
    rw [hR, inv_div, abs_of_pos (by positivity)]
  rw [hRinv] at h1
  refine Eq.trans ?_ h1
  simp [Complex.real_smul]

variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

theorem tau_pow_inversion (h : BumpProfile b δ M α β K B) (hb : 0 < b) (hδ : 0 < δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β)
    {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hint : Integrable fun τ : ℝ => (τ : ℂ) ^ k * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) (L : ℝ) :
    ∫ τ : ℝ, (τ : ℂ) ^ k * (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
      bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) =
      ((2 * Real.pi / c : ℝ) : ℂ) * (Complex.I ^ k * (c : ℂ) ^ k)⁻¹ * ((iteratedDeriv k B L : ℝ) : ℂ) := by
  have hb0 : 0 ≤ b * δ := by positivity
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set Bk : ℝ → ℝ := iteratedDeriv k B with hBk
  have hlap : ∀ τ : ℝ, bumpLaplace Bk ((c : ℂ) * ((τ : ℂ) * Complex.I)) =
      ((c : ℂ) * ((τ : ℂ) * Complex.I)) ^ k * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
    intro τ
    unfold bumpLaplace
    exact BumpProfile.laplace_pow h hb0 hbδ hβ (by simp) k
  have hfi : Integrable fun x : ℝ => (Bk x : ℂ) := (h.integrable_iteratedDeriv hbδ hβ k).ofReal
  have hfc : Continuous Bk := (h.contDiff_iteratedDeriv k).continuous
  have hint' : Integrable fun τ : ℝ => bumpLaplace Bk ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
    have := hint.const_mul (((c : ℂ) * Complex.I) ^ k)
    refine this.congr (ae_of_all _ fun τ => ?_)
    simp only [hlap]; rw [mul_pow, mul_pow]; ring
  have hinv := fourier_inversion_general hfi hfc hc hint' L
  simp only [hlap] at hinv
  have e : ∫ τ : ℝ, Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        (((c : ℂ) * ((τ : ℂ) * Complex.I)) ^ k * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) =
      ((c : ℂ) * Complex.I) ^ k * ∫ τ : ℝ, (τ : ℂ) ^ k * (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    show _ = _
    simp only []
    rw [mul_pow, mul_pow]; ring
  rw [e] at hinv
  have hI : Complex.I ^ k * (c : ℂ) ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (pow_ne_zero _ hcC)
  have hcpi : ((c / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : c / (2 * Real.pi) ≠ 0 := by positivity
    exact_mod_cast this
  have h2 : ((c / (2 * Real.pi) : ℝ) : ℂ) * (((c : ℂ) * Complex.I) ^ k * ∫ τ : ℝ, (τ : ℂ) ^ k *
      (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)))) = (Bk L : ℂ) := hinv
  set J := ∫ τ : ℝ, (τ : ℂ) ^ k * (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
      bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) with hJ
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← h2]
  push_cast
  rw [mul_pow]
  field_simp

/-- info: 'FormalResearch.SignUncertainty.fourier_inversion_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_inversion_general

/-- info: 'FormalResearch.SignUncertainty.tau_pow_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tau_pow_inversion

end FormalResearch.SignUncertainty
