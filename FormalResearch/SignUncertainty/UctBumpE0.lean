module

public import FormalResearch.SignUncertainty.UctBumpMain
public import FormalResearch.SignUncertainty.UctBumpReflAmp

/-!
# `uct:bump-symbol`: the exact Fourier identity `(uct:E0-def)` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:bump-symbol`, equation `(uct:E0-def)`:
`Δh_main(L) - c⁻¹ B(L) = (1/2π) ∫ E₀(τ) e^{icLτ} B̂(icτ) dτ`, `E₀(τ) = (1-iτ)^{-1/2} e^{B_c(iτ)} e^{-ic∫₀^τ m} - 1`
(`m = -ℓ`, `bumpE0 c τ = kernelAmp c τ - 1`; `bumpE0_explicit` matches the displayed formula).

`bump_fourier_inversion` is the exact Fourier inversion `(c/2π) ∫ e^{icLτ} B̂(icτ) dτ = B(L)` for a bump profile (`Mathlib` `Continuous.fourierInv_fourier_eq`);
`bump_E0_identity` is `(uct:E0-def)`.

Class: proved, no hypotheses beyond the `BumpProfile` ones.
-/

@[expose] public section

open MeasureTheory Set Filter Topology FourierTransform
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma fourier_bump_eq (B : ℝ → ℝ) (w : ℝ) :
    𝓕 (fun x : ℝ => (B x : ℂ)) w = bumpLaplace B (Complex.I * ((2 * Real.pi * w : ℝ) : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold bumpLaplace
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem bump_fourier_inversion (h : BumpProfile b δ M α β K B) (hbδ : b * δ ≤ 1) (hβ : 1 < β) {c : ℝ} (hc : 0 < c)
    (hint : Integrable fun τ : ℝ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) (L : ℝ) :
    ((c / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
      bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) = (B L : ℂ) := by
  set f : ℝ → ℂ := fun x => (B x : ℂ) with hf
  have hfi : Integrable f := by
    have := (h.integrable_iteratedDeriv hbδ hβ 0).ofReal (𝕜 := ℂ)
    simpa [iteratedDeriv_zero] using this
  have hfc : Continuous f := Complex.continuous_ofReal.comp h.smooth.continuous
  set R : ℝ := 2 * Real.pi / c with hR
  have hR0 : R ≠ 0 := by positivity
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hF : ∀ w : ℝ, 𝓕 f w = bumpLaplace B ((c : ℂ) * (((w * R : ℝ) : ℂ) * Complex.I)) := by
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
  have hinv := hfc.fourierInv_fourier_eq hfi hFi
  have h1 := congrFun hinv L
  rw [Real.fourierInv_eq'] at h1
  simp only [hF, smul_eq_mul] at h1
  have h2 : ∫ w : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ w L) * Complex.I) *
      bumpLaplace B ((c : ℂ) * (((w * R : ℝ) : ℂ) * Complex.I)) =
      ∫ w : ℝ, (fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) (w * R) := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only []
    congr 2
    rw [hR]
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    field_simp
  rw [h2, Measure.integral_comp_mul_right (fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) R] at h1
  have hRinv : |R⁻¹| = c / (2 * Real.pi) := by
    rw [hR, inv_div, abs_of_pos (by positivity)]
  rw [hRinv] at h1
  refine Eq.trans ?_ h1
  simp [Complex.real_smul]

/-- `E₀(τ) = (1-iτ)^{-1/2} e^{B_c(iτ)} e^{-ic∫₀^τ m} - 1` with `m = -ℓ`, i.e. `kernelAmp c τ - 1`. -/
noncomputable def bumpE0 (c τ : ℝ) : ℂ := kernelAmp c τ - 1

lemma bumpE0_explicit (c τ : ℝ) :
    bumpE0 c τ = (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
      Complex.exp (-(Complex.I * ((c * ∫ u in (0 : ℝ)..τ, -ellFun u : ℝ) : ℂ))) - 1 := by
  unfold bumpE0 kernelAmp cpowI ellN
  have : (∫ u in (0 : ℝ)..τ, -ellFun u) = -∫ u in (0 : ℝ)..τ, ellFun u := intervalIntegral.integral_neg
  rw [this]
  congr 2
  · congr 2; ring
  · congr 1; push_cast; ring

theorem bump_laplace_integrable (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) :
    ∀ (B : ℝ → ℝ) (δ M c : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 0 < c → BumpProfile b δ M α β K B →
      Integrable fun τ : ℝ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, hdec⟩ := bump_laplace_decay (α := α) hb hβ K 2
  intro B δ M c hδ0 hδ1 hbδ hM hc h
  have ha0 : 0 < c * δ := mul_pos hc hδ0
  obtain ⟨hint, -⟩ := integral_inv_sq_scaled ha0
  have hcont : Continuous fun τ : ℝ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) :=
    (h.continuousOn_laplace (by positivity) hbδ (by linarith)).comp_continuous (by fun_prop) (fun τ => by simp)
  refine (hint.const_mul (C * M * bumpLambda α δ)).mono' hcont.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
  have := hdec B δ M c 0 τ hδ0 hδ1 hbδ hM hc le_rfl h
  simp only [Complex.ofReal_zero, zero_add, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] at this
  refine this.trans (le_of_eq ?_)
  rw [div_eq_mul_inv]

theorem bump_E0_identity (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) :
    ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 2 ≤ c → 0 < ξ → BumpProfile b δ M α β K B →
      bumpHmain c B ξ - ((c⁻¹ * B (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, bumpE0 c τ *
          Complex.exp (Complex.I * ((c * Real.log (Real.pi ^ 2 * ξ) * τ : ℝ) : ℂ)) *
          bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
  intro B δ M c ξ hδ0 hδ1 hbδ hM hc2 hξ h
  have hc0 : 0 < c := by linarith
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ) with hL
  set Φ : ℝ → ℂ := fun τ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) with hΦ
  have hΦi : Integrable Φ := bump_laplace_integrable (α := α) hb hβ K B δ M c hδ0 hδ1 hbδ hM hc0 h
  have hΦc : Continuous Φ :=
    (h.continuousOn_laplace (by positivity) hbδ (by linarith)).comp_continuous (by fun_prop) (fun τ => by simp)
  obtain ⟨Ca, hCa, haenv⟩ := kernel_amp_env2
  have hkc : Continuous (kernelAmp c) := (haenv c hc2).1.continuous
  have hexpc : Continuous fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) := by fun_prop
  -- integrability of both pieces
  have hi1 : Integrable fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ := by
    refine hΦi.norm.mono' (hexpc.mul hΦc).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hi2 : Integrable fun τ : ℝ => kernelAmp c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ := by
    refine hΦi.norm.mono' ((hkc.mul hexpc).mul hΦc).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    have hk : ‖kernelAmp c τ‖ ≤ 1 := by
      have h1 := norm_mellinK0_imag_le_one hc0 hξ τ
      rw [mellinK0_imag_eq hξ τ, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one] at h1
      exact h1
    rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) hk
  have hinv := bump_fourier_inversion h hbδ (by linarith) hc0 hΦi L
  have hmain : bumpHmain c B ξ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, kernelAmp c τ *
      Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ := by
    unfold bumpHmain bumpDW
    have e : ∀ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) =
        ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (kernelAmp c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ) := by
      intro τ
      rw [mellinK0_imag_eq hξ τ]; ring
    simp_rw [e]
    rw [integral_const_mul, ← mul_assoc]
    congr 1
    have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have hprod : c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hc0]; norm_num
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
    linarith [hprod]
  have hsplit : ∫ τ : ℝ, bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ =
      (∫ τ : ℝ, kernelAmp c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ) -
        ∫ τ : ℝ, Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ := by
    rw [← integral_sub hi2 hi1]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [bumpE0]; ring
  rw [hsplit, hmain, mul_sub]
  congr 1
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ =
      ((c⁻¹ : ℝ) : ℂ) * (((c / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ) := by
    rw [← mul_assoc]; congr 1; push_cast; field_simp
  rw [this, hinv]
  push_cast; ring

/-- info: 'FormalResearch.SignUncertainty.bump_fourier_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_fourier_inversion

/-- info: 'FormalResearch.SignUncertainty.bump_E0_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_E0_identity

/-- info: 'FormalResearch.SignUncertainty.bumpE0_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpE0_explicit

end FormalResearch.SignUncertainty
