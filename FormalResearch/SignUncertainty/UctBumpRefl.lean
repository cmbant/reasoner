module

public import FormalResearch.SignUncertainty.UctBumpReflB
public import FormalResearch.SignUncertainty.UctBumpReflAmp
public import FormalResearch.SignUncertainty.UctFourierTwice

/-!
# `uct:bump-symbol`: the reflected-density bound (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:bump-symbol`: "the reflected density, for every `L`, by
`C M (cδ)^{-1} Λ_α(δ) e^{-bcδ/2} min(1, L_+^{-2})`".

`bumpHrefl c B ξ = (c^{1/3}/2π) ∫ K₀(iτ,ξ) ΔW_c(1-iτ) dτ` (`Δh_refl`, `ξ = e^L/π²`).  `bump_refl_density` (for `c ≥ 2`, `cδ ≥ 1`):
the bound `C M (cδ)^{-1} Λ e^{-bcδ/2}` for every `L` (absolute estimate: `|K₀(iτ)| ≤ 1`), and, for `L = log(π²ξ) ≥ 1`, the same with an extra factor
`L^{-2}` (two integrations by parts against `e^{icLτ}`, `env2_fourier_decay`, with the amplitude envelope `kernel_amp_env2` and the envelope
`bump_refl_env2` of `B̂(c(1-iτ))`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `Δh_refl(L) = (c^{1/3}/2π) ∫ K₀(iτ,ξ) ΔW_c(1 - iτ) dτ`. -/
noncomputable def bumpHrefl (c : ℝ) (B : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B (1 - (τ : ℂ) * Complex.I)

lemma sq_exp_le {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) : (1 + x) ^ 2 * Real.exp (-(b * x / 4)) ≤ 2 + 64 / b ^ 2 := by
  set y : ℝ := b * x / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have h2 : y ^ 2 / 2 ≤ Real.exp y := by
    have := Real.pow_div_factorial_le_exp y hy0 2
    simpa [Nat.factorial] using this
  have hx' : x = 4 * y / b := by rw [hy]; field_simp
  have hE : 0 < Real.exp y := Real.exp_pos y
  have e1 : y ^ 2 * Real.exp (-y) ≤ 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]; nlinarith
  have e2 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have e3 : (1 + x) ^ 2 ≤ 2 + 2 * x ^ 2 := by nlinarith [sq_nonneg (1 - x)]
  have e4 : x ^ 2 = 16 * y ^ 2 / b ^ 2 := by rw [hx']; field_simp; ring
  have hb2 : 0 < b ^ 2 := by positivity
  calc (1 + x) ^ 2 * Real.exp (-(b * x / 4)) ≤ (2 + 2 * x ^ 2) * Real.exp (-y) := by
        rw [← hy]; exact mul_le_mul_of_nonneg_right e3 (Real.exp_pos _).le
    _ = 2 * Real.exp (-y) + 32 / b ^ 2 * (y ^ 2 * Real.exp (-y)) := by rw [e4]; ring
    _ ≤ 2 * 1 + 32 / b ^ 2 * 2 := by
        have : 0 ≤ 32 / b ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left e1 this]
    _ = 2 + 64 / b ^ 2 := by ring

set_option maxHeartbeats 1000000 in
theorem bump_refl_density {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 2 ≤ c → 1 ≤ c * δ → 0 < ξ →
      BumpProfile b δ M α β K B →
        ‖bumpHrefl c B ξ‖ ≤ C * M * (c * δ)⁻¹ * bumpLambda α δ * Real.exp (-(b * c * δ / 2)) ∧
        (1 ≤ Real.log (Real.pi ^ 2 * ξ) → ‖bumpHrefl c B ξ‖ ≤
          C * M * (c * δ)⁻¹ * bumpLambda α δ * Real.exp (-(b * c * δ / 2)) / Real.log (Real.pi ^ 2 * ξ) ^ 2) := by
  obtain ⟨Cb, hCb, hbenv⟩ := bump_refl_env2 (α := α) hb hβ K
  obtain ⟨Ca, hCa, haenv⟩ := kernel_amp_env2
  set I2 : ℝ := ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ with hI2
  have hI2n : 0 ≤ I2 := integral_nonneg fun x => by positivity
  set X : ℝ := 2 + 64 / b ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨(1 / (2 * Real.pi)) * I2 * X * Cb * (1 + 16 * Ca), by positivity,
    fun B δ M c ξ hδ0 hδ1 hbδ hM hc2 ha1 hξ h => ?_⟩
  have hc0 : 0 < c := by linarith
  set a : ℝ := c * δ with ha
  have ha0 : 0 < a := mul_pos hc0 hδ0
  have hbe := hbenv B δ M c hδ0 hδ1 hbδ hM hc0 h
  have hΛ : 1 ≤ bumpLambda α δ := one_le_bumpLambda (α := α) hδ0 hδ1
  have hΛ0 : 0 ≤ bumpLambda α δ := by linarith
  -- the exponential absorption: (1+a)² e^{-3ba/4} ≤ X e^{-ba/2}
  have hexp : (1 + a) ^ 2 * Real.exp (-(3 / 4 * b * c * δ)) ≤ X * Real.exp (-(b * c * δ / 2)) := by
    have h1 := sq_exp_le hb ha0.le
    have e : Real.exp (-(3 / 4 * b * c * δ)) = Real.exp (-(b * a / 4)) * Real.exp (-(b * c * δ / 2)) := by
      rw [← Real.exp_add]; congr 1; rw [ha]; ring
    rw [e]
    calc (1 + a) ^ 2 * (Real.exp (-(b * a / 4)) * Real.exp (-(b * c * δ / 2)))
        = ((1 + a) ^ 2 * Real.exp (-(b * a / 4))) * Real.exp (-(b * c * δ / 2)) := by ring
      _ ≤ X * Real.exp (-(b * c * δ / 2)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  -- Q: the constant in the envelope of B̂
  set Qb : ℝ := Cb * M * bumpLambda α δ * ((1 + a) ^ 2 * Real.exp (-(3 / 4 * b * c * δ))) with hQb
  have hQb0 : 0 ≤ Qb := by positivity
  have hQbX : Qb ≤ Cb * M * bumpLambda α δ * (X * Real.exp (-(b * c * δ / 2))) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have hQeq : ∀ τ : ℝ, Cb * M * bumpLambda α δ * (1 + c * δ) ^ 2 * Real.exp (-(3 / 4 * b * c * δ)) / (1 + c * δ * |τ|) ^ 6 =
      Qb * ((1 + a * |τ|) ^ 6)⁻¹ := by
    intro τ; rw [hQb, ha]; ring
  have hbenv' : ∀ τ : ℝ, ‖bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ)))‖ ≤ Qb * ((1 + a * |τ|) ^ 2)⁻¹ := by
    intro τ
    have h62 : ((1 + a * |τ|) ^ 6)⁻¹ ≤ ((1 + a * |τ|) ^ 2)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ (by nlinarith [mul_nonneg ha0.le (abs_nonneg τ)]) (by norm_num)
    calc ‖bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ)))‖
        ≤ Cb * M * bumpLambda α δ * (1 + c * δ) ^ 2 * Real.exp (-(3 / 4 * b * c * δ)) / (1 + c * δ * |τ|) ^ 6 := (hbe.2 τ).1
      _ = Qb * ((1 + a * |τ|) ^ 6)⁻¹ := hQeq τ
      _ ≤ Qb * ((1 + a * |τ|) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h62 hQb0
  obtain ⟨hint, hval⟩ := integral_inv_sq_scaled ha0
  -- rewriting of the integrand
  have hint_eq : ∀ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B (1 - (τ : ℂ) * Complex.I) =
      ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))) *
        Complex.exp (Complex.I * ((c * Real.log (Real.pi ^ 2 * ξ) * τ : ℝ) : ℂ))) := by
    intro τ
    rw [mellinK0_imag_eq hξ τ]
    unfold bumpDW
    rw [show (1 : ℂ) - (τ : ℂ) * Complex.I = 1 + (-Complex.I) * (τ : ℂ) by ring]
    ring
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hprod : c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hc0]; norm_num
  have hfac : ‖((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ)‖ * ‖((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
      abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    field_simp
    nlinarith [hprod]
  have hkey : ‖bumpHrefl c B ξ‖ = (1 / (2 * Real.pi)) * ‖∫ τ : ℝ, kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))) *
        Complex.exp (Complex.I * ((c * Real.log (Real.pi ^ 2 * ξ) * τ : ℝ) : ℂ))‖ := by
    unfold bumpHrefl
    simp_rw [hint_eq]
    rw [integral_const_mul, ← mul_assoc, norm_mul, norm_mul, hfac]
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have hfinal : (1 / (2 * Real.pi)) * I2 * X * Cb * (1 + 16 * Ca) * M * a⁻¹ * bumpLambda α δ * Real.exp (-(b * c * δ / 2)) =
      (1 / (2 * Real.pi)) * (Cb * M * bumpLambda α δ * (X * Real.exp (-(b * c * δ / 2)))) * (I2 / a) * (1 + 16 * Ca) := by
    have han : a ≠ 0 := ha0.ne'
    field_simp
  refine ⟨?_, fun hL => ?_⟩
  · -- absolute bound
    have habs : ‖∫ τ : ℝ, kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))) *
        Complex.exp (Complex.I * ((c * Real.log (Real.pi ^ 2 * ξ) * τ : ℝ) : ℂ))‖ ≤ ∫ τ : ℝ, Qb * ((1 + a * |τ|) ^ 2)⁻¹ := by
      refine norm_integral_le_of_norm_le (hint.const_mul Qb) (ae_of_all _ fun τ => ?_)
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      have hk : ‖kernelAmp c τ‖ ≤ 1 := by
        have h1 := norm_mellinK0_imag_le_one hc0 hξ τ
        rw [mellinK0_imag_eq hξ τ, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one] at h1
        exact h1
      calc ‖kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ)))‖ = ‖kernelAmp c τ‖ * ‖bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ)))‖ := norm_mul _ _
        _ ≤ 1 * (Qb * ((1 + a * |τ|) ^ 2)⁻¹) := mul_le_mul hk (hbenv' τ) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    rw [hkey]
    rw [integral_const_mul, hval] at habs
    calc (1 / (2 * Real.pi)) * ‖∫ τ : ℝ, kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))) *
          Complex.exp (Complex.I * ((c * Real.log (Real.pi ^ 2 * ξ) * τ : ℝ) : ℂ))‖
        ≤ (1 / (2 * Real.pi)) * (Qb * (I2 / a)) := mul_le_mul_of_nonneg_left habs hpi.le
      _ ≤ (1 / (2 * Real.pi)) * ((Cb * M * bumpLambda α δ * (X * Real.exp (-(b * c * δ / 2)))) * (I2 / a)) := by
          gcongr
      _ ≤ _ := by
          have : (1 / (2 * Real.pi)) * ((Cb * M * bumpLambda α δ * (X * Real.exp (-(b * c * δ / 2)))) * (I2 / a)) ≤
              (1 / (2 * Real.pi)) * ((Cb * M * bumpLambda α δ * (X * Real.exp (-(b * c * δ / 2)))) * (I2 / a)) * (1 + 16 * Ca) := by
            have h0 : 0 ≤ (1 / (2 * Real.pi)) * ((Cb * M * bumpLambda α δ * (X * Real.exp (-(b * c * δ / 2)))) * (I2 / a)) := by positivity
            nlinarith [mul_nonneg h0 hCa]
          refine this.trans (le_of_eq ?_)
          have han : a ≠ 0 := ha0.ne'
          field_simp
  · set Ls : ℝ := Real.log (Real.pi ^ 2 * ξ) with hLs
    have hL0 : 0 < Ls := by linarith
    have han : a ≠ 0 := ha0.ne'
    have hca : 1 ≤ a := ha1
    have hkenv := haenv c hc2
    have hfenv := hkenv.mul hbe
    have hPle : ∀ τ : ℝ, 4 * (Ca * (1 + c) ^ 2 * (1 + |τ|) ^ 4) *
        (Cb * M * bumpLambda α δ * (1 + c * δ) ^ 2 * Real.exp (-(3 / 4 * b * c * δ)) / (1 + c * δ * |τ|) ^ 6) ≤
        (16 * Ca * c ^ 2 * Qb) * ((1 + a * |τ|) ^ 2)⁻¹ := by
      intro τ
      rw [hQeq τ]
      have hu : 0 < 1 + |τ| := by positivity
      have hv : 0 < 1 + a * |τ| := by positivity
      have huv : 1 + |τ| ≤ 1 + a * |τ| := by nlinarith [abs_nonneg τ]
      have h4 : (1 + |τ|) ^ 4 * ((1 + a * |τ|) ^ 6)⁻¹ ≤ ((1 + a * |τ|) ^ 2)⁻¹ := by
        calc (1 + |τ|) ^ 4 * ((1 + a * |τ|) ^ 6)⁻¹ ≤ (1 + a * |τ|) ^ 4 * ((1 + a * |τ|) ^ 6)⁻¹ := by
              gcongr
          _ = ((1 + a * |τ|) ^ 2)⁻¹ := by field_simp
      have hc1 : (1 + c) ^ 2 ≤ 4 * c ^ 2 := by nlinarith
      have hpos : 0 ≤ 4 * Ca * Qb := by positivity
      calc 4 * (Ca * (1 + c) ^ 2 * (1 + |τ|) ^ 4) * (Qb * ((1 + a * |τ|) ^ 6)⁻¹)
          = (4 * Ca * Qb * (1 + c) ^ 2) * ((1 + |τ|) ^ 4 * ((1 + a * |τ|) ^ 6)⁻¹) := by ring
        _ ≤ (4 * Ca * Qb * (1 + c) ^ 2) * ((1 + a * |τ|) ^ 2)⁻¹ := by gcongr
        _ ≤ (4 * Ca * Qb * (4 * c ^ 2)) * ((1 + a * |τ|) ^ 2)⁻¹ := by gcongr
        _ = (16 * Ca * c ^ 2 * Qb) * ((1 + a * |τ|) ^ 2)⁻¹ := by ring
    have hfenv' : Env2 (fun τ : ℝ => kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))))
        (fun τ : ℝ => (16 * Ca * c ^ 2 * Qb) * ((1 + a * |τ|) ^ 2)⁻¹) :=
      hfenv.mono hPle
    have hω : c * Ls ≠ 0 := by positivity
    have hfd : ‖∫ τ : ℝ, kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))) *
        Complex.exp (Complex.I * ((c * Ls * τ : ℝ) : ℂ))‖ ≤
        (∫ τ : ℝ, (16 * Ca * c ^ 2 * Qb) * ((1 + a * |τ|) ^ 2)⁻¹) / (c * Ls) ^ 2 :=
      env2_fourier_decay hfenv' (hint.const_mul _) hω
    rw [integral_const_mul, hval] at hfd
    rw [hkey]
    set T : ℝ := Cb * M * bumpLambda α δ * (X * Real.exp (-(b * c * δ / 2))) with hT
    have hT0 : 0 ≤ T := by positivity
    have hc0' : c ≠ 0 := hc0.ne'
    calc (1 / (2 * Real.pi)) * ‖∫ τ : ℝ, kernelAmp c τ * bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))) *
          Complex.exp (Complex.I * ((c * Ls * τ : ℝ) : ℂ))‖
        ≤ (1 / (2 * Real.pi)) * ((16 * Ca * c ^ 2 * Qb * (I2 / a)) / (c * Ls) ^ 2) :=
          mul_le_mul_of_nonneg_left hfd hpi.le
      _ ≤ (1 / (2 * Real.pi)) * ((16 * Ca * c ^ 2 * T * (I2 / a)) / (c * Ls) ^ 2) := by
          gcongr
      _ = (1 / (2 * Real.pi)) * (T * (I2 / a)) * (16 * Ca) / Ls ^ 2 := by
          field_simp
      _ ≤ (1 / (2 * Real.pi)) * (T * (I2 / a)) * (1 + 16 * Ca) / Ls ^ 2 := by
          have h0 : 0 ≤ (1 / (2 * Real.pi)) * (T * (I2 / a)) := by positivity
          gcongr
          linarith
      _ = _ := by field_simp; rw [hT]; ring

/-- info: 'FormalResearch.SignUncertainty.bump_refl_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_refl_density

end FormalResearch.SignUncertainty
