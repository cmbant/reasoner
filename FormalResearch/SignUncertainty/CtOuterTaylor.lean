module

public import FormalResearch.SignUncertainty.CtOuterDeriv
public import FormalResearch.SignUncertainty.CtOuterOddTaylor

/-!
# `ct:outer` (2): Taylor expansion of `θ_ε` at `0`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2) ("`θ_ε(τ) = θ_1^ε τ + θ_3^ε τ³ + O(τ⁵)`").

**Proved here:** `θ_ε` is odd and `C^∞`, so `θ_ε(τ) = θ'_ε(0) τ + (θ'''_ε(0)/6) τ³ + O(τ⁵)` for `|τ| ≤ 1`
(`outerTheta_taylor`), and the linear coefficient is
`θ'_-(0) = 2π ∫_0^∞ u_r(t) cosh(πt)/sinh²(πt) dt - 1`, `θ'_+(0) = θ'_-(0) - π` (`deriv_outerTheta_zero`).

**Not proved here:** the closed forms `θ_1^- = -3 log 2 + I_0` (evaluation of the integral above) and `θ_3^±`
(see the report).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma hasDerivAt_arctan_tanh_zero :
    HasDerivAt (fun τ : ℝ => Real.arctan (Real.tanh (π * τ / 2))) (π / 2) 0 := by
  have h1 : HasDerivAt (fun τ : ℝ => π * τ / 2) (π / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul π).div_const 2
  have h2 : HasDerivAt Real.tanh 1 (π * 0 / 2) := by
    have h := (Real.hasDerivAt_sinh (π * 0 / 2)).div (Real.hasDerivAt_cosh (π * 0 / 2))
      (Real.cosh_pos _).ne'
    have e : Real.sinh / Real.cosh = Real.tanh := by ext x; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
    rw [e] at h
    convert h using 1
    simp
  have h3 := HasDerivAt.comp (0 : ℝ) h2 h1
  have h4 : HasDerivAt Real.arctan 1 (Real.tanh (π * 0 / 2)) := by
    have := Real.hasDerivAt_arctan (Real.tanh (π * 0 / 2))
    simpa using this
  have h5 := HasDerivAt.comp (0 : ℝ) h4 h3
  have h6 : (fun τ : ℝ => Real.arctan (Real.tanh (π * τ / 2))) =
      Real.arctan ∘ Real.tanh ∘ (fun τ : ℝ => π * τ / 2) := rfl
  rw [h6]
  simpa using h5

/-- **`ct:outer` (2): the linear Taylor coefficient.** -/
theorem deriv_outerTheta_zero (ε : ℝ) :
    deriv (outerTheta ε) 0 = (deriv H0 0).re - 1 - (if ε = 1 then π else 0) := by
  have hH : HasDerivAt H0 (deriv H0 0) ((0 : ℝ) : ℂ) := by
    have := (differentiableOn_H0.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))).hasDerivAt
    simpa using this
  have hl : HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I ((0 : ℝ) : ℂ) := by
    simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul Complex.I
  have hH' : HasDerivAt H0 (deriv H0 0) (Complex.I * ((0 : ℝ) : ℂ)) := by simpa using hH
  have h0 : HasDerivAt (fun z : ℂ => H0 (Complex.I * z)) (deriv H0 0 * Complex.I) ((0 : ℝ) : ℂ) :=
    HasDerivAt.comp ((0 : ℝ) : ℂ) hH' hl
  have h1 : HasDerivAt (fun τ : ℝ => H0 (Complex.I * (τ : ℂ))) (deriv H0 0 * Complex.I) 0 := h0.comp_ofReal
  have h2 : HasDerivAt (fun τ : ℝ => (H0 (Complex.I * (τ : ℂ))).im) ((deriv H0 0 * Complex.I).im) 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun τ : ℝ => Real.arctan τ) 1 0 := by
    simpa using Real.hasDerivAt_arctan (0 : ℝ)
  have h4 := hasDerivAt_arctan_tanh_zero
  have hev : outerTheta ε =ᶠ[𝓝 (0 : ℝ)] fun τ : ℝ => (H0 (Complex.I * (τ : ℂ))).im - Real.arctan τ -
      (if ε = 1 then 2 * Real.arctan (Real.tanh (π * τ / 2)) else 0) := by
    have hnb : ∀ᶠ τ : ℝ in 𝓝 0, |τ| < 1 / 2 := by
      have := Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)
      filter_upwards [this] with τ hτ using by simpa [Real.dist_eq] using hτ
    filter_upwards [hnb] with τ hτ
    have hn : ‖Complex.I * (τ : ℂ)‖ < 1 / 2 := by simpa [norm_mul] using hτ
    have hb : Complex.I * (τ : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_zero_iff.mpr hn
    have hcl : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
    unfold outerTheta
    rw [outerHbar_eq_H0 hcl hb]
  have hre : (deriv H0 0 * Complex.I).im = (deriv H0 0).re := by simp
  by_cases hε : ε = 1
  · have h5 : HasDerivAt (fun τ : ℝ => (H0 (Complex.I * (τ : ℂ))).im - Real.arctan τ -
        2 * Real.arctan (Real.tanh (π * τ / 2))) ((deriv H0 0).re - 1 - 2 * (π / 2)) 0 := by
      rw [← hre]; exact (h2.sub h3).sub (h4.const_mul 2)
    simp only [hε, ↓reduceIte]
    simp only [hε, ↓reduceIte] at hev
    rw [(h5.congr_of_eventuallyEq hev).deriv]; ring
  · have h5 : HasDerivAt (fun τ : ℝ => (H0 (Complex.I * (τ : ℂ))).im - Real.arctan τ - 0)
        ((deriv H0 0).re - 1 - 0) 0 := by
      rw [← hre]; exact (h2.sub h3).sub (hasDerivAt_const _ _)
    simp only [hε, ↓reduceIte]
    simp only [hε, ↓reduceIte] at hev
    rw [(h5.congr_of_eventuallyEq hev).deriv]

/-- **`ct:outer` (2): Taylor expansion of `θ_ε` to order `τ⁵`** (odd `C^∞`): with `θ_1^ε = θ_ε'(0)` and
`θ_3^ε = θ_ε'''(0)/6`, `|θ_ε(τ) - θ_1^ε τ - θ_3^ε τ³| ≤ C |τ|⁵` for `|τ| ≤ 1`. -/
theorem outerTheta_taylor (ε : ℝ) :
    ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ 1 →
      |outerTheta ε τ - deriv (outerTheta ε) 0 * τ - iteratedDeriv 3 (outerTheta ε) 0 / 6 * τ ^ 3| ≤ C * |τ| ^ 5 :=
  odd_taylor5 (contDiff_outerTheta ε) (outerTheta_neg ε)

end FormalResearch.SignUncertainty.CtOuter
