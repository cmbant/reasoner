module

public import FormalResearch.SignUncertainty.CtOuterBandAmpMul

/-!
# The factor `exp(g)` with `g' = O((1+τ)^{-2})`, `g'' = O((1+τ)^{-3})`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (`ct:A-derivs`).  **Proved.**
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

/-- `G = exp ∘ g` has `G' = g' G`, `G'' = (g'' + g'²) G`. -/
theorem exp_factor {g g1 g2 : ℝ → ℂ} {r0 Kg : ℝ} (hKg : 0 ≤ Kg)
    (hg : ∀ τ : ℝ, 0 < τ → HasDerivAt g (g1 τ) τ) (hg1 : ∀ τ : ℝ, 0 < τ → HasDerivAt g1 (g2 τ) τ)
    (hg2c : ContinuousOn g2 (Ioi 0)) (hre : ∀ τ : ℝ, 0 < τ → (g τ).re ≤ r0)
    (hb1 : ∀ τ : ℝ, 0 < τ → ‖g1 τ‖ ≤ Kg / (1 + τ) ^ 2) (hb2 : ∀ τ : ℝ, 0 < τ → ‖g2 τ‖ ≤ Kg / (1 + τ) ^ 3) :
    (∀ τ : ℝ, 0 < τ → HasDerivAt (fun τ => Complex.exp (g τ)) (g1 τ * Complex.exp (g τ)) τ) ∧
    (∀ τ : ℝ, 0 < τ → HasDerivAt (fun τ => g1 τ * Complex.exp (g τ)) ((g2 τ + g1 τ * g1 τ) * Complex.exp (g τ)) τ) ∧
    ContinuousOn (fun τ => (g2 τ + g1 τ * g1 τ) * Complex.exp (g τ)) (Ioi 0) ∧
    (∀ τ : ℝ, 0 < τ → ‖Complex.exp (g τ)‖ ≤ Real.exp r0) ∧
    (∀ τ : ℝ, 0 < τ → ‖g1 τ * Complex.exp (g τ)‖ ≤ Kg * Real.exp r0 / (1 + τ) ^ 2) ∧
    (∀ τ : ℝ, 0 < τ → ‖(g2 τ + g1 τ * g1 τ) * Complex.exp (g τ)‖ ≤ (Kg + Kg ^ 2) * Real.exp r0 / (1 + τ) ^ 3) := by
  have hn : ∀ τ : ℝ, 0 < τ → ‖Complex.exp (g τ)‖ ≤ Real.exp r0 := fun τ hτ => by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (hre τ hτ)
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_, ?_, hn, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · exact ((hg τ hτ).cexp).congr_deriv (by ring)
  · have := (hg1 τ hτ).mul ((hg τ hτ).cexp)
    exact this.congr_deriv (by ring)
  · have cg : ContinuousOn g (Ioi 0) := fun τ hτ => (hg τ hτ).continuousAt.continuousWithinAt
    have cg1 : ContinuousOn g1 (Ioi 0) := fun τ hτ => (hg1 τ hτ).continuousAt.continuousWithinAt
    exact (hg2c.add (cg1.mul cg1)).mul (Complex.continuous_exp.comp_continuousOn cg)
  · rw [norm_mul]
    have := mul_le_mul (hb1 τ hτ) (hn τ hτ) (norm_nonneg _) (by positivity)
    calc ‖g1 τ‖ * ‖Complex.exp (g τ)‖ ≤ Kg / (1 + τ) ^ 2 * Real.exp r0 := this
      _ = _ := by ring
  · rw [norm_mul]
    have h1 : ‖g2 τ + g1 τ * g1 τ‖ ≤ (Kg + Kg ^ 2) / (1 + τ) ^ 3 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have a1 := hb2 τ hτ
      have a2 := mul_le_mul (hb1 τ hτ) (hb1 τ hτ) (norm_nonneg _) (by positivity)
      have hD : (1 : ℝ) ≤ 1 + τ := by linarith
      have e : Kg / (1 + τ) ^ 2 * (Kg / (1 + τ) ^ 2) ≤ Kg ^ 2 / (1 + τ) ^ 3 := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (1 + τ) ^ 3 ≤ (1 + τ) ^ 4 := pow_le_pow_right₀ hD (by norm_num)
        nlinarith [sq_nonneg Kg, mul_le_mul_of_nonneg_left this (sq_nonneg Kg)]
      calc ‖g2 τ‖ + ‖g1 τ‖ * ‖g1 τ‖ ≤ Kg / (1 + τ) ^ 3 + Kg ^ 2 / (1 + τ) ^ 3 := add_le_add a1 (a2.trans e)
        _ = _ := by ring
    have := mul_le_mul h1 (hn τ hτ) (norm_nonneg _) (by positivity)
    calc ‖g2 τ + g1 τ * g1 τ‖ * ‖Complex.exp (g τ)‖ ≤ (Kg + Kg ^ 2) / (1 + τ) ^ 3 * Real.exp r0 := this
      _ = _ := by ring

end FormalResearch.SignUncertainty.CtOsc
