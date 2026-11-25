module

public import FormalResearch.SignUncertainty.CtOuterG3Ibp
public import FormalResearch.SignUncertainty.CtOuterTheta1

/-!
# `θ_3^± = ½ζ(3) + c_{3,mp} (+ π³/6)`: the cubic Taylor coefficient of `ct:outer` (2)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2) (`ct:theta3`).  **Proved.**

`θ_ε'''(0) = -Re H₀'''(0) + 2 + [ε = 1]π³` (`iteratedDeriv_three_outerTheta`),
`H₀'''(0) = -∫_ℝ (u_r'' - u_r''(0)) π cosh/sinh²` (`deriv3_H0_zero_uR`, two integrations by parts on the strip,
dominated convergence at the fold), the splitting `u_r'' - u_r''(0) = ½(L'' + 7π²/30) + g` with
`u_r''(0) = -7π²/60 - 1` (`uR2_zero`) and `L = log(m'(t)/t)`, and `(π/3)∫_0^∞ g K̂ + 1/3 = ½ζ(3)`
(`c3_1t2_value`: Mittag-Leffler series, `∑_{k≥2}(-1)^k/k³ = 1 - ¾ζ(3)`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- **`θ_3^ε = θ_ε'''(0)/6 = ½ζ(3) + c_{3,mp} + [ε=1]π³/6`** (`ct:theta3`). -/
theorem theta_three_eq (ε : ℝ) : iteratedDeriv 3 (outerTheta ε) 0 / 6 = ctTheta3 ε := by
  rw [iteratedDeriv_three_outerTheta_P]
  have h1 := ctC3mp_eq
  have h2 := c3_1t2_value
  unfold ctTheta3
  rw [h1]
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]
    linarith only [h2]
  · simp only [h, ↓reduceIte]
    linarith only [h2]

/-- The paper's closed forms for the Taylor coefficients of `θ_ε` at `0` (`ct:theta1`, `ct:theta3`). -/
theorem ctThetaValuesTarget : CtThetaValuesTarget := fun ε hε =>
  ⟨deriv_outerTheta_zero_eq_ctTheta1 hε, theta_three_eq ε⟩

/-- info: 'FormalResearch.SignUncertainty.CtOuter.theta_three_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_three_eq

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ctThetaValuesTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctThetaValuesTarget

end FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- **`ct:outer` (2), unconditional, with the paper's constants:**
`θ_ε(τ) = θ_1^ε τ + θ_3^ε τ³ + O(τ⁵)` with `θ_1^ε = -3 log 2 + I_0 (- π)` and
`θ_3^ε = ½ζ(3) + c_{3,mp} (+ π³/6)` (`CtOuter.ctTheta1`, `CtOuter.ctTheta3`).  This restates
`CtOuter.ct_outer_part2_taylor_values` without its hypothesis. -/
theorem ct_outer_part2_taylor_values {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ 1 →
      |CtOuter.outerTheta ε τ - CtOuter.ctTheta1 ε * τ - CtOuter.ctTheta3 ε * τ ^ 3| ≤ C * |τ| ^ 5 :=
  CtOuter.ct_outer_part2_taylor_values CtOuter.ctThetaValuesTarget hε

/-- info: 'FormalResearch.SignUncertainty.ct_outer_part2_taylor_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part2_taylor_values

end FormalResearch.SignUncertainty
