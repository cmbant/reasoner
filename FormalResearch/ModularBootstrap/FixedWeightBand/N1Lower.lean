module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWInterface

/-!
# The `𝒩 = 1` NS Super-Virasoro Lower Bound

Source: `CFT/modular_bootstrap/paper/n1_super_virasoro.tex`, Theorem 3 (`n1:T3`), the instance
`(w, Q) = (1, (1 - q^{1/2})^2)` of Theorem 5 (`n1:T5`), with `c̃ = c - 3/2`; lower half by Theorem `W1'(1)`
(`lower_o1_two_edge.tex`, `wone:genlower(1)`).

* `n1_lowerBoundInput`: `FixedWeightLowerBoundInput n1SuperVirasoroProblem`, unconditional;
* `n1_T_V_lower`: explicitly, `T_V(c̃) ≥ ξ̄ c̃ + A_opt c̃^{1/3} - D_-` (in the form `T_*(c̃) - D_- ≤ T_V(c̃)`)
  for all `c̃ ≥ c₁`.

Not formalised: the matching upper bound at `𝒩 = 1` (the design side is formalised only for
`virasoroProblem`).
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing FixedWeight

/-- **`𝒩 = 1` NS lower bound** (`n1:T3`, lower half): Theorem `W1'(1)` at
`n1SuperVirasoroProblem` (`w = 1`, `μ = (1/2, 1/2)`), unconditional. -/
theorem n1_lowerBoundInput : FixedWeightLowerBoundInput n1SuperVirasoroProblem :=
  fixedWeightLowerBoundInput_of_problem n1SuperVirasoroProblem

/-- **`𝒩 = 1` NS lower bound, explicit form**: there are `c₁ ≥ 12` and `D_- ≥ 0` with
`T_*(c̃) - D_- ≤ T_V(c̃)` for all `c̃ ≥ c₁` (`c̃ = c - 3/2`, total null shift `1`). -/
theorem n1_T_V_lower :
    ∃ c₁ D_minus : ℝ, 12 ≤ c₁ ∧ 0 ≤ D_minus ∧
      ∀ {cTilde : ℝ}, c₁ ≤ cTilde → TStar cTilde - D_minus ≤ n1SuperVirasoroProblem.T_V cTilde := by
  obtain ⟨c₁, D, hc₁, hD, h⟩ := n1_lowerBoundInput
  rw [n1SuperVirasoroProblem_totalShift] at hc₁
  exact ⟨c₁, D, le_trans (by norm_num) hc₁, hD, h⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.n1_lowerBoundInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_lowerBoundInput

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.n1_T_V_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_T_V_lower

end FormalResearch.ModularBootstrap.FixedWeightBand
