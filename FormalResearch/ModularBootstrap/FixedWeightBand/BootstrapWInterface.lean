module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWYV
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure

/-!
# Theorem `W1'(1)` / Theorem `J` at Every Fixed `(w, Q)`: `FixedWeightLowerBoundInput prob`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Theorem
`W1'(1)` (`wone:genlower`), Theorem `J` (`vlo:J`).

* `LemmaQData.theoremJ_T_V_W`: `T_*(c̃) - C ≤ T_V(c̃)` for `c̃ ≥ c₂` from `YVInputForW prob b`
  (`b ≤ b_V`), through `T_weak ≤ T_V` (the Virasoro `theoremJ_T_VFor`);
* `fixedWeightLowerBoundInput_of_YVForW`: the consumer interface `FixedWeightLowerBoundInput prob`;
* `fixedWeightLowerBoundInput_of_problem`: unconditional for every `prob : FixedWeightProblem`, with
  the band-feedback input supplied by Proposition `Y_V` (`proposition_YV_W`), Lemma `D'` and Lemma `Z`
  at weight `w` (`lemma_Z_W_band`) and the scale choice `LemmaQData.bvChoice`.

Not formalised here: `corollary_E1` needs an upper bound (Theorem C15) as well.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing FixedWeightTip ConcreteBootstrap FixedWeight

variable {prob : FixedWeightProblem}

/-- **Theorem `J` for `T_V` at weight `w`** from the band-feedback input at a scale `0 < b ≤ b_V`. -/
theorem LemmaQData.theoremJ_T_V_W (Q : LemmaQData prob) {b : ℝ} (hb_pos : 0 < b)
    (hb_le : b ≤ Q.bV) (hYV : YVInputForW prob b) :
    ∃ c_2 C : ℝ, Q.cQ ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' → TStar c' - C ≤ prob.T_V c' := by
  obtain ⟨c_2, C, hc2, hC, hft⟩ := theoremFTLFW_W_of_YVFor Q hb_pos hb_le hYV
  refine ⟨c_2, C, hc2, hC, fun {c'} hc' => ?_⟩
  have hsh : 12 * prob.totalShift ≤ c' := by
    have := Q.hcQ_shift
    linarith [hc2.trans hc']
  have hne : {T : ℝ | 0 < T ∧ ∃ g, prob.IsWeaklyFeasible (c' / 12) T g}.Nonempty := by
    obtain ⟨T, hT_pos, g, hg⟩ := prob.feasible_nonempty hsh
    exact ⟨T, hT_pos, g, hg.isWeaklyFeasible⟩
  have hweak : TStar c' - C ≤ prob.T_weak c' := by
    refine le_csInf hne ?_
    rintro T ⟨_, g, hg⟩
    have := hft hc' hg
    unfold TStar
    simpa using this
  exact hweak.trans (prob.T_weak_le_T_V hsh)

/-- **Theorem `W1'(1)`** (`FixedWeightLowerBoundInput prob`) from the band-feedback input at a scale
`0 < b ≤ b_V`. -/
theorem LemmaQData.fixedWeightLowerBoundInput_of_YVForW (Q : LemmaQData prob) {b : ℝ}
    (hb_pos : 0 < b) (hb_le : b ≤ Q.bV) (hYV : YVInputForW prob b) :
    FixedWeightLowerBoundInput prob := by
  obtain ⟨c_2, C, hc2, hC, hTV⟩ := Q.theoremJ_T_V_W hb_pos hb_le hYV
  refine ⟨c_2, C, ?_, hC, fun {c'} hc' => hTV hc'⟩
  have h1 := Q.hcQ_10000
  have h2 := Q.hcQ_shift
  exact max_le (by linarith) (by linarith)

/-- **Theorem `W1'(1)` / Theorem `J` at every fixed `(w, Q)`, unconditional**
(`lower_o1_two_edge.tex`, `wone:genlower(1)`, `vlo:J`): `T_V(c̃) ≥ ξ̄ c̃ + A_opt c̃^{1/3} - D_-` for all
`c̃ ≥ c₁`. -/
theorem fixedWeightLowerBoundInput_of_problem (prob : FixedWeightProblem) :
    FixedWeightLowerBoundInput prob := by
  obtain ⟨Q⟩ := LemmaQData.nonempty prob
  exact Q.fixedWeightLowerBoundInput_of_YVForW Q.bvChoice_pos Q.bvChoice_le Q.yvInputForW_bvChoice

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.fixedWeightLowerBoundInput_of_problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeightLowerBoundInput_of_problem

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.theoremJ_T_V_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.theoremJ_T_V_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.fixedWeightLowerBoundInput_of_YVForW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.fixedWeightLowerBoundInput_of_YVForW

end FormalResearch.ModularBootstrap.FixedWeightBand
