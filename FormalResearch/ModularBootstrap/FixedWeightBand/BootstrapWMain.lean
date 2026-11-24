module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWHB
public import FormalResearch.ModularBootstrap.FoldTip.TwoEdgeInstance

/-!
# Theorem `FT-L.FW` at Every Fixed `(w, Q)` from the Band-Feedback Input (WP10)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Theorem `W1'(1)`
(`wone:genlower`) and Theorem `J` (`vlo:J`) at an arbitrary `prob : FixedWeightProblem`.

* `theoremFTLFW_W_of_YVFor` (re-derived from Theorem FT-2E, `FoldTip.ft_fixedWeight_twoEdge`): Steps 0-5 of Theorem `FT-L.FW` at scale `0 < b ≤ b_V` from `YVInputForW prob b`:
  there are `c₂ ≥ cQ` and `C ≥ 0` with `T ≥ ξ̄ c' + A_opt c'^{1/3} - C` for every weakly feasible test at
  `(c'/12, T)`, `c' ≥ c₂` (the Virasoro `theoremFTLFW_oneZero_of_YVFor`);
* `theoremJ_T_V_W`: `T_V(c̃) ≥ T_*(c̃) - C` from `YVInputForW`;
* `fixedWeightLowerBoundInput_of_YVForW`: the consumer interface
  `FixedWeightLowerBoundInput prob` (Theorem `W1'(1)`) from `YVInputForW prob b` at a scale `b ≤ b_V`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem}

/-- **Theorem `FT-L.FW` at `(P, Q) = (1, 0)`** (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`wone:ftlfw`) at scale `0 < b ≤ Q.bV` from `YVInputForW prob b`: Steps 0–5 give
`c₂ ≥ Q.cQ` and `C ≥ 0` such that every weakly feasible Virasoro test `g` at
`(c'/12, T)` with `c' ≥ c₂` obeys `T ≥ ξ̄ c' + A_opt c'^{1/3} - C`. -/
theorem theoremFTLFW_W_of_YVFor (Q : LemmaQData prob) {b : ℝ} (hb_pos : 0 < b)
    (hb_le : b ≤ Q.bV) (hYV : YVInputForW prob b) :
    ∃ c_2 C : ℝ, Q.cQ ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' T : ℝ}, c_2 ≤ c' → ∀ {g : ℝ → ℝ},
        prob.IsWeaklyFeasible (c' / 12) T g →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ T := by
  obtain ⟨C₁, K, hQ, hK, h⟩ := FoldTip.ft_fixedWeight_twoEdge Q hb_pos hb_le hYV
  exact ⟨C₁, K, hQ, hK, fun {_ _} hc' {_} hg => h _ hc' _ ⟨_, hg⟩⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.theoremFTLFW_W_of_YVFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremFTLFW_W_of_YVFor

end FormalResearch.ModularBootstrap.FixedWeightBand
