module

public import FormalResearch.ModularBootstrap.FoldTip.TwoEdgeLower
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWData

/-!
# Fixed-Weight Crossing Problems as a Fold Chart of Theorem FT-2E

Source: `CFT/modular_bootstrap/paper/fold_tip_two_edge.tex` (Theorem FT-2E, fixed Hermite--Biehler
data), `lower_o1_two_edge.tex` (`wone:ftlfw`, Step 5 chart inversion).

* `LemmaQData.foldChart`: the Langer chart of a fixed-weight problem at scale `c'`, `Δ = virasoroDeltaChart`,
  `ξ_* = ξ̄`, `β = 1/c_*`, `C_ξ = chartParams.C_xi`, radius `U_{c'} = A_{c'}²`, as a `FoldChart`; its
  `inv_lower` field is `LemmaQData.deltaChart_inversion` (the inversion used in Step 5 of
  `theoremFTLFW_W_of_YVFor`).

The violator family and chart coverage are in `TwoEdgeInstance.lean` (`twoEdgeInstance_of_YVForW`), which derives
`ft_fixedWeight_twoEdge`; `theoremFTLFW_W_of_YVFor` has the shape of `ft_twoEdge_lower_hb`
(`P = bootstrapParamsForW …`, `W_top = 0`, `u_* = a₁`, `Feasible c' T := ∃ g, IsWeaklyFeasible (c'/12) T g`).
-/

@[expose] public section

open scoped Real

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.ModularBootstrap.FixedWeightBand ConcreteBootstrap

/-- The Langer chart of a fixed-weight problem as a `FoldChart` (`β = 1/c_*`). -/
noncomputable def foldChartOfLemmaQ {prob : Crossing.FixedWeightProblem} (Q : LemmaQData prob) : FoldChart where
  ξs := xiBar
  β := 1 / cStar
  Cξ := chartParams.C_xi
  C0 := 1
  U := fun c' => Q.AC c' ^ 2
  Δ := virasoroDeltaChart
  hβ := one_div_pos.mpr cStar_pos
  hCξ := chartParams.hCxi_nn
  hC0 := le_rfl
  inv_lower := fun C hC u hu => by
    have h := Q.deltaChart_inversion (by linarith) hu
    have h2 : u / (1 / cStar) * C ^ (1 / 3 : ℝ) = cStar * C ^ (1 / 3 : ℝ) * u := by
      field_simp
    linarith

/-- The chart of `foldChartOfLemmaQ` is the Virasoro chart `Δ_{c'}`. -/
theorem foldChartOfLemmaQ_Δ {prob : Crossing.FixedWeightProblem} (Q : LemmaQData prob) :
    (foldChartOfLemmaQ Q).Δ = virasoroDeltaChart := rfl

/-- `foldChartOfLemmaQ` has slope `|u_*|/β = A_opt` at `u_* = a₁`: `(|a₁|/β) = A_opt`. -/
theorem foldChartOfLemmaQ_slope {prob : Crossing.FixedWeightProblem} (Q : LemmaQData prob) :
    |FormalResearch.Special.airyZero 1| / (foldChartOfLemmaQ Q).β = Aopt := by
  show |FormalResearch.Special.airyZero 1| / (1 / cStar) = Aopt
  unfold Aopt
  field_simp

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.foldChartOfLemmaQ_Δ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.foldChartOfLemmaQ_Δ

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.foldChartOfLemmaQ_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.foldChartOfLemmaQ_slope

end FormalResearch.ModularBootstrap.FoldTip
