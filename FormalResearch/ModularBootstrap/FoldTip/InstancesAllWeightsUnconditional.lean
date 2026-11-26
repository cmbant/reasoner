module

public import FormalResearch.ModularBootstrap.FoldTip.InstancesAllWeights
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpFinal

/-!
# Fold-tip hypotheses and the FT bundle at every weight, unconditionally

Source: Paper I `fold_tip_universality.tex` (Theorem FT, hypotheses H3, H4a, H4b) and Paper II
`n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`).

`Upper.Ramped.theoremC15UpperInput_probW` proves the `O(1)` upper bound `TheoremC15UpperInput prob` (hypothesis `H3`) for every
`prob : FixedWeightProblem`, so the `modH3` forms of `FoldTip/InstancesAllWeights.lean` become unconditional:

* `ft_fixedWeight_all`: the bundle `FTLower ∧ FTLiminf ∧ FTRigidity ∧ FTAiryLaw ∧ FTSigma` at every weight;
* `fw_foldTip_hypotheses_all`: `H1`, `H2`, `H2-hol`, `H2+`, `H3`, `H4a`, `H4b` at every weight;
* `corollary_E1_all`: Corollary E1 (`ds:E1`) at every `(w, Q)`.

All results are proved unconditionally.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.FixedWeightBand

universe u

/-- **FT bundle for every fixed-weight problem, unconditionally** (`ft_fixedWeight_modH3` with `H3` discharged by
`Upper.Ramped.theoremC15UpperInput_probW`). -/
theorem ft_fixedWeight_all (prob : FixedWeightProblem) :
    FTLower prob ∧ FTLiminf.{u} prob ∧ FTRigidity.{u} prob ∧ FTAiryLaw prob ∧ FTSigma prob :=
  ft_fixedWeight_modH3.{u} prob (Upper.Ramped.theoremC15UpperInput_probW prob)

/-- **The hypotheses of Theorem FT at every weight, unconditionally.** -/
theorem fw_foldTip_hypotheses_all (prob : FixedWeightProblem) :
    FTH1 (FoldTipSetting.ofFixedWeight prob) ∧ FTH3 (FoldTipSetting.ofFixedWeight prob) ∧
      FTH4b (FoldTipSetting.ofFixedWeight prob) (fwCrossingData prob) ∧
      ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
        FTH2 (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2plus (FoldTipSetting.ofFixedWeight prob) ς δ ∧
        FTH4a (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ :=
  fw_foldTip_hypotheses_modH3 prob (Upper.Ramped.theoremC15UpperInput_probW prob)

/-- **Corollary E1 (`ds:E1`) at every fixed weight `(w, Q)`, unconditionally**: `corollary_E1` with the lower bound
`fixedWeightLowerBoundInput_of_problem` (Theorem `W1'(1)`) and the upper bound `theoremC15UpperInput_probW`. -/
theorem corollary_E1_all (prob : FixedWeightProblem) :
    ∃ c₀ C : ℝ, max 1 (12 * prob.totalShift) ≤ c₀ ∧ 0 ≤ C ∧
      (∀ {cTilde : ℝ}, c₀ ≤ cTilde →
        0 < prob.T_V cTilde ∧
        |prob.T_V cTilde - TStar cTilde| ≤ C ∧
        |prob.Delta_best cTilde - (cTilde / lambdaV + Aopt * cTilde ^ ((1 : ℝ) / 3))| ≤ C ∧
        ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
          meas.ν (Set.Iio (prob.T_V cTilde)) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Set.Iio (prob.T_V cTilde + ε))) ∧
          prob.Delta_best cTilde = cTilde / 12 + prob.T_V cTilde) ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (prob.T_V (cSeq j) - TStar (cSeq j)) / (cSeq j) ^ ((1 : ℝ) / 3))
          atTop (𝓝 0)) :=
  corollary_E1 prob (fixedWeightLowerBoundInput_of_problem prob) (Upper.Ramped.theoremC15UpperInput_probW prob)

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_fixedWeight_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_fixedWeight_all

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fw_foldTip_hypotheses_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fw_foldTip_hypotheses_all

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.corollary_E1_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corollary_E1_all

end FormalResearch.ModularBootstrap.FoldTip
