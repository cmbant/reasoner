module

public import FormalResearch.ModularBootstrap.FoldTip.Concordance
public import FormalResearch.ModularBootstrap.FoldTip.Instances
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow

/-!
# Fold-tip hypotheses and the FT bundle at every weight, modulo the `O(1)` upper bound

Source: Paper I `fold_tip_universality.tex` (Theorem FT, hypotheses H3, H4a, H4b); this lane's
`FoldTip/Instances.lean` and `FoldTip/Concordance.lean`, whose `H4b` and `FTSigma` are stated for `prob.w = 1` only.

With Property (P), `Σ` at every weight (`Upper/Assembly/BumpedDesignWindow.lean`):

* `fwH4bW`: `H4b` at Airy level (`ShellHBData.airy`, from `FoldTip.FixedWeightDualDesigns`) for every
  fixed-weight problem (the `w = 1` hypothesis of `fwH4b` is removed); `H4a` is `fwH4a` (every weight already);
* `ft_C5c_fixedWeight`: `ft:C5c` (`DualMeasures.ft_C5c`) instantiated unconditionally at Airy level for every
  fixed-weight problem;
* `ftSigma_probW`: `FTSigma prob` for every fixed-weight problem;
* `ft_fixedWeight_modH3`: the bundle `FTLower ∧ FTLiminf ∧ FTRigidity ∧ FTAiryLaw ∧ FTSigma` at every weight, with the
  single hypothesis `TheoremC15UpperInput prob` (the `O(1)` upper bound, `H3`; a theorem for `prob.w = 1`,
  `Upper.Ramped.theoremC15UpperInput_prob`, and the target of W-P6 for `w > 1`);
* `fw_foldTip_hypotheses_modH3`: `H1`, `H2`, `H2-hol`, `H2+`, `H4a`, `H4b` unconditionally and `H3` from `hHi`.

**`H3` is not proved here**: it is the upper bound itself (W-P6).

All results are proved unconditionally.
-/

@[expose] public section

open Filter Topology MeasureTheory Metric Set Asymptotics
open scoped Real

namespace FormalResearch.ModularBootstrap.FoldTip

open Set MeasureTheory
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.FixedWeightTip
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.FixedWeightBand FormalResearch.Special

universe u

/-- **Conclusion `ft:C5c` at Airy level (`ShellHBData.airy`) for every fixed-weight problem, unconditionally**:
vague convergence of `spectralMeasure prob (cs j) (ν j)` to `hbQuadMeasure ShellHBData.airy` (`= airyQuadMeasure`),
with local boundedness and no-escape along any design matching the Airy quadrature integral. -/
theorem ft_C5c_fixedWeight (prob : FixedWeightProblem)
    (cs : ℕ → ℝ) (ν : ℕ → Measure ℝ) (hcs : Tendsto cs atTop atTop)
    (hν : ∀ j, ν j ∈ (fwCrossingData prob).extremal (cs j)) :
    let μ : ℕ → Measure ℝ := fun j => (fwCrossingData prob).window (cs j) (ν j)
    ∃ j₀ : ℕ, (∀ j, j₀ ≤ j → IsLocallyFiniteMeasure (μ j)) ∧
      (∀ (μ' : ℕ → Measure ℝ), (∀ j, μ' j = μ (j + j₀)) →
        LocallyBounded μ' ∧
        IsVagueLimit atTop μ' (hbQuadMeasure SignUncertainty.ShellHBData.airy) ∧
        ∀ {W : ℝ → ℝ}, FTDesign (fwCrossingData prob) W →
          (Integrable W (hbQuadMeasure SignUncertainty.ShellHBData.airy) ∧
            ∫ u, W u ∂(hbQuadMeasure SignUncertainty.ShellHBData.airy) = ∫ u, W u) →
          ∀ (des : SeqDesign μ'), des.W = W →
            ∀ {ε : ℝ}, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
              ∀ᶠ j in atTop, ∫ u in Iio (-R), des.U j u ∂(μ' j) ≤ ε) :=
  ft_C5c SignUncertainty.ShellHBData.airy (fwCrossingData prob) (fwH4bW prob) cs ν hcs hν

/-- **Extremal measures (C5c, Airy level) at every weight**: `FTSigma prob` for every fixed-weight problem. -/
theorem ftSigma_probW (prob : FixedWeightProblem) : FTSigma prob :=
  sigma_unconditional_probW prob

/-- **FT bundle for every fixed-weight problem, modulo the `O(1)` upper bound (H3)**: the lower bound, the liminf
(C2), the rigidity (C5a, C5b), the extremal-measure theorem (C5c, Airy level; no longer restricted to `w = 1`) are
unconditional at every weight; only the two-sided Airy law (C2 full, C4) uses the hypothesis `TheoremC15UpperInput prob`
(true for `prob.w = 1`, open for `w > 1`: W-P6). -/
theorem ft_fixedWeight_modH3 (prob : FixedWeightProblem) (hHi : TheoremC15UpperInput prob) :
    FTLower prob ∧ FTLiminf.{u} prob ∧ FTRigidity.{u} prob ∧ FTAiryLaw prob ∧ FTSigma prob :=
  ⟨fixedWeightLowerBoundInput_of_problem prob, (ft_fixedWeight_general.{u} prob).2.1,
    (ft_fixedWeight_general.{u} prob).2.2, ft_fixedWeight_H3 prob hHi, ftSigma_probW prob⟩

/-- **The hypotheses of Theorem FT at every weight, modulo `H3`**: `H1`, `H2`, `H2-hol`, `H2+`, `H4a`, `H4b` hold for
every fixed-weight problem; `H3` is `fwH3 prob hHi` from the `O(1)` upper bound. -/
theorem fw_foldTip_hypotheses_modH3 (prob : FixedWeightProblem) (hHi : TheoremC15UpperInput prob) :
    FTH1 (FoldTipSetting.ofFixedWeight prob) ∧ FTH3 (FoldTipSetting.ofFixedWeight prob) ∧
      FTH4b SignUncertainty.ShellHBData.airy (fwCrossingData prob) ∧
      ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
        FTH2 (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2plus (FoldTipSetting.ofFixedWeight prob) ς δ ∧
        FTH4a (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ := by
  obtain ⟨c0, a0, ς, δ, h, h2, h4⟩ := fw_hypotheses prob
  exact ⟨fwH1 prob, fwH3 prob hHi, fwH4bW prob, c0, a0, ς, δ, h.toFTH2, h, h2, h4⟩

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_C5c_fixedWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_C5c_fixedWeight

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_fixedWeight_modH3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_fixedWeight_modH3

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fw_foldTip_hypotheses_modH3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fw_foldTip_hypotheses_modH3

end FormalResearch.ModularBootstrap.FoldTip
