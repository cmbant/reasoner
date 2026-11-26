module

public import FormalResearch.ModularBootstrap.FoldTip.Concordance
public import FormalResearch.ModularBootstrap.FoldTip.Instances
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow

/-!
# Fold-tip hypotheses and the FT bundle at every weight, modulo the `O(1)` upper bound

Source: Paper I `fold_tip_universality.tex` (Theorem FT, hypotheses H3, H4a, H4b); this lane's
`FoldTip/Instances.lean` and `FoldTip/Concordance.lean`, whose `H4b` and `FTSigma` are stated for `prob.w = 1` only.

With Property (P), `Σ` at every weight (`Upper/Assembly/BumpedDesignWindow.lean`):

* `fwH4bW`: `H4b` for every fixed-weight problem (the `w = 1` hypothesis of `fwH4b` is removed);
  `H4a` is `fwH4a` (every weight already);
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

/-- **`H4b` for every fixed-weight problem, at every weight** (the weight-`w` form of `fwH4b`, from
Property (P) for the bumped designs and displaced designs `designPropertyP_probW`, `displacedPropertyP_probW`, the
omitted family and `Σ`, for every sequence of extremal crossing measures). -/
theorem fwH4bW (prob : FixedWeightProblem) :
    FTH4b (FoldTipSetting.ofFixedWeight prob) (fwCrossingData prob) := by
  refine ⟨⟨0, fun c _ ν hν g hg => ?_⟩, fun cs ν hcs hν => ?_⟩
  · obtain ⟨meas, hmeas, hc, hshift, -, -, -⟩ := hν
    obtain ⟨hgt, C, hC, hdecay⟩ := hg
    obtain ⟨hint, heq⟩ := sumRule_of_comb_decay prob hshift hc meas hgt hC hdecay
    have hae : ∀ᵐ x ∂meas.ν, x ∈ Ici (0 : ℝ) := by
      rw [ae_iff]
      have : {a : ℝ | ¬ a ∈ Ici (0 : ℝ)} = Iio 0 := by ext a; simp
      rw [this]
      exact meas.supp_nonneg
    have hres : meas.ν.restrict (Ici (0 : ℝ)) = meas.ν := Measure.restrict_eq_self_of_ae_mem hae
    subst hmeas
    refine ⟨?_, ?_⟩
    · have := hint
      unfold IntegrableOn at this
      rwa [hres] at this
    · rw [hres] at heq
      exact heq
  · choose meas hmeas using fun j => hν j
    let S : CrossingSequence prob :=
      { c := cs
        τ := fun j => prob.T_V (cs j)
        meas := meas
        tendsto_c := hcs
        c_pos := fun j => (hmeas j).2.1
        shift_le := fun j => by have := (hmeas j).2.2.1; linarith
        τ_pos := fun j => (hmeas j).2.2.2.1
        atGap := fun j => (hmeas j).2.2.2.2.1 }
    have hμ : (fun j => (fwCrossingData prob).window (cs j) (ν j)) = S.μS := by
      funext j
      show spectralMeasure prob (cs j) (ν j) = spectralMeasure prob (cs j) (meas j).ν
      rw [(hmeas j).1]
    have key : ∀ μ : ℕ → Measure ℝ, μ = S.μS →
        LocallyBounded μ ∧
        (∀ (D : Window) (T : DesignTest μ D) (ε : ℝ), 0 < ε →
          ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ᶠ j in atTop, ∫ u in Iio (-R), T.Ψ j u ∂(μ j) ≤ ε) ∧
        ∃ 𝒟 : Set Window, DesignPropertyP μ 𝒟 ∧
          Nonempty (SameSiteFamily 𝒟) ∧ Nonempty (DisplacedFamily 𝒟) ∧ Nonempty (OmittedFamily 𝒟) := by
      intro μ hμ'
      subst hμ'
      have hLo := fixedWeightLowerBoundInput_of_problem prob
      have hSig : SigmaConclusion S.μS :=
        sigma_of_threshold_probW prob hLo S (fun j => le_rfl) (𝒟x := displacedClassX)
          (displacedPropertyP_probW prob S) sameSiteFamily_designClass_exists.some
          (DisplacedFamily.mono (displacedClass_subset.trans Set.subset_union_right) displacedFamily)
          farFamily
      refine ⟨hSig.1, hSig.2.2.2.2, designClass ∪ displacedClassX, ?_, ?_, ?_, ?_⟩
      · exact designPropertyP_union (designPropertyP_probW prob S) (displacedPropertyP_probW prob S)
      · exact ⟨SameSiteFamily.mono Set.subset_union_left sameSiteFamily_designClass_exists.some⟩
      · exact ⟨DisplacedFamily.mono (displacedClass_subset.trans Set.subset_union_right) displacedFamily⟩
      · exact ⟨farFamily⟩
    exact key _ hμ

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
      FTH4b (FoldTipSetting.ofFixedWeight prob) (fwCrossingData prob) ∧
      ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
        FTH2 (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2plus (FoldTipSetting.ofFixedWeight prob) ς δ ∧
        FTH4a (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ := by
  obtain ⟨c0, a0, ς, δ, h, h2, h4⟩ := fw_hypotheses prob
  exact ⟨fwH1 prob, fwH3 prob hHi, fwH4bW prob, c0, a0, ς, δ, h.toFTH2, h, h2, h4⟩

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fwH4bW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwH4bW

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_fixedWeight_modH3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_fixedWeight_modH3

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fw_foldTip_hypotheses_modH3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fw_foldTip_hypotheses_modH3

end FormalResearch.ModularBootstrap.FoldTip
