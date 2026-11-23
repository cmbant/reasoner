module

public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQScale
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LemmaQ

/-!
# Bridge: scale-flexible Lemma Q versus the spinless Virasoro version (`wone:Q`)

At `prob = virasoroProblem` (`w = 1`) the general objects of `LemmaQScale` are the Virasoro ones:

* `chartACAt_eq_virasoroACAt`: `chartACAt = virasoroACAt`;
* `psiTilde_virasoroProblem`: `psiTilde virasoroProblem c' = virasoroPsiTilde c'` for `c' ≥ 0`;
* `deltaLobeAt_virasoroProblem`: `deltaLobeAt virasoroProblem = virasoroDeltaLobeAt`;
* `lemmaQ_part1At_of_general`: `ConcreteBootstrap.lemmaQ_part1At` at every scale
  `0 < b ≤ chartBV D.r₁` follows from `lemmaQ_general_part1At` (the Virasoro statement holds up to
  `virasoroBV`; the general one only up to the disc cap `chartBV D.r₁ ≤ virasoroBV`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing WeightAxioms ConcreteBootstrap FixedWeightTip

lemma chartACAt_eq_virasoroACAt (b c' : ℝ) : chartACAt b c' = virasoroACAt b c' := rfl

lemma psiTilde_virasoroProblem {c' : ℝ} (hc' : 0 ≤ c') (g : ℝ → ℝ) (u : ℂ) :
    psiTilde virasoroProblem c' g u = virasoroPsiTilde c' g u := by
  unfold psiTilde virasoroPsiTilde
  rw [show virasoroProblem.w = 1 from rfl, hankelContinuationW_one_eq hc',
    cardyVC_virasoro_eq]

lemma deltaLobeAt_virasoroProblem (b c' : ℝ) (g : ℝ → ℝ) :
    deltaLobeAt virasoroProblem b c' g = virasoroDeltaLobeAt b c' g := rfl

/-- The Virasoro `lemmaQ_part1At` at scale `0 < b ≤ chartBV D.r₁` is an instance of
`lemmaQ_general_part1At` at `w = 1`. -/
theorem lemmaQ_part1At_of_general (D : UniformPropositionPData virasoroProblem) {b : ℝ}
    (hb : 0 < b) (hb_le : b ≤ chartBV D.r_1) :
    ∃ c_Q1 C_gap κ_gap : ℝ, virasoroCQEnv ≤ c_Q1 ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' T : ℝ}, c_Q1 ≤ c' → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        virasoroProblem.cardyNorm (c' / 12) g > 0 ∧
        virasoroDeltaLobeAt b c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
        virasoroDeltaLobeAt b c' g < 1 / 2 ∧
        virasoroDeltaChart c' (virasoroACAt b c' ^ 2) < T := by
  obtain ⟨c_gap, C_gap, κ_gap, _, hC, hκ, h⟩ := lemmaQ_general_part1At D hb hb_le
  refine ⟨max virasoroCQEnv c_gap, C_gap, κ_gap, le_max_left _ _, hC, hκ,
    fun {c' T} hc' {g} hg => h ((le_max_right _ _).trans hc') hg⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.psiTilde_virasoroProblem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psiTilde_virasoroProblem

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemmaQ_part1At_of_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaQ_part1At_of_general

end FormalResearch.ModularBootstrap.FixedWeightBand
