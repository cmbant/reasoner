module

public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS4W
public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinWBridge
public import FormalResearch.ModularBootstrap.StripMultiplier.LemmaS4

/-!
# Bridge: Lemma S4 at Weight `w` versus the Spinless Virasoro Version (`vlo:S4`)

* `tildeWW_one_eq`: at `w = 1`, `tildeWW 1 = StripMultiplier.tildeWV` (the entire `m_g` agrees by
  `mellinMGEntireW_one_eq`, and `z = 1/2 + c' ω`).
* `lemma_S4_of_W`: the Virasoro `StripMultiplier.lemma_S4` (`virasoroProblem`, `c₀ ≥ 10000`) is the
  `w = 1` instance of `lemma_S4_W`.
* `lemma_S4_W_thermalDiff`: non-vacuity, the hypotheses of `lemma_S4_W` are met by every thermal
  difference `Ξ_β` at every weight and every `Q` (`thermalDiff_mem_TestClass`): the strip multiplier
  of `Ξ_β` is holomorphic, continuous, antisymmetric and bounded by `C M[Ξ_β]`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Chart

theorem tildeWW_one_eq (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) :
    tildeWW 1 c' g ζ = StripMultiplier.tildeWV c' g ζ := by
  unfold tildeWW StripMultiplier.tildeWV
  rw [mellinMGEntireW_one_eq]
  norm_num

/-- The Virasoro Lemma S4 (`StripMultiplier.lemma_S4`) is the `w = 1` instance of `lemma_S4_W`. -/
theorem lemma_S4_of_W :
    ∃ C c₀ : ℝ, 0 < C ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        DifferentiableOn ℂ (StripMultiplier.tildeWV c' g) stripOpen ∧
        ContinuousOn (StripMultiplier.tildeWV c' g) stripClosed ∧
        (∀ ζ ∈ stripClosed, StripMultiplier.tildeWV c' g (1 - ζ) =
          -StripMultiplier.tildeWV c' g ζ) ∧
        (∀ ζ ∈ stripClosed, ‖StripMultiplier.tildeWV c' g ζ‖ ≤
          C * virasoroProblem.cardyNorm (c' / 12) g) := by
  obtain ⟨C, c₀, hC, hc₀, h⟩ := lemma_S4_W virasoroProblem
  refine ⟨C, max c₀ 10000, hC, le_max_right _ _, fun {c'} hc' {g} hg => ?_⟩
  have h1 := h ((le_max_left _ _).trans hc') hg
  have hfun : tildeWW virasoroProblem.w c' g = StripMultiplier.tildeWV c' g := by
    funext ζ
    exact tildeWW_one_eq c' g ζ
  rw [hfun] at h1
  exact h1

/-- Non-vacuity of `lemma_S4_W`: for every weight and every `Q`, thermal differences `Ξ_β` are test
functions, so the strip multiplier of `Ξ_β` is holomorphic, continuous, antisymmetric and bounded by
`C M[Ξ_β]`. -/
theorem lemma_S4_W_thermalDiff (prob : FixedWeightProblem) :
    ∃ C c₀ : ℝ, 0 < C ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {β : ℝ}, 0 < β →
        DifferentiableOn ℂ (tildeWW prob.w c' (thermalDiff prob.w β)) stripOpen ∧
        ContinuousOn (tildeWW prob.w c' (thermalDiff prob.w β)) stripClosed ∧
        (∀ ζ ∈ stripClosed, tildeWW prob.w c' (thermalDiff prob.w β) (1 - ζ) =
          -tildeWW prob.w c' (thermalDiff prob.w β) ζ) ∧
        (∀ ζ ∈ stripClosed, ‖tildeWW prob.w c' (thermalDiff prob.w β) ζ‖ ≤
          C * prob.cardyNorm (c' / 12) (thermalDiff prob.w β)) := by
  obtain ⟨C, c₀, hC, hc₀, h⟩ := lemma_S4_W prob
  refine ⟨C, c₀, hC, hc₀, fun {c'} hc' {β} hβ => ?_⟩
  obtain ⟨hS, -, -⟩ := shift_le_of_max_le prob (hc₀.trans hc')
  exact h hc' (thermalDiff_mem_TestClass prob hS hβ)

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S4_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S4_of_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S4_W_thermalDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S4_W_thermalDiff

end FormalResearch.ModularBootstrap.FixedWeightBand
