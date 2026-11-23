module

public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS2W

/-!
# Bridge: Lemma S2 at Weight `w` versus the Spinless Virasoro Version (`vlo:S2`)

* `lemma_S2_of_W`: the Virasoro `ComplexBessel.lemma_S2` (`virasoroProblem`, `z = 1/2 + c' ω`,
  `c₀ ≥ 10000`) is the `w = 1` instance of `lemma_S2_W`.
* `lemma_S2_W_thermalDiff`: non-vacuity, the hypotheses of `lemma_S2_W` are met by every thermal
  difference `Ξ_β` (`thermalDiff_mem_TestClass`) at every weight and every `Q`: the Mellin integral of
  `Ξ_β` at `w/2 + c' ω` converges absolutely and obeys the crude Legendre bound.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing ComplexBessel

/-- The Virasoro Lemma S2 (`ComplexBessel.lemma_S2`) is the `w = 1` instance of `lemma_S2_W`. -/
theorem lemma_S2_of_W {μ₀ : ℝ} (hμ₀ : Real.pi * xiStar / 6 < μ₀) :
    ∃ C c₀ : ℝ, 0 < C ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {ω : ℂ}, μ₀ ≤ ω.re → ∀ {g : ℝ → ℝ},
        Crossing.TestClass Crossing.virasoroProblem (c' / 12) g →
        IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ ((1 / 2 + (c' : ℂ) * ω) - 1)) (Ioi 0) ∧
          ‖mellinMG g (1 / 2 + (c' : ℂ) * ω)‖ ≤
            C * Real.exp (c' * crudeExponentB ω) *
              Crossing.virasoroProblem.cardyNorm (c' / 12) g := by
  obtain ⟨C, c₀, hC, hc₀, h⟩ := lemma_S2_W virasoroProblem hμ₀
  refine ⟨C, max c₀ 10000, hC, le_max_right _ _, fun {c'} hc' {ω} hω {g} hg => ?_⟩
  have h1 := h ((le_max_left _ _).trans hc') hω hg
  have hw : ((virasoroProblem.w : ℕ) : ℂ) / 2 = 1 / 2 := by
    simp [virasoroProblem]
  rw [hw] at h1
  exact h1

/-- Non-vacuity of `lemma_S2_W`: for every weight and every `Q`, thermal differences `Ξ_β` are test
functions, so the crude Legendre bound holds for them. -/
theorem lemma_S2_W_thermalDiff (prob : FixedWeightProblem) {μ₀ : ℝ}
    (hμ₀ : Real.pi * xiStar / 6 < μ₀) :
    ∃ C c₀ : ℝ, 0 < C ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {ω : ℂ}, μ₀ ≤ ω.re → ∀ {β : ℝ}, 0 < β →
        IntegrableOn (fun t : ℝ => (thermalDiff prob.w β t : ℂ) *
            (t : ℂ) ^ (((prob.w : ℂ) / 2 + (c' : ℂ) * ω) - 1)) (Ioi 0) ∧
          ‖mellinMGW (thermalDiff prob.w β) ((prob.w : ℂ) / 2 + (c' : ℂ) * ω)‖ ≤
            C * Real.exp (c' * crudeExponentB ω) *
              prob.cardyNorm (c' / 12) (thermalDiff prob.w β) := by
  obtain ⟨C, c₀, hC, hc₀, h⟩ := lemma_S2_W prob hμ₀
  refine ⟨C, c₀, hC, hc₀, fun {c'} hc' {ω} hω {β} hβ => ?_⟩
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans (hc₀.trans hc')
  have hS : prob.totalShift ≤ c' / 12 := by
    have := (le_max_right _ _).trans (hc₀.trans hc')
    have hS0 := prob.totalShift_nonneg
    linarith
  exact h hc' hω (thermalDiff_mem_TestClass prob hS hβ)

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S2_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S2_of_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S2_W_thermalDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S2_W_thermalDiff

end FormalResearch.ModularBootstrap.FixedWeightBand
