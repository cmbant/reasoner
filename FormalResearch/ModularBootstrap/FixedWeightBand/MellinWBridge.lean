module

public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinW
public import FormalResearch.ModularBootstrap.Mellin.HankelMellin

/-!
# Bridge: Lemma S1 at Weight `w` versus the Spinless Virasoro Version (`vlo:S1`)

The weight-`w` Mellin development of `MellinW` (new names `mellinTransformW`, `mellinMGW`,
`mellinMGEntireW`) specialises to the existing weight-one `Mellin.HankelMellin` objects:

* `mellinTransformW_eq`, `mellinMGW_eq`: equal to `ComplexBessel.mellinTransformG`/`mellinMG` (by
  definition);
* `mellinMGEntireW_one_eq`: `mellinMGEntireW 1 g = Mellin.mellinMGEntire g`;
* `lemma_S1_of_ge_two_of_W`: the Virasoro `Mellin.lemma_S1_of_ge_two` is an instance of
  `lemma_S1_W` (`w = 1`, `S = 2`);
* `lemma_S1_W_thermalDiff`: non-vacuity, the hypotheses of `lemma_S1_W` are met by every thermal
  difference `Ξ_β` (`thermalDiff_mem_TestClass`) for `S ≤ a`, `0 < a`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing

theorem mellinTransformW_eq (g : ℝ → ℝ) (z : ℂ) :
    mellinTransformW g z = ComplexBessel.mellinTransformG g z := rfl

theorem mellinMGW_eq (g : ℝ → ℝ) (z : ℂ) :
    mellinMGW g z = ComplexBessel.mellinMG g z := rfl

theorem mellinMGEntireW_one_eq (g : ℝ → ℝ) (z : ℂ) :
    mellinMGEntireW 1 g z = Mellin.mellinMGEntire g z := by
  unfold mellinMGEntireW Mellin.mellinMGEntire
  simp [mellinMGW_eq]

/-- The Virasoro Lemma S1 (`a ≥ 2`) is the `w = 1` instance of `lemma_S1_W`. -/
theorem lemma_S1_of_ge_two_of_W {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, 0 < z.re →
        F z = (2 * (Real.pi : ℂ)) ^ z * ComplexBessel.mellinTransformG g z / Complex.Gamma z) ∧
      ∀ z : ℂ, F (1 - z) = -F z := by
  have hS : virasoroProblem.totalShift = 2 := virasoroProblem_totalShift
  obtain ⟨F, hF, hFz, hFs⟩ := lemma_S1_W virasoroProblem (by rw [hS]; exact ha)
    (by linarith) hg
  exact ⟨F, hF, hFz, fun z => by simpa using hFs z⟩

/-- Non-vacuity of `lemma_S1_W`: thermal differences are test functions, so the entire
antisymmetric `m_{Ξ_β}` exists at every weight and every `Q` for `S ≤ a`, `0 < a`. -/
theorem lemma_S1_W_thermalDiff (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (ha0 : 0 < a) {β : ℝ} (hβ : 0 < β) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, 0 < z.re →
        F z = (2 * (Real.pi : ℂ)) ^ z * mellinTransformW (thermalDiff prob.w β) z /
          Complex.Gamma z) ∧
      ∀ z : ℂ, F ((prob.w : ℂ) - z) = -F z :=
  lemma_S1_W prob ha ha0 (thermalDiff_mem_TestClass prob ha hβ)

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_of_ge_two_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_of_ge_two_of_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_W_thermalDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_W_thermalDiff

end FormalResearch.ModularBootstrap.FixedWeightBand
