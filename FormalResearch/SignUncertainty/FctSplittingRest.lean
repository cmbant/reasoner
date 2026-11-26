/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingConj

/-!
# `FctSplittingStmt` from the remaining clauses: the field `splitting` is split

Paper I (`constant_terms_five.tex`), `fct:splitting` (1)-(2).  `FctSplittingStmt (fctPhiHat h)` (`FctWarpAdmiss.lean`) asks, for `c ≥ c₀`, `ε = ±1`, for
`SplittingData (Φ̂_c)`: holomorphy on `Re ζ > 0`, continuity on `S̄`, real symmetry, a `C²` left edge trace, and the bound block (`log log` growth, `O(ζ³)` at `0`,
edge derivative bounds).  Holomorphy and real symmetry are **proved** from the descent bound (`fctPhiHat_differentiableOn`, `fctPhiHat_conj`), so the field `splitting`
of `FctMainHankelInputs` is replaced by the field `splitting_rest : FctSplittingRestStmt (fctPhiHat ·)` (the other clauses) and `FctSplittingStmt` is the theorem
`fctSplitting_of_rest`.

* `SplittingRest Φ`: the clauses `cont`, `left_c2`, `bounds` of `SplittingData Φ` (same statements).
* `fctSplitting_of_rest`: `FctSplittingRestStmt (fctPhiHat h)` + `FctDescentStmt h` + `K₄ ≥ 1` ⟹ `FctSplittingStmt (fctPhiHat h)`.

Class: proved from `FctDescentStmt` (named input) and `FctSplittingRestStmt` (named input).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- The clauses of `SplittingData Φ` that are not yet proved from the descent bound: continuity on `S̄`, `C²` left edge trace, and the bound block
(`log log` growth on `S̄`, `Φ = O(ζ³)` at `0`, the left and right edge derivative bounds `(fct:Fminus-edge)`, `(fct:Eminus-edge)`). -/
structure SplittingRest (Φ : ℂ → ℂ) : Prop where
  /-- continuous up to the left edge `Re ζ = 0` -/
  cont : ContinuousOn Φ closedStrip
  /-- left edge trace is `C²` off `0` -/
  left_c2 : ContDiffOn ℝ 2 (fun t : ℝ => Φ ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0}
  bounds : ∃ M : ℝ, 0 ≤ M ∧
    (∀ ζ ∈ closedStrip, ‖Φ ζ‖ ≤ M * Real.log (Real.log (4 + |ζ.im|))) ∧
    (∀ ζ ∈ closedStrip, ‖ζ‖ ≤ 1 → ‖Φ ζ‖ ≤ M * ‖ζ‖ ^ 3) ∧
    (∀ τ : ℝ, τ ≠ 0 →
      ‖deriv (fun t : ℝ => Φ ((t : ℂ) * Complex.I)) τ‖ ≤ M * min 1 (|τ| ^ 2) ∧
      ‖deriv (deriv (fun t : ℝ => Φ ((t : ℂ) * Complex.I))) τ‖ ≤ M * min 1 |τ|) ∧
    (∀ τ : ℝ, ‖deriv (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I)) τ‖ ≤ M ∧
      ‖deriv (deriv (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I))) τ‖ ≤ M)

/-- The remaining (not yet proved) part of `fct:splitting` (1)-(2) for `Φ̂_c`. -/
def FctSplittingRestStmt (PhiHat : ℝ → ℝ → ℂ → ℂ) : Prop :=
  ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → SplittingRest (PhiHat ε c)

/-- **`FctSplittingStmt` from the remaining clauses**: holomorphy and real symmetry of `Φ̂_c` are proved from `FctDescentStmt` (`K₄ ≥ 1`). -/
theorem fctSplitting_of_rest {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h)
    (hR : FctSplittingRestStmt (fctPhiHat h)) : FctSplittingStmt (fctPhiHat h) := by
  obtain ⟨c1, h1⟩ := fctPhiHat_differentiableOn hK4 hD
  obtain ⟨c2, h2⟩ := fctPhiHat_conj hK4 hD
  obtain ⟨c3, h3⟩ := hR
  refine ⟨max (max c1 c2) c3, fun ε c hε hc => ?_⟩
  have hr := h3 ε c hε ((le_max_right _ _).trans hc)
  exact ⟨h1 ε c hε ((le_max_left _ _).trans ((le_max_left _ _).trans hc)), hr.cont,
    h2 ε c hε ((le_max_right c1 c2).trans ((le_max_left _ _).trans hc)),
    hr.left_c2, hr.bounds⟩

/-- info: 'FormalResearch.SignUncertainty.fctSplitting_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctSplitting_of_rest

end FormalResearch.SignUncertainty
