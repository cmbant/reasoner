/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingConj
public import FormalResearch.SignUncertainty.FctSplittingCont

/-!
# `FctSplittingStmt` from the remaining clauses: the field `splitting` is split

Paper I (`constant_terms_five.tex`), `fct:splitting` (1)-(2).  `FctSplittingStmt (fctPhiHat h)` (`FctWarpAdmiss.lean`) asks, for `c ≥ c₀`, `ε = ±1`, for
`SplittingData (Φ̂_c)`: holomorphy on `Re ζ > 0`, continuity on `S̄`, real symmetry, a `C²` left edge trace, and the bound block (`log log` growth, `O(ζ³)` at `0`,
edge derivative bounds).  Holomorphy, real symmetry, continuity on `S̄` and the corner bound `Φ̂_c = O(ζ³)` are **proved** from the descent bound (`fctPhiHat_differentiableOn`, `fctPhiHat_conj`,
`fctPhiHat_cont_cubic`), so the field `splitting` of `FctMainHankelInputs` is replaced by the field `splitting_rest : FctSplittingRestStmt (fctPhiHat ·)` (the other clauses)
and `FctSplittingStmt` is the theorem `fctSplitting_of_rest`.

* `SplittingRest Φ`: the clauses `left_c2`, `loglog`, `left_deriv`, `right_deriv` of `SplittingData Φ` (same statements, separately).
* `fctSplitting_of_rest`: `FctSplittingRestStmt (fctPhiHat h)` + `FctDescentStmt h` + `K₄ ≥ 1` ⟹ `FctSplittingStmt (fctPhiHat h)`.

Class: proved from `FctDescentStmt` (named input) and `FctSplittingRestStmt` (named input).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- The clauses of `SplittingData Φ` that are not yet proved from the descent bound: the `C²` left edge trace, the `log log` growth on `S̄`, and the left and right
edge derivative bounds `(fct:Fminus-edge)`, `(fct:Eminus-edge)`, `(fct:Psi-edge)`.  (Continuity on `S̄` and `Φ = O(ζ³)` at `0` are **proved**, `fctPhiHat_cont_cubic`.)
The first two `τ`-derivatives of `Φ̂_c(iτ)` on the *whole* left edge, `M min(1,τ²)`, `M min(1,|τ|)`, are not stated in the paper for `Φ̂_c` (only for `F_-`, `Ψ_c`, `q₁`
separately); see `PLAN.md`. -/
structure SplittingRest (Φ : ℂ → ℂ) : Prop where
  /-- left edge trace is `C²` off `0` -/
  left_c2 : ContDiffOn ℝ 2 (fun t : ℝ => Φ ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0}
  /-- `log log` growth on `S̄` (`|Φ̂_c| ≤ C log log(4+|τ|)`) -/
  loglog : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ closedStrip, ‖Φ ζ‖ ≤ M * Real.log (Real.log (4 + |ζ.im|))
  /-- first two `τ`-derivatives on the whole left edge -/
  left_deriv : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, τ ≠ 0 →
    ‖deriv (fun t : ℝ => Φ ((t : ℂ) * Complex.I)) τ‖ ≤ M * min 1 (|τ| ^ 2) ∧
      ‖deriv (deriv (fun t : ℝ => Φ ((t : ℂ) * Complex.I))) τ‖ ≤ M * min 1 |τ|
  /-- first two `τ`-derivatives on the right edge `Re ζ = 1` -/
  right_deriv : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ,
    ‖deriv (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I)) τ‖ ≤ M ∧
      ‖deriv (deriv (fun t : ℝ => Φ (1 - (t : ℂ) * Complex.I))) τ‖ ≤ M

/-- The remaining (not yet proved) part of `fct:splitting` (1)-(2) for `Φ̂_c`. -/
def FctSplittingRestStmt (PhiHat : ℝ → ℝ → ℂ → ℂ) : Prop :=
  ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → SplittingRest (PhiHat ε c)

/-- **`FctSplittingStmt` from the remaining clauses**: holomorphy, real symmetry, continuity on `S̄` and `Φ̂_c = O(ζ³)` are proved from `FctDescentStmt` (`K₄ ≥ 1`). -/
theorem fctSplitting_of_rest {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h)
    (hR : FctSplittingRestStmt (fctPhiHat h)) : FctSplittingStmt (fctPhiHat h) := by
  obtain ⟨c1, h1⟩ := fctPhiHat_differentiableOn hK4 hD
  obtain ⟨c2, h2⟩ := fctPhiHat_conj hK4 hD
  obtain ⟨c4, h4⟩ := fctPhiHat_cont_cubic hK4 hD
  obtain ⟨c3, h3⟩ := hR
  refine ⟨max (max (max c1 c2) c3) c4, fun ε c hε hc => ?_⟩
  have hc1 : c1 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
  have hc2 : c2 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
  have hc3 : c3 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc4 : c4 ≤ c := (le_max_right _ _).trans hc
  have hr := h3 ε c hε hc3
  obtain ⟨hcont, M2, hM2, hcub⟩ := h4 ε c hε hc4
  obtain ⟨M1, hM1, hll⟩ := hr.loglog
  obtain ⟨M3, hM3, hl⟩ := hr.left_deriv
  obtain ⟨M4, hM4, hrt⟩ := hr.right_deriv
  refine ⟨h1 ε c hε hc1, hcont, h2 ε c hε hc2, hr.left_c2, max (max M1 M2) (max M3 M4), by positivity, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    exact (hll ζ hζ).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (loglog_nonneg (abs_nonneg _)))
  · intro ζ hζ hb
    exact (hcub ζ hζ hb).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (by positivity))
  · intro τ hτ
    obtain ⟨a, b⟩ := hl τ hτ
    have hm : (0 : ℝ) ≤ min 1 (|τ| ^ 2) := le_min zero_le_one (by positivity)
    have hm' : (0 : ℝ) ≤ min 1 |τ| := le_min zero_le_one (abs_nonneg _)
    exact ⟨a.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hm),
      b.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hm')⟩
  · intro τ
    obtain ⟨a, b⟩ := hrt τ
    exact ⟨a.trans ((le_max_right _ _).trans (le_max_right _ _)), b.trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- info: 'FormalResearch.SignUncertainty.fctSplitting_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctSplitting_of_rest

end FormalResearch.SignUncertainty
