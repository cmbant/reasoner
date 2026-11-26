/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingCauchy

/-!
# `Φ^warp_c` is the paper's two-branch function and is holomorphic on `Re ζ > 0` (`fct:splitting` (2))

Paper I (`constant_terms_five.tex`), `(fct:Phiwarp-def)` and the proof of `fct:splitting` (2) ("the two branches glue holomorphically across `Re ζ = 3/8`").

From the descent bound `FctDescentStmt h` (`(fct:F-38-bnd)`, a named input) and `K₄ ≥ 1`, for `c ≥ c₀` and `ε = ±1`:

* `fctPhiWarp_eq_left` / `fctPhiWarp_eq_right`: Lean's `fctPhiWarp` (`F_-` on the contour `7/16`) equals the paper's definition: `Φ_c - F_-^{3/8}` on `0 < Re ζ < 3/8` and
  `1 - F_+^{3/8}` on `Re ζ > 3/8`.  Uses the shift `F_-^{7/16} = F_-^{3/8}` (`Re ζ < 3/8`) and `F_-^{7/16} - F_+^{3/8} = F` (`3/8 < Re ζ < 7/16`, residue).
* `fctPhiWarp_differentiableOn`: `Φ^warp_c` is holomorphic on `{Re ζ > 0}` (the glued function).
* `fctPhiHat_differentiableOn`: `Φ̂_c = Φ^warp_c/N_c + β_c q₁` is holomorphic on `{Re ζ > 0}`: the clause `hol` of `SplittingData`.

Class: proved from `FctDescentStmt` (named input).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- The data of `D_{τ₁}` and the uniform contour bound used by the contour shift, from `FctDescentStmt` (`K₄ ≥ 1`): for `c ≥ c₀`, `ε = ±1`, with `(L₁, α)` the chosen
zero pair, `c > 0`, `D_{τ₁}` holomorphic on `S`, continuous, bounded and real-symmetric on `S̄`, and `‖F(σ+iy)‖ ≤ B` for `3/8 ≤ σ ≤ 7/16`. -/
theorem fctSplitting_setup {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ B : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      0 < c ∧ DifferentiableOn ℂ (fctDcompAt K4 c (fctWarpAlpha h ε c)) strip ∧
        ContinuousOn (fctDcompAt K4 c (fctWarpAlpha h ε c)) closedStrip ∧
        (∃ B' : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖ ≤ B') ∧
        (∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 →
          ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((σ : ℂ) + y * Complex.I)‖ ≤ B) ∧
        ∀ ζ ∈ closedStrip, fctDcompAt K4 c (fctWarpAlpha h ε c) (starRingEnd ℂ ζ) =
          starRingEnd ℂ (fctDcompAt K4 c (fctWarpAlpha h ε c) ζ) := by
  obtain ⟨C, c₀, hC⟩ := hD
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |fctWarpAlpha h ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨cD, hcD⟩ := fctDcomp_compData hK4 hα
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max (max c₀ cD) 1, |C| / Real.log 2, fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := (le_max_right _ _).trans hc
  have hDD := hcD ε c hε ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
  refine ⟨by linarith, hDD.hol, hDD.cont, hDD.bd, fun σ y h1 h2 => ?_, hDD.conj⟩
  refine (hC ε c hε ((le_max_left _ _).trans ((le_max_left _ _).trans hc)) σ y (by linarith) h2).trans ?_
  have hl : Real.log 2 ≤ Real.log (2 + |y|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])
  have hcpos : 0 < c := by linarith
  calc C * c⁻¹ / Real.log (2 + |y|) ≤ |C| * c⁻¹ / Real.log (2 + |y|) := by
        gcongr
        · exact (Real.log_pos (by linarith [abs_nonneg y])).le
        · exact le_abs_self C
    _ ≤ |C| * c⁻¹ / Real.log 2 := by gcongr
    _ ≤ |C| / Real.log 2 := by
        have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
        have h3 : |C| * c⁻¹ ≤ |C| * 1 := by gcongr
        rw [mul_one] at h3
        exact div_le_div_of_nonneg_right h3 hl0.le


section Glue

variable {K4 ε c L1 α B : ℝ}

/-- `Φ_c = 1 + F`. -/
lemma fctPhiC_eq (ζ : ℂ) : fctPhiC K4 ε c L1 α ζ = 1 + fctFint K4 ε c L1 α ζ := by
  unfold fctFint; ring

/-- **Right branch** of `(fct:Phiwarp-def)`: for `Re ζ > 3/8`, `Φ^warp_c(ζ) = 1 - F_+(ζ)` (`F_+` on the contour `Re t = 3/8`). -/
theorem fctPhiWarp_eq_right (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B)
    {ζ : ℂ} (h0 : 3 / 8 < ζ.re) :
    fctPhiWarp K4 ε c L1 α ζ = 1 - fctCauchy K4 ε c L1 α (3 / 8) ζ := by
  unfold fctPhiWarp
  split_ifs with h
  · have := fctCauchy_shift hc hDh hDc hDb hF h0 h
    rw [fctPhiC_eq]
    linear_combination -this
  · rfl

/-- **Left branch** of `(fct:Phiwarp-def)`: for `0 < Re ζ < 3/8`, `Φ^warp_c(ζ) = Φ_c(ζ) - F_-(ζ)` with the paper's contour `Re t = 3/8`. -/
theorem fctPhiWarp_eq_left (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B)
    {ζ : ℂ} (h1 : ζ.re < 3 / 8) :
    fctPhiWarp K4 ε c L1 α ζ = fctPhiC K4 ε c L1 α ζ - fctCauchy K4 ε c L1 α (3 / 8) ζ := by
  unfold fctPhiWarp
  split_ifs with hh
  · rw [fctCauchy_shift_left hc hDh hDc hDb hF h1]
  · exfalso; linarith

/-- **`Φ^warp_c` is holomorphic on `{Re ζ > 0}`** (`fct:splitting` (2): the two branches glue across `Re ζ = 3/8`). -/
theorem fctPhiWarp_differentiableOn (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) :
    DifferentiableOn ℂ (fctPhiWarp K4 ε c L1 α) {ζ : ℂ | 0 < ζ.re} := by
  have hU1 : IsOpen {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 7 / 16} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hU2 : IsOpen {ζ : ℂ | 3 / 8 < ζ.re} := isOpen_lt continuous_const Complex.continuous_re
  have hC7 := fctCauchy_differentiableOn (ε := ε) (L1 := L1) (α := α) hc hDc (σ := 7 / 16) (by norm_num) le_rfl
    (fun y => hF _ y (by norm_num) le_rfl) hU1 (fun w (hw : 0 < w.re ∧ w.re < 7 / 16) => ⟨hw.1, hw.2.ne⟩)
  have hC3 := fctCauchy_differentiableOn (ε := ε) (L1 := L1) (α := α) hc hDc (σ := 3 / 8) le_rfl (by norm_num)
    (fun y => hF _ y le_rfl (by norm_num)) hU2 (fun w (hw : 3 / 8 < w.re) => ⟨by linarith, by intro h; rw [h] at hw; norm_num at hw⟩)
  have hFb := fctFint_differentiableOn_band (ε := ε) (L1 := L1) (α := α) hc hDh hDc hDb
  have hsub : {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 7 / 16} ⊆ {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 2} :=
    fun ζ hζ => ⟨hζ.1, by linarith [hζ.2]⟩
  have h1 : DifferentiableOn ℂ (fctPhiWarp K4 ε c L1 α) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 7 / 16} := by
    have : DifferentiableOn ℂ (fun ζ => 1 + fctFint K4 ε c L1 α ζ - fctCauchy K4 ε c L1 α (7 / 16) ζ)
        {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 7 / 16} :=
      ((differentiableOn_const _).add (hFb.mono hsub)).sub hC7
    refine this.congr fun ζ hζ => ?_
    unfold fctPhiWarp
    split_ifs with hh
    · rw [fctPhiC_eq]
    · exact absurd hζ.2 hh
  have h2 : DifferentiableOn ℂ (fctPhiWarp K4 ε c L1 α) {ζ : ℂ | 3 / 8 < ζ.re} := by
    have : DifferentiableOn ℂ (fun ζ => 1 - fctCauchy K4 ε c L1 α (3 / 8) ζ) {ζ : ℂ | 3 / 8 < ζ.re} :=
      (differentiableOn_const _).sub hC3
    exact this.congr fun ζ hζ => fctPhiWarp_eq_right hc hDh hDc hDb hF hζ
  intro ζ hζ
  by_cases hlt : ζ.re < 7 / 16
  · exact (h1.differentiableAt (hU1.mem_nhds ⟨hζ, hlt⟩)).differentiableWithinAt
  · exact (h2.differentiableAt (hU2.mem_nhds (show 3 / 8 < ζ.re by have : 7 / 16 ≤ ζ.re := not_lt.mp hlt; linarith))).differentiableWithinAt

/-- `q₁` is holomorphic on `Re ζ > -1`. -/
lemma fctQ1_differentiableOn : DifferentiableOn ℂ fctQ1 {ζ : ℂ | 0 < ζ.re} := by
  intro ζ hζ
  have : ζ + 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; have := hζ; simp at this; linarith
  unfold fctQ1
  refine DifferentiableAt.differentiableWithinAt ?_
  fun_prop (disch := exact pow_ne_zero 4 this)

/-- **`Φ̂_c` is holomorphic on `{Re ζ > 0}`** (the `hol` clause of `SplittingData`; `Φ̂_c = Φ^warp_c/N_c + β_c q₁`). -/
theorem fctPhiHatAt_differentiableOn (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) :
    DifferentiableOn ℂ (fctPhiHatAt K4 ε c L1 α) {ζ : ℂ | 0 < ζ.re} := by
  unfold fctPhiHatAt
  exact ((fctPhiWarp_differentiableOn hc hDh hDc hDb hF).div_const _).add
    ((differentiableOn_const _).mul fctQ1_differentiableOn)

end Glue

/-- **`fct:splitting` (2), holomorphy clause** (from the descent bound): there is `c₀` such that for `ε = ±1`, `c ≥ c₀` the splitting function `Φ̂_c`
(`fctPhiHat h`) is holomorphic on `{Re ζ > 0}`. -/
theorem fctPhiHat_differentiableOn {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      DifferentiableOn ℂ (fctPhiHat h ε c) {ζ : ℂ | 0 < ζ.re} := by
  obtain ⟨c₀, B, hB⟩ := fctSplitting_setup hK4 hD
  refine ⟨c₀, fun ε c hε hc => ?_⟩
  obtain ⟨hc0, hDh, hDc, hDb, hF, -⟩ := hB ε c hε hc
  exact fctPhiHatAt_differentiableOn hc0 hDh hDc hDb hF

/-- **Glued form, from the descent bound**: for `c ≥ c₀`, `Φ^warp_c = Φ_c - F_-` on `0 < Re ζ < 3/8` and `= 1 - F_+` on `Re ζ > 3/8`. -/
theorem fctPhiWarp_paper_of_descent {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (∀ ζ : ℂ, ζ.re < 3 / 8 →
        fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ =
          fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ -
            fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) ζ) ∧
      (∀ ζ : ℂ, 3 / 8 < ζ.re →
        fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ =
          1 - fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) ζ) := by
  obtain ⟨c₀, B, hB⟩ := fctSplitting_setup hK4 hD
  refine ⟨c₀, fun ε c hε hc => ?_⟩
  obtain ⟨hc0, hDh, hDc, hDb, hF, -⟩ := hB ε c hε hc
  exact ⟨fun ζ h1 => fctPhiWarp_eq_left hc0 hDh hDc hDb hF h1, fun ζ h0 => fctPhiWarp_eq_right hc0 hDh hDc hDb hF h0⟩

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_differentiableOn

/-- info: 'FormalResearch.SignUncertainty.fctPhiWarp_paper_of_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiWarp_paper_of_descent

end FormalResearch.SignUncertainty
