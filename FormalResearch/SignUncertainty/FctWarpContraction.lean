/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The contraction step of `fct:warp-asymp` (1) (Step 4 of the proof)

Paper I (`constant_terms_five.tex`), proof of Proposition FCT.5 (1), Step 4: for `F = M y + N(y)` on the ball `B_r` with `M` invertible,
`κ = ‖M⁻¹‖` and `Lip(N; B_r) ≤ 1/(2κ)`, the map `Γ(y) = -M⁻¹ N(y)` is a `1/2`-contraction; if `κ ‖N(0)‖ ≤ ρ/2` and `ρ ≤ r` then `Γ` maps `B_ρ`
into itself, so `F` has a zero in `B_ρ`, and it is the only zero of `F` in `B_r`.

`exists_unique_zero_of_lipschitz_perturbation` is this statement for an arbitrary real Banach space (the paper uses `E = ℝ²`,
`F = (Re, Im) ∘ Ξ̂` in the coordinates `y = (û - a₁, α̃)`, `ρ = C_* c^{-4/3}`, `r = c^{-7/6}`).

Class: proved.
-/
@[expose] public section

open Metric Set

namespace FormalResearch.SignUncertainty

/-- **Step 4 of `fct:warp-asymp` (1), abstract form.**  Let `M : E ≃L[ℝ] E` with `‖M⁻¹‖ ≤ κ` and `F y = M y + N y` on `closedBall 0 r`, with
`N` `1/(2κ)`-Lipschitz there and `κ‖N 0‖ ≤ ρ/2`, `0 ≤ ρ ≤ r`.  Then `F` has a zero in `closedBall 0 ρ`, and no other zero in `closedBall 0 r`. -/
theorem exists_unique_zero_of_lipschitz_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (M : E ≃L[ℝ] E) {κ : ℝ} (hκ : 0 < κ) (hM : ‖(M.symm : E →L[ℝ] E)‖ ≤ κ) {F N : E → E} {r ρ : ℝ}
    (hF : ∀ y, F y = M y + N y) (hLip : ∀ y ∈ closedBall (0 : E) r, ∀ z ∈ closedBall (0 : E) r, ‖N y - N z‖ ≤ 1 / (2 * κ) * ‖y - z‖)
    (h0 : κ * ‖N 0‖ ≤ ρ / 2) (hρ0 : 0 ≤ ρ) (hρr : ρ ≤ r) :
    ∃ y ∈ closedBall (0 : E) ρ, F y = 0 ∧ ∀ z ∈ closedBall (0 : E) r, F z = 0 → z = y := by
  set Γ : E → E := fun y => -(M.symm (N y)) with hΓ
  have hΓlip : ∀ y ∈ closedBall (0 : E) r, ∀ z ∈ closedBall (0 : E) r, ‖Γ y - Γ z‖ ≤ 1 / 2 * ‖y - z‖ := by
    intro y hy z hz
    have : Γ y - Γ z = -(M.symm (N y - N z)) := by simp only [hΓ, map_sub]; abel
    rw [this, norm_neg]
    calc ‖M.symm (N y - N z)‖ ≤ ‖(M.symm : E →L[ℝ] E)‖ * ‖N y - N z‖ := (M.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ κ * (1 / (2 * κ) * ‖y - z‖) := mul_le_mul hM (hLip y hy z hz) (norm_nonneg _) hκ.le
      _ = 1 / 2 * ‖y - z‖ := by field_simp
  have hΓ0 : ‖Γ 0‖ ≤ ρ / 2 := by
    calc ‖Γ 0‖ = ‖M.symm (N 0)‖ := by simp [hΓ]
      _ ≤ ‖(M.symm : E →L[ℝ] E)‖ * ‖N 0‖ := (M.symm : E →L[ℝ] E).le_opNorm _
      _ ≤ κ * ‖N 0‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
      _ ≤ ρ / 2 := h0
  have hmaps : MapsTo Γ (closedBall (0 : E) ρ) (closedBall (0 : E) ρ) := by
    intro y hy
    have hy' : y ∈ closedBall (0 : E) r := closedBall_subset_closedBall hρr hy
    have h00 : (0 : E) ∈ closedBall (0 : E) r := mem_closedBall_self (hρ0.trans hρr)
    have hyρ : ‖y‖ ≤ ρ := by simpa using hy
    have := hΓlip y hy' 0 h00
    rw [mem_closedBall, dist_zero_right]
    calc ‖Γ y‖ = ‖(Γ y - Γ 0) + Γ 0‖ := by simp
      _ ≤ ‖Γ y - Γ 0‖ + ‖Γ 0‖ := norm_add_le _ _
      _ ≤ 1 / 2 * ‖y - 0‖ + ρ / 2 := add_le_add this hΓ0
      _ ≤ ρ := by rw [sub_zero]; linarith
  have hcontr : ContractingWith (1 / 2 : NNReal) (hmaps.restrict Γ (closedBall (0 : E) ρ) (closedBall (0 : E) ρ)) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun y z => ?_⟩
    have := hΓlip y (closedBall_subset_closedBall hρr y.2) z (closedBall_subset_closedBall hρr z.2)
    simp only [Subtype.dist_eq, dist_eq_norm, MapsTo.val_restrict_apply]
    simpa using this
  obtain ⟨y, hy, hfix, -⟩ := hcontr.exists_fixedPoint' (isClosed_closedBall.isComplete) hmaps
    (x := 0) (mem_closedBall_self hρ0) (edist_ne_top _ _)
  have hfix' : Γ y = y := hfix
  have key : ∀ z, Γ z = z → F z = 0 := by
    intro z hz
    rw [hF]
    have : N z = -(M z) := by
      have h1 : M (Γ z) = -(N z) := by simp [hΓ]
      rw [hz] at h1
      exact (neg_eq_iff_eq_neg.mp h1.symm).symm ▸ rfl
    simp [this]
  refine ⟨y, hy, key y hfix', fun z hz hFz => ?_⟩
  have hzfix : Γ z = z := by
    have : N z = -(M z) := by rw [hF] at hFz; exact eq_neg_of_add_eq_zero_right hFz
    simp [hΓ, this]
  have hy' : y ∈ closedBall (0 : E) r := closedBall_subset_closedBall hρr hy
  have h := hΓlip z hz y hy'
  rw [hzfix, hfix'] at h
  have : ‖z - y‖ ≤ 0 := by linarith [norm_nonneg (z - y)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- info: 'FormalResearch.SignUncertainty.exists_unique_zero_of_lipschitz_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_unique_zero_of_lipschitz_perturbation

end FormalResearch.SignUncertainty
