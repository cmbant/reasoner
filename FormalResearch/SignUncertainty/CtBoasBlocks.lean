module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasMBounds
public import FormalResearch.SignUncertainty.CtBoasPlb
public import FormalResearch.SignUncertainty.UctStripSplit

/-!
# `ct:boas` Step 3: block geometry of the stationary point `τ₀(L) = m⁻¹(L)`

`constant_terms_lower.tex`, `ct:boas` Step 3 ("`τ₀(L₀)/τ₀(L_j) ∈ [1/3, 3]` uniformly on every `I_j^{**}`").
The TeX proves it from the logarithmic derivative of `τ₀`; here `tau0_ratio_le` gets the same Harnack ratio from the mean
value theorem and `q(t) = t/(1+t²) ≤ m'(t)`, `m(t) ≤ π²t²/12`, with the block width `min(L,1)/5` in place of the TeX's
`min(L,1)/2` (the width of a block is a free parameter of the construction).  **Proved**, unconditional.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `m(τ₀(L)) = L` for `L > 0`. -/
lemma hankelEdgeM_tau0 {L : ℝ} (hL : 0 < L) : hankelEdgeM (tau0 L) = L := ceEll_tau0 hL

/-- `τ₀` is monotone on `(0, ∞)`. -/
lemma tau0_mono {L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') : tau0 L ≤ tau0 L' := by
  have hL' : 0 < L' := lt_of_lt_of_le hL hLL
  by_contra h
  rw [not_le] at h
  have := hankelEdgeM_strictMonoOn (mem_Ici.2 (tau0_pos hL').le) (mem_Ici.2 (tau0_pos hL).le) h
  rw [hankelEdgeM_tau0 hL, hankelEdgeM_tau0 hL'] at this
  linarith

/-- **Harnack ratio of `τ₀`** (`ct:boas` Step 3): if `0 < L ≤ L'` and `L' - L ≤ min(L,1)/5` then
`τ₀(L') ≤ 3 τ₀(L)`. -/
theorem tau0_ratio_le {L L' : ℝ} (hL : 0 < L) (hLL : L ≤ L') (hw : L' - L ≤ min L 1 / 5) :
    tau0 L' ≤ 3 * tau0 L := by
  have hL' : 0 < L' := lt_of_lt_of_le hL hLL
  have hτ := tau0_pos hL
  have hτ' := tau0_pos hL'
  set τ := tau0 L with hτdef
  set τ' := tau0 L' with hτ'def
  have hm : hankelEdgeM τ = L := hankelEdgeM_tau0 hL
  have hm' : hankelEdgeM τ' = L' := hankelEdgeM_tau0 hL'
  by_contra hcon
  rw [not_le] at hcon
  -- mean value theorem on `[τ, 3τ]`
  have hab : τ < 3 * τ := by linarith
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope hankelEdgeM hankelEdgeM' hab
    (hankelEdgeM_continuousOn.mono (fun x hx => le_trans hτ.le hx.1))
    (fun x hx => hankelEdgeM_hasDerivAt (lt_trans hτ hx.1))
  have hξ0 : 0 < ξ := lt_trans hτ hξ.1
  have hq := hankelEdgeM'_ge_simple hξ0
  have hq2 : τ / (1 + 9 * τ ^ 2) ≤ ξ / (1 + ξ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hτ.le hξ0.le) (sub_nonneg.2 hξ.2.le), mul_pos hτ hξ0, hξ.1, hξ.2,
      mul_nonneg hτ.le (sub_nonneg.2 (show ξ ≤ 9 * τ by linarith [hξ.2]))]
  have hdiff : hankelEdgeM (3 * τ) - hankelEdgeM τ = hankelEdgeM' ξ * (2 * τ) := by
    rw [hξd]; field_simp; ring
  have hmono : hankelEdgeM (3 * τ) ≤ hankelEdgeM τ' :=
    hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 hτ'.le) hcon.le
  have hΔ : 2 * τ ^ 2 / (1 + 9 * τ ^ 2) ≤ L' - L := by
    have : τ / (1 + 9 * τ ^ 2) * (2 * τ) ≤ hankelEdgeM' ξ * (2 * τ) :=
      mul_le_mul_of_nonneg_right (hq2.trans hq) (by positivity)
    have e : τ / (1 + 9 * τ ^ 2) * (2 * τ) = 2 * τ ^ 2 / (1 + 9 * τ ^ 2) := by field_simp
    linarith
  -- `τ² ≥ 12 L / π²`
  have hπ : π < 3.15 := Real.pi_lt_d2
  have hu : 12 * L ≤ π ^ 2 * τ ^ 2 := by
    have := hankelEdgeM_le_sq hτ.le; rw [hm] at this; linarith
  have hu2 : 1.2 * L ≤ τ ^ 2 := by
    have : π ^ 2 < 9.9226 := by nlinarith [Real.pi_pos]
    by_contra hh; rw [not_le] at hh
    nlinarith [sq_nonneg τ, Real.pi_pos, mul_pos hL (show (0:ℝ) < 1 by norm_num)]
  rw [div_le_iff₀ (by positivity)] at hΔ
  rcases le_total L 1 with h1 | h1
  · rw [min_eq_left h1] at hw
    nlinarith [mul_nonneg (sub_nonneg.2 hw) (sq_nonneg τ), mul_pos hL hτ, sq_nonneg τ,
      mul_nonneg hL.le (sq_nonneg τ)]
  · rw [min_eq_right h1] at hw
    have : 1 < τ ^ 2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hw) (sq_nonneg τ)]

/-- Two-sided Harnack ratio `τ₀(L')/τ₀(L) ∈ [1/3, 3]` when `|L' - L| ≤ min(L, L', 1)/5` (the hypotheses of
`hankel_frozen_P_lb` on `τ_j`). -/
theorem tau0_ratio {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L') (hw : |L' - L| ≤ min (min L L') 1 / 5) :
    tau0 L / 3 ≤ tau0 L' ∧ tau0 L' ≤ 3 * tau0 L := by
  rcases le_total L L' with h | h
  · rw [abs_of_nonneg (by linarith)] at hw
    have hmin : min (min L L') 1 = min L 1 := by rw [min_eq_left h]
    rw [hmin] at hw
    have := tau0_ratio_le hL h hw
    exact ⟨by linarith [tau0_pos hL, tau0_mono hL h], this⟩
  · rw [abs_of_nonpos (by linarith)] at hw
    have hmin : min (min L L') 1 = min L' 1 := by rw [min_eq_right h]
    rw [hmin] at hw
    have := tau0_ratio_le hL' h (by linarith)
    exact ⟨by linarith, by linarith [tau0_pos hL', tau0_mono hL' h]⟩

/-- info: 'FormalResearch.SignUncertainty.tau0_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tau0_ratio_le

end FormalResearch.SignUncertainty
