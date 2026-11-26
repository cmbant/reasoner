/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspBase

/-!
# `fct:unscaled-cusp`, the phase facts (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`.

For `h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀` write `w x = x / (1 + x²)` and `Λ x = log (1 + x²) / 2` (`w = Λ'`).  Then
`κ₁ w ≤ 𝔪' ≤ κ₃ w` on `(0, ∞)`, with `κ₃ = π² κ₂ / 3`, hence `κ₁ (Λ t - Λ s) ≤ 𝔪 t - 𝔪 s ≤ κ₃ (Λ t - Λ s)` for
`0 ≤ s ≤ t`.  These are the only inputs on `𝔪` used by the three regimes, together with `|𝔪''| ≤ C₂`, `|𝔪 - m| ≤ C₀`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-- `w x = x / (1 + x²)`. -/
noncomputable def cuspW (x : ℝ) : ℝ := x / (1 + x ^ 2)

/-- `Λ x = log (1 + x²) / 2`, the primitive of `cuspW`. -/
noncomputable def cuspLam (x : ℝ) : ℝ := Real.log (1 + x ^ 2) / 2

lemma cuspLam_hasDerivAt (x : ℝ) : HasDerivAt cuspLam (cuspW x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).const_add 1)
  have h2 := (h1.log (by positivity)).div_const 2
  refine h2.congr_deriv ?_
  unfold cuspW; field_simp

lemma cuspLam_continuous : Continuous cuspLam :=
  continuous_iff_continuousAt.2 fun x => (cuspLam_hasDerivAt x).continuousAt

lemma cuspW_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cuspW x := by unfold cuspW; positivity

lemma cuspW_le_self {x : ℝ} (hx : 0 ≤ x) : cuspW x ≤ x := by
  unfold cuspW
  rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]

lemma cuspLam_zero : cuspLam 0 = 0 := by simp [cuspLam]

lemma cuspLam_le_sq (x : ℝ) : cuspLam x ≤ x ^ 2 / 2 := by
  unfold cuspLam
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + x ^ 2 by positivity)
  linarith

lemma cuspLam_ge (x : ℝ) : x ^ 2 / (2 * (1 + x ^ 2)) ≤ cuspLam x := by
  unfold cuspLam
  have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x ^ 2 by positivity)
  have h2 : 1 - (1 + x ^ 2)⁻¹ = x ^ 2 / (1 + x ^ 2) := by field_simp; ring
  rw [h2] at this
  have : x ^ 2 / (2 * (1 + x ^ 2)) = x ^ 2 / (1 + x ^ 2) / 2 := by field_simp
  linarith [Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x ^ 2 by positivity)]

lemma cuspLam_nonneg (x : ℝ) : 0 ≤ cuspLam x := by
  unfold cuspLam
  have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x])
  linarith

lemma cuspLam_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : cuspLam s ≤ cuspLam t := by
  unfold cuspLam
  have : 1 + s ^ 2 ≤ 1 + t ^ 2 := by nlinarith
  have := Real.log_le_log (by positivity) this
  linarith

/-- `Λ x - Λ (x/2) ≥ (3/8) x²/(1+x²)`. -/
lemma cuspLam_half_diff (x : ℝ) : 3 / 8 * (x ^ 2 / (1 + x ^ 2)) ≤ cuspLam x - cuspLam (x / 2) := by
  unfold cuspLam
  have h4 : 0 < 1 + (x / 2) ^ 2 := by positivity
  have hy : 0 < (1 + x ^ 2) / (1 + (x / 2) ^ 2) := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hy
  have hlog : Real.log ((1 + x ^ 2) / (1 + (x / 2) ^ 2)) =
      Real.log (1 + x ^ 2) - Real.log (1 + (x / 2) ^ 2) := Real.log_div (by positivity) h4.ne'
  have h2 : 1 - ((1 + x ^ 2) / (1 + (x / 2) ^ 2))⁻¹ = 3 / 4 * (x ^ 2 / (1 + x ^ 2)) := by
    field_simp; ring
  rw [h2, hlog] at hl
  linarith

/-! ### Consequences of `CuspPhase` -/

section Phase

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ}

/-- The upper constant `κ₃ = π² κ₂ / 3`. -/
noncomputable def cuspK3 (κ₂ : ℝ) : ℝ := π ^ 2 * κ₂ / 3

lemma hankelEdgeM'_le_w {x : ℝ} (hx : 0 < x) : hankelEdgeM' x ≤ π ^ 2 / 3 * cuspW x := by
  obtain ⟨_, h1, h2⟩ := hankelEdgeM'_bounds hx
  have hpi : 6 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  unfold cuspW
  by_cases hx1 : x ≤ 1
  · have : x / 2 ≤ x / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    nlinarith
  · push Not at hx1
    have h3 : 1 / (2 * x) ≤ x / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h4 : 1 / x ≤ π ^ 2 / 3 * (1 / (2 * x)) := by
      rw [show π ^ 2 / 3 * (1 / (2 * x)) = π ^ 2 / 6 * (1 / x) by field_simp; ring]
      have : 0 < 1 / x := by positivity
      nlinarith
    have h5 : π ^ 2 / 3 * (1 / (2 * x)) ≤ π ^ 2 / 3 * (x / (1 + x ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith

lemma CuspPhase.hasDerivAt (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (x : ℝ) : HasDerivAt 𝔪 (deriv 𝔪 x) x :=
  ((h.contDiff.differentiable (by norm_num)) x).hasDerivAt

lemma CuspPhase.hasDerivAt₂ (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (x : ℝ) :
    HasDerivAt (deriv 𝔪) (iteratedDeriv 2 𝔪 x) x := by
  have h1 : Differentiable ℝ (deriv 𝔪) := by
    have := h.contDiff.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  have := (h1 x).hasDerivAt
  rwa [show iteratedDeriv 2 𝔪 = deriv (deriv 𝔪) by
    rw [iteratedDeriv_succ, iteratedDeriv_one]]

lemma CuspPhase.continuous (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : Continuous 𝔪 :=
  h.contDiff.continuous

lemma CuspPhase.continuous_deriv (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : Continuous (deriv 𝔪) := by
  have := h.contDiff.continuous_iteratedDeriv 1 (by norm_num)
  rwa [iteratedDeriv_one] at this

lemma CuspPhase.continuous_deriv₂ (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : Continuous (iteratedDeriv 2 𝔪) :=
  h.contDiff.continuous_iteratedDeriv 2 le_rfl

lemma CuspPhase.deriv_ge_w (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {x : ℝ} (hx : 0 < x) : κ₁ * cuspW x ≤ deriv 𝔪 x := by
  have h1 := h.deriv_lower x hx
  have h2 := (hankelEdgeM'_bounds hx).1
  have := h.κ₁_pos
  unfold cuspW
  nlinarith

lemma CuspPhase.deriv_le_w (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {x : ℝ} (hx : 0 < x) :
    deriv 𝔪 x ≤ cuspK3 κ₂ * cuspW x := by
  have h1 := h.deriv_upper x hx
  have h2 := hankelEdgeM'_le_w hx
  have := h.κ₂_pos
  unfold cuspK3
  nlinarith

lemma CuspPhase.κ₃_pos (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : 0 < cuspK3 κ₂ := by
  have := h.κ₂_pos
  unfold cuspK3; positivity

lemma CuspPhase.deriv_nonneg (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {x : ℝ} (hx : 0 < x) : 0 < deriv 𝔪 x := by
  have := h.deriv_ge_w hx
  have h1 := h.κ₁_pos
  have : 0 < cuspW x := by unfold cuspW; positivity
  nlinarith

/-- The two-sided comparison `κ₁ (Λ t - Λ s) ≤ 𝔪 t - 𝔪 s ≤ κ₃ (Λ t - Λ s)` for `0 ≤ s ≤ t`. -/
lemma CuspPhase.diff_bounds (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    κ₁ * (cuspLam t - cuspLam s) ≤ 𝔪 t - 𝔪 s ∧ 𝔪 t - 𝔪 s ≤ cuspK3 κ₂ * (cuspLam t - cuspLam s) := by
  have hc : ∀ (k : ℝ), ContinuousOn (fun x => 𝔪 x - k * cuspLam x) (Ici 0) := fun k =>
    (h.continuous.sub (continuous_const.mul cuspLam_continuous)).continuousOn
  have hd : ∀ (k : ℝ), ∀ x, HasDerivAt (fun x => 𝔪 x - k * cuspLam x) (deriv 𝔪 x - k * cuspW x) x := fun k x =>
    (h.hasDerivAt x).sub ((cuspLam_hasDerivAt x).const_mul k)
  constructor
  · have hm : MonotoneOn (fun x => 𝔪 x - κ₁ * cuspLam x) (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (hc κ₁) (fun x _ => (hd κ₁ x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      rw [(hd κ₁ x).deriv]
      linarith [h.deriv_ge_w hx]
    have := hm hs (le_trans hs hst) hst
    simp only at this
    linarith
  · have hm : MonotoneOn (fun x => cuspK3 κ₂ * cuspLam x - 𝔪 x) (Ici 0) := by
      have hc' : ContinuousOn (fun x => cuspK3 κ₂ * cuspLam x - 𝔪 x) (Ici 0) :=
        ((continuous_const.mul cuspLam_continuous).sub h.continuous).continuousOn
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hc'
        (fun x _ => (((cuspLam_hasDerivAt x).const_mul (cuspK3 κ₂)).sub (h.hasDerivAt x)).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      have hdd : HasDerivAt (fun x => cuspK3 κ₂ * cuspLam x - 𝔪 x) (cuspK3 κ₂ * cuspW x - deriv 𝔪 x) x :=
        ((cuspLam_hasDerivAt x).const_mul _).sub (h.hasDerivAt x)
      rw [hdd.deriv]
      linarith [h.deriv_le_w hx]
    have := hm hs (le_trans hs hst) hst
    simp only at this
    linarith

lemma CuspPhase.mono (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : 𝔪 s ≤ 𝔪 t := by
  have := (h.diff_bounds hs hst).1
  have h1 := h.κ₁_pos
  have := cuspLam_mono hs hst
  nlinarith

lemma CuspPhase.nonneg (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ 𝔪 t := by
  have := h.mono le_rfl ht
  rwa [h.zero] at this

/-- The phase `cuspPhase 𝔪 u` has derivative `u - 𝔪`. -/
lemma CuspPhase.hasDerivAt_phase (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (u x : ℝ) :
    HasDerivAt (cuspPhase 𝔪 u) (u - 𝔪 x) x := by
  unfold cuspPhase
  have h1 : HasDerivAt (fun τ => ∫ t in (0 : ℝ)..τ, 𝔪 t) (𝔪 x) x :=
    intervalIntegral.integral_hasDerivAt_right (h.continuous.intervalIntegrable _ _)
      (h.continuous.stronglyMeasurableAtFilter _ _) h.continuous.continuousAt
  have h2 : HasDerivAt (fun τ => u * τ - ∫ t in (0 : ℝ)..τ, 𝔪 t) (u * 1 - 𝔪 x) x :=
    ((hasDerivAt_id' x).const_mul u).sub h1
  simpa using h2

/-- Strict monotonicity consequence: the lower bound for `𝔪 x - 𝔪 t₀` when `x ≥ 2 t₀` (for `t₀ ≥ 0`). -/
lemma CuspPhase.far_lower (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ x : ℝ} (ht₀ : 0 ≤ t₀) (hx : 2 * t₀ ≤ x) :
    3 * κ₁ / 8 * (x ^ 2 / (1 + x ^ 2)) ≤ 𝔪 x - 𝔪 t₀ := by
  have hx0 : 0 ≤ x := by linarith
  have h1 := (h.diff_bounds (by linarith : 0 ≤ x / 2) (by linarith : x / 2 ≤ x)).1
  have h2 := h.mono ht₀ (by linarith : t₀ ≤ x / 2)
  have h3 := cuspLam_half_diff x
  have := h.κ₁_pos
  nlinarith

end Phase

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.CuspPhase.diff_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CuspPhase.diff_bounds

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.CuspPhase.far_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CuspPhase.far_lower

end FormalResearch.SignUncertainty.FctUnscaledCusp
