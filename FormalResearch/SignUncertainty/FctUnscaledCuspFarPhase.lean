/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspMidT0

/-!
# `fct:unscaled-cusp`, regime `u ≥ 1`: phase facts and elementary inequalities (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, third estimate.

For `h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀`, `u ≥ 1` and `𝔪 t₀ = u`, `t₀ > 0`, with `κ₃ = cuspK3 κ₂`:

* `CuspPhase.le_sq`: `𝔪 t ≤ κ₃ t²/2` (`t ≥ 0`), hence `2 ≤ κ₃ t₀²` (`CuspPhase.two_le_sq`);
* `CuspPhase.far_half_gap`: `u - 𝔪 x ≥ G₂ = 3κ₁/(4(κ₃+2))` for `0 ≤ x ≤ t₀/2`;
* `CuspPhase.far_mid_deriv`: `𝔪' x ≥ κ₁/((κ₃+2) t₀)` for `t₀/2 ≤ x ≤ 2t₀`;
* `CuspPhase.exists_cut`: `t_* > 0` with `𝔪 t_* = u/2` and `κ₃ t_*² ≥ u`.

Elementary: `one_add_mul_exp_le`, `pow_four_mul_exp_le`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-- `(1 + x) e^{-z x} ≤ 1 + 1/z`. -/
lemma one_add_mul_exp_le {z x : ℝ} (hz : 0 < z) (hx : 0 ≤ x) : (1 + x) * Real.exp (-z * x) ≤ 1 + 1 / z := by
  have h1 := Real.add_one_le_exp (z * x)
  have h2 : 0 < Real.exp (-z * x) := Real.exp_pos _
  have h3 : Real.exp (-z * x) * Real.exp (z * x) = 1 := by rw [← Real.exp_add]; simp
  have h4 : Real.exp (-z * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h5 : x * Real.exp (-z * x) ≤ 1 / z := by
    rw [le_div_iff₀ hz]
    nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]
  nlinarith

/-- `t⁴ e^{-z t} ≤ 24/z⁴`. -/
lemma pow_four_mul_exp_le {z t : ℝ} (hz : 0 < z) (ht : 0 ≤ t) : t ^ 4 * Real.exp (-z * t) ≤ 24 / z ^ 4 := by
  have h1 := Real.pow_div_factorial_le_exp (z * t) (by positivity) 4
  have h2 : 0 < Real.exp (-z * t) := Real.exp_pos _
  have h3 : Real.exp (-z * t) * Real.exp (z * t) = 1 := by rw [← Real.exp_add]; simp
  rw [le_div_iff₀ (by positivity)]
  have h4 : (z * t) ^ 4 / (Nat.factorial 4 : ℝ) = (z * t) ^ 4 / 24 := by norm_num [Nat.factorial]
  rw [h4] at h1
  have := mul_le_mul_of_nonneg_left h1 h2.le
  nlinarith [this]

section Far

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ}

/-- `𝔪 t ≤ κ₃ t²/2` for `t ≥ 0`. -/
lemma CuspPhase.le_sq (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t : ℝ} (ht : 0 ≤ t) : 𝔪 t ≤ cuspK3 κ₂ * t ^ 2 / 2 := by
  have h1 := (h.diff_bounds le_rfl ht).2
  rw [cuspLam_zero, h.zero] at h1
  have h2 := cuspLam_le_sq t
  have h3 := h.κ₃_pos
  nlinarith

/-- `2 ≤ κ₃ t₀²` when `𝔪 t₀ = u ≥ 1`. -/
lemma CuspPhase.two_le_sq (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) (hu : 1 ≤ u) :
    2 ≤ cuspK3 κ₂ * t₀ ^ 2 := by
  have := h.le_sq ht₀.le
  rw [hv] at this
  linarith

/-- The gap constant `G₂ = 3κ₁/(4(κ₃+2))`. -/
noncomputable def cuspG2 (κ₁ κ₂ : ℝ) : ℝ := 3 * κ₁ / (4 * (cuspK3 κ₂ + 2))

lemma cuspG2_pos (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : 0 < cuspG2 κ₁ κ₂ := by
  have := h.κ₁_pos
  have := h.κ₃_pos
  unfold cuspG2; positivity

/-- For `u ≥ 1`: the gap `u - 𝔪 x ≥ G₂` on `[0, t₀/2]`. -/
lemma CuspPhase.far_half_gap (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hu : 1 ≤ u) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ t₀ / 2) : cuspG2 κ₁ κ₂ ≤ u - 𝔪 x := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have h2s := h.two_le_sq ht₀ hv hu
  have h1 := h.mono hx0 hx
  have h2 := (h.diff_bounds (by linarith : 0 ≤ t₀ / 2) (by linarith : t₀ / 2 ≤ t₀)).1
  have h3 := cuspLam_half_diff t₀
  have h4 : 2 / (cuspK3 κ₂ + 2) ≤ t₀ ^ 2 / (1 + t₀ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h5 : cuspG2 κ₁ κ₂ = κ₁ * (3 / 8 * (2 / (cuspK3 κ₂ + 2))) := by
    unfold cuspG2; field_simp; ring
  rw [h5]
  have h6 : 3 / 8 * (2 / (cuspK3 κ₂ + 2)) ≤ 3 / 8 * (t₀ ^ 2 / (1 + t₀ ^ 2)) := by gcongr
  have h7 := mul_le_mul_of_nonneg_left (h6.trans h3) hκ.le
  linarith

/-- For `u ≥ 1`: `𝔪' ≥ κ₁/((κ₃+2) t₀)` on `[t₀/2, 2t₀]`. -/
lemma CuspPhase.far_mid_deriv (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hu : 1 ≤ u) {x : ℝ} (hx1 : t₀ / 2 ≤ x) (hx2 : x ≤ 2 * t₀) :
    κ₁ / ((cuspK3 κ₂ + 2) * t₀) ≤ deriv 𝔪 x := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have h2s := h.two_le_sq ht₀ hv hu
  have hx : 0 < x := by linarith
  have h1 := h.deriv_ge_w hx
  unfold cuspW at h1
  have h2 : 1 / ((cuspK3 κ₂ + 2) * t₀) ≤ x / (1 + x ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hx1 (mul_nonneg hκ3.le ht₀.le), mul_le_mul_of_nonneg_left hx2 hx.le]
  have h3 := mul_le_mul_of_nonneg_left h2 hκ.le
  calc κ₁ / ((cuspK3 κ₂ + 2) * t₀) = κ₁ * (1 / ((cuspK3 κ₂ + 2) * t₀)) := by ring
    _ ≤ κ₁ * (x / (1 + x ^ 2)) := h3
    _ ≤ deriv 𝔪 x := h1

/-- The cut point `t_*` with `𝔪 t_* = u/2` (`u > 0`) and `u ≤ κ₃ t_*²`. -/
lemma CuspPhase.exists_cut (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {u : ℝ} (hu : 0 < u) :
    ∃ ts : ℝ, 0 < ts ∧ 𝔪 ts = u / 2 ∧ u ≤ cuspK3 κ₂ * ts ^ 2 := by
  obtain ⟨ts, hts, hv⟩ := h.exists_t0 (half_pos hu)
  refine ⟨ts, hts, hv, ?_⟩
  have := h.le_sq hts.le
  rw [hv] at this
  linarith

end Far

end FormalResearch.SignUncertainty.FctUnscaledCusp
