/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspPhase

/-!
# `fct:unscaled-cusp`, regime `c^{-2/3} ≤ u ≤ 1`: the stationary point `t₀` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, second estimate.

For `h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀` and `0 < u ≤ 1` the stationary point `t₀ = 𝔪⁻¹(u)` exists (`exists_t0`) and, with
`Tm = exp(2/κ₁)` (`cuspTm`), satisfies `1 + t₀² ≤ Tm`, `κ₁ t₀²/(2 Tm) ≤ u ≤ κ₃ t₀²/2` (`CuspPhase.t0_bounds`);
the phase has the gaps `u - 𝔪 x ≥ 3κ₁ t₀²/(8 Tm)` on `[0, t₀/2]` (`CuspPhase.half_gap`) and the derivative lower bound
`𝔪' ≥ κ₁ t₀/(8 Tm)` on `[t₀/2, 2 t₀]` (`CuspPhase.mid_deriv`).  If moreover `c^{-2/3} ≤ u` then
`√(8/κ₃³) ≤ √c · (√t₀)³` (`cuspMid_q_lb`), which turns every `c^{-1} t₀^{-3/2}` into `c^{-1/2}`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-- `Tm = exp (2/κ₁)`, the bound for `1 + t₀²` when `u ≤ 1`. -/
noncomputable def cuspTm (κ₁ : ℝ) : ℝ := Real.exp (2 / κ₁)

lemma one_le_cuspTm (κ₁ : ℝ) (hκ : 0 < κ₁) : 1 ≤ cuspTm κ₁ := Real.one_le_exp (by positivity)

lemma cuspTm_pos (κ₁ : ℝ) : 0 < cuspTm κ₁ := Real.exp_pos _

section T0

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ}

/-- The stationary point `t₀ > 0` with `𝔪 t₀ = u`, for `u > 0`. -/
lemma CuspPhase.exists_t0 (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {u : ℝ} (hu : 0 < u) : ∃ t₀ : ℝ, 0 < t₀ ∧ 𝔪 t₀ = u := by
  have hκ := h.κ₁_pos
  set T : ℝ := Real.exp (u / κ₁) with hT
  have hT0 : 0 < T := Real.exp_pos _
  have hlog : u / κ₁ ≤ cuspLam T := by
    unfold cuspLam
    have h1 : Real.log (T ^ 2) ≤ Real.log (1 + T ^ 2) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow, hT, Real.log_exp] at h1
    push_cast at h1
    linarith
  have hd := (h.diff_bounds le_rfl hT0.le).1
  rw [cuspLam_zero, h.zero] at hd
  have hTu : u ≤ 𝔪 T := by
    have : u = κ₁ * (u / κ₁) := by field_simp
    nlinarith
  have hmem : u ∈ Icc (𝔪 0) (𝔪 T) := ⟨by rw [h.zero]; exact hu.le, hTu⟩
  obtain ⟨t₀, ht₀, hv⟩ := intermediate_value_Icc hT0.le h.continuous.continuousOn hmem
  refine ⟨t₀, ?_, hv⟩
  rcases ht₀.1.eq_or_lt with h0 | h0
  · rw [← h0, h.zero] at hv; linarith
  · exact h0

/-- Size of `t₀`: `1 + t₀² ≤ Tm`, `κ₁ t₀²/(2 Tm) ≤ u ≤ κ₃ t₀²/2`. -/
lemma CuspPhase.t0_bounds (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) (hu1 : u ≤ 1) :
    1 + t₀ ^ 2 ≤ cuspTm κ₁ ∧ cuspK3 κ₂ * t₀ ^ 2 / 2 ≥ u ∧ κ₁ * t₀ ^ 2 / (2 * cuspTm κ₁) ≤ u := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  obtain ⟨hd1, hd2⟩ := h.diff_bounds le_rfl ht₀.le
  rw [cuspLam_zero, h.zero, hv] at hd1 hd2
  have hl : cuspLam t₀ ≤ 1 / κ₁ := by
    rw [le_div_iff₀ hκ]; nlinarith
  have hTm : 1 + t₀ ^ 2 ≤ cuspTm κ₁ := by
    unfold cuspLam at hl
    have : Real.log (1 + t₀ ^ 2) ≤ 2 / κ₁ := by
      have : Real.log (1 + t₀ ^ 2) / 2 ≤ 1 / κ₁ := hl
      have h2 : 2 / κ₁ = 2 * (1 / κ₁) := by ring
      rw [h2]; linarith
    exact (Real.log_le_iff_le_exp (by positivity)).1 this
  refine ⟨hTm, ?_, ?_⟩
  · have := cuspLam_le_sq t₀
    nlinarith
  · have h3 := cuspLam_ge t₀
    have hTp := cuspTm_pos κ₁
    have h4 : t₀ ^ 2 / (2 * cuspTm κ₁) ≤ t₀ ^ 2 / (2 * (1 + t₀ ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h5 : κ₁ * (t₀ ^ 2 / (2 * cuspTm κ₁)) ≤ u := by
      have := mul_le_mul_of_nonneg_left (h4.trans h3) hκ.le
      linarith
    calc κ₁ * t₀ ^ 2 / (2 * cuspTm κ₁) = κ₁ * (t₀ ^ 2 / (2 * cuspTm κ₁)) := by ring
      _ ≤ u := h5

/-- The gap `u - 𝔪 x ≥ 3κ₁ t₀²/(8 Tm)` on `[0, t₀/2]`. -/
lemma CuspPhase.half_gap (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hu1 : u ≤ 1) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ t₀ / 2) :
    3 * κ₁ * t₀ ^ 2 / (8 * cuspTm κ₁) ≤ u - 𝔪 x := by
  have hκ := h.κ₁_pos
  have hTm := (h.t0_bounds ht₀ hv hu1).1
  have hTp := cuspTm_pos κ₁
  have h1 := h.mono hx0 hx
  have h2 := (h.diff_bounds (by linarith : 0 ≤ t₀ / 2) (by linarith : t₀ / 2 ≤ t₀)).1
  have h3 := cuspLam_half_diff t₀
  have h4 : 3 / 8 * (t₀ ^ 2 / cuspTm κ₁) ≤ 3 / 8 * (t₀ ^ 2 / (1 + t₀ ^ 2)) := by
    gcongr
  have h5 : 3 * κ₁ * t₀ ^ 2 / (8 * cuspTm κ₁) = κ₁ * (3 / 8 * (t₀ ^ 2 / cuspTm κ₁)) := by
    field_simp
  rw [h5]
  have h6 := mul_le_mul_of_nonneg_left (h4.trans h3) hκ.le
  linarith

/-- The derivative lower bound `𝔪' ≥ κ₁ t₀/(8 Tm)` on `[t₀/2, 2t₀]`. -/
lemma CuspPhase.mid_deriv (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hu1 : u ≤ 1) {x : ℝ} (hx1 : t₀ / 2 ≤ x) (hx2 : x ≤ 2 * t₀) : κ₁ * t₀ / (8 * cuspTm κ₁) ≤ deriv 𝔪 x := by
  have hκ := h.κ₁_pos
  have hTm := (h.t0_bounds ht₀ hv hu1).1
  have hTp := cuspTm_pos κ₁
  have hx : 0 < x := by linarith
  have h1 := h.deriv_ge_w hx
  unfold cuspW at h1
  have h2 : t₀ / (8 * cuspTm κ₁) ≤ x / (1 + x ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - 2 * t₀), mul_pos ht₀ hTp, mul_le_mul_of_nonneg_left hx2 hx.le]
  have h3 := mul_le_mul_of_nonneg_left h2 hκ.le
  calc κ₁ * t₀ / (8 * cuspTm κ₁) = κ₁ * (t₀ / (8 * cuspTm κ₁)) := by ring
    _ ≤ κ₁ * (x / (1 + x ^ 2)) := h3
    _ ≤ deriv 𝔪 x := h1

/-- The constant `ζ = √(8/κ₃³)`. -/
noncomputable def cuspZeta (κ₂ : ℝ) : ℝ := Real.sqrt (8 / cuspK3 κ₂ ^ 3)

/-- The lower bound `ζ ≤ c t₀³` from `c^{-2/3} ≤ u` and `u ≤ κ₃ t₀²/2`. -/
lemma CuspPhase.zeta_le (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u c : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hu1 : u ≤ 1) (hc : 0 < c) (hcu : c ^ (-(2 : ℝ) / 3) ≤ u) : cuspZeta κ₂ ≤ c * t₀ ^ 3 := by
  have hκ3 := h.κ₃_pos
  have hub := (h.t0_bounds ht₀ hv hu1).2.1
  have hcp : 0 < c ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have h1 : (c ^ (-(2 : ℝ) / 3)) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hcp.le hcu 3
  have h2 : (c ^ (-(2 : ℝ) / 3)) ^ 3 = (c ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    rw [show (-(2 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = -((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hc.le,
      Real.rpow_natCast]
  rw [h2] at h1
  have hu0 : 0 ≤ u := by have := hcp.le; linarith
  have h3 : u ^ 3 ≤ (cuspK3 κ₂ * t₀ ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hu0 hub 3
  have h4 : 1 ≤ c ^ 2 * (cuspK3 κ₂ * t₀ ^ 2 / 2) ^ 3 := by
    have : 1 ≤ c ^ 2 * u ^ 3 := by
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    exact this.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg c))
  unfold cuspZeta
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have e : (c * t₀ ^ 3) ^ 2 * cuspK3 κ₂ ^ 3 = 8 * (c ^ 2 * (cuspK3 κ₂ * t₀ ^ 2 / 2) ^ 3) := by ring
  rw [e]; linarith

/-- The lower bound `√ζ ≤ √c (√t₀)³`. -/
lemma CuspPhase.q_lb (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u c : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hu1 : u ≤ 1) (hc : 0 < c) (hcu : c ^ (-(2 : ℝ) / 3) ≤ u) :
    Real.sqrt (cuspZeta κ₂) ≤ Real.sqrt c * Real.sqrt t₀ ^ 3 := by
  have h1 := h.zeta_le ht₀ hv hu1 hc hcu
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have e : (Real.sqrt c * Real.sqrt t₀ ^ 3) ^ 2 = c * t₀ ^ 3 := by
    have : (Real.sqrt c * Real.sqrt t₀ ^ 3) ^ 2 = Real.sqrt c ^ 2 * (Real.sqrt t₀ ^ 2) ^ 3 := by ring
    rw [this, Real.sq_sqrt hc.le, Real.sq_sqrt ht₀.le]
  rw [e]; exact h1

lemma cuspZeta_pos (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : 0 < cuspZeta κ₂ := by
  have := h.κ₃_pos
  unfold cuspZeta; positivity

end T0

end FormalResearch.SignUncertainty.FctUnscaledCusp
