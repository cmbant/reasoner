/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymExpm1
public import FormalResearch.SignUncertainty.FctVacuumPointwise

/-!
# From `SymW` bounds with the weight `Cw τ₁^a (1+x)^{-8}` to the `min(t², 1)` / `min(1, t^{-8})` form of `QTSym` (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b).

* `raw_min_of_symW`: `f ∈ SymW S (Cw τ₁^a (1+x)^{-8}) K` (`a ≥ 2`, `τ₁ ≤ 1`) and `λ τ₁ ≤ x` on `S` give
  `|x^j f^{(j)}| ≤ (K_j Cw/λ²) min(x², 1)` and `≤ K_j Cw min(1, x^{-8})`;
* `tau0_three_quarter_ge`: `τ₀(3 m(τ)/4) ≥ λ τ` for `0 < τ ≤ 1/8` with an absolute `λ ∈ (0, 1]` (the left end `t = τ₀(3δ_L/4)` of
  the range is comparable with `τ₁`, `δ_L = m(τ₁)`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies

lemma raw_min_of_symW {S : Set ℝ} {K : ℕ → ℝ} {f : ℝ → ℝ} {τ₁ lam Cw : ℝ} {a : ℕ}
    (ha : 2 ≤ a) (hCw : 0 ≤ Cw) (hτ0 : 0 < τ₁) (hτ1 : τ₁ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (h : SymW S (fun x => Cw * τ₁ ^ a * ((1 + x) ^ 8)⁻¹) K f) (hS : ∀ x ∈ S, lam * τ₁ ≤ x) (j : ℕ) {x : ℝ} (hx : x ∈ S) :
    |x ^ j * iteratedDeriv j f x| ≤ (K j * Cw / lam ^ 2) * min (x ^ 2) 1 ∧
    |x ^ j * iteratedDeriv j f x| ≤ (K j * Cw) * min 1 ((x ^ 8)⁻¹) := by
  have hb := h.raw_bound j hx
  have hx0 : 0 < x := h.pos x hx
  have hK0 := h.K_nonneg j
  have hxl : lam * τ₁ ≤ x := hS x hx
  have hτa : τ₁ ^ a ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ0.le hτ1 ha
  have hτa1 : τ₁ ^ a ≤ 1 := pow_le_one₀ hτ0.le hτ1
  have hτa0 : 0 ≤ τ₁ ^ a := by positivity
  have hD : 0 < (1 + x) ^ 8 := by positivity
  have hDi : ((1 + x) ^ 8)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hDi8 : ((1 + x) ^ 8)⁻¹ ≤ (x ^ 8)⁻¹ := inv_anti₀ (pow_pos hx0 8) (pow_le_pow_left₀ hx0.le (by linarith) 8)
  have hDi0 : 0 ≤ ((1 + x) ^ 8)⁻¹ := by positivity
  have hW : τ₁ ^ a * ((1 + x) ^ 8)⁻¹ ≤ τ₁ ^ 2 := by nlinarith
  have hτx : τ₁ ^ 2 ≤ x ^ 2 / lam ^ 2 := by
    rw [le_div_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hlam2 : 1 ≤ 1 / lam ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  refine ⟨hb.trans ?_, hb.trans ?_⟩
  · have hmin : τ₁ ^ a * ((1 + x) ^ 8)⁻¹ ≤ min (x ^ 2) 1 / lam ^ 2 := by
      rcases le_total (x ^ 2) 1 with h1 | h1
      · rw [min_eq_left h1]; exact hW.trans hτx
      · rw [min_eq_right h1]
        calc τ₁ ^ a * ((1 + x) ^ 8)⁻¹ ≤ 1 := by nlinarith
          _ ≤ 1 / lam ^ 2 := hlam2
    calc K j * (Cw * τ₁ ^ a * ((1 + x) ^ 8)⁻¹) = K j * Cw * (τ₁ ^ a * ((1 + x) ^ 8)⁻¹) := by ring
      _ ≤ K j * Cw * (min (x ^ 2) 1 / lam ^ 2) := by gcongr
      _ = _ := by ring
  · have hmin : τ₁ ^ a * ((1 + x) ^ 8)⁻¹ ≤ min 1 ((x ^ 8)⁻¹) :=
      le_min (by nlinarith) ((mul_le_of_le_one_left hDi0 hτa1).trans hDi8)
    calc K j * (Cw * τ₁ ^ a * ((1 + x) ^ 8)⁻¹) = K j * Cw * (τ₁ ^ a * ((1 + x) ^ 8)⁻¹) := by ring
      _ ≤ K j * Cw * min 1 ((x ^ 8)⁻¹) := by gcongr

/-- `τ₀(3 m(τ)/4) ≥ λ τ` for `0 < τ ≤ 1/8`, with an absolute `λ ∈ (0, 1]`. -/
lemma tau0_three_quarter_ge : ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 8 →
    lam * τ ≤ tau0 (3 / 4 * uctM τ) := by
  obtain ⟨c1, hc1, hc1b⟩ := uct_m_lower_small
  obtain ⟨C, hC, hCb⟩ := uct_m_upper_small
  set lam : ℝ := min 1 (3 * c1 / (4 * C)) with hlam
  have hlam0 : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  refine ⟨lam, hlam0, hlam1, fun τ hτ hτ8 => ?_⟩
  have hLpos : 0 < 3 / 4 * uctM τ := by have := uctM_pos hτ; positivity
  have hmt : uctM (tau0 (3 / 4 * uctM τ)) = 3 / 4 * uctM τ := ceEll_tau0 hLpos
  by_contra hcon
  push Not at hcon
  have hlt : tau0 (3 / 4 * uctM τ) < lam * τ := hcon
  have hmono := uctM_strictMonoOn (mem_Ioi.mpr (tau0_pos hLpos)) (mem_Ioi.mpr (by positivity : 0 < lam * τ)) hlt
  have hlτ : lam * τ ≤ 1 / 8 := by nlinarith
  have h1 := hCb (lam * τ) ⟨by positivity, hlτ⟩
  have h2 := (hc1b τ ⟨hτ, hτ8⟩).1
  rw [hmt] at hmono
  have h3 : lam ≤ 3 * c1 / (4 * C) := min_le_right _ _
  have h4 : lam * C ≤ 3 * c1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at h3 ⊢
    nlinarith
  have h5 : C * (lam * τ) ^ 2 ≤ 3 / 4 * (c1 * τ ^ 2) := by
    calc C * (lam * τ) ^ 2 = (lam * C) * lam * τ ^ 2 := by ring
      _ ≤ (3 * c1 / 4) * 1 * τ ^ 2 := by gcongr
      _ = _ := by ring
  nlinarith

end FormalResearch.SignUncertainty.FctSym
