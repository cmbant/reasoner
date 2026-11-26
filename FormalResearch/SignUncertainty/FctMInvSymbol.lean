/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctMLarge
public import FormalResearch.SignUncertainty.FctSymInv

/-!
# `1/m` and `1/m'` as `t`-symbols on `(0, ∞)` (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b): the quotients `ϑ''/m'` and `ϑ'/m` of `Δ_curv`.

* `mInv_symW_Ioc`: `1/m ∈ SymW (0, 1/8] (t^{-2})` (`m = t² m_Q`, `m_Q` smooth and positive);
* `mInv_symW_all`: `1/m ∈ SymW (0, ∞) (max 1 t^{-2})` (with `mInv_symW` on `[1/8, ∞)`);
* `mDerivInv_symW`: `1/m' = t · A(t) ∈ SymW (0, ∞) (t · max 1 t^{-2})`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
  FormalResearch.SignUncertainty.FctCompD

lemma mQ_symW : ∃ K : ℕ → ℝ, SymW (Ioc (0 : ℝ) (1 / 8)) (fun _ => 1) K mQ := by
  choose B hB using fun j => CtMDeriv.bdd_iter_on_compact (isOpen_Ioo (a := (-1 / 4 : ℝ)) (b := 1 / 4)) contDiffOn_mQ
    (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) j
  exact ⟨_, SymW.of_bdd (b := 1 / 8) (by norm_num) isOpen_Ioo
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) contDiffOn_mQ
    (fun r x hx => hB r x ⟨hx.1.le, hx.2⟩)⟩

lemma mQ_ge : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ x ∈ Ioc (0 : ℝ) (1 / 8), m₀ ≤ mQ x := by
  have hc : ContinuousOn mQ (Icc (0 : ℝ) (1 / 8)) :=
    contDiffOn_mQ.continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨y₁, hy₁, h₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn ⟨0, by simp⟩ hc
  exact ⟨mQ y₁, mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [hy₁.1], by linarith [hy₁.2]⟩),
    fun x hx => h₁ ⟨hx.1.le, hx.2⟩⟩

/-- `1/m ∈ SymW (0, 1/8] (t^{-2})`. -/
lemma mInv_symW_Ioc : ∃ K : ℕ → ℝ, SymW (Ioc (0 : ℝ) (1 / 8)) (fun t => (t ^ 2)⁻¹) K (fun x => (uctM x)⁻¹) := by
  obtain ⟨K, hK⟩ := mQ_symW
  obtain ⟨m₀, hm₀, hge⟩ := mQ_ge
  have hinv := hK.inv hm₀ hge
  have hrp := SymW.rpow_gen (S := Ioc (0 : ℝ) (1 / 8)) (fun x hx => hx.1) 1 (-(2 : ℝ))
  have hmul := hrp.mul hinv
  refine ⟨_, (hmul.congr (U := Ioo 0 (1 / 4)) isOpen_Ioo
    (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) (g := fun x => (uctM x)⁻¹) (fun x hx => ?_)).of_le (fun x hx => ?_) (fun _ => le_rfl)⟩
  · have hx0 : 0 < x := hx.1
    simp only [uctM_eq_sq_mul_mQ hx0, one_mul, Real.rpow_neg hx0.le, Real.rpow_two, mul_inv]
  · have hx0 : 0 < x := hx.1
    simp only [abs_one, one_mul, mul_one]
    rw [Real.rpow_neg hx0.le, Real.rpow_two]

/-- `1/m ∈ SymW (0, ∞) (max 1 t^{-2})`. -/
theorem mInv_symW_all : ∃ K : ℕ → ℝ, SymW (Ioi (0 : ℝ)) wA K (fun x => (uctM x)⁻¹) := by
  obtain ⟨K₁, h₁⟩ := mInv_symW_Ioc
  obtain ⟨K₂, h₂⟩ := mInv_symW
  have h1 := h₁.of_le (w' := wA) (K' := K₁) (fun x hx => le_max_right _ _) (fun _ => le_rfl)
  have h2 := h₂.of_le (w' := wA) (K' := K₂) (fun x hx => le_max_left _ _) (fun _ => le_rfl)
  exact ⟨_, (h1.union h2).mono_set (fun x hx => by
    rcases le_or_gt x (1 / 8) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h.le)⟩

/-- `1/m' = t · A(t) ∈ SymW (0, ∞) (t · max 1 t^{-2})`. -/
theorem mDerivInv_symW : ∃ K : ℕ → ℝ, SymW (Ioi (0 : ℝ)) (fun x => |(1 : ℝ)| * x ^ (1 : ℝ) * wA x) K
    (fun x => (uctMderiv x)⁻¹) := by
  obtain ⟨K, hK⟩ := tauA_symW
  have hid := SymW.rpow_gen (S := Ioi (0 : ℝ)) (fun x hx => hx) 1 (1 : ℝ)
  refine ⟨_, (hid.mul hK).congr (U := Ioi 0) isOpen_Ioi subset_rfl (g := fun x => (uctMderiv x)⁻¹) (fun x hx => ?_)⟩
  have hx0 : 0 < x := hx
  have hmp := mPrime_pos hx0
  show 1 * x ^ (1 : ℝ) * tauA x = (uctMderiv x)⁻¹
  rw [uctMderiv_eq_mPrime hx0]
  unfold tauA
  rw [Real.rpow_one]
  field_simp

end FormalResearch.SignUncertainty.FctSym
