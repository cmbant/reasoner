/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymChain
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Reciprocals, unions and compact pieces of the symbol classes `SymW` (calculus for `fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`), the quotients
`1/m'(t)`, `1/mD` that occur in `∂_L = m'(t)^{-1} ∂_t`.

* `SymW.inv`: `f ∈ SymW S 1 K` with `f ≥ c > 0` on `S` gives `1/f ∈ SymW S 1 K'` (`K'` explicit);
* `SymW.of_bdd`: a function smooth near `[0, b]` is in `SymW (Ioc 0 b) 1`;
* `SymW.union`: the two pieces of a symbol on `S ∪ S'` with the same weight.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Nat

namespace FormalResearch.SignUncertainty.FctSym

lemma iteratedDeriv_inv_of_pos (j : ℕ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv j (fun y : ℝ => y⁻¹) y = (-1) ^ j * (j ! : ℝ) * (y ^ (j + 1))⁻¹ := by
  have := iteratedDerivWithin_one_div (𝕜 := ℝ) j (isOpen_Ioi (a := (0 : ℝ))) (mem_Ioi.mpr hy)
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi (mem_Ioi.mpr hy)] at this
  simp only [one_div] at this
  rw [this]
  have : y ^ (-1 - (j : ℤ)) = (y ^ (j + 1))⁻¹ := by
    rw [show (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [this]

/-- **Reciprocal of a symbol that stays away from `0`.** -/
theorem SymW.inv {S : Set ℝ} {K : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ} (hf : SymW S (fun _ => 1) K f) (hc : 0 < c)
    (hge : ∀ x ∈ S, c ≤ f x) :
    SymW S (fun _ => 1) (compK c⁻¹ (fun j => (j ! : ℝ) / c ^ (j + 1)) (fun k => K (k + 1)) 1) (fun x => (f x)⁻¹) := by
  have hΦ : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Ioi 0) := (contDiffOn_inv ℝ).mono (fun y hy => (ne_of_gt hy : y ≠ 0))
  refine SymW.comp_smooth (Φ := fun y : ℝ => y⁻¹) (V := Ioi 0) (P := fun j => (j ! : ℝ) / c ^ (j + 1)) (B := 1)
    (L := c⁻¹) hf isOpen_Ioi hΦ (fun x hx => lt_of_lt_of_le hc (hge x hx)) (fun j x hx => ?_)
    (fun j => by positivity) (fun _ _ => le_rfl) (by positivity) (fun x hx => ?_)
  · have hfx := hge x hx
    rw [iteratedDeriv_inv_of_pos j (lt_of_lt_of_le hc hfx), abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, Nat.abs_cast, abs_of_pos (inv_pos.mpr (pow_pos (lt_of_lt_of_le hc hfx) _)), div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact inv_anti₀ (pow_pos hc _) (pow_le_pow_left₀ hc.le (hge x hx) _)
  · simp only [mul_one]
    rw [abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hc (hge x hx)))]
    exact inv_anti₀ hc (hge x hx)

/-- A function smooth on an open set containing `(0, b]` with bounded derivatives there is a symbol of weight `1`. -/
theorem SymW.of_bdd {b : ℝ} (hb : 0 < b) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hbU : Ioc 0 b ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) {B : ℕ → ℝ} (hB : ∀ r, ∀ x ∈ Ioc 0 b, |iteratedDeriv r f x| ≤ B r) :
    SymW (Ioc 0 b) (fun _ => 1) (fun r => |B r| * b ^ r) f where
  pos := fun x hx => hx.1
  smooth := ⟨U, hU, hbU, hf⟩
  K_nonneg := fun r => by positivity
  w_nonneg := fun _ _ => zero_le_one
  bound := fun r x hx => by
    have hx0 := hx.1
    have h1 := (hB r x hx).trans (le_abs_self _)
    have h2 : b ^ r * (x ^ r)⁻¹ ≥ 1 := by
      rw [← div_eq_mul_inv, ge_iff_le, one_le_div (pow_pos hx0 _)]
      exact pow_le_pow_left₀ hx0.le hx.2 _
    calc |iteratedDeriv r f x| ≤ |B r| := h1
      _ = |B r| * 1 := (mul_one _).symm
      _ ≤ |B r| * (b ^ r * (x ^ r)⁻¹) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |B r| * b ^ r * 1 * (x ^ r)⁻¹ := by ring

/-- The union of two sets on which `f` is a symbol of the same weight. -/
theorem SymW.union {S S' : Set ℝ} {w : ℝ → ℝ} {K K' : ℕ → ℝ} {f : ℝ → ℝ} (h : SymW S w K f) (h' : SymW S' w K' f) :
    SymW (S ∪ S') w (fun r => max (K r) (K' r)) f where
  pos := fun x hx => hx.elim (h.pos x) (h'.pos x)
  smooth := by
    obtain ⟨U, hU, hSU, hfU⟩ := h.smooth
    obtain ⟨U', hU', hSU', hfU'⟩ := h'.smooth
    exact ⟨U ∪ U', hU.union hU', union_subset_union hSU hSU', hfU.union_of_isOpen hfU' hU hU'⟩
  K_nonneg := fun r => (h.K_nonneg r).trans (le_max_left _ _)
  w_nonneg := fun x hx => hx.elim (h.w_nonneg x) (h'.w_nonneg x)
  bound := fun r x hx => by
    have hxp : 0 < x := hx.elim (h.pos x) (h'.pos x)
    have hinv : 0 ≤ (x ^ r)⁻¹ := inv_nonneg.mpr (pow_nonneg hxp.le r)
    rcases hx with hx | hx
    · refine (h.bound r x hx).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (h.w_nonneg x hx)) hinv
    · refine (h'.bound r x hx).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (h'.w_nonneg x hx)) hinv

end FormalResearch.SignUncertainty.FctSym
