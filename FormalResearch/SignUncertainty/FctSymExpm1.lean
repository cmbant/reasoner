/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymChain

/-!
# `e^f - 1` of a small symbol, and the raw form of `SymW` bounds (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b): `e^{v} - 1` with `v = O(τ₁²)`, and `r₀ - 1`.

* `SymW.raw_bound`: `|x^r ∂^r f(x)| ≤ K_r w(x)` for `x ∈ S`;
* `abs_exp_sub_one_le_mul`: `|e^y - 1| ≤ |y| e^{|y|}`;
* `symW_exp_sub_one`: `f ∈ SymW S w K`, `w ≤ B` give `e^f - 1 ∈ SymW S w K'` with `K'` depending only on `K, B`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff

namespace FormalResearch.SignUncertainty.FctSym

lemma SymW.raw_bound {S : Set ℝ} {w : ℝ → ℝ} {K : ℕ → ℝ} {f : ℝ → ℝ} (h : SymW S w K f) (r : ℕ) {x : ℝ} (hx : x ∈ S) :
    |x ^ r * iteratedDeriv r f x| ≤ K r * w x := by
  have hxp := h.pos x hx
  have hxr : 0 < x ^ r := pow_pos hxp r
  rw [abs_mul, abs_of_pos hxr]
  calc x ^ r * |iteratedDeriv r f x| ≤ x ^ r * (K r * w x * (x ^ r)⁻¹) := by gcongr; exact h.bound r x hx
    _ = K r * w x := by field_simp

lemma abs_exp_sub_one_le_mul (y : ℝ) : |Real.exp y - 1| ≤ |y| * Real.exp |y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp y])]
    have h1 := Real.add_one_le_exp (-y)
    rw [Real.exp_neg] at h1
    have hp := Real.exp_pos y
    have : (1 - y) * Real.exp y ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h1 hp.le
      rw [inv_mul_cancel₀ hp.ne'] at this
      linarith
    nlinarith
  · rw [abs_of_nonpos h]
    have h1 := Real.add_one_le_exp y
    have h2 : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr h
    rw [abs_of_nonpos (by linarith)]
    have h3 : 1 ≤ Real.exp (-y) := Real.one_le_exp (by linarith)
    nlinarith [Real.exp_pos y]

lemma abs_iteratedDeriv_exp_sub_one_le (j : ℕ) (y : ℝ) :
    |iteratedDeriv j (fun y : ℝ => Real.exp y - 1) y| ≤ Real.exp |y| + 1 := by
  cases j with
  | zero =>
    simp only [iteratedDeriv_zero]
    calc |Real.exp y - 1| ≤ |Real.exp y| + |1| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_pos (Real.exp_pos y)]
        have := Real.exp_le_exp.mpr (le_abs_self y)
        rw [abs_one]; linarith
  | succ n =>
    have hd : deriv (fun y : ℝ => Real.exp y - 1) = Real.exp := by
      funext z; simp
    rw [iteratedDeriv_succ', hd, iteratedDeriv_eq_iterate, Real.iter_deriv_exp, abs_of_pos (Real.exp_pos y)]
    have := Real.exp_le_exp.mpr (le_abs_self y)
    linarith

/-- **`e^f - 1` of a symbol `f` with `w ≤ B`** (constants depend only on `K` and `B`). -/
theorem symW_exp_sub_one {S : Set ℝ} {w : ℝ → ℝ} {K : ℕ → ℝ} {f : ℝ → ℝ} {B : ℝ} (hf : SymW S w K f)
    (hwB : ∀ x ∈ S, w x ≤ B) :
    SymW S w (compK (K 0 * Real.exp (K 0 * B)) (fun _ => Real.exp (K 0 * B) + 1) (fun k => K (k + 1)) B)
      (fun x => Real.exp (f x) - 1) := by
  have hK0 := hf.K_nonneg 0
  have hB0 : ∀ x ∈ S, 0 ≤ B := fun x hx => (hf.w_nonneg x hx).trans (hwB x hx)
  have hfb : ∀ x ∈ S, |f x| ≤ K 0 * B := by
    intro x hx
    have := hf.bound 0 x hx
    simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hwB x hx) hK0)
  refine SymW.comp_smooth (Φ := fun y : ℝ => Real.exp y - 1) (V := univ) (P := fun _ => Real.exp (K 0 * B) + 1)
    (L := K 0 * Real.exp (K 0 * B)) hf isOpen_univ
    ((Real.contDiff_exp.sub contDiff_const).contDiffOn) (fun _ _ => mem_univ _) (fun j x hx => ?_)
    (fun _ => by positivity) hwB (by positivity) (fun x hx => ?_)
  · refine (abs_iteratedDeriv_exp_sub_one_le j _).trans ?_
    linarith [Real.exp_le_exp.mpr (hfb x hx)]
  · refine (abs_exp_sub_one_le_mul (f x)).trans ?_
    have h1 : |f x| ≤ K 0 * w x := by
      have := hf.bound 0 x hx
      simpa using this
    have h2 := Real.exp_le_exp.mpr (hfb x hx)
    have h3 : 0 ≤ K 0 * w x := mul_nonneg hK0 (hf.w_nonneg x hx)
    calc |f x| * Real.exp |f x| ≤ (K 0 * w x) * Real.exp (K 0 * B) := by
          gcongr
      _ = _ := by ring

end FormalResearch.SignUncertainty.FctSym
