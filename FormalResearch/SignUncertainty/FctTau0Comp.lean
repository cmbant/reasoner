/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctTauA

/-!
# Composition `g ∘ τ₀(· - s)`: `t`-symbol bounds become `L`-symbol bounds with absolute constants (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`): `t = τ₀(L̃)`, `L̃ = L - s`,
`∂_L = m'(t)^{-1} ∂_t`.

* `comp_tau0_shift`: if `g` is smooth on `(0, ∞)` and `|t^j g^{(j)}(t)| ≤ P_j om` at `t = τ₀(x - s)` for `x ≥ x₀`
  (`|s| ≤ x₀/2`), then `|∂_x^r g(τ₀(x - s))| ≤ chainM(P; r) · om(x) · lam(x)^r`, `lam x = max 1 x⁻¹`.  The constant `chainM P` depends only on
  the `t`-symbol constants `P` (and the absolute constants of `tau0_logDeriv_symbol`), not on `s`, `x₀`, `g`'s other parameters.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

lemma lamL_shift_le {x₀ s x : ℝ} (hx₀ : 0 < x₀) (hs : |s| ≤ x₀ / 2) (hx : x₀ ≤ x) :
    lamL (x - s) ≤ 2 * lamL x := by
  have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
  have hs2 := (abs_le.mp hs).2
  have hxs : x / 2 ≤ x - s := by linarith
  have hxs0 : 0 < x - s := by linarith
  have h1 : (x - s)⁻¹ ≤ 2 * x⁻¹ := by
    rw [show 2 * x⁻¹ = (x / 2)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) hxs
  have h2 : (1 : ℝ) ≤ lamL x := one_le_lamL x
  have h3 : x⁻¹ ≤ lamL x := le_max_right _ _
  unfold lamL at *
  refine max_le (by linarith) ?_
  linarith

/-- **`g ∘ τ₀(· - s)` from the `t`-symbol bounds of `g`** (see the module docstring). -/
theorem comp_tau0_shift : ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧ ∀ {x₀ s : ℝ} {g om : ℝ → ℝ} {P : ℕ → ℝ},
    0 < x₀ → |s| ≤ x₀ / 2 → ContDiffOn ℝ ∞ g (Ioi 0) → (∀ j, 0 ≤ P j) → (∀ x, x₀ ≤ x → 0 ≤ om x) →
    (∀ j, ∀ x, x₀ ≤ x → |tau0 (x - s) ^ j * iteratedDeriv j g (tau0 (x - s))| ≤ P j * om x) →
    ∀ r : ℕ, ∀ x, x₀ ≤ x →
      |iteratedDeriv r (fun y => g (tau0 (y - s))) x| ≤ chainM P (fun j => (j : ℝ)) A 1 r 0 * om x * lamL x ^ r := by
  obtain ⟨A, hA0, hA⟩ := tau0_logDeriv_symbol
  refine ⟨fun k => 2 ^ (k + 1) * A k, fun k => by have := hA0 k; positivity, ?_⟩
  intro x₀ s g om P hx₀ hs hg hP hom hbase r x hx
  have hU : IsOpen (Ioi s) := isOpen_Ioi
  have hxs : ∀ y, x₀ ≤ y → s < y := fun y hy => by linarith [(abs_le.mp hs).2]
  have hf : ContDiffOn ℝ ∞ (fun y => tau0 (y - s)) (Ioi s) :=
    contDiffOn_tau0.comp (contDiffOn_id.sub contDiffOn_const) (fun y hy => sub_pos.mpr hy)
  have hfpos : ∀ y ∈ Ioi s, 0 < tau0 (y - s) := fun y hy => tau0_pos (sub_pos.mpr hy)
  have hfun : (fun y => deriv (fun y => tau0 (y - s)) y / tau0 (y - s)) =
      fun y => (fun z => deriv tau0 z / tau0 z) (y - s) := by
    funext y; rw [deriv_comp_sub_const]
  refine comp_scale_bound hU (S := Ici x₀) (fun y hy => hxs y hy) hf hfpos hg
    (fun k y hy => ?_) (fun k => by have := hA0 k; positivity) hP (fun y hy => hom y hy)
    (fun y _ => lamL_nonneg y) (fun j y hy => hbase j y hy) r x hx r le_rfl
  have hy0 : 0 < y - s := by linarith [hxs y hy]
  have e := iteratedDeriv_comp_sub_const (n := k) (f := fun z => deriv tau0 z / tau0 z) (s := s)
  rw [hfun, e]
  refine (hA k (y - s) hy0).trans ?_
  have := lamL_shift_le hx₀ hs hy
  calc A k * lamL (y - s) ^ (k + 1) ≤ A k * (2 * lamL y) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (lamL_nonneg _) this _) (hA0 k)
    _ = 2 ^ (k + 1) * A k * lamL y ^ (k + 1) := by rw [mul_pow]; ring

/-- info: 'FormalResearch.SignUncertainty.FctSym.comp_tau0_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comp_tau0_shift

end FormalResearch.SignUncertainty.FctSym
