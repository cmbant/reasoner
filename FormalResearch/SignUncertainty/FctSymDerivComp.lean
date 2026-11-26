/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymChain

/-!
# Composition bounds that use only the derivative of the inner function (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b) (`fct:bump-sym-check`).

`comp_deriv_bound`: `|∂^i (Φ ∘ f)(x)| ≤ M_i om(x) x^{-i}` for `x ∈ S`, where only the derivative `f'` of the inner function is
a symbol on `S` (`|∂^k f'| ≤ A_k x^{-(k+1)}`) and the outer derivatives are controlled by a (possibly unbounded) scale `om`:
`|Φ^{(j)}(f x)| ≤ P_j om(x)`.  This is the version of `SymW.comp_smooth` needed for unbounded inner functions such as `m(t)`
(`m(t)^{-1}`, `m(t)^{3/2}` for `t ≥ 1/8`): the order-`0` size of `f` is never used.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff

namespace FormalResearch.SignUncertainty.FctSym

/-- **Composition with an inner function known only through its derivative.** -/
theorem comp_deriv_bound {S U : Set ℝ} (hU : IsOpen U) (hSU : S ⊆ U) (hpos : ∀ x ∈ S, 0 < x)
    {f Φ : ℝ → ℝ} {V : Set ℝ} {A P : ℕ → ℝ} {om : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hV : IsOpen V) (hΦ : ContDiffOn ℝ ∞ Φ V) (hfV : ∀ x ∈ U, f x ∈ V)
    (hA : ∀ k x, x ∈ S → |iteratedDeriv k (deriv f) x| ≤ A k * 1 * (x ^ (k + 1))⁻¹) (hA0 : ∀ k, 0 ≤ A k)
    (hP0 : ∀ j, 0 ≤ P j) (hom : ∀ x ∈ S, 0 ≤ om x)
    (hP : ∀ j x, x ∈ S → |iteratedDeriv j Φ (f x)| ≤ P j * om x) (i : ℕ) :
    ∀ x ∈ S, |iteratedDeriv i (fun y => Φ (f y)) x| ≤ chainM P (fun _ => 0) A 1 i 0 * om x * (x ^ i)⁻¹ := by
  have hcont : ContinuousOn f U := hf.continuousOn
  have hF : ∀ j, ContDiffOn ℝ ∞ (fun x => iteratedDeriv j Φ (f x)) U := fun j =>
    (contDiffOn_iteratedDeriv_of_isOpen hV hΦ j).comp hf hfV
  have ha : ContDiffOn ℝ ∞ (deriv f) U := hf.deriv_of_isOpen hU (by simp)
  have hderiv : ∀ j, ∀ x ∈ U, deriv (fun x => iteratedDeriv j Φ (f x)) x =
      deriv f x * (iteratedDeriv (j + 1) Φ (f x) + (fun _ : ℕ => (0 : ℝ)) j * iteratedDeriv j Φ (f x)) := by
    intro j y hy
    have h1 : HasDerivAt f (deriv f y) y :=
      ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)).hasDerivAt
    have h2 : HasDerivAt (iteratedDeriv j Φ) (iteratedDeriv (j + 1) Φ (f y)) (f y) := by
      have hd := ((contDiffOn_iteratedDeriv_of_isOpen hV hΦ j).differentiableOn (by simp)).differentiableAt
        (hV.mem_nhds (hfV y hy))
      rw [iteratedDeriv_succ]; exact hd.hasDerivAt
    have := (h2.comp y h1).deriv
    simp only [Function.comp_def] at this
    rw [this]; ring
  have hch := chain_bound (S := S) (U := U) hU hSU hpos (F := fun j x => iteratedDeriv j Φ (f x))
    (a := deriv f) (w := fun _ => 1) (om := om) (κ := fun _ => 0) (A := A) (P := P) (B := 1)
    hF ha hderiv hA (fun x _ => ⟨zero_le_one, le_rfl⟩) hA0 hP0 hom (fun j x hx => hP j x hx) i
  intro x hx
  exact hch 0 x hx i le_rfl

end FormalResearch.SignUncertainty.FctSym
