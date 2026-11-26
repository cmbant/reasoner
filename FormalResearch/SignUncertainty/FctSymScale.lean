/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymChain
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Scale-invariant composition `g ∘ f` (calculus for `fct:bump-sym-check`, the change of variable `L ↦ τ₀(L̃)`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`): `∂_L = m'(t)^{-1} ∂_t`,
`t = τ₀(L̃)`, so that a bound `|g^{(j)}(t)| ≤ P_j ω(t) t^{-j}` of the *t-symbol* class transfers to the *L-symbol* class with
constants that do not depend on any parameter of `g`.

For `f > 0` smooth put `a = f'/f` (the logarithmic derivative; `a = τ₀'/τ₀` for `f = τ₀`).  With
`F_j = (t^j g^{(j)}) ∘ f` one has `F_j' = a (F_{j+1} + j F_j)`, so `chain_bound_lam` gives the derivative bounds of all
orders of `g ∘ f = F_0`:

* `comp_scale_bound`: if `|a^{(k)}| ≤ A_k lam^{k+1}` and `|f^j g^{(j)}(f)| ≤ P_j om` on `S`, then
  `|(g ∘ f)^{(i)}| ≤ chainM(i) om lam^i` on `S`; the constant `chainM` depends only on `P`, `A`.

`lam x = x⁻¹` for a scale-invariant `a` (`a ≈ 1/(2x)`), and `lam = max 1 x⁻¹` when `a` stays bounded for large `x`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff

namespace FormalResearch.SignUncertainty.FctSym

/-- The family `F_j = f^j · g^{(j)}(f)` of the scale-invariant chain rule. -/
noncomputable def scaleF (f g : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ := f x ^ j * iteratedDeriv j g (f x)

lemma scaleF_zero (f g : ℝ → ℝ) : scaleF f g 0 = fun x => g (f x) := by
  funext x; simp [scaleF]

lemma contDiffOn_scaleF {U : Set ℝ} {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hfpos : ∀ x ∈ U, 0 < f x)
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (j : ℕ) : ContDiffOn ℝ ∞ (scaleF f g j) U := by
  unfold scaleF
  exact (hf.pow j).mul ((contDiffOn_iteratedDeriv_of_isOpen isOpen_Ioi hg j).comp hf fun x hx => hfpos x hx)

lemma deriv_scaleF {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hfpos : ∀ x ∈ U, 0 < f x)
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (j : ℕ) {x : ℝ} (hx : x ∈ U) :
    deriv (scaleF f g j) x =
      (deriv f x / f x) * (scaleF f g (j + 1) x + (j : ℝ) * scaleF f g j x) := by
  have hfx : HasDerivAt f (deriv f x) x :=
    ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hG : HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g (f x)) (f x) := by
    have hd := ((contDiffOn_iteratedDeriv_of_isOpen isOpen_Ioi hg j).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds (hfpos x hx))
    rw [iteratedDeriv_succ]; exact hd.hasDerivAt
  have h := (HasDerivAt.fun_pow hfx j).mul (hG.comp x hfx)
  have hne : f x ≠ 0 := (hfpos x hx).ne'
  have e : deriv (scaleF f g j) x = ↑j * f x ^ (j - 1) * deriv f x * iteratedDeriv j g (f x) +
      f x ^ j * (iteratedDeriv (j + 1) g (f x) * deriv f x) := by
    unfold scaleF
    exact h.deriv
  rw [e]
  unfold scaleF
  cases j with
  | zero => simp; field_simp
  | succ j =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [pow_succ]
    field_simp
    ring

/-- **Scale-invariant composition bound** (see the module docstring).  `g` smooth on `(0, ∞)`, `f > 0` smooth on an open
`U ⊇ S`, `a = f'/f` with `|a^{(k)}| ≤ A_k lam^{k+1}` on `S`, and `|f^j g^{(j)}(f)| ≤ P_j om` on `S` for all `j`.  Then
`|(g ∘ f)^{(i)}| ≤ chainM P (j ↦ j) A 1 r 0 · om · lam^i` for `i ≤ r`. -/
theorem comp_scale_bound {S U : Set ℝ} (hU : IsOpen U) (hSU : S ⊆ U) {f g lam om : ℝ → ℝ} {P A : ℕ → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hfpos : ∀ x ∈ U, 0 < f x) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (ha : ∀ k x, x ∈ S → |iteratedDeriv k (fun y => deriv f y / f y) x| ≤ A k * lam x ^ (k + 1))
    (hA : ∀ k, 0 ≤ A k) (hP : ∀ j, 0 ≤ P j) (hom : ∀ x ∈ S, 0 ≤ om x) (hlam : ∀ x ∈ S, 0 ≤ lam x)
    (hbase : ∀ j, ∀ x ∈ S, |f x ^ j * iteratedDeriv j g (f x)| ≤ P j * om x) (r : ℕ) :
    ∀ x ∈ S, ∀ i ≤ r, |iteratedDeriv i (fun y => g (f y)) x| ≤
      chainM P (fun j => (j : ℝ)) A 1 r 0 * om x * lam x ^ i := by
  intro x hx i hi
  have haU : ContDiffOn ℝ ∞ (fun y => deriv f y / f y) U :=
    (hf.deriv_of_isOpen hU (by simp)).div hf fun y hy => (hfpos y hy).ne'
  have := chain_bound_lam hU hSU (F := scaleF f g) (a := fun y => deriv f y / f y) (w := fun _ => 1) (om := om)
    (lam := lam) (κ := fun j => (j : ℝ)) (A := A) (P := P) (B := 1) (fun j => contDiffOn_scaleF hf hfpos hg j) haU
    (fun j y hy => deriv_scaleF hU hf hfpos hg j hy) (fun k y hy => by simpa using ha k y hy)
    (fun _ _ => ⟨zero_le_one, le_rfl⟩) hA hP hom hlam (fun j y hy => by simpa [scaleF] using hbase j y hy) r 0 x hx i hi
  simpa [scaleF_zero] using this

/-- info: 'FormalResearch.SignUncertainty.FctSym.comp_scale_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comp_scale_bound

end FormalResearch.SignUncertainty.FctSym
