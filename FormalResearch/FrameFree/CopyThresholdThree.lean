import Mathlib
import FormalResearch.FrameFree.CopyThresholdNever
import FormalResearch.FrameFree.CopyThresholdMain

/-!
# Three independent spins: no separation at `k ≤ 4` (Paper P, `thm:copythreshold` (b), `n = 3`)

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved** (the finite group-theory check
`rev3`, `rev4` is an exact `decide +kernel` certificate); no `native_decide`, no new axiom.

For three independent spins every word is `(σ_0, σ_1, σ_2)`, and a word is real as soon as
`(σ_a)_a = (w σ_a⁻¹ v)_a` for copy permutations `w, v` (`wordVal_im_eq_zero_of_rev`).  Normalising `σ_0` to
`1` this asks that a pair `(x, y) ∈ S_k²` be simultaneously conjugate to `(x⁻¹, y⁻¹)`, which holds for every
pair exactly when `k ≤ 4` (`rev3`, `rev4`; for `k = 5` there are `12` non-reversible orbits, as in CT-2 of
`verify_copy_threshold.py`, and the reality of those invariants is the symmetric-power multiset count that is
not formalised).  Hence `k_*(π) ≥ 5` for three independent spins; the table value `6` (R6/R12 of the paper) needs
the `k = 5` count and is not formalised.

* `exists_wv_three`: three fibres, simultaneous reversibility `⟹ ∃ w v`.
* `not_mem_visibleCopies_independent_three`: `k ≤ 4 ⟹ k ∉ VisibleCopies π` (three independent spins).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.Twirls

variable {α κ γ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  [Fintype γ] [DecidableEq γ]

/-- Three fibres: simultaneous reversibility of pairs gives `w, v` with `w σ_a⁻¹ v = σ_a`. -/
theorem exists_wv_three (f : α → Equiv.Perm γ) (hα : Fintype.card α = 3)
    (hrev : ∀ x y : Equiv.Perm γ, ∃ t : Equiv.Perm γ, t * x * t⁻¹ = x⁻¹ ∧ t * y * t⁻¹ = y⁻¹) :
    ∃ w v : Equiv.Perm γ, ∀ a, w * (f a)⁻¹ * v = f a := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hxyz⟩ := Finset.card_eq_three.1
    (show (Finset.univ : Finset α).card = 3 by rw [Finset.card_univ]; exact hα)
  have hall : ∀ a, a = x ∨ a = y ∨ a = z := fun a => by
    have : a ∈ ({x, y, z} : Finset α) := by rw [← hxyz]; exact Finset.mem_univ a
    simpa using this
  obtain ⟨t, ht1, ht2⟩ := hrev ((f y)⁻¹ * f x) ((f z)⁻¹ * f x)
  refine ⟨f x * t, f x * t⁻¹, fun a => ?_⟩
  rcases hall a with h | h | h <;> rw [h]
  · simp
  · calc f x * t * (f y)⁻¹ * (f x * t⁻¹)
        = f x * (t * ((f y)⁻¹ * f x) * t⁻¹) := by simp [mul_assoc]
      _ = f y := by rw [ht1]; simp [mul_assoc]
  · calc f x * t * (f z)⁻¹ * (f x * t⁻¹)
        = f x * (t * ((f z)⁻¹ * f x) * t⁻¹) := by simp [mul_assoc]
      _ = f z := by rw [ht2]; simp [mul_assoc]

set_option maxRecDepth 100000 in
/-- Every pair of permutations of `3` copies is simultaneously conjugate to its inverse pair. -/
theorem rev3 : ∀ x y : Equiv.Perm (Fin 3), ∃ t : Equiv.Perm (Fin 3),
    t * x * t⁻¹ = x⁻¹ ∧ t * y * t⁻¹ = y⁻¹ := by decide +kernel

set_option maxRecDepth 100000 in
/-- Every pair of permutations of `4` copies is simultaneously conjugate to its inverse pair. -/
theorem rev4 : ∀ x y : Equiv.Perm (Fin 4), ∃ t : Equiv.Perm (Fin 4),
    t * x * t⁻¹ = x⁻¹ ∧ t * y * t⁻¹ = y⁻¹ := by decide +kernel

/-- **Three independent spins: the twirls of `ψ^{⊗k}` and `(Θψ)^{⊗k}` coincide for `k ≤ 4`.** -/
theorem not_mem_visibleCopies_independent_three {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ]
    [DecidableEq κ] (π : α → κ) (hπ : Function.Injective π)
    (hα : Fintype.card α = 3) {k : ℕ} (hk : k ≤ 4) : k ∉ VisibleCopies π := by
  by_cases hk2 : k ≤ 2
  · exact not_mem_visibleCopies_independent hπ hk2
  · rintro ⟨ψ, -, hψ⟩
    refine hψ ((twirlsCoincide_iff π _).2 fun s hs => ?_)
    refine wordVal_im_eq_zero_of_rev π hπ (fun f => exists_wv_three f hα ?_) s hs ψ
    have : k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl
    · exact rev3
    · exact rev4

end FormalResearch.FrameFree.Twirls
