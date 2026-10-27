import Mathlib
import FormalResearch.FrameFree.CopyThresholdWords

/-!
# At most two independent frames: the twirls never separate (Paper P, `thm:copythreshold` (b), `k_* = ∞`)

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved** (no hypothesis, no new axiom).

For independent frames (`π` injective) on `n ≤ 2` qubits, every word is `s = (a ↦ σ_a)`, a permutation of the
copies for each qubit.  The value `Tr(P_s ρ^{⊗k})` of a *pure* state is unchanged when `s` is multiplied by a
copy permutation on either side (`wordVal_diag_mul`, `wordVal_mul_diag`), and `conj` of it is the value of
`s⁻¹`.  For `n ≤ 2` one finds `w, v` with `w σ_a⁻¹ v = σ_a` for every `a` (this is the fact that a permutation
and its inverse are conjugate, `Equiv.Perm.isConj_iff_cycleType_eq`), so the value of `s⁻¹` equals that of `s`:
all word values are real for every number `k` of copies.

* `exists_fiberPerm`: a fibre-preserving permutation of `α × γ` is `prodCongrRight f`.
* `wordVal_im_eq_zero_of_card_le_two`: all block-preserving word values of a pure state are real.
* `twirlsCoincide_of_card_le_two`: for every `k` and every pure `ψ` the twirls of `ψ^{⊗k}` and `(Θψ)^{⊗k}`
  agree, i.e. `k_*(ψ, π) = ∞` (the case `n ≤ 2` of the table of `thm:copythreshold`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.Twirls

variable {α κ γ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  [Fintype γ] [DecidableEq γ]

/-- A permutation of `α × γ` preserving the first coordinate is a family of copy permutations. -/
theorem exists_fiberPerm (s : Equiv.Perm (α × γ)) (h : ∀ q, (s q).1 = q.1) :
    ∃ f : α → Equiv.Perm γ, s = Equiv.prodCongrRight f := by
  have hs : ∀ a c, s (a, c) = (a, (s (a, c)).2) := fun a c => Prod.ext (h (a, c)) rfl
  have hs' : ∀ a c, s.symm (a, c) = (a, (s.symm (a, c)).2) := fun a c =>
    Prod.ext (by have := h (s.symm (a, c)); simpa using this.symm) rfl
  refine ⟨fun a => ⟨fun c => (s (a, c)).2, fun c => (s.symm (a, c)).2, fun c => ?_, fun c => ?_⟩, ?_⟩
  · show (s.symm (a, (s (a, c)).2)).2 = c
    rw [← hs a c, s.symm_apply_apply]
  · show (s (a, (s.symm (a, c)).2)).2 = c
    rw [← hs' a c, s.apply_symm_apply]
  · ext q
    · simp [h q]
    · rfl

theorem prodCongrRight_inv (f : α → Equiv.Perm γ) :
    (Equiv.prodCongrRight f)⁻¹ = Equiv.prodCongrRight (fun a => (f a)⁻¹) := by
  ext q <;> simp [Equiv.Perm.inv_def]

theorem diag_mul_prodCongrRight (w : Equiv.Perm γ) (f : α → Equiv.Perm γ) :
    diagPerm α w * Equiv.prodCongrRight f = Equiv.prodCongrRight (fun a => w * f a) := by
  ext q <;> simp [diagPerm]

theorem prodCongrRight_mul_diag (w : Equiv.Perm γ) (f : α → Equiv.Perm γ) :
    Equiv.prodCongrRight f * diagPerm α w = Equiv.prodCongrRight (fun a => f a * w) := by
  ext q <;> simp [diagPerm]

/-- A permutation is conjugate to its inverse. -/
theorem exists_conj_inv (x : Equiv.Perm γ) : ∃ t : Equiv.Perm γ, t * x * t⁻¹ = x⁻¹ := by
  have : IsConj x x⁻¹ := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, Equiv.Perm.cycleType_inv]
  exact isConj_iff.1 this

/-- For at most two fibres, `σ_a = w σ_a⁻¹ v` for suitable copy permutations `w, v`. -/
theorem exists_wv (f : α → Equiv.Perm γ) (hα : Fintype.card α ≤ 2) :
    ∃ w v : Equiv.Perm γ, ∀ a, w * (f a)⁻¹ * v = f a := by
  rcases Nat.lt_or_ge (Fintype.card α) 2 with h | h
  · have h1 : Fintype.card α ≤ 1 := by omega
    rcases isEmpty_or_nonempty α with he | ⟨⟨a0⟩⟩
    · exact ⟨1, 1, fun a => (he.false a).elim⟩
    · have hall : ∀ a, a = a0 := fun a => Fintype.card_le_one_iff.1 h1 a a0
      refine ⟨f a0, f a0, fun a => ?_⟩
      rw [hall a]; simp
  · have h2 : Fintype.card α = 2 := le_antisymm hα h
    obtain ⟨x, y, hxy, hxy'⟩ := (Finset.card_eq_two (s := (Finset.univ : Finset α))).1 (by rw [Finset.card_univ]; exact h2)
    have hall : ∀ a, a = x ∨ a = y := fun a => by
      have : a ∈ ({x, y} : Finset α) := by rw [← hxy']; exact Finset.mem_univ a
      simpa using this
    obtain ⟨t, ht⟩ := exists_conj_inv ((f y)⁻¹ * f x)
    refine ⟨f x * t, f x * t⁻¹, fun a => ?_⟩
    rcases hall a with h | h <;> rw [h]
    · simp [mul_assoc]
    · calc f x * t * (f y)⁻¹ * (f x * t⁻¹)
          = f x * (t * ((f y)⁻¹ * f x) * t⁻¹) := by simp [mul_assoc]
        _ = f y := by rw [ht]; simp [mul_assoc]

/-- **All word values of a pure state are real for `n ≤ 2` independent frames.** -/
theorem wordVal_im_eq_zero_of_card_le_two (π : α → κ) (hπ : Function.Injective π)
    (hα : Fintype.card α ≤ 2) (s : Equiv.Perm (α × γ)) (hs : BlockPres π s) (ψ : (α → Fin 2) → ℂ) :
    (wordVal γ s (pureOp ψ)).im = 0 := by
  obtain ⟨f, rfl⟩ := exists_fiberPerm s fun q => hπ (hs q)
  obtain ⟨w, v, hwv⟩ := exists_wv f hα
  have h1 : wordVal γ (Equiv.prodCongrRight f)⁻¹ (pureOp ψ) = wordVal γ (Equiv.prodCongrRight f) (pureOp ψ) := by
    have : Equiv.prodCongrRight f =
        diagPerm α w * (Equiv.prodCongrRight f)⁻¹ * diagPerm α v := by
      rw [prodCongrRight_inv, diag_mul_prodCongrRight, prodCongrRight_mul_diag]
      congr 1; ext a : 1; exact (hwv a).symm
    conv_rhs => rw [this]
    rw [wordVal_mul_diag, wordVal_diag_mul]
  rw [← Complex.conj_eq_iff_im, conj_wordVal _ (pureOp_isHermitian ψ), h1]

/-- **`k_*(ψ, π) = ∞` for at most two independent frames**: for every number `k` of copies and every pure
state, the twirls of `ψ^{⊗k}` and `(Θψ)^{⊗k}` over `K_π` coincide. -/
theorem twirlsCoincide_of_card_le_two (π : α → κ) (hπ : Function.Injective π)
    (hα : Fintype.card α ≤ 2) (ψ : (α → Fin 2) → ℂ) : TwirlsCoincide π γ (pureOp ψ) :=
  (twirlsCoincide_iff π _).2 fun s hs => wordVal_im_eq_zero_of_card_le_two π hπ hα s hs ψ

end FormalResearch.FrameFree.Twirls
