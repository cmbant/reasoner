module

public import FormalResearch.FourQubitEntropy.QVBlock.Symmetriser
public import FormalResearch.FourQubitEntropy.QVBlock.Blk

/-!
# Extending the block representation from generators (QV block calculus, T5)

If an invertible `C` satisfies `C Π_s = Blk(ρ₀ s) C` for generators `s` of `S_n`, then there is a
(unique) monoid homomorphism `ρ : S_n →* ∀ j, Matrix (mult j) (mult j)` with `ρ s = ρ₀ s` and
`C Π_g = Blk(ρ g) C` for all `g` (`exists_blockRep`).  `kronRep ρ p` is the tensor-product
representation `⊗_q ρ(·)(p q)` on the multiplicity space of the spin tuple `p`.
-/

@[expose] public section


open scoped Matrix BigOperators

namespace FormalResearch.FourQubitEntropy.QVBlock

set_option linter.unusedSectionVars false

/-- Intertwiners compose: `C A = B C` and `C A' = B' C` give `C (A A') = (B B') C`. -/
theorem intertwine_mul {R : Type*} [Semiring R] {α β : Type*} [Fintype α] [Fintype β]
    {C : Matrix α β R} {A A' : Matrix β β R} {B B' : Matrix α α R}
    (h : C * A = B * C) (h' : C * A' = B' * C) : C * (A * A') = (B * B') * C := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, h', ← Matrix.mul_assoc]

section
variable {𝕜 : Type*} [Field 𝕜]
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
variable {J : Type*} [Fintype J] [DecidableEq J] (dim : J → ℕ) {mult : J → ℕ}

/-- Uniqueness of block coordinates for an invertible `C`. -/
theorem blk_mul_right_cancel (hdim : ∀ j, 0 < dim j)
    (C : Matrix (Idx dim mult) (Fin n → σ) 𝕜) (Cinv : Matrix (Fin n → σ) (Idx dim mult) 𝕜)
    (hiC : C * Cinv = 1) {X Y : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜}
    (h : blk dim X * C = blk dim Y * C) : X = Y := by
  apply blk_injective dim hdim
  have := congrArg (· * Cinv) h
  simpa [Matrix.mul_assoc, hiC] using this

/-- **T5 (extension from generators).** -/
theorem exists_blockRep (hdim : ∀ j, 0 < dim j)
    (C : Matrix (Idx dim mult) (Fin n → σ) 𝕜) (Cinv : Matrix (Fin n → σ) (Idx dim mult) 𝕜)
    (hiC : C * Cinv = 1) {ι : Type*} (gens : ι → Equiv.Perm (Fin n))
    (hgen : Submonoid.closure (Set.range gens) = ⊤)
    (ρ0 : ι → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)
    (h0 : ∀ i, C * slotPerm 𝕜 (gens i) = blk dim (ρ0 i) * C) :
    ∃ ρ : Equiv.Perm (Fin n) →* (∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜),
      (∀ i, ρ (gens i) = ρ0 i) ∧ ∀ g, C * slotPerm 𝕜 g = blk dim (ρ g) * C := by
  let T : Submonoid (Equiv.Perm (Fin n)) :=
    { carrier := {g | ∃ X, C * slotPerm 𝕜 g = blk dim X * C}
      one_mem' := ⟨1, by rw [slotPerm_one, blk_one]; exact (Matrix.mul_one C).trans (Matrix.one_mul C).symm⟩
      mul_mem' := by
        rintro g h ⟨X, hX⟩ ⟨Y, hY⟩
        refine ⟨X * Y, ?_⟩
        rw [slotPerm_mul, blk_mul]
        exact intertwine_mul hX hY }
  have hT : T = ⊤ := by
    apply top_unique
    rw [← hgen, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨ρ0 i, h0 i⟩
  have hall : ∀ g, ∃ X, C * slotPerm 𝕜 g = blk dim X * C := fun g => by
    have : g ∈ T := by rw [hT]; trivial
    exact this
  choose r hr using hall
  have uniq : ∀ g X, C * slotPerm 𝕜 g = blk dim X * C → r g = X := fun g X hX =>
    blk_mul_right_cancel dim hdim C Cinv hiC ((hr g).symm.trans hX)
  refine ⟨{ toFun := r, map_one' := ?_, map_mul' := ?_ }, ?_, hr⟩
  · exact uniq 1 1 (by rw [slotPerm_one, blk_one]; exact (Matrix.mul_one C).trans (Matrix.one_mul C).symm)
  · intro g h
    apply uniq
    rw [slotPerm_mul, blk_mul]
    exact intertwine_mul (hr g) (hr h)
  · intro i
    exact uniq _ _ (h0 i)

variable {G : Type*} [Group G] {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The tensor-product representation `⊗_q ρ(·)(p q)` on the multiplicity space of `p`. -/
def kronRep (ρ : G →* (∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)) (p : Q → J) :
    G →* Matrix (∀ q, Fin (mult (p q))) (∀ q, Fin (mult (p q))) 𝕜 where
  toFun g := kronPi (fun q => ρ g (p q))
  map_one' := by simpa using kronPi_one (𝕜 := 𝕜) (Q := Q) (m := fun q => Fin (mult (p q)))
  map_mul' g h := by simp [kronPi_mul]

theorem kronRep_apply (ρ : G →* (∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜)) (p : Q → J) (g : G) :
    kronRep ρ p g = kronPi (fun q => ρ g (p q)) := rfl

end

end FormalResearch.FourQubitEntropy.QVBlock
