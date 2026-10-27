import Mathlib
import FormalResearch.QIB.BlockDecomp

/-!
# Block coordinates: a non-vacuity example and the rank-one reduction

Namespace `FormalResearch.QIB`.  Claim class: **proved** (finite linear algebra).

* `isotypicInvariants_trivial`: the isotypic hypothesis `IsotypicInvariants` holds for the trivial group
  acting on one sector with a one-dimensional carrier (so the hypothesis is satisfiable, and
  `invErr_eq` specialises there to the ordinary Helstrom formula).
* `tau_eq_smul_vecMulVec_of_kernel`, `rank_tau_le_one_of_kernel`: **the abstract core of the stabiliser
  proof of `prop:twoqubits`.**  If in sector `λ` the slices `v_{λ·b}` all lie in the kernel of an operator
  `K` on the carrier whose kernel is the line spanned by `k`, then the multiplicity block
  `τ_λ(v)` is `‖k‖² · |c⟩⟨c|`, of rank at most one.  For two qubits under collective `SU(2)` one would
  take `K` the generator of the stabiliser of `x = x₁ + x_s` (the vector `a ≠ 0` of `x₁` is fixed by the
  rotation about `a`; its action on each spin-`j` carrier has a one-dimensional kernel); that the
  isotypic projectors commute with `K`, that `K` kills `x^{⊗d}`, and the kernel statement on `V_j` are
  representation theory of `SL₂(ℂ)` that is **not** formalized here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

/-- One sector, one-dimensional carrier, multiplicity space `Fin m`, trivial group `{1}`: the commutant
is every matrix, which is `blockOp` of its single block. -/
theorem isotypicInvariants_trivial (m : ℕ) :
    IsotypicInvariants (Λ := Unit) (A := fun _ => Unit) (B := fun _ => Fin m)
      ({1} : Set (Matrix (Idx (fun _ : Unit => Unit) (fun _ : Unit => Fin m))
        (Idx (fun _ : Unit => Unit) (fun _ : Unit => Fin m)) ℂ)) := by
  intro M
  constructor
  · intro _
    refine ⟨fun _ => Matrix.of fun b b' => M ⟨(), ((), b)⟩ ⟨(), ((), b')⟩, ?_⟩
    ext ⟨l, α, b⟩ ⟨l', α', b'⟩
    obtain rfl : l = l' := Subsingleton.elim _ _
    obtain rfl : α = α' := Subsingleton.elim _ _
    rw [blockOp_apply_same]
    simp
  · intro _ U hU
    rw [Set.mem_singleton_iff.1 hU]
    simp

section Rank

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- If every column `α ↦ v_{λ α b}` lies on the line `ℂ k`, then `τ_λ(v) = ‖k‖² |c⟩⟨c|`. -/
theorem tau_eq_smul_vecMulVec_of_kernel (v : Idx A B → ℂ) (l : Λ) (k : A l → ℂ) (c : B l → ℂ)
    (hc : ∀ b α, v ⟨l, (α, b)⟩ = c b * k α) :
    tau v l = (star k ⬝ᵥ k) • Matrix.vecMulVec c (star c) := by
  ext b b'
  rw [tau_apply]
  simp only [hc, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  simp only [star_mul', dotProduct, Pi.star_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- The columns lie on a line if they lie in the kernel of `K` and that kernel is `ℂ k`. -/
theorem exists_coeff_of_kernel (v : Idx A B → ℂ) (l : Λ) (K : Matrix (A l) (A l) ℂ) (k : A l → ℂ)
    (hker : ∀ u : A l → ℂ, K *ᵥ u = 0 → ∃ c : ℂ, u = c • k)
    (hv : ∀ b : B l, K *ᵥ (fun α => v ⟨l, (α, b)⟩) = 0) :
    ∃ c : B l → ℂ, ∀ b α, v ⟨l, (α, b)⟩ = c b * k α := by
  choose c hc using fun b : B l => hker _ (hv b)
  refine ⟨c, fun b α => ?_⟩
  have := congrFun (hc b) α
  simpa using this

/-- **Rank-one reduction.**  If all slices of `v` in sector `λ` are annihilated by an operator `K` of the
carrier whose kernel is a line, the multiplicity block has rank at most one. -/
theorem rank_tau_le_one_of_kernel (v : Idx A B → ℂ) (l : Λ) (K : Matrix (A l) (A l) ℂ) (k : A l → ℂ)
    (hker : ∀ u : A l → ℂ, K *ᵥ u = 0 → ∃ c : ℂ, u = c • k)
    (hv : ∀ b : B l, K *ᵥ (fun α => v ⟨l, (α, b)⟩) = 0) :
    (tau v l).rank ≤ 1 := by
  obtain ⟨c, hc⟩ := exists_coeff_of_kernel v l K k hker hv
  rw [tau_eq_smul_vecMulVec_of_kernel v l k c hc]
  rw [← Matrix.smul_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

end Rank

end FormalResearch.QIB
