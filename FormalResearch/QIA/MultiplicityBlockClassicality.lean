import Mathlib
import FormalResearch.QIA.MultiplicityProfileQuantumExcess

/-!
# QI-A multiplicity-block classicality core

Source authority: `cmbant/QIprojects@b06a104c594b029aeb0fc2c8f401f8d4c55b901b`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

The paper's pure-copy classicalization criterion identifies commutativity of the
invariant algebra with multiplicity-freeness.  This module formalizes the finite
matrix-block core of that statement.  A full matrix algebra on a finite block
commutes exactly when its dimension is at most one; when the block has dimension
at least two, explicit matrix units give a noncommuting pair.  Therefore a
finite multiplicity profile is blockwise commutative exactly when every
multiplicity is at most one.

This is not yet the full deferred-query classicalization theorem.  In
particular, the operational bridge from a universal classical master POVM to
joint measurability of the compressed invariant PVMs, and the pure-copy
coherent-separation step used there, remain external.
-/

namespace FormalResearch.QIA

/-- Every full multiplicity matrix block is commutative.  This is the direct
sum blockwise algebraic condition corresponding to a commutative invariant
algebra once the symmetry-reduction identification has been supplied. -/
def multiplicityBlocksCommutative {α : Type*} [Fintype α] (g : α → Nat) : Prop :=
  ∀ a, ∀ A B : Matrix (Fin (g a)) (Fin (g a)) ℂ, A * B = B * A

/-- A square complex matrix algebra has a noncommuting pair exactly from
matrix size two onward. -/
theorem finMatrix_exists_noncommuting_iff (n : Nat) :
    (∃ A B : Matrix (Fin n) (Fin n) ℂ, A * B ≠ B * A) ↔ 2 ≤ n := by
  constructor
  · rintro ⟨A, B, hAB⟩
    by_contra htwo
    have hn : n = 0 ∨ n = 1 := by omega
    apply hAB
    rcases hn with rfl | rfl
    · ext i j
      exact Fin.elim0 i
    · ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, mul_comm]
  · intro hn
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hji : j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [i, j] at hv
    refine ⟨Matrix.single i j (1 : ℂ), Matrix.single j j (1 : ℂ), ?_⟩
    intro h
    have hprod :
        Matrix.single i j (1 : ℂ) = (0 : Matrix (Fin n) (Fin n) ℂ) := by
      simpa [hji] using h
    have hentry :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hprod
    have hone : (1 : ℂ) = 0 := by
      simpa [Matrix.single] using hentry
    exact one_ne_zero hone

/-- Equivalently, all square matrices of size `n` commute exactly when
`n ≤ 1`. -/
theorem finMatrix_forall_mul_comm_iff (n : Nat) :
    (∀ A B : Matrix (Fin n) (Fin n) ℂ, A * B = B * A) ↔ n ≤ 1 := by
  constructor
  · intro hcomm
    by_contra hle
    have htwo : 2 ≤ n := by omega
    obtain ⟨A, B, hAB⟩ := (finMatrix_exists_noncommuting_iff n).2 htwo
    exact hAB (hcomm A B)
  · intro hn A B
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · ext i j
      exact Fin.elim0 i
    · ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, mul_comm]

/-- Blockwise commutativity is exactly multiplicity-freeness. -/
theorem multiplicityBlocksCommutative_iff
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityBlocksCommutative g ↔ ∀ a, g a ≤ 1 := by
  constructor
  · intro h a
    exact (finMatrix_forall_mul_comm_iff (g a)).1 (h a)
  · intro h a
    exact (finMatrix_forall_mul_comm_iff (g a)).2 (h a)

/-- The profile contains an explicit noncommuting matrix block exactly when
some multiplicity is at least two. -/
theorem multiplicity_exists_noncommuting_block_iff
    {α : Type*} [Fintype α] (g : α → Nat) :
    (∃ a, ∃ A B : Matrix (Fin (g a)) (Fin (g a)) ℂ, A * B ≠ B * A) ↔
      ∃ a, 2 ≤ g a := by
  constructor
  · rintro ⟨a, A, B, hAB⟩
    exact ⟨a, (finMatrix_exists_noncommuting_iff (g a)).1 ⟨A, B, hAB⟩⟩
  · rintro ⟨a, ha⟩
    obtain ⟨A, B, hAB⟩ := (finMatrix_exists_noncommuting_iff (g a)).2 ha
    exact ⟨a, A, B, hAB⟩

/-- The existing odd-sector criterion is exactly the same algebraic
classicality boundary. -/
theorem multiplicityBlocksCommutative_iff_odd_zero
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityBlocksCommutative g ↔ multiplicityOddDimension g = 0 :=
  (multiplicityBlocksCommutative_iff g).trans
    (multiplicityOddDimension_eq_zero_iff g).symm

/-- Likewise, blockwise commutativity is equivalent to equality of the
matrix-algebra dimension and minimal multiplicity-memory dimension. -/
theorem multiplicityBlocksCommutative_iff_algebra_eq_memory
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityBlocksCommutative g ↔
      multiplicityAlgebraDimension g = multiplicityMemoryDimension g :=
  (multiplicityBlocksCommutative_iff g).trans
    (multiplicityAlgebra_eq_memory_iff g).symm

/-- A noncommuting block exists exactly when the conjugation-odd sector has
positive dimension. -/
theorem multiplicity_exists_noncommuting_block_iff_odd_pos
    {α : Type*} [Fintype α] (g : α → Nat) :
    (∃ a, ∃ A B : Matrix (Fin (g a)) (Fin (g a)) ℂ, A * B ≠ B * A) ↔
      0 < multiplicityOddDimension g :=
  (multiplicity_exists_noncommuting_block_iff g).trans
    (multiplicityOddDimension_pos_iff g).symm

end FormalResearch.QIA
