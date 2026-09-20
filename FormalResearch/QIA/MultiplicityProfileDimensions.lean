import Mathlib

namespace FormalResearch.QIA

open scoped BigOperators

/-- Total Hilbert dimension of a classical--quantum multiplicity register. -/
def multiplicityMemoryDimension {α : Type*} [Fintype α] (g : α → Nat) : Nat :=
  ∑ a : α, g a

/-- Dimension of the direct sum of full matrix algebras on the multiplicity
blocks. -/
def multiplicityAlgebraDimension {α : Type*} [Fintype α] (g : α → Nat) : Nat :=
  ∑ a : α, (g a)^2

/-- Real dimension of the conjugation-odd Hermitian sector for real-type
multiplicity blocks. -/
def multiplicityOddDimension {α : Type*} [Fintype α] (g : α → Nat) : Nat :=
  ∑ a : α, (g a).choose 2

/-- Elementary one-block identity: a `g x g` matrix block consists of `g`
classical diagonal directions plus twice the number of antisymmetric/odd
pairs. -/
theorem two_choose_two_add_self_eq_sq (n : Nat) :
    2 * n.choose 2 + n = n^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      simp only [Nat.succ_eq_add_one]
      nlinarith

/-- Universal dimension balance for a finite multiplicity profile:
`dim algebra = memory dimension + 2 * odd Hermitian dimension`. -/
theorem multiplicityAlgebra_eq_memory_add_two_odd
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityAlgebraDimension g =
      multiplicityMemoryDimension g + 2 * multiplicityOddDimension g := by
  unfold multiplicityAlgebraDimension multiplicityMemoryDimension multiplicityOddDimension
  calc
    (∑ a : α, (g a)^2) =
        ∑ a : α, (g a + 2 * (g a).choose 2) := by
      apply Finset.sum_congr rfl
      intro a ha
      have h := two_choose_two_add_self_eq_sq (g a)
      omega
    _ = (∑ a : α, g a) + ∑ a : α, 2 * (g a).choose 2 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a : α, g a) + 2 * ∑ a : α, (g a).choose 2 := by
      rw [Finset.mul_sum]

/-- A single block has no odd direction exactly when its multiplicity is at
most one. -/
theorem choose_two_eq_zero_iff_le_one (n : Nat) :
    n.choose 2 = 0 ↔ n ≤ 1 := by
  rw [Nat.choose_eq_zero_iff]
  omega

/-- The complete odd Hermitian sector vanishes exactly for a multiplicity-free
profile.  This is the finite combinatorial core of
`classicalizable iff no conjugation-odd multiplicity coherence`. -/
theorem multiplicityOddDimension_eq_zero_iff
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityOddDimension g = 0 ↔ ∀ a, g a ≤ 1 := by
  unfold multiplicityOddDimension
  simp [choose_two_eq_zero_iff_le_one]

/-- Equivalent numerical criterion: the matrix-algebra dimension equals the
minimal Hilbert memory dimension exactly in the multiplicity-free case. -/
theorem multiplicityAlgebra_eq_memory_iff
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityAlgebraDimension g = multiplicityMemoryDimension g ↔
      ∀ a, g a ≤ 1 := by
  rw [multiplicityAlgebra_eq_memory_add_two_odd]
  constructor
  · intro h
    have hodd : multiplicityOddDimension g = 0 := by omega
    exact (multiplicityOddDimension_eq_zero_iff g).mp hodd
  · intro h
    rw [(multiplicityOddDimension_eq_zero_iff g).mpr h]
    simp

end FormalResearch.QIA
