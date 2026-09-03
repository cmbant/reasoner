import Mathlib
import FormalResearch.QIA.MultiplicityProfileDimensions

namespace FormalResearch.QIA

/-- The conjugation-odd sector is nonzero exactly when some multiplicity block
has dimension at least two. -/
theorem multiplicityOddDimension_pos_iff
    {α : Type*} [Fintype α] (g : α → Nat) :
    0 < multiplicityOddDimension g ↔ ∃ a, 2 ≤ g a := by
  constructor
  · intro hpos
    by_contra hnone
    have hle : ∀ a, g a ≤ 1 := by
      intro a
      by_contra ha
      have htwo : 2 ≤ g a := by omega
      exact hnone ⟨a, htwo⟩
    have hz := (multiplicityOddDimension_eq_zero_iff g).2 hle
    omega
  · rintro ⟨a, ha⟩
    have hne : multiplicityOddDimension g ≠ 0 := by
      intro hz
      have hle := (multiplicityOddDimension_eq_zero_iff g).1 hz a
      omega
    omega

/-- The invariant observable algebra is strictly larger than the minimal
multiplicity memory exactly when a genuinely quantum multiplicity block is
present. -/
theorem multiplicityAlgebra_gt_memory_iff
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityMemoryDimension g < multiplicityAlgebraDimension g ↔
      ∃ a, 2 ≤ g a := by
  rw [multiplicityAlgebra_eq_memory_add_two_odd]
  constructor
  · intro h
    apply (multiplicityOddDimension_pos_iff g).1
    omega
  · intro h
    have hodd := (multiplicityOddDimension_pos_iff g).2 h
    omega

/-- Exact algebraic quantum excess: every odd Hermitian direction contributes
two real matrix-algebra directions beyond the diagonal/minimal-memory count. -/
theorem multiplicityAlgebra_sub_memory_eq_two_odd
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityAlgebraDimension g - multiplicityMemoryDimension g =
      2 * multiplicityOddDimension g := by
  rw [multiplicityAlgebra_eq_memory_add_two_odd]
  omega

end FormalResearch.QIA
