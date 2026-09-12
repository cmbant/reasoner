import FormalResearch.QIA.IsotypicMultiplicityReductionPositivity

/-!
# QI-A positivity of the assembled isotypic multiplicity reduction

This module lifts the sectorwise positive-semidefinite preservation proved in
`IsotypicMultiplicityReductionPositivity` through the finite dependent block
diagonal used by `isotypicMultiplicityReduction`.

The result is ordinary positivity of the manuscript's explicit finite
multiplicity reduction after isotypic coordinates have been supplied.  It does
not assert complete positivity or CPTP semantics.
-/

namespace FormalResearch.QIA

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- A finite dependent block diagonal of positive-semidefinite complex matrices
is positive semidefinite. -/
theorem blockDiagonal'_posSemidef_of_blocks
    {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → Nat)
    (M : ∀ a, Matrix (Fin (g a)) (Fin (g a)) ℂ)
    (hM : ∀ a, (M a).PosSemidef) :
    (Matrix.blockDiagonal' M).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.isHermitian_blockDiagonal'_iff.mpr fun a => (hM a).isHermitian
  · intro x
    have hsum :
        0 ≤ ∑ a : α,
          star (fun r : Fin (g a) => x ⟨a, r⟩) ⬝ᵥ
            (M a *ᵥ fun r : Fin (g a) => x ⟨a, r⟩) := by
      apply Finset.sum_nonneg
      intro a ha
      exact (hM a).dotProduct_mulVec_nonneg _
    simpa [dotProduct, mulVec, Matrix.blockDiagonal', Fintype.sum_sigma] using hsum

/-- The full finite isotypic multiplicity reduction preserves ordinary positive
semidefiniteness. -/
theorem isotypicMultiplicityReduction_posSemidef
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    {X : Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ}
    (hX : X.PosSemidef) :
    (isotypicMultiplicityReduction d g X).PosSemidef := by
  change
    (Matrix.blockDiagonal'
      (fun a => isotypicMultiplicityBlockReduction d g a X)).PosSemidef
  apply blockDiagonal'_posSemidef_of_blocks g
  intro a
  exact isotypicMultiplicityBlockReduction_posSemidef d g a hX

end

end FormalResearch.QIA
