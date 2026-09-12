import FormalResearch.QIA.CStarMatrixBlockFlattenPositivity
import FormalResearch.QIA.IsotypicMultiplicityReductionAmplification
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# QI-A complete positivity of the finite isotypic multiplicity reduction

This module bundles the explicit finite isotypic multiplicity reduction as a
Mathlib `CompletelyPositiveMap` between the corresponding finite complex matrix
C-star algebras.

The proof uses the canonical block-flatten positivity equivalence to translate
Mathlib's nested `CStarMatrix` amplification order into raw matrix positive
semidefiniteness, applies the existing arbitrary finite-ancilla amplification
theorem, and translates the result back to nested spectral nonnegativity.

This proves complete positivity of the explicit reduction after isotypic
coordinates have been supplied.  It does not construct the physical
Schur--Weyl coordinate equivalence, and it does not by itself package trace
preservation or make a CPTP claim.
-/

namespace FormalResearch.QIA

open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section

/-- The explicit finite isotypic multiplicity reduction, bundled as a Mathlib
completely positive map between finite complex matrix C-star algebras. -/
def isotypicMultiplicityReductionCompletelyPositive
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    CStarMatrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ →CP
      CStarMatrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ where
  toLinearMap := isotypicMultiplicityReduction d g
  map_cstarMatrix_nonneg' k M hM := by
    have hX : (cstarMatrixBlockFlatten M).PosSemidef :=
      cstarMatrixBlockFlatten_posSemidef_of_nonneg hM
    have hY :=
      isotypicMultiplicityReduction_amplification_posSemidef
        (β := Fin k) d g hX
    apply cstarMatrixBlockFlatten_nonneg_of_posSemidef
    simpa [cstarMatrixBlockFlatten] using hY

@[simp] theorem isotypicMultiplicityReductionCompletelyPositive_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : CStarMatrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ) :
    isotypicMultiplicityReductionCompletelyPositive d g X =
      isotypicMultiplicityReduction d g X := rfl

end

end FormalResearch.QIA
