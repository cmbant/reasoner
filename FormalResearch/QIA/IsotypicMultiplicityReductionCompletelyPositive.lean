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

/-- The raw finite isotypic multiplicity reduction transported across
`CStarMatrix.ofMatrixₗ` to a linear map between the corresponding C-star matrix
algebras. -/
def isotypicMultiplicityReductionCStarLinearMap
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    CStarMatrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ →ₗ[ℂ]
      CStarMatrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ :=
  (CStarMatrix.ofMatrixₗ (R := ℂ)).toLinearMap.comp
    ((isotypicMultiplicityReduction d g).comp
      (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap)

@[simp] theorem isotypicMultiplicityReductionCStarLinearMap_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : CStarMatrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ) :
    isotypicMultiplicityReductionCStarLinearMap d g X =
      CStarMatrix.ofMatrix
        (isotypicMultiplicityReduction d g (CStarMatrix.ofMatrix.symm X)) := rfl

/-- The explicit finite isotypic multiplicity reduction, bundled as a Mathlib
completely positive map between finite complex matrix C-star algebras. -/
def isotypicMultiplicityReductionCompletelyPositive
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    CStarMatrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ →CP
      CStarMatrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ where
  toLinearMap := isotypicMultiplicityReductionCStarLinearMap d g
  map_cstarMatrix_nonneg' k M hM := by
    have hX : (cstarMatrixBlockFlatten M).PosSemidef :=
      cstarMatrixBlockFlatten_posSemidef_of_nonneg hM
    have hY :=
      isotypicMultiplicityReduction_amplification_posSemidef
        (β := Fin k) d g hX
    apply cstarMatrixBlockFlatten_nonneg_of_posSemidef
    have heq :
        cstarMatrixBlockFlatten
            (M.map ⇑(isotypicMultiplicityReductionCStarLinearMap d g)) =
          (fun ir js : Fin k × multiplicityMemoryCarrier g =>
            isotypicMultiplicityReduction d g
              (fun p q =>
                cstarMatrixBlockFlatten M (ir.1, p) (js.1, q))
              ir.2 js.2) := by
      ext ir js
      rfl
    rw [heq]
    exact hY

@[simp] theorem isotypicMultiplicityReductionCompletelyPositive_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : CStarMatrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ) :
    isotypicMultiplicityReductionCompletelyPositive d g X =
      CStarMatrix.ofMatrix
        (isotypicMultiplicityReduction d g (CStarMatrix.ofMatrix.symm X)) := rfl

end

end FormalResearch.QIA
