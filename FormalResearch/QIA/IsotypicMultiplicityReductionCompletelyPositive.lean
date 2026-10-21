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
coordinates have been supplied.  The final definitions in this file combine
that result with the already proved raw-matrix trace identity into a finite
matrix CPTP certificate.  It does not construct the physical Schur--Weyl
coordinate equivalence.
-/

namespace FormalResearch.QIA

open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section

/-- A finite-dimensional quantum channel represented between complex matrix
algebras.  Mathlib supplies the completely-positive component; the trace
condition is written after transport across `CStarMatrix.ofMatrix`, so it is
the ordinary matrix trace used throughout the QI-A coordinate development. -/
structure MatrixCPTP (h q : Type*) [Fintype h] [DecidableEq h]
    [Fintype q] [DecidableEq q] where
  toCompletelyPositive :
    CStarMatrix h h ℂ →CP CStarMatrix q q ℂ
  trace_preserving : ∀ X : Matrix h h ℂ,
    Matrix.trace
        (CStarMatrix.ofMatrix.symm
          (toCompletelyPositive (CStarMatrix.ofMatrix X))) =
      Matrix.trace X

/-- The raw-matrix Schrödinger action of a packaged finite CPTP map. -/
abbrev MatrixCPTP.toMatrixMap
    {h q : Type*} [Fintype h] [DecidableEq h] [Fintype q] [DecidableEq q]
    (C : MatrixCPTP h q) : Matrix h h ℂ → Matrix q q ℂ :=
  fun X => CStarMatrix.ofMatrix.symm
    (C.toCompletelyPositive (CStarMatrix.ofMatrix X))

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

/-- The explicit coordinate multiplicity reduction is completely positive and
trace preserving, hence a finite-matrix quantum channel.  This is precisely
the Schrödinger-picture channel part of the symmetry-reduction theorem after
the finite isotypic coordinates have been supplied. -/
def isotypicMultiplicityReductionCPTP
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    MatrixCPTP (isotypicDirectSumCarrier d g) (multiplicityMemoryCarrier g) where
  toCompletelyPositive := isotypicMultiplicityReductionCompletelyPositive d g
  trace_preserving := by
    intro X
    change Matrix.trace (isotypicMultiplicityReduction d g X) = Matrix.trace X
    exact isotypicMultiplicityReduction_trace d g X

@[simp] theorem isotypicMultiplicityReductionCPTP_toMatrixMap
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : Matrix (isotypicDirectSumCarrier d g)
      (isotypicDirectSumCarrier d g) ℂ) :
    (isotypicMultiplicityReductionCPTP d g).toMatrixMap X =
      isotypicMultiplicityReduction d g X := rfl

/-- The trace-preserving component of the packaged coordinate reduction
channel, stated directly on raw matrices for use in the QI-A memory bounds. -/
theorem isotypicMultiplicityReductionCPTP_trace_preserving
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : Matrix (isotypicDirectSumCarrier d g)
      (isotypicDirectSumCarrier d g) ℂ) :
    Matrix.trace (isotypicMultiplicityReduction d g X) = Matrix.trace X :=
  isotypicMultiplicityReduction_trace d g X

end

end FormalResearch.QIA
