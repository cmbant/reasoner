import FormalResearch.QIA.IsotypicMultiplicityReductionPositive
import FormalResearch.QIA.MatrixTraceAdjointPositivity
import FormalResearch.QIA.MatrixTraceAdjointUnital

/-!
# QI-A coordinate isotypic reduction lifts every multiplicity POVM

The finite isotypic reduction sends a source matrix on
`⊕_a (V_a ⊗ M_a)` to its direct-sum multiplicity matrix.  The manuscript's
symmetry-sufficient reduction theorem needs more than trace preservation: a
POVM chosen on the direct-sum multiplicity system must lift to a source POVM
with exactly the same statistics.

For finite matrix spaces the canonical trace adjoint supplies that lift.  This
module proves that the adjoint of the explicit blockwise partial trace is
positive and unital, so it sends every finite multiplicity POVM to a source
POVM, and verifies the outcome-by-outcome trace identity.

This is the full measurement-simulation statement in the supplied isotypic
coordinates.  Identifying those coordinates with the physical compact-group
representation and identifying the lifted effects with all and only invariant
effects remain separate representation-theoretic steps.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- The canonical Heisenberg lift of a multiplicity effect through the
explicit finite isotypic reduction. -/
abbrev isotypicMultiplicityEffectLift
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ →ₗ[ℂ]
      Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ :=
  matrixTraceAdjoint (isotypicMultiplicityReduction d g)

/-- The coordinate isotypic reduction's canonical effect lift preserves
positive semidefiniteness. -/
theorem isotypicMultiplicityEffectLift_posSemidef
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    {B : Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ}
    (hB : B.PosSemidef) :
    (isotypicMultiplicityEffectLift d g B).PosSemidef := by
  apply matrixTraceAdjoint_posSemidef_of_posSemidef_preserving
    (isotypicMultiplicityReduction d g) ?_ hB
  intro X hX
  exact isotypicMultiplicityReduction_posSemidef d g hX

/-- The coordinate isotypic reduction's canonical effect lift is unital. -/
theorem isotypicMultiplicityEffectLift_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    isotypicMultiplicityEffectLift d g
      (1 : Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ) =
      (1 : Matrix (isotypicDirectSumCarrier d g)
        (isotypicDirectSumCarrier d g) ℂ) := by
  exact matrixTraceAdjoint_one_eq_one_of_tracePreserving
    (isotypicMultiplicityReduction d g)
    (isotypicMultiplicityReduction_trace d g)

/-- Every finite POVM on the direct-sum multiplicity system has a positive,
unital source lift through the explicit isotypic reduction, and each lifted
outcome has exactly the same probability on every source matrix.

This is the finite-coordinate measurement equivalence used in the upper-bound
half of the manuscript's symmetry-sufficient reduction theorem. -/
theorem isotypicMultiplicityEffectLift_lifts_POVM
    {α J : Type*} [Fintype α] [DecidableEq α] [Fintype J]
    (d g : α → Nat)
    (F : J → Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) =
      (1 : Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ)) :
    (∀ j, (isotypicMultiplicityEffectLift d g (F j)).PosSemidef) ∧
      (∑ j, isotypicMultiplicityEffectLift d g (F j)) =
        (1 : Matrix (isotypicDirectSumCarrier d g)
          (isotypicDirectSumCarrier d g) ℂ) ∧
      ∀ j X,
        Matrix.trace (isotypicMultiplicityEffectLift d g (F j) * X) =
          Matrix.trace (F j * isotypicMultiplicityReduction d g X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact isotypicMultiplicityEffectLift_posSemidef d g (hFpos j)
  · change
      (∑ j, matrixTraceAdjoint (isotypicMultiplicityReduction d g) (F j)) = _
    rw [← map_sum, hPOVM]
    exact isotypicMultiplicityEffectLift_one d g
  · intro j X
    exact (matrixTraceAdjoint_spec (isotypicMultiplicityReduction d g) (F j) X).symm

end

end FormalResearch.QIA
