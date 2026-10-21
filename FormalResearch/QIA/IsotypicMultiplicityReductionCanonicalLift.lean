import FormalResearch.QIA.IsotypicMultiplicityReductionPOVMLift

/-!
# QI-A canonical lift of the multiplicity basis PVM

The coordinate symmetry-reduction theorem has two descriptions of the same
sharp query: the multiplicity-side rank-one basis projector and the source
effect which is identity on the corresponding carrier factor.  The preceding
POVM-lift module proves abstractly that the trace adjoint of the reduction
transports every multiplicity POVM.  This file identifies that lift explicitly
on the basis PVM used by the deferred-query lower bound.

Thus, after finite isotypic coordinates have been supplied, the canonical
Heisenberg lift of `|e_{a,r}><e_{a,r}|` is exactly
`I_{V_a} ⊗ |e_{a,r}><e_{a,r}|`, represented here by
`isotypicDirectSumQueryProjector`.  This is stronger than the manuscript's
existence-of-a-lift assertion for this PVM: it pins down the canonical lift.
It still does not identify the supplied coordinates with a physical
compact-group isotypic decomposition.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- On every multiplicity basis outcome, the canonical Heisenberg lift of the
rank-one multiplicity projector is exactly the source query projector used in
the QI-A deferred-query converse. -/
theorem isotypicMultiplicityEffectLift_basisProjector_eq_queryProjector
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    isotypicMultiplicityEffectLift d g (multiplicityBasisProjector j) =
      isotypicDirectSumQueryProjector d g j := by
  apply (Matrix.ext_iff_trace_mul_right).2
  intro X
  rw [← matrixTraceAdjoint_spec]
  calc
    Matrix.trace
        (multiplicityBasisProjector j * isotypicMultiplicityReduction d g X) =
        isotypicMultiplicityReduction d g X j j := by
      simp [multiplicityBasisProjector, Matrix.trace, Matrix.mul_apply,
        Matrix.diagonal_apply]
    _ = Matrix.trace (isotypicDirectSumQueryProjector d g j * X) :=
      (isotypicDirectSumQueryProjector_trace_mul_eq_reduction_diagonal d g X j).symm

/-- The source query PVM is the canonical lift of the multiplicity-basis PVM.
In particular, this specializes the general POVM transport theorem to the
specific sharp PVM used in the manuscript's deferred-query lower bound. -/
theorem isotypicDirectSumQueryProjector_is_canonical_lift_basisPVM
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    (∀ j : multiplicityMemoryCarrier g,
      (isotypicMultiplicityEffectLift d g (multiplicityBasisProjector j)).PosSemidef) ∧
      (∑ j : multiplicityMemoryCarrier g,
        isotypicMultiplicityEffectLift d g (multiplicityBasisProjector j)) =
        (1 : Matrix (isotypicDirectSumCarrier d g)
          (isotypicDirectSumCarrier d g) ℂ) ∧
      ∀ j X,
        Matrix.trace
          (isotypicMultiplicityEffectLift d g (multiplicityBasisProjector j) * X) =
          Matrix.trace
            (multiplicityBasisProjector j * isotypicMultiplicityReduction d g X) := by
  apply isotypicMultiplicityEffectLift_lifts_POVM d g multiplicityBasisProjector
  · intro j
    exact multiplicityBasisProjector_posSemidef j
  · ext r s
    simp only [Matrix.sum_apply, multiplicityBasisProjector, Matrix.diagonal_apply]
    by_cases hrs : r = s
    · subst s
      simp
    · simp [hrs]

/-- The concrete source PVM from the deferred-query argument is therefore a
canonical lift of the multiplicity-basis PVM, with the exact outcome
probability identity written in the source-projector notation. -/
theorem isotypicDirectSumQueryProjector_PVM_reduction_statistics
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    (∀ j : multiplicityMemoryCarrier g,
      (isotypicDirectSumQueryProjector d g j).PosSemidef) ∧
      (∑ j : multiplicityMemoryCarrier g,
        isotypicDirectSumQueryProjector d g j) =
        (1 : Matrix (isotypicDirectSumCarrier d g)
          (isotypicDirectSumCarrier d g) ℂ) ∧
      ∀ j X,
        Matrix.trace (isotypicDirectSumQueryProjector d g j * X) =
          Matrix.trace
            (multiplicityBasisProjector j * isotypicMultiplicityReduction d g X) := by
  refine ⟨fun j => isotypicDirectSumQueryProjector_posSemidef d g j,
    isotypicDirectSumQueryProjector_sum_eq_one d g, ?_⟩
  intro j X
  rw [← isotypicMultiplicityEffectLift_basisProjector_eq_queryProjector d g j]
  exact (matrixTraceAdjoint_spec (isotypicMultiplicityReduction d g)
    (multiplicityBasisProjector j) X).symm

end

end FormalResearch.QIA
