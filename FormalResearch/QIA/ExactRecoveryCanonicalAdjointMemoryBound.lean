import FormalResearch.QIA.ExactRecoveryHeisenbergMemoryBound
import FormalResearch.QIA.MatrixDensityUpperBound
import FormalResearch.QIA.MatrixTraceAdjointPositivity
import FormalResearch.QIA.MatrixTraceAdjointUnital

/-!
# QI-A exact-recovery bound for a positive trace-preserving encoding

`ExactRecoveryHeisenbergMemoryBound` isolates the finite POVM argument, but
leaves its Heisenberg adjoint, positivity, unitality, and the elementary
density-matrix bound as hypotheses.  In finite matrix algebras each of these
has a canonical derivation from the usual Schrödinger-picture assumptions.

This file makes that derivation explicit.  Thus an exact recovery of one
coordinate pure state for every query label through a positive
trace-preserving encoding requires a memory Hilbert space at least as large as
the label set.  Complete positivity is not needed for this finite converse;
it is a stronger physical hypothesis which implies the positivity premise
used here.

As in the preceding module, this is the finite channel bridge only.  It does
not construct the QI-A symmetry-reduction encoding or a recovery channel.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Exact recovery of a family of normalized positive semidefinite witness
states through a positive trace-preserving finite encoding forces the number
of witnesses to fit in the memory Hilbert-space dimension.

The Heisenberg map is the canonical finite trace adjoint of `R`.  Its
positivity and unitality are derived, respectively, from positivity and trace
preservation of `R`; and the bound on each encoded witness follows from its
positive semidefiniteness and trace one. -/
theorem exactRecovery_card_le_memory_canonicalAdjoint_of_positive_tracePreserving
    {J q : Type*} [Fintype J] [DecidableEq J]
    [Fintype q] [DecidableEq q]
    (omega : J → Matrix q q ℂ)
    (R : Matrix q q ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hRpos : ∀ X : Matrix q q ℂ, X.PosSemidef → (R X).PosSemidef)
    (hRTP : ∀ X : Matrix q q ℂ, Matrix.trace (R X) = Matrix.trace X)
    (homegaPos : ∀ j, (omega j).PosSemidef)
    (homegaTrace : ∀ j, Matrix.trace (omega j) = 1)
    (hrecover : ∀ j, R (omega j) = coordinateProjector j) :
    Fintype.card J ≤ Fintype.card q := by
  apply exactRecoveryAdjoint_card_le_memory omega R (matrixTraceAdjoint R)
  · intro A hA
    exact matrixTraceAdjoint_posSemidef_of_posSemidef_preserving R hRpos hA
  · exact matrixTraceAdjoint_one_eq_one_of_tracePreserving R hRTP
  · intro A X
    exact matrixTraceAdjoint_spec R A X
  · exact hrecover
  · intro j
    apply posSemidef_le_one_of_trace_eq_one (homegaPos j)
    exact homegaTrace j

/-- QI-A multiplicity-profile specialization of the canonical-adjoint
exact-recovery converse.  One normalized auxiliary state is retained for
every direct-sum multiplicity basis vector, so the number of witnesses is
exactly `multiplicityMemoryDimension g`. -/
theorem multiplicityMemoryDimension_le_of_exactRecovery_canonicalAdjoint_of_positive_tracePreserving
    {α q : Type*} [Fintype α] [DecidableEq α]
    [Fintype q] [DecidableEq q]
    (g : α → Nat)
    (omega : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (R : Matrix q q ℂ →ₗ[ℂ]
      Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ)
    (hRpos : ∀ X : Matrix q q ℂ, X.PosSemidef → (R X).PosSemidef)
    (hRTP : ∀ X : Matrix q q ℂ, Matrix.trace (R X) = Matrix.trace X)
    (homegaPos : ∀ j, (omega j).PosSemidef)
    (homegaTrace : ∀ j, Matrix.trace (omega j) = 1)
    (hrecover : ∀ j, R (omega j) = coordinateProjector j) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  have h := exactRecovery_card_le_memory_canonicalAdjoint_of_positive_tracePreserving
    omega R hRpos hRTP homegaPos homegaTrace hrecover
  rw [multiplicityMemoryCarrier_card g] at h
  exact h

end

end FormalResearch.QIA
