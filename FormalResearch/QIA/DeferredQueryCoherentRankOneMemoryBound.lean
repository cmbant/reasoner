import FormalResearch.QIA.CoherentRankOneMatrixSeparation
import FormalResearch.QIA.DeferredQueryCanonicalAdjointMemoryBound

/-!
# QI-A deferred-query converse for the coherent rank-one source family

The canonical-adjoint deferred-query converse already reduces the memory lower
bound to one source-side input: a spanning Hermitian family.  The coherent
rank-one matrix bridge supplies exactly that input once algebraic symmetric
power is realized continuously in a finite Euclidean Hilbert space.

This module composes those results.  It removes the abstract `hspan` argument
from the deferred-query converse and states the source statistics directly on
the coherent pure-state rank-one matrices.  Constructing the concrete QI-A
symmetric-subspace/Schur realization, the physical channel, and the manuscript's
auxiliary query projectors and states remains model-specific.
-/

namespace FormalResearch.QIA

open Matrix
open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Exact deferred-query statistics on the coherent pure-state rank-one family
force the memory Hilbert-space dimension bound, using the canonical finite
trace adjoint of the encoding.

The abstract source-family spanning hypothesis has disappeared: it is discharged
by `coherentRankOneHermitian_span_eq_top`. -/
theorem deferredStatsOnCoherentRankOneFamily_card_le_memory_canonicalAdjoint
    {E J h q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype J] [Fintype h] [DecidableEq h]
    [Fintype q] [DecidableEq q]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] EuclideanSpace ℂ h)
    (hreal : Continuous fun v : Fin n → E =>
      ι (SymmetricPower.tprod ℂ v))
    (omega P : J → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (F : J → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hPullbackPos : ∀ j, (matrixTraceAdjoint C (F j)).PosSemidef)
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hstats : ∀ j x,
      Complex.re (Matrix.trace
        (F j * C (coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))))) =
      Complex.re (Matrix.trace
        (P j * coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x))))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  apply deferredStatsOnSpanningFamily_card_le_memory_canonicalAdjoint
    (coherentRankOneHermitianFamily ι)
    (coherentRankOneHermitian_span_eq_top ι hreal)
    omega P C F hFpos hPOVM hPullbackPos hP
  · intro j X hX
    rcases hX with ⟨x, rfl⟩
    simpa [coherentRankOneHermitian] using hstats j x
  · exact hdiag
  · exact hencoded

/-- QI-A multiplicity-profile specialization of the coherent rank-one
canonical-adjoint converse.  One query label is supplied for each basis vector
of the multiplicity-memory carrier, so the left-hand side is exactly
`multiplicityMemoryDimension g`. -/
theorem multiplicityMemoryDimension_le_of_deferredStatsOnCoherentRankOneFamily_canonicalAdjoint
    {E α h q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype α] [Fintype h] [DecidableEq h]
    [Fintype q] [DecidableEq q]
    {n : ℕ}
    (g : α → Nat)
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] EuclideanSpace ℂ h)
    (hreal : Continuous fun v : Fin n → E =>
      ι (SymmetricPower.tprod ℂ v))
    (omega P : multiplicityMemoryCarrier g → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (F : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hPullbackPos : ∀ j, (matrixTraceAdjoint C (F j)).PosSemidef)
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hstats : ∀ j x,
      Complex.re (Matrix.trace
        (F j * C (coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))))) =
      Complex.re (Matrix.trace
        (P j * coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x))))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  have hbound :=
    deferredStatsOnCoherentRankOneFamily_card_le_memory_canonicalAdjoint
      ι hreal omega P C F hFpos hPOVM hPullbackPos hP hstats hdiag hencoded
  rw [multiplicityMemoryCarrier_card g] at hbound
  exact hbound

end

end FormalResearch.QIA
