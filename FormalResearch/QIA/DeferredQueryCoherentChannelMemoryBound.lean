import FormalResearch.QIA.MatrixDensityUpperBound
import FormalResearch.QIA.DeferredQueryCoherentPositiveMemoryBound

/-!
# QI-A deferred-query converse from normalized states and a positive TP encoding

The positive coherent deferred-query converse still assumes explicitly that
each encoded witness state is bounded above by the identity.  For physical
density matrices and a positive trace-preserving encoding, that order bound is
automatic: positivity and trace preservation make every encoded witness a
positive-semidefinite unit-trace matrix, and `MatrixDensityUpperBound` then
places it below the identity.

This module performs exactly that composition.  It still assumes only ordinary
positivity, not complete positivity, and it does not construct the concrete
QI-A Schur/symmetric-subspace channel.
-/

namespace FormalResearch.QIA

open Matrix
open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Exact coherent-family deferred-query statistics force the memory dimension
bound for a positive trace-preserving encoding of normalized PSD witness
states.  The encoded-state bound `C (omega j) ≤ I` is derived internally. -/
theorem deferredStatsOnCoherentRankOneFamily_card_le_memory_canonicalAdjoint_of_positive_tracePreserving
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
    (hCpos : ∀ X : Matrix h h ℂ, X.PosSemidef → (C X).PosSemidef)
    (hTP : ∀ X : Matrix h h ℂ, Matrix.trace (C X) = Matrix.trace X)
    (homegaPos : ∀ j, (omega j).PosSemidef)
    (homegaTrace : ∀ j, Matrix.trace (omega j) = 1)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hstats : ∀ j x,
      Complex.re (Matrix.trace
        (F j * C (coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))))) =
      Complex.re (Matrix.trace
        (P j * coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x))))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1) :
    Fintype.card J ≤ Fintype.card q := by
  apply deferredStatsOnCoherentRankOneFamily_card_le_memory_canonicalAdjoint_of_posSemidef_preserving
    ι hreal omega P C F hCpos hFpos hPOVM hP hstats hdiag
  intro j
  apply posSemidef_le_one_of_trace_eq_one (hCpos (omega j) (homegaPos j))
  exact (hTP (omega j)).trans (homegaTrace j)

/-- Multiplicity-profile specialization under normalized PSD witness states and
a positive trace-preserving encoding map. -/
theorem multiplicityMemoryDimension_le_of_deferredStatsOnCoherentRankOneFamily_canonicalAdjoint_of_positive_tracePreserving
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
    (hCpos : ∀ X : Matrix h h ℂ, X.PosSemidef → (C X).PosSemidef)
    (hTP : ∀ X : Matrix h h ℂ, Matrix.trace (C X) = Matrix.trace X)
    (homegaPos : ∀ j, (omega j).PosSemidef)
    (homegaTrace : ∀ j, Matrix.trace (omega j) = 1)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hstats : ∀ j x,
      Complex.re (Matrix.trace
        (F j * C (coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))))) =
      Complex.re (Matrix.trace
        (P j * coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x))))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  apply multiplicityMemoryDimension_le_of_deferredStatsOnCoherentRankOneFamily_canonicalAdjoint_of_posSemidef_preserving
    g ι hreal omega P C F hCpos hFpos hPOVM hP hstats hdiag
  intro j
  apply posSemidef_le_one_of_trace_eq_one (hCpos (omega j) (homegaPos j))
  exact (hTP (omega j)).trans (homegaTrace j)

end

end FormalResearch.QIA
