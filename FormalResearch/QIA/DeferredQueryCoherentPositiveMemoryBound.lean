import FormalResearch.QIA.MatrixTraceAdjointPositivity
import FormalResearch.QIA.DeferredQueryCoherentRankOneMemoryBound

/-!
# QI-A deferred-query converse from source-channel positivity

`DeferredQueryCoherentRankOneMemoryBound` proves the coherent-source memory
lower bound once positivity of every pulled-back POVM effect is supplied.
`MatrixTraceAdjointPositivity` shows that this pullback positivity is automatic
for the canonical trace adjoint whenever the Schrödinger-picture encoding map
preserves positive-semidefinite matrices.

This module composes those results.  The converse is therefore stated using a
direct source-channel positivity assumption on the encoding, with no separate
`hPullbackPos` premise.

This is positivity only, not complete positivity or a concrete CPTP channel
construction.
-/

namespace FormalResearch.QIA

open Matrix
open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Exact deferred-query statistics on the coherent pure-state family force
the memory dimension bound whenever the encoding preserves positive-semidefinite
matrices.  Positivity of canonical-adjoint POVM effects is derived internally. -/
theorem deferredStatsOnCoherentRankOneFamily_card_le_memory_canonicalAdjoint_of_posSemidef_preserving
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
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  apply deferredStatsOnCoherentRankOneFamily_card_le_memory_canonicalAdjoint
    ι hreal omega P C F hFpos hPOVM ?_ hP hstats hdiag hencoded
  intro j
  exact matrixTraceAdjoint_posSemidef_of_posSemidef_preserving
    C hCpos (hFpos j)

/-- Multiplicity-profile specialization of the coherent deferred-query converse
under direct positive-semidefinite preservation by the encoding map. -/
theorem multiplicityMemoryDimension_le_of_deferredStatsOnCoherentRankOneFamily_canonicalAdjoint_of_posSemidef_preserving
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
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  apply multiplicityMemoryDimension_le_of_deferredStatsOnCoherentRankOneFamily_canonicalAdjoint
    g ι hreal omega P C F hFpos hPOVM ?_ hP hstats hdiag hencoded
  intro j
  exact matrixTraceAdjoint_posSemidef_of_posSemidef_preserving
    C hCpos (hFpos j)

end

end FormalResearch.QIA
