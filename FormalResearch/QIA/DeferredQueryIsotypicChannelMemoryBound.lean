import FormalResearch.QIA.IsotypicDirectSumAuxiliaryStates
import FormalResearch.QIA.DeferredQueryCoherentChannelMemoryBound

/-!
# QI-A deferred-query converse with explicit isotypic witnesses

This module instantiates the generic positive trace-preserving coherent-family
memory converse with the manuscript's explicit direct-sum source query
projectors and auxiliary states.

The remaining source-specific assumptions are the supplied finite Hilbert
realization of the symmetric-power source and equality of the target-memory
statistics with the explicit isotypic query statistics on coherent pure-copy
inputs.  The witness-state positivity, normalization, source-effect
self-adjointness, and unit diagonal score are all discharged by the finite
isotypic construction.
-/

namespace FormalResearch.QIA

open Matrix
open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Deferred coherent-query simulation through a positive trace-preserving
encoding requires memory dimension at least the total multiplicity dimension,
when the source query family is the manuscript's explicit isotypic-basis PVM.

`d a` is the irreducible carrier dimension in sector `a`, and `g a` its
multiplicity.  The assumption `hd` is exactly positivity of every nonempty
irreducible carrier dimension. -/
theorem multiplicityMemoryDimension_le_of_deferredStatsOnIsotypicCoherentFamily
    {E α q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype α] [DecidableEq α]
    [Fintype q] [DecidableEq q]
    {n : ℕ}
    (d g : α → Nat)
    (hd : ∀ a, 0 < d a)
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ]
      EuclideanSpace ℂ (isotypicDirectSumCarrier d g))
    (hreal : Continuous fun v : Fin n → E =>
      ι (SymmetricPower.tprod ℂ v))
    (C : Matrix (isotypicDirectSumCarrier d g)
          (isotypicDirectSumCarrier d g) ℂ →ₗ[ℂ]
        Matrix q q ℂ)
    (F : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (hCpos : ∀ X : Matrix (isotypicDirectSumCarrier d g)
        (isotypicDirectSumCarrier d g) ℂ,
      X.PosSemidef → (C X).PosSemidef)
    (hTP : ∀ X : Matrix (isotypicDirectSumCarrier d g)
        (isotypicDirectSumCarrier d g) ℂ,
      Matrix.trace (C X) = Matrix.trace X)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hstats : ∀ j x,
      Complex.re (Matrix.trace
        (F j * C (coherentRankOneMatrix
          (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))))) =
      Complex.re (Matrix.trace
        (isotypicDirectSumQueryProjector d g j *
          coherentRankOneMatrix
            (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))))) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  apply
    multiplicityMemoryDimension_le_of_deferredStatsOnCoherentRankOneFamily_canonicalAdjoint_of_positive_tracePreserving
      g ι hreal
      (fun j => isotypicDirectSumAuxiliaryState d g j)
      (fun j => isotypicDirectSumQueryProjector d g j)
      C F hCpos hTP
  · intro j
    exact isotypicDirectSumAuxiliaryState_posSemidef d g j
  · intro j
    exact isotypicDirectSumAuxiliaryState_trace d g hd j
  · exact hFpos
  · exact hPOVM
  · intro j
    exact isotypicDirectSumQueryProjector_isSelfAdjoint d g j
  · exact hstats
  · intro j
    simp [isotypicDirectSumQueryProjector_auxiliaryState_trace d g hd j]

end

end FormalResearch.QIA
