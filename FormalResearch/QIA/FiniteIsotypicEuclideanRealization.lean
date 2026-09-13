import FormalResearch.QIA.FiniteIsotypicCarrierCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# QI-A Euclidean realization of the finite isotypic carrier

The finite isotypic carrier theorem produces algebraic coordinates in the
function space `isotypicDirectSumCarrier d g → ℂ`.  The matrix-based QI-A
converse is formulated instead on `EuclideanSpace ℂ` over that same finite
carrier.  Since Euclidean space is the `PiLp 2` copy of the finite function
space, Mathlib supplies a canonical linear equivalence between the two.  This
module records that final coordinate conversion.

This is still only an algebraic realization theorem.  In particular, it does
not construct the physical compact-group action on symmetric copy space, prove
Schur--Weyl theory, prove that the chosen isotypic coordinates are unitary, or
discharge continuity of the coherent symmetric-power realization used by the
deferred-query separation theorem.
-/

namespace FormalResearch.QIA

open scoped TensorProduct InnerProductSpace

noncomputable section

/-- A complex finite semisimple module satisfying the finiteness hypotheses of
`finiteIsotypicBaseFieldCarrierCoordinates` admits coordinates in the exact
Euclidean carrier used by the finite matrix QI-A formalization. -/
theorem finiteIsotypicEuclideanCarrierCoordinates
    {A M : Type*}
    [Ring A] [Algebra ℂ A]
    [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    [IsSemisimpleModule A M] [IsNoetherian A M] [Module.Finite ℂ M] :
    ∃ d g : isotypicComponents A M → ℕ,
      Nonempty (M ≃ₗ[ℂ]
        EuclideanSpace ℂ (isotypicDirectSumCarrier d g)) := by
  obtain ⟨d, g, ⟨e⟩⟩ :=
    finiteIsotypicBaseFieldCarrierCoordinates (F := ℂ) (A := A) (M := M)
  let eLp :
      (isotypicDirectSumCarrier d g → ℂ) ≃ₗ[ℂ]
        EuclideanSpace ℂ (isotypicDirectSumCarrier d g) :=
    (WithLp.linearEquiv 2 ℂ
      (isotypicDirectSumCarrier d g → ℂ)).symm
  exact ⟨d, g, ⟨e.trans eLp⟩⟩

/-- Symmetric-power specialization of the finite Euclidean carrier theorem.

The hypotheses deliberately leave the representation algebra `A`, its action
on algebraic symmetric power, and semisimplicity as explicit source-specific
data.  The conclusion removes the separate assumption that one has already
chosen a linear equivalence from symmetric power to the nested finite carrier.
The remaining `hreal` continuity premise in the deferred-query theorem is not
claimed here. -/
theorem symmetricPower_finiteIsotypicEuclideanCarrierCoordinates
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Ring A] [Algebra ℂ A]
    {n : ℕ}
    [Module A (SymmetricPower ℂ (Fin n) E)]
    [IsScalarTower ℂ A (SymmetricPower ℂ (Fin n) E)]
    [IsSemisimpleModule A (SymmetricPower ℂ (Fin n) E)]
    [IsNoetherian A (SymmetricPower ℂ (Fin n) E)]
    [Module.Finite ℂ (SymmetricPower ℂ (Fin n) E)] :
    ∃ d g : isotypicComponents A (SymmetricPower ℂ (Fin n) E) → ℕ,
      Nonempty (SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ]
        EuclideanSpace ℂ (isotypicDirectSumCarrier d g)) := by
  exact finiteIsotypicEuclideanCarrierCoordinates
    (A := A) (M := SymmetricPower ℂ (Fin n) E)

end

end FormalResearch.QIA
