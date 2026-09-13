import FormalResearch.QIA.FiniteIsotypicEuclideanRealization
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.RingTheory.Noetherian.Basic

/-!
# QI-A finite symmetric-power isotypic realization

The Euclidean isotypic realization theorem currently asks separately for
finite-dimensionality and Noetherianity of the algebraic symmetric power.
For a finite-dimensional one-copy space, both are consequences of standard
algebraic facts already available in Mathlib: finite indexed tensor products
of finite modules are finite, the symmetric power is a quotient of that tensor
power, and Noetherianity ascends along a scalar tower.

This module removes those two bookkeeping assumptions.  It still does not
construct the physical representation algebra action, prove semisimplicity or
Schur--Weyl theory, identify the resulting coordinates with a unitary physical
decomposition, or discharge continuity of the coherent symmetric-power
realization.
-/

namespace FormalResearch.QIA

open scoped TensorProduct InnerProductSpace

noncomputable section

/-- Algebraic symmetric power of a finite module over a field is again finite.

This uses the surjection from the finite indexed tensor power onto symmetric
power; no topological structure on `SymmetricPower` is asserted. -/
theorem symmetricPower_moduleFinite
    {F E : Type*} [Field F]
    [AddCommGroup E] [Module F E] [Module.Finite F E]
    {n : ℕ} :
    Module.Finite F (SymmetricPower F (Fin n) E) := by
  apply Module.Finite.of_surjective (SymmetricPower.mk F (Fin n) E)
  exact LinearMap.range_eq_top.mp (SymmetricPower.range_mk F (Fin n) E)

/-- If algebraic symmetric power carries an action of a larger scalar algebra,
its finite-dimensionality over the base field implies Noetherianity for that
larger action through the scalar tower. -/
theorem symmetricPower_isNoetherian_of_finite
    {F A E : Type*} [Field F]
    [Ring A] [Algebra F A]
    [AddCommGroup E] [Module F E] [Module.Finite F E]
    {n : ℕ}
    [Module A (SymmetricPower F (Fin n) E)]
    [IsScalarTower F A (SymmetricPower F (Fin n) E)] :
    IsNoetherian A (SymmetricPower F (Fin n) E) := by
  letI : Module.Finite F (SymmetricPower F (Fin n) E) :=
    symmetricPower_moduleFinite (F := F) (E := E) (n := n)
  letI : IsNoetherian F (SymmetricPower F (Fin n) E) := inferInstance
  exact isNoetherian_of_tower F
    (inferInstance : IsNoetherian F (SymmetricPower F (Fin n) E))

/-- Finite-dimensional one-copy specialization of the Euclidean isotypic
carrier theorem.

Compared with `symmetricPower_finiteIsotypicEuclideanCarrierCoordinates`, this
version derives both base-field finiteness and `A`-Noetherianity of symmetric
power.  The representation algebra action and semisimplicity remain explicit
because they are the genuinely representation-theoretic part of the QI-A
Schur--Weyl bridge. -/
theorem symmetricPower_finiteIsotypicEuclideanCarrierCoordinates_of_finite
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Module.Finite ℂ E]
    [Ring A] [Algebra ℂ A]
    {n : ℕ}
    [Module A (SymmetricPower ℂ (Fin n) E)]
    [IsScalarTower ℂ A (SymmetricPower ℂ (Fin n) E)]
    [IsSemisimpleModule A (SymmetricPower ℂ (Fin n) E)] :
    ∃ d g : isotypicComponents A (SymmetricPower ℂ (Fin n) E) → ℕ,
      Nonempty (SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ]
        EuclideanSpace ℂ (isotypicDirectSumCarrier d g)) := by
  letI : Module.Finite ℂ (SymmetricPower ℂ (Fin n) E) :=
    symmetricPower_moduleFinite (F := ℂ) (E := E) (n := n)
  letI : IsNoetherian A (SymmetricPower ℂ (Fin n) E) :=
    symmetricPower_isNoetherian_of_finite (F := ℂ) (A := A) (E := E) (n := n)
  exact symmetricPower_finiteIsotypicEuclideanCarrierCoordinates
    (E := E) (A := A) (n := n)

end

end FormalResearch.QIA
