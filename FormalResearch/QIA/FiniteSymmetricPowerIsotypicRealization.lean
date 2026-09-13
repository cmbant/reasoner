import FormalResearch.QIA.FiniteIsotypicEuclideanRealization
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.RingTheory.Noetherian.Basic

/-!
# QI-A finite symmetric-power isotypic realization

The Euclidean isotypic realization theorem currently asks separately for
finite-dimensionality and Noetherianity of the algebraic symmetric power.
For a finite-dimensional one-copy complex space, both are consequences of
standard algebraic facts already available in Mathlib: finite indexed tensor
products of finite modules are finite, the symmetric power is a quotient of
that tensor power, and Noetherianity ascends along a scalar tower.

This module removes those two bookkeeping assumptions.  It still does not
construct the physical representation algebra action, prove semisimplicity or
Schur--Weyl theory, identify the resulting coordinates with a unitary physical
decomposition, or discharge continuity of the coherent symmetric-power
realization.
-/

namespace FormalResearch.QIA

open scoped TensorProduct InnerProductSpace

noncomputable section

/-- Algebraic symmetric power of a finite complex vector space is again finite.

Pinned Mathlib places the scalar type and tensor-index type in the same
universe, so this QI-A lemma is stated directly over `ℂ`, where `Fin n` has the
required universe.  The proof uses the surjection from finite indexed tensor
power onto symmetric power; no topology on `SymmetricPower` is asserted. -/
theorem complexSymmetricPower_moduleFinite
    {E : Type*} [AddCommGroup E] [Module ℂ E] [Module.Finite ℂ E]
    {n : ℕ} :
    Module.Finite ℂ (SymmetricPower ℂ (Fin n) E) := by
  exact Module.Finite.of_surjective
    (SymmetricPower.mk ℂ (Fin n) E)
    (LinearMap.range_eq_top.mp (SymmetricPower.range_mk ℂ (Fin n) E))

/-- If complex algebraic symmetric power carries an action of a larger scalar
algebra, finite-dimensionality of the one-copy space implies Noetherianity for
that larger action through the scalar tower. -/
theorem complexSymmetricPower_isNoetherian_of_finite
    {A E : Type*}
    [Ring A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [Module.Finite ℂ E]
    {n : ℕ}
    [Module A (SymmetricPower ℂ (Fin n) E)]
    [IsScalarTower ℂ A (SymmetricPower ℂ (Fin n) E)] :
    IsNoetherian A (SymmetricPower ℂ (Fin n) E) := by
  letI : Module.Finite ℂ (SymmetricPower ℂ (Fin n) E) :=
    complexSymmetricPower_moduleFinite (E := E) (n := n)
  letI : IsNoetherian ℂ (SymmetricPower ℂ (Fin n) E) := inferInstance
  exact isNoetherian_of_tower ℂ
    (inferInstance : IsNoetherian ℂ (SymmetricPower ℂ (Fin n) E))

/-- Under the finite one-copy hypotheses, the finite sector-index instance used
by the explicit QI-A carrier is available without separately assuming
Noetherianity of symmetric power in the theorem statement. -/
noncomputable instance symmetricPowerIsotypicComponentsFintypeOfFinite
    {E A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module.Finite ℂ E]
    [Ring A] [Algebra ℂ A]
    {n : ℕ}
    [Module A (SymmetricPower ℂ (Fin n) E)]
    [IsScalarTower ℂ A (SymmetricPower ℂ (Fin n) E)] :
    Fintype (isotypicComponents A (SymmetricPower ℂ (Fin n) E)) := by
  letI : IsNoetherian A (SymmetricPower ℂ (Fin n) E) :=
    complexSymmetricPower_isNoetherian_of_finite (A := A) (E := E) (n := n)
  exact Fintype.ofFinite _

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
    complexSymmetricPower_moduleFinite (E := E) (n := n)
  letI : IsNoetherian A (SymmetricPower ℂ (Fin n) E) :=
    complexSymmetricPower_isNoetherian_of_finite (A := A) (E := E) (n := n)
  exact symmetricPower_finiteIsotypicEuclideanCarrierCoordinates
    (E := E) (A := A) (n := n)

end

end FormalResearch.QIA
