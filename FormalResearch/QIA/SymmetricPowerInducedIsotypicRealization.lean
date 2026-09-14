import FormalResearch.QIA.EquivariantUnitarySemisimplicityTransport
import FormalResearch.QIA.FiniteSymmetricPowerIsotypicRealization

/-!
# Isotypic coordinates for the induced symmetric-power representation

The algebraic symmetric-power representation already carries Mathlib's canonical
group-algebra module structure on its `asModule` type.  This file combines that
structure with finite-dimensionality of algebraic symmetric power and the
semisimplicity transport theorem for an explicitly supplied equivariant unitary
realization.

The resulting sector labels are the isotypic components of the induced
`ℂ[G]`-module.  No identification with the manuscript's physical Schur--Weyl
labels, no construction of a physical local-unitary action, and no claim that
the resulting coordinate equivalence is unitary or isometric is made here.
-/

namespace FormalResearch.QIA

open scoped MonoidAlgebra InnerProductSpace

noncomputable section

/-- If the algebraic symmetric-power representation admits an explicit
equivariant finite-dimensional inner-product-preserving realization, then the
canonical group-algebra module of that representation admits finite Euclidean
isotypic coordinates with strictly positive irreducible-carrier dimensions.

The coordinate equivalence is returned on raw algebraic `SymmetricPower` by
precomposing the isotypic coordinates on `Representation.asModule` with the
canonical `asModuleEquiv.symm` equivalence. -/
theorem symmetricPower_inducedIsotypicEuclideanCarrierCoordinatesWithPositiveCarrier_of_equiv_innerPreserving
    {G E H : Type*} [Group G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    {n : ℕ}
    (ρ : Representation ℂ G E)
    (σ : Representation ℂ G H)
    (φ : (symmetricPowerRepresentation (ι := Fin n) ρ).Equiv σ)
    (hunitary : IsInnerPreservingRepresentation σ) :
    ∃ d g : isotypicComponents ℂ[G]
        (symmetricPowerRepresentation (ι := Fin n) ρ).asModule → ℕ,
      (∀ c, 0 < d c) ∧
      Nonempty (SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ]
        EuclideanSpace ℂ (isotypicDirectSumCarrier d g)) := by
  let π : Representation ℂ G (SymmetricPower ℂ (Fin n) E) :=
    symmetricPowerRepresentation (ι := Fin n) ρ
  letI : Module.Finite ℂ (SymmetricPower ℂ (Fin n) E) :=
    complexSymmetricPower_moduleFinite (E := E) (n := n)
  letI : IsSemisimpleModule ℂ[G] π.asModule := by
    exact isSemisimpleModule_asModule_of_equiv_innerPreserving
      π σ φ hunitary
  letI : IsNoetherian ℂ[G] π.asModule := by
    letI : IsNoetherian ℂ π.asModule := inferInstance
    exact isNoetherian_of_tower ℂ
      (inferInstance : IsNoetherian ℂ π.asModule)
  obtain ⟨d, g, hd, ⟨e⟩⟩ :=
    finiteIsotypicEuclideanCarrierCoordinatesWithPositiveCarrier
      (A := ℂ[G]) (M := π.asModule)
  refine ⟨d, g, hd, ?_⟩
  exact ⟨π.asModuleEquiv.symm.trans e⟩

/-- Positivity-erased wrapper for the induced symmetric-power isotypic
Euclidean realization. -/
theorem symmetricPower_inducedIsotypicEuclideanCarrierCoordinates_of_equiv_innerPreserving
    {G E H : Type*} [Group G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    {n : ℕ}
    (ρ : Representation ℂ G E)
    (σ : Representation ℂ G H)
    (φ : (symmetricPowerRepresentation (ι := Fin n) ρ).Equiv σ)
    (hunitary : IsInnerPreservingRepresentation σ) :
    ∃ d g : isotypicComponents ℂ[G]
        (symmetricPowerRepresentation (ι := Fin n) ρ).asModule → ℕ,
      Nonempty (SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ]
        EuclideanSpace ℂ (isotypicDirectSumCarrier d g)) := by
  obtain ⟨d, g, _hd, hcoord⟩ :=
    symmetricPower_inducedIsotypicEuclideanCarrierCoordinatesWithPositiveCarrier_of_equiv_innerPreserving
      ρ σ φ hunitary
  exact ⟨d, g, hcoord⟩

end

end FormalResearch.QIA
