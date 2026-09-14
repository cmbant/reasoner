import FormalResearch.QIA.UnitaryRepresentationSemisimplicity
import FormalResearch.QIA.SymmetricPowerRepresentation
import Mathlib.RepresentationTheory.Intertwining

/-!
# Transporting semisimplicity across equivariant unitary realizations

A representation equivalence induces a linear equivalence of the corresponding
group-algebra modules.  Hence semisimplicity can be transported across an
explicit equivariant realization.  Combining this with finite-dimensional
unitary semisimplicity removes a separate semisimplicity assumption once such a
unitary realization has actually been supplied.

This file does not construct the manuscript's physical local-unitary action or
an equivariant Hilbert realization of algebraic symmetric power.  Those remain
explicit hypotheses.
-/

namespace FormalResearch.QIA

open scoped MonoidAlgebra

noncomputable section

/-- A representation equivalence is also a linear equivalence between the
associated group-algebra modules. -/
def representationEquivAsModuleLinearEquiv
    {A G V W : Type*}
    [CommRing A] [Group G]
    [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W]
    {ρ : Representation A G V} {σ : Representation A G W}
    (φ : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[A[G]] σ.asModule := by
  apply LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap)
  exact φ.toLinearEquiv.bijective

/-- Semisimplicity of the group-algebra module is invariant under equivalence of
representations. -/
theorem isSemisimpleModule_asModule_iff_of_equiv
    {A G V W : Type*}
    [CommRing A] [Group G]
    [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W]
    {ρ : Representation A G V} {σ : Representation A G W}
    (φ : ρ.Equiv σ) :
    IsSemisimpleModule A[G] ρ.asModule ↔
      IsSemisimpleModule A[G] σ.asModule :=
  (representationEquivAsModuleLinearEquiv φ).isSemisimpleModule_iff

/-- If a complex representation is equivariantly equivalent to a
finite-dimensional inner-product-preserving representation, its group-algebra
module is semisimple. -/
theorem isSemisimpleModule_asModule_of_equiv_innerPreserving
    {G V H : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G V)
    (σ : Representation ℂ G H)
    (φ : ρ.Equiv σ)
    (hunitary : IsInnerPreservingRepresentation σ) :
    IsSemisimpleModule ℂ[G] ρ.asModule := by
  rw [isSemisimpleModule_asModule_iff_of_equiv φ]
  exact isSemisimpleModule_asModule_of_innerPreserving σ hunitary

/-- Representation-level form of semisimplicity transport from an explicit
finite-dimensional unitary realization. -/
theorem isSemisimpleRepresentation_of_equiv_innerPreserving
    {G V H : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G V)
    (σ : Representation ℂ G H)
    (φ : ρ.Equiv σ)
    (hunitary : IsInnerPreservingRepresentation σ) :
    Representation.IsSemisimpleRepresentation ρ := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact isSemisimpleModule_asModule_of_equiv_innerPreserving ρ σ φ hunitary

/-- In particular, an algebraic symmetric-power representation is semisimple as
soon as an explicit equivariant finite-dimensional unitary realization of that
representation is supplied. -/
theorem symmetricPowerRepresentation_isSemisimple_of_equiv_innerPreserving
    {G : Type} {E H : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    {n : ℕ}
    (ρ : Representation ℂ G E)
    (σ : Representation ℂ G H)
    (φ : (symmetricPowerRepresentation (ι := Fin n) ρ).Equiv σ)
    (hunitary : IsInnerPreservingRepresentation σ) :
    Representation.IsSemisimpleRepresentation
      (symmetricPowerRepresentation (ι := Fin n) ρ) := by
  exact isSemisimpleRepresentation_of_equiv_innerPreserving
    (symmetricPowerRepresentation (ι := Fin n) ρ) σ φ hunitary

end

end FormalResearch.QIA
