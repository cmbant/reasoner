import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# QI-A base-field coordinates for a finite isotypic block

The QI-A symmetry reduction ultimately uses complex-linear coordinates on each
finite isotypic block.  Mathlib's semisimple-module API produces multiplicity
coordinates as a linear equivalence over the representation algebra.  This
module records the scalar-restriction bridge: when the representation algebra
is an algebra over a base field `F`, the same finite multiplicity decomposition
is an `F`-linear equivalence.

This is an algebraic coordinate-existence result for one finite isotypic block.
It does not prove the compact-unitary Schur--Weyl decomposition of the physical
symmetric-copy space and does not assert that the resulting coordinates are
unitary/isometric.
-/

namespace FormalResearch.QIA

noncomputable section

/-- A finite semisimple `A`-module that is isotypic of type `S` admits finite
multiplicity coordinates that are linear over the base field `F`.

Mathlib supplies an `A`-linear equivalence `M ≃ₗ[A] (Fin g → S)`; restricting
scalars along `F → A` gives the base-field linear coordinates used by the
finite-dimensional QI-A carrier model. -/
theorem isotypicBaseFieldMultiplicityCoordinates
    {F A M S : Type*}
    [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]
    [AddCommGroup S] [Module F S] [Module A S] [IsScalarTower F A S]
    [IsSemisimpleModule A M] [Module.Finite A M]
    (h : IsIsotypicOfType A M S) :
    ∃ g : ℕ, Nonempty (M ≃ₗ[F] (Fin g → S)) := by
  obtain ⟨g, ⟨e⟩⟩ := h.linearEquiv_fun
  exact ⟨g, ⟨e.restrictScalars F⟩⟩

end

end FormalResearch.QIA
