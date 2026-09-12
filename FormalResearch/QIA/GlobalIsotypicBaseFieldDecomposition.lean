import FormalResearch.QIA.IsotypicBaseFieldCoordinates
import Mathlib.LinearAlgebra.DFinsupp

/-!
# QI-A global isotypic base-field decomposition

Mathlib proves that the isotypic components of a semisimple module are
independent and span the whole module.  Combining those results with
`iSupIndep.linearEquiv` gives an algebra-linear direct-sum decomposition.
This module records the corresponding equivalence after restricting scalars to
an underlying physical base field.

This is an algebraic global-isotypic decomposition.  It does not prove that a
physical symmetric-copy representation is semisimple/isotypically decomposed,
does not construct Schur--Weyl theory, and does not assert that the resulting
coordinates are unitary or isometric.
-/

namespace FormalResearch.QIA

noncomputable section

/-- A semisimple `A`-module decomposes, over the base field `F`, as the dependent
finite-support direct sum of all of its nonzero isotypic components.

The only input beyond Mathlib's semisimple-module theory is the compatible
scalar tower `F → A → M`. -/
theorem globalIsotypicBaseFieldDecomposition
    {F A M : Type*}
    [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]
    [IsSemisimpleModule A M] :
    Nonempty
      (M ≃ₗ[F]
        (Π₀ c : isotypicComponents A M, c.1)) := by
  classical
  have hind :
      iSupIndep (fun c : isotypicComponents A M => c.1) :=
    (sSupIndep_iff (isotypicComponents A M)).mp
      (sSupIndep_isotypicComponents A M)
  have htop :
      (⨆ c : isotypicComponents A M, c.1) = (⊤ : Submodule A M) := by
    rw [← sSup_eq_iSup, sSup_isotypicComponents]
  exact ⟨((hind.linearEquiv htop).symm).restrictScalars F⟩

end

end FormalResearch.QIA
