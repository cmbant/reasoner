import FormalResearch.QIA.GlobalIsotypicBaseFieldDecomposition
import FormalResearch.QIA.IsotypicDirectSumAuxiliaryStates
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Pi

/-!
# QI-A explicit finite scalar carrier from algebraic isotypic coordinates

The global semisimple decomposition gives a dependent finite-support direct sum
of isotypic components.  Under explicit Noetherian/base-field finiteness
hypotheses, each nonzero isotypic component has a finite multiplicity model by
one simple factor, and that simple factor has finite base-field coordinates.
This module assembles those ingredients into the concrete scalar carrier used
by the QI-A finite matrix channel and witness constructions.

This remains an algebraic coordinate theorem.  It does not identify a physical
symmetric-copy Hilbert space with the semisimple module, does not prove compact
Schur--Weyl theory, and does not assert that the resulting linear equivalence is
unitary or isometric.
-/

namespace FormalResearch.QIA

noncomputable section

/-- A base-field finite semisimple `A`-module that is Noetherian as an
`A`-module admits coordinates on the explicit finite carrier
`isotypicDirectSumCarrier d g`.

The sector type is Mathlib's finite type of nonzero isotypic components.  For
each sector, `g` is obtained from the finite isotypic multiplicity theorem and
`d` is the base-field dimension of the chosen simple factor.  Thus the target
coordinates have the manuscript-compatible shape `Σ (a,r), k` rather than an
abstract assumed coordinate type. -/
theorem finiteIsotypicBaseFieldCarrierCoordinates
    {F A M : Type*}
    [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M]
    [IsSemisimpleModule A M] [IsNoetherian A M] [Module.Finite F M] :
    ∃ d g : isotypicComponents A M → ℕ,
      Nonempty (M ≃ₗ[F]
        (isotypicDirectSumCarrier d g → F)) := by
  classical
  letI : Fintype (isotypicComponents A M) := Fintype.ofFinite _

  have hblock : ∀ c : isotypicComponents A M,
      ∃ (g : ℕ) (_ : NeZero g) (S : Submodule A M),
        S ≤ c.1 ∧ IsSimpleModule A S ∧
          Nonempty (c.1 ≃ₗ[A] (Fin g → S)) := by
    intro c
    exact (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun

  choose g hg S hSle hSsimple hcoord using hblock
  let d : isotypicComponents A M → ℕ :=
    fun c => Module.finrank F (S c)

  have hSfinite : ∀ c : isotypicComponents A M, Module.Finite F (S c) := by
    intro c
    exact Module.Finite.of_injective
      ((S c).subtype.restrictScalars F) (S c).subtype_injective

  let eBlock : ∀ c : isotypicComponents A M,
      c.1 ≃ₗ[F] ((r : Fin (g c)) → Fin (d c) → F) := fun c => by
    letI : Module.Finite F (S c) := hSfinite c
    exact ((hcoord c).some.restrictScalars F).trans
      (LinearEquiv.piCongrRight fun _ : Fin (g c) =>
        (Module.finBasis F (S c)).equivFun)

  let eGlobal : M ≃ₗ[F] ((c : isotypicComponents A M) → c.1) :=
    (globalIsotypicBaseFieldDecomposition (F := F) (A := A) (M := M)).some |>.trans
      DFinsupp.linearEquivFunOnFintype

  let eBlocks :
      ((c : isotypicComponents A M) → c.1) ≃ₗ[F]
        ((c : isotypicComponents A M) →
          (r : Fin (g c)) → Fin (d c) → F) :=
    LinearEquiv.piCongrRight eBlock

  let eMultiplicityCurry :
      ((c : isotypicComponents A M) →
          (r : Fin (g c)) → Fin (d c) → F) ≃ₗ[F]
        ((j : multiplicityMemoryCarrier g) → Fin (d j.1) → F) :=
    (LinearEquiv.piCurry (R := F)
      (fun c (r : Fin (g c)) => Fin (d c) → F)).symm

  let eCarrierCurry :
      ((j : multiplicityMemoryCarrier g) → Fin (d j.1) → F) ≃ₗ[F]
        (isotypicDirectSumCarrier d g → F) :=
    (LinearEquiv.piCurry (R := F)
      (fun j (_k : Fin (d j.1)) => F)).symm

  exact ⟨d, g,
    ⟨eGlobal.trans eBlocks |>.trans eMultiplicityCurry |>.trans eCarrierCurry⟩⟩

end

end FormalResearch.QIA
