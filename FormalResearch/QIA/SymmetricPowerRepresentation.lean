import FormalResearch.QIA.SymmetricPowerFunctoriality
import Mathlib.RepresentationTheory.Basic

/-!
# Algebraic representations on symmetric power

The algebraic symmetric-power map from `SymmetricPowerFunctoriality` preserves
identity and composition.  Consequently, any supplied linear monoid
representation on the one-copy module induces an algebraic representation on its
symmetric tensor power.

This file is deliberately representation-theoretic but still purely algebraic: it
does not construct the manuscript's physical local-unitary action, add a Hilbert
space structure to `SymmetricPower`, prove unitarity or isometry, prove
semisimplicity, or identify Schur--Weyl sectors.
-/

namespace FormalResearch.QIA

noncomputable section

universe u v w z

/-- Symmetric-power functoriality preserves the identity linear map. -/
@[simp]
theorem symmetricPowerMap_id
    {R ι : Type u} {M : Type v}
    [CommSemiring R]
    [AddCommMonoid M] [Module R M] :
    symmetricPowerMap (ι := ι) (LinearMap.id : M →ₗ[R] M) =
      (LinearMap.id : SymmetricPower R ι M →ₗ[R] SymmetricPower R ι M) := by
  apply LinearMap.ext_on
    (SymmetricPower.span_tprod_eq_top (R := R) (ι := ι) (M := M))
  rintro _ ⟨x, rfl⟩
  simp

/-- Symmetric-power functoriality preserves composition. -/
@[simp]
theorem symmetricPowerMap_comp
    {R ι : Type u} {M : Type v} {N : Type w} {P : Type z}
    [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    symmetricPowerMap (ι := ι) (g.comp f) =
      (symmetricPowerMap (ι := ι) g).comp (symmetricPowerMap (ι := ι) f) := by
  apply LinearMap.ext_on
    (SymmetricPower.span_tprod_eq_top (R := R) (ι := ι) (M := M))
  rintro _ ⟨x, rfl⟩
  simp

/-- Any supplied algebraic representation on the one-copy module induces a
representation on algebraic symmetric power by applying the action in every tensor
factor. -/
noncomputable def symmetricPowerRepresentation
    {R ι G : Type u} {M : Type v}
    [CommSemiring R] [Monoid G]
    [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) :
    Representation R G (SymmetricPower R ι M) where
  toFun g := symmetricPowerMap (ι := ι) (ρ g)
  map_one' := by
    rw [map_one]
    simpa only [Module.End.one_eq_id] using
      (symmetricPowerMap_id (R := R) (ι := ι) (M := M))
  map_mul' g h := by
    rw [map_mul]
    simpa only [Module.End.mul_eq_comp] using
      (symmetricPowerMap_comp (ι := ι) (g := ρ g) (f := ρ h))

/-- The induced representation acts on a pure symmetric tensor by applying the
one-copy representation in every slot. -/
@[simp]
theorem symmetricPowerRepresentation_tprod
    {R ι G : Type u} {M : Type v}
    [CommSemiring R] [Monoid G]
    [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) (g : G) (x : ι → M) :
    symmetricPowerRepresentation (ι := ι) ρ g (SymmetricPower.tprod R x) =
      SymmetricPower.tprod R (fun i => ρ g (x i)) := by
  exact symmetricPowerMap_tprod (ρ g) x

end

end FormalResearch.QIA
