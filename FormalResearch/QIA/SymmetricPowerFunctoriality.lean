import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Functoriality of algebraic symmetric tensor power

Mathlib's algebraic `SymmetricPower` is defined as a quotient of an indexed tensor
power by permutation relations, but the pinned API does not yet expose the induced
map on symmetric power from a linear map on the one-copy space.

This file supplies that quotient descent directly.  It is deliberately algebraic:
there is no topology, inner product, group action, semisimplicity, or Schur--Weyl
claim here.
-/

namespace FormalResearch.QIA

open scoped TensorProduct

noncomputable section

universe u v w

/-- A linear map on the one-copy space descends functorially to algebraic symmetric
power by applying it in every tensor factor before passing to the permutation
quotient. -/
def symmetricPowerMap
    {R ι : Type u} {M : Type v} {N : Type w}
    [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) :
    SymmetricPower R ι M →ₗ[R] SymmetricPower R ι N where
  __ :=
    AddCon.lift _
      ((SymmetricPower.mk R ι N).comp
        (PiTensorProduct.map (fun _ : ι => f))).toAddMonoidHom
      (AddCon.addConGen_le.2 fun _ _ h => by
        cases h with
        | perm e x =>
            change
              SymmetricPower.mk R ι N
                  (PiTensorProduct.map (fun _ : ι => f)
                    (PiTensorProduct.tprod R x)) =
                SymmetricPower.mk R ι N
                  (PiTensorProduct.map (fun _ : ι => f)
                    (PiTensorProduct.tprod R (fun i => x (e i))))
            rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
            exact
              (SymmetricPower.tprod_equiv e (fun i => f (x i))).symm)
  map_smul' r := by
    rintro ⟨x⟩
    exact map_smul
      ((SymmetricPower.mk R ι N).comp
        (PiTensorProduct.map (fun _ : ι => f))) r x

/-- The descended map acts on a pure symmetric tensor by applying the original
linear map in every slot. -/
@[simp]
theorem symmetricPowerMap_tprod
    {R ι : Type u} {M : Type v} {N : Type w}
    [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (x : ι → M) :
    symmetricPowerMap f (SymmetricPower.tprod R x) =
      SymmetricPower.tprod R (fun i => f (x i)) := by
  change
    SymmetricPower.mk R ι N
        (PiTensorProduct.map (fun _ : ι => f)
          (PiTensorProduct.tprod R x)) =
      SymmetricPower.tprod R (fun i => f (x i))
  rw [PiTensorProduct.map_tprod]
  rfl

end

end FormalResearch.QIA
