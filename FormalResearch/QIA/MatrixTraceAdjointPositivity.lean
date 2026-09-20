import FormalResearch.QIA.MatrixTraceAdjoint
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Complex.Module

/-!
# QI-A positivity of the finite matrix trace adjoint

For finite complex matrix algebras, the positive-semidefinite cone is self-dual
for the bilinear trace pairing used by `matrixTraceAdjoint`.  Consequently, if
a complex-linear Schrödinger-picture map preserves positive semidefinite
matrices, then its canonical trace adjoint also preserves positive semidefinite
matrices.

This is the finite-dimensional positivity bridge needed by the deferred-query
memory converse.  It does not assert complete positivity.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- The trace pairing of two positive-semidefinite complex matrices is
nonnegative.  Factoring the second matrix as `Xᴴ X` and cycling the trace turns
this into the trace of the positive-semidefinite congruence `X A Xᴴ`. -/
theorem matrix_trace_mul_nonneg_of_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  classical
  obtain ⟨X, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [star_eq_conjTranspose, Matrix.trace_mul_cycle']
  simpa [Matrix.mul_assoc] using
    (hA.mul_mul_conjTranspose_same X).trace_nonneg

/-- A complex-linear matrix map that preserves positive-semidefinite matrices
also preserves conjugate transpose.  This packages the map as Mathlib's
`PositiveLinearMap`; positivity then supplies the star-hom property on the
self-adjoint-decomposable matrix order. -/
theorem matrixLinearMap_map_conjTranspose_of_posSemidef_preserving
    {h q : Type*} [Fintype h] [DecidableEq h]
    [Fintype q] [DecidableEq q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (hCpos : ∀ X : Matrix h h ℂ, X.PosSemidef → (C X).PosSemidef)
    (X : Matrix h h ℂ) :
    C Xᴴ = (C X)ᴴ := by
  let Cp : Matrix h h ℂ →ₚ[ℂ] Matrix q q ℂ :=
    PositiveLinearMap.mk₀ C (by
      intro Y hY
      exact (hCpos Y hY.posSemidef).nonneg)
  change Cp Xᴴ = (Cp X)ᴴ
  exact map_star Cp X

/-- If `C` preserves positive-semidefinite matrices, then its canonical trace
adjoint sends Hermitian matrices to Hermitian matrices. -/
theorem matrixTraceAdjoint_isHermitian_of_posSemidef_preserving
    {h q : Type*} [Fintype h] [DecidableEq h]
    [Fintype q] [DecidableEq q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (hCpos : ∀ X : Matrix h h ℂ, X.PosSemidef → (C X).PosSemidef)
    {A : Matrix q q ℂ} (hA : A.IsHermitian) :
    (matrixTraceAdjoint C A).IsHermitian := by
  let M : Matrix h h ℂ := matrixTraceAdjoint C A
  change Mᴴ = M
  apply (Matrix.ext_iff_trace_mul_right).2
  intro X
  calc
    Matrix.trace (Mᴴ * X) = star (Matrix.trace (M * Xᴴ)) := by
      rw [← Matrix.trace_conjTranspose]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      exact Matrix.trace_mul_comm _ _
    _ = star (Matrix.trace (A * C Xᴴ)) := by
      rw [← matrixTraceAdjoint_spec C A Xᴴ]
    _ = star (Matrix.trace (A * (C X)ᴴ)) := by
      rw [matrixLinearMap_map_conjTranspose_of_posSemidef_preserving C hCpos X]
    _ = Matrix.trace (A * C X) := by
      rw [← Matrix.trace_conjTranspose]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq]
      exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (M * X) := by
      exact matrixTraceAdjoint_spec C A X

/-- Positivity transport for the canonical finite matrix trace adjoint.

If a complex-linear map sends every positive-semidefinite source matrix to a
positive-semidefinite target matrix, then its trace adjoint has the same
property. -/
theorem matrixTraceAdjoint_posSemidef_of_posSemidef_preserving
    {h q : Type*} [Fintype h] [DecidableEq h]
    [Fintype q] [DecidableEq q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (hCpos : ∀ X : Matrix h h ℂ, X.PosSemidef → (C X).PosSemidef)
    {A : Matrix q q ℂ} (hA : A.PosSemidef) :
    (matrixTraceAdjoint C A).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (matrixTraceAdjoint_isHermitian_of_posSemidef_preserving C hCpos hA.isHermitian)
  intro x
  let R : Matrix h h ℂ := Matrix.vecMulVec x (star x)
  have hR : R.PosSemidef := by
    simpa [R] using Matrix.posSemidef_vecMulVec_self_star x
  have hCR : (C R).PosSemidef := hCpos R hR
  have hnonneg : 0 ≤ Matrix.trace (A * C R) :=
    matrix_trace_mul_nonneg_of_posSemidef hA hCR
  rw [matrixTraceAdjoint_spec C A R] at hnonneg
  simpa [R, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] using hnonneg

end

end FormalResearch.QIA
