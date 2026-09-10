import FormalResearch.QIA.MatrixTracePairing

/-!
# QI-A finite matrix trace adjoint

For finite complex matrix spaces, the nondegenerate bilinear trace pairing
identifies each matrix space with its algebraic dual. Therefore every linear
map between finite matrix algebras has a canonical trace adjoint.

This is purely finite-dimensional linear algebra. It does not assert
positivity, complete positivity, trace preservation, or unitality; those are
the physical channel properties needed separately in QI-A.
-/

namespace FormalResearch.QIA

open LinearMap

noncomputable section

/-- The canonical adjoint of a finite matrix linear map with respect to the
bilinear trace pairing `(A,X) ↦ Tr(A X)`. -/
def matrixTraceAdjoint
    {h q : Type*} [Fintype h] [Fintype q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ) :
    Matrix q q ℂ →ₗ[ℂ] Matrix h h ℂ :=
  (matrixTraceDualEquiv (n := h)).symm.toLinearMap.comp
    (C.dualMap.comp (matrixTraceDualEquiv (n := q)).toLinearMap)

/-- The canonical trace adjoint satisfies the defining trace-duality identity. -/
@[simp] theorem matrixTraceAdjoint_spec
    {h q : Type*} [Fintype h] [Fintype q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (A : Matrix q q ℂ) (X : Matrix h h ℂ) :
    Matrix.trace (A * C X) = Matrix.trace (matrixTraceAdjoint C A * X) := by
  change (matrixTraceDualEquiv (n := q) A) (C X) =
    (matrixTraceDualEquiv (n := h) (matrixTraceAdjoint C A)) X
  rw [← LinearMap.dualMap_apply C (matrixTraceDualEquiv (n := q) A) X]
  simp [matrixTraceAdjoint]

/-- The trace adjoint is unique. Any linear map satisfying the same trace
identity agrees with `matrixTraceAdjoint`. -/
theorem matrixTraceAdjoint_unique
    {h q : Type*} [Fintype h] [Fintype q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (D : Matrix q q ℂ →ₗ[ℂ] Matrix h h ℂ)
    (hD : ∀ (A : Matrix q q ℂ) (X : Matrix h h ℂ),
      Matrix.trace (A * C X) = Matrix.trace (D A * X)) :
    D = matrixTraceAdjoint C := by
  apply LinearMap.ext
  intro A
  classical
  apply (Matrix.ext_iff_trace_mul_right).2
  intro X
  rw [← hD A X]
  exact matrixTraceAdjoint_spec C A X

end

end FormalResearch.QIA
