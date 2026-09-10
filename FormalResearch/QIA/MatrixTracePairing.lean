import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.Trace
import FormalResearch.QIA.PureCopyMemoryCore

/-!
# QI-A matrix trace pairing core

Source authority: `cmbant/QIprojects@b06a104c594b029aeb0fc2c8f401f8d4c55b901b`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

The pure-copy spanning argument ultimately uses the nondegenerate trace pairing
on multiplicity-matrix directions.  `PureCopyMemoryCore` kept surjectivity of
that pairing into the algebraic dual as an explicit hypothesis.  This module
removes that abstract finite-dimensional premise for full complex matrix
blocks: `(A,X) ↦ Tr(A X)` is nondegenerate, hence identifies the matrix space
with its algebraic dual.

For Hermitian matrices the displayed pairing is the usual Hilbert--Schmidt
pairing because `Aᴴ = A`.  The paper's actual spanning theorem is over the real
Hermitian multiplicity algebra; the restriction to that real subspace and,
most importantly, coherent-power polarization/separation remain external.
-/

namespace FormalResearch.QIA

open LinearMap

/-- The complex bilinear trace pairing on a finite square matrix block. -/
def matrixTraceBilinForm {n : Type*} [Fintype n] :
    LinearMap.BilinForm ℂ (Matrix n n ℂ) :=
  LinearMap.mk₂' ℂ ℂ (fun A X => Matrix.trace (A * X))
    (by intro A B X; simp [add_mul])
    (by intro c A X; simp [smul_mul_assoc])
    (by intro A X Y; simp [mul_add])
    (by intro c A X; simp [mul_smul_comm])

@[simp] theorem matrixTraceBilinForm_apply
    {n : Type*} [Fintype n] (A X : Matrix n n ℂ) :
    matrixTraceBilinForm A X = Matrix.trace (A * X) := rfl

/-- The matrix trace pairing is nondegenerate.  Mathlib's trace-extensionality
lemmas are themselves proved by testing against transposed matrix units, so
this is the exact finite matrix-unit separation argument. -/
theorem matrixTraceBilinForm_nondegenerate
    {n : Type*} [Fintype n] :
    (matrixTraceBilinForm (n := n)).Nondegenerate := by
  classical
  constructor
  · intro A hA
    apply (Matrix.ext_iff_trace_mul_right).2
    intro X
    simpa using hA X
  · intro X hX
    apply (Matrix.ext_iff_trace_mul_left).2
    intro A
    simpa using hX A

/-- In finite dimension, the nondegenerate trace form gives a linear
equivalence from the matrix block to its algebraic dual. -/
noncomputable def matrixTraceDualEquiv
    {n : Type*} [Fintype n] :
    Matrix n n ℂ ≃ₗ[ℂ] Module.Dual ℂ (Matrix n n ℂ) :=
  (matrixTraceBilinForm (n := n)).toDual matrixTraceBilinForm_nondegenerate

@[simp] theorem matrixTraceDualEquiv_apply
    {n : Type*} [Fintype n] (A X : Matrix n n ℂ) :
    matrixTraceDualEquiv A X = Matrix.trace (A * X) := rfl

/-- The trace pairing, viewed as a linear map into the algebraic dual, is
surjective.  This discharges the abstract `hpair` premise in
`span_eq_top_of_surjective_pairing_separation` for a full matrix block. -/
theorem matrixTraceBilinForm_surjective
    {n : Type*} [Fintype n] :
    Function.Surjective (matrixTraceBilinForm (n := n)) := by
  classical
  intro f
  let B := matrixTraceBilinForm (n := n)
  have hB : B.Nondegenerate := matrixTraceBilinForm_nondegenerate
  refine ⟨(B.toDual hB).symm f, ?_⟩
  apply LinearMap.ext
  intro X
  simpa [B] using
    (LinearMap.BilinForm.apply_toDual_symm_apply
      (B := B) (hB := hB) f X)

/-- Concrete full-matrix specialization of the abstract pure-copy spanning
core: once trace pairing with every member of `s` separates matrices, `s`
spans the whole matrix block.  No pairing-surjectivity hypothesis remains. -/
theorem matrix_span_eq_top_of_trace_separation
    {n : Type*} [Fintype n]
    (s : Set (Matrix n n ℂ))
    (hsep : ∀ A : Matrix n n ℂ,
      (∀ X ∈ s, Matrix.trace (A * X) = 0) → A = 0) :
    Submodule.span ℂ s = ⊤ := by
  apply span_eq_top_of_surjective_pairing_separation
    s (matrixTraceBilinForm (n := n)) matrixTraceBilinForm_surjective
  intro A hA
  apply hsep A
  intro X hX
  simpa using hA X hX

end FormalResearch.QIA
