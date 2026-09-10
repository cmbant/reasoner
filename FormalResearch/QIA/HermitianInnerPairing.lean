import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.BilinearForm.Properties
import FormalResearch.QIA.PureCopyMemoryCore

/-!
# QI-A real Hermitian inner-pairing core

Source authority: `cmbant/QIprojects@b06a104c594b029aeb0fc2c8f401f8d4c55b901b`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

The pure-copy spanning theorem is naturally a statement about the real vector
space of Hermitian multiplicity operators.  The previous matrix trace-pairing
module discharged nondegeneracy and dual-surjectivity on the full complex
matrix block.  Here we move the abstract spanning theorem onto the actual real
Hermitian vector space used by the paper.

The key observation is structural rather than matrix-specific: over `ℝ`, the
inner product is a nondegenerate bilinear form, hence in finite dimension it
identifies the space with its algebraic dual.  Mathlib already represents
self-adjoint elements as the real submodule `selfAdjoint.submodule ℝ A`, so no
custom Hermitian wrapper is introduced.

This still does not prove the coherent-power polarization/separation theorem,
or identify the reduced coherent-copy expectation functional with the
Hilbert--Schmidt pairing.  Those remain the source-specific bridge.
-/

namespace FormalResearch.QIA

open LinearMap
open scoped InnerProductSpace

noncomputable section

/-- The inner product of a real inner-product space, bundled as a bilinear
form. -/
def realInnerBilinForm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    LinearMap.BilinForm ℝ E :=
  innerₛₗ ℝ

@[simp] theorem realInnerBilinForm_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) :
    realInnerBilinForm E x y = ⟪x, y⟫_ℝ := rfl

/-- The real inner-product bilinear form is nondegenerate. -/
theorem realInnerBilinForm_nondegenerate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    (realInnerBilinForm E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (by
      simpa [realInnerBilinForm] using hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (by
      simpa [realInnerBilinForm] using hx x)

/-- In finite dimension, the real inner product is surjective onto the
algebraic dual. -/
theorem realInnerBilinForm_surjective
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Function.Surjective (realInnerBilinForm E) := by
  let B := realInnerBilinForm E
  have hB : B.Nondegenerate := realInnerBilinForm_nondegenerate E
  intro f
  refine ⟨(B.toDual hB).symm f, ?_⟩
  apply LinearMap.ext
  intro x
  simpa [B] using
    (LinearMap.BilinForm.apply_toDual_symm_apply
      (B := B) (hB := hB) f x)

/-- Finite-dimensional real inner-product specialization of the pure-copy
spanning core.  Pairing surjectivity is now internal: only separation of the
chosen family remains as a hypothesis. -/
theorem real_inner_span_eq_top_of_separation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (s : Set E)
    (hsep : ∀ y : E, (∀ x ∈ s, ⟪y, x⟫_ℝ = 0) → y = 0) :
    Submodule.span ℝ s = ⊤ := by
  apply span_eq_top_of_surjective_pairing_separation
    s (realInnerBilinForm E) (realInnerBilinForm_surjective E)
  intro y hy
  apply hsep y
  intro x hx
  simpa [realInnerBilinForm] using hy x hx

/-- The real vector space of Hermitian complex matrices, using mathlib's
self-adjoint submodule rather than a custom wrapper. -/
abbrev hermitianMatrixSpace (n : Type*) [Fintype n] : Type _ :=
  selfAdjoint.submodule ℝ (Matrix n n ℂ)

/-- The span theorem on the real Hermitian matrix space used by QI-A.  Once the
reduced coherent-copy family separates Hermitian directions under the inherited
Hilbert--Schmidt inner product, it spans the entire Hermitian block. -/
theorem hermitianMatrix_span_eq_top_of_inner_separation
    {n : Type*} [Fintype n]
    (s : Set (hermitianMatrixSpace n))
    (hsep : ∀ A : hermitianMatrixSpace n,
      (∀ X ∈ s, ⟪A, X⟫_ℝ = 0) → A = 0) :
    Submodule.span ℝ s = ⊤ := by
  exact real_inner_span_eq_top_of_separation s hsep

end

end FormalResearch.QIA
