import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.BilinearForm.Properties
import FormalResearch.QIA.PureCopyMemoryCore

/-!
# QI-A real Hermitian trace-pairing core

Source authority: `cmbant/QIprojects@b06a104c594b029aeb0fc2c8f401f8d4c55b901b`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

The pure-copy spanning theorem is a statement about the real vector space of
Hermitian multiplicity operators.  This module works directly with mathlib's
self-adjoint real submodule and the real Hilbert--Schmidt trace form

  `(A,X) ↦ Re (Tr (A X))`.

No normed-space wrapper on raw matrices is introduced.  Nondegeneracy is
proved algebraically by testing a Hermitian direction `A` against itself:
`A * A = Aᴴ * A` is positive semidefinite, its trace is a nonnegative real
scalar, and mathlib's `trace_conjTranspose_mul_self_eq_zero_iff` forces `A = 0`
when that trace vanishes.

This moves the abstract spanning core onto the actual real Hermitian matrix
space used by QI-A.  The source-specific remaining bridge is coherent-power
polarization/separation and its concrete identification with reduced copy
states; the symmetry-reduction/CPTP channel construction also remains outside
this module.
-/

namespace FormalResearch.QIA

open LinearMap Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- The real vector space of Hermitian complex matrices, represented by
mathlib's self-adjoint submodule. -/
abbrev hermitianMatrixSpace (n : Type*) [Fintype n] : Type _ :=
  selfAdjoint.submodule ℝ (Matrix n n ℂ)

/-- The real Hilbert--Schmidt trace pairing on Hermitian matrices. -/
def hermitianTraceBilinForm {n : Type*} [Fintype n] :
    LinearMap.BilinForm ℝ (hermitianMatrixSpace n) :=
  LinearMap.mk₂' ℝ ℝ
    (fun A X => Complex.re (Matrix.trace
      ((A : Matrix n n ℂ) * (X : Matrix n n ℂ))))
    (by intro A B X; simp [add_mul])
    (by intro c A X; simp [smul_mul_assoc])
    (by intro A X Y; simp [mul_add])
    (by intro c A X; simp [mul_smul_comm])

@[simp] theorem hermitianTraceBilinForm_apply
    {n : Type*} [Fintype n] (A X : hermitianMatrixSpace n) :
    hermitianTraceBilinForm A X =
      Complex.re (Matrix.trace
        ((A : Matrix n n ℂ) * (X : Matrix n n ℂ))) := rfl

/-- A Hermitian matrix has nonnegative self-pairing under the real trace form. -/
theorem hermitianTraceBilinForm_self_nonneg
    {n : Type*} [Fintype n]
    (A : hermitianMatrixSpace n) :
    0 ≤ hermitianTraceBilinForm A A := by
  classical
  let M : Matrix n n ℂ := A
  have hstar : Mᴴ = M := by
    simpa [M, Matrix.star_eq_conjTranspose] using A.2.star_eq
  have hpsd : (M * M).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self M
    simpa [hstar] using h
  have htrace_nonneg : 0 ≤ Matrix.trace (M * M) := hpsd.trace_nonneg
  have hre : 0 ≤ Complex.re (Matrix.trace (M * M)) :=
    (RCLike.nonneg_iff.mp htrace_nonneg).1
  simpa [M] using hre

/-- Zero self-pairing is rigid on the Hermitian matrix space. -/
theorem hermitianTraceBilinForm_self_zero_imp
    {n : Type*} [Fintype n]
    (A : hermitianMatrixSpace n)
    (hA : hermitianTraceBilinForm A A = 0) :
    A = 0 := by
  classical
  let M : Matrix n n ℂ := A
  have hstar : Mᴴ = M := by
    simpa [M, Matrix.star_eq_conjTranspose] using A.2.star_eq
  have hre : Complex.re (Matrix.trace (M * M)) = 0 := by
    simpa [M] using hA
  have hpsd : (M * M).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self M
    simpa [hstar] using h
  have htrace_nonneg : 0 ≤ Matrix.trace (M * M) := hpsd.trace_nonneg
  have htrace_self : IsSelfAdjoint (Matrix.trace (M * M)) :=
    IsSelfAdjoint.of_nonneg htrace_nonneg
  have htrace : Matrix.trace (M * M) = 0 := by
    exact (RCLike.re_eq_ofReal_of_isSelfAdjoint htrace_self).mp hre
  have htrace' : Matrix.trace (Mᴴ * M) = 0 := by
    simpa [hstar] using htrace
  have hM : M = 0 :=
    (Matrix.trace_conjTranspose_mul_self_eq_zero_iff).mp htrace'
  apply Subtype.ext
  simpa [M] using hM

/-- The real trace pairing on the Hermitian matrix space is nondegenerate. -/
theorem hermitianTraceBilinForm_nondegenerate
    {n : Type*} [Fintype n] :
    (hermitianTraceBilinForm (n := n)).Nondegenerate := by
  constructor
  · intro A hA
    exact hermitianTraceBilinForm_self_zero_imp A (hA A)
  · intro A hA
    exact hermitianTraceBilinForm_self_zero_imp A (hA A)

/-- In finite dimension, the nondegenerate real Hermitian trace form is
surjective onto the algebraic dual. -/
theorem hermitianTraceBilinForm_surjective
    {n : Type*} [Fintype n] :
    Function.Surjective (hermitianTraceBilinForm (n := n)) := by
  classical
  intro f
  let B := hermitianTraceBilinForm (n := n)
  have hB : B.Nondegenerate := hermitianTraceBilinForm_nondegenerate
  refine ⟨(B.toDual hB).symm f, ?_⟩
  apply LinearMap.ext
  intro X
  simpa [B] using
    (LinearMap.BilinForm.apply_toDual_symm_apply
      (B := B) (hB := hB) f X)

/-- QI-A Hermitian-matrix specialization of the pure-copy spanning core.
Once the chosen Hermitian family separates Hermitian directions under
`Re (Tr (A X))`, it spans the full real Hermitian matrix space.  Pairing
nondegeneracy and dual-surjectivity are internal Lean theorems. -/
theorem hermitianMatrix_span_eq_top_of_trace_separation
    {n : Type*} [Fintype n]
    (s : Set (hermitianMatrixSpace n))
    (hsep : ∀ A : hermitianMatrixSpace n,
      (∀ X ∈ s,
        Complex.re (Matrix.trace
          ((A : Matrix n n ℂ) * (X : Matrix n n ℂ))) = 0) →
      A = 0) :
    Submodule.span ℝ s = ⊤ := by
  apply span_eq_top_of_surjective_pairing_separation
    s (hermitianTraceBilinForm (n := n)) hermitianTraceBilinForm_surjective
  intro A hA
  apply hsep A
  intro X hX
  simpa using hA X hX

end

end FormalResearch.QIA
