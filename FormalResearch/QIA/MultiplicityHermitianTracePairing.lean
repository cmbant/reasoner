import Mathlib.LinearAlgebra.Pi
import FormalResearch.QIA.HermitianInnerPairing

/-!
# QI-A finite multiplicity Hermitian trace-pairing core

Source authority: `cmbant/QIprojects@d3e3d2e2a74201a178cd73ca7ef249b861c4f57e`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

QI-A's reduced multiplicity algebra is a finite direct sum of full matrix
blocks.  On Hermitian elements this is a finite real product of Hermitian
matrix spaces.  `HermitianInnerPairing` proves that the real trace form

  `(A,X) ↦ Re (Tr (A X))`

is nondegenerate on one Hermitian block.  This module lifts that statement to
a finite multiplicity profile by summing the block trace forms.  The lift is
proved one sector at a time using `Pi.single`, so no positivity or cancellation
argument for the total sum is required.

The resulting span theorem has the same finite Hermitian target as the
manuscript's pure-copy spanning theorem.  What remains source-specific is to
show that the reduced coherent-copy family separates every Hermitian direction
under this summed trace pairing (the coherent-power polarization/separation
bridge), together with the concrete symmetry-reduction/CPTP identification.
-/

namespace FormalResearch.QIA

open LinearMap Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- The real Hermitian part of a finite multiplicity-block algebra with block
sizes `g a`.  For finite sector labels this is the finite direct product, hence
canonically the same vector-space object as the finite direct sum. -/
abbrev multiplicityHermitianSpace
    {α : Type*} [Fintype α] (g : α → Nat) : Type _ :=
  ∀ a, hermitianMatrixSpace (Fin (g a))

/-- Sum of the real Hermitian trace pairings over all multiplicity blocks. -/
def multiplicityHermitianTraceBilinForm
    {α : Type*} [Fintype α] (g : α → Nat) :
    LinearMap.BilinForm ℝ (multiplicityHermitianSpace g) :=
  LinearMap.mk₂' ℝ ℝ
    (fun A X => ∑ a, hermitianTraceBilinForm (A a) (X a))
    (by intro A B X; simp [Finset.sum_add_distrib])
    (by intro c A X; simp [Finset.mul_sum])
    (by intro A X Y; simp [mul_add, Finset.sum_add_distrib])
    (by intro c A X; simp [Finset.mul_sum])

@[simp] theorem multiplicityHermitianTraceBilinForm_apply
    {α : Type*} [Fintype α] (g : α → Nat)
    (A X : multiplicityHermitianSpace g) :
    multiplicityHermitianTraceBilinForm g A X =
      ∑ a, Complex.re (Matrix.trace
        (((A a : hermitianMatrixSpace (Fin (g a))) :
            Matrix (Fin (g a)) (Fin (g a)) ℂ) *
         ((X a : hermitianMatrixSpace (Fin (g a))) :
            Matrix (Fin (g a)) (Fin (g a)) ℂ))) := by
  simp [multiplicityHermitianTraceBilinForm]

/-- Pairing against a vector supported in one sector reduces to that sector's
Hermitian trace pairing.  Kept as a small explicit lemma so dependent
`Pi.single` normalization does not burden the main nondegeneracy proof. -/
theorem multiplicityHermitianTraceBilinForm_single_right
    {α : Type*} [Fintype α] [DecidableEq α] (g : α → Nat)
    (A : multiplicityHermitianSpace g) (a : α)
    (X : hermitianMatrixSpace (Fin (g a))) :
    multiplicityHermitianTraceBilinForm g A (Pi.single a X) =
      hermitianTraceBilinForm (A a) X := by
  change (∑ b, hermitianTraceBilinForm (A b) ((Pi.single a X) b)) =
    hermitianTraceBilinForm (A a) X
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hba
    rw [Pi.single_eq_of_ne hba]
    exact map_zero _
  · simp

/-- The analogous one-sector reduction in the first argument. -/
theorem multiplicityHermitianTraceBilinForm_single_left
    {α : Type*} [Fintype α] [DecidableEq α] (g : α → Nat)
    (A : multiplicityHermitianSpace g) (a : α)
    (X : hermitianMatrixSpace (Fin (g a))) :
    multiplicityHermitianTraceBilinForm g (Pi.single a X) A =
      hermitianTraceBilinForm X (A a) := by
  change (∑ b, hermitianTraceBilinForm ((Pi.single a X) b) (A b)) =
    hermitianTraceBilinForm X (A a)
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hba
    rw [Pi.single_eq_of_ne hba]
    exact LinearMap.zero_apply _
  · simp

/-- The summed trace form is nondegenerate on the full finite Hermitian
multiplicity algebra.  A vector in either kernel is tested against a function
supported only in one sector, reducing immediately to block nondegeneracy. -/
theorem multiplicityHermitianTraceBilinForm_nondegenerate
    {α : Type*} [Fintype α] (g : α → Nat) :
    (multiplicityHermitianTraceBilinForm g).Nondegenerate := by
  classical
  constructor
  · intro A hA
    funext a
    apply (hermitianTraceBilinForm_nondegenerate
      (n := Fin (g a))).1
    intro X
    have h := hA (Pi.single a X)
    rw [multiplicityHermitianTraceBilinForm_single_right
      (α := α) g A a X] at h
    exact h
  · intro A hA
    funext a
    apply (hermitianTraceBilinForm_nondegenerate
      (n := Fin (g a))).2
    intro X
    have h := hA (Pi.single a X)
    rw [multiplicityHermitianTraceBilinForm_single_left
      (α := α) g A a X] at h
    exact h

/-- In finite dimension the summed nondegenerate trace form identifies the
full Hermitian multiplicity algebra with its algebraic dual. -/
theorem multiplicityHermitianTraceBilinForm_surjective
    {α : Type*} [Fintype α] (g : α → Nat) :
    Function.Surjective (multiplicityHermitianTraceBilinForm g) := by
  classical
  intro f
  let B := multiplicityHermitianTraceBilinForm g
  have hB : B.Nondegenerate :=
    multiplicityHermitianTraceBilinForm_nondegenerate (α := α) g
  refine ⟨(B.toDual hB).symm f, ?_⟩
  apply LinearMap.ext
  intro X
  simpa [B] using
    (LinearMap.BilinForm.apply_toDual_symm_apply
      (B := B) (hB := hB) f X)

/-- QI-A finite multiplicity-algebra specialization of the pure-copy spanning
core.  Once a Hermitian family separates all Hermitian directions under the
summed block trace pairing, it spans the entire real Hermitian multiplicity
algebra.  Pairing nondegeneracy and dual-surjectivity are internal theorems. -/
theorem multiplicityHermitian_span_eq_top_of_trace_separation
    {α : Type*} [Fintype α] (g : α → Nat)
    (s : Set (multiplicityHermitianSpace g))
    (hsep : ∀ A : multiplicityHermitianSpace g,
      (∀ X ∈ s,
        ∑ a, Complex.re (Matrix.trace
          (((A a : hermitianMatrixSpace (Fin (g a))) :
              Matrix (Fin (g a)) (Fin (g a)) ℂ) *
           ((X a : hermitianMatrixSpace (Fin (g a))) :
              Matrix (Fin (g a)) (Fin (g a)) ℂ))) = 0) →
      A = 0) :
    Submodule.span ℝ s = ⊤ := by
  apply span_eq_top_of_surjective_pairing_separation
    s (multiplicityHermitianTraceBilinForm g)
      (multiplicityHermitianTraceBilinForm_surjective (α := α) g)
  intro A hA
  apply hsep A
  intro X hX
  simpa using hA X hX

end

end FormalResearch.QIA
