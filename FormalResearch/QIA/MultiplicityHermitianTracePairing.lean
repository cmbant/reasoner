import Mathlib.LinearAlgebra.Pi
import FormalResearch.QIA.HermitianInnerPairing

/-!
# QI-A finite multiplicity Hermitian trace-pairing core

Source authority: `cmbant/QIprojects@d3e3d2e2a74201a178cd73ca7ef249b861c4f57e`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

QI-A's reduced multiplicity algebra is a finite direct sum of full matrix
blocks. On Hermitian elements this is a finite real product of Hermitian
matrix spaces. `HermitianInnerPairing` proves that the real trace form

  `(A,X) ↦ Re (Tr (A X))`

is nondegenerate on one Hermitian block. This module lifts that statement to
a finite multiplicity profile by summing the block trace forms.

The product nondegeneracy proof tests a direction against itself. Every block
self-pairing is nonnegative, so a zero total self-pairing makes every block
self-pairing zero; one-block rigidity then kills every component. This avoids
any dependent-coordinate update machinery.

The resulting span theorem has the same finite Hermitian target as the
manuscript's pure-copy spanning theorem. Combining it with the generic
recovery-extension lemma also gives the manuscript's part-(ii) linear step:
once the chosen family separates and is fixed by recovery after encoding, the
recovery composite is the identity on the whole Hermitian multiplicity space.

What remains source-specific is to show that the reduced coherent-copy family
separates every Hermitian direction under this summed trace pairing (the
coherent-power polarization/separation bridge), together with the concrete
symmetry-reduction/CPTP identification.
-/

namespace FormalResearch.QIA

open LinearMap Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- The real Hermitian part of a finite multiplicity-block algebra with block
sizes `g a`. For finite sector labels this finite product is canonically the
same vector-space object as the finite direct sum. -/
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

/-- Zero total self-pairing is rigid on the finite Hermitian multiplicity
algebra. Nonnegativity of every block turns the zero sum into blockwise zero
self-pairings. -/
theorem multiplicityHermitianTraceBilinForm_self_zero_imp
    {α : Type*} [Fintype α] (g : α → Nat)
    (A : multiplicityHermitianSpace g)
    (hA : multiplicityHermitianTraceBilinForm g A A = 0) :
    A = 0 := by
  classical
  change (∑ a, hermitianTraceBilinForm (A a) (A a)) = 0 at hA
  have hnonneg :
      ∀ a ∈ (Finset.univ : Finset α),
        0 ≤ hermitianTraceBilinForm (A a) (A a) :=
    fun a _ => hermitianTraceBilinForm_self_nonneg (A a)
  have hzero :
      ∀ a ∈ (Finset.univ : Finset α),
        hermitianTraceBilinForm (A a) (A a) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hA
  funext a
  exact hermitianTraceBilinForm_self_zero_imp
    (A a) (hzero a (Finset.mem_univ a))

/-- The summed trace form is nondegenerate on the full finite Hermitian
multiplicity algebra. -/
theorem multiplicityHermitianTraceBilinForm_nondegenerate
    {α : Type*} [Fintype α] (g : α → Nat) :
    (multiplicityHermitianTraceBilinForm g).Nondegenerate := by
  constructor
  · intro A hA
    exact multiplicityHermitianTraceBilinForm_self_zero_imp g A (hA A)
  · intro A hA
    exact multiplicityHermitianTraceBilinForm_self_zero_imp g A (hA A)

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
core. Once a Hermitian family separates all Hermitian directions under the
summed block trace pairing, it spans the entire real Hermitian multiplicity
algebra. Pairing nondegeneracy and dual-surjectivity are internal theorems. -/
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

/-- Manuscript part-(ii) linear consequence on the actual finite Hermitian
multiplicity space. Trace separation makes the chosen family span; therefore
any linear encoding/recovery pair that fixes that family has identity
composite on the entire Hermitian multiplicity algebra. This theorem does not
assert that `C` or `R` are physical quantum channels; the concrete CPTP bridge
remains separate. -/
theorem multiplicityHermitian_recovery_comp_encoding_eq_id_of_trace_separation
    {α M : Type*} [Fintype α] (g : α → Nat)
    [AddCommMonoid M] [Module ℝ M]
    (s : Set (multiplicityHermitianSpace g))
    (hsep : ∀ A : multiplicityHermitianSpace g,
      (∀ X ∈ s,
        ∑ a, Complex.re (Matrix.trace
          (((A a : hermitianMatrixSpace (Fin (g a))) :
              Matrix (Fin (g a)) (Fin (g a)) ℂ) *
           ((X a : hermitianMatrixSpace (Fin (g a))) :
              Matrix (Fin (g a)) (Fin (g a)) ℂ))) = 0) →
      A = 0)
    (C : multiplicityHermitianSpace g →ₗ[ℝ] M)
    (R : M →ₗ[ℝ] multiplicityHermitianSpace g)
    (hfix : ∀ X ∈ s, R (C X) = X) :
    R.comp C = LinearMap.id := by
  exact recovery_comp_encoding_eq_id_of_fix_spanning_family
    s (multiplicityHermitian_span_eq_top_of_trace_separation g s hsep)
      C R hfix

end

end FormalResearch.QIA
