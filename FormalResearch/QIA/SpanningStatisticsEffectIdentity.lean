import FormalResearch.QIA.MultiplicityHermitianTracePairing

/-!
# QI-A spanning-statistics effect identity

Source authority: `cmbant/QIprojects@f96b5b0be457867f068fc40461853048e346239d`,
`QI-A/paper/finite_copy_quantum_memory.tex`, manuscript blob
`6f4af839cc7c13b0cb2b3704fcefdeb1d88e9195`.

In the deferred-query proof, exact agreement of physical query statistics is
first known only on the coherent-copy family. Once that family spans the full
real Hermitian source space, equality of all trace statistics on the family
forces equality of the corresponding Hermitian effects.

This module formalizes that finite linear-algebra extension both on one full
Hermitian matrix space (matching the manuscript's symmetric-space operator
identity) and on the finite Hermitian multiplicity algebra. It does not prove
that the physical coherent-copy family spans; that remains the source-specific
coherent-power polarization/separation bridge.
-/

namespace FormalResearch.QIA

open LinearMap Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Two Hermitian matrices with the same real trace statistics on a spanning
Hermitian family are equal. This is the full-source-space form used after
coherent-copy spanning in the deferred-query argument. -/
theorem hermitianMatrix_eq_of_trace_eq_on_spanning_family
    {n : Type*} [Fintype n]
    (s : Set (hermitianMatrixSpace n))
    (hspan : Submodule.span ℝ s = ⊤)
    (A B : hermitianMatrixSpace n)
    (hstats : ∀ X ∈ s,
      hermitianTraceBilinForm A X = hermitianTraceBilinForm B X) :
    A = B := by
  let f : hermitianMatrixSpace n →ₗ[ℝ] ℝ := hermitianTraceBilinForm (A - B)
  have hf_generator : ∀ X ∈ s, f X = 0 := by
    intro X hX
    simp [f, hstats X hX]
  have hfOn : Set.EqOn f (0 : hermitianMatrixSpace n →ₗ[ℝ] ℝ)
      (Submodule.span ℝ s) :=
    (LinearMap.eqOn_span_iff).2 (by
      intro X hX
      simpa using hf_generator X hX)
  have hf_zero : ∀ X : hermitianMatrixSpace n,
      hermitianTraceBilinForm (A - B) X = 0 := by
    intro X
    have hX : X ∈ Submodule.span ℝ s := by
      rw [hspan]
      exact Submodule.mem_top
    have h := hfOn hX
    simpa [f] using h
  have hAB : A - B = 0 :=
    (hermitianTraceBilinForm_nondegenerate (n := n)).1 (A - B) hf_zero
  exact sub_eq_zero.mp hAB

/-- Separation-specialized full-matrix version. Once the chosen Hermitian
family separates all Hermitian directions, equality of its trace statistics
forces operator equality. -/
theorem hermitianMatrix_eq_of_trace_eq_on_separating_family
    {n : Type*} [Fintype n]
    (s : Set (hermitianMatrixSpace n))
    (hsep : ∀ D : hermitianMatrixSpace n,
      (∀ X ∈ s,
        Complex.re (Matrix.trace
          ((D : Matrix n n ℂ) * (X : Matrix n n ℂ))) = 0) →
      D = 0)
    (A B : hermitianMatrixSpace n)
    (hstats : ∀ X ∈ s,
      hermitianTraceBilinForm A X = hermitianTraceBilinForm B X) :
    A = B := by
  exact hermitianMatrix_eq_of_trace_eq_on_spanning_family
    s (hermitianMatrix_span_eq_top_of_trace_separation s hsep) A B hstats

/-- Two Hermitian multiplicity-algebra elements with the same trace statistics
on a spanning Hermitian family are equal. -/
theorem multiplicityHermitian_eq_of_trace_eq_on_spanning_family
    {α : Type*} [Fintype α] (g : α → Nat)
    (s : Set (multiplicityHermitianSpace g))
    (hspan : Submodule.span ℝ s = ⊤)
    (A B : multiplicityHermitianSpace g)
    (hstats : ∀ X ∈ s,
      multiplicityHermitianTraceBilinForm g A X =
        multiplicityHermitianTraceBilinForm g B X) :
    A = B := by
  let f : multiplicityHermitianSpace g →ₗ[ℝ] ℝ :=
    multiplicityHermitianTraceBilinForm g (A - B)
  have hf_generator : ∀ X ∈ s, f X = 0 := by
    intro X hX
    simp [f, hstats X hX]
  have hfOn : Set.EqOn f (0 : multiplicityHermitianSpace g →ₗ[ℝ] ℝ)
      (Submodule.span ℝ s) :=
    (LinearMap.eqOn_span_iff).2 (by
      intro X hX
      simpa using hf_generator X hX)
  have hf_zero : ∀ X : multiplicityHermitianSpace g,
      multiplicityHermitianTraceBilinForm g (A - B) X = 0 := by
    intro X
    have hX : X ∈ Submodule.span ℝ s := by
      rw [hspan]
      exact Submodule.mem_top
    have h := hfOn hX
    simpa [f] using h
  have hAB : A - B = 0 :=
    (multiplicityHermitianTraceBilinForm_nondegenerate g).1 (A - B) hf_zero
  exact sub_eq_zero.mp hAB

/-- Separation-specialized multiplicity version: if the chosen family
separates Hermitian directions under the summed trace pairing, then equality
of trace statistics on that family forces equality of Hermitian effects. -/
theorem multiplicityHermitian_eq_of_trace_eq_on_separating_family
    {α : Type*} [Fintype α] (g : α → Nat)
    (s : Set (multiplicityHermitianSpace g))
    (hsep : ∀ D : multiplicityHermitianSpace g,
      (∀ X ∈ s,
        ∑ a, Complex.re (Matrix.trace
          (((D a : hermitianMatrixSpace (Fin (g a))) :
              Matrix (Fin (g a)) (Fin (g a)) ℂ) *
           ((X a : hermitianMatrixSpace (Fin (g a))) :
              Matrix (Fin (g a)) (Fin (g a)) ℂ))) = 0) →
      D = 0)
    (A B : multiplicityHermitianSpace g)
    (hstats : ∀ X ∈ s,
      multiplicityHermitianTraceBilinForm g A X =
        multiplicityHermitianTraceBilinForm g B X) :
    A = B := by
  exact multiplicityHermitian_eq_of_trace_eq_on_spanning_family
    g s (multiplicityHermitian_span_eq_top_of_trace_separation g s hsep)
      A B hstats

end

end FormalResearch.QIA
