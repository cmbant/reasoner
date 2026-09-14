import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Semisimplicity of finite-dimensional unitary representations

A group representation on a finite-dimensional complex inner-product space is
completely reducible whenever each group element preserves the inner product.
The proof is the standard orthogonal-complement argument: the orthogonal
complement of an invariant subspace is invariant because the inverse action can
be moved to the first argument of the inner product.

This file does not construct any particular physical local-unitary action, nor
does it identify symmetric-power Schur--Weyl sectors.  It only discharges
semisimplicity once an inner-product-preserving representation has been supplied.
-/

namespace FormalResearch.QIA

open scoped MonoidAlgebra

noncomputable section

/-- A representation preserves the complex inner product elementwise. -/
def IsInnerPreservingRepresentation
    {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ρ : Representation ℂ G E) : Prop :=
  ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

/-- Every finite-dimensional complex inner-product-preserving group
representation is semisimple.  The complement of an invariant subspace is its
orthogonal complement. -/
theorem isSemisimpleRepresentation_of_innerPreserving
    {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E)
    (hunitary : IsInnerPreservingRepresentation ρ) :
    Representation.IsSemisimpleRepresentation ρ := by
  constructor
  intro p
  let q : Subrepresentation ρ :=
    { toSubmodule := p.toSubmoduleᗮ
      apply_mem_toSubmodule := by
        intro g v hv
        intro w hw
        rw [← Representation.self_inv_apply ρ g w, hunitary g]
        exact hv _ (p.apply_mem_toSubmodule g⁻¹ hw) }
  refine ⟨q, ?_⟩
  constructor
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    simpa [q] using (p.toSubmodule.isCompl_orthogonal.disjoint.eq_bot)
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    simpa [q] using (p.toSubmodule.isCompl_orthogonal.codisjoint.eq_top)

/-- The associated complex group-algebra module is semisimple under the same
finite-dimensional inner-product-preservation hypothesis. -/
theorem isSemisimpleModule_asModule_of_innerPreserving
    {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E)
    (hunitary : IsInnerPreservingRepresentation ρ) :
    IsSemisimpleModule ℂ[G] ρ.asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact isSemisimpleRepresentation_of_innerPreserving ρ hunitary

end

end FormalResearch.QIA
