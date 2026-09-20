import FormalResearch.QIA.DeferredQueryPostSeparationMemoryBound
import FormalResearch.QIA.SpanningStatisticsEffectIdentity

/-!
# QI-A deferred-query memory converse from a spanning source family

Source authority: `cmbant/QIprojects@f96b5b0be457867f068fc40461853048e346239d`,
`QI-A/paper/finite_copy_quantum_memory.tex`, manuscript blob
`6f4af839cc7c13b0cb2b3704fcefdeb1d88e9195`.

This module composes two already isolated finite steps in the manuscript's
no-recovery deferred-query converse. If the physical Hermitian source family
spans the whole source matrix space, exact later-query statistics imply the
Heisenberg operator identities `Cstar (F j) = P j`; those identities in turn
make the auxiliary encoded states perfectly distinguishable and force the
ordinary quantum memory dimension bound.

No recovery map is assumed. What remains external is the source-specific proof
that the actual coherent-copy family spans (equivalently, coherent-power
polarization/separation), together with the concrete symmetry-reduction/channel
identifications and construction of the manuscript's auxiliary projectors and
states.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Exact deferred-query statistics on a spanning Hermitian source family force
the number of perfectly separated query labels to fit inside the memory
Hilbert-space dimension. -/
theorem deferredStatsOnSpanningFamily_card_le_memory
    {J h q : Type*} [Fintype J] [Fintype h]
    [Fintype q] [DecidableEq q]
    (s : Set (hermitianMatrixSpace h))
    (hspan : Submodule.span ℝ s = ⊤)
    (omega P : J → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (Cstar : Matrix q q ℂ →ₗ[ℂ] Matrix h h ℂ)
    (F : J → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hCstarF : ∀ j, IsSelfAdjoint (Cstar (F j)))
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hadjoint : ∀ (A : Matrix q q ℂ) (X : Matrix h h ℂ),
      Matrix.trace (A * C X) = Matrix.trace (Cstar A * X))
    (hstats : ∀ j X, X ∈ s →
      Complex.re (Matrix.trace (F j * C (X : Matrix h h ℂ))) =
        Complex.re (Matrix.trace (P j * (X : Matrix h h ℂ))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  apply deferredAdjointOperatorIdentity_card_le_memory
    omega P C Cstar F hFpos hPOVM hadjoint
  · intro j
    exact traceAdjoint_effect_eq_of_stats_eq_on_spanning_family
      s hspan C Cstar (F j) (P j) (hCstarF j) (hP j) hadjoint
        (fun X hX => hstats j X hX)
  · exact hdiag
  · exact hencoded

/-- QI-A multiplicity specialization. Once the physical source family spans,
exact deferred statistics for one basis-projector label per multiplicity basis
vector force `K_G = sum g` to be no larger than the memory Hilbert dimension. -/
theorem multiplicityMemoryDimension_le_of_deferredStatsOnSpanningFamily
    {α h q : Type*} [Fintype α] [Fintype h]
    [Fintype q] [DecidableEq q]
    (g : α → Nat)
    (s : Set (hermitianMatrixSpace h))
    (hspan : Submodule.span ℝ s = ⊤)
    (omega P : multiplicityMemoryCarrier g → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (Cstar : Matrix q q ℂ →ₗ[ℂ] Matrix h h ℂ)
    (F : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hCstarF : ∀ j, IsSelfAdjoint (Cstar (F j)))
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hadjoint : ∀ (A : Matrix q q ℂ) (X : Matrix h h ℂ),
      Matrix.trace (A * C X) = Matrix.trace (Cstar A * X))
    (hstats : ∀ j X, X ∈ s →
      Complex.re (Matrix.trace (F j * C (X : Matrix h h ℂ))) =
        Complex.re (Matrix.trace (P j * (X : Matrix h h ℂ))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  have hbound := deferredStatsOnSpanningFamily_card_le_memory
    s hspan omega P C Cstar F hFpos hPOVM hCstarF hP
      hadjoint hstats hdiag hencoded
  rw [multiplicityMemoryCarrier_card g] at hbound
  exact hbound

end

end FormalResearch.QIA
