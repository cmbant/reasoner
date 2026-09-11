import FormalResearch.QIA.DeferredQuerySpanningMemoryBound
import FormalResearch.QIA.MatrixTraceAdjoint

/-!
# QI-A deferred-query memory converse with the canonical trace adjoint

This module removes an algebraic witness from the finite no-recovery converse.
For finite matrix spaces the trace adjoint of the encoding exists canonically,
so there is no need to quantify over a separate map `Cstar` and a separate
trace-duality equation.

The remaining adjoint-side physical input is positivity of the pulled-back
query effects. That positivity immediately supplies the self-adjointness needed
by the spanning-statistics operator-identity theorem.

What remains source-specific is still the same: coherent-power spanning /
polarization for the actual physical source family, concrete symmetry reduction
and channel realization, and the manuscript's auxiliary projectors/states.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Exact deferred-query statistics on a spanning Hermitian source family imply
the memory dimension bound using the canonical finite trace adjoint of `C`.
There is no arbitrary adjoint witness in the statement. -/
theorem deferredStatsOnSpanningFamily_card_le_memory_canonicalAdjoint
    {J h q : Type*} [Fintype J] [Fintype h]
    [Fintype q] [DecidableEq q]
    (s : Set (hermitianMatrixSpace h))
    (hspan : Submodule.span ℝ s = ⊤)
    (omega P : J → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (F : J → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hPullbackPos : ∀ j, (matrixTraceAdjoint C (F j)).PosSemidef)
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hstats : ∀ j X, X ∈ s →
      Complex.re (Matrix.trace (F j * C (X : Matrix h h ℂ))) =
        Complex.re (Matrix.trace (P j * (X : Matrix h h ℂ))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  apply deferredStatsOnSpanningFamily_card_le_memory
    s hspan omega P C (matrixTraceAdjoint C) F hFpos hPOVM
  · intro j
    exact (hPullbackPos j).isHermitian
  · exact hP
  · intro A X
    exact matrixTraceAdjoint_spec C A X
  · exact hstats
  · exact hdiag
  · exact hencoded

/-- QI-A multiplicity specialization with the canonical trace adjoint. -/
theorem multiplicityMemoryDimension_le_of_deferredStatsOnSpanningFamily_canonicalAdjoint
    {α h q : Type*} [Fintype α] [Fintype h]
    [Fintype q] [DecidableEq q]
    (g : α → Nat)
    (s : Set (hermitianMatrixSpace h))
    (hspan : Submodule.span ℝ s = ⊤)
    (omega P : multiplicityMemoryCarrier g → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (F : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hPullbackPos : ∀ j, (matrixTraceAdjoint C (F j)).PosSemidef)
    (hP : ∀ j, IsSelfAdjoint (P j))
    (hstats : ∀ j X, X ∈ s →
      Complex.re (Matrix.trace (F j * C (X : Matrix h h ℂ))) =
        Complex.re (Matrix.trace (P j * (X : Matrix h h ℂ))))
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  have hbound := deferredStatsOnSpanningFamily_card_le_memory_canonicalAdjoint
    s hspan omega P C F hFpos hPOVM hPullbackPos hP hstats hdiag hencoded
  rw [multiplicityMemoryCarrier_card g] at hbound
  exact hbound

end

end FormalResearch.QIA
