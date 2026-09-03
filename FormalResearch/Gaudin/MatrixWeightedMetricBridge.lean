import Mathlib
import FormalResearch.Gaudin.MatrixTreeHammingTriangle
import FormalResearch.Gaudin.SU2WeightedMetricSpecialization

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- Matrix-level G-I to G-II bridge.  Under the G-I component-rank hypothesis,
twice the reduced cross-fiber matrix rank is exactly the rank-one `(1,0)`
specialization of the all-type weighted Gaudin tree metric. -/
theorem crossFiberMatrix_rank_twice_eq_weightedTreeDistance_one_zero
    {K V A B α ι κ β : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [Fintype α] [DecidableEq α] [Fintype β]
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (bFiber : Basis ι K (LinearMap.ker I)) (bB : Basis κ K B)
    (componentLegs : β → Nat) (m k : Nat) (s t : Finset α)
    (hs : s.card = m - 3) (ht : t.card = m - 3)
    (hcommon : (s ∩ t).card = k)
    (hcard : Fintype.card β = k + 1)
    (hlegs : (∑ C : β, componentLegs C) = m + 2 * k)
    (htri : ∀ C : β, 3 ≤ componentLegs C)
    (hMatrixComponents :
      (crossFiberMatrix I J bFiber bB).rank =
        ∑ C : β, (componentLegs C - 3)) :
    2 * (crossFiberMatrix I J bFiber bB).rank =
      weightedTreeDistance 1 0
        (finsetBoolIndicator s) (finsetBoolIndicator t)
        emptyVertexIndicator emptyVertexIndicator := by
  have hTriangle := crossFiberMatrix_tree_hamming_triangle
    I J bFiber bB componentLegs m k s t
    hs ht hcommon hcard hlegs htri hMatrixComponents
  rw [← su2TreeRank_twice_eq_splitIndicatorHamming hs ht] at hTriangle
  rw [hTriangle.1]
  exact su2TreeRank_twice_eq_weightedTreeDistance_one_zero hs ht

/-- Equivalent compact triangle exposing the common rank parameter and the
all-type weighted metric specialization simultaneously. -/
theorem crossFiberMatrix_tree_weighted_metric_triangle
    {K V A B α ι κ β : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [Fintype α] [DecidableEq α] [Fintype β]
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (bFiber : Basis ι K (LinearMap.ker I)) (bB : Basis κ K B)
    (componentLegs : β → Nat) (m k : Nat) (s t : Finset α)
    (hs : s.card = m - 3) (ht : t.card = m - 3)
    (hcommon : (s ∩ t).card = k)
    (hcard : Fintype.card β = k + 1)
    (hlegs : (∑ C : β, componentLegs C) = m + 2 * k)
    (htri : ∀ C : β, 3 ≤ componentLegs C)
    (hMatrixComponents :
      (crossFiberMatrix I J bFiber bB).rank =
        ∑ C : β, (componentLegs C - 3)) :
    (crossFiberMatrix I J bFiber bB).rank = su2TreeRank m s t ∧
      2 * (crossFiberMatrix I J bFiber bB).rank =
        weightedTreeDistance 1 0
          (finsetBoolIndicator s) (finsetBoolIndicator t)
          emptyVertexIndicator emptyVertexIndicator := by
  exact ⟨(crossFiberMatrix_tree_hamming_triangle
      I J bFiber bB componentLegs m k s t
      hs ht hcommon hcard hlegs htri hMatrixComponents).1,
    crossFiberMatrix_rank_twice_eq_weightedTreeDistance_one_zero
      I J bFiber bB componentLegs m k s t
      hs ht hcommon hcard hlegs htri hMatrixComponents⟩

end FormalResearch.Gaudin
