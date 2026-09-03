import Mathlib
import FormalResearch.Gaudin.MatrixTreeRankTriangle
import FormalResearch.Gaudin.RobinsonFouldsHammingBridge

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- Boolean-metric closure of the G-I matrix/tree triangle.  Under the same
geometric component-rank hypothesis, the reduced cross-fiber matrix rank is
the SU(2) tree rank and twice that rank is exactly the Hamming distance between
the two split-indicator functions. -/
theorem crossFiberMatrix_tree_hamming_triangle
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
        hamming (finsetBoolIndicator s) (finsetBoolIndicator t) := by
  have hRank := crossFiberMatrix_tree_rank_triangle
    I J bFiber bB componentLegs m k s t
    hs ht hcommon hcard hlegs htri hMatrixComponents
  refine ⟨hRank.1, ?_⟩
  rw [hamming_finsetBoolIndicator_eq_robinsonFouldsDistance]
  exact hRank.2

/-- Joint-differential version of the same Boolean metric closure. -/
theorem joint_rank_tree_hamming_triangle
    {K V A B α ι κ β : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [FiniteDimensional K V]
    [Fintype α] [DecidableEq α] [Fintype β]
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (bFiber : Basis ι K (LinearMap.ker I)) (bB : Basis κ K B)
    (componentLegs : β → Nat) (m k n : Nat) (s t : Finset α)
    (hs : s.card = m - 3) (ht : t.card = m - 3)
    (hcommon : (s ∩ t).card = k)
    (hcard : Fintype.card β = k + 1)
    (hlegs : (∑ C : β, componentLegs C) = m + 2 * k)
    (htri : ∀ C : β, 3 ≤ componentLegs C)
    (hI : Module.finrank K (LinearMap.range I) = n)
    (hMatrixComponents :
      (crossFiberMatrix I J bFiber bB).rank =
        ∑ C : β, (componentLegs C - 3)) :
    Module.finrank K (LinearMap.range (I.prod J)) =
        n + su2TreeRank m s t ∧
      2 * (crossFiberMatrix I J bFiber bB).rank =
        hamming (finsetBoolIndicator s) (finsetBoolIndicator t) := by
  have hRank := joint_rank_tree_rank_triangle
    I J bFiber bB componentLegs m k n s t
    hs ht hcommon hcard hlegs htri hI hMatrixComponents
  refine ⟨hRank.1, ?_⟩
  rw [hamming_finsetBoolIndicator_eq_robinsonFouldsDistance]
  exact hRank.2

end FormalResearch.Gaudin
