import Mathlib
import FormalResearch.Gaudin.CrossPoissonMatrixRank
import FormalResearch.Gaudin.TreeClassicalRankTriangle

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- Matrix-level form of the G-I arbitrary-tree theorem.  Once the reduced
cross-fiber matrix is known to split into regular components of ranks `b_C-3`,
its ordinary matrix rank is exactly the tree-space rank and half the
Robinson--Foulds distance. -/
theorem crossFiberMatrix_tree_rank_triangle
    {K V A B α ι κ β : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [DecidableEq α] [Fintype β]
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
        robinsonFouldsDistance s t := by
  exact reduced_classical_rank_triangle componentLegs m k
    (crossFiberMatrix I J bFiber bB).rank s t
    hs ht hcommon hcard hlegs htri hMatrixComponents

/-- Joint-differential form.  In addition to the matrix/tree triangle, if the
first complete system has rank `n`, then the joint differential has rank
`n + r`, with the same tree rank `r`. -/
theorem joint_rank_tree_rank_triangle
    {K V A B α ι κ β : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [FiniteDimensional K V]
    [DecidableEq α] [Fintype β]
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
        robinsonFouldsDistance s t := by
  have hTriangle := crossFiberMatrix_tree_rank_triangle
    I J bFiber bB componentLegs m k s t
    hs ht hcommon hcard hlegs htri hMatrixComponents
  have hJoint := joint_rank_eq_n_add_crossFiberMatrix_rank
    I J bFiber bB n (crossFiberMatrix I J bFiber bB).rank hI rfl
  rw [hTriangle.1] at hJoint
  exact ⟨hJoint, hTriangle.2⟩

end FormalResearch.Gaudin
