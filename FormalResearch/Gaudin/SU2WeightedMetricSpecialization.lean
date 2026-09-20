import Mathlib
import FormalResearch.Gaudin.RobinsonFouldsHammingBridge

namespace FormalResearch.Gaudin

/-- Canonical empty vertex-indicator system for the rank-one specialization. -/
def emptyVertexIndicator : Fin 0 → Bool :=
  fun i => Fin.elim0 i

/-- The all-type weighted tree distance at edge weight `1` and vertex weight
`0` reduces exactly to Robinson--Foulds distance on SU(2) split systems. -/
theorem weightedTreeDistance_one_zero_splitIndicators_eq_RF
    {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Finset α) :
    weightedTreeDistance 1 0
      (finsetBoolIndicator s) (finsetBoolIndicator t)
      emptyVertexIndicator emptyVertexIndicator =
      robinsonFouldsDistance s t := by
  simp [weightedTreeDistance,
    hamming_finsetBoolIndicator_eq_robinsonFouldsDistance]

/-- Rank-one specialization of the all-type Gaudin metric: for two binary
`m`-leaf SU(2) coupling trees, the weighted distance `(ell,nu)=(1,0)` is
exactly twice the transition-rank parameter. -/
theorem su2TreeRank_twice_eq_weightedTreeDistance_one_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    {m : Nat} {s t : Finset α}
    (hs : s.card = m - 3) (ht : t.card = m - 3) :
    2 * su2TreeRank m s t =
      weightedTreeDistance 1 0
        (finsetBoolIndicator s) (finsetBoolIndicator t)
        emptyVertexIndicator emptyVertexIndicator := by
  rw [weightedTreeDistance_one_zero_splitIndicators_eq_RF]
  exact su2TreeRank_twice_eq_RF hs ht

end FormalResearch.Gaudin
