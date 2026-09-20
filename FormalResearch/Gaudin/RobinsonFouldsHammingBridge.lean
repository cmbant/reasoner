import Mathlib
import FormalResearch.Gaudin.WeightedTreeMetricSeparation
import FormalResearch.Gaudin.TreeSpaceRank

namespace FormalResearch.Gaudin

open scoped symmDiff

/-- Boolean indicator function of a finite split system. -/
def finsetBoolIndicator {α : Type*} [DecidableEq α]
    (s : Finset α) : α → Bool :=
  fun i => decide (i ∈ s)

/-- Pointwise Boolean mismatch is exactly membership in the symmetric
difference of the two split systems. -/
theorem bitMismatch_finsetBoolIndicator {α : Type*} [DecidableEq α]
    (s t : Finset α) (i : α) :
    bitMismatch (finsetBoolIndicator s i) (finsetBoolIndicator t i) =
      if i ∈ s ∆ t then 1 else 0 := by
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [finsetBoolIndicator, bitMismatch, hs, ht, Finset.mem_symmDiff]

/-- Hamming distance between split-indicator functions is the cardinality of
the symmetric difference. -/
theorem hamming_finsetBoolIndicator_eq_symmDiff_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Finset α) :
    hamming (finsetBoolIndicator s) (finsetBoolIndicator t) = (s ∆ t).card := by
  classical
  unfold hamming
  simp_rw [bitMismatch_finsetBoolIndicator]
  simpa using
    (Finset.sum_boole (R := Nat) (fun i : α => i ∈ s ∆ t) Finset.univ)

/-- The symmetric-difference cardinality is exactly the usual
Robinson--Foulds split distance. -/
theorem symmDiff_card_eq_robinsonFouldsDistance
    {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s ∆ t).card = robinsonFouldsDistance s t := by
  unfold robinsonFouldsDistance
  rw [Finset.symmDiff_def,
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff]

/-- Exact bridge from the Boolean Hamming metric to the G-I tree metric. -/
theorem hamming_finsetBoolIndicator_eq_robinsonFouldsDistance
    {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Finset α) :
    hamming (finsetBoolIndicator s) (finsetBoolIndicator t) =
      robinsonFouldsDistance s t := by
  rw [hamming_finsetBoolIndicator_eq_symmDiff_card,
    symmDiff_card_eq_robinsonFouldsDistance]

/-- For two binary `m`-leaf SU(2) coupling trees, twice the transition-rank
parameter is literally the Hamming distance between their split indicators. -/
theorem su2TreeRank_twice_eq_splitIndicatorHamming
    {α : Type*} [Fintype α] [DecidableEq α]
    {m : Nat} {s t : Finset α}
    (hs : s.card = m - 3) (ht : t.card = m - 3) :
    2 * su2TreeRank m s t =
      hamming (finsetBoolIndicator s) (finsetBoolIndicator t) := by
  rw [hamming_finsetBoolIndicator_eq_robinsonFouldsDistance]
  exact su2TreeRank_twice_eq_RF hs ht

end FormalResearch.Gaudin
