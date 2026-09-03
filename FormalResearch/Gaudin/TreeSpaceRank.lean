import Mathlib

namespace FormalResearch.Gaudin

/-- Number of splits present in the first tree but not common to both trees. -/
def splitDefect {α : Type*} [DecidableEq α] (s t : Finset α) : Nat :=
  s.card - (s ∩ t).card

/-- Robinson--Foulds distance written as the two directed split differences. -/
def robinsonFouldsDistance {α : Type*} [DecidableEq α]
    (s t : Finset α) : Nat :=
  (s \ t).card + (t \ s).card

/-- The split defect is exactly the number of splits lost from the first tree. -/
theorem splitDefect_eq_sdiff {α : Type*} [DecidableEq α]
    (s t : Finset α) : splitDefect s t = (s \ t).card := by
  unfold splitDefect
  have h := Finset.card_sdiff_add_card_inter s t
  omega

/-- Equal-size split systems lose the same number of splits in either
direction. -/
theorem sdiff_card_eq_of_card_eq {α : Type*} [DecidableEq α]
    {s t : Finset α} (hcard : s.card = t.card) :
    (s \ t).card = (t \ s).card := by
  have hs := Finset.card_sdiff_add_card_inter s t
  have ht := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm] at ht
  omega

/-- Core G-I combinatorial triangle: for two coupling-tree split systems with
the same number of internal splits, the Robinson--Foulds distance is twice the
common-split defect. -/
theorem robinsonFoulds_eq_two_splitDefect {α : Type*} [DecidableEq α]
    {s t : Finset α} (hcard : s.card = t.card) :
    robinsonFouldsDistance s t = 2 * splitDefect s t := by
  unfold robinsonFouldsDistance
  rw [splitDefect_eq_sdiff]
  have hsd := sdiff_card_eq_of_card_eq hcard
  omega

/-- Rank parameter used in the SU(2) recoupling manuscript:
`r = (m-3) - |Σ(T)∩Σ(T')|`. -/
def su2TreeRank {α : Type*} [DecidableEq α]
    (m : Nat) (s t : Finset α) : Nat :=
  (m - 3) - (s ∩ t).card

/-- When both binary coupling trees have the expected `m-3` internal splits,
`su2TreeRank` is exactly the directed split defect. -/
theorem su2TreeRank_eq_splitDefect {α : Type*} [DecidableEq α]
    {m : Nat} {s t : Finset α}
    (hs : s.card = m - 3) :
    su2TreeRank m s t = splitDefect s t := by
  simp [su2TreeRank, splitDefect, hs]

/-- Manuscript identity `d_RF = 2r`: for two `m`-leaf binary coupling trees,
the same integer `r` is half the Robinson--Foulds distance. -/
theorem su2TreeRank_twice_eq_RF {α : Type*} [DecidableEq α]
    {m : Nat} {s t : Finset α}
    (hs : s.card = m - 3) (ht : t.card = m - 3) :
    2 * su2TreeRank m s t = robinsonFouldsDistance s t := by
  rw [su2TreeRank_eq_splitDefect hs, robinsonFoulds_eq_two_splitDefect]
  · omega
  · omega

/-- Equivalent common-split formula from G-I. -/
theorem su2TreeRank_eq_common_split_formula {α : Type*} [DecidableEq α]
    (m : Nat) (s t : Finset α) :
    su2TreeRank m s t = (m - 3) - (s ∩ t).card := rfl

end FormalResearch.Gaudin
