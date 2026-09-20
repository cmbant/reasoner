import Mathlib
import FormalResearch.Gaudin.TreeSpaceRank
import FormalResearch.Gaudin.CommonSplitComponentCount

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- Arithmetic closure of the G-I arbitrary-tree rank theorem.  The geometric
input is isolated in `hRed`: after common-split reduction, the reduced
cross-Poisson rank is the sum of the irreducible component ranks `b_C-3`.
Everything from that point to the Robinson--Foulds formula is finite
bookkeeping. -/
theorem reduced_classical_rank_triangle
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (b : ι → Nat) (m k redRank : Nat) (s t : Finset α)
    (hs : s.card = m - 3) (ht : t.card = m - 3)
    (hcommon : (s ∩ t).card = k)
    (hcard : Fintype.card ι = k + 1)
    (hlegs : (∑ C : ι, b C) = m + 2 * k)
    (htri : ∀ C : ι, 3 ≤ b C)
    (hRed : redRank = ∑ C : ι, (b C - 3)) :
    redRank = su2TreeRank m s t ∧
      2 * redRank = robinsonFouldsDistance s t := by
  have hrank : redRank = su2TreeRank m s t := by
    rw [hRed]
    exact common_split_component_rank_sum_eq_su2TreeRank
      b m k s t hcard hlegs htri hcommon
  refine ⟨hrank, ?_⟩
  rw [hrank]
  exact su2TreeRank_twice_eq_RF hs ht

/-- Same conclusion with the common-split formula displayed explicitly. -/
theorem reduced_classical_rank_eq_common_split_defect
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (b : ι → Nat) (m k redRank : Nat) (s t : Finset α)
    (hcommon : (s ∩ t).card = k)
    (hcard : Fintype.card ι = k + 1)
    (hlegs : (∑ C : ι, b C) = m + 2 * k)
    (htri : ∀ C : ι, 3 ≤ b C)
    (hRed : redRank = ∑ C : ι, (b C - 3)) :
    redRank = m - 3 - k := by
  rw [hRed, common_split_component_rank_sum b m k hcard hlegs htri]

end FormalResearch.Gaudin
