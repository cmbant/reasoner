import Mathlib
import FormalResearch.Gaudin.TreeSpaceRank

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- Bookkeeping for cutting `k` common internal edges of an `m`-leg binary
coupling tree.  If the resulting `k+1` components have incident-leg counts
`b_C`, every cut edge is counted on both adjacent components, so
`Σ b_C = m + 2k`; consequently the sum of polygon dimensions `b_C-3` is
`m-3-k`. -/
theorem common_split_component_rank_sum
    {ι : Type*} [Fintype ι]
    (b : ι → Nat) (m k : Nat)
    (hcard : Fintype.card ι = k + 1)
    (hlegs : (∑ C : ι, b C) = m + 2 * k)
    (htri : ∀ C : ι, 3 ≤ b C) :
    (∑ C : ι, (b C - 3)) = m - 3 - k := by
  have hdecomp :
      (∑ C : ι, b C) = (∑ C : ι, (b C - 3)) + 3 * Fintype.card ι := by
    calc
      (∑ C : ι, b C) = ∑ C : ι, ((b C - 3) + 3) := by
        apply Finset.sum_congr rfl
        intro C hC
        have hCtri := htri C
        omega
      _ = (∑ C : ι, (b C - 3)) + ∑ _C : ι, 3 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ C : ι, (b C - 3)) + 3 * Fintype.card ι := by
        simp [Nat.mul_comm]
  rw [hlegs, hcard] at hdecomp
  omega

/-- Equivalent form with the G-I rank parameter on the right. -/
theorem common_split_component_rank_sum_eq_su2TreeRank
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (b : ι → Nat) (m k : Nat) (s t : Finset α)
    (hcard : Fintype.card ι = k + 1)
    (hlegs : (∑ C : ι, b C) = m + 2 * k)
    (htri : ∀ C : ι, 3 ≤ b C)
    (hcommon : (s ∩ t).card = k) :
    (∑ C : ι, (b C - 3)) = su2TreeRank m s t := by
  rw [common_split_component_rank_sum b m k hcard hlegs htri]
  simp [su2TreeRank, hcommon]

end FormalResearch.Gaudin
