import Mathlib
import FormalResearch.QIA.ThreeCopyChiralityOnset

namespace FormalResearch.QIA

/-- Elementary exponential separation used in the all-party chirality
persistence argument. -/
theorem six_mul_three_pow_lt_five_pow {m : Nat} (hm : 4 ≤ m) :
    6 * 3^m < 5^m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ, pow_succ]
      nlinarith

/-- Once the three-copy odd Hermitian sector appears at four parties, it stays
strictly positive for every larger party number. -/
theorem threeCopyOddHermitianDimensionQ_pos_of_four_le
    {m : Nat} (hm : 4 ≤ m) :
    0 < threeCopyOddHermitianDimensionQ m := by
  have hm1 : 1 ≤ m := by omega
  rw [threeCopyOddHermitianDimensionQ_closed hm1]
  have hmainNat := six_mul_three_pow_lt_five_pow hm
  have hmain :
      (6 : Rat) * (3 : Rat)^m < (5 : Rat)^m := by
    exact_mod_cast hmainNat
  have htwo : (0 : Rat) < (2 : Rat)^m := by positivity
  rcases neg_one_pow_eq_or Rat m with hpm | hpm
  · rw [hpm]
    norm_num
    nlinarith
  · rw [hpm]
    norm_num
    nlinarith

/-- The invariant algebra has a strict quantum excess over minimal memory for
all party numbers from the four-party onset onward. -/
theorem threeCopyAlgebra_gt_memory_of_four_le
    {m : Nat} (hm : 4 ≤ m) :
    threeCopyMemoryDimensionQ m < threeCopyAlgebraDimensionQ m := by
  have hodd := threeCopyOddHermitianDimensionQ_pos_of_four_le hm
  unfold threeCopyOddHermitianDimensionQ at hodd
  linarith

/-- Exact onset-and-persistence statement at three copies. -/
theorem threeCopy_chirality_onset_and_persistence :
    (∀ m : Nat, 1 ≤ m → m < 4 → threeCopyOddHermitianDimensionQ m = 0) ∧
      (∀ m : Nat, 4 ≤ m → 0 < threeCopyOddHermitianDimensionQ m) := by
  exact ⟨fun m hm h4 => threeCopyOddHermitianDimensionQ_eq_zero_before_four hm h4,
    fun m hm => threeCopyOddHermitianDimensionQ_pos_of_four_le hm⟩

end FormalResearch.QIA
