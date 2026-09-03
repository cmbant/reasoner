import Mathlib
import FormalResearch.QIA.ThreeCopyAlgebraBinomialBridge

namespace FormalResearch.QIA

/-- Before four parties, the three-copy conjugation-odd Hermitian sector
vanishes exactly.  This is derived from the closed all-party formula rather
than from a block table. -/
theorem threeCopyOddHermitianDimensionQ_eq_zero_before_four
    {m : Nat} (hm : 1 ≤ m) (h4 : m < 4) :
    threeCopyOddHermitianDimensionQ m = 0 := by
  rw [threeCopyOddHermitianDimensionQ_closed hm]
  interval_cases m <;> norm_num

/-- At four parties the odd Hermitian sector has dimension three. -/
theorem threeCopyOddHermitianDimensionQ_four :
    threeCopyOddHermitianDimensionQ 4 = 3 := by
  rw [threeCopyOddHermitianDimensionQ_closed (m := 4) (by norm_num)]
  norm_num

/-- Prior to the four-party onset, the invariant observable algebra has no
quantum excess over the minimal multiplicity memory. -/
theorem threeCopyAlgebra_eq_memory_before_four
    {m : Nat} (hm : 1 ≤ m) (h4 : m < 4) :
    threeCopyAlgebraDimensionQ m = threeCopyMemoryDimensionQ m := by
  have hodd := threeCopyOddHermitianDimensionQ_eq_zero_before_four hm h4
  unfold threeCopyOddHermitianDimensionQ at hodd
  linarith

/-- Four parties are the first positive-party case with a strict algebraic
quantum excess at three copies: the dimensions are `20`, `14`, and `3`. -/
theorem threeCopy_four_party_quantum_excess :
    threeCopyAlgebraDimensionQ 4 = 20 ∧
      threeCopyMemoryDimensionQ 4 = 14 ∧
      threeCopyOddHermitianDimensionQ 4 = 3 := by
  constructor
  · rw [threeCopyAlgebraDimensionQ_closed]
    norm_num
  constructor
  · rw [threeCopyMemoryDimensionQ_closed (m := 4) (by norm_num)]
    norm_num
  · exact threeCopyOddHermitianDimensionQ_four

/-- Compact finite-copy chirality-onset certificate. -/
theorem threeCopy_chirality_onset_at_four :
    (∀ m : Nat, 1 ≤ m → m < 4 → threeCopyOddHermitianDimensionQ m = 0) ∧
      threeCopyOddHermitianDimensionQ 4 = 3 := by
  exact ⟨fun m hm h4 => threeCopyOddHermitianDimensionQ_eq_zero_before_four hm h4,
    threeCopyOddHermitianDimensionQ_four⟩

end FormalResearch.QIA
