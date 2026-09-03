import Mathlib
import FormalResearch.QIA.ThreeCopyCharacterClosedForms

namespace FormalResearch.QIA

open scoped BigOperators

/-- Scalar binomial transform in the form needed for the three-copy `S₃`
character calculation. -/
theorem choose_power_sum_int (x : Int) (m : Nat) :
    (∑ k ∈ Finset.range (m + 1), (m.choose k : Int) * x^k) = (1 + x)^m := by
  have h := (add_pow x 1 m).symm
  simpa [mul_comm, mul_left_comm, mul_assoc, add_comm] using h

/-- The weighted sum over the number `k` of local standard factors is exactly
the classwise memory character numerator.  This is the binomial step behind
the closed all-party three-copy memory formula. -/
theorem threeCopyMemory_binomial_character_bridge (m : Nat) :
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : Int) * s3StandardInvariantNumerator k) =
      threeCopyMemoryCharacterNumerator m := by
  unfold s3StandardInvariantNumerator threeCopyMemoryCharacterNumerator
  calc
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : Int) *
        (∑ C : Fin 3, s3ClassSize C * (s3StandardChar C)^k)) =
      ∑ C : Fin 3, s3ClassSize C *
        (∑ k ∈ Finset.range (m + 1),
          (m.choose k : Int) * (s3StandardChar C)^k) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro C hC
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = ∑ C : Fin 3, s3ClassSize C * (1 + s3StandardChar C)^m := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [choose_power_sum_int]

/-- For positive party number the weighted character numerator is therefore
`3^m+3`. -/
theorem threeCopyMemory_weighted_numerator_closed {m : Nat} (hm : 1 ≤ m) :
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : Int) * s3StandardInvariantNumerator k) = 3^m + 3 := by
  rw [threeCopyMemory_binomial_character_bridge,
    threeCopyMemoryCharacterNumerator_closed hm]

/-- Rational generalized-Kronecker multiplicity obtained directly from the
`S₃` character average. -/
def s3StandardInvariantMultiplicityQ (k : Nat) : Rat :=
  (s3StandardInvariantNumerator k : Rat) / 6

/-- Rational three-copy memory dimension obtained by summing multiplicity
branches with the binomial local-label degeneracy. -/
def threeCopyMemoryDimensionQ (m : Nat) : Rat :=
  ∑ k ∈ Finset.range (m + 1),
    (m.choose k : Rat) * s3StandardInvariantMultiplicityQ k

/-- Exact all-party three-copy memory law in rational form:
`K_{m,3}=(3^m+3)/6` for positive `m`. -/
theorem threeCopyMemoryDimensionQ_closed {m : Nat} (hm : 1 ≤ m) :
    threeCopyMemoryDimensionQ m = ((3 : Rat)^m + 3) / 6 := by
  unfold threeCopyMemoryDimensionQ s3StandardInvariantMultiplicityQ
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast threeCopyMemory_weighted_numerator_closed hm

end FormalResearch.QIA
