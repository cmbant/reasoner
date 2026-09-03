import Mathlib
import FormalResearch.QIA.ThreeCopyMemoryBinomialBridge

namespace FormalResearch.QIA

open scoped BigOperators

/-- Squaring the `S₃` invariant-character numerator is the double character
sum over conjugacy-class pairs. -/
theorem s3StandardInvariantNumerator_sq_expansion (k : Nat) :
    (s3StandardInvariantNumerator k)^2 =
      ∑ C : Fin 3, ∑ D : Fin 3,
        s3ClassSize C * s3ClassSize D *
          (s3StandardChar C * s3StandardChar D)^k := by
  unfold s3StandardInvariantNumerator
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  rw [mul_pow]
  ring

/-- Binomially summing squared multiplicity numerators over the number of local
standard factors gives exactly the double classwise algebra numerator. -/
theorem threeCopyAlgebra_binomial_character_bridge (m : Nat) :
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : Int) * (s3StandardInvariantNumerator k)^2) =
      threeCopyAlgebraCharacterNumerator m := by
  simp_rw [s3StandardInvariantNumerator_sq_expansion, Finset.mul_sum]
  unfold threeCopyAlgebraCharacterNumerator
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  calc
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : Int) *
        (s3ClassSize C * s3ClassSize D *
          (s3StandardChar C * s3StandardChar D)^k)) =
      s3ClassSize C * s3ClassSize D *
        (∑ k ∈ Finset.range (m + 1),
          (m.choose k : Int) *
            (s3StandardChar C * s3StandardChar D)^k) := by
              rw [Finset.mul_sum]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
    _ = s3ClassSize C * s3ClassSize D *
        (1 + s3StandardChar C * s3StandardChar D)^m := by
      rw [choose_power_sum_int]

/-- Closed weighted squared-multiplicity numerator for every party number. -/
theorem threeCopyAlgebra_weighted_numerator_closed (m : Nat) :
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : Int) * (s3StandardInvariantNumerator k)^2) =
      5^m + 4 * 2^m + 4 * (-1 : Int)^m + 27 := by
  rw [threeCopyAlgebra_binomial_character_bridge,
    threeCopyAlgebraCharacterNumerator_closed]

/-- Rational three-copy invariant-algebra dimension obtained directly from the
squared generalized-Kronecker multiplicities. -/
def threeCopyAlgebraDimensionQ (m : Nat) : Rat :=
  ∑ k ∈ Finset.range (m + 1),
    (m.choose k : Rat) * (s3StandardInvariantMultiplicityQ k)^2

/-- Exact all-party three-copy invariant-algebra dimension law in rational
form. -/
theorem threeCopyAlgebraDimensionQ_closed (m : Nat) :
    threeCopyAlgebraDimensionQ m =
      ((5 : Rat)^m + 4 * (2 : Rat)^m + 4 * (-1 : Rat)^m + 27) / 36 := by
  unfold threeCopyAlgebraDimensionQ s3StandardInvariantMultiplicityQ
  have h36 : (36 : Rat) ≠ 0 := by norm_num
  calc
    (∑ k ∈ Finset.range (m + 1),
      (m.choose k : Rat) *
        (((s3StandardInvariantNumerator k : Rat) / 6)^2)) =
      (∑ k ∈ Finset.range (m + 1),
        (m.choose k : Rat) *
          ((s3StandardInvariantNumerator k : Rat)^2)) / 36 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro k hk
            field_simp
            ring
    _ = ((5 : Rat)^m + 4 * (2 : Rat)^m + 4 * (-1 : Rat)^m + 27) / 36 := by
      congr 1
      exact_mod_cast threeCopyAlgebra_weighted_numerator_closed m

/-- Rational odd-Hermitian dimension obtained from `choose(g,2)` via
`(D-K)/2`. -/
def threeCopyOddHermitianDimensionQ (m : Nat) : Rat :=
  (threeCopyAlgebraDimensionQ m - threeCopyMemoryDimensionQ m) / 2

/-- Closed all-party odd-Hermitian dimension for positive `m`. -/
theorem threeCopyOddHermitianDimensionQ_closed {m : Nat} (hm : 1 ≤ m) :
    threeCopyOddHermitianDimensionQ m =
      ((5 : Rat)^m - 6 * (3 : Rat)^m + 4 * (2 : Rat)^m +
        4 * (-1 : Rat)^m + 9) / 72 := by
  unfold threeCopyOddHermitianDimensionQ
  rw [threeCopyAlgebraDimensionQ_closed, threeCopyMemoryDimensionQ_closed hm]
  ring

end FormalResearch.QIA
