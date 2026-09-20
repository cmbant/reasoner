import Mathlib
import FormalResearch.QIA.FourQubitD3BlockCensus

namespace FormalResearch.QIA

open scoped BigOperators

/-- Character-sum numerator for the largest three-copy multiplicity block of
`m` qubits, i.e. the block where every local factor is the standard `S₃`
representation. -/
def threeCopyLargestBlockNumerator (m : Nat) : Int :=
  s3StandardInvariantNumerator m

/-- After summing over all local choices (trivial or standard), the binomial
transform of the multiplicity character average collapses classwise to this
three-term numerator. -/
def threeCopyMemoryCharacterNumerator (m : Nat) : Int :=
  ∑ C : Fin 3, s3ClassSize C * (1 + s3StandardChar C) ^ m

/-- Squaring multiplicities produces a double `S₃` character average.  After
summing over all local trivial/standard choices, the binomial transform again
collapses classwise to this double character sum. -/
def threeCopyAlgebraCharacterNumerator (m : Nat) : Int :=
  ∑ C : Fin 3, ∑ D : Fin 3,
    s3ClassSize C * s3ClassSize D *
      (1 + s3StandardChar C * s3StandardChar D) ^ m

/-- Closed largest-block numerator for positive party number:
`6 g_m = 2^m + 2(-1)^m`. -/
theorem threeCopyLargestBlockNumerator_closed {m : Nat} (hm : 1 ≤ m) :
    threeCopyLargestBlockNumerator m = 2^m + 2 * (-1 : Int)^m := by
  unfold threeCopyLargestBlockNumerator s3StandardInvariantNumerator
  simp [s3ClassSize, s3StandardChar, Fin.sum_univ_succ, zero_pow (Nat.ne_of_gt hm)]

/-- Closed memory numerator for positive party number:
`6 K_{m,3} = 3^m + 3`. -/
theorem threeCopyMemoryCharacterNumerator_closed {m : Nat} (hm : 1 ≤ m) :
    threeCopyMemoryCharacterNumerator m = 3^m + 3 := by
  unfold threeCopyMemoryCharacterNumerator
  simp [s3ClassSize, s3StandardChar, Fin.sum_univ_succ,
    zero_pow (Nat.ne_of_gt hm)]

/-- Closed invariant-algebra numerator:
`36 dim A_{m,3} = 5^m + 4·2^m + 4(-1)^m + 27`. -/
theorem threeCopyAlgebraCharacterNumerator_closed (m : Nat) :
    threeCopyAlgebraCharacterNumerator m =
      5^m + 4 * 2^m + 4 * (-1 : Int)^m + 27 := by
  unfold threeCopyAlgebraCharacterNumerator
  simp [s3ClassSize, s3StandardChar, Fin.sum_univ_succ]
  ring

/-- Numerator for the total real conjugation-odd Hermitian dimension, obtained
from `Σ choose(g,2) = (Σ g² - Σ g)/2`.  For positive `m`, multiplying by 72
removes all denominators. -/
def threeCopyOddHermitianNumerator (m : Nat) : Int :=
  threeCopyAlgebraCharacterNumerator m -
    6 * threeCopyMemoryCharacterNumerator m

/-- Closed odd-sector numerator:
`72 N_odd = 5^m - 6·3^m + 4·2^m + 4(-1)^m + 9`. -/
theorem threeCopyOddHermitianNumerator_closed {m : Nat} (hm : 1 ≤ m) :
    threeCopyOddHermitianNumerator m =
      5^m - 6 * 3^m + 4 * 2^m + 4 * (-1 : Int)^m + 9 := by
  unfold threeCopyOddHermitianNumerator
  rw [threeCopyAlgebraCharacterNumerator_closed,
    threeCopyMemoryCharacterNumerator_closed hm]
  ring

/-- Four-qubit specialization of the three closed character numerators. -/
theorem fourQubitD3_closed_form_numerators :
    threeCopyLargestBlockNumerator 4 = 18 ∧
    threeCopyMemoryCharacterNumerator 4 = 84 ∧
    threeCopyAlgebraCharacterNumerator 4 = 720 ∧
    threeCopyOddHermitianNumerator 4 = 216 := by
  norm_num [threeCopyLargestBlockNumerator_closed (m := 4),
    threeCopyMemoryCharacterNumerator_closed (m := 4),
    threeCopyAlgebraCharacterNumerator_closed,
    threeCopyOddHermitianNumerator_closed (m := 4)]

end FormalResearch.QIA
