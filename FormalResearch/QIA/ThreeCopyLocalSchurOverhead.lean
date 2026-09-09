import Mathlib
import FormalResearch.QIA.ThreeCopyCharacterClosedForms

namespace FormalResearch.QIA

open scoped BigOperators

/-!
# Three-copy local-Schur overhead

This module matches the exact character calculation in
`cmbant/QIprojects` at source commit
`a32a35809edd12b7d7cb7c23b332edad36efa5bc`, specifically
`QI-A/scripts/verify_local_schur_d3_overhead.py` and the consolidated QI-A
manuscript.

At three copies, a qubit retains the trivial and standard `S₃` sectors, while
a local dimension at least three retains the trivial, sign, and standard
sectors. Their classwise character sums are respectively `(3,1,0)` and
`(4,0,1)` on identity, transpositions, and three-cycles.
-/

/-- Sum of the allowed `S₃` characters at a qubit site for three copies. -/
def s3QubitAllowedCharSum : Fin 3 → Int := ![3, 1, 0]

/-- Sum of the allowed `S₃` characters at a site of local dimension at least
three for three copies. -/
def s3FullAllowedCharSum : Fin 3 → Int := ![4, 0, 1]

/-- Character-sum numerator `6 K` for `m` parties, of which `r` have local
dimension at least three and the remaining `m-r` are qubits. -/
def threeCopyLocalSchurMemoryNumerator (m r : Nat) : Int :=
  ∑ C : Fin 3,
    s3ClassSize C * (s3FullAllowedCharSum C) ^ r *
      (s3QubitAllowedCharSum C) ^ (m - r)

/-- Dimension retained by applying the local Schur transform independently at
three copies and discarding the carrier factors. -/
def threeCopyLocalSchurRetainedDimension (m r : Nat) : Int :=
  (4 : Int) ^ r * 3 ^ (m - r)

/-- In a genuinely mixed architecture, both non-identity `S₃` classes are
killed by one of the two site types, so the character numerator equals the
local-Schur retained dimension exactly. Equivalently, `L = 6 K`. -/
theorem threeCopyLocalSchur_mixed_numerator_eq_retained
    {m r : Nat} (hr0 : 1 ≤ r) (hrm : r < m) :
    threeCopyLocalSchurMemoryNumerator m r =
      threeCopyLocalSchurRetainedDimension m r := by
  have hmr : 1 ≤ m - r := Nat.sub_pos_iff_lt.mpr hrm
  unfold threeCopyLocalSchurMemoryNumerator
    threeCopyLocalSchurRetainedDimension
  simp [s3ClassSize, s3FullAllowedCharSum, s3QubitAllowedCharSum,
    Fin.sum_univ_succ, zero_pow (Nat.ne_of_gt hr0),
    zero_pow (Nat.ne_of_gt hmr)]

/-- At the all-qubit endpoint the transposition class contributes the residual
`+3`, giving `6 K = L + 3`. -/
theorem threeCopyLocalSchur_allQubit_numerator_eq_retained_add_three
    {m : Nat} (hm : 1 ≤ m) :
    threeCopyLocalSchurMemoryNumerator m 0 =
      threeCopyLocalSchurRetainedDimension m 0 + 3 := by
  unfold threeCopyLocalSchurMemoryNumerator
    threeCopyLocalSchurRetainedDimension
  simp [s3ClassSize, s3FullAllowedCharSum, s3QubitAllowedCharSum,
    Fin.sum_univ_succ, zero_pow (Nat.ne_of_gt hm)]

/-- At the all-high-dimensional endpoint the three-cycle class contributes the
residual `+2`, giving `6 K = L + 2`. -/
theorem threeCopyLocalSchur_allFull_numerator_eq_retained_add_two
    {m : Nat} (hm : 1 ≤ m) :
    threeCopyLocalSchurMemoryNumerator m m =
      threeCopyLocalSchurRetainedDimension m m + 2 := by
  unfold threeCopyLocalSchurMemoryNumerator
    threeCopyLocalSchurRetainedDimension
  simp [s3ClassSize, s3FullAllowedCharSum, s3QubitAllowedCharSum,
    Fin.sum_univ_succ, zero_pow (Nat.ne_of_gt hm)]

/-- Rational invariant-memory dimension obtained from the `S₃` character
numerator. -/
def threeCopyLocalSchurMemoryQ (m r : Nat) : Rat :=
  (threeCopyLocalSchurMemoryNumerator m r : Rat) / 6

/-- Rational form of the locally retained dimension. -/
def threeCopyLocalSchurRetainedDimensionQ (m r : Nat) : Rat :=
  (threeCopyLocalSchurRetainedDimension m r : Rat)

/-- Exact mixed-architecture relation `L = 6 K`. -/
theorem threeCopyLocalSchur_mixed_six_memory_eq_retained
    {m r : Nat} (hr0 : 1 ≤ r) (hrm : r < m) :
    6 * threeCopyLocalSchurMemoryQ m r =
      threeCopyLocalSchurRetainedDimensionQ m r := by
  unfold threeCopyLocalSchurMemoryQ threeCopyLocalSchurRetainedDimensionQ
  rw [threeCopyLocalSchur_mixed_numerator_eq_retained hr0 hrm]
  ring

/-- Exact all-qubit endpoint relation `6 K = L + 3`. -/
theorem threeCopyLocalSchur_allQubit_six_memory_eq_retained_add_three
    {m : Nat} (hm : 1 ≤ m) :
    6 * threeCopyLocalSchurMemoryQ m 0 =
      threeCopyLocalSchurRetainedDimensionQ m 0 + 3 := by
  unfold threeCopyLocalSchurMemoryQ threeCopyLocalSchurRetainedDimensionQ
  rw [threeCopyLocalSchur_allQubit_numerator_eq_retained_add_three hm]
  push_cast
  ring

/-- Exact all-high-dimensional endpoint relation `6 K = L + 2`. -/
theorem threeCopyLocalSchur_allFull_six_memory_eq_retained_add_two
    {m : Nat} (hm : 1 ≤ m) :
    6 * threeCopyLocalSchurMemoryQ m m =
      threeCopyLocalSchurRetainedDimensionQ m m + 2 := by
  unfold threeCopyLocalSchurMemoryQ threeCopyLocalSchurRetainedDimensionQ
  rw [threeCopyLocalSchur_allFull_numerator_eq_retained_add_two hm]
  push_cast
  ring

end FormalResearch.QIA
