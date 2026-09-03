import Mathlib
import FormalResearch.Gaudin.BernoulliPathMatrix

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- The `(j+n,j)` matrix-product equation for a candidate inverse column of
the universal Bernoulli--Chebyshev path matrix, written with zero-based
subdiagonal index `p`. -/
def bernoulliInverseConvolution (j n : Nat) (t : Nat → ℚ) : ℚ :=
  ∑ p ∈ Finset.range (n + 1),
    (Nat.choose (j + n) (2 * (n - p) + 1) : ℚ) * t p

/-- For a positive one-indexed column `j`, every off-diagonal inverse equation
forces the next coefficient from the preceding ones.  This is the raw
triangular recurrence before the manuscript's `s=n-p` reindexing and binomial
ratio simplification. -/
theorem bernoulli_inverse_raw_recurrence {j n : Nat} (t : Nat → ℚ)
    (hj : 1 ≤ j) (hn : 1 ≤ n)
    (hconv : bernoulliInverseConvolution j n t = 0) :
    t n =
      -(∑ p ∈ Finset.range n,
          (Nat.choose (j + n) (2 * (n - p) + 1) : ℚ) * t p) /
        ((j + n : Nat) : ℚ) := by
  unfold bernoulliInverseConvolution at hconv
  rw [Finset.sum_range_succ] at hconv
  simp [Nat.choose_one_right] at hconv
  have hpos : 0 < j + n := by omega
  have hden : ((j + n : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  rw [eq_div_iff hden]
  linarith

/-- The diagonal inverse equation fixes the initial coefficient `t₀=1/j`.
This records the other half of the manuscript's inverse recurrence. -/
theorem bernoulli_inverse_initial {j : Nat} (t : Nat → ℚ) (hj : 1 ≤ j)
    (hconv : bernoulliInverseConvolution j 0 t = 1) :
    t 0 = 1 / (j : ℚ) := by
  unfold bernoulliInverseConvolution at hconv
  simp [Nat.choose_one_right] at hconv
  have hden : (j : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hj
  rw [eq_div_iff hden]
  linarith

/-- Rational form of the elementary binomial ratio used to pass from the raw
triangular recurrence to the manuscript normalization. -/
theorem choose_succ_div_top {N k : Nat} (hN : 1 ≤ N) :
    (Nat.choose N (k + 1) : ℚ) / (N : ℚ) =
      (Nat.choose (N - 1) k : ℚ) / ((k + 1 : Nat) : ℚ) := by
  have hNq : (N : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have hkq : ((k + 1 : Nat) : ℚ) ≠ 0 := by positivity
  rw [div_eq_div_iff hNq hkq]
  have hnat :
      Nat.choose N (k + 1) * (k + 1) = Nat.choose (N - 1) k * N := by
    have h := (Nat.add_one_mul_choose_eq (N - 1) k).symm
    simpa [Nat.sub_add_cancel hN, Nat.mul_comm] using h
  exact_mod_cast hnat

/-- The same inverse-column recurrence with each coefficient normalized exactly
as in the Bernoulli--Chebyshev handoff.  The only remaining cosmetic step to
match the printed recurrence is the reindexing `s=n-p`. -/
theorem bernoulli_inverse_normalized_recurrence {j n : Nat} (t : Nat → ℚ)
    (hj : 1 ≤ j) (hn : 1 ≤ n)
    (hconv : bernoulliInverseConvolution j n t = 0) :
    t n =
      -∑ p ∈ Finset.range n,
        ((Nat.choose (j + n - 1) (2 * (n - p)) : ℚ) /
          ((2 * (n - p) + 1 : Nat) : ℚ)) * t p := by
  rw [bernoulli_inverse_raw_recurrence t hj hn hconv]
  rw [neg_div, Finset.sum_div]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro p hp
  have hN : 1 ≤ j + n := by omega
  have hratio := choose_succ_div_top (N := j + n) (k := 2 * (n - p)) hN
  calc
    ((Nat.choose (j + n) (2 * (n - p) + 1) : ℚ) * t p) /
        ((j + n : Nat) : ℚ) =
      ((Nat.choose (j + n) (2 * (n - p) + 1) : ℚ) /
        ((j + n : Nat) : ℚ)) * t p := by ring
    _ = ((Nat.choose (j + n - 1) (2 * (n - p)) : ℚ) /
        ((2 * (n - p) + 1 : Nat) : ℚ)) * t p := by
      rw [hratio]

/-- The first universal inverse subdiagonal derived from the exact convolution
relations.  This matches the handoff formula `t₁(j)=-(j-1)/6`. -/
theorem bernoulli_inverse_first_subdiag {j : Nat} (t : Nat → ℚ) (hj : 1 ≤ j)
    (h0 : bernoulliInverseConvolution j 0 t = 1)
    (h1 : bernoulliInverseConvolution j 1 t = 0) :
    t 1 = -((j : ℚ) - 1) / 6 := by
  have ht0 := bernoulli_inverse_initial t hj h0
  have ht1 := bernoulli_inverse_normalized_recurrence
    (j := j) (n := 1) t hj (by omega) h1
  norm_num at ht1
  rw [ht0, Nat.cast_choose_two] at ht1
  have hpred : ((j - 1 : Nat) : ℚ) = (j : ℚ) - 1 := by
    rw [Nat.cast_sub hj]
    norm_num
  rw [hpred] at ht1
  have hjq : (j : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hj
  rw [ht1]
  field_simp [hjq]
  ring

end FormalResearch.Gaudin
