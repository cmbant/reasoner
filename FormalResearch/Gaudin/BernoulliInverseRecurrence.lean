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

end FormalResearch.Gaudin
