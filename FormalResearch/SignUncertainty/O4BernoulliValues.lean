module

public import Mathlib.NumberTheory.Bernoulli

/-!
# The Bernoulli numbers `B_4, B_6` as exact rationals

Each `bernoulli' k` (`k ≤ 6`) is computed from `bernoulli'_def` and the previously computed values (so that no step unfolds the recursion).
The even `bernoulli (2 n) = bernoulli' (2 n)`.

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

lemma o4_bern'_0 : bernoulli' 0 = (1 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp

lemma o4_bern'_1 : bernoulli' 1 = (1 : ℚ) / 2 := by
  rw [bernoulli'_def]
  simp [Nat.choose]; norm_num

lemma o4_bern'_2 : bernoulli' 2 = (1 : ℚ) / 6 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose]; norm_num

lemma o4_bern'_3 : bernoulli' 3 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose]; norm_num

lemma o4_bern'_4 : bernoulli' 4 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose]; norm_num

lemma o4_bern'_5 : bernoulli' 5 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose]; norm_num

lemma o4_bern'_6 : bernoulli' 6 = (1 : ℚ) / 42 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_5]; norm_num

lemma o4_bernoulli_4 : bernoulli 4 = (-1 : ℚ) / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_4

lemma o4_bernoulli_6 : bernoulli 6 = (1 : ℚ) / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_6

end FormalResearch.SignUncertainty
