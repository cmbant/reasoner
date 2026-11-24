module

public import Mathlib.NumberTheory.Bernoulli

/-!
# The Bernoulli numbers `B_4, B_6, …, B_26` as exact rationals

Each `bernoulli' k` is computed from `bernoulli'_def` and the previously computed values (so that no step unfolds the recursion).
The even `bernoulli (2 n) = bernoulli' (2 n)`.

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

lemma o4_bern'_0 : bernoulli' 0 = (1 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose] <;> norm_num

lemma o4_bern'_1 : bernoulli' 1 = (1 : ℚ) / 2 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0] <;> norm_num

lemma o4_bern'_2 : bernoulli' 2 = (1 : ℚ) / 6 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1] <;> norm_num

lemma o4_bern'_3 : bernoulli' 3 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2] <;> norm_num

lemma o4_bern'_4 : bernoulli' 4 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3] <;> norm_num

lemma o4_bern'_5 : bernoulli' 5 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4] <;> norm_num

lemma o4_bern'_6 : bernoulli' 6 = (1 : ℚ) / 42 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5] <;> norm_num

lemma o4_bern'_7 : bernoulli' 7 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6] <;> norm_num

lemma o4_bern'_8 : bernoulli' 8 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7] <;> norm_num

lemma o4_bern'_9 : bernoulli' 9 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8] <;> norm_num

lemma o4_bern'_10 : bernoulli' 10 = (5 : ℚ) / 66 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9] <;> norm_num

lemma o4_bern'_11 : bernoulli' 11 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10] <;> norm_num

lemma o4_bern'_12 : bernoulli' 12 = (-691 : ℚ) / 2730 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11] <;> norm_num

lemma o4_bern'_13 : bernoulli' 13 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12] <;> norm_num

lemma o4_bern'_14 : bernoulli' 14 = (7 : ℚ) / 6 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13] <;> norm_num

lemma o4_bern'_15 : bernoulli' 15 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14] <;> norm_num

lemma o4_bern'_16 : bernoulli' 16 = (-3617 : ℚ) / 510 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15] <;> norm_num

lemma o4_bern'_17 : bernoulli' 17 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16] <;> norm_num

lemma o4_bern'_18 : bernoulli' 18 = (43867 : ℚ) / 798 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17] <;> norm_num

lemma o4_bern'_19 : bernoulli' 19 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18] <;> norm_num

lemma o4_bern'_20 : bernoulli' 20 = (-174611 : ℚ) / 330 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18, o4_bern'_19] <;> norm_num

lemma o4_bern'_21 : bernoulli' 21 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18, o4_bern'_19, o4_bern'_20] <;> norm_num

lemma o4_bern'_22 : bernoulli' 22 = (854513 : ℚ) / 138 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18, o4_bern'_19, o4_bern'_20, o4_bern'_21] <;> norm_num

lemma o4_bern'_23 : bernoulli' 23 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18, o4_bern'_19, o4_bern'_20, o4_bern'_21, o4_bern'_22] <;> norm_num

lemma o4_bern'_24 : bernoulli' 24 = (-236364091 : ℚ) / 2730 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18, o4_bern'_19, o4_bern'_20, o4_bern'_21, o4_bern'_22, o4_bern'_23] <;> norm_num

lemma o4_bern'_25 : bernoulli' 25 = (0 : ℚ) / 1 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18, o4_bern'_19, o4_bern'_20, o4_bern'_21, o4_bern'_22, o4_bern'_23, o4_bern'_24] <;> norm_num

lemma o4_bern'_26 : bernoulli' 26 = (8553103 : ℚ) / 6 := by
  rw [bernoulli'_def]
  simp [Finset.sum_range_succ, Nat.choose, o4_bern'_0, o4_bern'_1, o4_bern'_2, o4_bern'_3, o4_bern'_4, o4_bern'_5, o4_bern'_6, o4_bern'_7, o4_bern'_8, o4_bern'_9, o4_bern'_10, o4_bern'_11, o4_bern'_12, o4_bern'_13, o4_bern'_14, o4_bern'_15, o4_bern'_16, o4_bern'_17, o4_bern'_18, o4_bern'_19, o4_bern'_20, o4_bern'_21, o4_bern'_22, o4_bern'_23, o4_bern'_24, o4_bern'_25] <;> norm_num

lemma o4_bernoulli_4 : bernoulli 4 = (-1 : ℚ) / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_4

lemma o4_bernoulli_6 : bernoulli 6 = (1 : ℚ) / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_6

lemma o4_bernoulli_8 : bernoulli 8 = (-1 : ℚ) / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_8

lemma o4_bernoulli_10 : bernoulli 10 = (5 : ℚ) / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_10

lemma o4_bernoulli_12 : bernoulli 12 = (-691 : ℚ) / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_12

lemma o4_bernoulli_14 : bernoulli 14 = (7 : ℚ) / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_14

lemma o4_bernoulli_16 : bernoulli 16 = (-3617 : ℚ) / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_16

lemma o4_bernoulli_18 : bernoulli 18 = (43867 : ℚ) / 798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_18

lemma o4_bernoulli_20 : bernoulli 20 = (-174611 : ℚ) / 330 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_20

lemma o4_bernoulli_22 : bernoulli 22 = (854513 : ℚ) / 138 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_22

lemma o4_bernoulli_24 : bernoulli 24 = (-236364091 : ℚ) / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_24

lemma o4_bernoulli_26 : bernoulli 26 = (8553103 : ℚ) / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact o4_bern'_26

end FormalResearch.SignUncertainty
