/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.Mathematics.SpecialFunctions.Hypergeometric.Saalschutz

/-!

# Term identities for the Sears transformation

The splitting of the summand of a terminating balanced `₄F₃(1)` into the two factors of the double
sum that proves the Sears transformation.

## i. Overview

The Sears transformation (`PhyslibAlpha.Hypergeometric.sears`) expresses a terminating balanced
`₄F₃(1)` with upper parameters `-n, A, B, C` and lower parameters `d, e, f` through the series with
upper parameters `-n, A, d - B, d - C` and lower parameters `d, A - e - n + 1, A - f - n + 1`.
Its proof expands one ratio of Pochhammer symbols by the Pfaff–Saalschütz sum, which turns a
single sum into a double sum over `(j, i)`. This file records the identities for the summands.

- `searsOuter n A B C d A2 A3 j` is the factor of the double sum depending on `j` only;
- `searsInner n A D A2 A3 j i` is the summand, in `i`, of a Saalschütz sum for fixed `j`.

`term_split` writes the summand of the expanded sum as the product of the two factors, and
`final_pt` identifies the result of the inner Saalschütz sum with the summand of the series being
transformed.

## ii. Key results

- `searsOuter`, `searsInner`: the two factors of the double sum.
- `term_split`, `term_split'`: the summand of the expanded sum is `searsOuter * searsInner`.
- `final_pt`: the inner sum, evaluated by `saal`, is a multiple of the summand of the original
  series.

## iii. Table of contents

- A. The two factors
- B. Splitting the summand
- C. The evaluated inner sum

## iv. References

- G. E. Andrews, R. Askey, R. Roy, *Special Functions*, Cambridge University Press (1999),
  §3.3.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hypergeometric

open Finset

/-!

## A. The two factors

-/

/-- The first-stage double sum term of the Sears transformation. -/
def searsOuter (n : ℕ) (A B C d A2 A3 : ℝ) (j : ℕ) : ℝ :=
  rf (-n) j * rf A j * rf B j * rf C j / ((j.factorial : ℝ) * rf A2 j * rf A3 j * rf d j)

/-- The summand, in `i`, of the Saalschütz sum that follows the splitting of the summand. -/
def searsInner (n : ℕ) (A D A2 A3 : ℝ) (j i : ℕ) : ℝ :=
  rf (-(n : ℝ) + j) i * rf (A + j) i * rf D i /
    ((i.factorial : ℝ) * rf (A2 + j) i * rf (A3 + j) i)


/-!

## B. Splitting the summand

-/

/-- With `k = j + i`, the product of `(-n)_k (A)_k / (k! (A2)_k (A3)_k)`,
`(-1)^k (1 + B + C - d - k)_k` and the Saalschütz term of length `k` splits as
`searsOuter * searsInner`. -/
lemma term_split (n j i : ℕ) (A B C d A2 A3 : ℝ)
    (hD : rf (d - B - C) (j + i) ≠ 0) (hA2 : rf A2 (j + i) ≠ 0) (hA3 : rf A3 (j + i) ≠ 0)
    (hdj : rf d j ≠ 0) :
    rf (-(n : ℝ)) (j + i) * rf A (j + i) /
        (((j + i).factorial : ℝ) * rf A2 (j + i) * rf A3 (j + i)) *
      ((-1) ^ (j + i) * rf (1 + B + C - d - ((j + i : ℕ) : ℝ)) (j + i)) *
      saalTerm (j + i) B C d (1 + B + C - d - ((j + i : ℕ) : ℝ)) j =
    searsOuter n A B C d A2 A3 j * searsInner n A (d - B - C) A2 A3 j i := by
  have hij : j + i = i + j := add_comm j i
  have hD' : rf (d - B - C) i * rf (d - B - C + i) j ≠ 0 := by
    rw [← rf_add, ← hij]; exact hD
  have hDi : rf (d - B - C) i ≠ 0 := left_ne_zero_of_mul hD'
  have hDij : rf (d - B - C + i) j ≠ 0 := right_ne_zero_of_mul hD'
  have hA2' : rf A2 j * rf (A2 + j) i ≠ 0 := by rw [← rf_add]; exact hA2
  have hA3' : rf A3 j * rf (A3 + j) i ≠ 0 := by rw [← rf_add]; exact hA3
  have hA2j := left_ne_zero_of_mul hA2'
  have hA2i := right_ne_zero_of_mul hA2'
  have hA3j := left_ne_zero_of_mul hA3'
  have hA3i := right_ne_zero_of_mul hA3'
  have hfact : (((j + i).factorial : ℕ) : ℝ) = i.factorial * rf (1 + i) j := by
    have h := rf_one_add i j
    rw [hij, ← h]; ring
  have hE : rf (1 + B + C - d - ((j + i : ℕ) : ℝ)) (j + i) =
      (-1) ^ (j + i) * rf (d - B - C) (j + i) :=
    rf_reflect' _ _ _ (by push_cast; ring)
  have hsgn : ((-1 : ℝ) ^ (j + i)) * (-1) ^ (j + i) = 1 := by rw [← mul_pow]; simp
  have hneg : rf (-(((j + i : ℕ)) : ℝ)) j = (-1) ^ j * rf (1 + i) j :=
    rf_reflect' _ _ _ (by push_cast; ring)
  have hE2 : rf (1 + B + C - d - ((j + i : ℕ) : ℝ)) j = (-1) ^ j * rf (d - B - C + i) j :=
    rf_reflect' _ _ _ (by push_cast; ring)
  have hDs : rf (d - B - C) (j + i) = rf (d - B - C) i * rf (d - B - C + i) j := by
    rw [hij, rf_add]
  have hsj : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; simp
  have hf1 : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hf2 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hr1 : rf (1 + (i : ℝ)) j ≠ 0 := by
    intro h0
    have := rf_one_add i j
    rw [h0] at this
    have h3 : (((i + j).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact h3 (by rw [← this]; ring)
  simp only [searsOuter, searsInner, saalTerm]
  rw [rf_add (-(n : ℝ)) j i, rf_add A j i, rf_add A2 j i, rf_add A3 j i, hE, hDs, hneg, hE2, hfact]
  rw [show ((-1 : ℝ) ^ (j + i) * ((-1) ^ (j + i) * (rf (d - B - C) i * rf (d - B - C + i) j))) =
    rf (d - B - C) i * rf (d - B - C + i) j by rw [← mul_assoc, hsgn, one_mul]]
  field_simp


/-- `term_split` with the index `i` written as `k - j`. -/
lemma term_split' (n k j : ℕ) (hj : j ≤ k) (A B C d A2 A3 : ℝ)
    (hD : rf (d - B - C) k ≠ 0) (hA2 : rf A2 k ≠ 0) (hA3 : rf A3 k ≠ 0)
    (hdj : rf d j ≠ 0) :
    rf (-(n : ℝ)) k * rf A k / ((k.factorial : ℝ) * rf A2 k * rf A3 k) *
      ((-1) ^ k * rf (1 + B + C - d - (k : ℝ)) k) *
      saalTerm k B C d (1 + B + C - d - (k : ℝ)) j =
    searsOuter n A B C d A2 A3 j * searsInner n A (d - B - C) A2 A3 j (k - j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  have := term_split n j i A B C d A2 A3 hD hA2 hA3 hdj
  simpa using this


/-!

## C. The evaluated inner sum

-/

/-- The value of the inner Saalschütz sum, times `searsOuter`, is a multiple of the summand of the
series `₄F₃(-n, A, B, C; d, e, f)`. -/
lemma final_pt (j m : ℕ) (A B C d e f : ℝ) (hbal : d + e + f = A + B + C - ((j + m : ℕ) : ℝ) + 1)
    (he : rf e (j + m) ≠ 0) (hf : rf f (j + m) ≠ 0)
    (hA2 : rf (A - e - ((j + m : ℕ) : ℝ) + 1) (j + m) ≠ 0)
    (hA3 : rf (A - f - ((j + m : ℕ) : ℝ) + 1) (j + m) ≠ 0) (hd : rf d (j + m) ≠ 0) :
    searsOuter (j + m) A B C d (A - e - ((j + m : ℕ) : ℝ) + 1) (A - f - ((j + m : ℕ) : ℝ) + 1) j *
      ((-1) ^ (j + m - j) * rf ((A - e - ((j + m : ℕ) : ℝ) + 1) + j - (A + j)) (j + m - j) *
        rf ((A - e - ((j + m : ℕ) : ℝ) + 1) + j - (d - B - C)) (j + m - j) /
        (rf ((A - e - ((j + m : ℕ) : ℝ) + 1) + j) (j + m - j) *
          rf ((A - f - ((j + m : ℕ) : ℝ) + 1) + j) (j + m - j))) =
    rf e (j + m) * rf f (j + m) / (rf (A - e - ((j + m : ℕ) : ℝ) + 1) (j + m) *
        rf (A - f - ((j + m : ℕ) : ℝ) + 1) (j + m)) *
      (rf (-(((j + m : ℕ)) : ℝ)) j * rf A j * rf B j * rf C j /
        ((j.factorial : ℝ) * rf d j * rf e j * rf f j)) := by
  set A2 : ℝ := A - e - ((j + m : ℕ) : ℝ) + 1 with hA2d
  set A3 : ℝ := A - f - ((j + m : ℕ) : ℝ) + 1 with hA3d
  have hjm : j + m - j = m := by omega
  rw [hjm]
  have hs : ∀ x : ℝ, rf x (j + m) = rf x j * rf (x + j) m := fun x => rf_add x j m
  have e1 : rf (A2 + j - (A + j)) m = (-1) ^ m * rf (e + j) m :=
    rf_reflect' _ _ _ (by rw [hA2d]; push_cast; ring)
  have e2 : A2 + j - (d - B - C) = f + j := by rw [hA2d]; push_cast at hbal ⊢; linarith
  rw [e2, e1]
  have hej : rf e j ≠ 0 := rf_ne_zero_of_le he (by omega)
  have hfj : rf f j ≠ 0 := rf_ne_zero_of_le hf (by omega)
  have hdj : rf d j ≠ 0 := rf_ne_zero_of_le hd (by omega)
  have hA2' : rf A2 j * rf (A2 + j) m ≠ 0 := by rw [← hs]; exact hA2
  have hA3' : rf A3 j * rf (A3 + j) m ≠ 0 := by rw [← hs]; exact hA3
  have hA2j := left_ne_zero_of_mul hA2'
  have hA2m := right_ne_zero_of_mul hA2'
  have hA3j := left_ne_zero_of_mul hA3'
  have hA3m := right_ne_zero_of_mul hA3'
  have hsg : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have hf0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [hs e, hs f, hs A2, hs A3]
  simp only [searsOuter]
  rcases neg_one_pow_eq_or ℝ m with h | h <;> simp only [h] <;> field_simp

end PhyslibAlpha.Hypergeometric
