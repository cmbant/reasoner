/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Pochhammer symbols and elementary finite-product identities

## Main definitions

* `pochhammer`: the Pochhammer symbol `(a)_n`.

## Main results

* `pochhammer_zero`, `pochhammer_succ`: `(a)_0 = 1` and `(a)_{n+1} = (a)_n (a + n)`, DLMF 5.2.4.
* `pochhammer_neg_nat_eq_zero`: vanishing at negative integers, DLMF 5.2.7.
* `pochhammer_add`, `pochhammer_add_eq_sum`: concatenation and the binomial theorem for rising
  factorials.
* `sum_pochhammer_neg_nat_div_factorial_mul_pow`: `∑ₖ (-n)ₖ yᵏ / k! = (1 - y)ⁿ`.
* `pochhammer_reflect`, `pochhammer_one_sub_sub_mul`: reflection identities.
* `pochhammer_ne_zero_of_not_neg_nat`, `pochhammer_ne_zero_of_le`: nonvanishing.
-/

public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval

namespace DLMF.Hypergeometric

/-- The `n`-th Pochhammer symbol `(a)_n`. -/
abbrev pochhammer (a : ℂ) (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval a

/-- Identity under the stated parameter and domain assumptions: `pochhammer a 0 = 1`. -/
@[dlmf 5.2.E4]
theorem pochhammer_zero (a : ℂ) : pochhammer a 0 = 1 := by simp [pochhammer]

/-- `(a)₁ = a`. -/
theorem pochhammer_one (a : ℂ) : pochhammer a 1 = a := by simp [pochhammer]

/-- Identity under the stated parameter and domain assumptions:
`pochhammer a (n + 1) = pochhammer a n * (a + n)`. -/
@[dlmf 5.2.E4]
theorem pochhammer_succ (a : ℂ) (n : ℕ) : pochhammer a (n + 1) = pochhammer a n * (a + n) :=
  ascPochhammer_succ_eval n a

/-- `(1)ₙ = n!`. -/
theorem pochhammer_nat_one (n : ℕ) : pochhammer (1 : ℂ) n = n ! := by
  simp [pochhammer, ascPochhammer_eval_one]

/-- `(2)ₙ = (n + 1)!`. -/
theorem pochhammer_nat_two (n : ℕ) : pochhammer (2 : ℂ) n = ((n + 1)! : ℂ) := by
  unfold pochhammer
  rw [show (2 : ℂ) = ↑(2 : ℕ) by simp, ascPochhammer_nat_eq_natCast_ascFactorial]
  simp [Nat.ascFactorial_eq_div (n := 1) n, Nat.factorial_one, add_comm]

/-- `(0)ₙ₊₁ = 0`. -/
theorem pochhammer_zero_succ (n : ℕ) : pochhammer (0 : ℂ) (n + 1) = 0 := by
  rw [pochhammer, (ascPochhammer_eval_eq_zero_iff _ _).2]
  exact ⟨0, Nat.succ_pos n, by simp⟩

/-- `(a)ₙ ≠ 0` when `a` is not a nonpositive integer. -/
theorem pochhammer_ne_zero_of_not_neg_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (n : ℕ) :
    pochhammer a n ≠ 0 := by
  intro h
  obtain ⟨k, hk, hk'⟩ := (ascPochhammer_eval_eq_zero_iff (R := ℂ) n a).1 h
  exact ha k (neg_eq_iff_eq_neg.mp hk'.symm)

/-- Pochhammer symbols at points of positive real part do not vanish. -/
theorem pochhammer_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (k : ℕ) : pochhammer z k ≠ 0 :=
  pochhammer_ne_zero_of_not_neg_nat (fun j h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) k

/-- `Γ(α + k) = (α)ₖ Γ(α)` for `Re α > 0`. -/
theorem Gamma_add_nat_eq_pochhammer_mul_Gamma {α : ℂ} (hα : 0 < α.re) (k : ℕ) :
    Complex.Gamma (α + k) = pochhammer α k * Complex.Gamma α := by
  induction k with
  | zero => simp [pochhammer_zero]
  | succ k ih =>
    have hne : α + k ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih, pochhammer_succ]
    ring

/-- Concatenation of Pochhammer symbols: `(a)_{n+m} = (a)_n (a+n)_m`. -/
theorem pochhammer_add (a : ℂ) (n m : ℕ) : pochhammer a (n + m) = pochhammer a n *
    pochhammer (a + n) m := by
  induction m with
  | zero => simp [pochhammer_zero]
  | succ m ih =>
    rw [Nat.add_succ, pochhammer_succ, ih, pochhammer_succ]
    push_cast
    ring

/-- Binomial theorem for rising factorials: `(a + b)_N = ∑ C(N,m) (a)_m (b)_{N-m}`. -/
theorem pochhammer_add_eq_sum (a b : ℂ) (N : ℕ) :
    pochhammer (a + b) N = ∑ m ∈ Finset.range (N + 1), (N.choose m : ℂ) * pochhammer a m *
        pochhammer b (N - m) := by
  induction N with
  | zero => simp [pochhammer_zero]
  | succ N ih =>
    rw [pochhammer_succ, ih, Finset.sum_mul]
    rw [Finset.sum_range_succ' _ (N + 1)]
    simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib,
      Nat.choose_zero_right, Nat.cast_one, one_mul, pochhammer_zero, Nat.sub_zero,
          Nat.succ_eq_add_one]
    have hB : ∑ m ∈ Finset.range (N + 1), (N.choose (m + 1) : ℂ) * pochhammer a (m + 1) *
        pochhammer b (N + 1 - (m + 1)) + pochhammer b (N + 1) =
        ∑ m ∈ Finset.range (N + 1), (N.choose m : ℂ) * pochhammer a m *
            pochhammer b (N + 1 - m) := by
      rw [Finset.sum_range_succ'
          (fun m => (N.choose m : ℂ) * pochhammer a m * pochhammer b (N + 1 - m)),
        Finset.sum_range_succ]
      simp [Nat.choose_succ_self, pochhammer_zero]
    conv_rhs => rw [add_assoc, hB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmN : m ≤ N := by simp at hm; omega
    rw [show N + 1 - (m + 1) = N - m by omega, show N + 1 - m = (N - m) + 1 by omega,
      pochhammer_succ a m, pochhammer_succ b (N - m), Nat.cast_sub hmN]
    ring

/-- Distributing a power over the factors of a Pochhammer symbol. -/
theorem pochhammer_mul_pow (c t : ℂ) (k : ℕ) :
    pochhammer c k * t ^ k = ∏ j ∈ Finset.range k, ((c + j) * t) := by
  induction k with
  | zero => simp [pochhammer_zero]
  | succ k ih => rw [pochhammer_succ, Finset.prod_range_succ, ← ih]; ring

/-- Helper lemma for terminating hypergeometric sums: `(-n)_k = (-1)^k n^{\underline{k}}`. -/
theorem pochhammer_neg_coe_nat (n k : ℕ) :
    pochhammer (-(n : ℂ)) k = (-1 : ℂ) ^ k * n.descFactorial k := by
  rw [pochhammer, ascPochhammer_eval_neg_eq_descPochhammer ℂ (n : ℂ) k,
    descPochhammer_eval_eq_descFactorial ℂ n k]

/-- Binomial theorem in Pochhammer form: `∑ₖ (-n)ₖ yᵏ / k! = (1 - y)ⁿ`. -/
theorem sum_pochhammer_neg_nat_div_factorial_mul_pow (n : ℕ) (y : ℂ) :
    ∑ k ∈ Finset.range (n + 1), pochhammer (-(n : ℂ)) k / k ! * y ^ k = (1 - y) ^ n := by
  rw [sub_eq_add_neg, add_comm (1 : ℂ), add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose, one_pow, neg_pow y]
  push_cast
  field_simp

/-- Helper lemma for terminating hypergeometric sums. -/
@[dlmf 5.2.E7]
theorem pochhammer_neg_nat_eq_zero {n k : ℕ} (h : n < k) : pochhammer (-(n : ℂ)) k = 0 := by
  rw [pochhammer, ascPochhammer_eval_eq_zero_iff]
  exact ⟨n, h, by simp⟩

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`. -/
theorem pochhammer_three_halves_eq (n : ℕ) :
    pochhammer (3 / 2 : ℂ) n = (2 * n + 1 : ℂ) * pochhammer (1 / 2) n := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, pochhammer_succ, ih]
    push_cast
    ring

/-- Mathlib's left Pochhammer recurrence in the project's notation. -/
theorem pochhammer_succ_left (a : ℂ) (n : ℕ) : pochhammer a (n + 1) = a * pochhammer (a + 1) n := by
  simp [pochhammer, ascPochhammer_succ_left, Polynomial.eval_comp]

/-- Reflection of a Pochhammer symbol: `(1 - y - m)_m = (-1)^m (y)_m`. -/
theorem pochhammer_reflect (y : ℂ) (m : ℕ) : pochhammer (1 - y - m) m = (-1 : ℂ) ^ m *
    pochhammer y m := by
  induction m with
  | zero => simp [pochhammer_zero]
  | succ m ih =>
    rw [pochhammer_succ_left, show 1 - y - ((m + 1 : ℕ) : ℂ) + 1 = 1 - y - m by push_cast; ring, ih,
      pochhammer_succ]
    push_cast
    ring

/-- `(1-x-m)_{m-j} = (-1)^{m-j} (x)_m / (x)_j` in multiplied-out form. -/
theorem pochhammer_one_sub_sub_mul {x : ℂ} {m j : ℕ} (hj : j ≤ m) :
    pochhammer x j * pochhammer (1 - x - m) (m - j) = (-1 : ℂ) ^ (m - j) * pochhammer x m := by
  have h := pochhammer_reflect (x + j) (m - j)
  rw [show 1 - (x + j) - ((m - j : ℕ) : ℂ) = 1 - x - m by push_cast [hj]; ring] at h
  rw [h, show pochhammer x m = pochhammer x (j + (m - j)) by rw [Nat.add_sub_cancel' hj],
                                                               pochhammer_add]
  ring

/-- If `(x)_N ≠ 0` then `(x)_k ≠ 0` for every `k ≤ N`. -/
theorem pochhammer_ne_zero_of_le {x : ℂ} {N k : ℕ} (hk : k ≤ N) (h : pochhammer x N ≠ 0) :
    pochhammer x k ≠ 0 := by
  intro h0
  apply h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pochhammer_add, h0, zero_mul]

end DLMF.Hypergeometric
