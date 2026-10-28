import Mathlib

/-!
# A binomial-sum identity behind the odd-`n` purity tradeoff (pure algebra)

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200), proof of
`thm:odd-spinflip-tradeoff`: the polynomial `Q(x)` of that proof is the antisymmetrisation
`Σ_{s ≤ m} q_s (x^s - x^{n-s})` of its lower half, `n = 2m+1`, with
`q_s = (-1)^s [2 C(m,s) + C(m,s-1) - C(n,s)] - δ_{s0} + (1 + (-1)^m) δ_{sm}`.

`qSum_eq` proves this in any commutative ring, for every `m`:
`Σ_{s ≤ m} q_s (T^s - T^{2m+1-s}) = T^m - T^{m+1} - 1 + T^{2m+1} + (2-T)(1-T)^m - (1-T)^{2m+1}
 - (-1)^m (2T-1) T^m (1-T)^m`.
Claim class: **proved** (pure algebra, no hypotheses).
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SpinFlip

section QSum

variable {R : Type*} [CommRing R]

/-- The coefficient `q_s` of the proof of `thm:odd-spinflip-tradeoff` (`n = 2m+1`). -/
def qc (R : Type*) [CommRing R] (m s : ℕ) : R :=
  (-1) ^ s * (2 * (m.choose s : R) + (if s = 0 then 0 else (m.choose (s - 1) : R))
      - ((2 * m + 1).choose s : R))
    - (if s = 0 then 1 else 0) + (if s = m then 1 + (-1) ^ m else 0)

theorem sum_alt_choose_pow (T : R) (k : ℕ) :
    ∑ s ∈ range (k + 1), (-1 : R) ^ s * (k.choose s : R) * T ^ s = (1 - T) ^ k := by
  have h := add_pow (-T) (1 : R) k
  rw [show (1 : R) - T = -T + 1 by ring, h]
  refine sum_congr rfl fun s _ => ?_
  rw [neg_pow]; simp only [one_pow, mul_one]; ring

theorem sum_alt_choose_pow_rev (T : R) (k : ℕ) :
    ∑ s ∈ range (k + 1), (-1 : R) ^ s * (k.choose s : R) * T ^ (k - s) = (T - 1) ^ k := by
  have h := add_pow (-1 : R) T k
  rw [show T - 1 = -1 + T by ring, h]
  refine sum_congr rfl fun s _ => ?_
  ring

theorem pow_sub_split (T : R) (m s : ℕ) (hs : s ≤ m) :
    T ^ (2 * m + 1 - s) = T ^ (m + 1) * T ^ (m - s) := by
  rw [← pow_add]; congr 1; omega

/-- Part A. -/
theorem qsum_A (T : R) (m : ℕ) :
    ∑ s ∈ range (m + 1), (-1 : R) ^ s * (m.choose s : R) * (T ^ s - T ^ (2 * m + 1 - s))
      = (1 - T) ^ m - T ^ (m + 1) * (T - 1) ^ m := by
  simp_rw [mul_sub, sum_sub_distrib]
  rw [sum_alt_choose_pow]
  congr 1
  rw [← sum_alt_choose_pow_rev, mul_sum]
  refine sum_congr rfl fun s hs => ?_
  rw [pow_sub_split T m s (Nat.lt_succ_iff.mp (mem_range.mp hs))]; ring

/-- Part B. -/
theorem qsum_B (T : R) (m : ℕ) :
    ∑ s ∈ range (m + 1), (-1 : R) ^ s * (if s = 0 then 0 else (m.choose (s - 1) : R)) *
        (T ^ s - T ^ (2 * m + 1 - s))
      = -T * ((1 - T) ^ m - (-1) ^ m * T ^ m) + T ^ m * ((T - 1) ^ m - (-1) ^ m) := by
  rw [sum_range_succ']
  simp only [ite_true, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, mul_zero, zero_mul, add_zero]
  have h1 := sum_alt_choose_pow T m
  have h2 := sum_alt_choose_pow_rev T m
  rw [sum_range_succ] at h1 h2
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero] at h1 h2
  have e : ∀ t ∈ range m, (-1 : R) ^ (t + 1) * (m.choose t : R) * (T ^ (t + 1) - T ^ (2 * m + 1 - (t + 1)))
      = -T * ((-1 : R) ^ t * (m.choose t : R) * T ^ t)
        + T ^ m * ((-1 : R) ^ t * (m.choose t : R) * T ^ (m - t)) := by
    intro t ht
    have ht' : t ≤ m := (mem_range.mp ht).le
    have : T ^ (2 * m + 1 - (t + 1)) = T ^ m * T ^ (m - t) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; ring
  rw [sum_congr rfl e, sum_add_distrib, ← mul_sum, ← mul_sum]
  have a1 : ∑ t ∈ range m, (-1 : R) ^ t * (m.choose t : R) * T ^ t = (1 - T) ^ m - (-1) ^ m * T ^ m := by
    linear_combination h1
  have a2 : ∑ t ∈ range m, (-1 : R) ^ t * (m.choose t : R) * T ^ (m - t) = (T - 1) ^ m - (-1) ^ m := by
    linear_combination h2
  rw [a1, a2]

/-- Part C. -/
theorem qsum_C (T : R) (m : ℕ) :
    ∑ s ∈ range (m + 1), (-1 : R) ^ s * ((2 * m + 1).choose s : R) * (T ^ s - T ^ (2 * m + 1 - s))
      = (1 - T) ^ (2 * m + 1) := by
  have h := sum_alt_choose_pow T (2 * m + 1)
  rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring, sum_range_add] at h
  have hr := sum_range_reflect (fun x => (-1 : R) ^ (m + 1 + x) * ((2 * m + 1).choose (m + 1 + x) : R) *
    T ^ (m + 1 + x)) (m + 1)
  have key : ∀ s ∈ range (m + 1),
      (-1 : R) ^ (m + 1 + (m + 1 - 1 - s)) * ((2 * m + 1).choose (m + 1 + (m + 1 - 1 - s)) : R) *
        T ^ (m + 1 + (m + 1 - 1 - s))
      = -((-1 : R) ^ s * ((2 * m + 1).choose s : R) * T ^ (2 * m + 1 - s)) := by
    intro s hs
    have hs' : s ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hs)
    have e1 : m + 1 + (m + 1 - 1 - s) = 2 * m + 1 - s := by omega
    rw [e1]
    have e2 : (2 * m + 1).choose (2 * m + 1 - s) = (2 * m + 1).choose s :=
      Nat.choose_symm (by omega)
    rw [e2]
    have e3 : (-1 : R) ^ (2 * m + 1 - s) = -((-1 : R) ^ s) := by
      have : (-1 : R) ^ (2 * m + 1 - s) * (-1) ^ s = -1 := by
        rw [← pow_add, show 2 * m + 1 - s + s = 2 * m + 1 by omega, pow_succ, pow_mul]; simp
      have hs2 : ((-1 : R) ^ s) * (-1) ^ s = 1 := by rw [← mul_pow]; simp
      linear_combination (-1 : R) ^ s * this - (-1 : R) ^ (2 * m + 1 - s) * hs2
    rw [e3]; ring
  rw [sum_congr rfl key, sum_neg_distrib] at hr
  simp_rw [mul_sub, sum_sub_distrib]
  linear_combination h + hr

/-- **`Q = Σ_{s ≤ m} q_s (x^s - x^{n-s})`** (`n = 2m+1`), in any commutative ring. -/
theorem qSum_eq (T : R) (m : ℕ) :
    ∑ s ∈ range (m + 1), qc R m s * (T ^ s - T ^ (2 * m + 1 - s))
      = T ^ m - T ^ (m + 1) - 1 + T ^ (2 * m + 1) + (2 - T) * (1 - T) ^ m - (1 - T) ^ (2 * m + 1)
        - (-1) ^ m * (2 * T - 1) * T ^ m * (1 - T) ^ m := by
  have hterm : ∀ s ∈ range (m + 1), qc R m s * (T ^ s - T ^ (2 * m + 1 - s))
      = 2 * ((-1 : R) ^ s * (m.choose s : R) * (T ^ s - T ^ (2 * m + 1 - s)))
        + (-1 : R) ^ s * (if s = 0 then 0 else (m.choose (s - 1) : R)) * (T ^ s - T ^ (2 * m + 1 - s))
        - (-1 : R) ^ s * ((2 * m + 1).choose s : R) * (T ^ s - T ^ (2 * m + 1 - s))
        - (if s = 0 then (T ^ s - T ^ (2 * m + 1 - s)) else 0)
        + (if s = m then (1 + (-1) ^ m) * (T ^ s - T ^ (2 * m + 1 - s)) else 0) := by
    intro s _
    unfold qc
    split_ifs <;> ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
    ← mul_sum, qsum_A, qsum_B, qsum_C, sum_ite_eq', sum_ite_eq']
  simp only [mem_range, Nat.succ_pos, ite_true, Nat.lt_succ_self]
  have e : 2 * m + 1 - m = m + 1 := by omega
  rw [e]
  have hneg : (T - 1) ^ m = (-1) ^ m * (1 - T) ^ m := by
    rw [← neg_sub, neg_pow]
  rw [hneg]
  simp only [pow_zero, Nat.sub_zero, pow_succ, pow_mul]
  ring

end QSum

end FormalResearch.FourQubitEntropy.SpinFlip
