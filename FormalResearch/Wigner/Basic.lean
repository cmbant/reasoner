module

public import Mathlib

/-!
# Inverse factorials with zero extension, and finite telescoping

General machinery for finite hypergeometric sums such as Racah's formulas for the Wigner
`3j` and `6j` symbols.

* `invFact u = 1/u!` for `u ≥ 0` and `0` for `u < 0` (the same convention as Physlib's
  `invFact`, so Physlib's finite sums can be compared with ours verbatim).
* `ifa x` extends it to rational arguments: `ifa x = 1/x!` if `x` is a natural number and `0`
  otherwise.  Half-integral spin combinations that are not integers therefore make a Racah
  sum vanish, which is the parity selection rule.
* The shift identity `(x+1) * ifa (x+1) = ifa x` holds for **all** `x : ℚ`; this is what makes
  termwise telescoping certificates polynomial.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- `1/u!` for `u ≥ 0`, and `0` for negative `u`. -/
noncomputable def invFact (u : ℤ) : ℝ :=
  if 0 ≤ u then ((u.toNat.factorial : ℝ))⁻¹ else 0

lemma invFact_natCast (n : ℕ) : invFact (n : ℤ) = ((n.factorial : ℝ))⁻¹ := by
  simp [invFact]

lemma invFact_of_neg {u : ℤ} (h : u < 0) : invFact u = 0 := by
  simp [invFact, not_le.mpr h]

/-- The shift identity at integer arguments, valid for every integer. -/
lemma invFact_shift (n : ℤ) : ((n : ℝ) + 1) * invFact (n + 1) = invFact n := by
  rcases lt_trichotomy n (-1) with h | h | h
  · rw [invFact_of_neg (u := n + 1) (by omega), invFact_of_neg (u := n) (by omega)]; simp
  · subst h; simp [invFact]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, invFact_natCast, invFact_natCast,
      Nat.factorial_succ]
    push_cast
    have : ((m.factorial : ℝ)) ≠ 0 := by positivity
    field_simp

/-- `1/x!` for a rational `x` that is a natural number; `0` otherwise. -/
noncomputable def ifa (x : ℚ) : ℝ :=
  if x.den = 1 then invFact x.num else 0

lemma exists_int_iff {x : ℚ} : (∃ n : ℤ, x = n) ↔ x.den = 1 := by
  constructor
  · rintro ⟨n, rfl⟩; simp
  · intro h; exact ⟨x.num, (Rat.den_eq_one_iff x).mp h |>.symm⟩

lemma ifa_intCast (n : ℤ) : ifa (n : ℚ) = invFact n := by
  simp [ifa]

lemma ifa_of_not_int {x : ℚ} (h : ¬ ∃ n : ℤ, x = n) : ifa x = 0 := by
  rw [exists_int_iff] at h
  simp [ifa, h]

/-- The shift identity for rational arguments. -/
lemma ifa_shift (x : ℚ) : ((x : ℝ) + 1) * ifa (x + 1) = ifa x := by
  by_cases h : ∃ n : ℤ, x = n
  · obtain ⟨n, rfl⟩ := h
    have : ((n : ℚ) + 1) = ((n + 1 : ℤ) : ℚ) := by push_cast; ring
    rw [this, ifa_intCast, ifa_intCast]
    simpa using invFact_shift n
  · have h' : ¬ ∃ n : ℤ, x + 1 = n := by
      rintro ⟨n, hn⟩
      exact h ⟨n - 1, by push_cast; linarith⟩
    rw [ifa_of_not_int h, ifa_of_not_int h']; simp

/-- `x!⁻¹ = (x+1)⋯(x+k) (x+k)!⁻¹`. -/
lemma ifa_up (x : ℚ) (k : ℕ) :
    ifa x = (∏ i ∈ Finset.range k, ((x : ℝ) + (i + 1))) * ifa (x + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, Finset.prod_range_succ, mul_assoc]
    congr 1
    have := ifa_shift (x + k)
    rw [show x + ((k + 1 : ℕ) : ℚ) = x + k + 1 by push_cast; ring]
    push_cast at this ⊢
    rw [← this]; ring

lemma ifa_nonneg_of_ne_zero {x : ℚ} (h : ifa x ≠ 0) : 0 ≤ x := by
  by_cases hx : ∃ n : ℤ, x = n
  · obtain ⟨n, rfl⟩ := hx
    rw [ifa_intCast] at h
    by_contra hn
    exact h (invFact_of_neg (by exact_mod_cast not_le.mp hn))
  · exact absurd (ifa_of_not_int hx) h

lemma ifa_eq_zero_of_neg {x : ℚ} (h : x < 0) : ifa x = 0 := by
  by_contra hne
  exact absurd (ifa_nonneg_of_ne_zero hne) (not_le.mpr h)

/-- A finite telescoping sum over `ℕ`: if `H` has finite support and `H 0 = 0`, then
`∑ᶠ t, (H (t+1) - H t) = 0`. -/
lemma finsum_nat_telescope (H : ℕ → ℝ) (hfin : (Function.support H).Finite) (h0 : H 0 = 0) :
    ∑ᶠ t : ℕ, (H (t + 1) - H t) = 0 := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ t, N ≤ t → H t = 0 := by
    obtain ⟨N, hN⟩ := hfin.bddAbove
    exact ⟨N + 1, fun t ht => by
      by_contra h
      have := hN (show t ∈ Function.support H from h)
      omega⟩
  have hsub : Function.support (fun t => H (t + 1) - H t) ⊆ ↑(Finset.range N) := by
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply ht
    simp [hN t (by omega), hN (t + 1) (by omega)]
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_range_sub (fun t => H t) N,
    hN N le_rfl, h0]; simp

/-- The product `∏ ifa (x i)` over six rational arguments. -/
noncomputable def P6 (x : Fin 6 → ℚ) : ℝ := ∏ i, ifa (x i)

/-- Rewriting every factor of `P6 x` against reference arguments `r i = x i + k i`. -/
lemma P6_rel {x r : Fin 6 → ℚ} {k : Fin 6 → ℕ} (h : ∀ i, r i = x i + k i) :
    P6 x = (∏ i, ∏ j ∈ Finset.range (k i), ((x i : ℝ) + (j + 1))) * P6 r := by
  unfold P6
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [ifa_up (x i) (k i), ← h i]

/-- The product `∏ ifa (x i)` over seven rational arguments. -/
noncomputable def P7 (x : Fin 7 → ℚ) : ℝ := ∏ i, ifa (x i)

/-- Rewriting every factor of `P7 x` against reference arguments `r i = x i + k i`. -/
lemma P7_rel {x r : Fin 7 → ℚ} {k : Fin 7 → ℕ} (h : ∀ i, r i = x i + k i) :
    P7 x = (∏ i, ∏ j ∈ Finset.range (k i), ((x i : ℝ) + (j + 1))) * P7 r := by
  unfold P7
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [ifa_up (x i) (k i), ← h i]

/-- A finite telescoping sum over `range`. -/
lemma sum_range_telescope (H : ℕ → ℝ) (N : ℕ) (h0 : H 0 = 0) (hN : H N = 0) :
    ∑ s ∈ Finset.range N, (H (s + 1) - H s) = 0 := by
  rw [Finset.sum_range_sub, hN, h0]; simp

end FormalResearch.Wigner
