/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.ClebschGordanFormula
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.RacahDoubleSum

/-!

# The inner sum of Racah's double sum

The sum over `z` in `collapseSum`, at fixed `α`, is Racah's Clebsch–Gordan sum `racahR`, which is
also an alternating binomial sum in a second index `x`.

## i. Overview

For fixed `α`, the `z`-sum of `collapseSum` is, up to the factorials
`1 / (k₃! (b - k₃)! (c - k₃)!)`, the integer-valued sum `racahR (b - k₃) (c - k₃) k₃ (k₁ - α)
(K - k₁ - k₃)` of `ClebschGordanFormula`, namely the sum for the Clebsch–Gordan coefficient
`⟨b c k₃; ν β γ⟩` (`z_sum_eq_racahR`). By `racahL_eq_racahR`, which is the transformation between
the two forms of the Clebsch–Gordan sum, this equals `racahL`, a sum over a second index `x`
(`racahL_eq_x_sum`). Exchanging the order of the sums over `α` and `x`, the `α`-sum is then a
Vandermonde convolution (`RacahVandermonde`), which gives `Xs`.

This file converts between the integer binomial coefficients `zchoose` of `ClebschGordanFormula`
and the zero-extended real binomial coefficients `zbinom`.

## ii. Key results

- `z_sum_eq_racahR`: the inner sum of `collapseSum` as `racahR`.
- `racahL_eq_x_sum`: `racahL` as a sum over `x` of the shape of `Xs`.

## iii. Table of contents

- A. Binomial coefficients
- B. The inner sum

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

## A. Binomial coefficients

-/

/-- The integer binomial `zchoose` is the real zero-extended binomial `zbinom`. -/
lemma zchoose_eq_zbinom (n : ℕ) (j : ℤ) : ((zchoose n j : ℤ) : ℝ) = zbinom n j := by
  by_cases hj : j < 0
  · rw [zchoose_of_neg hj, zbinom, ite_eq_right (by omega)]; simp
  · obtain ⟨J, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
    rw [zchoose_natCast, zbinom]
    by_cases hJ : J ≤ n
    · rw [ite_eq_left (by omega)]; simp
    · rw [ite_eq_right (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma natCast_choose_eq (n z : ℕ) : ((n.choose z : ℕ) : ℝ) = zbinom n z := by
  rw [zbinom]
  by_cases hz : z ≤ n
  · rw [ite_eq_left (by omega)]; simp
  · rw [ite_eq_right (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

/-!

## B. The inner sum

-/

/-- The inner `z`-sum of `collapseSum` is Racah's sum `racahR` (divided by the factorials). -/
lemma z_sum_eq_racahR (b c k₃ : ℕ) (hb : k₃ ≤ b) (hc : k₃ ≤ c) (k₁ K α : ℤ) :
    ∑ᶠ z : ℤ, (-1 : ℝ) ^ z * invFact z * invFact (k₃ - z) * invFact (k₁ - α - z) *
        invFact (c - K + k₁ - z) * invFact (b - k₁ - k₃ + z + α) * invFact (K - k₁ - k₃ + z) =
      invFact k₃ * invFact ((b : ℤ) - k₃) * invFact ((c : ℤ) - k₃) *
        (racahR (b - k₃) (c - k₃) k₃ (k₁ - α) (K - k₁ - k₃) : ℝ) := by
  rw [finsum_int_eq_sum_range _ k₃ (fun z hz => ?_), racahR, Int.cast_sum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hzk : z ≤ k₃ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hz)
    push_cast
    rw [zchoose_eq_zbinom, zchoose_eq_zbinom, natCast_choose_eq, zbinom_eq, zbinom_eq, zbinom_eq,
      zpow_natCast, Nat.cast_sub hb, Nat.cast_sub hc]
    have f1 : factZ k₃ * invFact k₃ = 1 := factZ_mul_invFact (by omega)
    have f2 : factZ ((b : ℤ) - k₃) * invFact ((b : ℤ) - k₃) = 1 := factZ_mul_invFact (by omega)
    have f3 : factZ ((c : ℤ) - k₃) * invFact ((c : ℤ) - k₃) = 1 := factZ_mul_invFact (by omega)
    rw [invFact_congr (show (b : ℤ) - k₃ - (k₁ - α - z) = b - k₁ - k₃ + z + α by ring),
      invFact_congr (show (c : ℤ) - k₃ - (K - k₁ - k₃ + z) = c - K + k₁ - z by ring)]
    calc _ = (1 : ℝ) * 1 * 1 * ((-1 : ℝ) ^ z * invFact z * invFact (k₃ - z) * invFact (k₁ - α - z) *
        invFact (c - K + k₁ - z) * invFact (b - k₁ - k₃ + z + α) * invFact (K - k₁ - k₃ + z)) := by
          ring
      _ = (factZ k₃ * invFact k₃) * (factZ ((b : ℤ) - k₃) * invFact ((b : ℤ) - k₃)) *
          (factZ ((c : ℤ) - k₃) * invFact ((c : ℤ) - k₃)) *
          ((-1 : ℝ) ^ z * invFact z * invFact (k₃ - z) * invFact (k₁ - α - z) *
        invFact (c - K + k₁ - z) * invFact (b - k₁ - k₃ + z + α) * invFact (K - k₁ - k₃ + z)) := by
          rw [f1, f2, f3]
      _ = _ := by ring
  · rcases hz with hz | hz
    · rw [invFact_of_neg hz]; ring
    · rw [invFact_of_neg (by omega : (k₃ : ℤ) - z < 0)]; ring

/-- The `x`-form: `racahL` as the alternating binomial sum with factorials. -/
lemma racahL_eq_x_sum (b c k₃ : ℕ) (hb : k₃ ≤ b) (hc : k₃ ≤ c) (k₁ K α : ℤ) :
    (racahL (b - k₃) (c - k₃) k₃ (k₁ - α) (K - k₁ - k₃) : ℝ) =
      ∑ x ∈ Finset.range (k₃ + 1), (-1 : ℝ) ^ x * zbinom k₃ x *
        (factZ ((b : ℤ) - x) * invFact (k₁ - α - x) * invFact (b - k₁ + α)) *
        (factZ ((c : ℤ) - k₃ + x) * invFact (K - k₁ - k₃ + x) * invFact (c - K + k₁)) := by
  rw [racahL, Int.cast_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxk : x ≤ k₃ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  push_cast
  rw [zchoose_eq_zbinom, zchoose_eq_zbinom, natCast_choose_eq,
    show (((b - k₃ + k₃ - x : ℕ) : ℤ)) = (b : ℤ) - x by omega,
    show (((c - k₃ + x : ℕ) : ℤ)) = (c : ℤ) - k₃ + x by omega, zbinom_eq, zbinom_eq, zbinom_eq,
    show (b : ℤ) - x - (k₁ - α - x) = b - k₁ + α by ring,
    show (c : ℤ) - k₃ + x - (K - k₁ - k₃ + x) = c - K + k₁ by ring]
  ring

end PhyslibAlpha.Sl2
