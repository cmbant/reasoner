/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Wigner3j

/-!

# Racah's single-sum expression for the 6j symbol

The explicit expression `racah6j` of Racah's closed formula for the 6j symbol, as a product of four
triangle coefficients `Δ` and a single alternating sum, in the doubled units of `SixJ`.

## i. Overview

All spins are doubled naturals, as in `SixJ` and `SixJSymmetry`. Racah's formula (DLMF 34.4.2) is

`{j₁ j₂ j₃; j₄ j₅ j₆} = Δ(j₁ j₂ j₃) Δ(j₁ j₅ j₆) Δ(j₄ j₂ j₆) Δ(j₄ j₅ j₃) ·
  Σ_t (-1)^t (t + 1)! / ((t - α₁)! (t - α₂)! (t - α₃)! (t - α₄)! (β₁ - t)! (β₂ - t)! (β₃ - t)!)`

with the half-perimeters `α₁ = j₁ + j₂ + j₃`, `α₂ = j₁ + j₅ + j₆`, `α₃ = j₄ + j₂ + j₆`,
`α₄ = j₄ + j₅ + j₃`, the quadrilateral sums `β₁ = j₁ + j₂ + j₄ + j₅`, `β₂ = j₂ + j₃ + j₅ + j₆`,
`β₃ = j₃ + j₁ + j₆ + j₄`, and
`Δ(j₁ j₂ j₃)² = (j₁ + j₂ - j₃)! (j₁ - j₂ + j₃)! (-j₁ + j₂ + j₃)! / (j₁ + j₂ + j₃ + 1)!`.

Here the sum and the factorials are zero-extended over `ℤ`: `factZ n = n!` for `n ≥ 0` and `0` for
`n < 0`, and `invFact n = 1 / n!` for `n ≥ 0` and `0` for `n < 0` (`Wigner3j`), so that the sum
runs over exactly the `t` for which all seven factorial arguments are nonnegative. The unnormalised
sum is `racahSum6`, the squared triangle coefficient is `triCoeff` and `racah6j` is the full
right-hand side, in doubled units (a half-integer `x / 2` enters only through the integers
`(x + y - z) / 2`, which are exact for admissible triads).

That `racah6j` is the 6j symbol is proved in later files; this file only has the definitions.

## ii. Key results

- `factZ`, `factZ_mul_invFact`: the zero-extended factorial and its relation to `invFact`.
- `triCoeff`: `Δ²` of a triad, zero unless the three arguments are nonnegative.
- `racahSum6`: Racah's alternating sum.
- `triD`, `racah6j`: the right-hand side of Racah's formula in doubled units.

## iii. Table of contents

- A. The zero-extended factorial
- B. Racah's sum and the right-hand side

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).
- NIST Digital Library of Mathematical Functions, §34.4, https://dlmf.nist.gov/34.4.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

## A. The zero-extended factorial

-/

/-- `n!` for `n ≥ 0` and `0` for `n < 0`. -/
def factZ (u : ℤ) : ℝ := if 0 ≤ u then ((u.toNat.factorial : ℝ)) else 0

lemma factZ_natCast (n : ℕ) : factZ n = (n.factorial : ℝ) := by simp [factZ]

lemma factZ_eq_factorial {u : ℤ} {t : ℕ} (h : u = t) : factZ u = (t.factorial : ℝ) := by
  rw [h, factZ_natCast]

lemma factZ_of_neg {u : ℤ} (h : u < 0) : factZ u = 0 := by
  rw [factZ, ite_eq_right (not_le.mpr h)]

lemma factZ_ne_zero {u : ℤ} (h : 0 ≤ u) : factZ u ≠ 0 := by
  rw [factZ, ite_eq_left h]; exact_mod_cast Nat.factorial_ne_zero _

/-- `factZ` and `invFact` are inverse to each other on nonnegative integers. -/
lemma factZ_mul_invFact {u : ℤ} (h : 0 ≤ u) : factZ u * invFact u = 1 := by
  rw [factZ, invFact, ite_eq_left h, ite_eq_left h]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _)

lemma invFact_eq_inv {u : ℤ} (h : 0 ≤ u) : invFact u = (factZ u)⁻¹ := by
  rw [factZ, invFact, ite_eq_left h, ite_eq_left h]

/-!

## B. Racah's sum and the right-hand side

-/


/-- The square of Racah's `Δ`, `x! y! z! / (x + y + z + 1)!`, where `x, y, z` are the three
integers `j₁ + j₂ - j₃`, `j₁ - j₂ + j₃`, `-j₁ + j₂ + j₃` of a triad (zero unless all are `≥ 0`). -/
def triCoeff (x y z : ℤ) : ℝ := factZ x * factZ y * factZ z * invFact (x + y + z + 1)

/-- Racah's sum `Σ_t (-1)^t (t + 1)! / ∏ (t - αᵢ)! ∏ (βⱼ - t)!`, over the `t` for which all seven
arguments are nonnegative. -/
def racahSum6 (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) : ℝ :=
  ∑ᶠ t : ℤ, (-1 : ℝ) ^ t * factZ (t + 1) *
    (invFact (t - α₁) * invFact (t - α₂) * invFact (t - α₃) * invFact (t - α₄) *
      (invFact (β₁ - t) * invFact (β₂ - t) * invFact (β₃ - t)))

/-- `Δ²` of the triad `(j₁ j₂ j₃)` in doubled units (a half-integer `x/2` only enters through the
integers `(x + y - z)/2`, which are exact for even perimeter). -/
def triD (j₁ j₂ j₃ : ℕ) : ℝ :=
  triCoeff (((j₁ : ℤ) + j₂ - j₃) / 2) (((j₁ : ℤ) - j₂ + j₃) / 2) ((-(j₁ : ℤ) + j₂ + j₃) / 2)

/-- Racah's right-hand side for `{j₁ j₂ j₃; j₄ j₅ j₆}` in doubled units. -/
def racah6j (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  Real.sqrt (triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃) *
    racahSum6 (((j₁ : ℤ) + j₂ + j₃) / 2) (((j₁ : ℤ) + j₅ + j₆) / 2) (((j₄ : ℤ) + j₂ + j₆) / 2)
      (((j₄ : ℤ) + j₅ + j₃) / 2) (((j₁ : ℤ) + j₂ + j₄ + j₅) / 2) (((j₂ : ℤ) + j₃ + j₅ + j₆) / 2)
      (((j₃ : ℤ) + j₁ + j₆ + j₄) / 2)

end PhyslibAlpha.Sl2
