/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.RacahEdge
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJEdge

/-!

# Racah's formula for the 6j symbol with a vanishing spin

The operator-defined 6j symbol `sixJ` equals `racah6j` when `j₁ = 0` or `j₃ = 0`.

## i. Overview

All spins are doubled naturals. `sixJ_eq_racah6j` (`SixJRacah`) needs `0 < a` and `0 < c`. For
`a = 0` or `c = 0` the recoupling coefficient is `1` (`recoupling_zero_left`,
`recoupling_zero_right`), so the symbol is `(-1)^(a + b + c - K)` over `√((2j₁₂ + 1)(2j₂₃ + 1))`
(`sixJ_zero_left`, `sixJ_zero_right`). `racah6j_zero_left` and `racah6j_zero_right` evaluate
Racah's formula to the same value; with `a = 0` (so `k₁ = 0` and `K = k₃`) and with `c = 0` (so
`k₃ = 0` and `K = k₁`) this gives `sixJ_eq_racah6j_zero_left` and `sixJ_eq_racah6j_zero_right`,
in the shape of `sixJ_eq_racah6j`.

## ii. Key results

- `sixJ_zero_left`, `sixJ_zero_right`: the 6j symbol for `a = 0`, respectively `c = 0`.
- `sixJ_eq_racah6j_zero_left`, `sixJ_eq_racah6j_zero_right`: `sixJ` is `racah6j` for `a = 0`,
  respectively `c = 0`.

## iii. Table of contents

- A. The 6j symbol with a vanishing spin
- B. Racah's formula for the 6j symbol with a vanishing spin

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

## A. The 6j symbol with a vanishing spin

-/

/-- The 6j symbol for `j₁ = 0`: `(-1)^(b + c - K)` over `√((2j₁₂ + 1)(2j₂₃ + 1))`. -/
lemma sixJ_zero_left {b c K : ℕ} (hab : 0 < 0 + b) (hbc : 0 < b + c)
    {k₁ : Fin (min 0 b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA 0 b c K k₁)
    (hB : ValidB 0 b c K k₃) :
    sixJ hab hbc K k₁ k₃ = (-1) ^ (0 + b + c - K) /
      Real.sqrt (((0 + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) * ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ)) := by
  rw [sixJ, ite_eq_left ⟨hA, hB⟩, recoupling_zero_left hab hbc hA hB, mul_one]

/-- The 6j symbol for `j₃ = 0`: `(-1)^(a + b - K)` over `√((2j₁₂ + 1)(2j₂₃ + 1))`. -/
lemma sixJ_zero_right {a b K : ℕ} (hab : 0 < a + b) (hbc : 0 < b + 0)
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b 0 + 1)} (hA : ValidA a b 0 K k₁)
    (hB : ValidB a b 0 K k₃) :
    sixJ hab hbc K k₁ k₃ = (-1) ^ (a + b + 0 - K) /
      Real.sqrt (((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) * ((b + 0 - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ)) := by
  rw [sixJ, ite_eq_left ⟨hA, hB⟩, recoupling_zero_right hab hbc hA hB, mul_one]

/-!

## B. Racah's formula for the 6j symbol with a vanishing spin

-/

/-- **Racah's formula for the 6j symbol with `j₁ = 0`.** -/
lemma sixJ_eq_racah6j_zero_left {b c K : ℕ} (hab : 0 < 0 + b) (hbc : 0 < b + c)
    {k₁ : Fin (min 0 b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA 0 b c K k₁)
    (hB : ValidB 0 b c K k₃) :
    sixJ hab hbc K k₁ k₃ =
      racah6j 0 b (0 + b - 2 * (k₁ : ℕ)) c (0 + b + c - 2 * K) (b + c - 2 * (k₃ : ℕ)) := by
  have h₁ := k₁.isLt
  have h₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have e₁ : (k₁ : ℕ) = 0 := by omega
  have e₃ : (k₃ : ℕ) = K := by omega
  rw [sixJ_zero_left hab hbc ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩, e₁, e₃,
    show 0 + b - 2 * 0 = b by omega, show 0 + b + c - 2 * K = b + c - 2 * K by omega,
    show 0 + b + c - K = b + c - K by omega, racah6j_zero_left (by omega) (by omega)]

/-- **Racah's formula for the 6j symbol with `j₃ = 0`.** -/
lemma sixJ_eq_racah6j_zero_right {a b K : ℕ} (hab : 0 < a + b) (hbc : 0 < b + 0)
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b 0 + 1)} (hA : ValidA a b 0 K k₁)
    (hB : ValidB a b 0 K k₃) :
    sixJ hab hbc K k₁ k₃ =
      racah6j a b (a + b - 2 * (k₁ : ℕ)) 0 (a + b + 0 - 2 * K) (b + 0 - 2 * (k₃ : ℕ)) := by
  have h₁ := k₁.isLt
  have h₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have e₁ : (k₁ : ℕ) = K := by omega
  have e₃ : (k₃ : ℕ) = 0 := by omega
  rw [sixJ_zero_right hab hbc ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩, e₁, e₃,
    show b + 0 - 2 * 0 = b by omega, show a + b + 0 - 2 * K = a + b - 2 * K by omega,
    show a + b + 0 - K = a + b - K by omega, racah6j_zero_right (by omega) (by omega)]

end PhyslibAlpha.Sl2
