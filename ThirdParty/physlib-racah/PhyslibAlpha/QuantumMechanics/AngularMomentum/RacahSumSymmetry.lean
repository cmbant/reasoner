/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.RacahSum

/-!

# Column symmetries of Racah's expression for the 6j symbol

The expression `racah6j` of Racah's formula is invariant under permutations of the columns of
`{j₁ j₂ j₃; j₄ j₅ j₆}`.

## i. Overview

The 6j symbol is invariant under permutations of its columns (`sixJSym_swap₁₂`, `sixJSym_swap₂₃`
in `SixJSymmetry`). The same invariance of Racah's right-hand side `racah6j` is a statement about
the finite sum `racahSum6` and the four triangle coefficients: exchanging two columns permutes the
four triads, hence the four `Δ²`, and permutes the seven arguments of `racahSum6` among themselves
without changing the summand, because each summand is a product over these arguments.

## ii. Key results

- `triD_swap₁₂`, `triD_swap₂₃`: the triangle coefficient is symmetric in its arguments.
- `racah6j_swap₁₂`, `racah6j_swap₂₃`: invariance under exchanging the first two or the last two
  columns, which generate the permutations of the columns.

## iii. Table of contents

- A. Symmetries of the triangle coefficient
- B. Symmetries of the Racah sum
- C. Symmetries of the right-hand side

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

## A. Symmetries of the triangle coefficient

-/

lemma triCoeff_swap₂₃ (x y z : ℤ) : triCoeff x z y = triCoeff x y z := by
  unfold triCoeff; rw [show x + z + y + 1 = x + y + z + 1 by ring]; ring

lemma triD_swap₁₂ (j₁ j₂ j₃ : ℕ) : triD j₂ j₁ j₃ = triD j₁ j₂ j₃ := by
  unfold triD
  rw [show (((j₂ : ℤ) + j₁ - j₃) / 2) = ((j₁ : ℤ) + j₂ - j₃) / 2 by omega,
    show (((j₂ : ℤ) - j₁ + j₃) / 2) = ((-(j₁ : ℤ) + j₂ + j₃) / 2) by omega,
    show ((-(j₂ : ℤ) + j₁ + j₃) / 2) = (((j₁ : ℤ) - j₂ + j₃) / 2) by omega, triCoeff_swap₂₃]

lemma triD_swap₂₃ (j₁ j₂ j₃ : ℕ) : triD j₁ j₃ j₂ = triD j₁ j₂ j₃ := by
  unfold triD
  rw [show (((j₁ : ℤ) + j₃ - j₂) / 2) = ((j₁ : ℤ) - j₂ + j₃) / 2 by omega,
    show (((j₁ : ℤ) - j₃ + j₂) / 2) = ((j₁ : ℤ) + j₂ - j₃) / 2 by omega,
    show ((-(j₁ : ℤ) + j₃ + j₂) / 2) = ((-(j₁ : ℤ) + j₂ + j₃) / 2) by omega]
  unfold triCoeff
  rw [show ((j₁ : ℤ) - j₂ + j₃) / 2 + ((j₁ : ℤ) + j₂ - j₃) / 2 + (-(j₁ : ℤ) + j₂ + j₃) / 2 + 1 =
    ((j₁ : ℤ) + j₂ - j₃) / 2 + ((j₁ : ℤ) - j₂ + j₃) / 2 + (-(j₁ : ℤ) + j₂ + j₃) / 2 + 1 by ring]
  ring

/-!

## B. Symmetries of the Racah sum

-/

/-- `racahSum6` depends only on the values of its seven arguments. -/
lemma racahSum6_congr {α₁ α₂ α₃ α₄ β₁ β₂ β₃ α₁' α₂' α₃' α₄' β₁' β₂' β₃' : ℤ} (h1 : α₁ = α₁')
    (h2 : α₂ = α₂') (h3 : α₃ = α₃') (h4 : α₄ = α₄') (h5 : β₁ = β₁') (h6 : β₂ = β₂')
    (h7 : β₃ = β₃') :
    racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ = racahSum6 α₁' α₂' α₃' α₄' β₁' β₂' β₃' := by
  subst h1 h2 h3 h4 h5 h6 h7; rfl


/-- Exchanging `α₂ ↔ α₃` and `β₂ ↔ β₃` does not change `racahSum6`. -/
lemma racahSum6_perm₂₃ (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) :
    racahSum6 α₁ α₃ α₂ α₄ β₁ β₃ β₂ = racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ := by
  unfold racahSum6; refine finsum_congr fun t => ?_; ring

/-- Exchanging `α₃ ↔ α₄` and `β₁ ↔ β₃` does not change `racahSum6`. -/
lemma racahSum6_perm₃₄β₁₃ (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) :
    racahSum6 α₁ α₂ α₄ α₃ β₃ β₂ β₁ = racahSum6 α₁ α₂ α₃ α₄ β₁ β₂ β₃ := by
  unfold racahSum6; refine finsum_congr fun t => ?_; ring


/-!

## C. Symmetries of the right-hand side

-/

/-- `racah6j` is invariant under exchanging the first two columns. -/
lemma racah6j_swap₁₂ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racah6j j₂ j₁ j₃ j₅ j₄ j₆ = racah6j j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold racah6j
  rw [triD_swap₁₂ j₄ j₂ j₆, triD_swap₁₂ j₁ j₅ j₆, triD_swap₁₂ j₄ j₅ j₃, triD_swap₁₂ j₁ j₂ j₃,
    show triD j₁ j₂ j₃ * triD j₄ j₂ j₆ * triD j₁ j₅ j₆ * triD j₄ j₅ j₃ =
      triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃ by ring]
  congr 1
  refine Eq.trans ?_ (racahSum6_perm₂₃ _ _ _ _ _ _ _)
  apply racahSum6_congr <;> omega

/-- `racah6j` is invariant under exchanging the last two columns. -/
lemma racah6j_swap₂₃ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racah6j j₁ j₃ j₂ j₄ j₆ j₅ = racah6j j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold racah6j
  rw [triD_swap₂₃ j₁ j₂ j₃, triD_swap₂₃ j₁ j₅ j₆, triD_swap₂₃ j₄ j₂ j₆,
    triD_swap₂₃ j₄ j₅ j₃,
    show triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₅ j₃ * triD j₄ j₂ j₆ =
      triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃ by ring]
  congr 1
  refine Eq.trans ?_ (racahSum6_perm₃₄β₁₃ _ _ _ _ _ _ _)
  apply racahSum6_congr <;> omega

end PhyslibAlpha.Sl2
