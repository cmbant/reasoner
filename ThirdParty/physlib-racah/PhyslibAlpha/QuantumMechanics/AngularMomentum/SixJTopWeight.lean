/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.ClebschGordanFormula
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.RacahSum

/-!

# Top-weight Clebsch–Gordan coefficients and their products

Racah's formula for a Clebsch–Gordan coefficient has a single term at the top weight, and the
square roots in a product of three such coefficients combine into one constant.

## i. Overview

In doubled units, `cgCoefficient m n k l α β` is the Clebsch–Gordan coefficient
`⟨j₁ m₁ j₂ m₂ | J M⟩` with `j₁ = m/2`, `m₁ = j₁ - α`, `j₂ = n/2`, `m₂ = j₂ - β`,
`J = (m + n)/2 - k` and `M = J - l` (`ClebschGordanCoefficients`). By `cgCoefficient_racah` it is
a product of square roots of factorials times the Racah sum `racahSum m n k α β`. At the top
weight `l = 0`, `β = k - α`, the Racah sum has the single term `z = α` (`racahSum_top`), which
gives the closed form `cgCoefficient_top_racah`.

In the highest-weight reduction of the recoupling coefficient (`SixJProjection`), the three
coefficients `⟨j₁ α j₂ β | j₁₂ 0⟩`, `⟨j₁ α j₂₃ ν | J J⟩` and `⟨j₂ β j₃ k₂ | j₂₃ ν⟩` appear. The
first two are top-weight coefficients, and the third is expanded by Racah's formula. Their
square-root prefactors multiply to a perfect square times a constant (`sqrt_combine`), and
`cg_three_eq` expresses each summand of the sum over `α` as a constant `collapseConst` times
`collapseTerm`, in which the Racah sum of the third coefficient is still unevaluated.

## ii. Key results

- `racahSum_top`, `cgCoefficient_top_racah`: the top-weight coefficients in closed form.
- `collapseConst`, `collapseTerm`: the constant and the summand of the collapsed sum.
- `cg_three_eq`: the product of the three Clebsch–Gordan coefficients as
  `collapseConst * collapseTerm`.

## iii. Table of contents

- A. Top-weight Clebsch–Gordan coefficients
- B. The product of three coefficients

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

## A. Top-weight Clebsch–Gordan coefficients

-/

/-- `racahSum` on the top-weight diagonal `β = k - α` has a single term. -/
lemma racahSum_top {m n k α : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hα : α ≤ k) :
    racahSum m n k α (k - α) =
      (-1) ^ α /
        ((α.factorial * (k - α).factorial * (n - k).factorial * (m - k).factorial : ℕ) : ℝ) := by
  rw [racahSum, Finset.sum_eq_single α]
  · rw [ite_eq_left (by omega)]
    have h1 : n - (k - α) - α = n - k := by omega
    have h2 : m - k + α - α = m - k := by omega
    have h3 : k - α + α - k = 0 := by omega
    rw [h1, h2, h3]
    simp only [Nat.sub_self, Nat.factorial_zero, mul_one]
  · intro z _ hz
    rw [ite_eq_right]
    intro h
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma racahSum_eq_zero {m n k α β : ℕ}
    (h : ∀ z : ℕ, ¬(z ≤ α ∧ α ≤ m - k + z ∧ k ≤ β + z ∧ β + z ≤ n)) :
    racahSum m n k α β = 0 := by
  rw [racahSum]
  exact Finset.sum_eq_zero fun z _ => ite_eq_right_iff.mpr fun hz => absurd hz (h z)

/-- The normalisation `(N + 1)(m - k)!(n - k)! k! / (m + n - k + 1)!`, `N = m + n - 2k`, of
`cgCoefficient_racah`. -/
def cgNorm (m n k : ℕ) : ℝ :=
  (((m + n - 2 * k + 1) * (m - k).factorial * (n - k).factorial * k.factorial : ℕ) : ℝ) /
    ((m + n - k + 1).factorial : ℝ)

lemma cgNorm_nonneg (m n k : ℕ) : 0 ≤ cgNorm m n k := by
  unfold cgNorm
  positivity

/-- `cgCoefficient_racah`, with the normalisation `cgNorm`. -/
lemma cgCoefficient_racah' {m n k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (hα : α ≤ m) (hβ : β ≤ n) (h : α + β = k + l) :
    cgCoefficient m n k l α β =
      Real.sqrt (cgNorm m n k) * Real.sqrt (((m + n - 2 * k - l).factorial * l.factorial *
        α.factorial * (m - α).factorial * β.factorial * (n - β).factorial : ℕ) : ℝ) *
        racahSum m n k α β :=
  cgCoefficient_racah hkm hkn hl hα hβ h

/-- The top-weight Clebsch–Gordan coefficients `⟨m/2, m/2 - α; n/2, n/2 - (k - α) | J J⟩` have a
one-term Racah sum. -/
lemma cgCoefficient_top_racah {m n k α : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hα : α ≤ k) :
    cgCoefficient m n k 0 α (k - α) =
      Real.sqrt (cgNorm m n k) *
        Real.sqrt (((m + n - 2 * k).factorial * α.factorial * (m - α).factorial *
          (k - α).factorial * (n - k + α).factorial : ℕ) : ℝ) *
        ((-1) ^ α /
          ((α.factorial * (k - α).factorial * (n - k).factorial * (m - k).factorial : ℕ) : ℝ)) := by
  rw [cgCoefficient_racah hkm hkn (by omega) (by omega) (by omega) (by omega),
    racahSum_top hkm hkn hα, cgNorm]
  have h : n - (k - α) = n - k + α := by omega
  rw [h, Nat.sub_zero, Nat.factorial_zero, mul_one, mul_comm ((m + n - 2 * k).factorial) _]

/-- The coefficient `⟨m/2, m/2; n/2, n/2 - k | J J⟩` (`α = 0` of `cgCoefficient_top_racah`). -/
lemma cgCoefficient_top_racah_zero {m n k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    cgCoefficient m n k 0 0 k =
      Real.sqrt (cgNorm m n k) *
        Real.sqrt (((m + n - 2 * k).factorial * m.factorial * k.factorial *
          (n - k).factorial : ℕ) : ℝ) *
        (1 / ((k.factorial * (n - k).factorial * (m - k).factorial : ℕ) : ℝ)) := by
  have h := cgCoefficient_top_racah (α := 0) hkm hkn (Nat.zero_le k)
  simp only [Nat.sub_zero, pow_zero, Nat.factorial_zero, mul_one, one_mul, Nat.add_zero] at h
  exact h


/-!

## B. The product of three coefficients

-/

/-- Three products `√P √Q r`, whose `Q`-factors multiply to a constant times a square, combine. -/
lemma sqrt_combine {P₁ P₂ P₃ Q₁ Q₂ Q₃ Q w r₁ r₂ r₃ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hP₃ : 0 ≤ P₃) (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂) (hQ : 0 ≤ Q) (hw : 0 ≤ w)
    (h : Q₁ * Q₂ * Q₃ = Q * w ^ 2) :
    (Real.sqrt P₁ * Real.sqrt Q₁ * r₁) * ((Real.sqrt P₂ * Real.sqrt Q₂ * r₂) *
      (Real.sqrt P₃ * Real.sqrt Q₃ * r₃)) =
        Real.sqrt (P₁ * P₂ * P₃ * Q) * w * (r₁ * r₂ * r₃) := by
  have hq : Real.sqrt Q₁ * Real.sqrt Q₂ * Real.sqrt Q₃ = Real.sqrt Q * w := by
    rw [← Real.sqrt_mul hQ₁, ← Real.sqrt_mul (mul_nonneg hQ₁ hQ₂), h, Real.sqrt_mul hQ,
      Real.sqrt_sq hw]
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hP₁ hP₂) hP₃), Real.sqrt_mul (mul_nonneg hP₁ hP₂),
    Real.sqrt_mul hP₁]
  linear_combination (Real.sqrt P₁ * Real.sqrt P₂ * Real.sqrt P₃ * r₁ * r₂ * r₃) * hq

/-- The constant of the reduction of the recoupling coefficient to a double sum: the square roots
of the three summed Clebsch–Gordan coefficients, collected into one. -/
def collapseConst (a b c K k₁ k₃ : ℕ) : ℝ :=
  Real.sqrt (cgNorm a b k₁ * cgNorm a (b + c - 2 * k₃) (K - k₃) * cgNorm b c k₃ *
      (((a + b - 2 * k₁).factorial * (a + b + c - 2 * K).factorial * (K - k₁).factorial *
        (c - (K - k₁)).factorial : ℕ) : ℝ)) /
    (((b - k₁).factorial * (a - k₁).factorial * (b + c - k₃ - K).factorial *
      (a - (K - k₃)).factorial : ℕ) : ℝ)

/-- The summand of the collapsed sum over `α`, with the `z`-sum still inside `racahSum`. -/
def collapseTerm (a b c K k₁ k₃ α : ℕ) : ℝ :=
  (((a - α).factorial * (b - k₁ + α).factorial * (b + c - k₃ - K + α).factorial : ℕ) : ℝ) /
    (α.factorial : ℝ) * racahSum b c k₃ (k₁ - α) (K - k₁)

/-- Each summand of the sum of products of the three Clebsch–Gordan coefficients is the constant
`collapseConst` times `collapseTerm`. -/
lemma cg_three_eq {a b c K k₁ k₃ α : ℕ} (ha : 0 < a) (hk₁a : k₁ ≤ a) (hk₁b : k₁ ≤ b)
    (hk₃b : k₃ ≤ b) (hk₃c : k₃ ≤ c) (hk₁K : k₁ ≤ K) (hA₃ : K - k₁ ≤ c) (hk₃K : k₃ ≤ K)
    (hB₂ : K - k₃ ≤ a) (hB₃ : K - k₃ ≤ b + c - 2 * k₃) (hα : α ≤ k₁) :
    cgCoefficient a b k₁ 0 α (k₁ - α) *
      (cgCoefficient a (b + c - 2 * k₃) (K - k₃) 0 α (K - k₃ - α) *
        cgCoefficient b c k₃ (K - k₃ - α) (k₁ - α) (K - k₁)) =
      collapseConst a b c K k₁ k₃ * collapseTerm a b c K k₁ k₃ α := by
  by_cases hα4 : α ≤ K - k₃
  · rw [cgCoefficient_top_racah hk₁a hk₁b hα, cgCoefficient_top_racah hB₂ hB₃ hα4,
      cgCoefficient_racah' hk₃b hk₃c (by omega) (by omega) (by omega) (by omega)]
    have e1 : a + (b + c - 2 * k₃) - 2 * (K - k₃) = a + b + c - 2 * K := by omega
    have e2 : b + c - 2 * k₃ - (K - k₃ - α) = b + c - k₃ - K + α := by omega
    have e3 : b + c - 2 * k₃ - (K - k₃) + α = b + c - k₃ - K + α := by omega
    have e4 : b - (k₁ - α) = b - k₁ + α := by omega
    have e5 : b + c - 2 * k₃ - (K - k₃) = b + c - k₃ - K := by omega
    rw [e1, e2, e3, e4, e5, sqrt_combine (cgNorm_nonneg _ _ _) (cgNorm_nonneg _ _ _)
      (cgNorm_nonneg _ _ _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Q := (((a + b - 2 * k₁).factorial * (a + b + c - 2 * K).factorial *
        (K - k₁).factorial * (c - (K - k₁)).factorial : ℕ) : ℝ))
      (w := ((α.factorial * (a - α).factorial *
          (k₁ - α).factorial * (b - k₁ + α).factorial * (K - k₃ - α).factorial *
          (b + c - k₃ - K + α).factorial : ℕ) : ℝ)) ?_]
    · have hsq : (-1 : ℝ) ^ α * (-1) ^ α = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        simp
      rw [collapseConst, collapseTerm, div_mul_div_comm, hsq]
      push_cast
      field_simp
    · push_cast
      ring
  · rw [cgCoefficient_eq_zero_of_ne (by omega) hB₂ hB₃ (by omega), zero_mul, mul_zero,
      collapseTerm, racahSum_eq_zero (fun z hz => by omega), mul_zero, mul_zero]

end PhyslibAlpha.Sl2
