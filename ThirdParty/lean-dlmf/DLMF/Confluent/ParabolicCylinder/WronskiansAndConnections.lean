/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic.Functions

-- PATCH: removed `public import DLMF.Confluent.ParabolicCylinder.EquationAndIntegrals` (upstream file; none of its
-- 13 declarations is used in this file, checked by grep; the import closure is then the vendored Basic files only)
public import DLMF.ParabolicCylinder.Basic.Wronskians

/-!
# Parabolic cylinder functions: Wronskians and connection formulas

This file proves the connection formulas and recurrences for the second solution
`V(a,z) = V(a,0) u₁ + V'(a,0) u₂` (DLMF 12.4.2) and the connection formulas for `U(a, -z)`
(DLMF §§12.2, 12.8). The Wronskians, the connection formula DLMF 12.2.17 and Weber's equation
for `V` are in `DLMF.ParabolicCylinder.Basic.Wronskians`.

## Main results

* `parabolicCylinderU_neg_eq`, `parabolicCylinderV_neg_eq`: the connection formulas DLMF
  12.2.15–12.2.16 for every `a`.
* `parabolicCylinderU_neg_nat_sub_half_neg`, `parabolicCylinderV_nat_add_half_neg`: the parity
  relations DLMF 12.2.13–12.2.14.
* `parabolicCylinderV_eq`: the classical form of `V` in terms of `U(a, ±z)`, away from the poles of
  `Γ(1/2 + a)`.
* `parabolicCylinderV_eq_mul_I`, `parabolicCylinderV_eq_mul_neg_I`: the connection formula DLMF
  12.2.20 for every `a`.
* `parabolicCylinderV_three_term`, `parabolicCylinderV_recurrence_sub`,
  `parabolicCylinderV_recurrence_add`, `parabolicCylinderV_deriv_recurrence`: the recurrences DLMF
  12.8.5–12.8.8.

-/

public section

open Complex Filter MeasureTheory Asymptotics Set

open scoped Real Topology Nat

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### The second solution `V(a,z)` (DLMF 12.2, 12.4.2, 12.8) -/

/-- Duplication formula: `1/Γ(1/2 - a) = 2^{1/2+a} √π / (Γ(1/4 - a/2) Γ(3/4 - a/2))`. -/
theorem recip_Gamma_half_sub (a : ℂ) :
    (Gamma (1 / 2 - a))⁻¹ = (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹ *
      (2 : ℂ) ^ (1 / 2 + a) * (Real.sqrt π : ℂ) := by
  have h := recip_Gamma_half_add (-a)
  rwa [show (1 / 2 + -a : ℂ) = 1 / 2 - a by ring, show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring,
    show (1 / 2 - -a : ℂ) = 1 / 2 + a by ring] at h

/-- `2^x 2^y = 2^z` when `x + y = z`. -/
theorem two_cpow_mul_two_cpow (x y z : ℂ) (h : x + y = z) :
    (2 : ℂ) ^ x * 2 ^ y = 2 ^ z := by
  rw [← Complex.cpow_add _ _ two_ne_zero, h]

/-- **Connection formula** (DLMF 12.2.15), valid for every `a`:
`U(a,-z) = -sin(πa) U(a,z) + π/Γ(1/2 + a) V(a,z)`. -/
@[dlmf 12.2.E15]
theorem parabolicCylinderU_neg_eq (a z : ℂ) :
    parabolicCylinderU a (-z) = -Complex.sin (π * a) * parabolicCylinderU a z + π /
        Gamma (1 / 2 + a) * parabolicCylinderV a z := by
  have hg := (isWeberSolution_parabolicCylinderU a).lincomb (isWeberSolution_parabolicCylinderV a)
      (-Complex.sin (π * a))
    (π / Gamma (1 / 2 + a))
  refine (isWeberSolution_parabolicCylinderU_neg a).eq_of_initial hg ?_ ?_ z
  · simp only [neg_zero]
    rw [parabolicCylinderU_zero', parabolicCylinderV_zero', parabolicCylinderVZero,
        div_eq_mul_inv (π : ℂ) (Gamma (1 / 2 + a)),
      recip_Gamma_half_add, sin_pi_mul_eq_sq]
    have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
    rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
    have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
    have pw : (2 : ℂ) ^ (1 / 2 - a) * 2 ^ (a / 2 + 1 / 4) = 2 * 2 ^ (-(a / 2 + 1 / 4)) := by
      rw [two_cpow_mul_two_cpow _ _ (-(a / 2 + 1 / 4) + 1) (by ring),
        Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]; ring
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 - a)
    linear_combination (-(r * g3p * T * B) * (π * (g1p * g3m) + s)) * q2 +
      (-(r * g3p * s ^ 2)) * pw + (-(r * A * g3p)) * htr
  · simp only [neg_zero]
    rw [parabolicCylinderUDeriv_zero', parabolicCylinderVDeriv_zero', parabolicCylinderVDerivZero,
      div_eq_mul_inv (π : ℂ) (Gamma (1 / 2 + a)), recip_Gamma_half_add, sin_pi_mul_eq_sq]
    have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
    rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
    have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
    have pw : (2 : ℂ) ^ (1 / 2 - a) * 2 ^ (a / 2 + 3 / 4) = 2 * 2 ^ (-(a / 2 - 1 / 4)) := by
      rw [two_cpow_mul_two_cpow _ _ (-(a / 2 - 1 / 4) + 1) (by ring),
        Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]; ring
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 - a)
    linear_combination (-(r * g1p * T * B) * (π * (g1m * g3p) + c)) * q1 +
      (-(r * g1p * c ^ 2)) * pw + (-(r * A * g1p)) * htr

/-- **Connection formula** (DLMF 12.2.16), valid for every `a`:
`V(a,-z) = cos(πa)/Γ(1/2 - a) U(a,z) + sin(πa) V(a,z)`. -/
@[dlmf 12.2.E16]
theorem parabolicCylinderV_neg_eq (a z : ℂ) :
    parabolicCylinderV a (-z) = Complex.cos (π * a) / Gamma (1 / 2 - a) * parabolicCylinderU a z +
      Complex.sin (π * a) * parabolicCylinderV a z := by
  have hg := (isWeberSolution_parabolicCylinderU a).lincomb (isWeberSolution_parabolicCylinderV a)
    (Complex.cos (π * a) / Gamma (1 / 2 - a)) (Complex.sin (π * a))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  refine (isWeberSolution_parabolicCylinderV_neg a).eq_of_initial hg ?_ ?_ z
  · simp only [neg_zero]
    rw [parabolicCylinderU_zero', parabolicCylinderV_zero', parabolicCylinderVZero,
        div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, sin_pi_mul_eq_sq, cos_pi_mul_eq_mul]
    have pw : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-2 * s * c * g1m * g3m * g3p * T * A) * hππ +
      (-2 * s * c * π * g1m * g3m * g3p) * pw + (-2 * s * c * B * g3m) * q1 +
      (B * g3m * (1 - s ^ 2 + c ^ 2)) * q2 + (-s * B * g3m) * htr
  · simp only [neg_zero]
    rw [parabolicCylinderUDeriv_zero', parabolicCylinderVDeriv_zero', parabolicCylinderVDerivZero,
        div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, sin_pi_mul_eq_sq, cos_pi_mul_eq_mul]
    have pw : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (2 * s * c * g1m * g3m * g1p * T * A) * hππ +
      (2 * s * c * π * g1m * g3m * g1p) * pw + (2 * s * c * B * g1m) * q2 +
      (-(B * g1m * (1 + s ^ 2 - c ^ 2))) * q1 + (c * B * g1m) * htr

/-- `cos(nπ) = (-1)^n` for natural `n`. -/
theorem cos_nat_mul_pi' (n : ℕ) : Complex.cos (n * π) = (-1) ^ n := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
    Real.cos_nat_mul_pi]
  push_cast; ring

/-- Parity of `U` at the Hermite parameters (DLMF 12.2.13):
`U(-n - 1/2, -z) = (-1)ⁿ U(-n - 1/2, z)`. -/
@[dlmf 12.2.E13]
theorem parabolicCylinderU_neg_nat_sub_half_neg (n : ℕ) (z : ℂ) :
    parabolicCylinderU (-n - 1 / 2) (-z) = (-1) ^ n * parabolicCylinderU (-n - 1 / 2) z := by
  rw [parabolicCylinderU_neg_eq, show (1 / 2 + (-(n : ℂ) - 1 / 2)) = -(n : ℂ) by ring,
    Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, add_zero,
    show (π : ℂ) * (-(n : ℂ) - 1 / 2) = -(n * π) - π / 2 by ring, Complex.sin_sub_pi_div_two,
    Complex.cos_neg, cos_nat_mul_pi']
  ring

/-- Parity of `V` at the parameters `n + 1/2` (DLMF 12.2.14):
`V(n + 1/2, -z) = (-1)ⁿ V(n + 1/2, z)`. -/
@[dlmf 12.2.E14]
theorem parabolicCylinderV_nat_add_half_neg (n : ℕ) (z : ℂ) :
    parabolicCylinderV (n + 1 / 2) (-z) = (-1) ^ n * parabolicCylinderV (n + 1 / 2) z := by
  rw [parabolicCylinderV_neg_eq, show (1 / 2 - ((n : ℂ) + 1 / 2)) = -(n : ℂ) by ring,
    Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul, zero_add,
    show (π : ℂ) * ((n : ℂ) + 1 / 2) = n * π + π / 2 by ring, Complex.sin_add_pi_div_two,
    cos_nat_mul_pi']

/-- The classical form of `V` (DLMF 12.2.15 solved for `V`):
`V(a,z) = Γ(1/2 + a)/π (sin(πa) U(a,z) + U(a,-z))`, away from the poles of `Γ(1/2 + a)`. -/
theorem parabolicCylinderV_eq {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    parabolicCylinderV a z = Gamma (1 / 2 + a) / π *
        (Complex.sin (π * a) * parabolicCylinderU a z + parabolicCylinderU a (-z)) := by
  have hΓ := Complex.Gamma_ne_zero ha
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [parabolicCylinderU_neg_eq, show Complex.sin (π * a) * parabolicCylinderU a z +
      (-Complex.sin (π * a) * parabolicCylinderU a z + π / Gamma (1 / 2 + a) *
          parabolicCylinderV a z) =
      π / Gamma (1 / 2 + a) * parabolicCylinderV a z by ring, ← mul_assoc, div_mul_div_comm,
    mul_comm (Gamma (1 / 2 + a)) (π : ℂ), div_self (mul_ne_zero hπ0 hΓ), one_mul]

/-- `exp(-iπ(a/2 - 1/4)) = sin(π(1/4 + a/2)) + i cos(π(1/4 + a/2))`. -/
theorem exp_neg_I_pi_quarter (a : ℂ) :
    exp (-I * π * (a / 2 - 1 / 4)) =
      Complex.sin (π * (1 / 4 + a / 2)) + Complex.cos (π * (1 / 4 + a / 2)) * I := by
  rw [show -I * π * (a / 2 - 1 / 4) = (-(π * (1 / 4 + a / 2) - π / 2)) * I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.cos_sub_pi_div_two,
    Complex.sin_sub_pi_div_two]
  ring

/-- `exp(iπ(a/2 - 1/4)) = sin(π(1/4 + a/2)) - i cos(π(1/4 + a/2))`. -/
theorem exp_I_pi_quarter (a : ℂ) :
    exp (I * π * (a / 2 - 1 / 4)) =
      Complex.sin (π * (1 / 4 + a / 2)) - Complex.cos (π * (1 / 4 + a / 2)) * I := by
  rw [show I * π * (a / 2 - 1 / 4) = (π * (1 / 4 + a / 2) - π / 2) * I by ring,
    Complex.exp_mul_I, Complex.cos_sub_pi_div_two, Complex.sin_sub_pi_div_two]
  ring

/-- **Connection formula** (DLMF 12.2.20, upper signs), valid for every `a`:
`V(a,z) = -i/Γ(1/2 - a) U(a,z) + √(2/π) e^{-iπ(a/2 - 1/4)} U(-a, iz)`. -/
@[dlmf 12.2.E20]
theorem parabolicCylinderV_eq_mul_I (a z : ℂ) :
    parabolicCylinderV a z = -I / Gamma (1 / 2 - a) * parabolicCylinderU a z +
      (Real.sqrt (2 / π) : ℂ) * exp (-I * π * (a / 2 - 1 / 4)) *
          parabolicCylinderU (-a) (I * z) := by
  have hg := (isWeberSolution_parabolicCylinderU a).lincomb
      (isWeberSolution_parabolicCylinderU_mul_I a) (-I / Gamma (1 / 2 - a))
    ((Real.sqrt (2 / π) : ℂ) * exp (-I * π * (a / 2 - 1 / 4)))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  refine (isWeberSolution_parabolicCylinderV a).eq_of_initial hg ?_ ?_ z
  · simp only [mul_zero]
    rw [parabolicCylinderV_zero', parabolicCylinderVZero, parabolicCylinderU_zero' a,
        parabolicCylinderU_zero' (-a), div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, exp_neg_I_pi_quarter, show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (I * g1m * g3m * T * A * g3p) * hππ + (I * g1m * g3m * g3p * π) * pwA +
      (I * g3m * B) * q1 + (-(s + c * I) * A2 * g3m) * hR + (-(s + c * I) * g3m) * pwB +
      (B * g3m) * q2
  · simp only [mul_zero]
    rw [parabolicCylinderVDeriv_zero', parabolicCylinderVDerivZero, parabolicCylinderUDeriv_zero' a,
        parabolicCylinderUDeriv_zero' (-a),
      div_eq_mul_inv _ (Gamma (1 / 2 - a)), recip_Gamma_half_sub, exp_neg_I_pi_quarter,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-I * g1m * g3m * T * A * g1p) * hππ + (-I * g1m * g3m * g1p * π) * pwA +
      (-I * g1m * B) * q2 + ((s + c * I) * I * A2 * g1m) * hR + ((s + c * I) * I * g1m) * pwB +
      (c * B * g1m) * Complex.I_sq + (B * g1m) * q1

/-- **Connection formula** (DLMF 12.2.20, lower signs), valid for every `a`:
`V(a,z) = i/Γ(1/2 - a) U(a,z) + √(2/π) e^{iπ(a/2 - 1/4)} U(-a, -iz)`. -/
@[dlmf 12.2.E20]
theorem parabolicCylinderV_eq_mul_neg_I (a z : ℂ) :
    parabolicCylinderV a z = I / Gamma (1 / 2 - a) * parabolicCylinderU a z +
      (Real.sqrt (2 / π) : ℂ) * exp (I * π * (a / 2 - 1 / 4)) *
          parabolicCylinderU (-a) (-I * z) := by
  have hg := (isWeberSolution_parabolicCylinderU a).lincomb
      (isWeberSolution_parabolicCylinderU_mul_neg_I a) (I / Gamma (1 / 2 - a))
    ((Real.sqrt (2 / π) : ℂ) * exp (I * π * (a / 2 - 1 / 4)))
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  refine (isWeberSolution_parabolicCylinderV a).eq_of_initial hg ?_ ?_ z
  · simp only [mul_zero]
    rw [parabolicCylinderV_zero', parabolicCylinderVZero, parabolicCylinderU_zero' a,
        parabolicCylinderU_zero' (-a), div_eq_mul_inv _ (Gamma (1 / 2 - a)),
      recip_Gamma_half_sub, exp_I_pi_quarter, show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 + 1 / 4)) = 2 ^ (a / 2 + 1 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 + 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 + 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 1 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (-I * g1m * g3m * T * A * g3p) * hππ + (-I * g1m * g3m * g3p * π) * pwA +
      (-I * g3m * B) * q1 + (-(s - c * I) * A2 * g3m) * hR + (-(s - c * I) * g3m) * pwB +
      (B * g3m) * q2
  · simp only [mul_zero]
    rw [parabolicCylinderVDeriv_zero', parabolicCylinderVDerivZero, parabolicCylinderUDeriv_zero' a,
        parabolicCylinderUDeriv_zero' (-a),
      div_eq_mul_inv _ (Gamma (1 / 2 - a)), recip_Gamma_half_sub, exp_I_pi_quarter,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have pwA : (2 : ℂ) ^ (1 / 2 + a) * 2 ^ (-(a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) :=
      two_cpow_mul_two_cpow _ _ _ (by ring)
    have pwB : (Real.sqrt 2 : ℂ) * 2 ^ (-(-a / 2 - 1 / 4)) = 2 ^ (a / 2 + 3 / 4) := by
      rw [← two_cpow_half]; exact two_cpow_mul_two_cpow _ _ _ (by ring)
    set g1m := (Gamma (1 / 4 - a / 2))⁻¹
    set g3m := (Gamma (3 / 4 - a / 2))⁻¹
    set g1p := (Gamma (1 / 4 + a / 2))⁻¹
    set g3p := (Gamma (3 / 4 + a / 2))⁻¹
    set c := Complex.cos (π * (1 / 4 + a / 2))
    set s := Complex.sin (π * (1 / 4 + a / 2))
    set r := (Real.sqrt π : ℂ)
    set A := (2 : ℂ) ^ (-(a / 2 - 1 / 4))
    set A2 := (2 : ℂ) ^ (-(-a / 2 - 1 / 4))
    set B := (2 : ℂ) ^ (a / 2 + 3 / 4)
    set T := (2 : ℂ) ^ (1 / 2 + a)
    linear_combination (I * g1m * g3m * T * A * g1p) * hππ + (I * g1m * g3m * g1p * π) * pwA +
      (I * g1m * B) * q2 + (-(s - c * I) * I * A2 * g1m) * hR + (-(s - c * I) * I * g1m) * pwB +
      (c * B * g1m) * Complex.I_sq + (B * g1m) * q1

/-- DLMF 12.8.7: `V'(a,z) + (z/2) V(a,z) - V(a+1,z) = 0`. -/
@[dlmf 12.8.E7]
theorem parabolicCylinderV_recurrence_add (a z : ℂ) :
    deriv (parabolicCylinderV a) z + z / 2 * parabolicCylinderV a z -
        parabolicCylinderV (a + 1) z = 0 := by
  rw [deriv_parabolicCylinderV]
  have hs : IsWeberSolution (a + 1)
      (fun w => parabolicCylinderVDeriv a w + w / 2 * parabolicCylinderV a w -
      parabolicCylinderV (a + 1) w)
      (fun w => (w ^ 2 / 4 + a) * parabolicCylinderV a w + 1 / 2 * parabolicCylinderV a w + w / 2 *
          parabolicCylinderVDeriv a w -
        parabolicCylinderVDeriv (a + 1) w) := fun w => by
    have hU := hasDerivAt_parabolicCylinderV a w
    have hU' := hasDerivAt_parabolicCylinderVDeriv a w
    have hV := hasDerivAt_parabolicCylinderV (a + 1) w
    have hV' := hasDerivAt_parabolicCylinderVDeriv (a + 1) w
    refine ⟨(hU'.add (((hasDerivAt_id w).div_const 2).mul hU)).sub hV |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).add
        (hU.const_mul (1 / 2))).add (((hasDerivAt_id w).div_const 2).mul hU')).sub hV'
        |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : parabolicCylinderVDeriv a 0 + 0 / 2 * parabolicCylinderV a 0 -
      parabolicCylinderV (a + 1) 0 = 0 := by
    simp only [parabolicCylinderVDeriv_zero', parabolicCylinderV_zero', parabolicCylinderVZero,
        parabolicCylinderVDerivZero]
    rw [show 3 / 4 - (a + 1) / 2 = 1 / 4 - a / 2 by ring,
      show 1 / 4 + (a + 1) / 2 = 3 / 4 + a / 2 by ring,
      show (a + 1) / 2 + 1 / 4 = a / 2 + 3 / 4 by ring]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * parabolicCylinderV a 0 + 1 / 2 * parabolicCylinderV a 0 + 0 /
      2 * parabolicCylinderVDeriv a 0 -
      parabolicCylinderVDeriv (a + 1) 0 = 0 := by
    have hgA := mul_recip_Gamma_add_one' (-1 / 4 - a / 2)
    rw [show -1 / 4 - a / 2 + 1 = 3 / 4 - a / 2 by ring] at hgA
    have hgB := mul_recip_Gamma_add_one' (1 / 4 + a / 2)
    rw [show 1 / 4 + a / 2 + 1 = 5 / 4 + a / 2 by ring] at hgB
    have pw : (2 : ℂ) ^ (a / 2 + 5 / 4) = 2 * 2 ^ (a / 2 + 1 / 4) := by
      rw [show a / 2 + 5 / 4 = (a / 2 + 1 / 4) + 1 by ring, Complex.cpow_add _ _ two_ne_zero,
        Complex.cpow_one]; ring
    simp only [parabolicCylinderVDeriv_zero', parabolicCylinderV_zero', parabolicCylinderVZero,
        parabolicCylinderVDerivZero]
    rw [show 1 / 4 - (a + 1) / 2 = -1 / 4 - a / 2 by ring,
      show 3 / 4 + (a + 1) / 2 = 5 / 4 + a / 2 by ring,
      show (a + 1) / 2 + 3 / 4 = a / 2 + 5 / 4 by ring, ← hgA, ← hgB, pw]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.6: `V'(a,z) - (z/2) V(a,z) - (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E6]
theorem parabolicCylinderV_recurrence_sub (a z : ℂ) :
    deriv (parabolicCylinderV a) z - z / 2 * parabolicCylinderV a z - (a - 1 / 2) *
        parabolicCylinderV (a - 1) z = 0 := by
  rw [deriv_parabolicCylinderV]
  have hs : IsWeberSolution (a - 1)
      (fun w => parabolicCylinderVDeriv a w - w / 2 * parabolicCylinderV a w - (a - 1 / 2) *
          parabolicCylinderV (a - 1) w)
      (fun w => (w ^ 2 / 4 + a) * parabolicCylinderV a w - 1 / 2 * parabolicCylinderV a w - w / 2 *
          parabolicCylinderVDeriv a w -
        (a - 1 / 2) * parabolicCylinderVDeriv (a - 1) w) := fun w => by
    have hU := hasDerivAt_parabolicCylinderV a w
    have hU' := hasDerivAt_parabolicCylinderVDeriv a w
    have hV := hasDerivAt_parabolicCylinderV (a - 1) w
    have hV' := hasDerivAt_parabolicCylinderVDeriv (a - 1) w
    refine ⟨(hU'.sub (((hasDerivAt_id w).div_const 2).mul hU)).sub (hV.const_mul (a - 1 / 2))
      |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).sub
        (hU.const_mul (1 / 2))).sub (((hasDerivAt_id w).div_const 2).mul hU')).sub
        (hV'.const_mul (a - 1 / 2)) |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : parabolicCylinderVDeriv a 0 - 0 / 2 * parabolicCylinderV a 0 - (a - 1 / 2) *
      parabolicCylinderV (a - 1) 0 = 0 := by
    have hgA := mul_recip_Gamma_add_one' (1 / 4 - a / 2)
    rw [show 1 / 4 - a / 2 + 1 = 5 / 4 - a / 2 by ring] at hgA
    have hgB := mul_recip_Gamma_add_one' (a / 2 - 1 / 4)
    rw [show a / 2 - 1 / 4 + 1 = 3 / 4 + a / 2 by ring] at hgB
    have pw : (2 : ℂ) ^ (a / 2 + 3 / 4) = 2 * 2 ^ (a / 2 - 1 / 4) := by
      rw [show a / 2 + 3 / 4 = (a / 2 - 1 / 4) + 1 by ring, Complex.cpow_add _ _ two_ne_zero,
        Complex.cpow_one]; ring
    simp only [parabolicCylinderVDeriv_zero', parabolicCylinderV_zero', parabolicCylinderVZero,
        parabolicCylinderVDerivZero]
    rw [show 3 / 4 - (a - 1) / 2 = 5 / 4 - a / 2 by ring,
      show 1 / 4 + (a - 1) / 2 = a / 2 - 1 / 4 by ring,
      show (a - 1) / 2 + 1 / 4 = a / 2 - 1 / 4 by ring, ← hgA, ← hgB, pw]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * parabolicCylinderV a 0 - 1 / 2 * parabolicCylinderV a 0 - 0 /
      2 * parabolicCylinderVDeriv a 0 -
      (a - 1 / 2) * parabolicCylinderVDeriv (a - 1) 0 = 0 := by
    simp only [parabolicCylinderVDeriv_zero', parabolicCylinderV_zero', parabolicCylinderVZero,
        parabolicCylinderVDerivZero]
    rw [show 1 / 4 - (a - 1) / 2 = 3 / 4 - a / 2 by ring,
      show 3 / 4 + (a - 1) / 2 = 1 / 4 + a / 2 by ring,
      show (a - 1) / 2 + 3 / 4 = a / 2 + 1 / 4 by ring]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.5: `z V(a,z) - V(a+1,z) + (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E5]
theorem parabolicCylinderV_three_term (a z : ℂ) :
    z * parabolicCylinderV a z - parabolicCylinderV (a + 1) z + (a - 1 / 2) *
        parabolicCylinderV (a - 1) z = 0 := by
  linear_combination parabolicCylinderV_recurrence_add a z - parabolicCylinderV_recurrence_sub a z

/-- DLMF 12.8.8: `2 V'(a,z) - V(a+1,z) - (a - 1/2) V(a-1,z) = 0`. -/
@[dlmf 12.8.E8]
theorem parabolicCylinderV_deriv_recurrence (a z : ℂ) :
    2 * deriv (parabolicCylinderV a) z - parabolicCylinderV (a + 1) z - (a - 1 / 2) *
        parabolicCylinderV (a - 1) z = 0 := by
  linear_combination parabolicCylinderV_recurrence_add a z + parabolicCylinderV_recurrence_sub a z

end DLMF.Confluent

end
end
