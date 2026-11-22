/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic.WeberEquation

/-!
# Parabolic cylinder functions: Wronskians and the second solution (DLMF §12.2)

The Wronskians of Weber's function `U(a,z)` with its rotations, the connection formula
DLMF 12.2.17, and Weber's equation, initial values and Wronskian of the second solution
`V(a,z) = V(a,0) u₁ + V'(a,0) u₂` (DLMF 12.4.2), which is entire in `a` and `z`.

## Main results

* `parabolicCylinderU_wronskian_neg`: `𝒲{U(a,z), U(a,-z)} = √(2π)/Γ(1/2 + a)` (DLMF 12.2.11).
* `parabolicCylinderU_wronskian_mul_I`, `parabolicCylinderU_wronskian_mul_neg_I`: the Wronskians
  DLMF 12.2.12.
* `parabolicCylinderU_connection_mul_I`, `parabolicCylinderU_connection_mul_neg_I`: the connection
  formula DLMF 12.2.17.
* `hasDerivAt_parabolicCylinderVDeriv`, `isWeberSolution_parabolicCylinderV`: Weber's equation for
  `V` (DLMF 12.2.2).
* `parabolicCylinderV_zero`, `parabolicCylinderVDeriv_zero`: the initial values of `V` (DLMF 12.2.8,
  12.2.9).
* `parabolicCylinderV_wronskian`: `𝒲{U, V} = √(2/π)` (DLMF 12.2.10).

## Implementation notes

The upper-sign Wronskian in DLMF 12.2.12 is proved as printed in the DLMF. The connection
formulas DLMF 12.2.15, 12.2.16, 12.2.20, the parity relations and the recurrences of `V` are in
`DLMF.Confluent.ParabolicCylinder.WronskiansAndConnections`.
-/

public section

open Complex Filter
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The derivative of `w ↦ U(a,-w)` is `-U'(a,-z)`. -/
theorem hasDerivAt_parabolicCylinderU_neg (a z : ℂ) :
    HasDerivAt (fun w => parabolicCylinderU a (-w)) (-parabolicCylinderUDeriv a (-z)) z := by
  have h := (hasDerivAt_parabolicCylinderU a (-z)).comp z (hasDerivAt_neg z)
  exact h.congr_deriv (by ring)

/-- The derivative of `w ↦ U(b, iw)` is `i U'(b, iz)`. -/
theorem hasDerivAt_parabolicCylinderU_mul_I (b z : ℂ) :
    HasDerivAt (fun w => parabolicCylinderU b (I * w))
        (I * parabolicCylinderUDeriv b (I * z)) z := by
  have h := (hasDerivAt_parabolicCylinderU b (I * z)).comp z ((hasDerivAt_id z).const_mul I)
  exact h.congr_deriv (by ring)

/-- The derivative of `w ↦ U(b, -iw)` is `-i U'(b, -iz)`. -/
theorem hasDerivAt_parabolicCylinderU_mul_neg_I (b z : ℂ) :
    HasDerivAt (fun w => parabolicCylinderU b (-I * w))
        (-I * parabolicCylinderUDeriv b (-I * z)) z := by
  have h := (hasDerivAt_parabolicCylinderU b (-I * z)).comp z ((hasDerivAt_id z).const_mul (-I))
  exact h.congr_deriv (by ring)

/-- `U(a,-z)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSolution_parabolicCylinderU_neg (a : ℂ) :
    IsWeberSolution a (fun w => parabolicCylinderU a (-w))
        (fun w => -parabolicCylinderUDeriv a (-w)) := fun z => by
  refine ⟨hasDerivAt_parabolicCylinderU_neg a z, ?_⟩
  have h := ((hasDerivAt_parabolicCylinderUDeriv a (-z)).comp z (hasDerivAt_neg z)).neg
  exact h.congr_deriv (by ring)

/-- `U(-a, iz)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSolution_parabolicCylinderU_mul_I (a : ℂ) :
    IsWeberSolution a (fun w => parabolicCylinderU (-a) (I * w))
        (fun w => I * parabolicCylinderUDeriv (-a) (I * w)) :=
  fun z => by
  refine ⟨hasDerivAt_parabolicCylinderU_mul_I (-a) z, ?_⟩
  have h := ((hasDerivAt_parabolicCylinderUDeriv (-a) (I * z)).comp z
    ((hasDerivAt_id z).const_mul I)).const_mul I
  have hI4 : I ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  refine h.congr_deriv ?_
  ring_nf
  simp only [hI4, Complex.I_sq]
  ring

/-- `U(-a, -iz)` solves Weber's equation `w'' = (z²/4 + a) w`. -/
theorem isWeberSolution_parabolicCylinderU_mul_neg_I (a : ℂ) :
    IsWeberSolution a (fun w => parabolicCylinderU (-a) (-I * w))
        (fun w => -I * parabolicCylinderUDeriv (-a) (-I * w)) :=
  fun z => by
  refine ⟨hasDerivAt_parabolicCylinderU_mul_neg_I (-a) z, ?_⟩
  have h := ((hasDerivAt_parabolicCylinderUDeriv (-a) (-I * z)).comp z
    ((hasDerivAt_id z).const_mul (-I))).const_mul (-I)
  have hI4 : I ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  refine h.congr_deriv ?_
  ring_nf
  simp only [hI4, Complex.I_sq]
  ring

/-- **Wronskian** (DLMF 12.2.11): `𝒲{U(a,z), U(a,-z)} = √(2π)/Γ(1/2 + a)`. -/
@[dlmf 12.2.E11]
theorem parabolicCylinderU_wronskian_neg (a z : ℂ) :
    parabolicCylinderU a z * deriv (fun w => parabolicCylinderU a (-w)) z -
        deriv (parabolicCylinderU a) z * parabolicCylinderU a (-z) =
      (Real.sqrt (2 * π) : ℂ) / Gamma (1 / 2 + a) := by
  rw [(hasDerivAt_parabolicCylinderU_neg a z).deriv, deriv_parabolicCylinderU]
  have hW := (isWeberSolution_parabolicCylinderU a).wronskian_eq
      (isWeberSolution_parabolicCylinderU_neg a) z
  simp only [neg_zero] at hW
  rw [hW, parabolicCylinderU_zero', parabolicCylinderUDeriv_zero']
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hinv : (Gamma (3 / 4 + a / 2))⁻¹ * (Gamma (1 / 4 + a / 2))⁻¹ =
      (Gamma (1 / 2 + a))⁻¹ * ((2 : ℂ) ^ (1 / 2 - a))⁻¹ * (Real.sqrt π : ℂ)⁻¹ := by
    rw [← mul_inv, mul_comm, hd, mul_inv, mul_inv]
  have hP : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4)) * (Real.sqrt 2 : ℂ) =
      2 ^ (1 / 2 - a) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero,
      ← Complex.cpow_add _ _ two_ne_zero]
    ring_nf
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have h2π : (Real.sqrt (2 * π) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h22 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have e : (Real.sqrt π : ℂ) * 2 ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
        -(-((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹)) -
      -((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹) *
        ((Real.sqrt π : ℂ) * 2 ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹) =
      2 * ((Real.sqrt π : ℂ) * (Real.sqrt π : ℂ)) *
        ((2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4))) *
        ((Gamma (3 / 4 + a / 2))⁻¹ * (Gamma (1 / 4 + a / 2))⁻¹) := by ring
  rw [e, hinv, h2π, div_eq_mul_inv ((Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ))]
  generalize (Gamma (1 / 2 + a))⁻¹ = A
  generalize hQ : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(a / 2 - 1 / 4)) = Q at hP
  generalize (2 : ℂ) ^ (1 / 2 - a) = T at hP hT
  rw [← hP]
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h22; norm_num at h22
  have hQ0 : Q ≠ 0 := by rintro rfl; rw [zero_mul] at hP; exact hT hP.symm
  field_simp
  linear_combination (-A) * h22

/-- Euler's reflection formula for reciprocals, valid for every complex `s`. -/
theorem pi_mul_recip_Gamma_mul_recip_Gamma (s : ℂ) :
    (π : ℂ) * ((Gamma s)⁻¹ * (Gamma (1 - s))⁻¹) = Complex.sin (π * s) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_inv, Complex.Gamma_mul_Gamma_one_sub, inv_div]
  field_simp

/-- **Wronskians** (DLMF 12.2.12, upper signs):
`𝒲{U(a,z), U(-a,iz)} = -i e^{iπ(a/2 + 1/4)}`, as printed in the DLMF. -/
@[dlmf 12.2.E12]
theorem parabolicCylinderU_wronskian_mul_I (a z : ℂ) :
    parabolicCylinderU a z * deriv (fun w => parabolicCylinderU (-a) (I * w)) z -
        deriv (parabolicCylinderU a) z * parabolicCylinderU (-a) (I * z) =
      -I * exp (I * π * (a / 2 + 1 / 4)) := by
  rw [(hasDerivAt_parabolicCylinderU_mul_I (-a) z).deriv, deriv_parabolicCylinderU]
  have hW := (isWeberSolution_parabolicCylinderU a).wronskian_eq
      (isWeberSolution_parabolicCylinderU_mul_I a) z
  simp only [mul_zero] at hW
  rw [hW, parabolicCylinderU_zero' a, parabolicCylinderUDeriv_zero' (-a),
      parabolicCylinderUDeriv_zero' a, parabolicCylinderU_zero' (-a),
    show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring,
    show (π : ℂ) * (1 / 4 + a / 2) = π * (a / 2 + 1 / 4) by ring] at q2
  have hc : Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (a / 2 + 1 / 4)) := by
    rw [← Complex.sin_pi_div_two_sub]; ring_nf
  have hexp : exp (I * π * (a / 2 + 1 / 4)) =
      Complex.cos (π * (a / 2 + 1 / 4)) + Complex.sin (π * (a / 2 + 1 / 4)) * I := by
    rw [← Complex.exp_mul_I]; ring_nf
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 + 1 / 4) + -(-a / 2 - 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 - 1 / 4) + -(-a / 2 + 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hexp]
  set X1 := (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4))
  set X2 := (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4))
  set Y1 := (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹
  set Y2 := (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹
  linear_combination (-I * X1 * Y1 + X2 * Y2) * hππ - I * π * Y1 * p1 - I * q1 - I * hc +
    π * Y2 * p2 + q2 + Complex.sin (π * (a / 2 + 1 / 4)) * Complex.I_sq

/-- **Wronskians** (DLMF 12.2.12, lower signs):
`𝒲{U(a,z), U(-a,-iz)} = i e^{-iπ(a/2 + 1/4)}`. -/
@[dlmf 12.2.E12]
theorem parabolicCylinderU_wronskian_mul_neg_I (a z : ℂ) :
    parabolicCylinderU a z * deriv (fun w => parabolicCylinderU (-a) (-I * w)) z -
        deriv (parabolicCylinderU a) z * parabolicCylinderU (-a) (-I * z) =
      I * exp (-I * π * (a / 2 + 1 / 4)) := by
  rw [(hasDerivAt_parabolicCylinderU_mul_neg_I (-a) z).deriv, deriv_parabolicCylinderU]
  have hW := (isWeberSolution_parabolicCylinderU a).wronskian_eq
      (isWeberSolution_parabolicCylinderU_mul_neg_I a) z
  simp only [mul_zero] at hW
  rw [hW, parabolicCylinderU_zero' a, parabolicCylinderUDeriv_zero' (-a),
      parabolicCylinderUDeriv_zero' a, parabolicCylinderU_zero' (-a),
    show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring,
    show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring,
    show (π : ℂ) * (1 / 4 + a / 2) = π * (a / 2 + 1 / 4) by ring] at q2
  have hc : Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (a / 2 + 1 / 4)) := by
    rw [← Complex.sin_pi_div_two_sub]; ring_nf
  have hexp : exp (-I * π * (a / 2 + 1 / 4)) =
      Complex.cos (π * (a / 2 + 1 / 4)) - Complex.sin (π * (a / 2 + 1 / 4)) * I := by
    rw [show -I * π * (a / 2 + 1 / 4) = (-(π * (a / 2 + 1 / 4))) * I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 + 1 / 4) + -(-a / 2 - 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4)) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show -(a / 2 - 1 / 4) + -(-a / 2 + 1 / 4) = 0 by ring,
      Complex.cpow_zero]
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hexp]
  set X1 := (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (-(-a / 2 - 1 / 4))
  set X2 := (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (-(-a / 2 + 1 / 4))
  set Y1 := (Gamma (1 / 4 - a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹
  set Y2 := (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 - a / 2))⁻¹
  linear_combination (I * X1 * Y1 + X2 * Y2) * hππ + I * π * Y1 * p1 + I * q1 + I * hc +
    π * Y2 * p2 + q2 + Complex.sin (π * (a / 2 + 1 / 4)) * Complex.I_sq

/-- Linear combinations of solutions of Weber's equation are solutions. -/
theorem IsWeberSolution.lincomb {a : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsWeberSolution a f f')
    (hg : IsWeberSolution a g g') (c₁ c₂ : ℂ) :
    IsWeberSolution a (fun w => c₁ * f w + c₂ * g w) (fun w => c₁ * f' w + c₂ * g' w) := fun z =>
  ⟨((hf z).1.const_mul c₁).add ((hg z).1.const_mul c₂),
    (((hf z).2.const_mul c₁).add ((hg z).2.const_mul c₂)).congr_deriv (by ring)⟩

/-- **Connection formula** (DLMF 12.2.17, upper signs):
`√(2π) U(-a, iz) = Γ(1/2 + a) (e^{-iπ(a/2 - 1/4)} U(a,z) + e^{iπ(a/2 - 1/4)} U(a,-z))`.
At the poles of `Γ(1/2 + a)` the bracket vanishes and the right side is a limit `∞ · 0`,
so those parameters are excluded. -/
@[dlmf 12.2.E17]
theorem parabolicCylinderU_connection_mul_I {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    (Real.sqrt (2 * π) : ℂ) * parabolicCylinderU (-a) (I * z) = Gamma (1 / 2 + a) *
      (exp (-I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a z +
        exp (I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a (-z)) := by
  set A := Gamma (1 / 2 + a) with hA
  set e₁ := exp (-I * π * (a / 2 - 1 / 4)) with he₁d
  set e₂ := exp (I * π * (a / 2 - 1 / 4)) with he₂d
  have hf := (isWeberSolution_parabolicCylinderU_mul_I a).lincomb
      (isWeberSolution_parabolicCylinderU_mul_I a)
    (Real.sqrt (2 * π) : ℂ) 0
  have hg := ((isWeberSolution_parabolicCylinderU a).lincomb
      (isWeberSolution_parabolicCylinderU_neg a) (A * e₁) (A * e₂))
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring, ← hA] at hd
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hA0 : A ≠ 0 := Complex.Gamma_ne_zero ha
  have hprod : Gamma (1 / 4 + a / 2) * Gamma (3 / 4 + a / 2) ≠ 0 := by
    rw [hd]; exact mul_ne_zero (mul_ne_zero hA0 hT) hπ
  have hΓ1 : Gamma (1 / 4 + a / 2) ≠ 0 := left_ne_zero_of_mul hprod
  have hΓ3 : Gamma (3 / 4 + a / 2) ≠ 0 := right_ne_zero_of_mul hprod
  have hAe : A = Gamma (1 / 4 + a / 2) * Gamma (3 / 4 + a / 2) /
      ((2 : ℂ) ^ (1 / 2 - a) * (Real.sqrt π : ℂ)) := by
    rw [hd]; field_simp
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have hcos : Complex.cos (π * (a / 2 - 1 / 4)) = Complex.sin (π * (1 / 4 + a / 2)) := by
    rw [← Complex.sin_add_pi_div_two]; ring_nf
  have hsin : Complex.sin (π * (a / 2 - 1 / 4)) = -Complex.sin (π * (1 / 4 - a / 2)) := by
    rw [← Complex.sin_neg]; ring_nf
  have he₁ : e₁ = Complex.cos (π * (a / 2 - 1 / 4)) - Complex.sin (π * (a / 2 - 1 / 4)) * I := by
    rw [he₁d, show -I * π * (a / 2 - 1 / 4) = (-(π * (a / 2 - 1 / 4))) * I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have he₂ : e₂ = Complex.cos (π * (a / 2 - 1 / 4)) + Complex.sin (π * (a / 2 - 1 / 4)) * I := by
    rw [he₂d, show I * π * (a / 2 - 1 / 4) = (π * (a / 2 - 1 / 4)) * I by ring,
      Complex.exp_mul_I]
  rw [hcos, ← q2] at he₁ he₂
  rw [hsin, ← q1] at he₁ he₂
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have h2π : (Real.sqrt (2 * π) : ℂ) = (Real.sqrt 2 : ℂ) * (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_mul (by norm_num), Complex.ofReal_mul]
  have hpow (x y : ℂ) (hxy : 1 / 2 + x + (1 / 2 - a) = 1 + y) :
      (Real.sqrt 2 : ℂ) * 2 ^ x * 2 ^ (1 / 2 - a) = 2 * 2 ^ y := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero, ← Complex.cpow_add _ _ two_ne_zero,
      hxy, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  have key := hf.eq_of_initial hg ?_ ?_ z
  · simp only [zero_mul, add_zero] at key
    rw [key]; ring
  · simp only [mul_zero, neg_zero, zero_mul, add_zero]
    rw [parabolicCylinderU_zero' (-a), parabolicCylinderU_zero' a, he₁, he₂, hAe, h2π,
      show (3 / 4 + -a / 2 : ℂ) = 3 / 4 - a / 2 by ring]
    have r := hpow (-(-a / 2 + 1 / 4)) (-(a / 2 + 1 / 4)) (by ring)
    generalize (Gamma (3 / 4 - a / 2))⁻¹ = m3
    generalize (Gamma (1 / 4 - a / 2))⁻¹ = m1
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hT r
    generalize Gamma (1 / 4 + a / 2) = B at hΓ1
    generalize Gamma (3 / 4 + a / 2) = C at hΓ3
    generalize (2 : ℂ) ^ (-(a / 2 + 1 / 4)) = P at r
    generalize (2 : ℂ) ^ (-(-a / 2 + 1 / 4)) = P' at r
    field_simp
    have hππ2 : (Real.sqrt π : ℂ) ^ 2 = π := by rw [sq, hππ]
    linear_combination ((Real.sqrt π : ℂ) ^ 2 * m3 * C) * r + (2 * P * m3 * C) * hππ2
  · simp only [mul_zero, neg_zero, zero_mul, add_zero]
    rw [parabolicCylinderUDeriv_zero' (-a), parabolicCylinderUDeriv_zero' a, he₁, he₂, hAe, h2π,
      show (1 / 4 + -a / 2 : ℂ) = 1 / 4 - a / 2 by ring]
    have r := hpow (-(-a / 2 - 1 / 4)) (-(a / 2 - 1 / 4)) (by ring)
    generalize (Gamma (3 / 4 - a / 2))⁻¹ = m3
    generalize (Gamma (1 / 4 - a / 2))⁻¹ = m1
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hT r
    generalize Gamma (1 / 4 + a / 2) = B at hΓ1
    generalize Gamma (3 / 4 + a / 2) = C at hΓ3
    generalize (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = P at r
    generalize (2 : ℂ) ^ (-(-a / 2 - 1 / 4)) = P' at r
    field_simp
    have hππ2 : (Real.sqrt π : ℂ) ^ 2 = π := by rw [sq, hππ]
    linear_combination (-(Real.sqrt π : ℂ) ^ 2 * I * m1 * B) * r + (-2 * I * P * m1 * B) * hππ2

/-- **Connection formula** (DLMF 12.2.17, lower signs):
`√(2π) U(-a, -iz) = Γ(1/2 + a) (e^{-iπ(a/2 - 1/4)} U(a,-z) + e^{iπ(a/2 - 1/4)} U(a,z))`. -/
@[dlmf 12.2.E17]
theorem parabolicCylinderU_connection_mul_neg_I {a : ℂ} (ha : ∀ n : ℕ, 1 / 2 + a ≠ -n) (z : ℂ) :
    (Real.sqrt (2 * π) : ℂ) * parabolicCylinderU (-a) (-I * z) = Gamma (1 / 2 + a) *
      (exp (-I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a (-z) +
        exp (I * π * (a / 2 - 1 / 4)) * parabolicCylinderU a z) := by
  have h := parabolicCylinderU_connection_mul_I ha (-z)
  rwa [neg_neg, show I * -z = -I * z by ring] at h

/-- `V(a,·)` has derivative `parabolicCylinderVDeriv a`. -/
theorem hasDerivAt_parabolicCylinderV (a z : ℂ) : HasDerivAt (parabolicCylinderV a)
    (parabolicCylinderVDeriv a z) z :=
  ((hasDerivAt_parabolicCylinderEven a z).const_mul _).add
      ((hasDerivAt_parabolicCylinderOdd a z).const_mul _)

/-- Weber's equation (DLMF 12.2.2) for `V`. -/
@[dlmf 12.2.E2]
theorem hasDerivAt_parabolicCylinderVDeriv (a z : ℂ) :
    HasDerivAt (parabolicCylinderVDeriv a) ((z ^ 2 / 4 + a) * parabolicCylinderV a z) z := by
  refine (((hasDerivAt_parabolicCylinderEvenDeriv a z).const_mul _).add
    ((hasDerivAt_parabolicCylinderOddDeriv a z).const_mul _)).congr_deriv ?_
  rw [parabolicCylinderV]
  ring

/-- `V(a,z)` solves Weber's equation, with derivative `parabolicCylinderVDeriv a`. -/
theorem isWeberSolution_parabolicCylinderV (a : ℂ) : IsWeberSolution a (parabolicCylinderV a)
    (parabolicCylinderVDeriv a) :=
  fun z => ⟨hasDerivAt_parabolicCylinderV a z, hasDerivAt_parabolicCylinderVDeriv a z⟩

/-- `deriv (V(a,·)) = parabolicCylinderVDeriv a`. -/
theorem deriv_parabolicCylinderV (a : ℂ) : deriv (parabolicCylinderV a) =
    parabolicCylinderVDeriv a :=
  funext fun z => (hasDerivAt_parabolicCylinderV a z).deriv

/-- The value `V(a,0)` is `parabolicCylinderVZero a` (DLMF 12.2.8). -/
theorem parabolicCylinderV_zero' (a : ℂ) : parabolicCylinderV a 0 = parabolicCylinderVZero a := by
  simp [parabolicCylinderV, parabolicCylinderEven_zero, parabolicCylinderOdd_zero]

/-- The value `V'(a,0)` is `parabolicCylinderVDerivZero a` (DLMF 12.2.9). -/
theorem parabolicCylinderVDeriv_zero' (a : ℂ) : parabolicCylinderVDeriv a 0 =
    parabolicCylinderVDerivZero a := by
  simp [parabolicCylinderVDeriv, parabolicCylinderEvenDeriv_zero, parabolicCylinderOddDeriv_zero]

/-- `V(a,0)` (DLMF 12.2.8). -/
@[dlmf 12.2.E8]
theorem parabolicCylinderV_zero (a : ℂ) :
    parabolicCylinderV a 0 = π * (2 : ℂ) ^ (a / 2 + 1 / 4) /
      (Gamma (3 / 4 - a / 2) ^ 2 * Gamma (1 / 4 + a / 2)) := by
  rw [parabolicCylinderV_zero', parabolicCylinderVZero]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- `V'(a,0)` (DLMF 12.2.9). -/
@[dlmf 12.2.E9]
theorem parabolicCylinderVDeriv_zero (a : ℂ) :
    parabolicCylinderVDeriv a 0 = π * (2 : ℂ) ^ (a / 2 + 3 / 4) /
      (Gamma (1 / 4 - a / 2) ^ 2 * Gamma (3 / 4 + a / 2)) := by
  rw [parabolicCylinderVDeriv_zero', parabolicCylinderVDerivZero]
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- The derivative of `w ↦ V(a,-w)` is `-V'(a,-z)`. -/
theorem hasDerivAt_parabolicCylinderV_neg (a z : ℂ) :
    HasDerivAt (fun w => parabolicCylinderV a (-w)) (-parabolicCylinderVDeriv a (-z)) z := by
  have h := (hasDerivAt_parabolicCylinderV a (-z)).comp z (hasDerivAt_neg z)
  exact h.congr_deriv (by ring)

/-- `V(a,-z)` solves Weber's equation. -/
theorem isWeberSolution_parabolicCylinderV_neg (a : ℂ) :
    IsWeberSolution a (fun w => parabolicCylinderV a (-w))
        (fun w => -parabolicCylinderVDeriv a (-w)) := fun z => by
  refine ⟨hasDerivAt_parabolicCylinderV_neg a z, ?_⟩
  have h := ((hasDerivAt_parabolicCylinderVDeriv a (-z)).comp z (hasDerivAt_neg z)).neg
  exact h.congr_deriv (by ring)

/-- Legendre duplication for reciprocals, valid for every `a`:
`1/Γ(1/2 + a) = 2^{1/2-a} √π / (Γ(1/4 + a/2) Γ(3/4 + a/2))`. -/
theorem recip_Gamma_half_add (a : ℂ) :
    (Gamma (1 / 2 + a))⁻¹ = (Gamma (1 / 4 + a / 2))⁻¹ * (Gamma (3 / 4 + a / 2))⁻¹ *
      (2 : ℂ) ^ (1 / 2 - a) * (Real.sqrt π : ℂ) := by
  have hd := Complex.Gamma_mul_Gamma_add_half (1 / 4 + a / 2)
  rw [show 1 / 4 + a / 2 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (1 / 4 + a / 2) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 / 2 - a) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  rw [← mul_inv, hd, mul_inv, mul_inv]
  field_simp

/-- `sin(π(1/4 - a/2)) = cos(π(1/4 + a/2))`. -/
theorem sin_pi_quarter_sub (a : ℂ) :
    Complex.sin (π * (1 / 4 - a / 2)) = Complex.cos (π * (1 / 4 + a / 2)) := by
  rw [← Complex.sin_pi_div_two_sub]; ring_nf

/-- `sin(πa) = sin²(π(1/4 + a/2)) - cos²(π(1/4 + a/2))`. -/
theorem sin_pi_mul_eq_sq (a : ℂ) :
    Complex.sin (π * a) =
      Complex.sin (π * (1 / 4 + a / 2)) ^ 2 - Complex.cos (π * (1 / 4 + a / 2)) ^ 2 := by
  rw [show (π : ℂ) * a = 2 * (π * (1 / 4 + a / 2)) - π / 2 by ring,
    Complex.sin_sub_pi_div_two, Complex.cos_two_mul]
  linear_combination (-1 : ℂ) * Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))

/-- `cos(πa) = 2 sin(π(1/4 + a/2)) cos(π(1/4 + a/2))`. -/
theorem cos_pi_mul_eq_mul (a : ℂ) :
    Complex.cos (π * a) =
      2 * Complex.sin (π * (1 / 4 + a / 2)) * Complex.cos (π * (1 / 4 + a / 2)) := by
  rw [show (π : ℂ) * a = 2 * (π * (1 / 4 + a / 2)) - π / 2 by ring,
    Complex.cos_sub_pi_div_two, Complex.sin_two_mul]

/-- **Wronskian** (DLMF 12.2.10): `𝒲{U(a,z), V(a,z)} = √(2/π)`. -/
@[dlmf 12.2.E10]
theorem parabolicCylinderV_wronskian (a z : ℂ) :
    parabolicCylinderU a z * deriv (parabolicCylinderV a) z - deriv (parabolicCylinderU a) z *
        parabolicCylinderV a z = (Real.sqrt (2 / π) : ℂ) := by
  rw [deriv_parabolicCylinderV, deriv_parabolicCylinderU]
  have hW := (isWeberSolution_parabolicCylinderU a).wronskian_eq
      (isWeberSolution_parabolicCylinderV a) z
  rw [hW, parabolicCylinderU_zero', parabolicCylinderUDeriv_zero', parabolicCylinderV_zero',
      parabolicCylinderVDeriv_zero', parabolicCylinderVZero, parabolicCylinderVDerivZero]
  have q1 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 - a / 2)
  rw [show 1 - (1 / 4 - a / 2) = 3 / 4 + a / 2 by ring, sin_pi_quarter_sub] at q1
  have q2 := pi_mul_recip_Gamma_mul_recip_Gamma (1 / 4 + a / 2)
  rw [show 1 - (1 / 4 + a / 2) = 3 / 4 - a / 2 by ring] at q2
  have htr := Complex.sin_sq_add_cos_sq (π * (1 / 4 + a / 2))
  have p1 : (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * 2 ^ (a / 2 + 3 / 4) = (Real.sqrt 2 : ℂ) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]; ring_nf
  have p2 : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * 2 ^ (a / 2 + 1 / 4) = (Real.sqrt 2 : ℂ) := by
    rw [← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]; ring_nf
  have hππ : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hR : (Real.sqrt (2 / π) : ℂ) * (Real.sqrt π : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le),
      div_mul_cancel₀ _ Real.pi_ne_zero]
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine mul_left_cancel₀ hπ0 ?_
  set g1m := (Gamma (1 / 4 - a / 2))⁻¹
  set g3m := (Gamma (3 / 4 - a / 2))⁻¹
  set g1p := (Gamma (1 / 4 + a / 2))⁻¹
  set g3p := (Gamma (3 / 4 + a / 2))⁻¹
  set c := Complex.cos (π * (1 / 4 + a / 2))
  set s := Complex.sin (π * (1 / 4 + a / 2))
  set r := (Real.sqrt π : ℂ)
  set R := (Real.sqrt (2 / π) : ℂ)
  set t := (Real.sqrt 2 : ℂ)
  linear_combination (π ^ 2 * r * g3p ^ 2 * g1m ^ 2) * p1 + (π ^ 2 * r * g1p ^ 2 * g3m ^ 2) * p2
    + (r * t * (π * (g1m * g3p) + c)) * q1 + (r * t * (π * (g1p * g3m) + s)) * q2
    + (r * t) * htr + R * hππ - r * hR

end DLMF.Confluent
