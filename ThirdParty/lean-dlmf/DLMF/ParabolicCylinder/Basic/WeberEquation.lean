/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic.Functions
public import DLMF.Confluent.Basic.KummerContiguous
-- PATCH: Mathlib's probabilists' Hermite polynomials (`hermite`, `hermite_zero`, `hermite_one`); previously reached
-- through the TauCeti Hermite import removed from `DLMF/ParabolicCylinder/Basic/Functions.lean`
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Weber's equation, initial values and recurrences (DLMF §§12.2, 12.7, 12.8)

The solutions `u₁`, `u₂`, `U(a,z)` of Weber's equation `w'' = (z²/4 + a) w` defined in
`DLMF.ParabolicCylinder.Basic.Functions`: their derivatives, Weber's equation, initial values,
uniqueness of solutions with given initial data, the recurrences of `U`, and the Hermite
specializations.

## Main results

* `hasDerivAt_parabolicCylinderEven`, `hasDerivAt_parabolicCylinderOdd`,
  `hasDerivAt_parabolicCylinderU`, `deriv_parabolicCylinderU`: the derivatives.
* `hasDerivAt_parabolicCylinderUDeriv`, `deriv_deriv_parabolicCylinderU`,
  `isWeberSolution_parabolicCylinderEven`, `isWeberSolution_parabolicCylinderOdd`,
  `isWeberSolution_parabolicCylinderU`: Weber's equation (DLMF 12.2.2).
* `parabolicCylinderU_zero`, `parabolicCylinderUDeriv_zero`: the initial values `U(a,0)`, `U'(a,0)`
  (DLMF 12.2.6, 12.2.7).
* `IsWeberSolution.wronskian_eq`, `IsWeberSolution.eq_zero`, `IsWeberSolution.eq_of_initial`:
  constancy of the Wronskian and uniqueness for given initial data.
* `parabolicCylinderU_recurrence_sub`, `parabolicCylinderU_recurrence_add`,
  `parabolicCylinderU_three_term`, `parabolicCylinderU_deriv_recurrence`: the recurrences DLMF
  12.8.1–12.8.4.
* `parabolicCylinderU_neg_half`, `parabolicCylinderD_nat`: `D_0(z) = e^{-z²/4}` and
  `D_n(z) = e^{-z²/4} He_n(z)` (DLMF 12.7.1, 12.7.2).

## Implementation notes

The Wronskians and the second solution `V` are in
`DLMF.ParabolicCylinder.Basic.Wronskians`; the asymptotic expansion and integral
representations are in `DLMF.Confluent.ParabolicCylinder.EquationAndIntegrals`.
-/

public section

open Complex Filter
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- `5/2` is not a nonpositive integer. -/
theorem five_halves_ne_neg_nat : ∀ k : ℕ, (5 / 2 : ℂ) ≠ -k := fun k h => by
  have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Derivative of `z ↦ M(α, b, z²/2)`: it is `z (α/b) M(α+1, b+1, z²/2)`. -/
theorem hasDerivAt_kummerM_half_sq {α b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (fun z : ℂ => kummerM α b (z ^ 2 / 2))
      (z * (α / b * kummerM (α + 1) (b + 1) (z ^ 2 / 2))) z := by
  have h := (hasDerivAt_kummerM_shift (a := α) hb (z ^ 2 / 2)).comp z
    (((hasDerivAt_pow 2 z).div_const 2))
  exact h.congr_deriv (by push_cast; ring)

/-- `d/dz e^{-z²/4} = -(z/2) e^{-z²/4}`. -/
theorem hasDerivAt_exp_neg_sq_div_four (z : ℂ) :
    HasDerivAt (fun z : ℂ => exp (-z ^ 2 / 4)) (-z / 2 * exp (-z ^ 2 / 4)) z := by
  have h := (((hasDerivAt_pow 2 z).neg).div_const 4).cexp
  exact h.congr_deriv (by simp only [Pi.neg_apply]; push_cast; ring)

/-- The even Weber solution `parabolicCylinderEven a` has derivative `parabolicCylinderEvenDeriv a`.
-/
theorem hasDerivAt_parabolicCylinderEven (a z : ℂ) : HasDerivAt (parabolicCylinderEven a)
    (parabolicCylinderEvenDeriv a z) z := by
  have h := (hasDerivAt_exp_neg_sq_div_four z).mul
    (hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4) Complex.one_div_two_ne_neg_natCast z)
  exact h.congr_deriv (by unfold parabolicCylinderEvenDeriv; ring)

/-- `(parabolicCylinderEvenDeriv a)' = (z²/4 + a) parabolicCylinderEven a`, i.e.
`parabolicCylinderEven a` solves Weber's equation `w'' = (z²/4 + a) w` (DLMF 12.2.2). -/
theorem hasDerivAt_parabolicCylinderEvenDeriv (a z : ℂ) :
    HasDerivAt (parabolicCylinderEvenDeriv a) ((z ^ 2 / 4 + a) * parabolicCylinderEven a z) z := by
  have hb1 : ∀ k : ℕ, (1 / 2 + 1 : ℂ) ≠ -k := by
    norm_num; exact Complex.three_div_two_ne_neg_natCast
  have h0 := hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4) Complex.one_div_two_ne_neg_natCast z
  have h1 := hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4 + 1) hb1 z
  have h := (((hasDerivAt_id z).mul (hasDerivAt_exp_neg_sq_div_four z)).mul
    ((h0.const_mul (-(1 / 2))).add (h1.const_mul (a + 1 / 2))))
  have hc := kummerM_ode_contiguous (a := a / 2 + 1 / 4) (b := 1 / 2)
      Complex.one_div_two_ne_neg_natCast
    (z := z ^ 2 / 2)
  refine h.congr_deriv ?_
  unfold parabolicCylinderEven
  simp only [id, Pi.add_apply, Pi.mul_apply]
  rw [show a / 2 + 1 / 4 + 1 + 1 = a / 2 + 1 / 4 + 2 by ring]
  norm_num at hc ⊢
  linear_combination (exp (-z ^ 2 / 4) * (8 * (a / 2 + 1 / 4) / 3)) * hc

/-- The odd Weber solution `parabolicCylinderOdd a` has derivative `parabolicCylinderOddDeriv a`. -/
theorem hasDerivAt_parabolicCylinderOdd (a z : ℂ) : HasDerivAt (parabolicCylinderOdd a)
    (parabolicCylinderOddDeriv a z) z := by
  have h := ((hasDerivAt_id z).mul (hasDerivAt_exp_neg_sq_div_four z)).mul
    (hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4) Complex.three_div_two_ne_neg_natCast z)
  exact h.congr_deriv (by unfold parabolicCylinderOddDeriv; simp only [id, Pi.mul_apply]; ring)

/-- `(parabolicCylinderOddDeriv a)' = (z²/4 + a) parabolicCylinderOdd a`, i.e.
`parabolicCylinderOdd a` solves Weber's equation. -/
theorem hasDerivAt_parabolicCylinderOddDeriv (a z : ℂ) :
    HasDerivAt (parabolicCylinderOddDeriv a) ((z ^ 2 / 4 + a) * parabolicCylinderOdd a z) z := by
  have hb1 : ∀ k : ℕ, (3 / 2 + 1 : ℂ) ≠ -k := by
    norm_num; exact five_halves_ne_neg_nat
  have h0 := hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4) Complex.three_div_two_ne_neg_natCast z
  have h1 := hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4 + 1) hb1 z
  have h := (hasDerivAt_exp_neg_sq_div_four z).mul
    ((((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_pow 2 z).div_const 2)).mul h0).add
      (((hasDerivAt_pow 2 z).const_mul ((a + 3 / 2) / 3)).mul h1))
  have hc := kummerM_ode_contiguous (a := a / 2 + 3 / 4) (b := 3 / 2)
    Complex.three_div_two_ne_neg_natCast (z := z ^ 2 / 2)
  refine h.congr_deriv ?_
  unfold parabolicCylinderOdd
  rw [show a / 2 + 3 / 4 + 1 + 1 = a / 2 + 3 / 4 + 2 by ring]
  norm_num at hc ⊢
  linear_combination (exp (-z ^ 2 / 4) * (8 * (a / 2 + 3 / 4) * z / 15)) * hc

/-- `U(a,·)` has derivative `parabolicCylinderUDeriv a`. -/
theorem hasDerivAt_parabolicCylinderU (a z : ℂ) : HasDerivAt (parabolicCylinderU a)
    (parabolicCylinderUDeriv a z) z :=
  ((hasDerivAt_parabolicCylinderEven a z).const_mul _).sub
      ((hasDerivAt_parabolicCylinderOdd a z).const_mul _)

/-- **Weber's equation** (DLMF 12.2.2): `U''(a,z) = (z²/4 + a) U(a,z)`. -/
@[dlmf 12.2.E2]
theorem hasDerivAt_parabolicCylinderUDeriv (a z : ℂ) :
    HasDerivAt (parabolicCylinderUDeriv a) ((z ^ 2 / 4 + a) * parabolicCylinderU a z) z := by
  refine (((hasDerivAt_parabolicCylinderEvenDeriv a z).const_mul _).sub
    ((hasDerivAt_parabolicCylinderOddDeriv a z).const_mul _)).congr_deriv ?_
  rw [parabolicCylinderU]
  ring

/-- Weber's equation in `deriv` form. -/
theorem deriv_deriv_parabolicCylinderU (a z : ℂ) :
    deriv (deriv (parabolicCylinderU a)) z = (z ^ 2 / 4 + a) * parabolicCylinderU a z := by
  have : deriv (parabolicCylinderU a) = parabolicCylinderUDeriv a := funext fun w =>
      (hasDerivAt_parabolicCylinderU a w).deriv
  rw [this, (hasDerivAt_parabolicCylinderUDeriv a z).deriv]

/-- `U(a,0)` (DLMF 12.2.6). -/
@[dlmf 12.2.E6]
theorem parabolicCylinderU_zero (a : ℂ) :
    parabolicCylinderU a 0 = (Real.sqrt π : ℂ) /
        ((2 : ℂ) ^ (a / 2 + 1 / 4) * Gamma (3 / 4 + a / 2)) := by
  simp only [parabolicCylinderU, parabolicCylinderEven, parabolicCylinderOdd, zero_pow two_ne_zero,
      zero_div, neg_zero, Complex.exp_zero,
    kummerM_zero, mul_zero, sub_zero, mul_one, Complex.cpow_neg]
  field_simp

/-- `U'(a,0)` (DLMF 12.2.7). -/
@[dlmf 12.2.E7]
theorem parabolicCylinderUDeriv_zero (a : ℂ) :
    parabolicCylinderUDeriv a 0 = -(Real.sqrt π : ℂ) /
        ((2 : ℂ) ^ (a / 2 - 1 / 4) * Gamma (1 / 4 + a / 2)) := by
  simp only [parabolicCylinderUDeriv, parabolicCylinderEvenDeriv, parabolicCylinderOddDeriv,
      zero_pow two_ne_zero, zero_div, neg_zero,
    Complex.exp_zero, kummerM_zero, zero_mul, mul_zero, sub_zero, mul_one, add_zero,
    zero_sub, Complex.cpow_neg]
  field_simp

/-- `U(-1/2, z) = D_0(z) = e^{-z²/4}` (DLMF 12.7.1). -/
@[dlmf 12.7.E1]
theorem parabolicCylinderU_neg_half (z : ℂ) : parabolicCylinderU (-1 / 2) z = exp (-z ^ 2 / 4) := by
  have h1 : (3 / 4 + -1 / 2 / 2 : ℂ) = 1 / 2 := by ring
  have h2 : (1 / 4 + -1 / 2 / 2 : ℂ) = 0 := by ring
  have h3 : (-1 / 2 / 2 + 1 / 4 : ℂ) = 0 := by ring
  have hΓ : Gamma (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  rw [parabolicCylinderU, parabolicCylinderEven, h1, h2, h3, Complex.Gamma_zero, inv_zero, hΓ,
    kummerM_of_zero_param, neg_zero, Complex.cpow_zero]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- `2^{1/2} = √2` as complex numbers. -/
theorem two_cpow_half : (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
  norm_num

/-- The even Weber solution takes the value `1` at `0`. -/
theorem parabolicCylinderEven_zero (a : ℂ) : parabolicCylinderEven a 0 = 1 := by
  simp [parabolicCylinderEven, kummerM_zero]

/-- The derivative of the even Weber solution vanishes at `0`. -/
theorem parabolicCylinderEvenDeriv_zero (a : ℂ) : parabolicCylinderEvenDeriv a 0 = 0 := by
  simp [parabolicCylinderEvenDeriv]

/-- The odd Weber solution vanishes at `0`. -/
theorem parabolicCylinderOdd_zero (a : ℂ) : parabolicCylinderOdd a 0 = 0 := by
  simp [parabolicCylinderOdd]

/-- The derivative of the odd Weber solution is `1` at `0`. -/
theorem parabolicCylinderOddDeriv_zero (a : ℂ) : parabolicCylinderOddDeriv a 0 = 1 := by
  simp [parabolicCylinderOddDeriv, kummerM_zero]

/-- The even Weber solution solves Weber's equation, with derivative `parabolicCylinderEvenDeriv a`.
-/
theorem isWeberSolution_parabolicCylinderEven (a : ℂ) : IsWeberSolution a (parabolicCylinderEven a)
    (parabolicCylinderEvenDeriv a) :=
  fun z => ⟨hasDerivAt_parabolicCylinderEven a z, hasDerivAt_parabolicCylinderEvenDeriv a z⟩

/-- The odd Weber solution solves Weber's equation, with derivative `parabolicCylinderOddDeriv a`.
-/
theorem isWeberSolution_parabolicCylinderOdd (a : ℂ) : IsWeberSolution a (parabolicCylinderOdd a)
    (parabolicCylinderOddDeriv a) :=
  fun z => ⟨hasDerivAt_parabolicCylinderOdd a z, hasDerivAt_parabolicCylinderOddDeriv a z⟩

/-- `U(a,z)` solves Weber's equation, with derivative `parabolicCylinderUDeriv a`. -/
theorem isWeberSolution_parabolicCylinderU (a : ℂ) : IsWeberSolution a (parabolicCylinderU a)
    (parabolicCylinderUDeriv a) :=
  fun z => ⟨hasDerivAt_parabolicCylinderU a z, hasDerivAt_parabolicCylinderUDeriv a z⟩

/-- The Wronskian of two solutions of Weber's equation is constant. -/
theorem IsWeberSolution.wronskian_eq {a : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsWeberSolution a f f')
    (hg : IsWeberSolution a g g') (z : ℂ) :
    f z * g' z - f' z * g z = f 0 * g' 0 - f' 0 * g 0 := by
  have hd : ∀ w, HasDerivAt (fun w => f w * g' w - f' w * g w) 0 w := fun w =>
    (((hf w).1.mul (hg w).2).sub ((hf w).2.mul (hg w).1)).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0

/-- A solution of Weber's equation with vanishing initial data vanishes identically. -/
theorem IsWeberSolution.eq_zero {a : ℂ} {f f' : ℂ → ℂ} (hf : IsWeberSolution a f f') (h0 : f 0 = 0)
    (h1 : f' 0 = 0) (z : ℂ) : f z = 0 := by
  have h₁ := hf.wronskian_eq (isWeberSolution_parabolicCylinderEven a) z
  have h₂ := hf.wronskian_eq (isWeberSolution_parabolicCylinderOdd a) z
  have h₃ := (isWeberSolution_parabolicCylinderEven a).wronskian_eq
      (isWeberSolution_parabolicCylinderOdd a) z
  simp only [h0, h1, parabolicCylinderEven_zero, parabolicCylinderEvenDeriv_zero,
      parabolicCylinderOdd_zero, parabolicCylinderOddDeriv_zero] at h₁ h₂ h₃
  linear_combination (-(parabolicCylinderOdd a z)) * h₁ + parabolicCylinderEven a z * h₂ - f z * h₃

/-- Solutions of Weber's equation are determined by their initial data. -/
theorem IsWeberSolution.eq_of_initial {a : ℂ} {f f' g g' : ℂ → ℂ} (hf : IsWeberSolution a f f')
    (hg : IsWeberSolution a g g') (h0 : f 0 = g 0) (h1 : f' 0 = g' 0) (z : ℂ) : f z = g z := by
  have hd : IsWeberSolution a (fun w => f w - g w) (fun w => f' w - g' w) := fun w =>
    ⟨(hf w).1.sub (hg w).1, ((hf w).2.sub (hg w).2).congr_deriv (by ring)⟩
  exact sub_eq_zero.mp (hd.eq_zero (by simp [h0]) (by simp [h1]) z)

/-- `U(a,0) = √π 2^{-(a/2+1/4)} / Γ(3/4 + a/2)` (DLMF 12.2.6). -/
theorem parabolicCylinderU_zero' (a : ℂ) :
    parabolicCylinderU a 0 = (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) *
        (Gamma (3 / 4 + a / 2))⁻¹ := by
  simp [parabolicCylinderU, parabolicCylinderEven_zero, parabolicCylinderOdd_zero]

/-- `U'(a,0) = -√π 2^{-(a/2-1/4)} / Γ(1/4 + a/2)` (DLMF 12.2.7). -/
theorem parabolicCylinderUDeriv_zero' (a : ℂ) :
    parabolicCylinderUDeriv a 0 =
      -((Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹) := by
  simp [parabolicCylinderUDeriv, parabolicCylinderEvenDeriv_zero, parabolicCylinderOddDeriv_zero]

/-- `s / Γ(s + 1) = 1 / Γ(s)` for every complex `s`, with Mathlib's totalized `Γ`. -/
theorem mul_recip_Gamma_add_one' (s : ℂ) : s * (Gamma (s + 1))⁻¹ = (Gamma s)⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  rw [Complex.Gamma_add_one s hs]
  rcases eq_or_ne (Gamma s) 0 with hg | hg
  · simp [hg]
  · field_simp

/-- `2^{x-1} = 2^x/2`. -/
theorem two_cpow_sub_one (x : ℂ) : (2 : ℂ) ^ (x - 1) = (2 : ℂ) ^ x / 2 := by
  rw [Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one]

/-- `deriv (U(a,·)) = parabolicCylinderUDeriv a`. -/
theorem deriv_parabolicCylinderU (a : ℂ) : deriv (parabolicCylinderU a) =
    parabolicCylinderUDeriv a :=
  funext fun z => (hasDerivAt_parabolicCylinderU a z).deriv

/-- DLMF 12.8.3: `U'(a,z) - (z/2) U(a,z) + U(a-1,z) = 0`. -/
@[dlmf 12.8.E3]
theorem parabolicCylinderU_recurrence_sub (a z : ℂ) :
    deriv (parabolicCylinderU a) z - z / 2 * parabolicCylinderU a z +
        parabolicCylinderU (a - 1) z = 0 := by
  rw [deriv_parabolicCylinderU]
  have hs : IsWeberSolution (a - 1)
      (fun w => parabolicCylinderUDeriv a w - w / 2 * parabolicCylinderU a w +
      parabolicCylinderU (a - 1) w)
      (fun w => (w ^ 2 / 4 + a) * parabolicCylinderU a w - 1 / 2 * parabolicCylinderU a w - w / 2 *
          parabolicCylinderUDeriv a w +
        parabolicCylinderUDeriv (a - 1) w) := fun w => by
    have hU := hasDerivAt_parabolicCylinderU a w
    have hU' := hasDerivAt_parabolicCylinderUDeriv a w
    have hV := hasDerivAt_parabolicCylinderU (a - 1) w
    have hV' := hasDerivAt_parabolicCylinderUDeriv (a - 1) w
    refine ⟨(hU'.sub (((hasDerivAt_id w).div_const 2).mul hU)).add hV |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).sub
        (hU.const_mul (1 / 2))).sub (((hasDerivAt_id w).div_const 2).mul hU')).add hV'
        |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : parabolicCylinderUDeriv a 0 - 0 / 2 * parabolicCylinderU a 0 +
      parabolicCylinderU (a - 1) 0 = 0 := by
    rw [parabolicCylinderUDeriv_zero' a, parabolicCylinderU_zero' a,
        parabolicCylinderU_zero' (a - 1),
      show 3 / 4 + (a - 1) / 2 = 1 / 4 + a / 2 by ring,
      show -((a - 1) / 2 + 1 / 4) = -(a / 2 - 1 / 4) by ring]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * parabolicCylinderU a 0 - 1 / 2 * parabolicCylinderU a 0 - 0 /
      2 * parabolicCylinderUDeriv a 0 +
      parabolicCylinderUDeriv (a - 1) 0 = 0 := by
    have hg := mul_recip_Gamma_add_one' (a / 2 - 1 / 4)
    rw [show a / 2 - 1 / 4 + 1 = 3 / 4 + a / 2 by ring] at hg
    rw [parabolicCylinderUDeriv_zero' a, parabolicCylinderU_zero' a,
        parabolicCylinderUDeriv_zero' (a - 1),
      show 1 / 4 + (a - 1) / 2 = a / 2 - 1 / 4 by ring,
      show -((a - 1) / 2 - 1 / 4) = -(a / 2 + 1 / 4) + 1 by ring,
      Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one, ← hg]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.2: `U'(a,z) + (z/2) U(a,z) + (a + 1/2) U(a+1,z) = 0`. -/
@[dlmf 12.8.E2]
theorem parabolicCylinderU_recurrence_add (a z : ℂ) :
    deriv (parabolicCylinderU a) z + z / 2 * parabolicCylinderU a z + (a + 1 / 2) *
        parabolicCylinderU (a + 1) z = 0 := by
  rw [deriv_parabolicCylinderU]
  have hs : IsWeberSolution (a + 1)
      (fun w => parabolicCylinderUDeriv a w + w / 2 * parabolicCylinderU a w + (a + 1 / 2) *
          parabolicCylinderU (a + 1) w)
      (fun w => (w ^ 2 / 4 + a) * parabolicCylinderU a w + 1 / 2 * parabolicCylinderU a w + w / 2 *
          parabolicCylinderUDeriv a w +
        (a + 1 / 2) * parabolicCylinderUDeriv (a + 1) w) := fun w => by
    have hU := hasDerivAt_parabolicCylinderU a w
    have hU' := hasDerivAt_parabolicCylinderUDeriv a w
    have hV := hasDerivAt_parabolicCylinderU (a + 1) w
    have hV' := hasDerivAt_parabolicCylinderUDeriv (a + 1) w
    refine ⟨(hU'.add (((hasDerivAt_id w).div_const 2).mul hU)).add (hV.const_mul (a + 1 / 2))
      |>.congr_deriv ?_, ?_⟩
    · simp only [id]; ring
    · refine ((((((hasDerivAt_pow 2 w).div_const 4).add_const a).mul hU).add
        (hU.const_mul (1 / 2))).add (((hasDerivAt_id w).div_const 2).mul hU')).add
        (hV'.const_mul (a + 1 / 2)) |>.congr_deriv ?_
      simp only [id]; push_cast; ring
  have h0 : parabolicCylinderUDeriv a 0 + 0 / 2 * parabolicCylinderU a 0 + (a + 1 / 2) *
      parabolicCylinderU (a + 1) 0 = 0 := by
    have hg := mul_recip_Gamma_add_one' (1 / 4 + a / 2)
    rw [show 1 / 4 + a / 2 + 1 = 3 / 4 + (a + 1) / 2 by ring] at hg
    rw [parabolicCylinderUDeriv_zero' a, parabolicCylinderU_zero' a,
        parabolicCylinderU_zero' (a + 1),
      show -((a + 1) / 2 + 1 / 4) = -(a / 2 - 1 / 4) - 1 by ring,
      two_cpow_sub_one, ← hg]
    ring
  have h1 : ((0 : ℂ) ^ 2 / 4 + a) * parabolicCylinderU a 0 + 1 / 2 * parabolicCylinderU a 0 + 0 /
      2 * parabolicCylinderUDeriv a 0 +
      (a + 1 / 2) * parabolicCylinderUDeriv (a + 1) 0 = 0 := by
    rw [parabolicCylinderUDeriv_zero' a, parabolicCylinderU_zero' a,
        parabolicCylinderUDeriv_zero' (a + 1),
      show 1 / 4 + (a + 1) / 2 = 3 / 4 + a / 2 by ring,
      show -((a + 1) / 2 - 1 / 4) = -(a / 2 + 1 / 4) by ring]
    ring
  exact hs.eq_zero h0 h1 z

/-- DLMF 12.8.1: `z U(a,z) - U(a-1,z) + (a + 1/2) U(a+1,z) = 0`. -/
@[dlmf 12.8.E1]
theorem parabolicCylinderU_three_term (a z : ℂ) :
    z * parabolicCylinderU a z - parabolicCylinderU (a - 1) z + (a + 1 / 2) *
        parabolicCylinderU (a + 1) z = 0 := by
  linear_combination parabolicCylinderU_recurrence_add a z - parabolicCylinderU_recurrence_sub a z

/-- DLMF 12.8.4: `2 U'(a,z) + U(a-1,z) + (a + 1/2) U(a+1,z) = 0`. -/
@[dlmf 12.8.E4]
theorem parabolicCylinderU_deriv_recurrence (a z : ℂ) :
    2 * deriv (parabolicCylinderU a) z + parabolicCylinderU (a - 1) z + (a + 1 / 2) *
        parabolicCylinderU (a + 1) z = 0 := by
  linear_combination parabolicCylinderU_recurrence_add a z + parabolicCylinderU_recurrence_sub a z

section Hermite

open Polynomial

/-- `U'(-1/2, z) = -(z/2) e^{-z²/4}`. -/
theorem parabolicCylinderUDeriv_neg_half (z : ℂ) : parabolicCylinderUDeriv (-1 / 2) z = -z / 2 *
    exp (-z ^ 2 / 4) := by
  have h : parabolicCylinderU (-1 / 2) = fun z => exp (-z ^ 2 / 4) :=
      funext parabolicCylinderU_neg_half
  have hd := hasDerivAt_parabolicCylinderU (-1 / 2) z
  rw [h] at hd
  exact hd.unique (hasDerivAt_exp_neg_sq_div_four z)

/-- The recurrence 12.8.1 in Whittaker's notation: `D_{ν+2} = z D_{ν+1} - (ν+1) D_ν`. -/
theorem parabolicCylinderD_add_two (ν z : ℂ) :
    parabolicCylinderD (ν + 2) z = z * parabolicCylinderD (ν + 1) z - (ν + 1) *
        parabolicCylinderD ν z := by
  have h := parabolicCylinderU_three_term (-(ν + 1) - 1 / 2) z
  rw [show -(ν + 1) - 1 / 2 - 1 = -(ν + 2) - 1 / 2 by ring,
    show -(ν + 1) - 1 / 2 + 1 = -ν - 1 / 2 by ring] at h
  simp only [parabolicCylinderD]
  linear_combination -h

-- PATCH: local proofs of `hermite_derivative_succ` and `hermite_add_two`, replacing the two lemmas that
-- `TauCeti.RingTheory.Polynomial.Hermite.Derivative` provided (TauCeti is not vendored). Mathlib v4.35 has
-- `hermite_succ` (`He_{n+1} = x He_n - He_n'`) but neither identity. Statements as used below.

/-- The derivative of the probabilists' Hermite polynomials: `He_{n+1}' = (n+1) He_n`. -/
theorem hermite_derivative_succ (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1) • hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    have hA : derivative (hermite n) = X * hermite n - hermite (n + 1) := by
      rw [hermite_succ n]; ring
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih, map_nsmul, hA]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- The three-term recurrence of the probabilists' Hermite polynomials: `He_{n+2} = x He_{n+1} - (n+1) He_n`. -/
theorem hermite_add_two (n : ℕ) :
    hermite (n + 1 + 1) = X * hermite (n + 1) - (n + 1) • hermite n := by
  rw [hermite_succ (n + 1), hermite_derivative_succ n]

/-- **`D_n(z) = e^{-z²/4} He_n(z)`** (DLMF 12.7.2), with Mathlib's probabilists' Hermite
polynomials `He_n = Polynomial.hermite n`. -/
@[dlmf 12.7.E2]
theorem parabolicCylinderD_nat (n : ℕ) (z : ℂ) : parabolicCylinderD n z = exp (-z ^ 2 / 4) *
    aeval z (hermite n) := by
  have key : ∀ n : ℕ, parabolicCylinderD n z = exp (-z ^ 2 / 4) * aeval z (hermite n) ∧
      parabolicCylinderD (n + 1 : ℕ) z = exp (-z ^ 2 / 4) * aeval z (hermite (n + 1)) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp only [parabolicCylinderD, Nat.cast_zero, hermite_zero, map_one, mul_one]
        rw [show -(0 : ℂ) - 1 / 2 = -1 / 2 by ring, parabolicCylinderU_neg_half]
      · have h := parabolicCylinderU_recurrence_sub (-1 / 2) z
        rw [deriv_parabolicCylinderU, parabolicCylinderUDeriv_neg_half,
            parabolicCylinderU_neg_half] at h
        simp only [parabolicCylinderD, zero_add, Nat.cast_one, hermite_one, aeval_X]
        rw [show (-1 : ℂ) - 1 / 2 = -1 / 2 - 1 by ring]
        linear_combination h
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := parabolicCylinderD_add_two (n : ℂ) z
      rw [show (n : ℂ) + 2 = ((n + 1 + 1 : ℕ) : ℂ) by push_cast; ring,
        show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, ih.1, ih.2] at h
      rw [h, hermite_add_two]
      simp only [map_sub, map_mul, aeval_X, nsmul_eq_mul, map_natCast]
      push_cast
      ring
  exact (key n).1

end Hermite

end DLMF.Confluent
