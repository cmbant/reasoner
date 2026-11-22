/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic.Functions
public import DLMF.Confluent.Basic.KummerProperties
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Error, Dawson and Fresnel functions: basic properties (DLMF §7.2)

Values, derivatives, entireness, power series and real restrictions of the functions defined
in `DLMF.Confluent.Basic.ErrorFunctions` and `DLMF.ErrorFunctions.Basic.Functions`.

## Main results

* `erf_zero`: `erf 0 = 0`.
* `erf_eq_integral`, `erf_complex_segment_integral`: `erf z = (2/√π) ∫₀^z e^{-t²} dt`
  (DLMF 7.2.1), on the real line and along the segment.
* `erf_ofReal`, `erfc_ofReal`: on real arguments `erf` and `erfc` agree with TauCeti's
  `TauCeti.Real.erf` and `TauCeti.Real.erfc`.
* `hasDerivAt_erf_complex`, `hasDerivAt_dawsonF_complex`, `hasDerivAt_fresnelC_complex`,
  `hasDerivAt_fresnelS_complex`: the derivatives.
* `differentiable_erf_complex`, `faddeevaW_entire`, `dawsonF_entire`, `fresnelC_entire`,
  `fresnelS_entire`, `fresnelTail_entire`, `fresnelAuxiliaryFComplex_entire`,
  `fresnelAuxiliaryGComplex_entire`: these functions are entire (DLMF §7.2).
* `fresnelC_hasSum`, `fresnelS_hasSum`: the power series of `C(z)` and `S(z)`
  (DLMF 7.6.4, 7.6.6).
* `dawsonF_ofReal`, `fresnelC_ofReal`, `fresnelS_ofReal`, `fresnelAuxiliaryFComplex_ofReal`,
  `fresnelAuxiliaryGComplex_ofReal`: agreement with the real-variable definitions.
* `iteratedErfc_neg_one`: the initial repeated integral `i⁻¹ erfc z = (2/√π) e^{-z²}`.
* `Real.voigt_symmetry`: the parity of the Voigt functions in `x` (DLMF 7.19.6).

## Implementation notes

The integral representations DLMF 7.2.2–7.2.4, 7.2.6 and 7.2.12 and the bounds of `erf` and
`erfc` are in `DLMF.ErrorFunctions.AnalyticProperties`.
-/

public noncomputable section
open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Confluent

/-- `erf 0 = 0`. -/
theorem erf_zero : erf 0 = 0 := by simp [erf]

/-- Integral representation `erf z = (2/√π) ∫_0^z e^{-t²} dt`. -/
@[dlmf 7.2.E1]
theorem erf_eq_integral (z : ℝ) :
    erf z =
      (2 : ℂ) / (Real.sqrt π : ℂ) *
        ∫ t : ℝ in (0 : ℝ)..z, Complex.exp (-(t : ℂ) ^ 2) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ Set.uIcc (0 : ℝ) z) => (hasDerivAt_gaussianPrimitive (x : ℂ)).comp_ofReal)
    (show IntervalIntegrable (fun t : ℝ => exp (-(t : ℂ) ^ 2)) MeasureTheory.volume 0 z from
      Continuous.intervalIntegrable (by fun_prop) _ _)
  simpa [erf, mul_assoc] using congrArg (fun w : ℂ => (2 : ℂ) / Real.sqrt π * w) hi.symm

/-- The complex error function on real inputs agrees with TauCeti's real error function. -/
theorem erf_ofReal (x : ℝ) : erf x = (TauCeti.Real.erf x : ℂ) := by
  rw [erf_eq_integral, TauCeti.Real.erf_def]
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  congr 1
  funext t
  simp

/-- The complex complementary error function restricts to TauCeti's real complement. -/
theorem erfc_ofReal (x : ℝ) : erfc x = (TauCeti.Real.erfc x : ℂ) := by
  simp [erfc, erf_ofReal, TauCeti.Real.erfc_def]

/-- The proved Kummer Gaussian antiderivative gives the complex error-function derivative. -/
theorem hasDerivAt_erf_complex (z : ℂ) :
    HasDerivAt erf (2/Real.sqrt π*exp (-z^2)) z := by
  have he : erf = fun w : ℂ => (2/(Real.sqrt π:ℂ))*(w*kummerM (1/2) (3/2) (-w^2)) := by
    funext w
    unfold erf
    ring
  rw [he]
  exact (hasDerivAt_gaussianPrimitive z).const_mul _

/-- The complex error function is entire, directly from its Kummer derivative. -/
@[fun_prop] theorem differentiable_erf_complex : Differentiable ℂ erf :=
  fun z => (hasDerivAt_erf_complex z).differentiableAt

/-- Fresnel primitives differentiate to their entire cosine integrand. -/
theorem hasDerivAt_fresnelC_complex (z : ℂ) :
    HasDerivAt fresnelC (cos (π*z^2/2)) z :=
  hasDerivAt_primitive (by fun_prop) z

/-- Fresnel primitives differentiate to their entire sine integrand. -/
theorem hasDerivAt_fresnelS_complex (z : ℂ) :
    HasDerivAt fresnelS (sin (π*z^2/2)) z :=
  hasDerivAt_primitive (by fun_prop) z

/-- The series with terms `(fun n : ℕ => (-1 :
ℂ)^n*(π/2)^(2*n+0)*z^(4*n+1)/((2*n+0).factorial*(4*n+1 : ℂ)))` converges to `(fresnelC
z)`. -/
@[dlmf 7.6.E4]
theorem fresnelC_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*(π/2)^(2*n+0)*z^(4*n+1)/((2*n+0).factorial*(4*n+1 : ℂ)))
      (fresnelC z) := by
  have hs (w : ℂ) : HasSum (fun n : ℕ =>
      ((-1:ℂ)^n*(π/2:ℂ)^(2*n+0)/(2*n+0).factorial)*w^(2*(2*n+0)))
      (cos (π*w^2/2)) := by
    convert Complex.hasSum_cos (π*w^2/2) using 1
    funext n
    simp only [Nat.add_zero,div_pow,mul_pow,← pow_mul]
    ring
  have h := hasSum_primitive_monomials
    (fun n : ℕ=>(-1:ℂ)^n*(π/2:ℂ)^(2*n+0)/(2*n+0).factorial)
    (fun n=>2*(2*n+0)) hs z
  change HasSum _ (fresnelC z) at h
  refine h.congr_fun fun n=>?_
  rw [show 2*(2*n+0)+1=4*n+1 by omega]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The series with terms `(fun n : ℕ => (-1 :
ℂ)^n*(π/2)^(2*n+1)*z^(4*n+3)/((2*n+1).factorial*(4*n+3 : ℂ)))` converges to `(fresnelS
z)`. -/
@[dlmf 7.6.E6]
theorem fresnelS_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*(π/2)^(2*n+1)*z^(4*n+3)/((2*n+1).factorial*(4*n+3 : ℂ)))
      (fresnelS z) := by
  have hs (w : ℂ) : HasSum (fun n : ℕ =>
      ((-1:ℂ)^n*(π/2:ℂ)^(2*n+1)/(2*n+1).factorial)*w^(2*(2*n+1)))
      (sin (π*w^2/2)) := by
    convert Complex.hasSum_sin (π*w^2/2) using 1
    all_goals
      funext n
      simp only [Nat.add_zero,div_pow,mul_pow,← pow_mul]
      ring
  have h := hasSum_primitive_monomials
    (fun n : ℕ=>(-1:ℂ)^n*(π/2:ℂ)^(2*n+1)/(2*n+1).factorial)
    (fun n=>2*(2*n+1)) hs z
  change HasSum _ (fresnelS z) at h
  refine h.congr_fun fun n=>?_
  rw [show 2*(2*n+1)+1=4*n+3 by omega]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Dawson differentiation uses only the entire Gaussian primitive. -/
theorem hasDerivAt_dawsonF_complex (z : ℂ) :
    HasDerivAt dawsonF (1-2*z*dawsonF z) z := by
  have hd := (((hasDerivAt_id z).pow 2).neg.cexp).mul
    (hasDerivAt_primitive (by fun_prop : Differentiable ℂ (fun t : ℂ => exp (t^2))) z)
  have he : exp (-z^2)*exp (z^2)=1 := by rw [← Complex.exp_add]; simp
  refine hd.congr_deriv ?_
  dsimp [dawsonF]
  linear_combination he

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem faddeevaW_entire  :
    Differentiable ℂ faddeevaW := by
  unfold faddeevaW erfc
  fun_prop

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem dawsonF_entire  :
    Differentiable ℂ dawsonF := by
  exact fun z => (hasDerivAt_dawsonF_complex z).differentiableAt

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelC_entire  :
    Differentiable ℂ fresnelC := by
  exact differentiable_primitive (by fun_prop)

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelS_entire  :
    Differentiable ℂ fresnelS := by
  exact differentiable_primitive (by fun_prop)

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelTail_entire  :
    Differentiable ℂ fresnelTail := by
  unfold fresnelTail
  exact ((differentiable_const _).sub fresnelC_entire).sub (fresnelS_entire.const_mul I)

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelAuxiliaryFComplex_entire  :
    Differentiable ℂ fresnelAuxiliaryFComplex := by
  unfold fresnelAuxiliaryFComplex
  exact (((differentiable_const (1/2:ℂ)).sub fresnelS_entire).mul (by fun_prop)).sub
    (((differentiable_const (1/2:ℂ)).sub fresnelC_entire).mul (by fun_prop))

/-- Entire differentiability asserted in DLMF §7.2. -/
theorem fresnelAuxiliaryGComplex_entire  :
    Differentiable ℂ fresnelAuxiliaryGComplex := by
  unfold fresnelAuxiliaryGComplex
  exact (((differentiable_const (1/2:ℂ)).sub fresnelC_entire).mul (by fun_prop)).add
    (((differentiable_const (1/2:ℂ)).sub fresnelS_entire).mul (by fun_prop))

/-- Agreement with the existing real-variable definition. -/
theorem dawsonF_ofReal (x : ℝ) :
    dawsonF x = (Real.dawsonF x : ℂ) := by
  rw [dawsonF, primitive_ofReal, Real.dawsonF, Complex.ofReal_mul,
    ← intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]

/-- Agreement with the existing real-variable definition. -/
theorem fresnelC_ofReal (x : ℝ) :
    fresnelC x = (Real.fresnelC x : ℂ) := by
  rw [fresnelC, primitive_ofReal, Real.fresnelC, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  push_cast
  rfl

/-- Agreement with the existing real-variable definition. -/
theorem fresnelS_ofReal (x : ℝ) :
    fresnelS x = (Real.fresnelS x : ℂ) := by
  rw [fresnelS, primitive_ofReal, Real.fresnelS, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  push_cast
  rfl

/-- Agreement with the existing real-variable definition. -/
theorem fresnelAuxiliaryFComplex_ofReal (x : ℝ) :
    fresnelAuxiliaryFComplex x = (fresnelAuxiliaryF x : ℂ) := by
  simp only [fresnelAuxiliaryFComplex, fresnelAuxiliaryF, fresnelC_ofReal, fresnelS_ofReal]
  push_cast
  rfl

/-- Agreement with the existing real-variable definition. -/
theorem fresnelAuxiliaryGComplex_ofReal (x : ℝ) :
    fresnelAuxiliaryGComplex x = (fresnelAuxiliaryG x : ℂ) := by
  simp only [fresnelAuxiliaryGComplex, fresnelAuxiliaryG, fresnelC_ofReal, fresnelS_ofReal]
  push_cast
  rfl

/-- Identity under the stated parameter and domain assumptions: `erf z = 2/Real.sqrt π*primitive
(fun t => exp (-t^2)) z`. -/
@[dlmf 7.2.E1]
theorem erf_complex_segment_integral (z : ℂ) :
    erf z = 2/Real.sqrt π*primitive (fun t => exp (-t^2)) z := by
  have h := primitive_eq_sub hasDerivAt_gaussianPrimitive z
  simp only [zero_mul, sub_zero] at h
  rw [h, erf]
  ring

/-- The repeated integral of index `-1` is the Gaussian `(2/√π) e^{-z²}` (DLMF 7.18.1). -/
@[simp]
theorem iteratedErfc_neg_one (z : ℂ) : iteratedErfc (-1) z = 2/Real.sqrt π*exp (-z^2) := by
  simp [iteratedErfc]

/-- Identity under the stated parameter and domain assumptions: `Real.voigtU (-x) t=Real.voigtU x
t ∧ Real.voigtV (-x) t = -Real.voigtV x t`. -/
@[dlmf 7.19.E6]
theorem Real.voigt_symmetry (x : ℝ) {t : ℝ} :
    Real.voigtU (-x) t=Real.voigtU x t ∧ Real.voigtV (-x) t = -Real.voigtV x t := by
  constructor
  · rw [Real.voigtU, Real.voigtU, ← integral_neg_eq_self]
    congr 1; congr 1; funext y
    rw [show -x - -y = -(x-y) by ring, neg_sq, neg_sq]
  · rw [Real.voigtV, Real.voigtV, ← integral_neg_eq_self, ← mul_neg, ← integral_neg]
    congr 1; congr 1; funext y
    rw [show -(-x - -y)^2 = -(x-y)^2 by ring, neg_sq]
    ring

end DLMF.Confluent
