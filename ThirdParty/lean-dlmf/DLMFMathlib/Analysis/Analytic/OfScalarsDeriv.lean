/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic

/-!
# Termwise calculus of scalar power series

For `f : ℂ → ℂ` represented on a ball by the scalar power series `∑ cₙ zⁿ` (`ofScalars ℂ c`),
the derivative is represented by `∑ (n + 1) c_{n+1} zⁿ`, and multiplication by `z` shifts the
coefficients back. A quadratic recurrence for the coefficients then gives a second-order linear
differential equation, the mechanism behind the hypergeometric and confluent hypergeometric
equations.

## Main results

* `HasFPowerSeriesOnBall.deriv_ofScalars`: termwise differentiation.
* `HasFPowerSeriesOnBall.hasSum_mul_pow`, `HasSum.mul_pow_shift`,
  `HasFPowerSeriesOnBall.hasSum_z_mul_deriv`: the series sums of `f`, of a shifted series and of
  `z f'`.
* `HasFPowerSeriesOnBall.ode_of_recurrence`: a quadratic coefficient recurrence gives a
  second-order differential equation.
-/

@[expose] public section

open FormalMultilinearSeries
open scoped ENNReal

noncomputable section

/-- Termwise differentiation, as a direct scalar specialization of Mathlib's
`HasFPowerSeriesOnBall.fderiv`. -/
theorem HasFPowerSeriesOnBall.deriv_ofScalars {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) :
    HasFPowerSeriesOnBall (deriv f) (ofScalars ℂ (fun n => (n + 1) * c (n + 1))) 0 r := by
  have hd := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv
  have heq : (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
      (ofScalars ℂ c).derivSeries = ofScalars ℂ (fun n => (n + 1) * c (n + 1)) := by
    ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    rw [apply_eq_prod_smul_coeff]
    simp [derivSeries_coeff_one, coeff_ofScalars, ofScalars, mul_comm]
  simpa only [heq, Function.comp_def, ContinuousLinearMap.apply_apply,
    fderiv_eq_deriv_mul, mul_one] using hd

/-- Scalar coefficients give the usual series sum on the ball. -/
theorem HasFPowerSeriesOnBall.hasSum_mul_pow {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) : HasSum (fun n => c n * z ^ n) (f z) := by
  simpa only [ofScalars_apply_eq, smul_eq_mul, zero_add] using h.hasSum hz

/-- Shifting a power series after multiplication by its variable. -/
theorem HasSum.mul_pow_shift {c : ℕ → ℂ} {s z : ℂ}
    (h : HasSum (fun n => c (n + 1) * z ^ n) s) (h0 : c 0 = 0) :
    HasSum (fun n => c n * z ^ n) (z * s) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa [Finset.sum_range_one, h0, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
    h.mul_left z

/-- Multiplying the differentiated series by `z` restores its original indexing. -/
theorem HasFPowerSeriesOnBall.hasSum_z_mul_deriv {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) :
    HasSum (fun n : ℕ => (n : ℂ) * c n * z ^ n) (z * deriv f z) := by
  apply HasSum.mul_pow_shift (c := fun n => (n : ℂ) * c n) ?_ (by simp)
  simpa only [Nat.cast_add, Nat.cast_one] using h.deriv_ofScalars.hasSum_mul_pow hz

/-- A quadratic coefficient recurrence gives a second-order differential equation.
This applies to both the Gauss and confluent hypergeometric series. -/
theorem HasFPowerSeriesOnBall.ode_of_recurrence {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) {A B C D : ℂ}
    (hrec : ∀ n : ℕ, (n + 1 : ℂ) * (D + n) * c (n + 1) =
      (A * n * (n - 1) + B * n + C) * c n) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) :
    z * (1 - A * z) * deriv (deriv f) z + (D - B * z) * deriv f z - C * f z = 0 := by
  have h0 := h.hasSum_mul_pow hz
  have h1 := h.deriv_ofScalars.hasSum_mul_pow hz
  have hz1 := h.hasSum_z_mul_deriv hz
  have hz2 := h.deriv_ofScalars.hasSum_z_mul_deriv hz
  have hzz2 : HasSum (fun n : ℕ => (n : ℂ) * (n - 1) * c n * z ^ n)
      (z ^ 2 * deriv (deriv f) z) := by
    have hs : HasSum (fun n : ℕ =>
        (n + 1 : ℂ) * ((n + 1 : ℂ) - 1) * c (n + 1) * z ^ n)
        (z * deriv (deriv f) z) := by
      convert hz2 using 1
      funext n
      ring
    have ht := HasSum.mul_pow_shift (c := fun n => (n : ℂ) * (n - 1) * c n)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hs) (by simp)
    convert ht using 1
    ring
  have hleft := hz2.add (h1.mul_left D)
  have hright := ((hzz2.mul_left A).add (hz1.mul_left B)).add (h0.mul_left C)
  have heq : (fun n : ℕ => (n : ℂ) * ((n + 1) * c (n + 1)) * z ^ n +
        D * ((n + 1) * c (n + 1) * z ^ n)) =
      (fun n : ℕ => (A * ((n : ℂ) * (n - 1) * c n * z ^ n) +
        B * ((n : ℂ) * c n * z ^ n)) + C * (c n * z ^ n)) := by
    funext n
    calc
      _ = ((n + 1 : ℂ) * (D + n) * c (n + 1)) * z ^ n := by ring
      _ = _ := by rw [hrec]; ring
  rw [heq] at hleft
  have he := hleft.unique hright
  linear_combination he
