/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.ExponentialIntegrals
-- PATCH: removed `public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral` (its only use, `Real.tendsto_sinIntegral_atTop`, is removed; closure 100+ modules)
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Real exponential, sine and cosine integrals: series and derivatives

Power series, derivatives, parity and the limit at infinity of the real-variable functions
`Ein`, `Si`, `Cin` and `Ci` defined in `DLMF.Confluent.Basic.ExponentialIntegrals`.

## Main results

* `Real.hasSum_expIntegralEin`, `Real.hasSum_sinIntegral`, `Real.hasSum_cosIntegralCin`,
  `Real.cosIntegral_eq_tsum`: the power series (DLMF 6.6.4–6.6.6).
* `Real.hasDerivAt_sinIntegral`, `Real.hasDerivAt_cosIntegral`: `Si' = sinc` and
  `Ci'(x) = cos x / x`.
* `Real.sinIntegral_neg`: `Si` is odd.
* `hasSum_intervalIntegral_of_dominated`: termwise integration of a dominated series.

## Implementation notes

The relations to `E₁` are in `DLMF.Confluent.ExpIntegral`.
-/

public section

open Complex Filter Set MeasureTheory
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Confluent

/-- For `t ≠ 0`, `(1 - e^{-t})/t = ∑_k (-1)^k t^k/(k+1)!`. -/
theorem hasSum_einIntegrand {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun k : ℕ => (-1) ^ k * t ^ k / (k + 1)!) ((1 - Real.exp (-t)) / t) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-t)
  rw [← Real.exp_eq_exp_ℝ, ← hasSum_nat_add_iff' 1] at h
  have h2 := h.mul_left (-1 / t)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at h2
  convert h2 using 1
  · funext k
    rw [pow_succ, neg_pow t k]
    field_simp
  · field_simp
    ring

/-- Termwise integration on `[0, x]` of a series dominated by a summable sequence. -/
theorem hasSum_intervalIntegral_of_dominated {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {b : ℕ → ℝ} (x : ℝ)
    (hF : ∀ k, Continuous (F k)) (hb : ∀ k t, |t| ≤ |x| → |F k t| ≤ b k) (hs : Summable b)
    (hlim : ∀ t, t ≠ 0 → HasSum (fun k => F k t) (f t)) :
    HasSum (fun k => ∫ t in (0 : ℝ)..x, F k t) (∫ t in (0 : ℝ)..x, f t) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => b k) (fun k => (hF k).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun t ht => ?_)
    (Eventually.of_forall fun t _ => hs) intervalIntegrable_const
    ((Measure.ae_ne volume 0).mono fun t ht _ => hlim t ht)
  refine (Real.norm_eq_abs _).symm ▸ hb k t ?_
  rcases ht with ⟨h1, h2⟩
  rcases le_total 0 x with hx | hx
  · simp only [hx, inf_of_le_left, sup_of_le_right] at h1 h2
    rw [abs_of_pos h1, abs_of_nonneg hx]; exact h2
  · simp only [hx, inf_of_le_right, sup_of_le_left] at h1 h2
    rw [abs_of_nonpos h2, abs_of_nonpos hx]; linarith

/-- **The power series of `Ein`** (DLMF 6.6.4):
`Ein(x) = ∑_{k≥0} (-1)^k x^{k+1} / ((k+1) (k+1)!)`. -/
@[dlmf 6.6.E4]
theorem Real.hasSum_expIntegralEin (x : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * x ^ (k + 1) / ((k + 1) * (k + 1)!))
        (Real.expIntegralEin x) := by
  have h := hasSum_intervalIntegral_of_dominated (F := fun k t =>
    (-1) ^ k * t ^ k / (k + 1)!) x (fun k => by fun_prop) (fun k t ht => ?_)
    (Real.summable_pow_div_factorial |x|) (fun t ht => hasSum_einIntegrand ht)
  · refine h.congr_fun fun k => ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
      Nat.abs_cast]
    have hf : (k ! : ℝ) ≤ (k + 1)! := by exact_mod_cast Nat.factorial_le (Nat.le_succ k)
    calc |t| ^ k / ((k + 1)! : ℝ) ≤ |x| ^ k / (k + 1)! := by gcongr
      _ ≤ |x| ^ k / k ! := by gcongr

/-- `Si'(x) = sinc x`. -/
theorem Real.hasDerivAt_sinIntegral (x : ℝ) : HasDerivAt Real.sinIntegral (Real.sinc x) x :=
  intervalIntegral.integral_hasDerivAt_right (Real.continuous_sinc.intervalIntegrable _ _)
    (Real.continuous_sinc.stronglyMeasurableAtFilter _ _) Real.continuous_sinc.continuousAt

/-- `Si` is odd. -/
theorem Real.sinIntegral_neg (x : ℝ) : Real.sinIntegral (-x) = -Real.sinIntegral x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) Real.sinc
  simp only [Real.sinc_neg, neg_zero] at h
  rw [Real.sinIntegral, Real.sinIntegral, h, intervalIntegral.integral_symm]

-- PATCH: removed (unused by the target; its closure is 100+ modules): `Real.tendsto_sinIntegral_atTop`, from TauCeti's Dirichlet integral. Upstream lines 107-110; see NOTICE.md

/-- **The power series of `Si`** (DLMF 6.6.5):
`Si(x) = ∑_{k≥0} (-1)^k x^{2k+1} / ((2k+1) (2k+1)!)`. -/
@[dlmf 6.6.E5]
theorem Real.hasSum_sinIntegral (x : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1) * (2 * k + 1)!))
      (Real.sinIntegral x) := by
  have h := hasSum_intervalIntegral_of_dominated (F := fun k t =>
    (-1) ^ k * t ^ (2 * k) / (2 * k + 1)!) (f := Real.sinc) (b := fun k => (x ^ 2) ^ k / k !) x
    (fun k => by fun_prop) (fun k t ht => ?_) (Real.summable_pow_div_factorial _)
    (fun t ht => ?_)
  · refine h.congr_fun fun k => ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring_nf
  · rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast,
      ← pow_mul, show x ^ (2 * k) = |x| ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
    have hf : (k ! : ℝ) ≤ (2 * k + 1)! := by exact_mod_cast Nat.factorial_le (by omega)
    calc |t| ^ (2 * k) / ((2 * k + 1)! : ℝ) ≤ |x| ^ (2 * k) / (2 * k + 1)! := by gcongr
      _ ≤ |x| ^ (2 * k) / k ! := by gcongr
  · have hs := (Real.hasSum_sin t).div_const t
    rw [← Real.sinc_of_ne_zero ht] at hs
    refine hs.congr_fun fun k => ?_
    rw [pow_succ]
    field_simp

/-- **The power series of `Cin`**: `Cin(x) = ∑_{k≥0} (-1)^k x^{2k+2} / ((2k+2) (2k+2)!)`. -/
theorem Real.hasSum_cosIntegralCin (x : ℝ) :
    HasSum (fun k : ℕ => (-1) ^ k * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!))
      (Real.cosIntegralCin x) := by
  have h := hasSum_intervalIntegral_of_dominated (F := fun k t =>
    (-1) ^ k * t ^ (2 * k + 1) / (2 * k + 2)!) (f := fun t => (1 - Real.cos t) / t)
    (b := fun k => |x| * (x ^ 2) ^ k / k !) x
    (fun k => by fun_prop) (fun k t ht => ?_)
    ((Real.summable_pow_div_factorial (x ^ 2)).mul_left |x| |>.congr fun k => by ring)
    (fun t ht => ?_)
  · refine h.congr_fun fun k => ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    have hk : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring_nf
  · rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast,
      ← sq_abs x, ← pow_mul, pow_succ]
    have hf : (k ! : ℝ) ≤ (2 * k + 2)! := by exact_mod_cast Nat.factorial_le (by omega)
    calc |t| ^ (2 * k) * |t| / ((2 * k + 2)! : ℝ) ≤ |x| ^ (2 * k) * |x| / (2 * k + 2)! := by
          gcongr
      _ ≤ |x| ^ (2 * k) * |x| / k ! := by gcongr
      _ = |x| * |x| ^ (2 * k) / k ! := by ring
  · have hc := (Real.hasSum_cos t)
    rw [← hasSum_nat_add_iff' 1] at hc
    have hs := (hc.neg.div_const t)
    simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one] at hs
    convert hs using 1
    · funext k
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_succ (-1 : ℝ), pow_succ t (2 * k + 1)]
      field_simp
    · ring

/-- **The power series of `Ci`** (DLMF 6.6.6): for `x > 0`,
`Ci(x) = γ + log x + ∑_{k≥0} (-1)^{k+1} x^{2k+2} / ((2k+2) (2k+2)!)`. -/
@[dlmf 6.6.E6]
theorem Real.cosIntegral_eq_tsum (x : ℝ) :
    Real.cosIntegral x = Real.eulerMascheroniConstant + Real.log x +
      ∑' k : ℕ, (-1) ^ (k + 1) * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!) := by
  rw [Real.cosIntegral, (Real.hasSum_cosIntegralCin x).tsum_eq.symm, ← tsum_neg]
  · have : (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!)) =
        fun k => -((-1) ^ k * x ^ (2 * k + 2) / ((2 * k + 2) * (2 * k + 2)!)) := by
      funext k; ring
    rw [this]
    ring

/-- `Ci'(x) = cos x / x` for `x > 0`. -/
theorem Real.hasDerivAt_cosIntegral {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.cosIntegral (Real.cos x / x) x := by
  have hcont : ContinuousOn (fun t : ℝ => (1 - Real.cos t) / t) (Set.Ioi 0) :=
    fun t ht => (by fun_prop (disch := exact (ne_of_gt ht)) :
      ContinuousAt (fun t : ℝ => (1 - Real.cos t) / t) t).continuousWithinAt
  have hCin : HasDerivAt Real.cosIntegralCin ((1 - Real.cos x) / x) x := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_
      (hcont.continuousAt (Ioi_mem_nhds hx))
    · refine (intervalIntegrable_const (c := |x|)).mono_fun'
        (by fun_prop : Measurable fun t : ℝ => (1 - Real.cos t) / t).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := by
        rcases ht with ⟨h1, _⟩
        exact lt_of_le_of_lt (le_min le_rfl hx.le) h1
      have htx : t ≤ x := by
        rcases ht with ⟨_, h2⟩
        exact h2.trans (max_le hx.le le_rfl)
      show ‖(1 - Real.cos t) / t‖ ≤ |x|
      have h1 := Real.one_sub_sq_div_two_le_cos (x := t)
      have h2 := Real.cos_le_one t
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, abs_of_nonneg (by linarith),
        div_le_iff₀ ht0, abs_of_pos hx]
      nlinarith
    · exact (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx)
  have h := (hCin.neg.add (Real.hasDerivAt_log hx.ne')).add_const Real.eulerMascheroniConstant
  refine h.congr_deriv ?_
  field_simp
  ring

end DLMF.Confluent
