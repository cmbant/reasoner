/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.PrincipalBranch
public import DLMF.Hypergeometric.Basic.ParameterAnalyticity
public import DLMF.Hypergeometric.Basic.GaussEquation
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Gauss function on the cut plane (DLMF §§15.2(i), 15.6)

Euler's integral represents `₂F₁` on the unit disk for `Re c > Re b > 0`. Its regularized form
`regularizedGaussHypergeometricIntegral` is analytic on the cut plane `ℂ ∖ [1, ∞)`, and the
contiguous shifts of `regularizedGaussHypergeometric` reduce every parameter triple to that region.
This file proves that `regularizedGaussHypergeometric` is the analytic continuation of Mathlib's
`regularizedGaussHGFun` to the cut plane.

## Main results

* `ordinaryHypergeometric_eq_integral`: Euler's integral, DLMF 15.6.1 (AAR Theorem 2.2.1).
* `regularizedGaussHypergeometricIntegral_eq_regularizedGaussHypergeometricFun`,
  `analyticOnNhd_regularizedGaussHypergeometricIntegral`: Euler's integral agrees with `𝐅` on the
  disk and is analytic on the cut plane for `Re b > 0`, `Re (c - b) > 0`.
* `regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun`,
  `analyticOnNhd_regularizedGaussHypergeometric`, `regularizedGaussHypergeometric_unique`: agreement
  with `𝐅` on the disk, analyticity on the cut plane and uniqueness characterize the continuation.
* `regularizedGaussHypergeometric_zero_of_regular`: `𝐅(a,b;c;0) = 1/Γ(c)` for regular `c`.
* `regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral`: the continuation is
  Euler's integral on the whole cut plane.
* `ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric`: `₂F₁ = Γ(c) 𝐅` on the disk.
* `regularizedGaussHypergeometric_symm`: symmetry in `a` and `b`.
* `deriv_regularizedGaussHypergeometric`, `iteratedDeriv_regularizedGaussHypergeometric`: DLMF
  15.5.1–15.5.2 on the cut plane.
* `regularizedGaussHypergeometric_ode`: the hypergeometric equation DLMF 15.10.1 on the cut plane.
* `regularizedGaussHypergeometric_neg_nat`: DLMF 15.2.3_5 on the cut plane.

## Implementation notes

`cutPlane = {z | 1 - z ∈ slitPlane}` is open and star-shaped about `0`, so the identity
principle `eqOn_cutPlane_of_eqOn_disk` lifts every identity from the unit disk. The contiguous
relations and transformations on the cut plane are in `DLMF.Hypergeometric.ArgumentContinuation`.
-/

public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Real Nat Topology Interval ComplexOrder

noncomputable section

namespace DLMF.Hypergeometric

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`. -/
theorem re_c_pos_of {b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re) : 0 < c.re := by
  have : c.re = b.re + (c - b).re := by simp [sub_re]
  linarith

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`. -/
theorem not_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) : ∀ k : ℕ, w ≠ -k := by
  intro k hk
  have : w.re = -k := by simpa using congrArg Complex.re hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`.
AAR's binomial expansion of `(1-zt)^{-a}` on `t ∈ [0,1]`. -/
theorem hasSum_one_sub_mul_cpow {a z : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => pochhammer a n / n.factorial * (z * t) ^ n) ((1 - z * t) ^ (-a)) := by
  have hzt : ‖z * (t : ℂ)‖ < 1 := by
    rw [norm_mul]
    have htnorm : ‖(t : ℂ)‖ = |t| := by simp
    rw [htnorm]
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    nlinarith [norm_nonneg z, hz, abs_nonneg t]
  simpa using hasSum_pochhammer_div_factorial (β := a) (z := z * t) hzt

/-- Helper lemma for `ordinaryHypergeometric_eq_integral`. -/
theorem euler_term_eq_gaussHypergeometricCoeff {a b c : ℂ} (n : ℕ)
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) :
    Gamma c / (Gamma b * Gamma (c - b)) *
        (pochhammer a n / n.factorial * betaIntegral (b + n) (c - b)) =
      gaussHypergeometricCoeff a b c n := by
  have hb' : 0 < (b + n).re := by
    have : (b + n).re = b.re + n := by simp
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hGamma := Gamma_mul_Gamma_eq_betaIntegral hb' hcb
  have hcpos := re_c_pos_of hb hcb
  have hc : ∀ k : ℕ, c ≠ -k := not_neg_nat_of_re_pos hcpos
  have hbn : ∀ k : ℕ, b ≠ -k := not_neg_nat_of_re_pos hb
  have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hc n)
  have hb0 : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hc0 : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hcpos
  have hcb0 : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hbeta : betaIntegral (b + n) (c - b) =
      Gamma (b + n) * Gamma (c - b) / Gamma (c + n) := by
    have hsum : b + n + (c - b) = c + n := by ring
    rw [hsum] at hGamma
    exact eq_div_of_mul_eq hcn (by rw [mul_comm]; exact hGamma.symm)
  have hpochb : Gamma (b + n) / Gamma b = pochhammer b n := Gamma_add_nat_div_Gamma_eq b hbn
  have hpochc : Gamma (c + n) / Gamma c = pochhammer c n := Gamma_add_nat_div_Gamma_eq c hc
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hcp : pochhammer c n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hc n
  have hbmul : Gamma (b + n) = pochhammer b n * Gamma b := (div_eq_iff hb0).mp hpochb
  have hcmul : Gamma (c + n) = pochhammer c n * Gamma c := (div_eq_iff hc0).mp hpochc
  rw [hbeta, gaussHypergeometricCoeff, hbmul, hcmul]
  field [hb0, hc0, hcb0, hcn, hf, hcp]

/-- Euler's integral representation of `₂F₁`, AAR Theorem 2.2.1. -/
@[dlmf 15.6.E1]
theorem ordinaryHypergeometric_eq_integral {a b c z : ℂ}
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : ‖z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c / (Gamma b * Gamma (c - b)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  let d : ℕ → ℂ := fun n => pochhammer a n / n.factorial * z ^ n
  let F : ℕ → ℝ → ℂ := fun n t => w t * (d n * (t : ℂ) ^ n)
  have hw : IntervalIntegrable w volume 0 1 := betaIntegral_convergent hb hcb
  have hd : Summable (fun n => ‖d n‖) := (hasSum_pochhammer_div_factorial (β := a) hz).summable.norm
  have hFi (n : ℕ) : IntervalIntegrable (F n) volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (F := F) (f := fun t => w t * (1 - z * t) ^ (-a))
    (fun n t => ‖d n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hd.mul_right ‖w t‖)
    (by
      simp_rw [tsum_mul_right]
      exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t ht => ?_)
  · have hterm (n : ℕ) :
        ∫ t : ℝ in (0 : ℝ)..1, F n t =
          (pochhammer a n / n.factorial * betaIntegral (b + n) (c - b)) * z ^ n := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
      have hp : (t : ℂ) ^ (b + n - 1) = (t : ℂ) ^ (b - 1) * (t : ℂ) ^ n := by
        rw [show b + n - 1 = (b - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
      dsimp [F, w, d]
      rw [hp]
      ring
    have hs' := hs.mul_left (Gamma c / (Gamma b * Gamma (c - b)))
    have hscaled (n : ℕ) : Gamma c / (Gamma b * Gamma (c - b)) *
        (∫ t : ℝ in (0 : ℝ)..1, F n t) = gaussHypergeometricCoeff a b c n * z ^ n := by
      rw [hterm, ← mul_assoc, euler_term_eq_gaussHypergeometricCoeff n hb hcb]
    simp_rw [hscaled] at hs'
    exact ((hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
      (mem_eball_one_of_norm_lt_one hz)).unique hs'
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    calc
      ‖F n t‖ = ‖w t‖ * (‖d n‖ * ‖(t : ℂ)‖ ^ n) := by
        simp only [F, norm_mul, norm_pow]
      _ ≤ ‖w t‖ * (‖d n‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht1) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h := (hasSum_one_sub_mul_cpow (a := a) ht' hz).mul_left (w t)
    simpa only [F, d, mul_pow, mul_assoc] using h

/-- On the unit disk the Euler integral is the regularized Gauss function. -/
theorem regularizedGaussHypergeometricIntegral_eq_regularizedGaussHypergeometricFun {a b c : ℂ}
    (hb : 0 < b.re)
    (hcb : 0 < (c - b).re)
    {z : ℂ} (hz : ‖z‖ < 1) : regularizedGaussHypergeometricIntegral a b c z
        = regularizedGaussHGFun a b c z := by
  have hc := not_neg_nat_of_re_pos (re_c_pos_of hb hcb)
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hb)
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hcb)
  rw [regularizedGaussHypergeometricFun_eq_div_Gamma hc,
      ordinaryHypergeometric_eq_integral hb hcb hz,
    regularizedGaussHypergeometricIntegral]
  simp only [eulerKernel]
  set I := ∫ t : ℝ in (0 : ℝ)..1,
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) with hI
  field_simp

/-- For `z` in the cut plane, `t ↦ (1 - z t)^s` is continuous on `[0, 1]`. -/
theorem continuousOn_one_sub_mul_cpow {z : ℂ} (hz : z ∈ cutPlane) (s : ℂ) :
    ContinuousOn (fun t : ℝ => (1 - z * t) ^ s) (Icc (0 : ℝ) 1) :=
  (continuousOn_const.sub (continuousOn_const.mul continuous_ofReal.continuousOn)).cpow
    continuousOn_const (fun _ ht => one_sub_mul_mem_slitPlane hz ht)

/-- For `Re c > Re b > 0` and `z` in the cut plane, the Euler kernel is integrable on `[0, 1]`. -/
theorem intervalIntegrable_eulerKernel {a b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re)
    {z : ℂ} (hz : z ∈ cutPlane) : IntervalIntegrable (eulerKernel a b c z) volume 0 1 := by
  have h := (betaIntegral_convergent hb hcb).mul_continuousOn
    (by rw [uIcc_of_le zero_le_one]; exact continuousOn_one_sub_mul_cpow hz (-a))
  exact h

/-- For `z` in the cut plane and `t ∈ [0, 1]`, the Euler kernel is complex-differentiable in `z`,
  with derivative `eulerKernelDeriv`. -/
theorem hasDerivAt_eulerKernel {a b c z : ℂ} (hz : z ∈ cutPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun w => eulerKernel a b c w t) (eulerKernelDeriv a b c z t) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w * (t : ℂ)) (-(1 * (t : ℂ))) z :=
    ((hasDerivAt_id' z).mul_const _).const_sub 1
  have h2 := h1.cpow_const (c := -a) (one_sub_mul_mem_slitPlane hz ht)
  exact h2.const_mul _

/-- Differentiation under the integral sign for Euler's integral. -/
theorem hasDerivAt_integral_eulerKernel {a b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re)
    {z₀ : ℂ} (hz₀ : z₀ ∈ cutPlane) :
    HasDerivAt (fun z => ∫ t : ℝ in (0 : ℝ)..1, eulerKernel a b c z t)
      (∫ t : ℝ in (0 : ℝ)..1, eulerKernelDeriv a b c z₀ t) z₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_cutPlane z₀ hz₀
  have hclosed : Metric.closedBall z₀ (ε / 2) ⊆ cutPlane :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hsub : Metric.ball z₀ (ε / 2) ⊆ cutPlane := Metric.ball_subset_closedBall.trans hclosed
  -- a uniform bound for the `z`-dependent factor of the derivative
  set G : ℝ × ℂ → ℂ := fun p => -a * (1 - p.2 * p.1) ^ (-a - 1) * -(1 * (p.1 : ℂ)) with hG
  have hGcont : ContinuousOn G (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z₀ (ε / 2)) := by
    have hpow : ContinuousOn (fun p : ℝ × ℂ => (1 - p.2 * p.1) ^ (-a - 1))
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z₀ (ε / 2)) := by
      refine (continuousOn_const.sub (continuous_snd.continuousOn.mul
        (continuous_ofReal.comp continuous_fst).continuousOn)).cpow continuousOn_const ?_
      intro p hp
      exact one_sub_mul_mem_slitPlane (hclosed hp.2) hp.1
    exact (continuousOn_const.mul hpow).mul
      (continuousOn_const.mul (continuous_ofReal.comp continuous_fst).continuousOn).neg
  obtain ⟨C, hC⟩
      := (isCompact_Icc.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    hGcont
  have hbeta := betaIntegral_convergent hb hcb
  have hIoc : ∀ t ∈ Ι (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => by
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  have hderiv_int : ∀ z ∈ Metric.closedBall z₀ (ε / 2),
      IntervalIntegrable (eulerKernelDeriv a b c z) volume 0 1 := by
    intro z hz
    refine hbeta.mul_continuousOn ?_
    rw [uIcc_of_le zero_le_one]
    have : ContinuousOn (fun t : ℝ => G (t, z)) (Icc (0 : ℝ) 1) :=
      hGcont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht, hz⟩)
    exact this
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun z t => eulerKernel a b c z t)
    (F' := fun z t => eulerKernelDeriv a b c z t) (bound := fun t =>
      ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ * C)
    (Metric.ball_mem_nhds z₀ (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [Metric.ball_mem_nhds z₀ (half_pos hε)] with z hz
    exact (intervalIntegrable_iff.mp (intervalIntegrable_eulerKernel hb hcb (hsub hz))).1
  · exact intervalIntegrable_eulerKernel hb hcb hz₀
  · exact (intervalIntegrable_iff.mp
      (hderiv_int z₀ (Metric.mem_closedBall_self (half_pos hε).le))).1
  · refine ae_of_all _ fun t ht z hz => ?_
    have ht' := hIoc t ht
    show ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * G (t, z)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC (t, z) ⟨ht', Metric.ball_subset_closedBall hz⟩)
      (norm_nonneg _)
  · exact hbeta.norm.mul_const C
  · refine ae_of_all _ fun t ht z hz => ?_
    exact hasDerivAt_eulerKernel (hsub hz) (hIoc t ht)

/-- Euler's integral is analytic in `z` on the cut plane when `Re b > 0`, `Re (c - b) > 0`. -/
theorem analyticOnNhd_regularizedGaussHypergeometricIntegral (a : ℂ) {b c : ℂ} (hb : 0 < b.re)
    (hcb : 0 < (c - b).re) :
    AnalyticOnNhd ℂ (regularizedGaussHypergeometricIntegral a b c) cutPlane := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_cutPlane
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold regularizedGaussHypergeometricIntegral
  exact (differentiableAt_const _).mul (hasDerivAt_integral_eulerKernel hb hcb hz).differentiableAt

/-- For `x > 0`, `⌈x - 1⌉₊ < ⌈x⌉₊`. -/
theorem ceil_sub_one_lt_ceil {x : ℝ} (hx : 0 < x) : ⌈x - 1⌉₊ < ⌈x⌉₊ := by
  have h1 : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
  have : ⌈x - 1⌉₊ ≤ ⌈x⌉₊ - 1 :=
    Nat.ceil_le.mpr (by push_cast [Nat.cast_sub h1]; linarith [Nat.le_ceil x])
  omega

/-- Raising `c` by one decreases a positive `c`-shift count. -/
theorem shiftC_add_one_lt {b c : ℂ} (h : 0 < shiftC b c) : shiftC b (c + 1) < shiftC b c := by
  have hx : 0 < 1 + (shiftB b : ℝ) - (c - b).re := Nat.ceil_pos.mp h
  have : 1 + (shiftB b : ℝ) - (c + 1 - b).re = 1 + (shiftB b : ℝ) - (c - b).re - 1 := by
    simp only [sub_re, add_re, one_re]; ring
  unfold shiftC
  rw [this]
  exact ceil_sub_one_lt_ceil hx

/-- Raising `b` by one decreases a positive `b`-shift count. -/
theorem shiftB_add_one_lt {b : ℂ} (h : 0 < shiftB b) : shiftB (b + 1) < shiftB b := by
  have hx : 0 < 1 - b.re := Nat.ceil_pos.mp h
  have : 1 - (b + 1).re = 1 - b.re - 1 := by simp only [add_re, one_re]; ring
  unfold shiftB
  rw [this]
  exact ceil_sub_one_lt_ceil hx

/-- No `c`-shift is needed when `Re (c - b) ≥ 1 + shiftB b`. -/
theorem shiftC_eq_zero_of {b c : ℂ} (h : (c - b).re ≥ 1 + shiftB b) : shiftC b c = 0 := by
  unfold shiftC
  rw [Nat.ceil_eq_zero]
  linarith

/-- When both shift counts vanish, `Re b ≥ 1` and `Re (c - b) ≥ 1`, so Euler's integral applies. -/
theorem euler_region_of_shift_eq_zero {b c : ℂ} (hB : shiftB b = 0) (hC : shiftC b c = 0) :
    1 ≤ b.re ∧ 1 ≤ (c - b).re := by
  have hB' : 1 - b.re ≤ 0 := Nat.ceil_eq_zero.mp hB
  have hC' : 1 + (shiftB b : ℝ) - (c - b).re ≤ 0 := Nat.ceil_eq_zero.mp hC
  rw [hB, Nat.cast_zero] at hC'
  constructor <;> linarith

/-- Unfolding the recursion when a `c`-shift is needed: the contiguous relation in `c`. -/
theorem regularizedGaussHypergeometricByShifts_succ_of_pos_c {n : ℕ} {a b c z : ℂ}
    (h : 0 < shiftC b c) :
    regularizedGaussHypergeometricByShifts (n + 1) a b c z =
      (c - a) * regularizedGaussHypergeometricByShifts n a b (c + 1) z + a
          * regularizedGaussHypergeometricByShifts n (a + 1) b (c + 1) z := by
  simp only [regularizedGaussHypergeometricByShifts, h, ↓reduceIte]

/-- Unfolding the recursion when only a `b`-shift is needed: the contiguous relation in `b`. -/
lemma regularizedGaussHypergeometricByShifts_succ_of_pos_b {n : ℕ} {a b c z : ℂ}
    (hc : ¬ 0 < shiftC b c)
    (hb : 0 < shiftB b) :
    regularizedGaussHypergeometricByShifts (n + 1) a b c z =
      regularizedGaussHypergeometricByShifts n a (b + 1) c z - a * z
          * regularizedGaussHypergeometricByShifts n (a + 1) (b + 1) (c + 1) z := by
  simp only [regularizedGaussHypergeometricByShifts, hc, hb, ↓reduceIte]

/-- Unfolding the recursion when no shift is needed: Euler's integral. -/
theorem regularizedGaussHypergeometricByShifts_succ_of_zero {n : ℕ} {a b c z : ℂ}
    (hc : ¬ 0 < shiftC b c)
    (hb : ¬ 0 < shiftB b) : regularizedGaussHypergeometricByShifts (n + 1) a b c z
        = regularizedGaussHypergeometricIntegral a b c z := by
  simp only [regularizedGaussHypergeometricByShifts, hc, hb, ↓reduceIte]

/-- The measures of the recursive calls in the `b`-shift branch. -/
theorem shiftMeasure_b_step {b c : ℂ} (hc : ¬ 0 < shiftC b c) (hb : 0 < shiftB b) :
    shiftMeasure (b + 1) c < shiftMeasure b c ∧
      shiftMeasure (b + 1) (c + 1) < shiftMeasure b c := by
  have hC0 : shiftC b c = 0 := Nat.eq_zero_of_not_pos hc
  have hlt := shiftB_add_one_lt hb
  have hre : c.re - b.re ≥ 1 + shiftB b := by
    have := (Nat.ceil_eq_zero.mp hC0 : 1 + (shiftB b : ℝ) - (c - b).re ≤ 0)
    simp only [sub_re] at this
    linarith
  have hB' : (shiftB (b + 1) : ℝ) + 1 ≤ shiftB b := by exact_mod_cast hlt
  have h1 : shiftC (b + 1) c = 0 := by
    apply shiftC_eq_zero_of
    simp only [sub_re, add_re, one_re]
    linarith
  have h2 : shiftC (b + 1) (c + 1) = 0 := by
    apply shiftC_eq_zero_of
    simp only [sub_re, add_re, one_re]
    linarith
  unfold shiftMeasure
  rw [h1, h2, hC0]
  omega

/-- On the unit disk, every stage of the recursion agrees with `𝐅` once the fuel suffices. -/
lemma regularizedGaussHypergeometricByShifts_eq_regularized (n : ℕ) {a b c : ℂ}
    (hn : shiftMeasure b c ≤ n) {z : ℂ}
    (hz : ‖z‖ < 1) : regularizedGaussHypergeometricByShifts n a b c z =
        regularizedGaussHGFun a b c z := by
  induction n generalizing a b c with
  | zero =>
    have h0 : shiftB b = 0 ∧ shiftC b c = 0 := by unfold shiftMeasure at hn; omega
    obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero h0.1 h0.2
    exact regularizedGaussHypergeometricIntegral_eq_regularizedGaussHypergeometricFun (by linarith)
        (by linarith) hz
  | succ n ih =>
    by_cases hc : 0 < shiftC b c
    · rw [regularizedGaussHypergeometricByShifts_succ_of_pos_c hc]
      have hlt := shiftC_add_one_lt hc
      have hn' : shiftMeasure b (c + 1) ≤ n := by unfold shiftMeasure at hn ⊢; omega
      rw [ih hn', ih hn', regularizedGaussHypergeometricFun_contiguous_c a b c hz]
    · by_cases hb : 0 < shiftB b
      · rw [regularizedGaussHypergeometricByShifts_succ_of_pos_b hc hb]
        obtain ⟨hm1, hm2⟩ := shiftMeasure_b_step hc hb
        rw [ih (a := a) (b := b + 1) (c := c) (by omega),
          ih (a := a + 1) (b := b + 1) (c := c + 1) (by omega)]
        linear_combination (-1 : ℂ) * regularizedGaussHypergeometricFun_contiguous_shift_b a b c hz
      · rw [regularizedGaussHypergeometricByShifts_succ_of_zero hc hb]
        obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero (Nat.eq_zero_of_not_pos hb)
          (Nat.eq_zero_of_not_pos hc)
        exact regularizedGaussHypergeometricIntegral_eq_regularizedGaussHypergeometricFun
            (by linarith) (by linarith) hz

/-- Every stage of the recursion is analytic on the cut plane once the fuel suffices. -/
lemma analyticOnNhd_regularizedGaussHypergeometricAux (n : ℕ) {a b c : ℂ}
    (hn : shiftMeasure b c ≤ n) :
    AnalyticOnNhd ℂ (fun z => regularizedGaussHypergeometricByShifts n a b c z) cutPlane := by
  induction n generalizing a b c with
  | zero =>
    have h0 : shiftB b = 0 ∧ shiftC b c = 0 := by unfold shiftMeasure at hn; omega
    obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero h0.1 h0.2
    exact analyticOnNhd_regularizedGaussHypergeometricIntegral a (by linarith) (by linarith)
  | succ n ih =>
    by_cases hc : 0 < shiftC b c
    · simp_rw [regularizedGaussHypergeometricByShifts_succ_of_pos_c hc]
      have hlt := shiftC_add_one_lt hc
      have hn' : shiftMeasure b (c + 1) ≤ n := by unfold shiftMeasure at hn ⊢; omega
      exact (analyticOnNhd_const.mul (ih hn')).add (analyticOnNhd_const.mul (ih hn'))
    · by_cases hb : 0 < shiftB b
      · simp_rw [regularizedGaussHypergeometricByShifts_succ_of_pos_b hc hb]
        obtain ⟨hm1, hm2⟩ := shiftMeasure_b_step hc hb
        exact (ih (a := a) (b := b + 1) (c := c) (by omega)).sub
          ((analyticOnNhd_const.mul analyticOnNhd_id).mul
            (ih (a := a + 1) (b := b + 1) (c := c + 1) (by omega)))
      · simp_rw [regularizedGaussHypergeometricByShifts_succ_of_zero hc hb]
        obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero (Nat.eq_zero_of_not_pos hb)
          (Nat.eq_zero_of_not_pos hc)
        exact analyticOnNhd_regularizedGaussHypergeometricIntegral a (by linarith) (by linarith)

/-- On the unit disk the continuation is the regularized Gauss series. -/
theorem regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    regularizedGaussHypergeometric a b c z = regularizedGaussHGFun a b c z :=
  regularizedGaussHypergeometricByShifts_eq_regularized _ le_rfl hz

/-- The continuation is analytic on the cut plane. -/
theorem analyticOnNhd_regularizedGaussHypergeometric (a b c : ℂ) : AnalyticOnNhd ℂ
    (regularizedGaussHypergeometric a b c)
    cutPlane :=
  analyticOnNhd_regularizedGaussHypergeometricAux _ le_rfl

/-- The continued regularized function `𝐅(a, b; c; z)` is analytic on the cut plane. -/
@[fun_prop]
theorem analyticAt_regularizedGaussHypergeometric (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    AnalyticAt ℂ (regularizedGaussHypergeometric a b c) z :=
  analyticOnNhd_regularizedGaussHypergeometric a b c z hz

/-- The continued regularized function `𝐅(a, b; c; z)` is differentiable on the cut plane. -/
@[fun_prop]
theorem differentiableAt_regularizedGaussHypergeometric (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    DifferentiableAt ℂ (regularizedGaussHypergeometric a b c) z :=
  (analyticAt_regularizedGaussHypergeometric a b c hz).differentiableAt

/-- Uniqueness: any function analytic on the cut plane that agrees with `𝐅` on the unit disk
is the continuation. -/
theorem regularizedGaussHypergeometric_unique {a b c : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f cutPlane)
    (h : ∀ z : ℂ, ‖z‖ < 1 → f z = regularizedGaussHGFun a b c z) :
    EqOn f (regularizedGaussHypergeometric a b c) cutPlane :=
  eqOn_cutPlane_of_eqOn_disk hf (analyticOnNhd_regularizedGaussHypergeometric a b c) fun z hz =>
    (h z hz).trans (regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun a b c
        hz).symm

/-- The continuation equals the Euler integral on the whole cut plane, for `Re b > 0` and
`Re (c - b) > 0`. -/
theorem regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricIntegral {a b c : ℂ}
    (hb : 0 < b.re)
    (hcb : 0 < (c - b).re) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHypergeometric a b c z = regularizedGaussHypergeometricIntegral a b c z :=
  (regularizedGaussHypergeometric_unique
      (analyticOnNhd_regularizedGaussHypergeometricIntegral a hb hcb)
    (fun _ hw => regularizedGaussHypergeometricIntegral_eq_regularizedGaussHypergeometricFun hb
        hcb hw) hz).symm

/-- The classical `₂F₁` on the unit disk is `Γ(c)` times the continuation. -/
theorem ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    {z : ℂ} (hz : ‖z‖ < 1) : ₂F₁ a b c z = Gamma c * regularizedGaussHypergeometric a b c z := by
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun a b c hz,
      regularizedGaussHypergeometricFun_eq_div_Gamma hc,
    mul_div_cancel₀ _ (Gamma_ne_zero hc)]

/-- Symmetry `𝐅(a,b;c;z) = 𝐅(b,a;c;z)` on the cut plane. -/
theorem regularizedGaussHypergeometric_symm (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHypergeometric a b c z = regularizedGaussHypergeometric b a c z :=
  eqOn_cutPlane_of_eqOn_disk (analyticOnNhd_regularizedGaussHypergeometric a b c)
      (analyticOnNhd_regularizedGaussHypergeometric b a c)
    (fun z hz => by rw
        [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun a b c hz,
            regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun b a c hz,
      regularizedGaussHGFun_symm]) hz

/-- 15.5.1 on the cut plane: `𝐅'(a,b;c;z) = a b 𝐅(a+1,b+1;c+1;z)`. -/
theorem deriv_regularizedGaussHypergeometric (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    deriv (regularizedGaussHypergeometric a b c) z = a * b *
        regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) z :=
  eqOn_cutPlane_of_eqOn_disk (f := deriv (regularizedGaussHypergeometric a b c))
    (g := fun z => a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) z)
    (analyticOnNhd_regularizedGaussHypergeometric a b c).deriv
        (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      have heq : regularizedGaussHypergeometric a b c =ᶠ[𝓝 z] regularizedGaussHGFun a b c := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
        exact regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun a b c hw
      rw [heq.deriv_eq, deriv_regularizedGaussHypergeometricFun a b c hz,
          regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz])
    hz

/-- 15.5.2 on the cut plane: `𝐅⁽ⁿ⁾(a,b;c;z) = (a)ₙ (b)ₙ 𝐅(a+n,b+n;c+n;z)`. -/
theorem iteratedDeriv_regularizedGaussHypergeometric (a b c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ cutPlane) :
    iteratedDeriv n (regularizedGaussHypergeometric a b c) z =
      pochhammer a n * pochhammer b n *
          regularizedGaussHypergeometric (a + n) (b + n) (c + n) z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, pochhammer_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (regularizedGaussHypergeometric a b c) =ᶠ[𝓝 z]
        fun w => pochhammer a n * pochhammer b n *
            regularizedGaussHypergeometric (a + n) (b + n) (c + n) w := by
      filter_upwards [isOpen_cutPlane.mem_nhds hz] with w hw
      exact ih hw
    rw [heq.deriv_eq, deriv_const_mul _ (differentiableAt_regularizedGaussHypergeometric _ _ _ hz),
      deriv_regularizedGaussHypergeometric _ _ _ hz, pochhammer_succ, pochhammer_succ,
      show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
      show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring,
      show c + ((n + 1 : ℕ) : ℂ) = c + n + 1 by push_cast; ring]
    ring

/-- `𝐅(a,b;c;0) = 1/Γ(c)` for regular `c`. -/
theorem regularizedGaussHypergeometricFun_zero_of_regular {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    regularizedGaussHGFun a b c 0 = 1/Gamma c := by
  rw [regularizedGaussHypergeometricFun_eq_div_Gamma hc, ordinaryHypergeometric_zero]

/-- `𝐅(a,b;c;0) = 1/Γ(c)` for regular `c`, on the cut plane. -/
theorem regularizedGaussHypergeometric_zero_of_regular {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    regularizedGaussHypergeometric a b c 0 = 1/Gamma c := by
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ (by simp),
    regularizedGaussHypergeometricFun_zero_of_regular hc]

/-- The hypergeometric equation (DLMF 15.10.1) for the continuation `𝐅` on the cut plane, with
`𝐅'` and `𝐅''` written through 15.5.1–15.5.2. -/
@[dlmf 15.10.E1]
theorem regularizedGaussHypergeometric_ode (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    z * (1 - z) * (pochhammer a 2 * pochhammer b 2 *
        regularizedGaussHypergeometric (a + 2) (b + 2) (c + 2) z) +
      (c - (a + b + 1) * z) * (a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) z) -
      a * b * regularizedGaussHypergeometric a b c z = 0 := by
  have hdisk : ∀ w : ℂ, ‖w‖ < 1 →
      w * (1 - w) * (pochhammer a 2 * pochhammer b 2 *
          regularizedGaussHGFun (a + 2) (b + 2) (c + 2) w) +
        (c - (a + b + 1) * w) * (a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) w) -
        a * b * regularizedGaussHGFun a b c w = 0 := by
    intro w hw
    have h := regularizedGaussHypergeometricFun_ode a b c hw
    have h2 := iteratedDeriv_regularizedGaussHypergeometricFun a b c 2 hw
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h2
    rw [h2, deriv_regularizedGaussHypergeometricFun a b c hw] at h
    push_cast at h
    linear_combination h
  refine eqOn_cutPlane_of_eqOn_disk
    (f := fun z =>
      z * (1 - z) * (pochhammer a 2 * pochhammer b 2 *
          regularizedGaussHypergeometric (a + 2) (b + 2) (c + 2) z) +
        (c - (a + b + 1) * z) * (a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) z) -
        a * b * regularizedGaussHypergeometric a b c z) (g := fun _ => 0)
    (by intro z hz; fun_prop (disch := assumption)) analyticOnNhd_const (fun w hw => ?_) hz
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hw,
    regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hw,
    regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hw]
  exact hdisk w hw

/-- DLMF 15.2.3_5 on the cut plane: `𝐅(a,b;-n;z) = (a)ₙ₊₁ (b)ₙ₊₁ zⁿ⁺¹ 𝐅(a+n+1,b+n+1;n+2;z)`. -/
@[dlmf 15.2.E3_5]
theorem regularizedGaussHypergeometric_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHypergeometric a b (-n) z = pochhammer a (n + 1) *
        pochhammer b (n + 1) * z ^ (n + 1) *
      regularizedGaussHypergeometric (a + n + 1) (b + n + 1) (n + 2) z := by
  refine eqOn_cutPlane_of_eqOn_disk (f := regularizedGaussHypergeometric a b (-n))
    (g := fun z => pochhammer a (n + 1) * pochhammer b (n + 1) * z ^ (n + 1) *
      regularizedGaussHypergeometric (a + n + 1) (b + n + 1) (n + 2) z)
    (analyticOnNhd_regularizedGaussHypergeometric _ _ _)
    (by intro z hz; fun_prop (disch := assumption)) (fun z hz => ?_) hz
  have hc : ∀ k : ℕ, ((n : ℂ) + 2) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz,
      regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz,
    regularized_at_neg_nat a b n hz, regularizedGaussHypergeometricFun_eq_div_Gamma hc,
    show (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  push_cast
  ring

end DLMF.Hypergeometric
