/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import DLMFMathlib.Analysis.Analytic.OfScalarsDeriv
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# The Gauss series on the unit disk (DLMF §15.2(i))

Mathlib defines `ordinaryHypergeometric` (`₂F₁`) as the sum of the Gauss series and proves that
its radius of convergence is `1`, or `⊤` when the series terminates. This file collects the
series facts used throughout DLMF Chapter 15: the power-series representation on the disk, the
terminating case and absolute convergence on the unit circle. The scalar power-series calculus
behind the hypergeometric differential equations is in
`DLMFMathlib.Analysis.Analytic.OfScalarsDeriv`.

## Main results

* `ordinaryHypergeometricSeries_radius_ge_one`, `hasFPowerSeriesOnBall_ordinaryHypergeometric`:
  the Gauss series represents `₂F₁` on the unit disk.
* `analyticAt_ordinaryHypergeometric`: `₂F₁(a,b;c;·)` is analytic on the unit disk.
* `ordinaryHypergeometric_zero_left`: `₂F₁(0,b;c;z) = 1`.
* `ordinaryHypergeometric_eq_sum_neg_nat`: a terminating `₂F₁(-n,b;c;z)` is a polynomial,
  DLMF 15.2.4.
* `ordinaryHypergeometric_eq_one_sub_neg_cpow`: `₂F₁(a,c;c;z) = (1-z)^{-a}`, DLMF 15.4.6.
* `regularizedHGFun_eq_tsum'`: Mathlib's regularized `ₚF_q` as a `tsum` of its coefficients.
* `hasSum_pochhammer_div_factorial`: the binomial series `∑ (β)_n / n! z^n = (1-z)^{-β}`.
* `tendsto_gaussHypergeometricCoeff_div_cpow`: the normalized Gauss coefficients have a Gamma-ratio
  limit.
* `ordinaryHypergeometric_summable_of_mem_sphere`: absolute convergence on the unit circle,
  §15.2(i).

## Implementation notes

The value at zero is Mathlib's `ordinaryHypergeometric_zero` and the numerator symmetry of the
series is `ordinaryHypergeometricSeries_symm`. Further special values (DLMF §15.4) are in
`DLMF.Hypergeometric.Basic.SpecialValues`.
-/

public section

open Complex Filter Nat FormalMultilinearSeries
open scoped Topology Real ENNReal

noncomputable section

namespace DLMF.Hypergeometric

/-- Adding a natural number preserves exclusion of the nonpositive integers. -/
theorem not_neg_nat_add_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (m : ℕ) :
    ∀ k : ℕ, a + m ≠ -k := by
  intro k h
  apply ha (k + m)
  push_cast
  linear_combination h

/-- Helper lemma for series identities inside the unit disk. -/
theorem mem_eball_one_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    z ∈ Metric.eball (0 : ℂ) 1 := by
  rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
  exact ENNReal.coe_lt_coe.mpr (mod_cast hz)

/-- The Gauss series has radius at least one, including terminating numerator parameters. -/
theorem ordinaryHypergeometricSeries_radius_ge_one (a b c : ℂ) :
    1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ k : ℕ, a = -k
  · obtain ⟨k, rfl⟩ := ha
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact le_top
  by_cases hb : ∃ k : ℕ, b = -k
  · obtain ⟨k, rfl⟩ := hb
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₂]
    exact le_top
  by_cases hc : ∃ k : ℕ, c = -k
  · obtain ⟨k, rfl⟩ := hc
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₃]
    exact le_top
  rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c]
  · intro k
    exact ⟨fun h => ha ⟨k, by linear_combination h⟩,
      fun h => hb ⟨k, by linear_combination h⟩,
      fun h => hc ⟨k, by linear_combination h⟩⟩

/-- The Gauss series represents `₂F₁` throughout the open unit disk. -/
theorem hasFPowerSeriesOnBall_ordinaryHypergeometric (a b c : ℂ) :
    HasFPowerSeriesOnBall (₂F₁ a b c) (ofScalars ℂ (gaussHypergeometricCoeff a b c)) 0 1 := by
  have hr := ordinaryHypergeometricSeries_radius_ge_one a b c
  have h := ((ordinaryHypergeometricSeries ℂ a b c).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by simp) hr)).mono (by simp) hr
  change HasFPowerSeriesOnBall (₂F₁ a b c) (ordinaryHypergeometricSeries ℂ a b c) 0 1 at h
  have heq : ordinaryHypergeometricCoefficient a b c = gaussHypergeometricCoeff a b c :=
    funext (ordinaryHypergeometricCoefficient_eq a b c)
  simpa only [ordinaryHypergeometricSeries, heq] using h

/-- Absolute summability of the Gauss series inside the unit disk. -/
theorem summable_norm_gaussHypergeometricCoeff_mul_pow (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖gaussHypergeometricCoeff a b c n * z ^ n‖ := by
  have h := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hr : (‖z‖₊ : ENNReal) < (ofScalars ℂ (gaussHypergeometricCoeff a b c)).radius := by
    refine lt_of_lt_of_le ?_ h.r_le
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    exact hz
  refine ((ofScalars ℂ (gaussHypergeometricCoeff a b c)).summable_norm_mul_pow hr).congr
    fun n => ?_
  rw [ofScalars_norm, norm_mul, norm_pow, coe_nnnorm]

/-- Helper lemma for generating-function estimates. -/
theorem pochhammer_eval_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_nonneg ih (add_nonneg hx (Nat.cast_nonneg n))

/-- Helper lemma for generating-function estimates. -/
theorem norm_pochhammer_le (z : ℂ) (n : ℕ) :
    ‖pochhammer z n‖ ≤ (ascPochhammer ℝ n).eval ‖z‖ := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, norm_mul, ascPochhammer_succ_eval]
    have hle : ‖z + n‖ ≤ ‖z‖ + n := by
      calc
        ‖z + (n : ℂ)‖ ≤ ‖z‖ + ‖(n : ℂ)‖ := norm_add_le _ _
        _ = ‖z‖ + n := by simp
    have hnn : 0 ≤ (ascPochhammer ℝ n).eval ‖z‖ := pochhammer_eval_nonneg (norm_nonneg z) n
    exact mul_le_mul ih hle (norm_nonneg _) hnn

/-- Helper lemma for generating-function estimates. -/
theorem pochhammer_eval_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    (ascPochhammer ℝ n).eval x ≤ (ascPochhammer ℝ n).eval y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact mul_le_mul ih (add_le_add hxy le_rfl)
      (add_nonneg hx (Nat.cast_nonneg n)) (pochhammer_eval_nonneg (le_trans hx hxy) n)

/-- `₂F₁(a, b; c; ·)` is analytic on the open unit disk. -/
theorem analyticAt_ordinaryHypergeometric {a b c z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (₂F₁ a b c) z :=
  (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
    (mem_eball_one_of_norm_lt_one hz)

/-- The series `₂F₁(0,b;c;z)` terminates after the constant term. -/
theorem ordinaryHypergeometric_zero_left (b c z : ℂ) : ₂F₁ (0 : ℂ) b c z = 1 := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  have h : (fun n : ℕ =>
      (n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval 0 * (ascPochhammer ℂ n).eval b *
        ((ascPochhammer ℂ n).eval c)⁻¹ * z ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp
  rw [h, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- Helper lemma for Chu–Vandermonde and the shifted Legendre evaluation. -/
theorem gaussHypergeometricCoeff_neg_nat (n : ℕ) (b c : ℂ) (k : ℕ) :
    gaussHypergeometricCoeff (-(n : ℂ)) b c k =
      (-1 : ℂ) ^ k * n.choose k * pochhammer b k / pochhammer c k := by
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [gaussHypergeometricCoeff, pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field [hk]

/-- A terminating `₂F₁(-n,b;c;z)` is a polynomial of degree at most `n`. -/
@[dlmf 15.2.E4]
theorem ordinaryHypergeometric_eq_sum_neg_nat (n : ℕ) (b c z : ℂ) :
    ₂F₁ (-(n : ℂ)) b c z =
      ∑ k ∈ Finset.range (n + 1), gaussHypergeometricCoeff (-(n : ℂ)) b c k * z ^ k := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  have hterm : (fun k : ℕ =>
      (k !⁻¹ : ℂ) * (ascPochhammer ℂ k).eval (-(n : ℂ)) *
        (ascPochhammer ℂ k).eval b * ((ascPochhammer ℂ k).eval c)⁻¹ * z ^ k) =
      fun k => gaussHypergeometricCoeff (-(n : ℂ)) b c k * z ^ k := by
    funext k
    simp [gaussHypergeometricCoeff, pochhammer, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hterm]
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [gaussHypergeometricCoeff, pochhammer_neg_nat_eq_zero hkn]

/-- Cancelling equal upper and lower parameters identifies the hypergeometric power series
with the binomial series composed with negation. -/
theorem ordinaryHypergeometricSeries_eq_binomialSeries_comp {a c : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    ordinaryHypergeometricSeries ℂ a c c =
      (binomialSeries ℂ (-a)).compContinuousLinearMap (-1 : ℂ →L[ℂ] ℂ) := by
  rw [binomialSeries_eq_ordinaryHypergeometricSeries (a := -a) hc,
    FormalMultilinearSeries.compContinuousLinearMap_comp]
  have hid : (-ContinuousLinearMap.id ℂ ℂ).comp (-1 : ℂ →L[ℂ] ℂ) =
      ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp
  rw [neg_neg, hid, FormalMultilinearSeries.compContinuousLinearMap_id]

/-- AAR (2.1.6): `₂F₁(a,c;c;z) = (1-z)^{-a}` for `|z| < 1`. -/
@[dlmf 15.4.E6]
theorem ordinaryHypergeometric_eq_one_sub_neg_cpow {a c z : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) (hz : ‖z‖ < 1) :
    ₂F₁ a c c z = (1 - z) ^ (-a) := by
  have h0 : HasFPowerSeriesOnBall (fun x : ℂ => (1 + x) ^ (-a))
      (binomialSeries ℂ (-a)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero (a := -a)
  have hfps : HasFPowerSeriesOnBall (fun x : ℂ => (1 - x) ^ (-a))
      (ordinaryHypergeometricSeries ℂ a c c) 0 1 := by
    rw [ordinaryHypergeometricSeries_eq_binomialSeries_comp hc]
    simpa [Function.comp_def, sub_eq_add_neg] using
      h0.compContinuousLinearMap (u := (-1 : ℂ →L[ℂ] ℂ)) (x := (0 : ℂ))
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one hz
  have hs : HasSum (fun n : ℕ => ordinaryHypergeometricSeries ℂ a c c n fun _ => z)
      ((1 - z) ^ (-a)) := by
    simpa using hfps.hasSum hz'
  have hmem : z ∈ Metric.eball (0 : ℂ) (ordinaryHypergeometricSeries ℂ a c c).radius :=
    Metric.eball_subset_eball hfps.r_le hz'
  exact ((ordinaryHypergeometricSeries ℂ a c c).hasSum hmem).unique hs

/-- Euler's Gamma approximants written using Pochhammer symbols. -/
theorem GammaSeq_eq_pochhammer (s : ℂ) (n : ℕ) :
    GammaSeq s n = (n : ℂ) ^ s * n.factorial / (pochhammer s n * (s + n)) := by
  have hp (k : ℕ) : (∏ j ∈ Finset.range k, (s + j)) = pochhammer s k := by
    induction k with
    | zero => simp [pochhammer_zero]
    | succ k ih => rw [Finset.prod_range_succ, ih, pochhammer_succ]
  rw [GammaSeq, hp, pochhammer_succ]

/-- The normalized Gauss coefficients have a finite Gamma-ratio limit. -/
theorem tendsto_gaussHypergeometricCoeff_div_cpow {a b c : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) :
    Tendsto (fun n : ℕ => gaussHypergeometricCoeff a b c n / (n : ℂ) ^ (a + b - c - 1))
      atTop (𝓝 (Gamma c / (Gamma a * Gamma b))) := by
  have hlim (s : ℂ) : Tendsto (fun n : ℕ => 1 + s / (n : ℂ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat s).const_add 1
  have ht := ((hlim c).div ((hlim a).mul (hlim b)) (by norm_num)).mul
    ((GammaSeq_tendsto_Gamma c).div
      ((GammaSeq_tendsto_Gamma a).mul (GammaSeq_tendsto_Gamma b))
      (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb)))
  simp only [mul_one, div_one, one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs (s : ℂ) (h : ∀ k : ℕ, s ≠ -k) : s + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using h n
  have hp (s : ℂ) : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
  simp only [Pi.div_apply]
  rw [GammaSeq_eq_pochhammer, GammaSeq_eq_pochhammer, GammaSeq_eq_pochhammer,
    gaussHypergeometricCoeff, cpow_sub _ _ hn0, cpow_sub _ _ hn0, cpow_add _ _ hn0, cpow_one]
  field [hn0, hs a ha, hs b hb, hs c hc,
    show (n : ℂ) + a ≠ 0 by simpa only [add_comm] using hs a ha,
    show (n : ℂ) + b ≠ 0 by simpa only [add_comm] using hs b hb, hp a, hp b, hp c,
    pochhammer_ne_zero_of_not_neg_nat ha n, pochhammer_ne_zero_of_not_neg_nat hb n,
    pochhammer_ne_zero_of_not_neg_nat hc n, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- AAR Theorem 2.1.2 (absolute convergence on the unit circle). -/
@[dlmf 15.2.i]
theorem ordinaryHypergeometric_summable_of_mem_sphere {a b c z : ℂ}
    (hz : ‖z‖ = 1) (h : 0 < (c - a - b).re) :
    Summable fun n : ℕ => gaussHypergeometricCoeff a b c n * z ^ n := by
  have hfinite (k : ℕ) (hk : a = -k ∨ b = -k ∨ c = -k) :
      Summable fun n : ℕ => gaussHypergeometricCoeff a b c n * z ^ n := by
    apply (summable_nat_add_iff (k + 1)).mp
    have he : (fun n : ℕ => gaussHypergeometricCoeff a b c (n + (k + 1)) * z ^ (n + (k + 1))) =
        fun _ => (0 : ℂ) := by
      funext n
      have hn : k < n + (k + 1) := by omega
      rcases hk with rfl | rfl | rfl <;>
          simp [gaussHypergeometricCoeff, pochhammer_neg_nat_eq_zero hn]
    rw [he]
    exact summable_zero
  by_cases ha : ∀ k : ℕ, a ≠ -k
  · by_cases hb : ∀ k : ℕ, b ≠ -k
    · by_cases hc : ∀ k : ℕ, c ≠ -k
      · have ht := (tendsto_gaussHypergeometricCoeff_div_cpow ha hb hc).norm
        have hlim : Tendsto (fun n : ℕ => ‖gaussHypergeometricCoeff a b c n‖ /
            (n : ℝ) ^ (a + b - c - 1).re) atTop (𝓝 ‖Gamma c / (Gamma a * Gamma b)‖) := by
          apply ht.congr'
          filter_upwards [eventually_gt_atTop 0] with n hn
          rw [norm_div, norm_natCast_cpow_of_pos hn]
        have hs : Summable (fun n : ℕ => ‖gaussHypergeometricCoeff a b c n‖) :=
          summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by
            simp only [sub_re, add_re, one_re] at h ⊢; linarith))
            (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow hlim)
        apply Summable.of_norm
        simpa only [norm_mul, norm_pow, hz, one_pow, mul_one] using hs
      · push Not at hc
        obtain ⟨k, hk⟩ := hc
        exact hfinite k (Or.inr (Or.inr hk))
    · push Not at hb
      obtain ⟨k, hk⟩ := hb
      exact hfinite k (Or.inr (Or.inl hk))
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    exact hfinite k (Or.inl hk)

/-- Helper lemma for binomial expansions of `(1-z)^{-β}`. -/
theorem gaussHypergeometricCoeff_self_right (β : ℂ) (n : ℕ) :
    gaussHypergeometricCoeff β 1 1 n = pochhammer β n / n.factorial := by
  have h1 : pochhammer (1 : ℂ) n = n.factorial := pochhammer_nat_one n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp [gaussHypergeometricCoeff, h1]
  field [hf]

/-- Helper lemma for binomial expansions of `(1-z)^{-β}`. -/
theorem one_not_neg_nat : ∀ k : ℕ, (1 : ℂ) ≠ -k := by
  intro k h
  have : (1 : ℝ) = -k := by simpa using congrArg Complex.re h
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The binomial series `∑ (β)_n / n! z^n = (1-z)^{-β}` for `|z| < 1`. -/
theorem hasSum_pochhammer_div_factorial {β z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => pochhammer β n / n.factorial * z ^ n) ((1 - z) ^ (-β)) := by
  have hc : ∀ k : ℕ, (k : ℂ) ≠ -(1 : ℂ) := fun k hk =>
    one_not_neg_nat k (neg_eq_iff_eq_neg.mp hk.symm)
  have hval := ordinaryHypergeometric_eq_one_sub_neg_cpow (a := β) (c := 1) hc hz
  have hs := (hasFPowerSeriesOnBall_ordinaryHypergeometric β 1 1).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz)
  have hfun : (fun n : ℕ => gaussHypergeometricCoeff β 1 1 n * z ^ n) =
      fun n => pochhammer β n / n.factorial * z ^ n := by
    funext n
    rw [gaussHypergeometricCoeff_self_right]
  rwa [hfun, hval] at hs

/-- The regularized function as a `tsum` of its coefficients. -/
theorem regularizedHGFun_eq_tsum' (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun a b z = ∑' n : ℕ, regularizedHGFunCoeff a b n * z ^ n := by
  simp only [regularizedHGFun, FormalMultilinearSeries.sum, regularizedHGFunSeries,
    ofScalars_apply_eq, smul_eq_mul]

end DLMF.Hypergeometric
