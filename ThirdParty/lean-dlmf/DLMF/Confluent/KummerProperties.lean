/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic
public import DLMF.ErrorFunctions.Basic.Properties

public import DLMF.Hypergeometric.EulerIntegral
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
-- PATCH: removed `public import TauCeti.Analysis.SpecialFunctions.Erf` (unused: no declaration of that module occurs in the file)

/-!
# Properties of Kummer's function

This file develops further properties of Kummer's function `M(a,c,z) = ₁F₁(a;c;z)`
(AAR §4.1): the coefficient form of Kummer's transformation, confluence from Gauss's function,
Euler's integral, and parabolic zero-free regions (AAR §4.16).

## Main results

* `kummerMCoeff_kummer_convolution`: the Chu–Vandermonde evaluation of the coefficient
  convolution in Kummer's transformation.
* `tendsto_ordinaryHypergeometric_div_atTop`: confluence,
  `M(a,c,z) = lim_{b→∞} ₂F₁(a,b;c;z/b)`.
* `kummerM_eq_euler_integral`: Euler's integral for `M` (DLMF 13.4.1).
* `SaffVarga.partialSums`: the Saff–Varga theorem for partial sums (AAR Theorem 4.16.1).
* `kummerM_ne_zero_of_mem_parabolicRegion`: the parabolic zero-free regions of AAR
  Corollary 4.16.4.

## Implementation notes

The canonical definitions are in `DLMF.Confluent.Basic`. The series, Kummer's equation,
Kummer's transformation and the relation to Mathlib's regularized `regularizedHGFun {a} {c}`
are in `DLMF.Confluent.Basic.KummerProperties`; the error-function bridges to TauCeti are in
`DLMF.ErrorFunctions.Basic.Properties`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §§4.1, 4.16.
-/

public section

open Complex Filter intervalIntegral
open scoped Real Nat Topology ENNReal
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- Chu–Vandermonde evaluates the coefficient convolution in Kummer's transformation. -/
theorem kummerMCoeff_kummer_convolution {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      kummerMCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial) =
      kummerMCoeff a c n := by
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      kummerMCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial =
        gaussHypergeometricCoeff (-(n : ℂ)) (c - a) c k / n.factorial := by
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hnk : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
    have hch : (n.choose k : ℂ) = n.factorial / (k.factorial * (n - k).factorial) := by
      apply (eq_div_iff (mul_ne_zero hk0 hnk)).2
      simpa [mul_assoc] using congrArg (Nat.cast : ℕ → ℂ)
        (Nat.choose_mul_factorial_mul_factorial hk')
    rw [gaussHypergeometricCoeff_neg_nat, hch]
    unfold kummerMCoeff
    field [hn, hk0, hnk, pochhammer_ne_zero_of_not_neg_nat hc k]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hv := chu_vandermonde n (b := c - a) hc
  rw [ordinaryHypergeometric_eq_sum_neg_nat] at hv
  simp only [one_pow, mul_one, sub_sub_cancel] at hv
  rw [hv]
  unfold kummerMCoeff
  ring

/-- The normalized Pochhammer factors have a recurrence with limit multiplier one. -/
theorem pochhammer_div_pow_succ {b : ℂ} (hb : b ≠ 0) (n : ℕ) :
    pochhammer b (n + 1) / b ^ (n + 1) = (pochhammer b n / b ^ n) * (1 + (n : ℂ) / b) := by
  rw [pochhammer_succ, pow_succ]
  field_simp

/-- Each normalized Pochhammer symbol tends to one as its parameter tends to infinity. -/
theorem tendsto_pochhammer_div_pow (n : ℕ) :
    Tendsto (fun b : ℕ => pochhammer (b : ℂ) n / (b : ℂ) ^ n) atTop (𝓝 1) := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    have ht := ih.mul ((tendsto_const_div_atTop_nhds_zero_nat (n : ℂ)).const_add 1)
    simp only [add_zero, mul_one] at ht
    apply ht.congr'
    filter_upwards [Filter.eventually_ne_atTop 0] with b hb
    exact (pochhammer_div_pow_succ (Nat.cast_ne_zero.mpr hb) n).symm

/-- `(c + t)_k / t^k → 1` as the real variable `t → ∞`. -/
theorem tendsto_pochhammer_add_div_pow (c : ℂ) (k : ℕ) :
    Tendsto (fun t : ℝ => pochhammer (c + t) k / (t : ℂ) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp [pochhammer_zero]
  | succ k ih =>
    have h0 : Tendsto (fun t : ℝ => (c + k) / (t : ℂ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : Tendsto (fun t : ℝ => ‖c + k‖ / t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_div, norm_real, Real.norm_of_nonneg ht.le]
    have ht := ih.mul (h0.const_add 1)
    simp only [add_zero, mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [pochhammer_succ, pow_succ]
    field_simp
    ring

/-- `(-N)_k / (-N)^k → 1` as the natural number `N → ∞`. -/
theorem tendsto_pochhammer_neg_div_pow (k : ℕ) :
    Tendsto (fun N : ℕ => pochhammer (-(N : ℂ)) k / (-(N : ℂ)) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp [pochhammer_zero]
  | succ k ih =>
    have h0 : Tendsto (fun N : ℕ => -((k : ℂ) / N)) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (k : ℂ)).neg
    have ht := ih.mul (h0.const_add 1)
    simp only [add_zero, mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [pochhammer_succ, pow_succ]
    field_simp
    ring

/-- Normalized positive Pochhammer symbols decrease as the parameter increases. -/
theorem norm_pochhammer_div_pow_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (n : ℕ) :
    ‖pochhammer (y : ℂ) n / (y : ℂ) ^ n‖ ≤ ‖pochhammer (x : ℂ) n / (x : ℂ) ^ n‖ := by
  have hy : 0 < y := hx.trans_le hxy
  have hnorm (t : ℝ) (ht : 0 < t) (k : ℕ) :
      ‖1 + (k : ℂ) / (t : ℂ)‖ = 1 + (k : ℝ) / t := by
    have he : (1 : ℂ) + k / (t : ℂ) = ((1 + (k : ℝ) / t : ℝ) : ℂ) := by push_cast; rfl
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_div_pow_succ (ofReal_ne_zero.mpr (ne_of_gt hy)),
      pochhammer_div_pow_succ (ofReal_ne_zero.mpr (ne_of_gt hx)), norm_mul, norm_mul,
          hnorm y hy, hnorm x hx]
    exact mul_le_mul ih (add_le_add_right (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hx hxy) 1)
      (by positivity) (norm_nonneg _)

/-- Rescaled Gauss coefficients separate into confluent coefficients and a normalized Pochhammer. -/
theorem gaussHypergeometricCoeff_mul_div_pow (a b c z : ℂ) (n : ℕ) :
    gaussHypergeometricCoeff a b c n * (z / b) ^ n =
      (kummerMCoeff a c n * z ^ n) * (pochhammer b n / b ^ n) := by
  simp only [gaussHypergeometricCoeff, kummerMCoeff, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Confluence: `M(a,c,z) = lim_{b→∞} ₂F₁(a,b;c;z/b)`. -/
theorem tendsto_ordinaryHypergeometric_div_atTop {a c z : ℂ} :
    Tendsto (fun b : ℕ => ₂F₁ a (b : ℂ) c (z / b)) atTop (𝓝 (kummerM a c z)) := by
  obtain ⟨B, hB⟩ := exists_nat_gt ‖z‖
  have hBpos : (0 : ℝ) < B := (norm_nonneg z).trans_lt hB
  have harg : ‖z / (B : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_natCast, div_lt_one hBpos]
    exact hB
  let f (b n : ℕ) := gaussHypergeometricCoeff a (b : ℂ) c n * (z / b) ^ n
  let bound (n : ℕ) := ‖f B n‖
  have hsum : Summable bound :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric a (B : ℂ) c).hasSum_mul_pow
      (mem_eball_one_of_norm_lt_one harg)).summable.norm
  have hlim (n : ℕ) : Tendsto (fun b => f b n) atTop (𝓝 (kummerMCoeff a c n * z ^ n)) := by
    simpa only [f, gaussHypergeometricCoeff_mul_div_pow, mul_one] using
      (tendsto_pochhammer_div_pow n).const_mul (kummerMCoeff a c n * z ^ n)
  have hbound : ∀ᶠ b : ℕ in atTop, ∀ n, ‖f b n‖ ≤ bound n := by
    filter_upwards [eventually_ge_atTop B] with b hb n
    dsimp [bound, f]
    simp only [gaussHypergeometricCoeff_mul_div_pow, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa only [ofReal_natCast] using norm_pochhammer_div_pow_le hBpos (Nat.cast_le.mpr hb) n
  have ht := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  have he (b : ℕ) : ₂F₁ a (b : ℂ) c (z / b) = ∑' n, f b n := by
    rw [ordinaryHypergeometric_eq_tsum]
    apply tsum_congr
    intro n
    simp only [f, gaussHypergeometricCoeff, pochhammer, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [← he, kummerM, kummerMCoeff] using ht

/-- Euler's integral for Kummer's function, obtained by integrating the exponential
series against the beta weight (AAR §4.2). This is the `M` form of DLMF 13.4.1. -/
@[dlmf 13.4.E1]
theorem kummerM_eq_euler_integral {a c z : ℂ}
    (ha : 0 < a.re) (hca : 0 < (c - a).re) :
    kummerM a c z = Gamma c / (Gamma a * Gamma (c - a)) *
      ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (c - a - 1) * exp (z * t) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (c - a - 1)
  let d : ℕ → ℂ := fun n => z ^ n / n.factorial
  let F : ℕ → ℝ → ℂ := fun n t => w t * (d n * (t : ℂ) ^ n)
  have hexp (u : ℂ) : HasSum (fun n : ℕ => u ^ n / n.factorial) (exp u) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp u
  have hw : IntervalIntegrable w MeasureTheory.volume 0 1 := betaIntegral_convergent ha hca
  have hd : Summable (fun n => ‖d n‖) := (hexp z).summable.norm
  have hFi (n : ℕ) : IntervalIntegrable (F n) MeasureTheory.volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (F := F) (f := fun t => w t * exp (z * t))
    (fun n t => ‖d n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hd.mul_right ‖w t‖)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t _ => ?_)
  · have hterm (n : ℕ) : ∫ t : ℝ in (0 : ℝ)..1, F n t =
        betaIntegral (a + n) (c - a) / n.factorial * z ^ n := by
      rw [betaIntegral, div_eq_mul_inv, ← intervalIntegral.integral_mul_const,
        ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have hp : (t : ℂ) ^ (a + n - 1) = (t : ℂ) ^ (a - 1) * (t : ℂ) ^ n := by
        rw [show a + n - 1 = (a - 1) + n by ring,
          cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne'), cpow_natCast]
      dsimp [F, w, d]
      rw [hp]
      ring
    have hscaled (n : ℕ) : Gamma c / (Gamma a * Gamma (c - a)) *
        (∫ t : ℝ in (0 : ℝ)..1, F n t) = kummerMCoeff a c n * z ^ n := by
      have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      have he := euler_term_eq_gaussHypergeometricCoeff (a := 1) n ha hca
      simp only [pochhammer_nat_one, div_self hf, one_mul, gaussHypergeometricCoeff] at he
      rw [hterm]
      dsimp [kummerMCoeff]
      linear_combination (norm := (field_simp; ring)) (z ^ n / n.factorial) * he
    have hs' := hs.mul_left (Gamma c / (Gamma a * Gamma (c - a)))
    simp_rw [hscaled] at hs'
    exact hs'.tsum_eq
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
  · convert (hexp (z * t)).mul_left (w t) using 1
    congr 1
    funext n
    simp only [F, d, mul_pow]
    ring

section ParabolicRegion

/-! Saff–Varga zero-free parabolic regions (AAR §4.16); helpers in `SaffVarga`. -/

open Set Metric
open scoped NNReal

/-- The basic step of Saff–Varga: if `z` lies in the parabolic region `P_α` and `Re β ≥ α > 0`,
then `z + β ≠ 0` and `Re (z / (z + β)) < 1`. -/
theorem SaffVarga.step {α : ℝ} (hα : 0 < α) {z β : ℂ} (hz : z.im ^ 2 < 4 * α * (z.re + α))
    (hβ : α ≤ β.re) : z + β ≠ 0 ∧ (z / (z + β)).re < 1 := by
  have key : 0 < z.re * β.re + z.im * β.im + (β.re ^ 2 + β.im ^ 2) := by
    have h1 : 0 < z.re + β.re + α := by nlinarith [sq_nonneg z.im]
    have h2 : α * (z.re + α) ≤ β.re * (z.re + β.re) := by nlinarith
    nlinarith [sq_nonneg (β.im + z.im / 2)]
  have hne : z + β ≠ 0 := by
    intro h
    have hb : β = -z := by linear_combination h
    rw [hb] at key
    simp at key
    nlinarith
  refine ⟨hne, ?_⟩
  have hn : 0 < Complex.normSq (z + β) := Complex.normSq_pos.2 hne
  rw [Complex.div_re, ← add_div, div_lt_one hn]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im] at hn ⊢
  nlinarith

/-- **Saff–Varga for partial sums** (AAR Theorem 4.16.1 and Corollary 4.16.3). Let `A k > 0`
and `b (k+1) = A k / A (k+1)`. If `0 < α ≤ b 1` and `α ≤ b (k+2) - b (k+1)` for all `k`, then
no partial sum `∑_{k ≤ n} A k z^k` vanishes in the parabolic region `y² < 4α(x+α)`. -/
theorem SaffVarga.partialSums {A b : ℕ → ℝ} (hA : ∀ k, 0 < A k) (hb : ∀ k, 0 < b (k + 1))
    (hbA : ∀ k, b (k + 1) * A (k + 1) = A k) {α : ℝ} (hα : 0 < α) (h1 : α ≤ b 1)
    (h2 : ∀ k, α ≤ b (k + 2) - b (k + 1)) {z : ℂ} (hz : z.im ^ 2 < 4 * α * (z.re + α)) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (A k : ℂ) * z ^ k) ≠ 0 := by
  set S : ℕ → ℂ := fun n => ∑ k ∈ Finset.range (n + 1), (A k : ℂ) * z ^ k with hS
  have hbA' : ∀ k, (b (k + 1) : ℂ) * A (k + 1) = A k := fun k => by exact_mod_cast hbA k
  have hrec : ∀ n, (b (n + 2) : ℂ) * S (n + 2) = (z + b (n + 2)) * S (n + 1) - z * S n := by
    intro n
    simp only [hS, Finset.sum_range_succ]
    linear_combination (z ^ (n + 2)) * hbA' (n + 1)
  have hS0 : S 0 = A 0 := by simp [hS]
  have hb' : ∀ k, (b (k + 1) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hb k).ne'
  have claim : ∀ n, S (n + 1) ≠ 0 ∧ (z * S n / (b (n + 1) * S (n + 1))).re < 1 := by
    intro n
    induction n with
    | zero =>
      have hrec1 : (b 1 : ℂ) * S 1 = (z + b 1) * S 0 := by
        simp only [hS, Finset.sum_range_succ, Finset.sum_range_zero]
        linear_combination z * hbA' 0
      obtain ⟨hne, hlt⟩ := SaffVarga.step hα (β := (b 1 : ℂ)) hz (by simpa using h1)
      have hA0 : S 0 ≠ 0 := by rw [hS0]; exact_mod_cast (hA 0).ne'
      have hS1 : S 1 = (z + b 1) * S 0 / b 1 := by
        rw [eq_div_iff (hb' 0), mul_comm, hrec1]
      refine ⟨by rw [hS1]; exact div_ne_zero (mul_ne_zero hne hA0) (hb' 0), ?_⟩
      rw [show (b (0 + 1) : ℂ) * S (0 + 1) = (z + b 1) * S 0 by simpa using hrec1]
      rwa [mul_div_mul_right _ _ hA0]
    | succ n ih =>
      obtain ⟨hne, hlt⟩ := ih
      set μ := z * S n / (b (n + 1) * S (n + 1)) with hμ
      set β : ℂ := b (n + 2) - b (n + 1) * μ with hβ
      have hβre : α ≤ β.re := by
        have : β.re = b (n + 2) - b (n + 1) * μ.re := by
          simp [hβ, Complex.mul_re]
        rw [this]
        have := h2 n
        nlinarith [hb n]
      obtain ⟨hzβ, hlt'⟩ := SaffVarga.step hα hz hβre
      have hμS : (b (n + 1) : ℂ) * μ * S (n + 1) = z * S n := by
        rw [hμ]; field_simp [hb' n]
      have hrec' : (b (n + 2) : ℂ) * S (n + 2) = S (n + 1) * (z + β) := by
        rw [hrec n, hβ]; linear_combination hμS
      have hS2 : S (n + 2) = S (n + 1) * (z + β) / b (n + 2) := by
        rw [eq_div_iff (hb' (n + 1)), mul_comm, hrec']
      refine ⟨by rw [hS2]; exact div_ne_zero (mul_ne_zero hne hzβ) (hb' (n + 1)), ?_⟩
      rw [show (b (n + 1 + 1) : ℂ) * S (n + 1 + 1) = S (n + 1) * (z + β) from hrec',
        mul_comm (S (n + 1)), mul_div_mul_right _ _ hne]
      exact hlt'
  rcases n with _ | n
  · change S 0 ≠ 0
    rw [hS0]; exact_mod_cast (hA 0).ne'
  · exact (claim n).1

/-- **A Hurwitz-type lemma.** Let functions `s n`, eventually zero-free on an open set `U`,
converge to `f` uniformly on every ball about `0`, and let `f` be analytic and not locally zero
at `z₀ ∈ U`. Then `f z₀ ≠ 0`. The proof applies the maximum modulus principle to `1 / s n` on a
small disk about `z₀`. -/
theorem SaffVarga.hurwitz {f : ℂ → ℂ} {s : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hf : AnalyticAt ℂ f z₀) (hfne : ¬∀ᶠ z in 𝓝 z₀, f z = 0)
    (hs : ∀ n, Differentiable ℂ (s n)) (hsU : ∀ᶠ n in atTop, ∀ z ∈ U, s n z ≠ 0)
    (hconv : ∀ R : ℝ≥0, TendstoUniformlyOn s f atTop (ball 0 R)) : f z₀ ≠ 0 := by
  intro h0
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact hfne h
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
  obtain ⟨ε', hε', hε'U⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r := min ε ε' / 2 with hr
  have hm0 : 0 < min ε ε' := lt_min hε hε'
  have hr0 : 0 < r := by positivity
  have hrε : r < ε := by have := min_le_left ε ε'; linarith
  have hrε' : r < ε' := by have := min_le_right ε ε'; linarith
  have hcb : closedBall z₀ r ⊆ U := fun z hz =>
    hε'U (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) hrε'))
  have hsph : ∀ z ∈ sphere z₀ r, f z ≠ 0 := fun z hz => by
    rw [mem_sphere] at hz
    refine hεf (by rw [hz]; exact hrε) ?_
    intro hzz
    rw [hzz, dist_self] at hz
    exact hr0.ne' hz.symm
  set R : ℝ≥0 := ⟨‖z₀‖ + r + 1, by positivity⟩ with hR
  have hsub : closedBall z₀ r ⊆ ball 0 R := fun z hz => by
    rw [mem_ball, dist_zero_right]
    have h1 := mem_closedBall.1 hz
    rw [dist_eq_norm] at h1
    have h2 := norm_le_norm_add_norm_sub' z z₀
    change ‖z‖ < ‖z₀‖ + r + 1
    linarith
  have hfc : ContinuousOn f (closedBall z₀ r) :=
    ((hconv R).continuousOn (Frequently.of_forall fun n => (hs n).continuous.continuousOn)).mono
      hsub
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr0.le)
    (continuous_norm.comp_continuousOn (hfc.mono sphere_subset_closedBall))
  set m := ‖f w‖ with hmdef
  have hm : 0 < m := norm_pos_iff.2 (hsph w hw)
  have hun := Metric.tendstoUniformlyOn_iff.1 (hconv R) (m / 2) (by positivity)
  obtain ⟨n, hn1, hn2⟩ := (hun.and hsU).exists
  have hsn0 : ‖s n z₀‖ < m / 2 := by
    have := hn1 z₀ (hsub (mem_closedBall_self hr0.le))
    rwa [dist_eq_norm, h0, zero_sub, norm_neg] at this
  have hsph' : ∀ z ∈ sphere z₀ r, m / 2 ≤ ‖s n z‖ := fun z hz => by
    have h1 : m ≤ ‖f z‖ := hwmin hz
    have h2 := hn1 z (hsub (sphere_subset_closedBall hz))
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_norm_le (f z) (f z - s n z)
    rw [sub_sub_cancel] at h3
    linarith
  have hd : DiffContOnCl ℂ (fun z => (s n z)⁻¹) (ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr0.ne']
    exact fun z hz => ((hs n z).inv (hn2 z (hcb hz))).differentiableWithinAt
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (C := 2 / m)
    (fun z hz => by
      rw [frontier_ball z₀ hr0.ne'] at hz
      rw [norm_inv, ← inv_div]
      exact inv_anti₀ (by positivity) (hsph' z hz))
    (subset_closure (mem_ball_self hr0))
  have hpos : 0 < ‖s n z₀‖ := norm_pos_iff.2 (hn2 z₀ hz₀)
  rw [norm_inv, ← inv_div] at hmax
  have := (inv_le_inv₀ hpos (by positivity)).1 hmax
  linarith

/-- The three parameter cases of AAR Corollary 4.16.4 give the Saff–Varga conditions. -/
theorem SaffVarga.params {a c α : ℝ}
    (hparams : (0 < c ∧ c ≤ a ∧ α = c / a) ∨
      (1 ≤ a ∧ a ≤ c ∧ α = 1) ∨
      (0 < a ∧ a < 1 ∧ a ≤ c ∧ c < 2 * a / (1 - a) ∧
        α = (2 * a - c + c * a) / (a ^ 2 + a))) :
    0 < a ∧ 0 < c ∧ 0 < α ∧ α ≤ SaffVarga.seriesCoeffRatio a c 1 ∧
      ∀ k : ℕ, α ≤ SaffVarga.seriesCoeffRatio a c (k + 2) -
          SaffVarga.seriesCoeffRatio a c (k + 1) := by
  have hdiff : ∀ k : ℕ, 0 < a → SaffVarga.seriesCoeffRatio a c (k + 2) -
      SaffVarga.seriesCoeffRatio a c (k + 1) =
      (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) / ((a + (k + 1)) * (a + k)) := by
    intro k ha
    have h1 : 0 < a + k := by positivity
    have h2 : 0 < a + (k + 1) := by positivity
    simp only [SaffVarga.seriesCoeffRatio]
    push_cast
    rw [div_sub_div _ _ (by ring_nf; positivity) (by ring_nf; positivity), div_eq_div_iff
      (by ring_nf; positivity) (by positivity)]
    ring
  rcases hparams with ⟨hc, hca, rfl⟩ | ⟨ha, hac, rfl⟩ | ⟨ha, ha1, hac, hc2, rfl⟩
  · have ha : 0 < a := lt_of_lt_of_le hc hca
    refine ⟨ha, hc, div_pos hc ha, by simp [SaffVarga.seriesCoeffRatio], fun k => ?_⟩
    rw [hdiff k ha, div_le_div_iff₀ ha (by positivity)]
    have : (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) * a -
        c * ((a + (k + 1)) * (a + k)) = (k + 1) * (a - c) * (2 * a + k) := by ring
    have : 0 ≤ ((k:ℝ) + 1) * (a - c) * (2 * a + k) := by
      have : (0:ℝ) ≤ k := k.cast_nonneg
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  · have ha0 : 0 < a := by linarith
    have hc : 0 < c := by linarith
    refine ⟨ha0, hc, one_pos, ?_, fun k => ?_⟩
    · have : SaffVarga.seriesCoeffRatio a c 1 = c / a := by simp [SaffVarga.seriesCoeffRatio]
      rw [this, le_div_iff₀ ha0]; linarith
    · rw [hdiff k ha0, le_div_iff₀ (by positivity)]
      have : (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) -
          ((a + (k + 1)) * (a + k)) = (a - 1) * (c - a) := by ring
      nlinarith [mul_nonneg (show 0 ≤ a - 1 by linarith) (show 0 ≤ c - a by linarith)]
  · have hc : 0 < c := by linarith
    have h1a : 0 < 1 - a := by linarith
    have hα : 0 < 2 * a - c + c * a := by
      rw [lt_div_iff₀ h1a] at hc2; nlinarith
    have hden : 0 < a ^ 2 + a := by positivity
    refine ⟨ha, hc, div_pos hα hden, ?_, fun k => ?_⟩
    · simp only [SaffVarga.seriesCoeffRatio]; push_cast
      rw [div_le_div_iff₀ hden (by linarith)]
      nlinarith [mul_nonneg (show 0 ≤ c - a by linarith) ha.le]
    · rw [hdiff k ha, div_le_div_iff₀ hden (by positivity)]
      have : (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) * (a ^ 2 + a) -
          (2 * a - c + c * a) * ((a + (k + 1)) * (a + k)) =
          (1 - a) * (c - a) * (2 * a + k + 1) * k := by ring
      have : 0 ≤ (1 - a) * (c - a) * (2 * a + k + 1) * k := by
        have : (0:ℝ) ≤ k := k.cast_nonneg
        apply mul_nonneg (mul_nonneg (mul_nonneg h1a.le (by linarith)) (by linarith)) this
      nlinarith

/-- The parabolic zero-free regions of AAR Corollary 4.16.4. The partial sums are
zero-free there by Saff–Varga (`SaffVarga.partialSums`), and the limit by a Hurwitz-type
argument (`SaffVarga.hurwitz`). The hypothesis `hre` is implied by `him`. -/
theorem kummerM_ne_zero_of_mem_parabolicRegion {a c α : ℝ} {z : ℂ}
    (hparams : (0 < c ∧ c ≤ a ∧ α = c / a) ∨
      (1 ≤ a ∧ a ≤ c ∧ α = 1) ∨
      (0 < a ∧ a < 1 ∧ a ≤ c ∧ c < 2 * a / (1 - a) ∧
        α = (2 * a - c + c * a) / (a ^ 2 + a)))
    (him : z.im ^ 2 < 4 * α * (z.re + α)) :
    kummerM a c z ≠ 0 := by
  obtain ⟨ha, hc, hα, h1, h2⟩ := SaffVarga.params hparams
  have hck : ∀ k : ℕ, (c : ℂ) ≠ -k := fun k h => by
    have : c = -(k : ℝ) := by exact_mod_cast h
    have := k.cast_nonneg (α := ℝ); linarith
  have hA : ∀ k, 0 < SaffVarga.seriesCoeff a c k := fun k => by
    unfold SaffVarga.seriesCoeff
    have := ascPochhammer_pos k a ha
    have := ascPochhammer_pos k c hc
    positivity
  have hb : ∀ k, 0 < SaffVarga.seriesCoeffRatio a c (k + 1) := fun k => by
    unfold SaffVarga.seriesCoeffRatio; push_cast
    have : (0:ℝ) ≤ k := k.cast_nonneg
    apply div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hbA : ∀ k, SaffVarga.seriesCoeffRatio a c (k + 1) * SaffVarga.seriesCoeff a c (k + 1) =
      SaffVarga.seriesCoeff a c k := fun k => by
    unfold SaffVarga.seriesCoeffRatio SaffVarga.seriesCoeff
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
    have h1 : 0 < a + k := by positivity
    have h2 : 0 < c + k := by positivity
    have h3 := ascPochhammer_pos k c hc
    have h4 := ascPochhammer_pos k a ha
    push_cast
    rw [show a + ((k:ℝ) + 1) - 1 = a + k by ring, show c + ((k:ℝ) + 1) - 1 = c + k by ring,
      div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcoef : ∀ k, kummerMCoeff a c k = (SaffVarga.seriesCoeff a c k : ℂ) := fun k => by
    simp only [kummerMCoeff, SaffVarga.seriesCoeff, pochhammer_ofReal]
    push_cast; ring
  set p := FormalMultilinearSeries.ofScalars ℂ (kummerMCoeff a c) with hp
  have hps := hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hck
  have hsum : ∀ n, (fun y => p.partialSum n y) =
      fun y => ∑ k ∈ Finset.range n, (SaffVarga.seriesCoeff a c k : ℂ) * y ^ k := fun n => by
    funext y
    simp only [FormalMultilinearSeries.partialSum, hp, FormalMultilinearSeries.ofScalars_apply_eq,
      hcoef, smul_eq_mul]
  set U : Set ℂ := {z | z.im ^ 2 < 4 * α * (z.re + α)} with hU
  have hUo : IsOpen U := isOpen_lt (by fun_prop) (by fun_prop)
  refine SaffVarga.hurwitz (s := fun n y => p.partialSum n y) hUo him
    (hps.analyticAt_of_mem (by simp)) ?_ (fun n => ?_) ?_ (fun R => ?_)
  · intro hev
    have hon : AnalyticOnNhd ℂ (kummerM a c) univ := fun w _ => hps.analyticAt_of_mem (by simp)
    have := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ z) hev (mem_univ 0)
    simp at this
  · simp only [hsum n]; fun_prop
  · filter_upwards [eventually_ge_atTop 1] with n hn w hw
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp only [hsum (m + 1)]
    exact SaffVarga.partialSums hA hb hbA hα h1 h2 hw m
  · have := hps.tendstoUniformlyOn (r' := R) ENNReal.coe_lt_top
    simpa using this

end ParabolicRegion

end DLMF.Confluent
