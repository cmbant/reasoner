/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.KummerProperties
public import DLMF.Hypergeometric.Continuation
public import DLMFMathlib.Analysis.Complex.ParameterContinuity

/-!
# The regularized Kummer function as an entire function of its parameters

This file develops the series, majorants and analyticity of the regularized Kummer function
`𝐌(a,b,z) = regularizedHGFun {a} {b} z` in its parameters and argument (DLMF §13.2(i)).

## Main results

* `regularizedConfluent_eq_tsum`, `summable_regularizedConfluent_term`: `𝐌(a,b,z)` as the sum
  of `∑ (a)_n zⁿ / (n! Γ(b+n))`, convergent for all `a, b, z`.
* `hasFPowerSeriesOnBall_regularizedConfluent`: the series converges on all of `ℂ`.
* `analyticOnNhd_regularizedConfluent_comp`, `differentiable_regularizedConfluent_comp`: `𝐌` is
  entire along any entire curve in the parameter plane.
* `analyticOnNhd_regularizedConfluent_a`, `analyticOnNhd_regularizedConfluent_b`: `𝐌` is entire
  in each parameter.
* `deriv_regularizedConfluent`: `𝐌'(a,b,z) = a 𝐌(a+1,b+1,z)` (DLMF 13.3.15), with no hypothesis
  on the parameters.
* `continuous_regularizedConfluent`: joint continuity in the parameters and the argument.
* `regularizedConfluent_eq_div_Gamma`: `𝐌(a,b,z) = M(a,b,z)/Γ(b)` off the poles of `Γ(b)`.
-/

public section

open Complex Filter Set FormalMultilinearSeries DLMF.Hypergeometric
open scoped Real Nat Topology ENNReal

noncomputable section

set_option autoImplicit false

namespace DLMF.Confluent

/-! ### Series and majorants -/

/-- The regularized Kummer function as a series with explicit terms. -/
theorem regularizedConfluent_eq_tsum (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      ∑' n : ℕ, pochhammer a n * z ^ n / n.factorial * (Gamma (b + n))⁻¹ := by
  rw [regularizedHGFun_eq_tsum]
  congr 1
  funext n
  rw [regularizedHGFunCoeff_singleton]
  ring

/-- The power series of the regularized `₁F̃₁(a;b;·)` has infinite radius of convergence. -/
theorem radius_regularizedConfluentSeries (a b : ℂ) :
    (regularizedHGFunSeries {a} {b}).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top (by simp)

/-- The regularized Kummer series converges on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_regularizedConfluent (a b : ℂ) :
    HasFPowerSeriesOnBall (regularizedHGFun {a} {b})
      (ofScalars ℂ (regularizedHGFunCoeff {a} {b})) 0 ⊤ := by
  have hr := radius_regularizedConfluentSeries a b
  change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {b}).sum
    (regularizedHGFunSeries {a} {b}) 0 ⊤
  simpa only [hr] using (regularizedHGFunSeries {a} {b}).hasFPowerSeriesOnBall (by rw [hr]; simp)

/-- The series `∑ (a)_n zⁿ / (n! Γ(b+n))` converges for all `a, b, z`. -/
theorem summable_regularizedConfluent_term (a b z : ℂ) :
    Summable fun n : ℕ => pochhammer a n * z ^ n / n.factorial * (Gamma (b + n))⁻¹ := by
  have h := (hasFPowerSeriesOnBall_regularizedConfluent a b).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  refine h.summable.congr fun n => ?_
  rw [regularizedHGFunCoeff_singleton]
  ring

/-- For `b = 1 - N` and `n ≥ N`, the `n`-th term of the regularized series has norm `|(α)_n| / (n!
(n-N)!)`. -/
theorem norm_regularizedConfluentSeries_apply_ofReal (α : ℝ) (N n : ℕ) (hn : N ≤ n) :
    ‖regularizedHGFunSeries {(α : ℂ)} {1 - (N : ℂ)} n‖ =
      ‖pochhammer (α : ℂ) n‖ / (n.factorial * (n - N).factorial) := by
  have hΓ : Gamma ((1 : ℂ) - N + n) = ((n - N).factorial : ℂ) := by
    rw [show (1 : ℂ) - N + n = ((n - N : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hn]; ring]
    exact Complex.Gamma_nat_eq_factorial _
  rw [norm_apply_eq_norm_coef, regularizedHGFunSeries_coeff, regularizedHGFunCoeff_singleton, hΓ,
    norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]

/-- The tail-domination step: the `n`-th term is bounded by the `n`-th term of the majorant
series `𝐌(α, 1 - N, ‖z‖)`. -/
theorem norm_confluent_term_le_majorant {a b z : ℂ} {α : ℝ} (ha : ‖a‖ ≤ α) {N : ℕ}
    (hre : 1 ≤ (b + N).re) {m : ℝ} (hm : 0 < m) (hΓ : m ≤ ‖Gamma (b + N)‖) {n : ℕ}
    (hn : N ≤ n) :
    ‖pochhammer a n * z ^ n / n.factorial * (Gamma (b + n))⁻¹‖ ≤
      m⁻¹ * (‖regularizedHGFunSeries {(α : ℂ)} {1 - (N : ℂ)} n‖ * ‖z‖ ^ n) := by
  rw [norm_regularizedConfluentSeries_apply_ofReal α N n hn, norm_mul, norm_div, norm_mul,
    norm_pow, Complex.norm_natCast]
  have hA : ‖pochhammer a n‖ ≤ ‖pochhammer (α : ℂ) n‖ := norm_ascPochhammer_eval_le ha n
  have hG := norm_recip_Gamma_add_nat_le hre hm hΓ hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hf' : (0 : ℝ) < (n - N).factorial := by positivity
  calc ‖pochhammer a n‖ * ‖z‖ ^ n / n.factorial * ‖(Gamma (b + n))⁻¹‖
      ≤ ‖pochhammer (α : ℂ) n‖ * ‖z‖ ^ n / n.factorial * (((n - N).factorial : ℝ)⁻¹ * m⁻¹) := by
        gcongr
    _ = _ := by field_simp

/-! ### Analyticity in the parameters -/

/-- The regularized Kummer function is entire along any entire curve in the parameter plane
(DLMF §13.2(i)): for entire `A B`, `w ↦ 𝐌(A w, B w, z)` is entire. -/
theorem analyticOnNhd_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w => regularizedHGFun {A w} {B w} z) univ := by
  simp_rw [regularizedConfluent_eq_tsum]
  refine analyticOnNhd_tsum_of_eventually_dominated ?_ ?_ ?_
  · intro n
    have h1 : Differentiable ℂ fun w => pochhammer (A w) n :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    exact ((h1.mul_const _).div_const _).mul (differentiable_one_div_Gamma.comp (hB.add_const _))
  · intro w
    exact summable_regularizedConfluent_term _ _ z
  · intro w₀
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (B w₀).re ≤ N := exists_nat_ge _
    have hre0 : 2 ≤ (B w₀ + N).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
    have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
      hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevC : ∀ᶠ w in 𝓝 w₀, (B w₀).re - 1 < (B w).re :=
      (Complex.continuous_re.comp hB.continuous).continuousAt.eventually
        (lt_mem_nhds (by show (B w₀).re - 1 < (B w₀).re; linarith))
    have hevV : ∀ᶠ w in 𝓝 w₀, B w ∈ V := hB.continuous.continuousAt (hVopen.mem_nhds hc₀V)
    obtain ⟨U, hU, hUopen, hw₀U⟩ := eventually_nhds_iff.mp (hevA.and (hevC.and hevV))
    refine ⟨U, hUopen, hw₀U, N, ?_⟩
    set p := regularizedHGFunSeries {((‖A w₀‖ + 1 : ℝ) : ℂ)} {1 - (N : ℂ)} with hp
    have hz' : (‖z‖₊ : ENNReal) < p.radius := by
      rw [hp, radius_regularizedConfluentSeries]
      exact ENNReal.coe_lt_top
    have hm : 0 < ‖Gamma (B w₀ + N)‖ / 2 := by
      have hpole : ∀ k : ℕ, B w₀ + N ≠ -k := fun k h => by
        have := congrArg Complex.re h
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
      positivity
    refine ⟨fun n => (‖Gamma (B w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n),
      (p.summable_norm_mul_pow hz').mul_left _, ?_⟩
    intro n hn w hw
    obtain ⟨hAw, hCw, hVw⟩ := hU w hw
    have hre : 1 ≤ (B w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using norm_confluent_term_le_majorant hAw.le hre hm (hV _ hVw).le hn

/-- `𝐌(a,b,z)` is entire in `b`. -/
theorem analyticOnNhd_regularizedConfluent_b (a z : ℂ) :
    AnalyticOnNhd ℂ (fun b => regularizedHGFun {a} {b} z) univ :=
  analyticOnNhd_regularizedConfluent_comp (differentiable_const a) differentiable_id z

/-- `𝐌(a,b,z)` is entire in `a`. -/
theorem analyticOnNhd_regularizedConfluent_a (b z : ℂ) :
    AnalyticOnNhd ℂ (fun a => regularizedHGFun {a} {b} z) univ :=
  analyticOnNhd_regularizedConfluent_comp differentiable_id (differentiable_const b) z

/-- `w ↦ ₁F̃₁(A(w); B(w); z)` is analytic when `A` and `B` are entire. -/
@[fun_prop]
theorem analyticAt_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z w : ℂ) :
    AnalyticAt ℂ (fun w => regularizedHGFun {A w} {B w} z) w :=
  analyticOnNhd_regularizedConfluent_comp hA hB z w (mem_univ w)

/-- `w ↦ ₁F̃₁(A(w); B(w); z)` is entire when `A` and `B` are entire. -/
@[fun_prop]
theorem differentiable_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z : ℂ) :
    Differentiable ℂ (fun w => regularizedHGFun {A w} {B w} z) :=
  fun w => (analyticAt_regularizedConfluent_comp hA hB z w).differentiableAt

/-! ### Derivative -/

/-- Coefficient identity `(n+1) c_{n+1}(a;b) = a c_n(a+1;b+1)` for the regularized `₁F̃₁`. -/
theorem regularizedHGFunCoeff_singleton_succ (a b : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * regularizedHGFunCoeff {a} {b} (n + 1) =
      a * regularizedHGFunCoeff {a + 1} {b + 1} n := by
  rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton, pochhammer_succ_left,
    show b + ((n + 1 : ℕ) : ℂ) = b + 1 + n by push_cast; ring, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

/-- 13.3.15 for the regularized function: `𝐌'(a,b,z) = a 𝐌(a+1,b+1,z)`, with no hypothesis
on the parameters. -/
theorem deriv_regularizedConfluent (a b z : ℂ) :
    deriv (regularizedHGFun {a} {b}) z = a * regularizedHGFun {a + 1} {b + 1} z := by
  have hd := (hasFPowerSeriesOnBall_regularizedConfluent a b).deriv_ofScalars.hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  have hs := ((hasFPowerSeriesOnBall_regularizedConfluent (a + 1) (b + 1)).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)).mul_left a
  refine hd.unique ?_
  convert hs using 1
  funext n
  rw [← mul_assoc, regularizedHGFunCoeff_singleton_succ]

/-- The regularized `₁F̃₁(a;b;·)` is complex differentiable everywhere. -/
theorem differentiableAt_regularizedConfluent (a b z : ℂ) :
    DifferentiableAt ℂ (regularizedHGFun {a} {b}) z :=
  ((hasFPowerSeriesOnBall_regularizedConfluent a b).analyticAt_of_mem
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt

/-! ### Joint continuity -/

/-- `𝐌(a,b,z)` is jointly continuous in the parameters and the argument. -/
theorem continuous_regularizedConfluent :
    Continuous fun p : ℂ × ℂ × ℂ => regularizedHGFun {p.1} {p.2.1} p.2.2 := by
  simp_rw [regularizedConfluent_eq_tsum]
  refine continuous_tsum_of_eventually_dominated (fun n => ?_)
    (fun p => summable_regularizedConfluent_term _ _ _) fun p₀ => ?_
  · have h1 : Continuous fun p : ℂ × ℂ × ℂ => pochhammer p.1 n :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).continuous.comp continuous_fst
    exact ((h1.mul (by fun_prop)).div_const _).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))
  obtain ⟨a₀, b₀, z₀⟩ := p₀
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - b₀.re ≤ N := exists_nat_ge _
  have hre0 : 2 ≤ (b₀ + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
  set U : Set (ℂ × ℂ × ℂ) := {p | ‖p.1‖ < ‖a₀‖ + 1} ∩ ({p | b₀.re - 1 < p.2.1.re} ∩
    ((fun p : ℂ × ℂ × ℂ => p.2.1) ⁻¹' V ∩ {p | ‖p.2.2‖ < ‖z₀‖ + 1})) with hU
  have hUo : IsOpen U := by
    refine (isOpen_lt (by fun_prop) continuous_const).inter ((isOpen_lt continuous_const
      (by fun_prop)).inter ((hVopen.preimage (by fun_prop)).inter
        (isOpen_lt (by fun_prop) continuous_const)))
  refine ⟨U, hUo, ⟨by simp, by simp, hc₀V, by simp⟩, N, ?_⟩
  set p := regularizedHGFunSeries {((‖a₀‖ + 1 : ℝ) : ℂ)} {1 - (N : ℂ)} with hp
  set r : NNReal := ⟨‖z₀‖ + 1, by positivity⟩
  have hz' : (r : ENNReal) < p.radius := by
    rw [hp, radius_regularizedConfluentSeries]
    exact ENNReal.coe_lt_top
  have hm : 0 < ‖Gamma (b₀ + N)‖ / 2 := by
    have hpole : ∀ k : ℕ, b₀ + N ≠ -k := fun k h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
    positivity
  refine ⟨fun n => (‖Gamma (b₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (r : ℝ) ^ n),
    (p.summable_norm_mul_pow hz').mul_left _, ?_⟩
  rintro n hn ⟨a, b, z⟩ ⟨hAw, hCw, hVw, hzw⟩
  have hre : 1 ≤ (b + N).re := by
    simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
    change b₀.re - 1 < b.re at hCw
    linarith
  refine (norm_confluent_term_le_majorant hAw.le hre hm (hV _ hVw).le hn).trans ?_
  change _ ≤ (‖Gamma (b₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z₀‖ + 1) ^ n)
  change ‖z‖ < ‖z₀‖ + 1 at hzw
  gcongr

/-- Off the poles of `Γ(b)`, `𝐌(a,b,z) = M(a,b,z)/Γ(b)`. -/
theorem regularizedConfluent_eq_div_Gamma {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) (z : ℂ) :
    regularizedHGFun {a} {b} z = kummerM a b z / Gamma b := by
  rw [kummerM_eq_mul_regularizedHGFun hb, mul_div_cancel_left₀ _ (Gamma_ne_zero hb)]

end DLMF.Confluent
