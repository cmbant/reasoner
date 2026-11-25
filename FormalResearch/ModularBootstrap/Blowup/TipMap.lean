module

public import FormalResearch.ModularBootstrap.Constants
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tip rescaling geometry, disc averaging, and Lemma T1 (`blowup_limit.tex`)

Formalizes the tip coordinate, complex potential envelope `H`, distance `d`, disc-averaging
bounds, subharmonic mean-value inequality on discs, and **Lemma T1** (tip map `z_b` and its
local inversion) from `CFT/modular_bootstrap/paper/blowup_limit.tex`:

* `tipEps`, `bScale`, `tipH`, `tipDist`, `tipL`, `slitQ`, `kappa0`, `kappaC`, `asC`,
  `slitBoundaryMapC`.
* `tipH_eq_airyEnv`: exact identity `exp(H(ζ)) = airyEnv(-β ζ)` for all `ζ ∈ ℂ`.
* `tipDist_sq`, `tipDist_ge_half_abs_im`, `tipDist_ge_norm_div_sqrt_two`,
  `tipDist_sector_lower`: lower bounds on `d(ζ) = |ζ|^{1/2} Re √(-ζ)`.
* `tipH_disc_oscillation`: `|H(ζ) - H(ζ₀)| ≤ 3 K / 4` on `D(ζ₀, r)` for
  `r = (1/2) (1 + |ζ₀|)^{-1/2}`.
* `disc_avg_neg_log_tipDist`: disc average of `-log d` on `D(ζ₀, r)`.
* `subharmonic_disc_avg_le`: disc average inequality from Jensen's formula.
* `slitBoundaryMapC_injOn_UHP`: elementary algebraic injectivity of `ℬ` on the upper half-plane.
* `tipPsi`, `lemma_T1`: **Lemma T1** (proved with no unproved hypotheses).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap

open FormalResearch.Special

/-! ### Section 1: Tip coordinates, `H(ζ)`, `d(ζ)`, and elementary bounds -/

/-- Tip scaling parameter `ε = c'^{-2/3}`. -/
noncomputable def tipEps (c' : ℝ) : ℝ := c' ^ (-(2 / 3 : ℝ))

/-- Tip map `b(ζ) = ξ_* + ε ζ`. -/
noncomputable def bScale (c' : ℝ) (ζ : ℂ) : ℂ :=
  (xiStar : ℂ) + ((tipEps c' : ℝ) : ℂ) * ζ

/-- Tip exponent `H(ζ) = -K Re((-ζ)^{3/2})` (principal branch). -/
noncomputable def tipH (ζ : ℂ) : ℝ := -KTip * ((-ζ) ^ (3 / 2 : ℂ)).re

/-- Tip distance factor `d(ζ) = |ζ|^{1/2} Re √(-ζ)` (principal branch). -/
noncomputable def tipDist (ζ : ℂ) : ℝ := √‖ζ‖ * ((-ζ) ^ (1 / 2 : ℂ)).re

/-- Linear Cardy exponent `L(b) = (2π/3) b`. -/
noncomputable def tipL (b : ℂ) : ℂ := ((2 * π / 3 : ℝ) : ℂ) * b

/-- Quadratic coefficient `q = (1/2) ℬ''(σ_*) = √2 / (2π σ_* (σ_*^2 - 1))`. -/
noncomputable def slitQ : ℝ :=
  √2 / (2 * π * sigmaStar * (sigmaStar ^ 2 - 1))

/-- Leading Bessel asymptotic `as(z) = e^z / √(2π z)`. -/
noncomputable def asC (z : ℂ) : ℂ :=
  Complex.exp z / (2 * (π : ℂ) * z) ^ (1 / 2 : ℂ)

/-- Tip normalization constant `κ₀ = (2 ξ_* / 3) (1 - (√2 - 1)^4)^2 (2π L(ξ_*))^{-1/2}`. -/
noncomputable def kappa0 : ℝ :=
  (2 * xiStar / 3) * (1 - (√2 - 1) ^ 4) ^ 2 / √(2 * π * ((2 / 3 : ℝ) * Real.arsinh 1))

/-- Rescaled weight factor `κ_c = c'^{-1/6} κ₀`. -/
noncomputable def kappaC (c' : ℝ) : ℝ := c' ^ (-(1 / 6 : ℝ)) * kappa0

/-- Complex slit-strip boundary map `ℬ(z) = (2π)^{-1} log((z - 1) / (z(z + 1)))`. -/
noncomputable def slitBoundaryMapC (z : ℂ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * Complex.log ((z - 1) / (z * (z + 1)))

lemma tipEps_pos {c' : ℝ} (hc' : 0 < c') : 0 < tipEps c' :=
  Real.rpow_pos_of_pos hc' _

lemma tipEps_mul_self_cube {c' : ℝ} (hc' : 0 < c') : c' * tipEps c' ^ (3 / 2 : ℝ) = 1 := by
  unfold tipEps
  rw [← Real.rpow_mul hc'.le, show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
    Real.rpow_neg_one, mul_inv_cancel₀ hc'.ne']

lemma slitQ_pos : 0 < slitQ := by
  unfold slitQ
  have h1 : sigmaStar < 0 := sigmaStar_neg
  have h2 : (-0.42 : ℝ) < sigmaStar := sigmaStar_gt_neg_half
  have h3 : sigmaStar ^ 2 - 1 < 0 := by nlinarith
  have hprod : 0 < sigmaStar * (sigmaStar ^ 2 - 1) := mul_pos_of_neg_of_neg h1 h3
  have hden : 0 < 2 * π * sigmaStar * (sigmaStar ^ 2 - 1) := by
    rw [mul_assoc]; exact mul_pos (by positivity) hprod
  positivity

lemma kappa0_pos : 0 < kappa0 := by
  unfold kappa0
  have hxi := xiStar_pos
  have ha : 0 < Real.arsinh 1 := by
    rw [← Real.sinh_lt_sinh, Real.sinh_zero, Real.sinh_arsinh]; exact one_pos
  have hsq : √2 - 1 < 1 := by
    have : √2 < 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hpos : 0 < √2 - 1 := by
    have : 1 < √2 := by rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have h4 : (√2 - 1) ^ 4 < 1 := pow_lt_one₀ hpos.le hsq (by norm_num)
  have hsub : 0 < 1 - (√2 - 1) ^ 4 := sub_pos.mpr h4
  positivity

lemma kappaC_pos {c' : ℝ} (hc' : 0 < c') : 0 < kappaC c' :=
  mul_pos (Real.rpow_pos_of_pos hc' _) kappa0_pos

lemma ofReal_pos_mul_cpow {r : ℝ} (hr : 0 < r) (z s : ℂ) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  by_cases hz : z = 0
  · subst hz; simp only [mul_zero]
    by_cases hs : s = 0
    · subst hs; simp
    · simp [Complex.zero_cpow hs]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz), Complex.cpow_def_of_ne_zero hr0,
    Complex.cpow_def_of_ne_zero hz, ← Complex.exp_add, ← add_mul]
  congr 2
  apply Complex.ext
  · simp [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hz)]
  · simp [Complex.log_im, Complex.arg_real_mul z hr, Complex.arg_ofReal_of_nonneg hr.le]

lemma tipH_eq_airyEnv (ζ : ℂ) :
    Real.exp (tipH ζ) = airyEnv (-(betaTip : ℂ) * ζ) := by
  unfold tipH airyEnv
  congr 1
  have hb : (0 : ℝ) < betaTip := betaTip_pos
  have heq : -(betaTip : ℂ) * ζ = (betaTip : ℂ) * (-ζ) := by ring
  rw [heq, ofReal_pos_mul_cpow hb]
  have hreal : (betaTip : ℂ) ^ (3 / 2 : ℂ) = ((betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hb.le]
  rw [hreal, Complex.re_ofReal_mul]
  have hk := four_thirds_betaTip_rpow
  have halg : -(4 / 3 : ℝ) * (betaTip ^ (3 / 2 : ℝ) * ((-ζ) ^ (3 / 2 : ℂ)).re) =
      -((4 / 3 : ℝ) * betaTip ^ (3 / 2 : ℝ)) * ((-ζ) ^ (3 / 2 : ℂ)).re := by ring
  rw [halg, hk]

lemma tipH_le_KTip_norm (ζ : ℂ) : tipH ζ ≤ KTip * ‖ζ‖ ^ (3 / 2 : ℝ) := by
  unfold tipH
  have h := re_cpow_three_halves_le (-ζ)
  rw [norm_neg] at h
  have hK : 0 ≤ KTip := KTip_pos.le
  nlinarith

lemma tipH_ofReal_nonneg {s : ℝ} (hs : 0 ≤ s) : tipH (s : ℂ) = 0 := by
  by_cases hs0 : s = 0
  · subst hs0; unfold tipH; simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    unfold tipH
    have hre : ((-(s : ℂ)) ^ (3 / 2 : ℂ)).re = 0 := by
      have harg : (-(s : ℂ)).arg = π := by
        rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; rfl]
        exact Complex.arg_ofReal_of_neg (by linarith)
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (neg_ne_zero.mpr hs_pos.ne')),
        Complex.exp_re]
      have him : (Complex.log (-(s : ℂ)) * (3 / 2 : ℂ)).im = 3 * π / 2 := by
        simp [Complex.log_im, harg]; ring
      rw [him, show (3 * π / 2 : ℝ) = π + π / 2 by ring, Real.cos_add_pi_div_two,
        Real.sin_pi, neg_zero, mul_zero]
    rw [hre, mul_zero]

lemma tipDist_nonneg (ζ : ℂ) : 0 ≤ tipDist ζ :=
  mul_nonneg (Real.sqrt_nonneg _) (cpow_half_re_nonneg (-ζ))

lemma tipDist_sq (ζ : ℂ) : tipDist ζ ^ 2 = ‖ζ‖ * (‖ζ‖ - ζ.re) / 2 := by
  unfold tipDist
  have h1 := airySqrtRe_sq_sub (-ζ)
  have h2 := airySqrtRe_sq_add (-ζ)
  dsimp [airySqrtRe] at h1 h2
  have hre : (-ζ).re = -ζ.re := Complex.neg_re ζ
  have hn : ‖-ζ‖ = ‖ζ‖ := norm_neg ζ
  have h1' : ((-ζ) ^ (1 / 2 : ℂ)).re ^ 2 - ((-ζ) ^ (1 / 2 : ℂ)).im ^ 2 = -ζ.re := hre ▸ h1
  have h2' : ((-ζ) ^ (1 / 2 : ℂ)).re ^ 2 + ((-ζ) ^ (1 / 2 : ℂ)).im ^ 2 = ‖ζ‖ := hn ▸ h2
  have hsq : ((-ζ) ^ (1 / 2 : ℂ)).re ^ 2 = (‖ζ‖ - ζ.re) / 2 := by linarith
  rw [mul_pow, Real.sq_sqrt (norm_nonneg _), hsq]
  ring

lemma tipDist_ge_half_abs_im (ζ : ℂ) : |ζ.im| / 2 ≤ tipDist ζ := by
  have hsq : (|ζ.im| / 2) ^ 2 ≤ tipDist ζ ^ 2 := by
    rw [tipDist_sq, div_pow, sq_abs]
    have hre : ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hsum : 0 ≤ ‖ζ‖ + ζ.re := by
      linarith [Complex.abs_re_le_norm ζ, abs_le.mp (Complex.abs_re_le_norm ζ)]
    have him2 : ζ.im ^ 2 = (‖ζ‖ - ζ.re) * (‖ζ‖ + ζ.re) := by linarith
    have hle : ‖ζ‖ + ζ.re ≤ 2 * ‖ζ‖ := by
      linarith [Complex.re_le_norm ζ]
    calc ζ.im ^ 2 / 2 ^ 2 = (‖ζ‖ - ζ.re) * (‖ζ‖ + ζ.re) / 4 := by rw [him2]; ring
      _ ≤ (‖ζ‖ - ζ.re) * (2 * ‖ζ‖) / 4 := by
        gcongr; linarith [Complex.re_le_norm ζ]
      _ = ‖ζ‖ * (‖ζ‖ - ζ.re) / 2 := by ring
  have h1 : √((|ζ.im| / 2) ^ 2) ≤ √(tipDist ζ ^ 2) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (tipDist_nonneg ζ)] at h1

lemma tipDist_ge_norm_div_sqrt_two {ζ : ℂ} (hre : ζ.re ≤ 0) :
    ‖ζ‖ / √2 ≤ tipDist ζ := by
  have hsq : (‖ζ‖ / √2) ^ 2 ≤ tipDist ζ ^ 2 := by
    rw [tipDist_sq, div_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [norm_nonneg ζ]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (tipDist_nonneg ζ)] at h1

lemma tipDist_pos_of_not_nonneg {ζ : ℂ} (hζ : ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re)) :
    0 < tipDist ζ := by
  by_cases him : ζ.im = 0
  · have hre : ζ.re < 0 := lt_of_not_ge fun h => hζ ⟨him, h⟩
    have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr (fun h0 => by simp [h0] at hre)
    exact lt_of_lt_of_le (div_pos hnorm (by positivity)) (tipDist_ge_norm_div_sqrt_two hre.le)
  · exact lt_of_lt_of_le (div_pos (abs_pos.mpr him) two_pos) (tipDist_ge_half_abs_im ζ)

lemma tipDist_le_norm (ζ : ℂ) : tipDist ζ ≤ ‖ζ‖ := by
  have hsq : tipDist ζ ^ 2 ≤ ‖ζ‖ ^ 2 := by
    rw [tipDist_sq]
    have hle : ‖ζ‖ - ζ.re ≤ 2 * ‖ζ‖ := by
      linarith [neg_le_abs ζ.re, Complex.abs_re_le_norm ζ]
    nlinarith [norm_nonneg ζ]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (tipDist_nonneg ζ), Real.sqrt_sq (norm_nonneg ζ)] at h1

lemma tipDist_sector_lower {ζ₀ ζ : ℂ}
    (harg : |(-ζ₀).arg| ≤ 2 * π / 3) (hnorm : 8 ≤ ‖ζ₀‖)
    (hball : ζ ∈ ball ζ₀ ((1 / 2 : ℝ) * (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)))) :
    ‖ζ₀‖ / 4 ≤ tipDist ζ := by
  have hr_le : (1 / 2 : ℝ) * (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 / 6 := by
    have h1 : (3 : ℝ) ≤ (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      calc (3 : ℝ) = √9 := by norm_num
        _ ≤ √(1 + ‖ζ₀‖) := Real.sqrt_le_sqrt (by linarith)
    have h2 : (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 / 3 := by
      rw [Real.rpow_neg (by positivity), ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) h1
    linarith
  have hdist : ‖ζ - ζ₀‖ < 1 / 6 := by
    rw [← dist_eq_norm]; exact (mem_ball.mp hball).trans_le hr_le
  have hζ_ge : ‖ζ₀‖ - 1 / 6 ≤ ‖ζ‖ := by
    have := norm_sub_norm_le ζ₀ ζ
    rw [norm_sub_rev] at this
    linarith
  have hζ₀_pos : 0 < ‖ζ₀‖ := by linarith
  have hcos₀ : -(1 / 2 : ℝ) ≤ Real.cos (-ζ₀).arg := by
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (-ζ₀).arg)
      (by linarith [Real.pi_pos]) harg
    rw [Real.cos_abs, show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at h1
    exact h1
  have hre₀ : (-ζ₀).re = ‖ζ₀‖ * Real.cos (-ζ₀).arg := by
    have h := Complex.cos_arg (show -ζ₀ ≠ 0 by
      intro h0; simp only [neg_eq_zero] at h0; rw [h0, norm_zero] at hnorm; linarith)
    rw [norm_neg] at h
    rw [h]; field_simp [hζ₀_pos.ne']
  have hre_ζ₀ : ζ₀.re ≤ ‖ζ₀‖ / 2 := by
    rw [Complex.neg_re] at hre₀
    nlinarith
  have hre_ζ : ζ.re ≤ ‖ζ₀‖ / 2 + 1 / 6 := by
    have h1 : (ζ - ζ₀).re ≤ ‖ζ - ζ₀‖ := Complex.re_le_norm _
    rw [Complex.sub_re] at h1
    linarith
  have hsq : (‖ζ₀‖ / 4) ^ 2 ≤ tipDist ζ ^ 2 := by
    rw [tipDist_sq]
    have hsub : ‖ζ‖ - ζ.re ≥ ‖ζ₀‖ / 2 - 1 / 3 := by linarith
    have h1 : ‖ζ₀‖ / 2 - 1 / 3 ≥ (11 / 24 : ℝ) * ‖ζ₀‖ := by linarith
    have h2 : ‖ζ‖ ≥ (47 / 48 : ℝ) * ‖ζ₀‖ := by linarith
    nlinarith [hζ₀_pos]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (tipDist_nonneg ζ)] at h1

/-! ### Section 2: Oscillation of `H`, disc averaging of `-log d`, and Jensen disc average -/

private lemma re_cpow_half_eq_sqrt (z : ℂ) :
    (z ^ (1 / 2 : ℂ)).re = √((‖z‖ + z.re) / 2) := by
  have h1 := airySqrtRe_sq_sub z
  have h2 := airySqrtRe_sq_add z
  have hnn : 0 ≤ airySqrtRe z := airySqrtRe_nonneg z
  have hsq : airySqrtRe z ^ 2 = (‖z‖ + z.re) / 2 := by linarith
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq hnn] at this

private lemma continuous_re_cpow_three_halves :
    Continuous (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) := by
  have heq : (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) =
      fun z => 3 * z.re * √((‖z‖ + z.re) / 2) - 2 * (√((‖z‖ + z.re) / 2)) ^ 3 := by
    ext z; rw [re_cpow_three_halves_eq]; dsimp [airySqrtRe]; rw [re_cpow_half_eq_sqrt]
  rw [heq]
  fun_prop

lemma continuous_tipH : Continuous tipH := by
  unfold tipH
  exact continuous_const.mul (continuous_re_cpow_three_halves.comp continuous_neg)

lemma continuous_tipDist : Continuous tipDist := by
  unfold tipDist
  refine (Real.continuous_sqrt.comp continuous_norm).mul ?_
  have heq : (fun ζ : ℂ => ((-ζ) ^ (1 / 2 : ℂ)).re) =
      fun ζ => √((‖ζ‖ - ζ.re) / 2) := by
    ext ζ; rw [re_cpow_half_eq_sqrt, norm_neg, Complex.neg_re]; rfl
  rw [heq]; fun_prop

private lemma re_cpow_three_halves_lip_slit {z₁ z₂ : ℂ}
    (hseg : ∀ t ∈ Ioo (0 : ℝ) 1, -((1 - t) • z₁ + t • z₂) ∈ Complex.slitPlane)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - t) • z₁ + t • z₂‖ ≤ M) :
    |((-z₁) ^ (3 / 2 : ℂ)).re - ((-z₂) ^ (3 / 2 : ℂ)).re| ≤
      (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * ‖z₁ - z₂‖ := by
  let γ : ℝ → ℂ := fun t => (1 - t) • z₁ + t • z₂
  let f : ℝ → ℝ := fun t => ((-γ t) ^ (3 / 2 : ℂ)).re
  have hcont : ContinuousOn f (Icc 0 1) :=
    (continuous_re_cpow_three_halves.comp (continuous_neg.comp (by fun_prop))).continuousOn
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt f ((-(3 / 2 : ℂ) * (-γ t) ^ (1 / 2 : ℂ) * (z₂ - z₁)).re) t := by
    intro t ht
    have hγ_deriv : HasDerivAt (fun s : ℝ => -γ s) (-(z₂ - z₁)) t := by
      have h1 : (fun s : ℝ => -γ s) = fun s : ℝ => -z₁ + (s : ℂ) * (-(z₂ - z₁)) := by
        ext s; apply Complex.ext <;> dsimp [γ] <;> simp <;> ring
      rw [h1]
      have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * (-(z₂ - z₁))) (1 * (-(z₂ - z₁))) t :=
        (Complex.ofRealCLM.hasDerivAt).mul_const (-(z₂ - z₁))
      simpa using hlin.const_add (-z₁)
    have hcp : HasDerivAt (fun w : ℂ => w ^ (3 / 2 : ℂ))
        ((3 / 2 : ℂ) * (-γ t) ^ ((3 / 2 : ℂ) - 1)) (-γ t) :=
      (Complex.hasStrictDerivAt_cpow_const (hseg t ht)).hasDerivAt
    have hcomp := hcp.comp t hγ_deriv
    have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp)
    refine hre.congr_deriv ?_
    simp only [Complex.reCLM_apply]
    congr 1
    rw [show (3 / 2 : ℂ) - 1 = (1 / 2 : ℂ) by norm_num]
    ring
  obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope f
    (fun t => (-(3 / 2 : ℂ) * (-γ t) ^ (1 / 2 : ℂ) * (z₂ - z₁)).re) zero_lt_one hcont hderiv
  have hc_bd : |(-(3 / 2 : ℂ) * (-γ c) ^ (1 / 2 : ℂ) * (z₂ - z₁)).re| ≤
      (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * ‖z₁ - z₂‖ := by
    have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM c ⟨hc.1.le, hc.2.le⟩)
    calc |(-(3 / 2 : ℂ) * (-γ c) ^ (1 / 2 : ℂ) * (z₂ - z₁)).re|
        ≤ ‖-(3 / 2 : ℂ) * (-γ c) ^ (1 / 2 : ℂ) * (z₂ - z₁)‖ := Complex.abs_re_le_norm _
      _ = (3 / 2 : ℝ) * ‖(-γ c) ^ (1 / 2 : ℂ)‖ * ‖z₁ - z₂‖ := by
          rw [norm_mul, norm_mul, norm_neg, show ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) by norm_num,
            norm_sub_rev]
      _ = (3 / 2 : ℝ) * ‖γ c‖ ^ (1 / 2 : ℝ) * ‖z₁ - z₂‖ := by
          rw [norm_cpow_half, norm_neg, Real.sqrt_eq_rpow]
      _ ≤ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * ‖z₁ - z₂‖ := by
          gcongr; exact hM c ⟨hc.1.le, hc.2.le⟩
  have hf0 : f 0 = ((-z₁) ^ (3 / 2 : ℂ)).re := by simp [f, γ]
  have hf1 : f 1 = ((-z₂) ^ (3 / 2 : ℂ)).re := by simp [f, γ]
  rw [sub_zero, div_one] at hc_slope
  rw [← hf0, ← hf1, abs_sub_comm, ← hc_slope]
  exact hc_bd

private lemma re_cpow_three_halves_lip_real {x₁ x₂ : ℝ} {M : ℝ}
    (hx₁ : ‖(x₁ : ℂ)‖ ≤ M) (hx₂ : ‖(x₂ : ℂ)‖ ≤ M) :
    |((-(x₁ : ℂ)) ^ (3 / 2 : ℂ)).re - ((-(x₂ : ℂ)) ^ (3 / 2 : ℂ)).re| ≤
      (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * ‖(x₁ : ℂ) - (x₂ : ℂ)‖ := by
  have hval : ∀ x : ℝ, ((-(x : ℂ)) ^ (3 / 2 : ℂ)).re = (max 0 (-x)) ^ (3 / 2 : ℝ) := fun x => by
    rcases le_total 0 x with hx | hx
    · have h0 : tipH (x : ℂ) = 0 := tipH_ofReal_nonneg hx
      unfold tipH at h0
      have hK := KTip_pos.ne'
      have hre : ((-(x : ℂ)) ^ (3 / 2 : ℂ)).re = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd (neg_eq_zero.mp h) hK
        · exact h
      rw [hre, max_eq_left (by linarith), Real.zero_rpow (by norm_num)]
    · have hnn : 0 ≤ -x := by linarith
      rw [max_eq_right hnn, show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; rfl,
        show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hnn, Complex.ofReal_re]
  rw [hval x₁, hval x₂]
  have hMnn : 0 ≤ M := (norm_nonneg _).trans hx₁
  let f : ℝ → ℝ := fun t => (max 0 (-t)) ^ (3 / 2 : ℝ)
  have hsub : ∀ a b : ℝ, a ≤ b → |a| ≤ M → |b| ≤ M →
      |f a - f b| ≤ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * |a - b| := by
    intro a b hab ha hb
    rcases le_total 0 a with ha0 | ha0
    · have hb0 : 0 ≤ b := ha0.trans hab
      simp [f, max_eq_left (by linarith : -a ≤ 0), max_eq_left (by linarith : -b ≤ 0)]
      positivity
    · rcases le_total 0 b with hb0 | hb0
      · have hal : |f a - f 0| ≤ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * |a - 0| := by
          rcases eq_or_lt_of_le ha0 with rfl | ha_lt
          · simp
          · have ha_pos : 0 < -a := neg_pos.mpr ha_lt
            have h0pow : (0 : ℝ) ^ (3 / 2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
            simp only [f, neg_zero, max_eq_right ha_pos.le, max_self, h0pow, sub_zero]
            have h1 : (-a) ^ (3 / 2 : ℝ) = (-a) * (-a) ^ (1 / 2 : ℝ) := by
              rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha_pos, Real.rpow_one]
            have h1nn : 0 ≤ (-a) ^ (1 / 2 : ℝ) := Real.rpow_nonneg ha_pos.le (1 / 2)
            rw [h1, abs_of_nonneg (mul_nonneg ha_pos.le h1nn), abs_of_nonpos ha0]
            have h2 : (-a) ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow ha_pos.le (by rwa [abs_of_nonpos ha0] at ha) (by norm_num)
            nlinarith
        have hbr : f b = f 0 := by simp [f, max_eq_left (by linarith : -b ≤ 0)]
        rw [hbr]
        have hle_dist : |a - 0| ≤ |a - b| := by
          rw [sub_zero, abs_of_nonpos ha0, abs_of_nonpos (sub_nonpos.mpr hab)]; linarith
        calc |f a - f 0| ≤ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * |a - 0| := hal
          _ ≤ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * |a - b| :=
            mul_le_mul_of_nonneg_left hle_dist (by positivity)
      · rcases eq_or_lt_of_le hab with rfl | hlt
        · simp
        · have hcont : ContinuousOn (fun t : ℝ => (-t) ^ (3 / 2 : ℝ)) (Icc a b) :=
            (continuous_id.neg.rpow_const (fun _ => Or.inr (by norm_num))).continuousOn
          have hder : ∀ t ∈ Ioo a b,
              HasDerivAt (fun t : ℝ => (-t) ^ (3 / 2 : ℝ)) (-(3 / 2 : ℝ) * (-t) ^ (1 / 2 : ℝ)) t := by
            intro t ht
            have hpos : 0 < -t := by linarith [ht.2, hb0]
            exact ((hasDerivAt_id t).neg.rpow_const (Or.inl hpos.ne')).congr_deriv (by simp; ring)
          obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => (-t) ^ (3 / 2 : ℝ))
            (fun t => -(3 / 2 : ℝ) * (-t) ^ (1 / 2 : ℝ)) hlt hcont hder
          have hfa : f a = (-a) ^ (3 / 2 : ℝ) := by dsimp [f]; rw [max_eq_right (by linarith)]
          have hfb : f b = (-b) ^ (3 / 2 : ℝ) := by dsimp [f]; rw [max_eq_right (by linarith)]
          rw [hfa, hfb]
          have hc_le : |-(3 / 2 : ℝ) * (-c) ^ (1 / 2 : ℝ)| ≤ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
            have hcnn : 0 ≤ -c := by linarith [hc.2, hb0]
            rw [abs_mul, abs_neg, abs_of_pos (by norm_num),
              abs_of_nonneg (Real.rpow_nonneg hcnn _)]
            have hcm : -c ≤ M := by linarith [hc.1, (abs_le.mp ha).1]
            gcongr
          have hmul := congrArg (· * (b - a)) hc_slope
          rw [div_mul_cancel₀ _ (sub_pos.mpr hlt).ne'] at hmul
          rw [abs_sub_comm ((-a) ^ (3 / 2 : ℝ)), ← hmul, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
          calc |-(3 / 2 : ℝ) * (-c) ^ (1 / 2 : ℝ)| * (b - a)
              ≤ (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * (b - a) :=
                mul_le_mul_of_nonneg_right hc_le (sub_pos.mpr hlt).le
            _ = (3 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * |a - b| := by
                rw [← abs_of_pos (sub_pos.mpr hlt), abs_sub_comm]
  have hx1' : |x₁| ≤ M := by simpa [Complex.norm_real, Real.norm_eq_abs] using hx₁
  have hx2' : |x₂| ≤ M := by simpa [Complex.norm_real, Real.norm_eq_abs] using hx₂
  rw [show ‖(x₁ : ℂ) - (x₂ : ℂ)‖ = |x₁ - x₂| by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]]
  rcases le_total x₁ x₂ with h12 | h21
  · exact hsub x₁ x₂ h12 hx1' hx2'
  · rw [abs_sub_comm (f x₁), abs_sub_comm x₁]
    exact hsub x₂ x₁ h21 hx2' hx1'

lemma tipH_disc_oscillation (ζ₀ ζ : ℂ)
    (hball : ζ ∈ ball ζ₀ ((1 / 2 : ℝ) * (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)))) :
    |tipH ζ - tipH ζ₀| ≤ 3 * KTip / 4 := by
  set r : ℝ := (1 / 2 : ℝ) * (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ))
  have hr_pos : 0 < r := by positivity
  have hr_bound : (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * r ≤ 1 / 2 := by
    have h1p : 1 ≤ 1 + ‖ζ₀‖ := by linarith [norm_nonneg ζ₀]
    have hr_le : r ≤ 1 / 2 := by
      have : (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h1p (by norm_num)
      dsimp [r]; linarith
    have hsq : ((‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * r) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((‖ζ₀‖ + r) ^ (1 / 2 : ℝ)) 2,
        ← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
      have hr2 : r ^ 2 = (1 / 4 : ℝ) * (1 + ‖ζ₀‖)⁻¹ := by
        dsimp [r]; rw [mul_pow, ← Real.rpow_natCast ((1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ))) 2,
          ← Real.rpow_mul (by positivity)]
        norm_num; rw [Real.rpow_neg_one]
      rw [hr2]
      have hle : ‖ζ₀‖ + r ≤ 1 + ‖ζ₀‖ := by linarith
      calc (‖ζ₀‖ + r) * ((1 / 4 : ℝ) * (1 + ‖ζ₀‖)⁻¹)
          ≤ (1 + ‖ζ₀‖) * ((1 / 4 : ℝ) * (1 + ‖ζ₀‖)⁻¹) := by gcongr
        _ = 1 / 4 := by field_simp [show (1 + ‖ζ₀‖) ≠ 0 by positivity]
        _ = (1 / 2 : ℝ) ^ 2 := by norm_num
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by norm_num)] at hsqrt
  have hM_ball : ∀ w ∈ ball ζ₀ r, ‖w‖ ≤ ‖ζ₀‖ + r := fun w hw => by
    calc ‖w‖ = ‖(w - ζ₀) + ζ₀‖ := by ring_nf
      _ ≤ ‖w - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
      _ ≤ r + ‖ζ₀‖ := by linarith [(dist_eq_norm w ζ₀ ▸ mem_ball.mp hw).le]
      _ = ‖ζ₀‖ + r := by ring
  have hM_seg : ∀ z₁ z₂ : ℂ, z₁ ∈ ball ζ₀ r → z₂ ∈ ball ζ₀ r →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - t) • z₁ + t • z₂‖ ≤ ‖ζ₀‖ + r := fun z₁ z₂ hz₁ hz₂ t ht =>
    hM_ball _ ((convex_ball ζ₀ r) hz₁ hz₂ (sub_nonneg.mpr ht.2) ht.1 (by ring))
  have hlip : ∀ z₁ z₂ : ℂ, z₁ ∈ ball ζ₀ r → z₂ ∈ ball ζ₀ r →
      |((-z₁) ^ (3 / 2 : ℂ)).re - ((-z₂) ^ (3 / 2 : ℂ)).re| ≤
        (3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖z₁ - z₂‖ := by
    intro z₁ z₂ hz₁ hz₂
    by_cases h1 : z₁.im = 0 ∧ z₂.im = 0
    · have hz1c : z₁ = (z₁.re : ℂ) := Complex.ext rfl h1.1
      have hz2c : z₂ = (z₂.re : ℂ) := Complex.ext rfl h1.2
      rw [hz1c, hz2c]
      exact re_cpow_three_halves_lip_real
        (by rw [← hz1c]; exact hM_ball z₁ hz₁) (by rw [← hz2c]; exact hM_ball z₂ hz₂)
    · have hhalf : ∀ {a b : ℂ}, a ∈ ball ζ₀ r → b ∈ ball ζ₀ r →
          (0 ≤ a.im ∧ 0 ≤ b.im ∧ (a.im ≠ 0 ∨ b.im ≠ 0) ∨
            a.im ≤ 0 ∧ b.im ≤ 0 ∧ (a.im ≠ 0 ∨ b.im ≠ 0)) →
          |((-a) ^ (3 / 2 : ℂ)).re - ((-b) ^ (3 / 2 : ℂ)).re| ≤
            (3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖a - b‖ := by
        intro a b ha hb hsign
        refine re_cpow_three_halves_lip_slit (fun t ht => ?_) (hM_seg a b ha hb)
        rw [Complex.mem_slitPlane_iff]; right
        have him_eq : (-((1 - t) • a + t • b)).im = -((1 - t) * a.im + t * b.im) := by
          rw [Complex.neg_im, Complex.add_im, Algebra.smul_def, Algebra.smul_def]
          simp [Complex.mul_im]
        rw [him_eq]
        rcases hsign with ⟨ha0, hb0, hor⟩ | ⟨ha0, hb0, hor⟩
        · have hpos : 0 < (1 - t) * a.im + t * b.im := by
            rcases hor with ha' | hb'
            · have : 0 < (1 - t) * a.im := mul_pos (sub_pos.mpr ht.2) (lt_of_le_of_ne ha0 ha'.symm)
              linarith [mul_nonneg ht.1.le hb0]
            · have : 0 < t * b.im := mul_pos ht.1 (lt_of_le_of_ne hb0 hb'.symm)
              linarith [mul_nonneg (sub_nonneg.mpr ht.2.le) ha0]
          linarith
        · have hneg : (1 - t) * a.im + t * b.im < 0 := by
            rcases hor with ha' | hb'
            · have : (1 - t) * a.im < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) (lt_of_le_of_ne ha0 ha')
              linarith [mul_nonpos_of_nonneg_of_nonpos ht.1.le hb0]
            · have : t * b.im < 0 := mul_neg_of_pos_of_neg ht.1 (lt_of_le_of_ne hb0 hb')
              linarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2.le) ha0]
          linarith
      by_cases hsame : (0 ≤ z₁.im ∧ 0 ≤ z₂.im) ∨ (z₁.im ≤ 0 ∧ z₂.im ≤ 0)
      · exact hhalf hz₁ hz₂ (by rcases hsame with ⟨a, b⟩ | ⟨a, b⟩ <;> [left; right] <;> exact ⟨a, b, not_and_or.mp h1⟩)
      · have hopp : (z₁.im < 0 ∧ 0 < z₂.im) ∨ (0 < z₁.im ∧ z₂.im < 0) := by
          rw [not_or] at hsame
          rcases lt_or_ge z₁.im 0 with h | h <;> rcases lt_or_ge z₂.im 0 with h' | h'
          · exact absurd ⟨h.le, h'.le⟩ hsame.2
          · left; refine ⟨h, lt_of_le_of_ne h' ?_⟩
            intro e; exact hsame.2 ⟨h.le, by linarith⟩
          · right; refine ⟨lt_of_le_of_ne h ?_, h'⟩
            intro e; exact hsame.2 ⟨by linarith, h'.le⟩
          · exact absurd ⟨h, h'⟩ hsame.1
        have hden : z₂.im - z₁.im ≠ 0 := by rcases hopp with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
        let t₀ : ℝ := -z₁.im / (z₂.im - z₁.im)
        have ht₀_0 : 0 < t₀ := by
          dsimp [t₀]; rcases hopp with ⟨a, b⟩ | ⟨a, b⟩
          · exact div_pos (by linarith) (by linarith)
          · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
        have ht₀_1 : t₀ < 1 := by
          dsimp [t₀]; rcases hopp with ⟨a, b⟩ | ⟨a, b⟩
          · rw [div_lt_one (by linarith)]; linarith
          · rw [div_lt_one_of_neg (by linarith)]; linarith
        let z₀ : ℂ := (1 - t₀) • z₁ + t₀ • z₂
        have hz₀_ball : z₀ ∈ ball ζ₀ r :=
          (convex_ball ζ₀ r) hz₁ hz₂ (sub_nonneg.mpr ht₀_1.le) ht₀_0.le (by ring)
        have hz₀_im : z₀.im = 0 := by
          dsimp [z₀, t₀]
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
          field_simp [hden]; ring
        have h1_part : |((-z₁) ^ (3 / 2 : ℂ)).re - ((-z₀) ^ (3 / 2 : ℂ)).re| ≤
            (3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖z₁ - z₀‖ := by
          refine hhalf hz₁ hz₀_ball ?_
          rcases hopp with ⟨a, _⟩ | ⟨a, _⟩
          · right; exact ⟨a.le, hz₀_im.le, Or.inl a.ne⟩
          · left; exact ⟨a.le, hz₀_im.ge, Or.inl a.ne'⟩
        have h2_part : |((-z₀) ^ (3 / 2 : ℂ)).re - ((-z₂) ^ (3 / 2 : ℂ)).re| ≤
            (3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖z₀ - z₂‖ := by
          refine hhalf hz₀_ball hz₂ ?_
          rcases hopp with ⟨_, b⟩ | ⟨_, b⟩
          · left; exact ⟨hz₀_im.ge, b.le, Or.inr b.ne'⟩
          · right; exact ⟨hz₀_im.le, b.le, Or.inr b.ne⟩
        have hcol : ‖z₁ - z₀‖ + ‖z₀ - z₂‖ = ‖z₁ - z₂‖ := by
          have hz10 : z₁ - z₀ = (t₀ : ℂ) * (z₁ - z₂) := by
            apply Complex.ext <;> dsimp [z₀] <;> simp <;> ring
          have hz02 : z₀ - z₂ = ((1 - t₀ : ℝ) : ℂ) * (z₁ - z₂) := by
            apply Complex.ext <;> dsimp [z₀] <;> simp <;> ring
          rw [hz10, hz02, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht₀_0,
            abs_of_pos (sub_pos.mpr ht₀_1)]
          ring
        calc |((-z₁) ^ (3 / 2 : ℂ)).re - ((-z₂) ^ (3 / 2 : ℂ)).re|
            ≤ |((-z₁) ^ (3 / 2 : ℂ)).re - ((-z₀) ^ (3 / 2 : ℂ)).re| +
                |((-z₀) ^ (3 / 2 : ℂ)).re - ((-z₂) ^ (3 / 2 : ℂ)).re| := abs_sub_le _ _ _
          _ ≤ (3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖z₁ - z₀‖ +
                (3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖z₀ - z₂‖ := add_le_add h1_part h2_part
          _ = (3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖z₁ - z₂‖ := by rw [← mul_add, hcol]
  unfold tipH
  rw [show -KTip * ((-ζ) ^ (3 / 2 : ℂ)).re - -KTip * ((-ζ₀) ^ (3 / 2 : ℂ)).re =
    KTip * (((-ζ₀) ^ (3 / 2 : ℂ)).re - ((-ζ) ^ (3 / 2 : ℂ)).re) by ring,
    abs_mul, abs_of_pos KTip_pos, abs_sub_comm]
  calc KTip * |((-ζ) ^ (3 / 2 : ℂ)).re - ((-ζ₀) ^ (3 / 2 : ℂ)).re|
      ≤ KTip * ((3 / 2 : ℝ) * (‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * ‖ζ - ζ₀‖) := by
        gcongr; exact KTip_pos.le; exact hlip ζ ζ₀ hball (mem_ball_self hr_pos)
    _ ≤ KTip * ((3 / 2 : ℝ) * ((‖ζ₀‖ + r) ^ (1 / 2 : ℝ) * r)) := by
        rw [mul_assoc (3 / 2 : ℝ)]
        gcongr; exact KTip_pos.le; exact (dist_eq_norm ζ ζ₀ ▸ mem_ball.mp hball).le
    _ ≤ KTip * ((3 / 2 : ℝ) * (1 / 2 : ℝ)) := by gcongr; exact KTip_pos.le
    _ = 3 * KTip / 4 := by ring

private lemma ae_im_ne_zero : ∀ᵐ ζ : ℂ, ζ.im ≠ 0 := by
  have h0 : volume ({ζ : ℂ | ζ.im = 0}) = 0 := by
    have hpre : {ζ : ℂ | ζ.im = 0} = Complex.measurableEquivRealProd ⁻¹' (univ ×ˢ {(0 : ℝ)}) := by
      ext ζ; simp [Complex.measurableEquivRealProd]
    rw [hpre, (Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet)),
      Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_singleton, mul_zero]
  exact ae_iff.mpr (by simpa using h0)

private lemma intervalIntegrable_posLog_inv_abs_zero (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => max 0 (Real.log (1 / |y|))) volume a b := by
  have hlog : IntervalIntegrable (fun y : ℝ => |Real.log y|) volume a b :=
    (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).abs
  have hmeas : Measurable (fun y : ℝ => max 0 (Real.log (1 / |y|))) :=
    Measurable.max measurable_const (Real.measurable_log.comp (measurable_const.div continuous_abs.measurable))
  refine hlog.mono_fun hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (le_max_left 0 _), Real.norm_of_nonneg (abs_nonneg (Real.log y))]
  by_cases hy : y = 0
  · subst hy; simp
  · rw [one_div, Real.log_inv, Real.log_abs]
    rcases le_total (-Real.log y) 0 with h | h
    · rw [max_eq_left h]; exact abs_nonneg _
    · rw [max_eq_right h, ← abs_neg]; exact le_abs_self _

private lemma integrable_posLog_inv_abs_zero :
    Integrable (fun y : ℝ => max 0 (Real.log (1 / |y|))) := by
  have hi := (intervalIntegrable_posLog_inv_abs_zero (-1) 1).1
  have hsupp : ∀ y ∉ Ioc (-1 : ℝ) 1, max 0 (Real.log (1 / |y|)) = 0 := fun y hy => by
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
    have hge : 1 ≤ |y| := by
      rcases hy with h1 | h2
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge (abs_nonneg _)))
  have hind : Integrable ((Ioc (-1 : ℝ) 1).indicator (fun y : ℝ => max 0 (Real.log (1 / |y|)))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hi
  refine hind.congr (Eventually.of_forall fun y => ?_)
  by_cases hmem : y ∈ Ioc (-1 : ℝ) 1
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem]; exact (hsupp y hmem).symm

private lemma integral_posLog_inv_abs_zero_eq_two :
    ∫ y : ℝ, max 0 (Real.log (1 / |y|)) = 2 := by
  have hsplit := integral_add_compl (s := Ioc (-1 : ℝ) 1) measurableSet_Ioc integrable_posLog_inv_abs_zero
  have hzero : ∫ y in (Ioc (-1 : ℝ) 1)ᶜ, max 0 (Real.log (1 / |y|)) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    rw [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hy
    have hge : 1 ≤ |y| := by
      rcases hy with h1 | h2
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge (abs_nonneg _)))
  rw [hzero, add_zero, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hsplit
  rw [← hsplit]
  have heq : EqOn (fun u : ℝ => max 0 (Real.log (1 / |u|))) (fun u => -Real.log u) (uIcc (-1 : ℝ) 1) := by
    intro u hu
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hu
    dsimp only
    by_cases hu0 : u = 0
    · subst hu0; simp
    · have hlog : 0 ≤ -Real.log u := by
        rw [← Real.log_abs, neg_nonneg]; exact Real.log_nonpos (abs_nonneg u) (abs_le.mpr hu)
      rw [one_div, Real.log_inv, Real.log_abs, max_eq_right hlog]
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_neg, integral_log]
  norm_num

private lemma integrable_posLog_div_abs_on_Icc (r a b : ℝ) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => max 0 (Real.log (r / |y|))) (Icc a b) := by
  have hsub : Integrable (fun y : ℝ => max 0 (Real.log (r / |y|))) := by
    have hmeas : Measurable (fun y : ℝ => max 0 (Real.log (r / |y|))) :=
      Measurable.max measurable_const (Real.measurable_log.comp (measurable_const.div continuous_abs.measurable))
    have hbox : IntervalIntegrable (fun y : ℝ => max 0 (Real.log r) + max 0 (Real.log (1 / |y|)))
        volume (-r) r :=
      intervalIntegrable_const.add (intervalIntegrable_posLog_inv_abs_zero (-r) r)
    have hind : Integrable ((Ioc (-r) r).indicator
        (fun y : ℝ => max 0 (Real.log r) + max 0 (Real.log (1 / |y|)))) :=
      (integrable_indicator_iff measurableSet_Ioc).mpr
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hbox)
    refine hind.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (le_max_left 0 _)]
    by_cases hy : y ∈ Ioc (-r) r
    · rw [indicator_of_mem hy]
      by_cases hy0 : y = 0
      · subst hy0; simp
      · have hy_pos : 0 < |y| := abs_pos.mpr hy0
        rw [show r / |y| = r * (1 / |y|) by ring, Real.log_mul hr.ne' (one_div_pos.mpr hy_pos).ne']
        rcases le_total (Real.log r + Real.log (1 / |y|)) 0 with h | h
        · rw [max_eq_left h]; positivity
        · rw [max_eq_right h]; exact add_le_add (le_max_right 0 (Real.log r)) (le_max_right 0 (Real.log (1 / |y|)))
    · rw [indicator_of_notMem hy]
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
      have hge : r ≤ |y| := by
        rcases hy with h1 | h2
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge (abs_nonneg _)))]
  exact hsub.integrableOn

private lemma integral_posLog_div_abs_eq (r : ℝ) (hr : 0 < r) :
    ∫ y : ℝ, max 0 (Real.log (r / |y|)) = 2 * r := by
  have heq : (fun y : ℝ => max 0 (Real.log (r / |y|))) =
      fun y => (fun u : ℝ => max 0 (Real.log (1 / |u|))) (r⁻¹ * y) := by
    ext y; dsimp only; rw [abs_mul, abs_of_pos (inv_pos.mpr hr)]; congr 2; field_simp [hr.ne']
  rw [heq, Measure.integral_comp_mul_left (fun u : ℝ => max 0 (Real.log (1 / |u|))) r⁻¹,
    inv_inv, abs_of_pos hr, smul_eq_mul, integral_posLog_inv_abs_zero_eq_two]
  ring

private lemma box_integral_im (x₁ x₂ y₁ y₂ : ℝ) (hx : x₁ ≤ x₂) (_hy : y₁ ≤ y₂) (f : ℝ → ℝ)
    (_hf : IntegrableOn f (Icc y₁ y₂)) :
    ∫ ζ in Complex.measurableEquivRealProd ⁻¹' (Icc x₁ x₂ ×ˢ Icc y₁ y₂), f ζ.im =
      (x₂ - x₁) * ∫ y in Icc y₁ y₂, f y := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  have h1 : ∫ ζ in Complex.measurableEquivRealProd ⁻¹' (Icc x₁ x₂ ×ˢ Icc y₁ y₂), f ζ.im =
      ∫ p in Icc x₁ x₂ ×ˢ Icc y₁ y₂, f p.2 := by
    have := hmp.setIntegral_preimage_emb Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => f p.2) (Icc x₁ x₂ ×ˢ Icc y₁ y₂)
    simpa [Complex.measurableEquivRealProd] using this
  rw [h1]
  have h2 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun _ : ℝ => (1 : ℝ)) f (Icc x₁ x₂) (Icc y₁ y₂)
  simp only [one_mul, integral_const, Measure.real_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hx), smul_eq_mul, mul_one,
    Measure.restrict_apply_univ] at h2
  exact h2

lemma disc_avg_neg_log_tipDist (ζ₀ : ℂ) :
    let r : ℝ := (1 / 2 : ℝ) * (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ))
    IntegrableOn (fun ζ : ℂ => -Real.log (tipDist ζ)) (ball ζ₀ r) ∧
      (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ)) ≤
        Real.log (1 / r) + Real.log 2 + 4 / π ∧
      (2 * r ≤ |ζ₀.im| →
        (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ)) ≤
          Real.log (4 / |ζ₀.im|)) ∧
      (|(-ζ₀).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ₀‖ →
        (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ)) ≤
          -Real.log (‖ζ₀‖ / 4)) := by
  intro r
  have hr_pos : 0 < r := by positivity
  have hr_le_half : r ≤ 1 / 2 := by
    have : (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg ζ₀]) (by norm_num)
    dsimp [r]; linarith
  have hlog2r_nn : 0 ≤ Real.log (2 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr_pos]; linarith)
  have hR_pos : 0 < ‖ζ₀‖ + r := by positivity
  have hball_ne_top : volume (ball ζ₀ r) ≠ ⊤ := by finiteness
  let box : Set (ℝ × ℝ) := Icc (ζ₀.re - r) (ζ₀.re + r) ×ˢ Icc (ζ₀.im - r) (ζ₀.im + r)
  have hpre : ball ζ₀ r ⊆ Complex.measurableEquivRealProd ⁻¹' box := fun ζ hζ => by
    have hdist := (dist_eq_norm ζ ζ₀ ▸ mem_ball.mp hζ).le
    have hre := (Complex.abs_re_le_norm (ζ - ζ₀)).trans hdist
    have him := (Complex.abs_im_le_norm (ζ - ζ₀)).trans hdist
    rw [Complex.sub_re, abs_le] at hre
    rw [Complex.sub_im, abs_le] at him
    change (ζ.re ∈ Icc (ζ₀.re - r) (ζ₀.re + r) ∧ ζ.im ∈ Icc (ζ₀.im - r) (ζ₀.im + r))
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hint_posLog_fun : ∀ c : ℝ, 0 < c →
      IntegrableOn (fun ζ : ℂ => max 0 (Real.log (c / |ζ.im|))) (ball ζ₀ r) := fun c hc => by
    have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (ζ₀.re - r) (ζ₀.re + r)) :=
      integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have h2 : IntegrableOn (fun y : ℝ => max 0 (Real.log (c / |y|))) (Icc (ζ₀.im - r) (ζ₀.im + r)) :=
      integrable_posLog_div_abs_on_Icc c _ _ hc
    have hbox_int : IntegrableOn (fun p : ℝ × ℝ => max 0 (Real.log (c / |p.2|))) box := by
      dsimp [box]
      rw [IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
      simpa using MeasureTheory.Integrable.mul_prod h1 h2
    have hcomp : IntegrableOn (fun ζ : ℂ => max 0 (Real.log (c / |ζ.im|)))
        (Complex.measurableEquivRealProd ⁻¹' box) := by
      have h := (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
        Complex.measurableEquivRealProd.measurableEmbedding).mpr hbox_int
      exact IntegrableOn.congr_fun h (fun _ _ => rfl)
        ((measurableSet_Icc.prod measurableSet_Icc).preimage Complex.measurableEquivRealProd.measurable)
    exact hcomp.mono_set hpre
  have hint_posLog := hint_posLog_fun 2 two_pos
  have hint_d : IntegrableOn (fun ζ : ℂ => -Real.log (tipDist ζ)) (ball ζ₀ r) := by
    let dom : ℂ → ℝ := fun ζ => max 0 (Real.log (2 / |ζ.im|)) + |Real.log (‖ζ₀‖ + r)|
    have hdom_int : IntegrableOn dom (ball ζ₀ r) :=
      hint_posLog.add (integrableOn_const hball_ne_top)
    have hmeas : Measurable (fun ζ : ℂ => -Real.log (tipDist ζ)) :=
      (Real.measurable_log.comp continuous_tipDist.measurable).neg
    refine hdom_int.mono' hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_ball).mpr ?_)
    filter_upwards [ae_im_ne_zero] with ζ him hζ
    have hnorm_le : ‖ζ‖ ≤ ‖ζ₀‖ + r := by
      calc ‖ζ‖ = ‖(ζ - ζ₀) + ζ₀‖ := by ring_nf
        _ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
        _ ≤ r + ‖ζ₀‖ := by linarith [(dist_eq_norm ζ ζ₀ ▸ mem_ball.mp hζ).le]
        _ = ‖ζ₀‖ + r := by ring
    have hd_pos : 0 < tipDist ζ := tipDist_pos_of_not_nonneg fun h => him h.1
    have hlo : -Real.log (‖ζ₀‖ + r) ≤ -Real.log (tipDist ζ) :=
      neg_le_neg (Real.log_le_log hd_pos ((tipDist_le_norm ζ).trans hnorm_le))
    have hhi : -Real.log (tipDist ζ) ≤ max 0 (Real.log (2 / |ζ.im|)) := by
      have him_pos : 0 < |ζ.im| := abs_pos.mpr him
      have h1 : -Real.log (tipDist ζ) ≤ Real.log (2 / |ζ.im|) := by
        rw [← Real.log_inv]
        refine Real.log_le_log (inv_pos.mpr hd_pos) ?_
        rw [inv_eq_one_div, div_le_div_iff₀ hd_pos him_pos]
        linarith [tipDist_ge_half_abs_im ζ]
      exact h1.trans (le_max_right 0 _)
    rw [Real.norm_eq_abs, abs_le]
    dsimp [dom]
    constructor <;> linarith [neg_abs_le (Real.log (‖ζ₀‖ + r)), le_abs_self (Real.log (‖ζ₀‖ + r)),
      le_max_left (0 : ℝ) (Real.log (2 / |ζ.im|))]
  have hball_vol : volume.real (ball ζ₀ r) = π * r ^ 2 := by
    rw [Measure.real_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr_pos.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  have hgen : (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ)) ≤
      Real.log (1 / r) + Real.log 2 + 4 / π := by
    have hint_r : IntegrableOn (fun ζ : ℂ => max 0 (Real.log (r / |ζ.im|))) (ball ζ₀ r) :=
      hint_posLog_fun r hr_pos
    have hpt : ∀ᵐ ζ ∂(volume.restrict (ball ζ₀ r)),
        -Real.log (tipDist ζ) ≤ Real.log (2 / r) + max 0 (Real.log (r / |ζ.im|)) := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [ae_im_ne_zero] with ζ him _
      have him_pos : 0 < |ζ.im| := abs_pos.mpr him
      have hd_pos : 0 < tipDist ζ := tipDist_pos_of_not_nonneg fun h => him h.1
      have h1 : -Real.log (tipDist ζ) ≤ Real.log (2 / |ζ.im|) := by
        rw [← Real.log_inv]
        refine Real.log_le_log (inv_pos.mpr hd_pos) ?_
        rw [inv_eq_one_div, div_le_div_iff₀ hd_pos him_pos]
        linarith [tipDist_ge_half_abs_im ζ]
      have h2 : Real.log (2 / |ζ.im|) = Real.log (2 / r) + Real.log (r / |ζ.im|) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; field_simp [hr_pos.ne', him_pos.ne']
      rw [h2] at h1
      linarith [le_max_right 0 (Real.log (r / |ζ.im|))]
    have hmono1 : ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ)) ≤
        ∫ ζ in ball ζ₀ r, (Real.log (2 / r) + max 0 (Real.log (r / |ζ.im|))) :=
      integral_mono_ae hint_d ((integrableOn_const hball_ne_top).add hint_r) hpt
    rw [integral_add (integrableOn_const hball_ne_top) hint_r,
      setIntegral_const, hball_vol, smul_eq_mul] at hmono1
    have hmono2 : ∫ ζ in ball ζ₀ r, max 0 (Real.log (r / |ζ.im|)) ≤
        ∫ ζ in Complex.measurableEquivRealProd ⁻¹' box, max 0 (Real.log (r / |ζ.im|)) := by
      refine setIntegral_mono_set ?_ (Eventually.of_forall fun _ => le_max_left 0 _) hpre.eventuallySubset
      have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (ζ₀.re - r) (ζ₀.re + r)) :=
        integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      have h2 : IntegrableOn (fun y : ℝ => max 0 (Real.log (r / |y|))) (Icc (ζ₀.im - r) (ζ₀.im + r)) :=
        integrable_posLog_div_abs_on_Icc r _ _ hr_pos
      have hbox_int : IntegrableOn (fun p : ℝ × ℝ => max 0 (Real.log (r / |p.2|))) box := by
        dsimp [box]
        rw [IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
        simpa using MeasureTheory.Integrable.mul_prod h1 h2
      exact (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
        Complex.measurableEquivRealProd.measurableEmbedding).mpr hbox_int
    have hbox_val : ∫ ζ in Complex.measurableEquivRealProd ⁻¹' box, max 0 (Real.log (r / |ζ.im|)) ≤ 4 * r ^ 2 := by
      rw [box_integral_im (ζ₀.re - r) (ζ₀.re + r) (ζ₀.im - r) (ζ₀.im + r)
        (by linarith) (by linarith) _ (integrable_posLog_div_abs_on_Icc r _ _ hr_pos)]
      have h_int : ∫ y in Icc (ζ₀.im - r) (ζ₀.im + r), max 0 (Real.log (r / |y|)) ≤ 2 * r := by
        calc ∫ y in Icc (ζ₀.im - r) (ζ₀.im + r), max 0 (Real.log (r / |y|))
            ≤ ∫ y : ℝ, max 0 (Real.log (r / |y|)) := by
              refine setIntegral_le_integral ?_ (Eventually.of_forall fun _ => le_max_left 0 _)
              have h_box := integrable_posLog_div_abs_on_Icc r (-r) r hr_pos
              have hind : Integrable ((Icc (-r) r).indicator
                  (fun y : ℝ => max 0 (Real.log (r / |y|)))) :=
                (integrable_indicator_iff measurableSet_Icc).mpr h_box
              refine hind.congr (Eventually.of_forall fun y => ?_)
              by_cases hy : y ∈ Icc (-r) r
              · rw [indicator_of_mem hy]
              · rw [indicator_of_notMem hy, mem_Icc, not_and_or, not_le, not_le] at *
                have hge : r ≤ |y| := by
                  rcases hy with h1 | h2
                  · rw [abs_of_nonpos (by linarith)]; linarith
                  · rw [abs_of_pos (by linarith)]; linarith
                exact (max_eq_left (Real.log_nonpos (by positivity)
                  (div_le_one_of_le₀ hge (abs_nonneg _)))).symm
          _ = 2 * r := integral_posLog_div_abs_eq r hr_pos
      nlinarith
    have hlog_split : Real.log (2 / r) = Real.log (1 / r) + Real.log 2 := by
      rw [← Real.log_mul (by positivity) two_pos.ne']; congr 1; ring
    have hpi_pos : 0 < π * r ^ 2 := by positivity
    calc (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ))
        ≤ (π * r ^ 2)⁻¹ * ((π * r ^ 2) * Real.log (2 / r) + 4 * r ^ 2) := by
          gcongr; linarith
      _ = Real.log (2 / r) + 4 / π := by field_simp [Real.pi_pos.ne', hr_pos.ne']
      _ = Real.log (1 / r) + Real.log 2 + 4 / π := by rw [hlog_split]
  refine ⟨hint_d, hgen, ?_, ?_⟩
  · intro him
    have him_pos : 0 < |ζ₀.im| := by linarith
    have hpt : ∀ᵐ ζ ∂(volume.restrict (ball ζ₀ r)),
        -Real.log (tipDist ζ) ≤ Real.log (4 / |ζ₀.im|) := by
      rw [ae_restrict_iff' measurableSet_ball]
      refine Eventually.of_forall fun ζ hζ => ?_
      have hdist := (Complex.abs_im_le_norm (ζ - ζ₀)).trans (dist_eq_norm ζ ζ₀ ▸ mem_ball.mp hζ).le
      rw [Complex.sub_im] at hdist
      have him_ζ : |ζ₀.im| / 2 ≤ |ζ.im| := by
        have h1 : |ζ₀.im| - |ζ.im| ≤ |ζ.im - ζ₀.im| := by
          rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
        linarith
      have hd_lb : |ζ₀.im| / 4 ≤ tipDist ζ := by linarith [tipDist_ge_half_abs_im ζ]
      have hd_pos : 0 < tipDist ζ := lt_of_lt_of_le (by positivity) hd_lb
      rw [← Real.log_inv]
      refine Real.log_le_log (inv_pos.mpr hd_pos) ?_
      rw [inv_eq_one_div, div_le_div_iff₀ hd_pos him_pos]
      linarith
    have hmono := integral_mono_ae hint_d (integrableOn_const hball_ne_top) hpt
    rw [setIntegral_const, hball_vol, smul_eq_mul] at hmono
    calc (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ))
        ≤ (π * r ^ 2)⁻¹ * ((π * r ^ 2) * Real.log (4 / |ζ₀.im|)) := by gcongr
      _ = Real.log (4 / |ζ₀.im|) := by field_simp [Real.pi_pos.ne', hr_pos.ne']
  · intro harg hnorm
    have hnorm_pos : 0 < ‖ζ₀‖ := by linarith
    have hpt : ∀ᵐ ζ ∂(volume.restrict (ball ζ₀ r)),
        -Real.log (tipDist ζ) ≤ -Real.log (‖ζ₀‖ / 4) := by
      rw [ae_restrict_iff' measurableSet_ball]
      refine Eventually.of_forall fun ζ hζ => ?_
      have hd := tipDist_sector_lower harg hnorm hζ
      exact neg_le_neg (Real.log_le_log (by positivity) hd)
    have hmono := integral_mono_ae hint_d (integrableOn_const hball_ne_top) hpt
    rw [setIntegral_const, hball_vol, smul_eq_mul] at hmono
    calc (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ))
        ≤ (π * r ^ 2)⁻¹ * ((π * r ^ 2) * (-Real.log (‖ζ₀‖ / 4))) := by gcongr
      _ = -Real.log (‖ζ₀‖ / 4) := by field_simp [Real.pi_pos.ne', hr_pos.ne']

/-! ### Section 3: Subharmonic disc average inequality from Jensen's formula -/

private lemma circleAverage_eq_integral_Ioo_neg_pi_pi (g : ℂ → ℝ) (c : ℂ) (ρ : ℝ) :
    Real.circleAverage g c ρ = (2 * π)⁻¹ * ∫ θ in Ioo (-π) π, g (circleMap c ρ θ) := by
  rw [Real.circleAverage_def, smul_eq_mul]
  congr 1
  have hper : Function.Periodic (fun θ => g (circleMap c ρ θ)) (2 * π) := by
    intro θ; simp [circleMap, add_mul, Complex.exp_add]
  have hshift := hper.intervalIntegral_add_eq (-π) 0
  rw [zero_add, show (-π) + 2 * π = π by ring] at hshift
  rw [← hshift, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm

private lemma quasiMeasurePreserving_polarCoord_symm :
    MeasureTheory.QuasiMeasurePreserving Complex.polarCoord.symm
      (volume.restrict Complex.polarCoord.target) volume := by
  have hcont : Continuous Complex.polarCoord.symm := by
    rw [show Complex.polarCoord.symm = Complex.equivRealProdCLM.symm ∘ polarCoord.symm from rfl]
    exact Complex.equivRealProdCLM.symm.continuous.comp continuous_polarCoord_symm
  refine ⟨hcont.measurable.aemeasurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply hcont.measurable hs]
  have hlin := Complex.lintegral_comp_polarCoord_symm (s.indicator (fun _ => (1 : ENNReal)))
  have hrhs : ∫⁻ p : ℂ, s.indicator (fun _ => (1 : ENNReal)) p = 0 := by
    rw [lintegral_indicator hs, setLIntegral_one, hs0]
  rw [hrhs] at hlin
  have hae : ∀ᵐ p ∂(volume.restrict Complex.polarCoord.target),
      ENNReal.ofReal p.1 • s.indicator (fun _ => (1 : ENNReal)) (Complex.polarCoord.symm p) = 0 :=
    (lintegral_eq_zero_iff ((Measurable.ennreal_ofReal measurable_fst).smul
      ((Measurable.indicator measurable_const hs).comp hcont.measurable))).mp hlin
  have hae_mem : ∀ᵐ p ∂(volume.restrict Complex.polarCoord.target),
      p ∉ Complex.polarCoord.symm ⁻¹' s := by
    rw [ae_restrict_iff' Complex.polarCoord.open_target.measurableSet] at hae ⊢
    refine hae.mono fun p hp hpt => ?_
    have hp1 : 0 < p.1 := by rw [Complex.polarCoord_target] at hpt; exact hpt.1
    have hpos : ENNReal.ofReal p.1 ≠ 0 := (ENNReal.ofReal_pos.mpr hp1).ne'
    have hmul0 : ENNReal.ofReal p.1 * s.indicator (fun _ => (1 : ENNReal)) (Complex.polarCoord.symm p) = 0 := by
      simpa [smul_eq_mul] using hp hpt
    have hind0 : s.indicator (fun _ => (1 : ENNReal)) (Complex.polarCoord.symm p) = 0 :=
      (mul_eq_zero.mp hmul0).resolve_left hpos
    intro hmem
    have hmem' : Complex.polarCoord.symm p ∈ s := hmem
    rw [indicator_of_mem hmem'] at hind0
    exact one_ne_zero hind0
  have heq : {p : ℝ × ℝ | ¬ p ∉ Complex.polarCoord.symm ⁻¹' s} = Complex.polarCoord.symm ⁻¹' s := by
    ext p; simp
  rw [← heq]
  exact ae_iff.mp hae_mem

/-- Subharmonic disc average inequality: if `f` is holomorphic on `closedBall ζ₀ r` (`r > 0`)
with `f ζ₀ ≠ 0`, and `Real.log ‖f ζ‖ ≤ B ζ` a.e. on `ball ζ₀ r` with `B` integrable on `ball ζ₀ r`,
then `Real.log ‖f ζ₀‖ ≤ (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, B ζ`. -/
theorem subharmonic_disc_avg_le {f : ℂ → ℂ} {B : ℂ → ℝ} {ζ₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall ζ₀ r)) (hf0 : f ζ₀ ≠ 0)
    (hB_int : IntegrableOn B (ball ζ₀ r))
    (hB_le : ∀ᵐ ζ ∂(volume.restrict (ball ζ₀ r)), Real.log ‖f ζ‖ ≤ B ζ) :
    Real.log ‖f ζ₀‖ ≤ (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, B ζ := by
  have hjensen : ∀ ρ ∈ Ioo 0 r, Real.log ‖f ζ₀‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) ζ₀ ρ := by
    intro ρ hρ
    have hρ_ne : ρ ≠ 0 := hρ.1.ne'
    have hsub : closedBall ζ₀ |ρ| ⊆ closedBall ζ₀ r := by
      rw [abs_of_pos hρ.1]; exact closedBall_subset_closedBall hρ.2.le
    have hform := (hf.mono hsub).circleAverage_log_norm hf0
    rw [hform]
    have hsum_nn : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall ζ₀ |ρ|) u : ℝ) *
        Real.log (ρ * ‖ζ₀ - u‖⁻¹) := by
      refine finsum_nonneg fun u => ?_
      by_cases hu : u ∈ closedBall ζ₀ |ρ|
      · by_cases huz : u = ζ₀
        · rw [huz]
          have hord : MeromorphicOn.divisor f (closedBall ζ₀ |ρ|) ζ₀ = 0 := by
            rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono hsub) (mem_closedBall_self (abs_nonneg ρ)),
              (hf ζ₀ (hsub (mem_closedBall_self (abs_nonneg ρ)))).analyticOrderAt_eq_zero.mpr hf0]
            simp
          simp [hord]
        · have hdiv_nn : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall ζ₀ |ρ|) u : ℝ) := by
            exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.mono hsub)) u
          have hnorm_pos : 0 < ‖ζ₀ - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huz))
          have hnorm_le : ‖ζ₀ - u‖ ≤ ρ := by
            rw [mem_closedBall, dist_eq_norm, norm_sub_rev, abs_of_pos hρ.1] at hu; exact hu
          have hlog_nn : 0 ≤ Real.log (ρ * ‖ζ₀ - u‖⁻¹) :=
            Real.log_nonneg (by rw [← div_eq_mul_inv, one_le_div hnorm_pos]; exact hnorm_le)
          exact mul_nonneg hdiv_nn hlog_nn
      · have hzero : MeromorphicOn.divisor f (closedBall ζ₀ |ρ|) u = 0 :=
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
        simp [hzero]
    linarith
  let G : ℂ → ℝ := (ball 0 r).indicator (fun w => B (ζ₀ + w))
  have hG_int : Integrable G := by
    have hcomp : IntegrableOn (fun w : ℂ => B (ζ₀ + w)) (ball 0 r) := by
      have hmp := measurePreserving_add_left (volume : Measure ℂ) ζ₀
      have h1 := (hmp.integrableOn_comp_preimage (Homeomorph.addLeft ζ₀).measurableEmbedding).mpr hB_int
      have hpre : (fun w : ℂ => ζ₀ + w) ⁻¹' ball ζ₀ r = ball 0 r := by
        ext w; simp [mem_ball, dist_eq_norm]
      rwa [hpre] at h1
    exact (integrable_indicator_iff measurableSet_ball).mpr hcomp
  have hB_eq_G : ∫ ζ in ball ζ₀ r, B ζ = ∫ w : ℂ, G w := by
    rw [← integral_indicator measurableSet_ball]
    have h1 := integral_add_left_eq_self (μ := (volume : Measure ℂ))
      (fun w : ℂ => (ball ζ₀ r).indicator B w) ζ₀
    rw [← h1]
    congr 1; ext w
    by_cases hw : w ∈ ball 0 r
    · have hw' : ζ₀ + w ∈ ball ζ₀ r := by simpa [mem_ball, dist_eq_norm] using hw
      simp [G, indicator_of_mem hw, indicator_of_mem hw']
    · have hw' : ζ₀ + w ∉ ball ζ₀ r := by simpa [mem_ball, dist_eq_norm] using hw
      simp [G, indicator_of_notMem hw, indicator_of_notMem hw']
  have hpolar := Complex.integral_comp_polarCoord_symm G
  have hpolar_int : IntegrableOn (fun p : ℝ × ℝ => p.1 * G (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
    have haes : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * G (Complex.polarCoord.symm p))
        (volume.restrict Complex.polarCoord.target) :=
      (continuous_fst.aestronglyMeasurable).mul
        (hG_int.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_polarCoord_symm)
    refine ⟨haes, ?_⟩
    have hlin := Complex.lintegral_comp_polarCoord_symm (fun w => ‖G w‖ₑ)
    have hfin : ∫⁻ w : ℂ, ‖G w‖ₑ < ⊤ := hG_int.hasFiniteIntegral
    rw [← hlin] at hfin
    refine lt_of_le_of_lt (setLIntegral_mono' Complex.polarCoord.open_target.measurableSet ?_) hfin
    intro p hp
    have hp1 : 0 < p.1 := by rw [Complex.polarCoord_target] at hp; exact hp.1
    rw [enorm_mul, Real.enorm_of_nonneg hp1.le]
    exact le_rfl
  have hprod_target_eq : (volume.restrict Complex.polarCoord.target : Measure (ℝ × ℝ)) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [Complex.polarCoord_target, Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
  have hG_polar_eq : ∫ ζ in ball ζ₀ r, B ζ =
      ∫ ρ in Ioo 0 r, ρ * ∫ θ in Ioo (-π) π, B (circleMap ζ₀ ρ θ) := by
    rw [hB_eq_G, ← hpolar]
    have hprod_int : Integrable (fun p : ℝ × ℝ => p.1 * G (Complex.polarCoord.symm p))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      rw [← hprod_target_eq]; exact hpolar_int
    have h1 : ∫ p in polarCoord.target, p.1 • G (Complex.polarCoord.symm p) =
        ∫ p : ℝ × ℝ, p.1 * G (Complex.polarCoord.symm p)
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      rw [← hprod_target_eq]; rfl
    rw [h1, integral_prod _ hprod_int]
    have hsplit : ∫ ρ in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, ρ * G (Complex.polarCoord.symm (ρ, θ)) =
        ∫ ρ in Ioo 0 r, ∫ θ in Ioo (-π) π, ρ * G (Complex.polarCoord.symm (ρ, θ)) := by
      have hIoi : Ioi (0 : ℝ) = Ioo 0 r ∪ Ici r := by
        ext ρ; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]; constructor
        · intro h; rcases lt_or_ge ρ r with h' | h'; exact Or.inl ⟨h, h'⟩; exact Or.inr h'
        · rintro (⟨h, _⟩ | h); exact h; linarith
      have hdisj : Disjoint (Ioo 0 r) (Ici r) :=
        Set.disjoint_left.mpr fun _ h1 h2 => by linarith [h1.2, mem_Ici.mp h2]
      have hint_outer : IntegrableOn (fun ρ => ∫ θ in Ioo (-π) π, ρ * G (Complex.polarCoord.symm (ρ, θ))) (Ioi 0) :=
        hprod_int.integral_prod_left
      rw [hIoi, setIntegral_union hdisj measurableSet_Ici (hint_outer.mono_set Ioo_subset_Ioi_self)
        (hint_outer.mono_set (Ici_subset_Ioi.mpr hr))]
      have hzero : ∫ ρ in Ici r, ∫ θ in Ioo (-π) π, ρ * G (Complex.polarCoord.symm (ρ, θ)) = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun ρ hρ => ?_
        have hinner : (fun θ : ℝ => ρ * G (Complex.polarCoord.symm (ρ, θ))) = 0 := by
          ext θ
          have hnot : Complex.polarCoord.symm (ρ, θ) ∉ ball (0 : ℂ) r := by
            simp only [mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, not_lt]
            exact (mem_Ici.mp hρ).trans (le_abs_self ρ)
          dsimp [G]
          rw [indicator_of_notMem hnot, mul_zero]
        rw [hinner]; simp
      rw [hzero, add_zero]
    rw [hsplit]
    refine setIntegral_congr_fun measurableSet_Ioo fun ρ hρ => ?_
    rw [integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    have hmem : Complex.polarCoord.symm (ρ, θ) ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hρ.1]; exact hρ.2
    rw [show G (Complex.polarCoord.symm (ρ, θ)) = B (ζ₀ + Complex.polarCoord.symm (ρ, θ)) from
      indicator_of_mem hmem _]
    congr 2
    simp [Complex.exp_mul_I]
  have hprod_box_int : Integrable (fun p : ℝ × ℝ => p.1 * G (Complex.polarCoord.symm p))
      ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-π) π))) := by
    have hsub : Ioo 0 r ×ˢ Ioo (-π) π ⊆ Complex.polarCoord.target := by
      rw [Complex.polarCoord_target]; exact prod_mono Ioo_subset_Ioi_self Subset.rfl
    have h1 := hpolar_int.mono_set hsub
    change IntegrableOn (fun p : ℝ × ℝ => p.1 * G (Complex.polarCoord.symm p)) (Ioo 0 r ×ˢ Ioo (-π) π) at h1
    unfold IntegrableOn at h1
    rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at h1
    exact h1
  have hae_ρ_int : ∀ᵐ ρ ∂(volume.restrict (Ioo 0 r)),
      IntegrableOn (fun θ => B (circleMap ζ₀ ρ θ)) (Ioo (-π) π) := by
    filter_upwards [hprod_box_int.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with ρ hρ_int hρ
    have h1 : IntegrableOn (fun θ => G (Complex.polarCoord.symm (ρ, θ))) (Ioo (-π) π) := by
      have h2 := hρ_int.const_mul ρ⁻¹
      refine IntegrableOn.congr_fun h2 (fun θ _ => ?_) measurableSet_Ioo
      change ρ⁻¹ * (ρ * G (Complex.polarCoord.symm (ρ, θ))) = G (Complex.polarCoord.symm (ρ, θ))
      rw [← mul_assoc, inv_mul_cancel₀ hρ.1.ne', one_mul]
    refine IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Ioo
    have hmem : Complex.polarCoord.symm (ρ, θ) ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hρ.1]; exact hρ.2
    have hG_eq : G (Complex.polarCoord.symm (ρ, θ)) = B (ζ₀ + Complex.polarCoord.symm (ρ, θ)) :=
      indicator_of_mem hmem _
    rw [hG_eq]
    congr 2
    simp [Complex.exp_mul_I]
  have hae_ρ_le : ∀ᵐ ρ ∂(volume.restrict (Ioo 0 r)),
      ∀ᵐ θ ∂(volume.restrict (Ioo (-π) π)),
        Real.log ‖f (circleMap ζ₀ ρ θ)‖ ≤ B (circleMap ζ₀ ρ θ) := by
    let bad : Set ℂ := {ζ | ζ ∈ ball ζ₀ r ∧ ¬ Real.log ‖f ζ‖ ≤ B ζ}
    have hbad_null : volume bad = 0 := by
      have h := ae_iff.mp ((ae_restrict_iff' measurableSet_ball).mp hB_le)
      simpa [bad, not_imp] using h
    let badM : Set ℂ := toMeasurable volume bad
    have hbadM_meas : MeasurableSet badM := measurableSet_toMeasurable volume bad
    have hbadM_null : volume badM = 0 := (measure_toMeasurable bad).trans hbad_null
    let bad0 : Set ℂ := (fun w => ζ₀ + w) ⁻¹' badM
    have hbad0_meas : MeasurableSet bad0 := hbadM_meas.preimage (continuous_const.add continuous_id).measurable
    have hbad0_null : volume bad0 = 0 := by
      have hmp := measurePreserving_add_left (volume : Measure ℂ) ζ₀
      rw [hmp.measure_preimage hbadM_meas.nullMeasurableSet, hbadM_null]
    have hqmp := MeasureTheory.QuasiMeasurePreserving.preimage_null
      quasiMeasurePreserving_polarCoord_symm hbad0_null
    have hcont_symm : Continuous Complex.polarCoord.symm := by
      rw [show Complex.polarCoord.symm = Complex.equivRealProdCLM.symm ∘ polarCoord.symm from rfl]
      exact Complex.equivRealProdCLM.symm.continuous.comp continuous_polarCoord_symm
    let S : Set (ℝ × ℝ) := Complex.polarCoord.symm ⁻¹' bad0
    have hS_meas : MeasurableSet S := hbad0_meas.preimage hcont_symm.measurable
    have hS_null : ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-π) π))) S = 0 := by
      have hsub : Ioo 0 r ×ˢ Ioo (-π) π ⊆ Complex.polarCoord.target := by
        rw [Complex.polarCoord_target]; exact prod_mono Ioo_subset_Ioi_self Subset.rfl
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
      exact le_antisymm ((Measure.restrict_mono hsub le_rfl S).trans (le_of_eq hqmp)) bot_le
    rw [Measure.prod_apply hS_meas] at hS_null
    have hae_sec : ∀ᵐ ρ ∂(volume.restrict (Ioo 0 r)),
        volume.restrict (Ioo (-π) π) (Prod.mk ρ ⁻¹' S) = 0 :=
      (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS_meas)).mp hS_null
    filter_upwards [hae_sec, ae_restrict_mem measurableSet_Ioo] with ρ hρ_sec hρ
    have hae_θ : ∀ᵐ θ ∂(volume.restrict (Ioo (-π) π)), (ρ, θ) ∉ S :=
      ae_iff.mpr (by
        have heq : {θ : ℝ | ¬(ρ, θ) ∉ S} = Prod.mk ρ ⁻¹' S := by ext θ; simp
        rwa [heq])
    filter_upwards [hae_θ, ae_restrict_mem measurableSet_Ioo] with θ hθ_not _
    by_contra hnot
    apply hθ_not
    change ζ₀ + Complex.polarCoord.symm (ρ, θ) ∈ badM
    apply subset_toMeasurable volume bad
    have hcirc : ζ₀ + Complex.polarCoord.symm (ρ, θ) = circleMap ζ₀ ρ θ := by
      simp [circleMap, Complex.exp_mul_I]
    rw [hcirc]
    refine ⟨?_, hnot⟩
    rw [mem_ball, mem_sphere.mp (circleMap_mem_sphere ζ₀ hρ.1.le θ)]
    exact hρ.2
  -- Step 3: Integrate `Real.log ‖f ζ₀‖ ≤ (2π)⁻¹ ∫ B(circleMap ζ₀ ρ θ) dθ` weighted by `2 π ρ` on `Ioo 0 r`.
  have hρ_le_avg : ∀ᵐ ρ ∂(volume.restrict (Ioo 0 r)),
      2 * π * ρ * Real.log ‖f ζ₀‖ ≤ ρ * ∫ θ in Ioo (-π) π, B (circleMap ζ₀ ρ θ) := by
    filter_upwards [hae_ρ_int, hae_ρ_le, ae_restrict_mem measurableSet_Ioo] with ρ hρ_int hρ_le hρ
    have hjen := hjensen ρ hρ
    have hcirc_int : CircleIntegrable (fun z => Real.log ‖f z‖) ζ₀ ρ := by
      have hsub : closedBall ζ₀ |ρ| ⊆ closedBall ζ₀ r := by
        rw [abs_of_pos hρ.1]; exact closedBall_subset_closedBall hρ.2.le
      exact ((hf.mono hsub).mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    have hlog_eq : Real.circleAverage (fun z => Real.log ‖f z‖) ζ₀ ρ =
        (2 * π)⁻¹ * ∫ θ in Ioo (-π) π, Real.log ‖f (circleMap ζ₀ ρ θ)‖ :=
      circleAverage_eq_integral_Ioo_neg_pi_pi _ _ _
    have hint_log : IntegrableOn (fun θ => Real.log ‖f (circleMap ζ₀ ρ θ)‖) (Ioo (-π) π) := by
      have hper : Function.Periodic (fun θ => Real.log ‖f (circleMap ζ₀ ρ θ)‖) (2 * π) := by
        intro θ; simp [circleMap, add_mul, Complex.exp_add]
      have h2 := hper.intervalIntegrable₀ (by positivity : (2 * π : ℝ) ≠ 0) hcirc_int (-π) π
      have h3 := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos] : -π ≤ π)).1 h2
      exact h3.congr_set_ae Ioo_ae_eq_Ioc
    have hmono : ∫ θ in Ioo (-π) π, Real.log ‖f (circleMap ζ₀ ρ θ)‖ ≤
        ∫ θ in Ioo (-π) π, B (circleMap ζ₀ ρ θ) :=
      integral_mono_ae hint_log hρ_int hρ_le
    rw [hlog_eq] at hjen
    have hmul := mul_le_mul_of_nonneg_left hjen (mul_nonneg (mul_nonneg two_pos.le Real.pi_pos.le) hρ.1.le)
    calc 2 * π * ρ * Real.log ‖f ζ₀‖
        ≤ 2 * π * ρ * ((2 * π)⁻¹ * ∫ θ in Ioo (-π) π, Real.log ‖f (circleMap ζ₀ ρ θ)‖) := hmul
      _ = ρ * ∫ θ in Ioo (-π) π, Real.log ‖f (circleMap ζ₀ ρ θ)‖ := by
          field_simp [Real.pi_pos.ne']
      _ ≤ ρ * ∫ θ in Ioo (-π) π, B (circleMap ζ₀ ρ θ) :=
          mul_le_mul_of_nonneg_left hmono hρ.1.le
  have hint_lhs : IntegrableOn (fun ρ : ℝ => 2 * π * ρ * Real.log ‖f ζ₀‖) (Ioo 0 r) :=
    ((continuous_const.mul continuous_id).mul continuous_const).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hint_rhs : IntegrableOn (fun ρ : ℝ => ρ * ∫ θ in Ioo (-π) π, B (circleMap ζ₀ ρ θ)) (Ioo 0 r) := by
    have h1 := hprod_box_int.integral_prod_left
    refine IntegrableOn.congr_fun h1 (fun ρ hρ => ?_) measurableSet_Ioo
    dsimp only
    rw [integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    have hmem : Complex.polarCoord.symm (ρ, θ) ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hρ.1]; exact hρ.2
    have hG_eq : G (Complex.polarCoord.symm (ρ, θ)) = B (ζ₀ + Complex.polarCoord.symm (ρ, θ)) :=
      indicator_of_mem hmem _
    rw [hG_eq]
    congr 2
    simp [Complex.exp_mul_I]
  have hint_mono := integral_mono_ae hint_lhs hint_rhs hρ_le_avg
  have hlhs_val : ∫ ρ in Ioo 0 r, 2 * π * ρ * Real.log ‖f ζ₀‖ = π * r ^ 2 * Real.log ‖f ζ₀‖ := by
    have hcon : (fun ρ : ℝ => 2 * π * ρ * Real.log ‖f ζ₀‖) =
        fun ρ => (2 * π * Real.log ‖f ζ₀‖) * ρ := funext fun ρ => by ring
    rw [hcon, integral_const_mul, setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le hr.le, integral_id, zero_pow two_ne_zero, sub_zero]
    ring
  rw [hlhs_val, ← hG_polar_eq] at hint_mono
  have hpi_pos : 0 < π * r ^ 2 := by positivity
  calc Real.log ‖f ζ₀‖ = (π * r ^ 2)⁻¹ * (π * r ^ 2 * Real.log ‖f ζ₀‖) := by
        field_simp [Real.pi_pos.ne', hr.ne']
    _ ≤ (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, B ζ := mul_le_mul_of_nonneg_left hint_mono (by positivity)

/-! ### Section 4: Elementary injectivity of `ℬ` on `ℍ` and Lemma T1 (tip map) -/

/-- Elementary algebraic injectivity of `slitBoundaryMapC` on the open upper half-plane `{z | 0 < z.im}`. -/
theorem slitBoundaryMapC_injOn_UHP :
    Set.InjOn slitBoundaryMapC {z : ℂ | 0 < z.im} := by
  intro z₁ hz₁ z₂ hz₂ hEq
  unfold slitBoundaryMapC at hEq
  have hpi : ((2 * π : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
  have hlog : Complex.log ((z₁ - 1) / (z₁ * (z₁ + 1))) =
      Complex.log ((z₂ - 1) / (z₂ * (z₂ + 1))) :=
    mul_left_cancel₀ hpi hEq
  have hne : ∀ z : ℂ, 0 < z.im → (z - 1) / (z * (z + 1)) ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    have hz1 : z - 1 ≠ 0 := fun h => by
      have : z = 1 := sub_eq_zero.mp h; simp [this] at hz
    have hz2 : z + 1 ≠ 0 := fun h => by
      have : z = -1 := eq_neg_of_add_eq_zero_left h; simp [this] at hz
    exact div_ne_zero hz1 (mul_ne_zero hz0 hz2)
  have hrat : (z₁ - 1) / (z₁ * (z₁ + 1)) = (z₂ - 1) / (z₂ * (z₂ + 1)) := by
    have := congrArg Complex.exp hlog
    rwa [Complex.exp_log (hne z₁ hz₁), Complex.exp_log (hne z₂ hz₂)] at this
  have hz1_0 : z₁ ≠ 0 := fun h => by simp [h] at hz₁
  have hz1_p : z₁ + 1 ≠ 0 := fun h => by
    have : z₁ = -1 := eq_neg_of_add_eq_zero_left h; simp [this] at hz₁
  have hz2_0 : z₂ ≠ 0 := fun h => by simp [h] at hz₂
  have hz2_p : z₂ + 1 ≠ 0 := fun h => by
    have : z₂ = -1 := eq_neg_of_add_eq_zero_left h; simp [this] at hz₂
  have hcross : (z₁ - 1) * (z₂ * (z₂ + 1)) = (z₂ - 1) * (z₁ * (z₁ + 1)) :=
    (div_eq_div_iff (mul_ne_zero hz1_0 hz1_p) (mul_ne_zero hz2_0 hz2_p)).mp hrat
  have hfac : (z₁ - z₂) * (1 + z₁ + z₂ - z₁ * z₂) = 0 := by linear_combination hcross
  by_contra hne12
  have hquad : 1 + z₁ + z₂ - z₁ * z₂ = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne12)
  have hz1_m : z₁ - 1 ≠ 0 := fun h => by
    have : z₁ = 1 := sub_eq_zero.mp h; simp [this] at hz₁
  have hz2_eq : z₂ = 1 + 2 / (z₁ - 1) := by
    field_simp [hz1_m]; linear_combination -hquad
  have him : z₂.im = -2 * z₁.im / Complex.normSq (z₁ - 1) := by
    rw [hz2_eq, Complex.add_im, Complex.one_im, zero_add, div_eq_mul_inv, Complex.mul_im]
    simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero, Complex.inv_im, Complex.sub_im,
      Complex.one_im, sub_zero]
    ring
  have hz1_im_pos : 0 < z₁.im := hz₁
  have hz2_im_pos : 0 < z₂.im := hz₂
  have hns_pos : 0 < Complex.normSq (z₁ - 1) := Complex.normSq_pos.mpr hz1_m
  have hneg : z₂.im < 0 := by rw [him]; exact div_neg_of_neg_of_pos (by linarith) hns_pos
  linarith

private lemma slitBoundaryMapC_ofReal_Ioo {σ : ℝ} (hσ : σ ∈ Ioo (-1) 0) :
    slitBoundaryMapC (σ : ℂ) = (slitBoundaryMap σ : ℂ) := by
  unfold slitBoundaryMapC slitBoundaryMap
  have hpos : 0 < (1 - σ) / ((-σ) * (1 + σ)) := by
    have h1 : 0 < 1 - σ := by linarith [hσ.2]
    have h2 : 0 < -σ := by linarith [hσ.2]
    have h3 : 0 < 1 + σ := by linarith [hσ.1]
    positivity
  have h1 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.2.ne
  have h2 : (σ : ℂ) + 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by linarith [hσ.1])
  have h2' : (1 : ℂ) + (σ : ℂ) ≠ 0 := by rw [add_comm]; exact h2
  have hrat : ((σ : ℂ) - 1) / ((σ : ℂ) * ((σ : ℂ) + 1)) =
      (((1 - σ) / ((-σ) * (1 + σ)) : ℝ) : ℂ) := by
    push_cast; field_simp [h1, h2, h2']; ring
  rw [hrat, ← Complex.ofReal_log hpos.le]
  push_cast; rfl

private lemma slitBoundaryMapC_analyticAt_sigmaStar :
    AnalyticAt ℂ slitBoundaryMapC (sigmaStar : ℂ) := by
  have hσ : sigmaStar ∈ Ioo (-1 : ℝ) 0 :=
    ⟨by linarith [sigmaStar_gt_neg_half], sigmaStar_neg⟩
  have hpos : 0 < (1 - sigmaStar) / ((-sigmaStar) * (1 + sigmaStar)) := by
    have h1 : 0 < 1 - sigmaStar := by linarith [hσ.2]
    have h2 : 0 < -sigmaStar := by linarith [hσ.2]
    have h3 : 0 < 1 + sigmaStar := by linarith [hσ.1]
    positivity
  have h1 : (sigmaStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr sigmaStar_neg.ne
  have h2 : (sigmaStar : ℂ) + 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by linarith [sigmaStar_gt_neg_half])
  have h2' : (1 : ℂ) + (sigmaStar : ℂ) ≠ 0 := by rw [add_comm]; exact h2
  have hrat_eq : ((sigmaStar : ℂ) - 1) / ((sigmaStar : ℂ) * ((sigmaStar : ℂ) + 1)) =
      (((1 - sigmaStar) / ((-sigmaStar) * (1 + sigmaStar)) : ℝ) : ℂ) := by
    push_cast; field_simp [h1, h2, h2']; ring
  have hmem_re : (((1 - sigmaStar) / ((-sigmaStar) * (1 + sigmaStar)) : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; rw [Complex.ofReal_re]; exact hpos
  have hmem : ((sigmaStar : ℂ) - 1) / ((sigmaStar : ℂ) * ((sigmaStar : ℂ) + 1)) ∈ Complex.slitPlane := by
    rwa [hrat_eq]
  have hrat_an : AnalyticAt ℂ (fun z : ℂ => (z - 1) / (z * (z + 1))) (sigmaStar : ℂ) :=
    ((analyticAt_id (𝕜 := ℂ) |>.sub analyticAt_const).div
      ((analyticAt_id (𝕜 := ℂ)).mul ((analyticAt_id (𝕜 := ℂ)).add analyticAt_const))
      (mul_ne_zero h1 h2))
  exact analyticAt_const.mul (hrat_an.clog hmem)

private lemma hasDerivAt_slitBoundaryMapC_near_sigmaStar :
    ∀ᶠ z in 𝓝 (sigmaStar : ℂ),
      HasDerivAt slitBoundaryMapC
        (-((z - (sigmaStar : ℂ)) * (z - (sigmaPlus : ℂ))) /
          (2 * (π : ℂ) * z * (z ^ 2 - 1))) z := by
  have hσ : sigmaStar ∈ Ioo (-1 : ℝ) 0 :=
    ⟨by linarith [sigmaStar_gt_neg_half], sigmaStar_neg⟩
  have h1 : (sigmaStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.2.ne
  have h2 : (sigmaStar : ℂ) + 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by linarith [hσ.1])
  have h2' : (1 : ℂ) + (sigmaStar : ℂ) ≠ 0 := by rw [add_comm]; exact h2
  have hopen_rat : ∀ᶠ z in 𝓝 (sigmaStar : ℂ),
      ((z - 1) / (z * (z + 1)) ∈ Complex.slitPlane) ∧ z ≠ 0 ∧ z - 1 ≠ 0 ∧ z + 1 ≠ 0 := by
    have hpos : 0 < (1 - sigmaStar) / ((-sigmaStar) * (1 + sigmaStar)) := by
      have ha : 0 < 1 - sigmaStar := by linarith [hσ.2]
      have hb : 0 < -sigmaStar := by linarith [hσ.2]
      have hc : 0 < 1 + sigmaStar := by linarith [hσ.1]
      positivity
    have hrat_eq : ((sigmaStar : ℂ) - 1) / ((sigmaStar : ℂ) * ((sigmaStar : ℂ) + 1)) =
        (((1 - sigmaStar) / ((-sigmaStar) * (1 + sigmaStar)) : ℝ) : ℂ) := by
      push_cast; field_simp [h1, h2, h2']; ring
    have hcont : ContinuousAt (fun z : ℂ => (z - 1) / (z * (z + 1))) (sigmaStar : ℂ) :=
      ((continuousAt_id (X := ℂ) |>.sub continuousAt_const).div
        ((continuousAt_id (X := ℂ)).mul ((continuousAt_id (X := ℂ)).add continuousAt_const))
        (mul_ne_zero h1 h2))
    have hmem_re : (((1 - sigmaStar) / ((-sigmaStar) * (1 + sigmaStar)) : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; rw [Complex.ofReal_re]; exact hpos
    have hslit : ∀ᶠ z in 𝓝 (sigmaStar : ℂ), (z - 1) / (z * (z + 1)) ∈ Complex.slitPlane :=
      hcont.eventually (Complex.isOpen_slitPlane.mem_nhds (by
        change ((sigmaStar : ℂ) - 1) / ((sigmaStar : ℂ) * ((sigmaStar : ℂ) + 1)) ∈ Complex.slitPlane
        rwa [hrat_eq]))
    have hne0 : ∀ᶠ z in 𝓝 (sigmaStar : ℂ), z ≠ 0 :=
      continuousAt_id.eventually_ne h1
    have hne1 : ∀ᶠ z in 𝓝 (sigmaStar : ℂ), z - 1 ≠ 0 := by
      have hne_val : (sigmaStar : ℂ) - 1 ≠ 0 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        exact Complex.ofReal_ne_zero.mpr (by linarith [hσ.2])
      exact (continuousAt_id.sub continuousAt_const).eventually_ne hne_val
    have hnep1 : ∀ᶠ z in 𝓝 (sigmaStar : ℂ), z + 1 ≠ 0 :=
      (continuousAt_id.add continuousAt_const).eventually_ne h2
    exact hslit.and (hne0.and (hne1.and hnep1))
  filter_upwards [hopen_rat] with z ⟨hz_slit, hz0, hz1, hzp1⟩
  let r : ℂ → ℂ := fun w => (w - 1) / (w * (w + 1))
  have hr_deriv : HasDerivAt r
      ((1 * (z * (z + 1)) - (z - 1) * (1 * (z + 1) + z * 1)) / (z * (z + 1)) ^ 2) z :=
    ((hasDerivAt_id z).sub_const 1).div
      ((hasDerivAt_id z).mul ((hasDerivAt_id z).add_const 1)) (mul_ne_zero hz0 hzp1)
  have hlog : HasDerivAt (fun w => Complex.log (r w))
      ((r z)⁻¹ * ((1 * (z * (z + 1)) - (z - 1) * (1 * (z + 1) + z * 1)) / (z * (z + 1)) ^ 2)) z := by
    have hz_slit' : r z ∈ Complex.slitPlane := hz_slit
    exact (Complex.hasDerivAt_log hz_slit').comp z hr_deriv
  have hB : HasDerivAt slitBoundaryMapC (((2 * π : ℝ) : ℂ)⁻¹ *
      ((r z)⁻¹ * ((1 * (z * (z + 1)) - (z - 1) * (1 * (z + 1) + z * 1)) / (z * (z + 1)) ^ 2))) z :=
    hlog.const_mul _
  refine hB.congr_deriv ?_
  have hsq : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnum : 1 * (z * (z + 1)) - (z - 1) * (1 * (z + 1) + z * 1) =
      -((z - (sigmaStar : ℂ)) * (z - (sigmaPlus : ℂ))) := by
    unfold sigmaStar sigmaPlus; push_cast; linear_combination -hsq
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hz2 : z ^ 2 - 1 ≠ 0 := by
    rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring]; exact mul_ne_zero hz1 hzp1
  dsimp [r]; rw [hnum]
  push_cast
  field_simp [hz0, hz1, hzp1, hpi, hz2]
  ring

private lemma tipPsi_exists :
    ∃ (r_ψ : ℝ) (tipPsi : ℂ → ℂ), 0 < r_ψ ∧
      AnalyticOnNhd ℂ tipPsi (ball 0 r_ψ) ∧
      tipPsi 0 = 0 ∧
      deriv tipPsi 0 = (1 / √slitQ : ℂ) ∧
      (∀ v : ℝ, |v| < r_ψ → (tipPsi (v : ℂ)).im = 0) ∧
      (∀ v ∈ ball (0 : ℂ) r_ψ,
        slitBoundaryMapC ((sigmaStar : ℂ) + tipPsi v) = (xiStar : ℂ) + v ^ 2) := by
  let B₀ : ℂ → ℂ := fun w => slitBoundaryMapC ((sigmaStar : ℂ) + w) - (xiStar : ℂ)
  have hB₀_an : AnalyticAt ℂ B₀ 0 := by
    have hcomp : AnalyticAt ℂ (fun w : ℂ => slitBoundaryMapC ((sigmaStar : ℂ) + w)) 0 := by
      have hid : AnalyticAt ℂ (fun w : ℂ => (sigmaStar : ℂ) + w) 0 :=
        analyticAt_const.add (analyticAt_id (𝕜 := ℂ))
      have h0 : AnalyticAt ℂ slitBoundaryMapC ((fun w : ℂ => (sigmaStar : ℂ) + w) 0) := by
        dsimp only; rw [add_zero]; exact slitBoundaryMapC_analyticAt_sigmaStar
      exact h0.comp hid
    exact hcomp.sub analyticAt_const
  have hB₀_0 : B₀ 0 = 0 := by
    dsimp [B₀]
    have hσ : sigmaStar ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [sigmaStar_gt_neg_half], sigmaStar_neg⟩
    rw [add_zero, slitBoundaryMapC_ofReal_Ioo hσ, slitBoundaryMap_sigmaStar, sub_self]
  have hB₀_deriv_nhds : ∀ᶠ w in 𝓝 (0 : ℂ),
      HasDerivAt B₀
        (-((w * ((sigmaStar : ℂ) + w - (sigmaPlus : ℂ))) /
          (2 * (π : ℂ) * ((sigmaStar : ℂ) + w) * (((sigmaStar : ℂ) + w) ^ 2 - 1)))) w := by
    have ht : Tendsto (fun w : ℂ => (sigmaStar : ℂ) + w) (𝓝 0) (𝓝 (sigmaStar : ℂ)) := by
      simpa using (tendsto_const_nhds (x := (sigmaStar : ℂ))).add
        (tendsto_id : Tendsto id (𝓝 (0 : ℂ)) (𝓝 0))
    filter_upwards [ht.eventually hasDerivAt_slitBoundaryMapC_near_sigmaStar] with w hw
    have hcomp := hw.comp w ((hasDerivAt_id w).const_add (sigmaStar : ℂ))
    refine (hcomp.sub_const (xiStar : ℂ)).congr_deriv ?_
    simp only [mul_one, add_sub_cancel_left]; ring
  let g₁ : ℂ → ℂ := dslope B₀ 0
  let g₂ : ℂ → ℂ := dslope g₁ 0
  have hg₁_an : AnalyticAt ℂ g₁ 0 := by
    obtain ⟨ρ, hρ, hB_ball⟩ := Metric.mem_nhds_iff.mp hB₀_an.eventually_analyticAt
    have hB_on : AnalyticOnNhd ℂ B₀ (ball 0 ρ) := fun z hz => hB_ball hz
    have hd_on : DifferentiableOn ℂ g₁ (ball 0 ρ) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hρ))).2
        hB_on.differentiableOn
    exact (hd_on.analyticOnNhd isOpen_ball) 0 (mem_ball_self hρ)
  have hg₂_an : AnalyticAt ℂ g₂ 0 := by
    obtain ⟨ρ, hρ, hg₁_ball⟩ := Metric.mem_nhds_iff.mp hg₁_an.eventually_analyticAt
    have hg₁_on : AnalyticOnNhd ℂ g₁ (ball 0 ρ) := fun z hz => hg₁_ball hz
    have hd_on : DifferentiableOn ℂ g₂ (ball 0 ρ) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hρ))).2
        hg₁_on.differentiableOn
    exact (hd_on.analyticOnNhd isOpen_ball) 0 (mem_ball_self hρ)
  have hB₀_deriv0 : deriv B₀ 0 = 0 := by
    have h := hB₀_deriv_nhds.self_of_nhds
    rw [h.deriv]; simp
  have hg₁_0 : g₁ 0 = 0 := by dsimp [g₁]; rw [dslope_same, hB₀_deriv0]
  have hB₀_eq_g₂ : ∀ w : ℂ, B₀ w = w ^ 2 * g₂ w := fun w => by
    have h1 := (sub_smul_dslope B₀ 0 w).symm
    have h2 := (sub_smul_dslope g₁ 0 w).symm
    rw [hB₀_0, sub_zero, sub_zero, smul_eq_mul] at h1
    rw [hg₁_0, sub_zero, sub_zero, smul_eq_mul] at h2
    change B₀ w = w * g₁ w at h1
    change g₁ w = w * g₂ w at h2
    rw [h1, h2]; ring
  let r_rat : ℂ → ℂ := fun w =>
    -(((sigmaStar : ℂ) + w - (sigmaPlus : ℂ)) /
      (2 * (π : ℂ) * ((sigmaStar : ℂ) + w) * (((sigmaStar : ℂ) + w) ^ 2 - 1)))
  have hσ2_real : sigmaStar ^ 2 - 1 ≠ 0 := by
    have := sigmaStar_gt_neg_half; have := sigmaStar_neg; nlinarith
  have hσ2_c : (sigmaStar : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr hσ2_real
  have hr_rat_0 : r_rat 0 = 2 * (slitQ : ℂ) := by
    dsimp [r_rat]; unfold slitQ sigmaPlus
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hσ0 : (sigmaStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr sigmaStar_neg.ne
    push_cast; field_simp [hpi, hσ0, hσ2_c]
    unfold sigmaStar; push_cast; ring
  have hg₂_0 : g₂ 0 = (slitQ : ℂ) := by
    have h_eq : ∀ᶠ w in 𝓝[≠] (0 : ℂ), r_rat w = 2 * g₂ w + w * deriv g₂ w := by
      have hg₂_diff : ∀ᶠ w in 𝓝 (0 : ℂ), HasDerivAt g₂ (deriv g₂ w) w := by
        obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hg₂_an.eventually_analyticAt
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with w hw
        exact ((hball hw).differentiableAt).hasDerivAt
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hB₀_deriv_nhds.and hg₂_diff),
        self_mem_nhdsWithin] with w ⟨hB_w, hg₂_w⟩ hw0
      have hB_w' : HasDerivAt B₀ (w * (2 * g₂ w + w * deriv g₂ w)) w := by
        have hmul : HasDerivAt (fun z : ℂ => z ^ 2 * g₂ z) (w * (2 * g₂ w + w * deriv g₂ w)) w :=
          ((hasDerivAt_pow 2 w).mul hg₂_w).congr_deriv (by simp; ring)
        exact hmul.congr_of_eventuallyEq (Eventually.of_forall fun z => hB₀_eq_g₂ z)
      have hderiv_eq := hB_w.unique hB_w'
      have h_alg : w * r_rat w = w * (2 * g₂ w + w * deriv g₂ w) := by
        convert hderiv_eq using 1; dsimp [r_rat]; ring
      exact mul_left_cancel₀ hw0 h_alg
    have hr_cont : ContinuousAt r_rat 0 := by
      dsimp [r_rat]
      refine ((continuousAt_const.add continuousAt_id).sub continuousAt_const).div
        ((continuousAt_const.mul (continuousAt_const.add continuousAt_id)).mul
          (((continuousAt_const.add continuousAt_id).pow 2).sub continuousAt_const)) ?_ |>.neg
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have hσ0 : (sigmaStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr sigmaStar_neg.ne
      simp [hpi, hσ0, hσ2_c]
    have hg₂_cont : ContinuousAt (fun w => 2 * g₂ w + w * deriv g₂ w) 0 := by
      have hdg₂_an : AnalyticAt ℂ (deriv g₂) 0 := hg₂_an.deriv
      exact (continuousAt_const.mul hg₂_an.continuousAt).add
        (continuousAt_id.mul hdg₂_an.continuousAt)
    have hlim : r_rat 0 = (fun w => 2 * g₂ w + w * deriv g₂ w) 0 :=
      tendsto_nhds_unique (hr_cont.tendsto.mono_left nhdsWithin_le_nhds)
        ((hg₂_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' (h_eq.mono fun _ h => h.symm))
    simp only [zero_mul, add_zero, hr_rat_0] at hlim
    linear_combination -hlim / 2
  let h : ℂ → ℂ := fun w => w * (g₂ w / (slitQ : ℂ)) ^ (1 / 2 : ℂ)
  have hh_an : AnalyticAt ℂ h 0 := by
    have hq0 : (slitQ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr slitQ_pos.ne'
    have hmem : g₂ 0 / (slitQ : ℂ) ∈ Complex.slitPlane := by
      rw [hg₂_0, div_self hq0, Complex.mem_slitPlane_iff]; left; simp
    exact analyticAt_id.mul ((hg₂_an.div analyticAt_const hq0).cpow analyticAt_const hmem)
  have hh_0 : h 0 = 0 := by simp [h]
  have hh_deriv : HasDerivAt h 1 0 := by
    have hq0 : (slitQ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr slitQ_pos.ne'
    have h1 : HasDerivAt (fun w : ℂ => (g₂ w / (slitQ : ℂ)) ^ (1 / 2 : ℂ))
        ((1 / 2 : ℂ) * (g₂ 0 / (slitQ : ℂ)) ^ ((1 / 2 : ℂ) - 1) * (deriv g₂ 0 / (slitQ : ℂ))) 0 := by
      have hmem : g₂ 0 / (slitQ : ℂ) ∈ Complex.slitPlane := by
        rw [hg₂_0, div_self hq0, Complex.mem_slitPlane_iff]; left; simp
      exact (hg₂_an.differentiableAt.hasDerivAt.div_const _).cpow_const hmem
    have h2 := (hasDerivAt_id (0 : ℂ)).mul h1
    refine h2.congr_deriv ?_
    simp [hg₂_0, div_self hq0]
  have hh_deriv_ne : deriv h 0 ≠ 0 := by rw [hh_deriv.deriv]; exact one_ne_zero
  let φ : ℂ → ℂ := hh_an.hasStrictDerivAt.localInverse h (deriv h 0) 0 hh_deriv_ne
  have hφ_an : AnalyticAt ℂ φ 0 := by
    simpa [φ, hh_0] using hh_an.analyticAt_localInverse hh_deriv_ne
  have hφ_0 : φ 0 = 0 := by
    have h0 := (hh_an.hasStrictDerivAt.hasStrictFDerivAt_equiv hh_deriv_ne).localInverse_apply_image
    simpa [φ, hh_0] using h0
  have hφ_deriv : deriv φ 0 = 1 := by
    have ht := hh_an.hasStrictDerivAt.to_localInverse hh_deriv_ne
    simpa [φ, hh_0, hh_deriv.deriv] using ht.hasDerivAt.deriv
  have hφ_inv : ∀ᶠ u in 𝓝 (0 : ℂ), h (φ u) = u := by
    simpa [φ, hh_0] using hh_an.hasStrictDerivAt.eventually_right_inverse hh_deriv_ne
  have hh_real : ∀ᶠ x : ℝ in 𝓝 0, (h (x : ℂ)).im = 0 := by
    have hσ_open : Ioo (-1 : ℝ) 0 ∈ 𝓝 (sigmaStar + 0) := by
      rw [add_zero]
      exact isOpen_Ioo.mem_nhds ⟨by linarith [sigmaStar_gt_neg_half], sigmaStar_neg⟩
    have hx_nhds : ∀ᶠ x : ℝ in 𝓝 0, sigmaStar + x ∈ Ioo (-1 : ℝ) 0 := by
      have ht : ContinuousAt (fun x : ℝ => sigmaStar + x) 0 :=
        continuousAt_const.add (continuousAt_id (X := ℝ))
      exact ht.eventually hσ_open
    have hg₂_nhds : ∀ᶠ x : ℝ in 𝓝 0, 0 < (g₂ (x : ℂ)).re ∧ (g₂ (x : ℂ)).im = 0 := by
      have hg₂_re_pos : ∀ᶠ x : ℝ in 𝓝 0, 0 < (g₂ (x : ℂ)).re := by
        have hg₂_c : ContinuousAt g₂ ((0 : ℝ) : ℂ) := by simpa using hg₂_an.continuousAt
        have hcont : ContinuousAt (fun x : ℝ => (g₂ (x : ℂ)).re) 0 :=
          Complex.continuous_re.continuousAt.comp
            (hg₂_c.comp (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))))
        exact hcont.eventually (Ioi_mem_nhds (by simp [hg₂_0, slitQ_pos]))
      filter_upwards [hx_nhds, hg₂_re_pos] with x hx hre
      refine ⟨hre, ?_⟩
      by_cases hx0 : x = 0
      · subst hx0; simp [hg₂_0]
      · have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
        have hB_im : (B₀ (x : ℂ)).im = 0 := by
          dsimp [B₀]
          rw [show (sigmaStar : ℂ) + (x : ℂ) = ((sigmaStar + x : ℝ) : ℂ) by push_cast; rfl,
            slitBoundaryMapC_ofReal_Ioo hx]
          simp
        have hB_eq := hB₀_eq_g₂ (x : ℂ)
        have hx2_pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
        have hx2_c : ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        have hg_eq : g₂ (x : ℂ) = B₀ (x : ℂ) / ((x ^ 2 : ℝ) : ℂ) := by
          rw [hB_eq, hx2_c]; field_simp [Complex.ofReal_ne_zero.mpr hx2_pos.ne']
        rw [hg_eq, Complex.div_ofReal_im, hB_im, zero_div]
    filter_upwards [hg₂_nhds] with x ⟨hre, him⟩
    have hq_pos : 0 < slitQ := slitQ_pos
    have hrat_pos : 0 < (g₂ (x : ℂ)).re / slitQ := div_pos hre hq_pos
    have hrat_eq : g₂ (x : ℂ) / (slitQ : ℂ) = (((g₂ (x : ℂ)).re / slitQ : ℝ) : ℂ) := by
      have hg_eq : g₂ (x : ℂ) = ((g₂ (x : ℂ)).re : ℂ) := Complex.ext rfl him
      rw [hg_eq]; push_cast; rfl
    dsimp [h]
    rw [hrat_eq, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hrat_pos.le, ← Complex.ofReal_mul, Complex.ofReal_im]
  have hφ_real : ∀ᶠ x : ℝ in 𝓝 0, (φ (x : ℂ)).im = 0 := by
    let hℝ : ℝ → ℝ := fun x => (h (x : ℂ)).re
    have hh_strict : HasStrictDerivAt h 1 0 := hh_deriv.deriv ▸ hh_an.hasStrictDerivAt
    have hhℝ_deriv : HasStrictDerivAt hℝ 1 0 := by
      have h0 : HasStrictFDerivAt h (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (1 : ℂ))) (Complex.ofRealCLM (0 : ℝ)) := by
        simpa using hh_strict.hasStrictFDerivAt.restrictScalars ℝ
      have hcomp := Complex.reCLM.hasStrictFDerivAt.comp (0 : ℝ)
        (h0.comp (0 : ℝ) Complex.ofRealCLM.hasStrictFDerivAt)
      refine (hasStrictDerivAt_iff_hasStrictFDerivAt).mpr ?_
      exact hcomp.congr_fderiv (ContinuousLinearMap.ext fun x => by
        simp [ContinuousLinearMap.toSpanSingleton_apply])
    let φℝ : ℝ → ℝ := hhℝ_deriv.localInverse hℝ 1 0 one_ne_zero
    have hhℝ_0 : hℝ 0 = 0 := by simp [hℝ, hh_0]
    have hφℝ_inv : ∀ᶠ x in 𝓝 (0 : ℝ), hℝ (φℝ x) = x := by
      simpa [φℝ, hhℝ_0] using hhℝ_deriv.eventually_right_inverse one_ne_zero
    have hφℝ_cont : ContinuousAt φℝ 0 := by
      simpa [φℝ, hhℝ_0] using (hhℝ_deriv.hasStrictFDerivAt_equiv one_ne_zero).localInverse_continuousAt
    have hφℝ_0 : φℝ 0 = 0 := by
      have himg := (hhℝ_deriv.hasStrictFDerivAt_equiv one_ne_zero).localInverse_apply_image
      change φℝ (hℝ 0) = 0 at himg
      rwa [hhℝ_0] at himg
    have h_eq_on : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), φ (x : ℂ) = (φℝ x : ℂ) := by
      have hφ_left : ∀ᶠ w in 𝓝 (0 : ℂ), φ (h w) = w := by
        simpa [φ] using hh_an.hasStrictDerivAt.eventually_left_inverse hh_deriv_ne
      have hφ_left' : ∀ᶠ w in 𝓝 ((φℝ 0 : ℝ) : ℂ), φ (h w) = w := by
        rwa [hφℝ_0, Complex.ofReal_zero]
      have hc : ContinuousAt (fun x : ℝ => (φℝ x : ℂ)) 0 :=
        (Complex.continuous_ofReal.continuousAt (x := φℝ 0)).comp hφℝ_cont
      have h1 : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), φ (h (φℝ x : ℂ)) = (φℝ x : ℂ) := hc.eventually hφ_left'
      have h2 : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), (h (φℝ x : ℂ)).im = 0 :=
        hφℝ_cont.eventually (by simpa [hφℝ_0] using hh_real)
      filter_upwards [h1, h2, hφℝ_inv] with x hx1 hx2 hx3
      have h_eq : h (φℝ x : ℂ) = (x : ℂ) := Complex.ext (by simpa [hℝ] using hx3) hx2
      rwa [h_eq] at hx1
    filter_upwards [h_eq_on] with x hx
    rw [hx, Complex.ofReal_im]
  let tipPsi : ℂ → ℂ := fun v => φ (v / (√slitQ : ℂ))
  have hsq_pos : 0 < √slitQ := Real.sqrt_pos.mpr slitQ_pos
  have hsq_c : (√slitQ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq_pos.ne'
  have hψ_an : AnalyticAt ℂ tipPsi 0 := by
    have hdiv : AnalyticAt ℂ (fun v : ℂ => v / (√slitQ : ℂ)) 0 :=
      (analyticAt_id (𝕜 := ℂ)).div analyticAt_const hsq_c
    have hφ0 : AnalyticAt ℂ φ ((fun v : ℂ => v / (√slitQ : ℂ)) 0) := by
      dsimp only; rw [zero_div]; exact hφ_an
    exact AnalyticAt.comp (f := fun v : ℂ => v / (√slitQ : ℂ)) (g := φ) hφ0 hdiv
  have hψ_0 : tipPsi 0 = 0 := by simp [tipPsi, hφ_0]
  have hψ_deriv : deriv tipPsi 0 = (1 / √slitQ : ℂ) := by
    have h1 : HasDerivAt φ 1 0 := by rw [← hφ_deriv]; exact hφ_an.differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun v : ℂ => v / (√slitQ : ℂ)) (1 / (√slitQ : ℂ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).div_const (√slitQ : ℂ)
    have h1' : HasDerivAt φ 1 ((0 : ℂ) / (√slitQ : ℂ)) := by simpa using h1
    have h3 := (h1'.comp (0 : ℂ) h2).deriv
    simpa [tipPsi, Function.comp_def, one_div] using h3
  have hψ_eq_B : ∀ᶠ v in 𝓝 (0 : ℂ), B₀ (tipPsi v) = v ^ 2 := by
    have ht : Tendsto (fun v : ℂ => v / (√slitQ : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa [zero_div] using (tendsto_id (α := ℂ) (x := 𝓝 (0 : ℂ))).div_const (√slitQ : ℂ)
    filter_upwards [ht.eventually hφ_inv] with v hv
    have h1 : h (tipPsi v) = v / (√slitQ : ℂ) := hv
    have h2 : (h (tipPsi v)) ^ 2 = (v / (√slitQ : ℂ)) ^ 2 := congrArg (· ^ 2) h1
    have hh_sq : ∀ w : ℂ, (h w) ^ 2 = w ^ 2 * ((g₂ w / (slitQ : ℂ)) ^ (1 / 2 : ℂ)) ^ 2 := fun w => by
      dsimp [h]; ring
    have hq0 : (slitQ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr slitQ_pos.ne'
    have hB : B₀ (tipPsi v) = (slitQ : ℂ) * (h (tipPsi v)) ^ 2 := by
      rw [hh_sq, cpow_half_sq, hB₀_eq_g₂]
      field_simp [hq0]
    rw [hB, h2, div_pow, show ((√slitQ : ℂ)) ^ 2 = (slitQ : ℂ) by
      exact_mod_cast Real.sq_sqrt slitQ_pos.le]
    field_simp [hq0]
  have hψ_real : ∀ᶠ v : ℝ in 𝓝 0, (tipPsi (v : ℂ)).im = 0 := by
    have ht : Tendsto (fun v : ℝ => v / √slitQ) (𝓝 0) (𝓝 0) := by
      simpa [zero_div] using (tendsto_id (α := ℝ) (x := 𝓝 (0 : ℝ))).div_const (√slitQ)
    filter_upwards [ht.eventually hφ_real] with v hv
    simpa [tipPsi] using hv
  obtain ⟨r₁, hr₁, hψ_ball⟩ := Metric.mem_nhds_iff.mp hψ_an.eventually_analyticAt
  obtain ⟨r₂, hr₂, hB_ball⟩ := Metric.mem_nhds_iff.mp hψ_eq_B
  obtain ⟨r₃, hr₃, hr_ball⟩ := Metric.mem_nhds_iff.mp hψ_real
  refine ⟨min r₁ (min r₂ r₃), tipPsi, lt_min hr₁ (lt_min hr₂ hr₃), ?_, hψ_0, hψ_deriv, ?_, ?_⟩
  · exact (fun z hz => hψ_ball (ball_subset_ball (min_le_left _ _) hz))
  · intro v hv
    exact hr_ball (by simpa [Real.dist_eq] using lt_of_lt_of_le hv ((min_le_right _ _).trans (min_le_right _ _)))
  · intro v hv
    have hv2 : v ∈ ball (0 : ℂ) r₂ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hv
    have hBv := hB_ball hv2
    dsimp [B₀] at hBv
    linear_combination hBv

/-- **Lemma T1** (`blowup_limit.tex`, Lemma `bl:T1`): tip map and its local asymptotics.
Proved completely from the explicit slit-strip boundary map `slitBoundaryMapC` and
analytic local inversion (no unproved hypotheses). -/
theorem lemma_T1 :
    ∃ (ρ₁ C_T1 : ℝ) (ψ : ℂ → ℂ), 0 < ρ₁ ∧ 0 ≤ C_T1 ∧
      AnalyticOnNhd ℂ ψ (ball 0 (2 * √ρ₁)) ∧
      ψ 0 = 0 ∧ deriv ψ 0 = (1 / √slitQ : ℂ) ∧
      (∀ v : ℝ, |v| < 2 * √ρ₁ → (ψ (v : ℂ)).im = 0) ∧
      ∀ {c' : ℝ} {ζ : ℂ}, 0 < c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
        tipEps c' * ‖ζ‖ ≤ ρ₁ →
        let ε := tipEps c'
        let v := I * ((√ε : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
        let z_b := (sigmaStar : ℂ) + ψ v
        ‖v‖ = √(ε * ‖ζ‖) ∧
        0 < z_b.im ∧
        ‖z_b - (sigmaStar : ℂ)‖ ≤ 0.1 ∧
        slitBoundaryMapC z_b = bScale c' ζ ∧
        (∀ w : ℂ, 0 < w.im → slitBoundaryMapC w = bScale c' ζ → w = z_b) ∧
        |z_b.im - √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re| ≤
          C_T1 * √(ε * ‖ζ‖) * (√(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) ∧
        |‖z_b - (sigmaStar : ℂ)‖ - √(ε * ‖ζ‖ / slitQ)| ≤
          C_T1 * √(ε * ‖ζ‖) * √(ε * ‖ζ‖ / slitQ) ∧
        |z_b.im * ‖z_b - (sigmaStar : ℂ)‖ - (ε / slitQ) * tipDist ζ| ≤
          C_T1 * √(ε * ‖ζ‖) * ((ε / slitQ) * tipDist ζ) := by
  obtain ⟨r_ψ, ψ, hr_ψ, hψ_an, hψ_0, hψ_deriv, hψ_real, hψ_B⟩ := tipPsi_exists
  let r₀ : ℝ := r_ψ / 2
  have hr₀_pos : 0 < r₀ := by positivity
  have hcl_sub : closedBall (0 : ℂ) r₀ ⊆ ball 0 r_ψ :=
    closedBall_subset_ball (by dsimp [r₀]; linarith)
  let R : ℂ → ℂ := dslope (dslope ψ 0) 0
  have hR_an : AnalyticOnNhd ℂ R (ball 0 r_ψ) := by
    have hd1 : DifferentiableOn ℂ (dslope ψ 0) (ball 0 r_ψ) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hr_ψ))).2
        hψ_an.differentiableOn
    have hd2 : DifferentiableOn ℂ R (ball 0 r_ψ) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hr_ψ))).2 hd1
    exact hd2.analyticOnNhd isOpen_ball
  have hψ_rep : ∀ v : ℂ, ψ v = v * (1 / √slitQ : ℂ) + v ^ 2 * R v := fun v => by
    have h1 := sub_smul_dslope ψ 0 v
    have h2 := sub_smul_dslope (dslope ψ 0) 0 v
    rw [hψ_0, sub_zero, sub_zero, smul_eq_mul] at h1
    rw [dslope_same, hψ_deriv, sub_zero, smul_eq_mul] at h2
    have h2' : dslope ψ 0 v = (1 / √slitQ : ℂ) + v * R v := eq_add_of_sub_eq' h2.symm
    rw [h2'] at h1
    linear_combination -h1
  have hR_real : ∀ x : ℝ, |x| < r_ψ → (R (x : ℂ)).im = 0 := fun x hx => by
    by_cases hx0 : x = 0
    · have hseq : Tendsto (fun n : ℕ => r₀ / (n + 2 : ℝ)) atTop (nhds 0) := by
        simpa using tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
      have hcont : ContinuousAt (fun t : ℝ => (R (t : ℂ)).im) 0 := by
        have hR0 : ContinuousAt R ((0 : ℝ) : ℂ) := by
          simpa using (hR_an 0 (mem_ball_self hr_ψ)).continuousAt
        exact Complex.continuous_im.continuousAt.comp (hR0.comp Complex.continuous_ofReal.continuousAt)
      have hval : ∀ n : ℕ, (R (((r₀ / (n + 2 : ℝ) : ℝ) : ℂ))).im = 0 := fun n => by
        have hpos : 0 < r₀ / (n + 2 : ℝ) := div_pos hr₀_pos (by positivity)
        have hlt : |r₀ / (n + 2 : ℝ)| < r_ψ := by
          rw [abs_of_pos hpos]
          have hle : r₀ / (n + 2 : ℝ) ≤ r₀ := div_le_self hr₀_pos.le (by linarith)
          dsimp [r₀] at hle ⊢; linarith
        have hrep := hψ_rep ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ)
        have h_im_ψ : (ψ ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ)).im = 0 := hψ_real _ hlt
        have hc2 : (((r₀ / (n + 2 : ℝ) : ℝ) : ℂ) ^ 2) = (((r₀ / (n + 2 : ℝ)) ^ 2 : ℝ) : ℂ) := by
          push_cast; rfl
        have hne2 : (((r₀ / (n + 2 : ℝ)) ^ 2 : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
        have hR_eq : R ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ) =
            (ψ ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ) -
              ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ) * (1 / √slitQ : ℂ)) /
              (((r₀ / (n + 2 : ℝ)) ^ 2 : ℝ) : ℂ) := by
          calc R ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ)
              = ((((r₀ / (n + 2 : ℝ)) ^ 2 : ℝ) : ℂ) * R ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ)) /
                  (((r₀ / (n + 2 : ℝ)) ^ 2 : ℝ) : ℂ) := (mul_div_cancel_left₀ _ hne2).symm
            _ = (ψ ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ) -
                  ((r₀ / (n + 2 : ℝ) : ℝ) : ℂ) * (1 / √slitQ : ℂ)) /
                  (((r₀ / (n + 2 : ℝ)) ^ 2 : ℝ) : ℂ) := by
                rw [← hc2, hrep]; ring
        have h_im_lin : (((r₀ / (n + 2 : ℝ) : ℝ) : ℂ) * (1 / √slitQ : ℂ)).im = 0 := by
          rw [show (1 / √slitQ : ℂ) = ((1 / √slitQ : ℝ) : ℂ) by push_cast; rfl,
            ← Complex.ofReal_mul, Complex.ofReal_im]
        rw [hR_eq, Complex.div_ofReal_im, Complex.sub_im, h_im_ψ, h_im_lin, sub_self, zero_div]
      subst hx0
      have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
      exact tendsto_nhds_unique (hcont.tendsto.comp hseq)
        (hzero.congr' (Eventually.of_forall fun n => (hval n).symm))
    · have hrep := hψ_rep (x : ℂ)
      have h_im_ψ : (ψ (x : ℂ)).im = 0 := hψ_real x hx
      have hc2 : ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      have hne2 : ((x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hx0)
      have hR_eq : R (x : ℂ) = (ψ (x : ℂ) - (x : ℂ) * (1 / √slitQ : ℂ)) / ((x ^ 2 : ℝ) : ℂ) := by
        calc R (x : ℂ) = (((x ^ 2 : ℝ) : ℂ) * R (x : ℂ)) / ((x ^ 2 : ℝ) : ℂ) :=
              (mul_div_cancel_left₀ _ hne2).symm
          _ = (ψ (x : ℂ) - (x : ℂ) * (1 / √slitQ : ℂ)) / ((x ^ 2 : ℝ) : ℂ) := by
              rw [← hc2, hrep]; ring
      rw [hR_eq, Complex.div_ofReal_im, Complex.sub_im, h_im_ψ]
      simp
  obtain ⟨M_R, hM_R⟩ := (isCompact_closedBall (0 : ℂ) r₀).exists_bound_of_continuousOn
    (hR_an.continuousOn.mono hcl_sub)
  obtain ⟨M_R', hM_R'⟩ := (isCompact_closedBall (0 : ℂ) r₀).exists_bound_of_continuousOn
    (hR_an.deriv.continuousOn.mono hcl_sub)
  let C_R : ℝ := max M_R 0
  let C_R' : ℝ := max M_R' 0
  have hC_R_nn : 0 ≤ C_R := le_max_right _ _
  have hC_R'_nn : 0 ≤ C_R' := le_max_right _ _
  have hR_bd : ∀ v ∈ closedBall (0 : ℂ) r₀, ‖R v‖ ≤ C_R := fun v hv =>
    (hM_R v hv).trans (le_max_left _ _)
  have hR'_bd : ∀ v ∈ closedBall (0 : ℂ) r₀, ‖deriv R v‖ ≤ C_R' := fun v hv =>
    (hM_R' v hv).trans (le_max_left _ _)
  let C_norm : ℝ := √slitQ * C_R
  let C_im : ℝ := √slitQ * (2 * C_R + r₀ * C_R')
  let C_0 : ℝ := max C_norm C_im
  let C_T1 : ℝ := 3 * C_0 + C_0 ^ 2
  let ρ_s : ℝ := min (r₀ / 2) (min (1 / (2 * (C_0 + 1))) (1 / (20 * (1 / √slitQ + r₀ * C_R + 1))))
  let ρ₁ : ℝ := ρ_s ^ 2
  have hρ_s_pos : 0 < ρ_s := by positivity
  have hρ₁_pos : 0 < ρ₁ := by positivity
  have h2sq_le : 2 * √ρ₁ ≤ r_ψ := by
    rw [show √ρ₁ = ρ_s from Real.sqrt_sq hρ_s_pos.le]
    have : ρ_s ≤ r₀ / 2 := min_le_left _ _
    dsimp [r₀] at this ⊢; linarith
  refine ⟨ρ₁, C_T1, ψ, hρ₁_pos, by positivity, hψ_an.mono (ball_subset_ball h2sq_le),
    hψ_0, hψ_deriv, fun v hv => hψ_real v (hv.trans_le h2sq_le), ?_⟩
  intro c' ζ hc' hζ hεζ
  set ε := tipEps c'
  set v := I * ((√ε : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
  set z_b := (sigmaStar : ℂ) + ψ v
  have hε_pos : 0 < ε := tipEps_pos hc'
  have hv_norm : ‖v‖ = √(ε * ‖ζ‖) := by
    dsimp [v]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_cpow_half, norm_neg, Real.sqrt_mul hε_pos.le]
  have hv_le_ρs : ‖v‖ ≤ ρ_s := by
    rw [hv_norm]; exact (Real.sqrt_le_sqrt hεζ).trans_eq (Real.sqrt_sq hρ_s_pos.le)
  have hv_cl : v ∈ closedBall (0 : ℂ) r₀ := by
    rw [mem_closedBall, dist_zero_right]
    exact hv_le_ρs.trans ((min_le_left _ _).trans (by linarith))
  have hv_ball : v ∈ ball (0 : ℂ) r_ψ := hcl_sub hv_cl
  have hv_sq : v ^ 2 = ((ε : ℝ) : ℂ) * ζ := by
    dsimp [v]
    rw [mul_pow, mul_pow, I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hε_pos.le,
      cpow_half_sq]
    ring
  have hv_im : v.im = √ε * ((-ζ) ^ (1 / 2 : ℂ)).re := by
    dsimp [v]
    have h1 : I * ((√ε : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ) =
        (((√ε : ℝ) : ℂ) * ((-ζ) ^ (1 / 2 : ℂ))) * I := by ring
    rw [h1, Complex.mul_I_im, Complex.re_ofReal_mul]
  have hsqrt_re_pos : 0 < ((-ζ) ^ (1 / 2 : ℂ)).re := by
    have h1 : 0 < tipDist ζ := tipDist_pos_of_not_nonneg hζ
    unfold tipDist at h1
    rcases mul_pos_iff.mp h1 with ⟨_, h⟩ | ⟨ha, _⟩
    · exact h
    · linarith [Real.sqrt_nonneg ‖ζ‖]
  have hv_im_pos : 0 < v.im := by rw [hv_im]; exact mul_pos (Real.sqrt_pos.mpr hε_pos) hsqrt_re_pos
  have hv_im_err : |((v ^ 2 * R v)).im| ≤ (2 * C_R + r₀ * C_R') * ‖v‖ * |v.im| := by
    have hre_cl : (v.re : ℂ) ∈ closedBall (0 : ℂ) r₀ := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm v).trans (mem_closedBall.mp hv_cl |> fun h => by simpa [dist_zero_right] using h)
    have hR_im : |(R v).im| ≤ C_R' * |v.im| := by
      have h_im_0 : (R (v.re : ℂ)).im = 0 := hR_real v.re (by
        have := mem_ball.mp (hcl_sub hre_cl)
        simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using this)
      have hdiff : ∀ w ∈ ball (0 : ℂ) r_ψ, DifferentiableAt ℂ R w := fun w hw =>
        (hR_an w hw).differentiableAt
      have hmvt : ‖R v - R (v.re : ℂ)‖ ≤ C_R' * ‖v - (v.re : ℂ)‖ := by
        refine (convex_closedBall (0 : ℂ) r₀).norm_image_sub_le_of_norm_deriv_le
          (fun w hw => hdiff w (hcl_sub hw)) hR'_bd hre_cl hv_cl
      have hvsub : ‖v - (v.re : ℂ)‖ = |v.im| := by
        have : v - (v.re : ℂ) = (v.im : ℂ) * I := by apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      calc |(R v).im| = |(R v - R (v.re : ℂ)).im| := by rw [Complex.sub_im, h_im_0, sub_zero]
        _ ≤ ‖R v - R (v.re : ℂ)‖ := Complex.abs_im_le_norm _
        _ ≤ C_R' * ‖v - (v.re : ℂ)‖ := hmvt
        _ = C_R' * |v.im| := by rw [hvsub]
    have hv2_im : |(v ^ 2).im| ≤ 2 * ‖v‖ * |v.im| := by
      rw [sq, Complex.mul_im, show v.re * v.im + v.im * v.re = 2 * v.re * v.im by ring,
        abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr; exact Complex.abs_re_le_norm v
    have hv2_re : |(v ^ 2).re| ≤ ‖v‖ ^ 2 := by
      calc |(v ^ 2).re| ≤ ‖v ^ 2‖ := Complex.abs_re_le_norm _
        _ = ‖v‖ ^ 2 := norm_pow v 2
    rw [Complex.mul_im]
    calc |(v ^ 2).re * (R v).im + (v ^ 2).im * (R v).re|
        ≤ |(v ^ 2).re * (R v).im| + |(v ^ 2).im * (R v).re| := abs_add_le _ _
      _ = |(v ^ 2).re| * |(R v).im| + |(v ^ 2).im| * |(R v).re| := by rw [abs_mul, abs_mul]
      _ ≤ ‖v‖ ^ 2 * (C_R' * |v.im|) + (2 * ‖v‖ * |v.im|) * C_R := by
          gcongr
          exact (Complex.abs_re_le_norm _).trans (hR_bd v hv_cl)
      _ = (2 * C_R + ‖v‖ * C_R') * ‖v‖ * |v.im| := by ring
      _ ≤ (2 * C_R + r₀ * C_R') * ‖v‖ * |v.im| := by
          have hv_r0 : ‖v‖ ≤ r₀ := by simpa [mem_closedBall, dist_zero_right] using hv_cl
          gcongr
  have hz_im_eq : z_b.im = (ψ v).im := by dsimp [z_b]; simp
  have hlin_im : (v * (1 / √slitQ : ℂ)).im = √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re := by
    rw [show (1 / √slitQ : ℂ) = ((1 / √slitQ : ℝ) : ℂ) by push_cast; rfl,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      hv_im, Real.sqrt_div hε_pos.le]
    ring
  have him_eq : z_b.im - √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re = (v ^ 2 * R v).im := by
    rw [hz_im_eq, hψ_rep v, Complex.add_im, hlin_im]; ring
  have hC0_nn : 0 ≤ C_0 := le_trans (by positivity) (le_max_left C_norm C_im)
  have hC_im_bound : |(v ^ 2 * R v).im| ≤
      C_im * √(ε * ‖ζ‖) * (√(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by
    rw [← hv_norm]
    calc |(v ^ 2 * R v).im| ≤ (2 * C_R + r₀ * C_R') * ‖v‖ * |v.im| := hv_im_err
      _ = C_im * ‖v‖ * (√(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by
          rw [abs_of_pos hv_im_pos, hv_im, Real.sqrt_div hε_pos.le]; dsimp [C_im]
          field_simp [(Real.sqrt_pos.mpr slitQ_pos).ne']
  have hz_im_err : |z_b.im - √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re| ≤
      C_T1 * √(ε * ‖ζ‖) * (√(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by
    rw [him_eq]
    refine hC_im_bound.trans ?_
    have : C_im ≤ C_0 := le_max_right _ _
    have hCT1_ge : C_im ≤ C_T1 := by dsimp [C_T1]; nlinarith [sq_nonneg C_0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCT1_ge (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) hsqrt_re_pos.le)
  have hC0_v_half : C_0 * √(ε * ‖ζ‖) ≤ 1 / 2 := by
    have hρ_le : ρ_s ≤ 1 / (2 * (C_0 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    calc C_0 * √(ε * ‖ζ‖) = C_0 * ‖v‖ := by rw [hv_norm]
      _ ≤ C_0 * ρ_s := mul_le_mul_of_nonneg_left hv_le_ρs hC0_nn
      _ ≤ C_0 * (1 / (2 * (C_0 + 1))) := mul_le_mul_of_nonneg_left hρ_le hC0_nn
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
          linarith
  have hz_im_pos : 0 < z_b.im := by
    have hmain_pos : 0 < √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re :=
      mul_pos (Real.sqrt_pos.mpr (div_pos hε_pos slitQ_pos)) hsqrt_re_pos
    have herr_half : |(v ^ 2 * R v).im| ≤ (1 / 2 : ℝ) * (√(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) :=
      hC_im_bound.trans (mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right (le_max_right C_norm C_im) (Real.sqrt_nonneg _)).trans hC0_v_half)
        hmain_pos.le)
    have hlo := (abs_le.mp herr_half).1
    linarith [him_eq]
  have hz_norm_bound : |‖z_b - (sigmaStar : ℂ)‖ - √(ε * ‖ζ‖ / slitQ)| ≤
      C_norm * √(ε * ‖ζ‖) * √(ε * ‖ζ‖ / slitQ) := by
    have hsub : z_b - (sigmaStar : ℂ) = ψ v := by dsimp [z_b]; ring
    rw [hsub, hψ_rep v]
    have htri : |‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖ - ‖v * (1 / √slitQ : ℂ)‖| ≤ ‖v ^ 2 * R v‖ := by
      rw [abs_sub_le_iff]; constructor
      · calc ‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖ - ‖v * (1 / √slitQ : ℂ)‖
            ≤ (‖v * (1 / √slitQ : ℂ)‖ + ‖v ^ 2 * R v‖) - ‖v * (1 / √slitQ : ℂ)‖ :=
              sub_le_sub_right (norm_add_le _ _) _
          _ = ‖v ^ 2 * R v‖ := by ring
      · calc ‖v * (1 / √slitQ : ℂ)‖ - ‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖
            ≤ ‖(v * (1 / √slitQ : ℂ) + v ^ 2 * R v) - v ^ 2 * R v‖ -
                ‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖ := by simp
          _ ≤ (‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖ + ‖v ^ 2 * R v‖) -
                ‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖ := by
              gcongr; exact norm_sub_le _ _
          _ = ‖v ^ 2 * R v‖ := by ring
    have hmain_norm : ‖v * (1 / √slitQ : ℂ)‖ = √(ε * ‖ζ‖ / slitQ) := by
      rw [show (1 / √slitQ : ℂ) = ((1 / √slitQ : ℝ) : ℂ) by push_cast; rfl,
        norm_mul, hv_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr slitQ_pos)),
        Real.sqrt_div (mul_nonneg hε_pos.le (norm_nonneg _)), one_div, div_eq_mul_inv]
    rw [hmain_norm] at htri
    refine htri.trans ?_
    rw [norm_mul, norm_pow]
    have hsqq : √slitQ ≠ 0 := (Real.sqrt_pos.mpr slitQ_pos).ne'
    calc ‖v‖ ^ 2 * ‖R v‖ ≤ ‖v‖ ^ 2 * C_R := by gcongr; exact hR_bd v hv_cl
      _ = C_norm * ‖v‖ * (‖v‖ / √slitQ) := by dsimp [C_norm]; field_simp [hsqq]
      _ = C_norm * √(ε * ‖ζ‖) * √(ε * ‖ζ‖ / slitQ) := by
          rw [hv_norm, Real.sqrt_div (mul_nonneg hε_pos.le (norm_nonneg _))]
  have hz_norm_err : |‖z_b - (sigmaStar : ℂ)‖ - √(ε * ‖ζ‖ / slitQ)| ≤
      C_T1 * √(ε * ‖ζ‖) * √(ε * ‖ζ‖ / slitQ) := by
    refine hz_norm_bound.trans ?_
    have : C_norm ≤ C_0 := le_max_left _ _
    have hCT1_ge : C_norm ≤ C_T1 := by dsimp [C_T1]; nlinarith [sq_nonneg C_0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCT1_ge (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hz_small : ‖z_b - (sigmaStar : ℂ)‖ ≤ 0.1 := by
    have hsub : z_b - (sigmaStar : ℂ) = ψ v := by dsimp [z_b]; ring
    rw [hsub, hψ_rep v]
    have h1 : ‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖ ≤ ‖v‖ * (1 / √slitQ + r₀ * C_R) := by
      calc ‖v * (1 / √slitQ : ℂ) + v ^ 2 * R v‖
          ≤ ‖v * (1 / √slitQ : ℂ)‖ + ‖v ^ 2 * R v‖ := norm_add_le _ _
        _ = ‖v‖ * (1 / √slitQ) + ‖v‖ * (‖v‖ * ‖R v‖) := by
            rw [show (1 / √slitQ : ℂ) = ((1 / √slitQ : ℝ) : ℂ) by push_cast; rfl,
              norm_mul v _, norm_mul (v ^ 2) (R v), norm_pow v 2, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr slitQ_pos))]; ring
        _ ≤ ‖v‖ * (1 / √slitQ) + ‖v‖ * (r₀ * C_R) := by
            gcongr
            · simpa [mem_closedBall, dist_zero_right] using hv_cl
            · exact hR_bd v hv_cl
        _ = ‖v‖ * (1 / √slitQ + r₀ * C_R) := by ring
    refine h1.trans ?_
    have h2 : ρ_s ≤ 1 / (20 * (1 / √slitQ + r₀ * C_R + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h3 : ‖v‖ ≤ 1 / (20 * (1 / √slitQ + r₀ * C_R + 1)) := hv_le_ρs.trans h2
    have hden_pos : 0 < 1 / √slitQ + r₀ * C_R + 1 := by positivity
    calc ‖v‖ * (1 / √slitQ + r₀ * C_R)
        ≤ (1 / (20 * (1 / √slitQ + r₀ * C_R + 1))) * (1 / √slitQ + r₀ * C_R) := by gcongr
      _ ≤ (1 / (20 * (1 / √slitQ + r₀ * C_R + 1))) * (1 / √slitQ + r₀ * C_R + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1 / 20 := by field_simp [hden_pos.ne']
      _ ≤ 0.1 := by norm_num
  have hz_b_eq : slitBoundaryMapC z_b = bScale c' ζ := by
    dsimp [z_b]; unfold bScale; rw [hψ_B v hv_ball, hv_sq]
  have hz_uniq : ∀ w : ℂ, 0 < w.im → slitBoundaryMapC w = bScale c' ζ → w = z_b := fun w hw hweq =>
    slitBoundaryMapC_injOn_UHP hw hz_im_pos (hweq.trans hz_b_eq.symm)
  have hz_prod_err : |z_b.im * ‖z_b - (sigmaStar : ℂ)‖ - (ε / slitQ) * tipDist ζ| ≤
      C_T1 * √(ε * ‖ζ‖) * ((ε / slitQ) * tipDist ζ) := by
    set a₀ := √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re
    set b₀ := √(ε * ‖ζ‖ / slitQ)
    have ha₀_nn : 0 ≤ a₀ := mul_nonneg (Real.sqrt_nonneg _) hsqrt_re_pos.le
    have hb₀_nn : 0 ≤ b₀ := Real.sqrt_nonneg _
    have hprod0 : a₀ * b₀ = (ε / slitQ) * tipDist ζ := by
      dsimp [a₀, b₀]; unfold tipDist
      rw [Real.sqrt_div hε_pos.le, Real.sqrt_div (mul_nonneg hε_pos.le (norm_nonneg _)),
        Real.sqrt_mul hε_pos.le]
      have hq_ne : √slitQ ≠ 0 := (Real.sqrt_pos.mpr slitQ_pos).ne'
      have hsqε : √ε ^ 2 = ε := Real.sq_sqrt hε_pos.le
      have hsqq : √slitQ ^ 2 = slitQ := Real.sq_sqrt slitQ_pos.le
      field_simp [hq_ne, slitQ_pos.ne']
      rw [hsqε, hsqq]
      ring
    have ha_bd : |z_b.im - a₀| ≤ C_0 * √(ε * ‖ζ‖) * a₀ := by
      rw [him_eq]
      exact hC_im_bound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C_norm C_im) (Real.sqrt_nonneg _)) ha₀_nn)
    have hb_bd : |‖z_b - (sigmaStar : ℂ)‖ - b₀| ≤ C_0 * √(ε * ‖ζ‖) * b₀ :=
      hz_norm_bound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C_norm C_im) (Real.sqrt_nonneg _)) hb₀_nn)
    have hb_le : ‖z_b - (sigmaStar : ℂ)‖ ≤ (1 + C_0 * √(ε * ‖ζ‖)) * b₀ := by
      have := (abs_le.mp hb_bd).2; linarith
    have hsq1 : √(ε * ‖ζ‖) ≤ 1 := by
      rw [← hv_norm]
      have h2 : ρ_s ≤ 1 / (20 * (1 / √slitQ + r₀ * C_R + 1)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have h1_ge : (1 : ℝ) ≤ 20 * (1 / √slitQ + r₀ * C_R + 1) := by
        have : 0 ≤ 1 / √slitQ := by positivity
        have : 0 ≤ r₀ * C_R := by positivity
        linarith
      have h20 : 1 / (20 * (1 / √slitQ + r₀ * C_R + 1)) ≤ 1 :=
        div_le_one_of_le₀ h1_ge (by positivity)
      exact hv_le_ρs.trans (h2.trans h20)
    have hCT_ge : 2 * C_0 + C_0 ^ 2 * √(ε * ‖ζ‖) ≤ C_T1 := by
      have h1 : C_0 ^ 2 * √(ε * ‖ζ‖) ≤ C_0 ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hsq1 (sq_nonneg _)
      dsimp [C_T1]; linarith
    rw [← hprod0]
    calc |z_b.im * ‖z_b - (sigmaStar : ℂ)‖ - a₀ * b₀|
        = |(z_b.im - a₀) * ‖z_b - (sigmaStar : ℂ)‖ + a₀ * (‖z_b - (sigmaStar : ℂ)‖ - b₀)| := by
          congr 1; ring
      _ ≤ |(z_b.im - a₀) * ‖z_b - (sigmaStar : ℂ)‖| + |a₀ * (‖z_b - (sigmaStar : ℂ)‖ - b₀)| :=
          abs_add_le _ _
      _ = |z_b.im - a₀| * ‖z_b - (sigmaStar : ℂ)‖ + a₀ * |‖z_b - (sigmaStar : ℂ)‖ - b₀| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg ha₀_nn]
      _ ≤ (C_0 * √(ε * ‖ζ‖) * a₀) * ((1 + C_0 * √(ε * ‖ζ‖)) * b₀) +
            a₀ * (C_0 * √(ε * ‖ζ‖) * b₀) :=
          add_le_add (mul_le_mul ha_bd hb_le (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left hb_bd ha₀_nn)
      _ = (2 * C_0 + C_0 ^ 2 * √(ε * ‖ζ‖)) * √(ε * ‖ζ‖) * (a₀ * b₀) := by ring
      _ ≤ C_T1 * √(ε * ‖ζ‖) * (a₀ * b₀) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCT_ge (Real.sqrt_nonneg _)) (mul_nonneg ha₀_nn hb₀_nn)
  exact ⟨hv_norm, hz_im_pos, hz_small, hz_b_eq, hz_uniq, hz_im_err, hz_norm_err, hz_prod_err⟩

/-! ### Axiom checks for headline theorems -/
/-- info: 'FormalResearch.ModularBootstrap.tipH_eq_airyEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.tipH_eq_airyEnv

/-- info: 'FormalResearch.ModularBootstrap.tipH_disc_oscillation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.tipH_disc_oscillation

/-- info: 'FormalResearch.ModularBootstrap.disc_avg_neg_log_tipDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.disc_avg_neg_log_tipDist

/-- info: 'FormalResearch.ModularBootstrap.subharmonic_disc_avg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.subharmonic_disc_avg_le

/-- info: 'FormalResearch.ModularBootstrap.slitBoundaryMapC_injOn_UHP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitBoundaryMapC_injOn_UHP

/-- info: 'FormalResearch.ModularBootstrap.lemma_T1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.lemma_T1

end FormalResearch.ModularBootstrap
