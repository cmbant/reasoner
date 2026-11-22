module

public import FormalResearch.ModularBootstrap.Blowup.PotentialAndWeight
public import FormalResearch.ModularBootstrap.Integration.StripKernel
public import FormalResearch.Special.AiryHypergeometric
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Complex Sector Asymptotic of `I₀` and Unconditional Lemma T3

Source:
* `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), proof of (c);
* `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma `bl:T3` and its proof.

Proves the classical Laplace asymptotic for `besselI0C z` uniformly in closed sectors
`|arg z| ≤ π/2 - ε` as `|z| → ∞`, discharges `BesselI0Asymptotic` from
`Blowup.PotentialAndWeight`, and derives unconditional forms of `lemma_T3` and `lemma_T3_W_bound`.

## Main results
* `integration_besselI0C_eq_blowup`: `Integration.besselI0C z = besselI0C z` for all `z : ℂ`.
* `complex_gaussian_Ioi`: `∫ t in Ioi 0, exp (-z * t^2) = (√π / 2 : ℂ) * z ^ (-(1/2 : ℂ))` for
  `0 < z.re`.
* `besselI0C_sector_asymptotic_of_re_ge`: quantitative sector asymptotic on
  `0 < κ * ‖z‖ ≤ z.re`, `r₀ ≤ z.re`.
* `besselI0C_sector_asymptotic`: uniform asymptotic `‖besselI0C z - asC z‖ ≤ (C / ‖z‖) * ‖asC z‖`
  in every closed sector `|z.arg| ≤ π / 2 - ε`, `R ≤ ‖z‖`.
* `besselI0Asymptotic`: proof of `Blowup.BesselI0Asymptotic` (`2 ≤ z.re`, `|z.im| ≤ z.re`).
* `lemma_T3_unconditional`, `lemma_T3_W_bound_unconditional`: unconditional versions of `bl:T3`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set intervalIntegral
open scoped Real Nat Interval

namespace FormalResearch.ModularBootstrap.ComplexBessel

/-! ### Section 1: Equivalence between series and integral definitions of `I₀(z)` -/

private lemma integration_besselI0C_differentiable :
    Differentiable ℂ Integration.besselI0C := by
  intro z₀
  have h1 : HasDerivAt (fun z : ℂ => ∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)))
      (∫ θ in (0 : ℝ)..π, (Real.cos θ : ℂ) * Complex.exp (z₀ * (Real.cos θ : ℝ))) z₀ := by
    let F : ℂ → ℝ → ℂ := fun z θ => Complex.exp (z * (Real.cos θ : ℝ))
    let F' : ℂ → ℝ → ℂ := fun z θ => (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ))
    have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Ι (0 : ℝ) π)) :=
      Eventually.of_forall fun z => (by fun_prop : Continuous (F z)).aestronglyMeasurable
    have hF_int : IntervalIntegrable (F z₀) volume 0 π :=
      (by fun_prop : Continuous (F z₀)).intervalIntegrable 0 π
    have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ι (0 : ℝ) π)) :=
      (by fun_prop : Continuous (F' z₀)).aestronglyMeasurable
    have hbound : ∀ᵐ θ : ℝ, θ ∈ Ι (0 : ℝ) π → ∀ z ∈ ball z₀ 1, ‖F' z θ‖ ≤ Real.exp (‖z₀‖ + 1) := by
      refine Eventually.of_forall fun θ _ z hz => ?_
      have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have hlt : ‖z - z₀‖ < 1 := by simpa [Complex.dist_eq] using mem_ball.mp hz
        linarith [show ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ by simpa using norm_add_le (z - z₀) z₀]
      have hre : (z * (Real.cos θ : ℝ)).re ≤ ‖z₀‖ + 1 := by
        calc (z * (Real.cos θ : ℝ)).re ≤ ‖z * (Real.cos θ : ℝ)‖ := Complex.re_le_norm _
          _ = ‖z‖ * |Real.cos θ| := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ (‖z₀‖ + 1) * 1 := mul_le_mul hz_norm hcos (abs_nonneg _) (by positivity)
          _ = ‖z₀‖ + 1 := mul_one _
      calc ‖F' z θ‖ = |Real.cos θ| * Real.exp ((z * (Real.cos θ : ℝ)).re) := by
            dsimp [F']; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
        _ ≤ 1 * Real.exp (‖z₀‖ + 1) :=
            mul_le_mul hcos (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le zero_le_one
        _ = Real.exp (‖z₀‖ + 1) := one_mul _
    have hdiff : ∀ᵐ θ : ℝ, θ ∈ Ι (0 : ℝ) π →
        ∀ z ∈ ball z₀ 1, HasDerivAt (F · θ) (F' z θ) z := by
      refine Eventually.of_forall fun θ _ z _ => ?_
      have hd : HasDerivAt (fun w : ℂ => w * (Real.cos θ : ℂ)) (Real.cos θ : ℂ) z := by
        simpa using (hasDerivAt_id z).mul_const (Real.cos θ : ℂ)
      exact (hd.cexp).congr_deriv (by dsimp [F']; ring)
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (ball_mem_nhds z₀ one_pos) hF_meas hF_int hF'_meas hbound
      intervalIntegrable_const hdiff).2
  have h2 : Integration.besselI0C =
      fun z : ℂ => (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)) := rfl
  rw [h2]
  exact (h1.const_mul (π : ℂ)⁻¹).differentiableAt

private lemma blowup_besselI0C_ofReal (x : ℝ) :
    besselI0C (x : ℂ) = (Bessel.besselI0 x : ℂ) := by
  rw [besselI0C_eq_hgfun, FormalResearch.Special.regularizedHGFun_zero_singleton]
  rw [Bessel.besselI0_eq, Bessel.besselS]
  have hy : 0 ≤ x ^ 2 / 4 := by positivity
  have hsum : HasSum (fun k : ℕ => ((Bessel.besselTerm 0 (x ^ 2 / 4) k : ℝ) : ℂ))
      ((∑' k : ℕ, Bessel.besselTerm 0 (x ^ 2 / 4) k : ℝ) : ℂ) :=
    Complex.ofRealCLM.hasSum (Bessel.besselS_hasSum 0 hy)
  have hterm : ∀ k : ℕ, (((x : ℂ) ^ 2 / 4) ^ k / ((k ! : ℂ) * Complex.Gamma (1 + (k : ℂ)))) =
      ((Bessel.besselTerm 0 (x ^ 2 / 4) k : ℝ) : ℂ) := fun k => by
    unfold Bessel.besselTerm
    rw [add_comm (1 : ℂ) (k : ℂ), Complex.Gamma_nat_eq_factorial, show (k + 0)! = k ! from rfl]
    push_cast
    ring
  rw [← hsum.tsum_eq]
  refine tsum_congr fun k => ?_
  rw [show 1 / ((k ! : ℂ) * Complex.Gamma (1 + (k : ℂ))) * ((x : ℂ) ^ 2 / 4) ^ k =
      ((x : ℂ) ^ 2 / 4) ^ k / ((k ! : ℂ) * Complex.Gamma (1 + (k : ℂ))) by ring]
  exact hterm k

/-- The integral representation `Integration.besselI0C` and series definition `besselI0C` agree on
all of `ℂ`. -/
theorem integration_besselI0C_eq_blowup (z : ℂ) :
    Integration.besselI0C z = besselI0C z := by
  have han1 : AnalyticOnNhd ℂ Integration.besselI0C univ :=
    (integration_besselI0C_differentiable.differentiableOn).analyticOnNhd isOpen_univ
  have han2 : AnalyticOnNhd ℂ besselI0C univ :=
    (besselI0C_entire.differentiableOn).analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), Integration.besselI0C w = besselI0C w := by
    rw [frequently_nhdsWithin_iff, Filter.frequently_iff]
    intro U hU
    obtain ⟨r, hr_pos, hrU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨((r / 2 : ℝ) : ℂ), hrU ?_, ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr_pos)]
      linarith
    · rw [Integration.besselI0C_ofReal, blowup_besselI0C_ofReal]
    · simp only [mem_compl_iff, mem_singleton_iff]
      exact Complex.ofReal_ne_zero.mpr (half_pos hr_pos).ne'
  exact congrFun (han1.eq_of_frequently_eq han2 hfreq) z

/-! ### Section 2: Complex Gaussian integral on `Re z > 0` -/

private lemma integrableOn_exp_neg_mul_sq_complex {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2)) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2))
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2)).aestronglyMeasurable
  refine (Bessel.gauss_integrableOn hz).mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => ?_)
  rw [Complex.norm_exp]
  have hre : (-z * (t : ℂ) ^ 2).re = -z.re * t ^ 2 := by
    rw [show (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) by push_cast; rfl, neg_mul, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
  rw [hre]

private lemma integrableOn_sq_mul_exp_neg_mul_sq {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-δ * t ^ 2)) (Ioi (0 : ℝ)) := by
  have hdom : Integrable (fun t : ℝ => (2 / δ) * Real.exp (-(δ / 2) * t ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Bessel.gauss_integrableOn (by positivity : 0 < δ / 2)).const_mul (2 / δ)
  refine hdom.mono
    ((measurable_id.pow_const 2).mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_id.pow_const 2)))).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun (t : ℝ) _ => ?_)
  have hb_nn : 0 ≤ t ^ 2 * Real.exp (-δ * t ^ 2) := mul_nonneg (sq_nonneg t) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hb_nn, Real.norm_of_nonneg (by positivity)]
  have hy : δ / 2 * t ^ 2 ≤ Real.exp (δ / 2 * t ^ 2) := by
    have := Real.add_one_le_exp (δ / 2 * t ^ 2); linarith
  have hexp_split : Real.exp (-δ * t ^ 2) =
      Real.exp (-(δ / 2 * t ^ 2)) * Real.exp (-(δ / 2) * t ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp_inv : Real.exp (δ / 2 * t ^ 2) * Real.exp (-(δ / 2 * t ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hle1 : (δ / 2 * t ^ 2) * Real.exp (-(δ / 2 * t ^ 2)) ≤ 1 := by
    have hexp_mul := mul_le_mul_of_nonneg_right hy (Real.exp_pos (-(δ / 2 * t ^ 2))).le
    linarith [hexp_mul, hexp_inv]
  have hle2 : t ^ 2 * Real.exp (-(δ / 2 * t ^ 2)) ≤ 2 / δ := by
    have hmul : (δ / 2) * (t ^ 2 * Real.exp (-(δ / 2 * t ^ 2))) ≤ 1 := by linarith
    calc t ^ 2 * Real.exp (-(δ / 2 * t ^ 2))
        = (2 / δ) * ((δ / 2) * (t ^ 2 * Real.exp (-(δ / 2 * t ^ 2)))) := by
          have hδ0 : δ ≠ 0 := hδ.ne'
          field_simp [hδ0]
      _ ≤ (2 / δ) * 1 := mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = 2 / δ := mul_one _
  calc t ^ 2 * Real.exp (-δ * t ^ 2) =
        (t ^ 2 * Real.exp (-(δ / 2 * t ^ 2))) * Real.exp (-(δ / 2) * t ^ 2) := by
          rw [hexp_split]; ring
    _ ≤ (2 / δ) * Real.exp (-(δ / 2) * t ^ 2) :=
        mul_le_mul_of_nonneg_right hle2 (Real.exp_pos _).le

private lemma hasDerivAt_complex_gaussian {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (fun z : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2))
      (∫ t in Ioi (0 : ℝ), -((t : ℂ) ^ 2) * Complex.exp (-z₀ * (t : ℂ) ^ 2)) z₀ := by
  let δ : ℝ := z₀.re / 2
  have hδ : 0 < δ := by positivity
  let F : ℂ → ℝ → ℂ := fun z t => Complex.exp (-z * (t : ℂ) ^ 2)
  let F' : ℂ → ℝ → ℂ := fun z t => -((t : ℂ) ^ 2) * Complex.exp (-z * (t : ℂ) ^ 2)
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun z =>
      (Complex.continuous_exp.measurable.comp
        (measurable_const.mul ((Complex.continuous_ofReal.measurable).pow_const 2))).aestronglyMeasurable
  have hF_int : Integrable (F z₀) (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_exp_neg_mul_sq_complex hz₀
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ioi (0 : ℝ))) :=
    (((Complex.continuous_ofReal.measurable.pow_const 2).neg).mul
      (Complex.continuous_exp.measurable.comp
        (measurable_const.mul ((Complex.continuous_ofReal.measurable).pow_const 2)))).aestronglyMeasurable
  have hbound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ ball z₀ δ,
      ‖F' z t‖ ≤ t ^ 2 * Real.exp (-δ * t ^ 2) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun (t : ℝ) _ z hz => ?_)
    have hz_re : δ < z.re := by
      have habs : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
      have hball : ‖z - z₀‖ < δ := by simpa [Complex.dist_eq] using mem_ball.mp hz
      have hδ_eq : δ = z₀.re / 2 := rfl
      linarith [(abs_lt.mp (habs.trans_lt hball)).1]
    dsimp only [F']
    rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ) ^ 2).re = -z.re * t ^ 2 := by
      rw [show (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) by push_cast; rfl, neg_mul, Complex.neg_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
    rw [hre]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg t)
    nlinarith [sq_nonneg t]
  have hdiff : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ ball z₀ δ,
      HasDerivAt (F · t) (F' z t) z := by
    refine Eventually.of_forall fun t z _ => ?_
    have hd : HasDerivAt (fun w : ℂ => -w * (t : ℂ) ^ 2) (-((t : ℂ) ^ 2)) z := by
      have hd0 : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
      exact (hd0.mul_const ((t : ℂ) ^ 2)).congr_deriv (by simp)
    exact (hd.cexp).congr_deriv (by dsimp [F']; rw [mul_comm])
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (F' := F') (x₀ := z₀)
    (s := ball z₀ δ) (bound := fun t : ℝ => t ^ 2 * Real.exp (-δ * t ^ 2))
    (ball_mem_nhds z₀ hδ) hF_meas hF_int hF'_meas hbound
    (integrableOn_sq_mul_exp_neg_mul_sq hδ) hdiff
  simpa [F, F'] using key.2

private lemma complex_gaussian_differentiableOn :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2))
      {z : ℂ | 0 < z.re} :=
  fun _ hz => (hasDerivAt_complex_gaussian hz).differentiableAt.differentiableWithinAt

/-- Complex Gaussian integral on `Re z > 0`:
`∫ t in Ioi 0, exp (-z * t^2) = (√π / 2 : ℂ) * z ^ (-(1/2 : ℂ))`. -/
theorem complex_gaussian_Ioi {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2) =
      ((√Real.pi / 2 : ℝ) : ℂ) * z ^ (-(1 / 2 : ℂ)) := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  let f : ℂ → ℂ := fun w => ∫ t in Ioi (0 : ℝ), Complex.exp (-w * (t : ℂ) ^ 2)
  let g : ℂ → ℂ := fun w => ((√Real.pi / 2 : ℝ) : ℂ) * w ^ (-(1 / 2 : ℂ))
  have hf_an : AnalyticOnNhd ℂ f U :=
    complex_gaussian_differentiableOn.analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ g U := fun w hw => by
    refine analyticAt_const.mul (analyticAt_id.cpow analyticAt_const ?_)
    exact Complex.mem_slitPlane_iff.mpr (Or.inl hw)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = g w := by
    rw [frequently_nhdsWithin_iff, Filter.frequently_iff]
    intro V hV
    obtain ⟨r, hr_pos, hrV⟩ := Metric.mem_nhds_iff.mp hV
    let x : ℝ := 1 + min (r / 2) (1 / 2)
    have hx_pos : 0 < x := by positivity
    refine ⟨(x : ℂ), hrV ?_, ?_, ?_⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, x]
      have hmn : 0 ≤ min (r / 2) (1 / 2) := le_min (half_pos hr_pos).le (by norm_num)
      rw [show ((1 + min (r / 2) (1 / 2) : ℝ) : ℂ) - 1 = ((min (r / 2) (1 / 2) : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmn]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr_pos)
    · change ∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (t : ℂ) ^ 2) =
        ((√Real.pi / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ))
      have hofReal : ∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (t : ℂ) ^ 2) =
          ((∫ t in Ioi (0 : ℝ), Real.exp (-x * t ^ 2) : ℝ) : ℂ) := by
        have hfn : (fun t : ℝ => Complex.exp (-(x : ℂ) * (t : ℂ) ^ 2)) =
            fun t : ℝ => Complex.ofRealCLM (Real.exp (-x * t ^ 2)) := by
          ext t; simp [Complex.ofReal_exp]
        rw [hfn, Complex.ofRealCLM.integral_comp_comm (Bessel.gauss_integrableOn hx_pos)]
        rfl
      rw [hofReal, Bessel.gauss_Ioi x]
      have hreal_eq : √(Real.pi / x) / 2 = (√Real.pi / 2) * x ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_div Real.pi_pos.le, Real.rpow_neg hx_pos.le, div_eq_mul_inv]
        simp_rw [Real.sqrt_eq_rpow]
        ring
      rw [hreal_eq, Complex.ofReal_mul, show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hx_pos.le]
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have : x = 1 := Complex.ofReal_injective h
      linarith [lt_min (half_pos hr_pos) (by norm_num : (0 : ℝ) < 1 / 2)]
  exact hf_an.eqOn_of_preconnected_of_frequently_eq hg_an hU_conn (by simp [U]) hfreq hz

/-! ### Section 3: Change of variables `t = √2 sin(θ/2)`, chord bound, and tails -/

private lemma integral_cos_half_change (z : ℂ) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) =
      ∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
        ((√2 / √(1 - t ^ 2 / 2) : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun θ => √2 * Real.sin (θ / 2)
  let f' : ℝ → ℝ := fun θ => (√2 / 2) * Real.cos (θ / 2)
  let g : ℝ → ℂ := fun t => Complex.exp (-z * (t : ℂ) ^ 2) * ((√2 / √(1 - t ^ 2 / 2) : ℝ) : ℂ)
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (Real.pi / 2), HasDerivAt f (f' θ) θ := by
    intro θ _
    have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (x / 2)) (Real.cos (θ / 2) * (1 / 2)) θ :=
      h1.sin
    exact (h2.const_mul √2).congr_deriv (by dsimp [f']; ring)
  have hf'_cont : ContinuousOn f' (uIcc (0 : ℝ) (Real.pi / 2)) :=
    (by fun_prop : Continuous f').continuousOn
  have hg_cont : ContinuousOn g (f '' uIcc (0 : ℝ) (Real.pi / 2)) := by
    have himg : f '' uIcc (0 : ℝ) (Real.pi / 2) ⊆ Icc 0 1 := by
      rintro t ⟨θ, hθ, rfl⟩
      rw [uIcc_of_le (by positivity)] at hθ
      have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hsin_le : Real.sin (θ / 2) ≤ Real.sin (Real.pi / 4) :=
        Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          (by linarith [hθ.2])
      rw [Real.sin_pi_div_four] at hsin_le
      refine ⟨mul_nonneg (Real.sqrt_nonneg _) hsin_nn, ?_⟩
      calc √2 * Real.sin (θ / 2) ≤ √2 * (√2 / 2) := by gcongr
        _ = 1 := by rw [← mul_div_assoc, Real.mul_self_sqrt zero_le_two]; norm_num
    refine ContinuousOn.mono ?_ himg
    intro t ht
    have hpos : 0 < 1 - t ^ 2 / 2 := by
      have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      linarith
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun s : ℝ => Complex.exp (-z * (s : ℂ) ^ 2)) t := by fun_prop
    have h2 : ContinuousAt (fun s : ℝ => ((√2 / √(1 - s ^ 2 / 2) : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div ((Real.continuous_sqrt.continuousAt.comp
          (by fun_prop : Continuous fun s : ℝ => 1 - s ^ 2 / 2).continuousAt))
          (Real.sqrt_ne_zero'.mpr hpos))
    exact h1.mul h2
  have hcomp := intervalIntegral.integral_deriv_smul_comp' hderiv hf'_cont hg_cont
  have hf0 : f 0 = 0 := by simp [f]
  have hfpi : f (Real.pi / 2) = 1 := by
    dsimp [f]
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four, ← mul_div_assoc,
      Real.mul_self_sqrt zero_le_two]
    norm_num
  rw [hf0, hfpi] at hcomp
  rw [← hcomp]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le (by positivity)] at hθ
  have hcos_pos : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hf_sq : f θ ^ 2 = 1 - Real.cos θ := by
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    have hcos_sq := Real.cos_sq (θ / 2)
    have hsin_sq := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hcos_sq
    linarith
  have hsqrt_eq : √(1 - f θ ^ 2 / 2) = Real.cos (θ / 2) := by
    rw [hf_sq, show 1 - (1 - Real.cos θ) / 2 = (1 + Real.cos θ) / 2 by ring]
    have hcos_half : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
      have := Real.cos_sq (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      linarith
    rw [← hcos_half, Real.sqrt_sq hcos_pos.le]
  dsimp only [Function.comp_apply, g, f']
  rw [Complex.real_smul, hsqrt_eq, ← Complex.ofReal_pow, hf_sq]
  have hcos_ne : (Real.cos (θ / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos_pos.ne'
  have h2_sq : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]; norm_num
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_div]
  calc Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))
      = Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((((√2 : ℂ) * (√2 : ℂ)) / 2) *
          ((Real.cos (θ / 2) : ℂ) / (Real.cos (θ / 2) : ℂ))) := by
        rw [h2_sq, div_self hcos_ne]; norm_num
    _ = ((√2 : ℂ) / 2 * (Real.cos (θ / 2) : ℂ)) *
          (Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((√2 : ℂ) / (Real.cos (θ / 2) : ℂ))) := by
        ring

private lemma chord_bound_inv_sqrt {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ 1 / √(1 - u / 2) - 1 ∧ 1 / √(1 - u / 2) - 1 ≤ (√2 - 1) * u := by
  have hpos : 0 < 1 - u / 2 := by linarith
  have hsqrt_pos : 0 < √(1 - u / 2) := Real.sqrt_pos.mpr hpos
  have hle1 : √(1 - u / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  constructor
  · rw [sub_nonneg, one_le_div hsqrt_pos]; exact hle1
  · rw [sub_le_iff_le_add, div_le_iff₀ hsqrt_pos]
    have hrhs_nn : 0 ≤ (√2 - 1) * u + 1 := by
      have : 0 ≤ √2 - 1 :=
        sub_nonneg.mpr (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num))
      positivity
    rw [← Real.sqrt_sq hrhs_nn, ← Real.sqrt_mul (by positivity : 0 ≤ ((√2 - 1) * u + 1) ^ 2),
      Real.one_le_sqrt]
    set c : ℝ := √2 - 1 with hc_def
    have hfact : (1 - u / 2) * (1 + c * u) ^ 2 - 1 =
        u * (1 - u) * ((2 * c - 1 / 2) + (1 / 2 - c) * u) := by
      have hcr : c ^ 2 = 1 - 2 * c := by
        rw [hc_def]; ring_nf; rw [Real.sq_sqrt zero_le_two]; ring
      calc (1 - u / 2) * (1 + c * u) ^ 2 - 1
          = (2 * c - 1 / 2) * u + (c ^ 2 - c) * u ^ 2 - (c ^ 2 / 2) * u ^ 3 := by ring
        _ = (2 * c - 1 / 2) * u + ((1 - 2 * c) - c) * u ^ 2 - ((1 - 2 * c) / 2) * u ^ 3 := by
            rw [hcr]
        _ = u * (1 - u) * ((2 * c - 1 / 2) + (1 / 2 - c) * u) := by ring
    have hsqrt2_lo : (1.41 : ℝ) < √2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.41)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hsqrt2_hi : √2 < (1.42 : ℝ) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.42)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hc1 : 0 ≤ 2 * c - 1 / 2 := by rw [hc_def]; linarith
    have hc2' : 0 ≤ 1 / 2 - c := by rw [hc_def]; linarith
    have hnonneg : 0 ≤ u * (1 - u) * ((2 * c - 1 / 2) + (1 / 2 - c) * u) := by
      have : 0 ≤ 1 - u := sub_nonneg.mpr hu1
      positivity
    linarith

private lemma tail_exp_neg_sq_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (1 : ℝ), Real.exp (-a * t ^ 2) ≤ Real.exp (-a) / a := by
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-a * t ^ 2)) (Ioi 1) :=
    (Bessel.gauss_integrableOn ha).mono_set (Ioi_subset_Ioi zero_le_one)
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (a := -a) (by linarith) 1
  calc ∫ t in Ioi (1 : ℝ), Real.exp (-a * t ^ 2)
      ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-a * t) := by
        refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun t ht => ?_
        refine Real.exp_le_exp.mpr ?_
        have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
        nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ht1)]
    _ = Real.exp (-a) / a := by
        rw [integral_exp_mul_Ioi (by linarith)]
        simp [div_eq_mul_inv]

private lemma norm_exp_mul_I_sub_one_tail {z : ℂ} (hz : 0 < z.re) :
    ‖∫ t in Ioi (1 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2)‖ ≤ Real.exp (-z.re) / z.re := by
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2)) (Ioi 1) :=
    (integrableOn_exp_neg_mul_sq_complex hz).mono_set (Ioi_subset_Ioi zero_le_one)
  have hre : ∀ t : ℝ, (-z * (t : ℂ) ^ 2).re = -z.re * t ^ 2 := fun t => by
    rw [show (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) by push_cast; rfl, neg_mul, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-z * (t : ℂ) ^ 2)‖ = Real.exp (-z.re * t ^ 2) := fun t => by
    rw [Complex.norm_exp, hre t]
  calc ‖∫ t in Ioi (1 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2)‖
      ≤ ∫ t in Ioi (1 : ℝ), ‖Complex.exp (-z * (t : ℂ) ^ 2)‖ := norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (1 : ℝ), Real.exp (-z.re * t ^ 2) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => hnorm t
    _ ≤ Real.exp (-z.re) / z.re := tail_exp_neg_sq_Ioi hz

private lemma norm_chord_error_le {z : ℂ} (hz : 0 < z.re) :
    ‖∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
        ((1 / √(1 - t ^ 2 / 2) - 1 : ℝ) : ℂ)‖ ≤
      (√2 - 1) * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) := by
  have hcont : ContinuousOn (fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2) *
      ((1 / √(1 - t ^ 2 / 2) - 1 : ℝ) : ℂ)) (Icc 0 1) := by
    intro t ht
    have hpos : 0 < 1 - t ^ 2 / 2 := by nlinarith [ht.1, ht.2]
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun s : ℝ => Complex.exp (-z * (s : ℂ) ^ 2)) t := by fun_prop
    have h2 : ContinuousAt (fun s : ℝ => ((1 / √(1 - s ^ 2 / 2) - 1 : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_const.div ((Real.continuous_sqrt.continuousAt.comp
          (by fun_prop : Continuous fun s : ℝ => 1 - s ^ 2 / 2).continuousAt))
          (Real.sqrt_ne_zero'.mpr hpos)).sub continuousAt_const)
    exact h1.mul h2
  have hle : ‖∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
      ((1 / √(1 - t ^ 2 / 2) - 1 : ℝ) : ℂ)‖ ≤
      ∫ t in (0 : ℝ)..1, (√2 - 1) * (t ^ 2 * Real.exp (-z.re * t ^ 2)) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_
      ((by fun_prop : Continuous fun t : ℝ => (√2 - 1) * (t ^ 2 * Real.exp (-z.re * t ^ 2))).intervalIntegrable 0 1))
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 := ht.2
    have hchord := chord_bound_inv_sqrt (sq_nonneg t) (by nlinarith)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hchord.1, Complex.norm_exp]
    have hre : (-z * (t : ℂ) ^ 2).re = -z.re * t ^ 2 := by
      rw [show (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) by push_cast; rfl, neg_mul, Complex.neg_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
    rw [hre]
    calc Real.exp (-z.re * t ^ 2) * (1 / √(1 - t ^ 2 / 2) - 1)
        ≤ Real.exp (-z.re * t ^ 2) * ((√2 - 1) * t ^ 2) :=
          mul_le_mul_of_nonneg_left hchord.2 (Real.exp_pos _).le
      _ = (√2 - 1) * (t ^ 2 * Real.exp (-z.re * t ^ 2)) := by ring
  refine hle.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hmom := Bessel.moment_succ_succ_le hz 0
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at hmom
  have hgauss := Bessel.gauss_interval_le hz zero_le_one
  have hsqrt2_nn : 0 ≤ √2 - 1 :=
    sub_nonneg.mpr (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num))
  have hrpow : √(Real.pi / z.re) / (4 * z.re) = √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow]
    have hz_rpow : z.re ^ (3 / 2 : ℝ) = z.re ^ (1 / 2 : ℝ) * z.re := by
      calc z.re ^ (3 / 2 : ℝ) = z.re ^ (1 / 2 + 1 : ℝ) := by norm_num
        _ = z.re ^ (1 / 2 : ℝ) * z.re ^ (1 : ℝ) := Real.rpow_add hz _ _
        _ = z.re ^ (1 / 2 : ℝ) * z.re := by rw [Real.rpow_one]
    rw [hz_rpow, Real.sqrt_eq_rpow]
    field_simp [hz.ne', (Real.rpow_pos_of_pos hz _).ne']
  calc (√2 - 1) * ∫ t in (0 : ℝ)..1, t ^ 2 * Real.exp (-z.re * t ^ 2)
      ≤ (√2 - 1) * (1 / (2 * z.re) * ∫ t in (0 : ℝ)..1, Real.exp (-z.re * t ^ 2)) := by
        gcongr
    _ ≤ (√2 - 1) * (1 / (2 * z.re) * (√(Real.pi / z.re) / 2)) := by gcongr
    _ = (√2 - 1) * (√(Real.pi / z.re) / (4 * z.re)) := by ring
    _ = (√2 - 1) * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) := by rw [hrpow]; ring

private lemma norm_pi_half_tail_le {z : ℂ} (hz : 0 < z.re) :
    ‖∫ θ in (Real.pi / 2)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))‖ ≤
      (Real.pi / 2) * Real.exp (-z.re) := by
  have hle_pi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hbd : ∀ θ ∈ Ioc (Real.pi / 2) Real.pi,
      ‖Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))‖ ≤ Real.exp (-z.re) := by
    intro θ hθ
    rw [Complex.norm_exp]
    have hre : (-z * ((1 - Real.cos θ : ℝ) : ℂ)).re = -z.re * (1 - Real.cos θ) := by
      rw [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, neg_mul]
    rw [hre]
    refine Real.exp_le_exp.mpr ?_
    have hcos_nonpos : Real.cos θ ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2, Real.pi_pos])
    nlinarith [hz]
  have hint := intervalIntegral.norm_integral_le_of_norm_le hle_pi
    (Eventually.of_forall hbd) (intervalIntegrable_const (μ := volume))
  simpa [intervalIntegral.integral_const, smul_eq_mul, Real.norm_of_nonneg Real.pi_pos.le,
    Real.norm_of_nonneg (Real.exp_pos _).le,
    show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, mul_comm] using hint

/-! ### Section 4: Exact decomposition of `besselI0C z - asC z` and sector asymptotic -/

private lemma asC_eq_gaussian {z : ℂ} (hz : 0 < z.re) :
    asC z = (Complex.exp z / (Real.pi : ℂ)) *
      (√2 * ∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2)) := by
  rw [complex_gaussian_Ioi hz]
  unfold asC
  have hz_ne : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcpow : (2 * (Real.pi : ℂ) * z) ^ (1 / 2 : ℂ) =
      ((√(2 * Real.pi) : ℝ) : ℂ) * z ^ (1 / 2 : ℂ) := by
    rw [show 2 * (Real.pi : ℂ) * z = ((2 * Real.pi : ℝ) : ℂ) * z by push_cast; ring,
      ofReal_mul_cpow h2pi_pos z (1 / 2 : ℂ),
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow h2pi_pos.le, ← Real.sqrt_eq_rpow]
  have hz_inv : z ^ (-(1 / 2 : ℂ)) = (z ^ (1 / 2 : ℂ))⁻¹ := by
    rw [Complex.cpow_neg]
  have hsqrt_id : √2 * (√Real.pi / 2) / Real.pi = (√(2 * Real.pi))⁻¹ := by
    rw [Real.sqrt_mul zero_le_two]
    have hp : √Real.pi * √Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
    have hp_ne : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have h2_ne : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
    field_simp
    nlinarith [hp, Real.mul_self_sqrt zero_le_two]
  have hz12_ne : z ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz_ne)
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hs2pi_ne : ((√(2 * Real.pi) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr h2pi_pos).ne'
  rw [hcpow, hz_inv]
  calc Complex.exp z / (((√(2 * Real.pi) : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))
      = Complex.exp z * ((√(2 * Real.pi) : ℂ)⁻¹) * (z ^ (1 / 2 : ℂ))⁻¹ := by
        field_simp [hs2pi_ne, hz12_ne]
    _ = Complex.exp z * ((√2 * (√Real.pi / 2) / Real.pi : ℝ) : ℂ) * (z ^ (1 / 2 : ℂ))⁻¹ := by
        rw [hsqrt_id]; push_cast; rfl
    _ = (Complex.exp z / (Real.pi : ℂ)) * (√2 * (((√Real.pi / 2 : ℝ) : ℂ) * (z ^ (1 / 2 : ℂ))⁻¹)) := by
        push_cast; ring

private lemma norm_asC {z : ℂ} (hz : 0 < z.re) :
    ‖asC z‖ = Real.exp z.re / √(2 * Real.pi * ‖z‖) := by
  unfold asC
  have hz_ne : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2piz_ne : 2 * (Real.pi : ℂ) * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) hz_ne
  have hcpow_norm : ‖(2 * (Real.pi : ℂ) * z) ^ (1 / 2 : ℂ)‖ = √(2 * Real.pi * ‖z‖) := by
    rw [Complex.cpow_def_of_ne_zero h2piz_ne, Complex.norm_exp]
    have hre : (Complex.log (2 * (Real.pi : ℂ) * z) * (1 / 2 : ℂ)).re =
        Real.log (2 * Real.pi * ‖z‖) / 2 := by
      rw [Complex.mul_re, Complex.log_re, show (1 / 2 : ℂ).re = 1 / 2 by norm_num,
        show (1 / 2 : ℂ).im = 0 by norm_num, mul_zero, sub_zero,
        norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      ring
    rw [hre, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 1; ring
  rw [norm_div, Complex.norm_exp, hcpow_norm]

private lemma besselI0C_sub_asC_decomp {z : ℂ} (hz : 0 < z.re) :
    besselI0C z - asC z = (Complex.exp z / (Real.pi : ℂ)) *
      (√2 * (∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
          ((1 / √(1 - t ^ 2 / 2) - 1 : ℝ) : ℂ))
       - √2 * (∫ t in Ioi (1 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2))
       + ∫ θ in (Real.pi / 2)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))) := by
  rw [← integration_besselI0C_eq_blowup]
  have hI0 : Integration.besselI0C z = (Complex.exp z / (Real.pi : ℂ)) *
      ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) := by
    unfold Integration.besselI0C
    have h1 : (Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos θ : ℝ)) =
        (Complex.exp z / (Real.pi : ℂ)) *
          ((Complex.exp z)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos θ : ℝ))) := by
      have hexp : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
      field_simp [hexp]
    rw [h1]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hsplit_pi : ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2), Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))) +
        ∫ θ in (Real.pi / 2)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) := by
    have hc : Continuous fun θ : ℝ => Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) := by fun_prop
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have hsplit_gauss : ∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2) =
      (∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2)) +
        ∫ t in Ioi (1 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2) := by
    have hint := integrableOn_exp_neg_mul_sq_complex hz
    rw [intervalIntegral.integral_of_le zero_le_one, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
      MeasureTheory.setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hsplit_chord :
      (∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) * ((√2 / √(1 - t ^ 2 / 2) : ℝ) : ℂ)) =
      √2 * (∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
          ((1 / √(1 - t ^ 2 / 2) - 1 : ℝ) : ℂ)) +
        √2 * (∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2)) := by
    have hc1 : IntervalIntegrable (fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2) *
        ((1 / √(1 - t ^ 2 / 2) - 1 : ℝ) : ℂ)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      intro t ht
      have hpos : 0 < 1 - t ^ 2 / 2 := by nlinarith [ht.1, ht.2]
      refine ContinuousAt.continuousWithinAt ?_
      exact (by fun_prop : ContinuousAt (fun s : ℝ => Complex.exp (-z * (s : ℂ) ^ 2)) t).mul
        (Complex.continuous_ofReal.continuousAt.comp ((continuousAt_const.div
          (Real.continuous_sqrt.continuousAt.comp (by fun_prop : Continuous fun s : ℝ => 1 - s ^ 2 / 2).continuousAt)
          (Real.sqrt_ne_zero'.mpr hpos)).sub continuousAt_const))
    have hc2 : IntervalIntegrable (fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2)) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * (t : ℂ) ^ 2)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hc1.const_mul _) (hc2.const_mul _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring
  rw [hI0, hsplit_pi, integral_cos_half_change, hsplit_chord, asC_eq_gaussian hz, hsplit_gauss]
  ring

/-- Quantitative complex sector asymptotic for `I₀(z)` on `{z : ℂ | 0 < z.re ∧ κ * ‖z‖ ≤ z.re}`
with `0 < κ` (uniform even for small `|z|`, since `|as(z)| ~ |z|^{-1/2} → ∞` as `|z| → 0`). -/
theorem besselI0C_sector_asymptotic_of_re_pos {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.re → κ * ‖z‖ ≤ z.re →
      ‖besselI0C z - asC z‖ ≤ (C / ‖z‖) * ‖asC z‖ := by
  let C : ℝ := (√2 * (√2 - 1) / 2 + 2 / √Real.pi + √Real.pi * √2) / κ ^ (3 / 2 : ℝ)
  have hC_nn : 0 ≤ C := by
    have h1 : 0 ≤ √2 - 1 :=
      sub_nonneg.mpr (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num))
    positivity
  refine ⟨C, hC_nn, fun z hz_pos hsec => ?_⟩
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hz_pos (Complex.re_le_norm z)
  rw [besselI0C_sub_asC_decomp hz_pos, norm_mul, norm_div, Complex.norm_exp,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  set I1 := ∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
    ((1 / √(1 - t ^ 2 / 2) - 1 : ℝ) : ℂ)
  set I2 := ∫ t in Ioi (1 : ℝ), Complex.exp (-z * (t : ℂ) ^ 2)
  set I3 := ∫ θ in (Real.pi / 2)..Real.pi, Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))
  have htri : ‖(√2 : ℂ) * I1 - (√2 : ℂ) * I2 + I3‖ ≤ √2 * ‖I1‖ + √2 * ‖I2‖ + ‖I3‖ := by
    have hsqrt2 : ‖(√2 : ℂ)‖ = √2 := by
      rw [show (√2 : ℂ) = ((√2 : ℝ) : ℂ) by rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    calc ‖(√2 : ℂ) * I1 - (√2 : ℂ) * I2 + I3‖
        ≤ ‖(√2 : ℂ) * I1 - (√2 : ℂ) * I2‖ + ‖I3‖ := norm_add_le _ _
      _ ≤ (‖(√2 : ℂ) * I1‖ + ‖(√2 : ℂ) * I2‖) + ‖I3‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ = √2 * ‖I1‖ + √2 * ‖I2‖ + ‖I3‖ := by rw [norm_mul, norm_mul, hsqrt2]
  have hI1 := norm_chord_error_le hz_pos
  have hI2 := norm_exp_mul_I_sub_one_tail hz_pos
  have hI3 := norm_pi_half_tail_le hz_pos
  have hsqrt2_nn : 0 ≤ √2 := Real.sqrt_nonneg _
  have hsum_bd : √2 * ‖I1‖ + √2 * ‖I2‖ + ‖I3‖ ≤
      √2 * ((√2 - 1) * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ))) +
      √2 * (Real.exp (-z.re) / z.re) + (Real.pi / 2) * Real.exp (-z.re) := by
    gcongr
  have has_eq : Real.exp z.re / Real.pi = √(2 * Real.pi * ‖z‖) / Real.pi * ‖asC z‖ := by
    rw [norm_asC hz_pos]
    have hs_ne : √(2 * Real.pi * ‖z‖) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp [hs_ne, Real.pi_pos.ne']
  have hzr_pow : κ ^ (3 / 2 : ℝ) * ‖z‖ ^ (3 / 2 : ℝ) ≤ z.re ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow hκ.le (norm_nonneg z)]
    exact Real.rpow_le_rpow (by positivity) hsec (by norm_num)
  have hscale_eq : √(2 * Real.pi * ‖z‖) / Real.pi = √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul zero_le_two]
    have hp : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hp_ne : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp [hp_ne, Real.pi_pos.ne']
    rw [← Real.sqrt_eq_rpow]
    calc √Real.pi ^ 2 * √‖z‖ = Real.pi * √‖z‖ := by rw [hp]
      _ = Real.pi * √‖z‖ := rfl
  have hz_12_32 : ‖z‖ ^ (1 / 2 : ℝ) / ‖z‖ ^ (3 / 2 : ℝ) = 1 / ‖z‖ := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hnorm_pos, Real.rpow_one]
    have h12 : ‖z‖ ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hnorm_pos _).ne'
    field_simp [h12, hnorm_pos.ne']
  have hz_ratio : ‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ) ≤ 1 / (κ ^ (3 / 2 : ℝ) * ‖z‖) := by
    calc ‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)
        ≤ ‖z‖ ^ (1 / 2 : ℝ) / (κ ^ (3 / 2 : ℝ) * ‖z‖ ^ (3 / 2 : ℝ)) := by gcongr
      _ = (‖z‖ ^ (1 / 2 : ℝ) / ‖z‖ ^ (3 / 2 : ℝ)) / κ ^ (3 / 2 : ℝ) := by ring
      _ = 1 / (κ ^ (3 / 2 : ℝ) * ‖z‖) := by rw [hz_12_32]; ring
  -- Elementary exponential bounds for all y > 0: y^{1/2} exp(-y) ≤ 1 and y^{3/2} exp(-y) ≤ 2.
  have hexp_half : Real.exp (-z.re) ≤ 1 / z.re ^ (1 / 2 : ℝ) := by
    have h1 : z.re ^ (1 / 2 : ℝ) ≤ 1 + z.re := by
      rcases le_or_gt z.re 1 with hle | hgt
      · calc z.re ^ (1 / 2 : ℝ) ≤ 1 ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hz_pos.le hle (by norm_num)
          _ = 1 := Real.one_rpow _
          _ ≤ 1 + z.re := by linarith
      · have hpow : z.re ^ (1 / 2 : ℝ) ≤ z.re ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hgt.le (by norm_num)
        rw [Real.rpow_one] at hpow
        linarith
    have h2 : z.re ^ (1 / 2 : ℝ) ≤ Real.exp z.re := by linarith [Real.add_one_le_exp z.re]
    have h3 : Real.exp z.re * Real.exp (-z.re) = 1 := by rw [← Real.exp_add]; simp
    have h4 : z.re ^ (1 / 2 : ℝ) * Real.exp (-z.re) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-z.re)).le
      linarith
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hz_pos _)]
    linarith
  have hexp_three_halves : Real.exp (-z.re) ≤ 2 / z.re ^ (3 / 2 : ℝ) := by
    have h1 : z.re ^ (3 / 2 : ℝ) ≤ 2 * Real.exp z.re := by
      rcases le_or_gt z.re 1 with hle | hgt
      · have hr : z.re ^ (3 / 2 : ℝ) ≤ 1 := by
          calc z.re ^ (3 / 2 : ℝ) ≤ 1 ^ (3 / 2 : ℝ) :=
                Real.rpow_le_rpow hz_pos.le hle (by norm_num)
            _ = 1 := Real.one_rpow _
        have hex : 1 ≤ Real.exp z.re := Real.one_le_exp hz_pos.le
        linarith
      · have hr : z.re ^ (3 / 2 : ℝ) ≤ z.re ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hgt.le (by norm_num)
        rw [Real.rpow_two] at hr
        have hq := Real.quadratic_le_exp_of_nonneg hz_pos.le
        linarith
    have h2 : Real.exp z.re * Real.exp (-z.re) = 1 := by rw [← Real.exp_add]; simp
    have h3 : z.re ^ (3 / 2 : ℝ) * Real.exp (-z.re) ≤ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-z.re)).le
      linarith
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hz_pos _)]
    linarith
  have hz_1_12 : z.re ^ (1 / 2 : ℝ) * z.re = z.re ^ (3 / 2 : ℝ) := by
    calc z.re ^ (1 / 2 : ℝ) * z.re = z.re ^ (1 / 2 : ℝ) * z.re ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = z.re ^ (1 / 2 + 1 : ℝ) := (Real.rpow_add hz_pos _ _).symm
      _ = z.re ^ (3 / 2 : ℝ) := by norm_num
  have h2sq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hp_ne : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpiece1 : √(2 * Real.pi * ‖z‖) / Real.pi *
      (√2 * ((√2 - 1) * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)))) ≤
      (√2 * (√2 - 1) / 2 / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by
    rw [hscale_eq]
    have h1 : √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi *
        (√2 * ((√2 - 1) * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)))) =
        (√2 - 1) / 2 * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := by
      field_simp [hp_ne]; nlinarith [h2sq]
    rw [h1]
    have hsub_nn : 0 ≤ √2 - 1 :=
      sub_nonneg.mpr (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num))
    have hsq2_ge1 : 1 ≤ √2 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
    calc (√2 - 1) / 2 * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ))
        ≤ (√2 - 1) / 2 * (1 / (κ ^ (3 / 2 : ℝ) * ‖z‖)) := by gcongr
      _ ≤ √2 * (√2 - 1) / 2 * (1 / (κ ^ (3 / 2 : ℝ) * ‖z‖)) := by
          gcongr; nlinarith
      _ = (√2 * (√2 - 1) / 2 / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by ring
  have hpiece2 : √(2 * Real.pi * ‖z‖) / Real.pi * (√2 * (Real.exp (-z.re) / z.re)) ≤
      (2 / √Real.pi / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by
    rw [hscale_eq]
    have h1 : Real.exp (-z.re) / z.re ≤ 1 / z.re ^ (3 / 2 : ℝ) := by
      calc Real.exp (-z.re) / z.re ≤ (1 / z.re ^ (1 / 2 : ℝ)) / z.re := by gcongr
        _ = 1 / (z.re ^ (1 / 2 : ℝ) * z.re) := by ring
        _ = 1 / z.re ^ (3 / 2 : ℝ) := by rw [hz_1_12]
    have h2 : √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * (√2 * (Real.exp (-z.re) / z.re)) ≤
        (2 / √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := by
      calc √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * (√2 * (Real.exp (-z.re) / z.re))
          ≤ √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * (√2 * (1 / z.re ^ (3 / 2 : ℝ))) := by gcongr
        _ = (√2 * √2 / √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := by ring
        _ = (2 / √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := by rw [h2sq]
    calc √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * (√2 * (Real.exp (-z.re) / z.re))
        ≤ (2 / √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := h2
      _ ≤ (2 / √Real.pi) * (1 / (κ ^ (3 / 2 : ℝ) * ‖z‖)) := by gcongr
      _ = (2 / √Real.pi / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by ring
  have hpiece3 : √(2 * Real.pi * ‖z‖) / Real.pi * ((Real.pi / 2) * Real.exp (-z.re)) ≤
      (√Real.pi * √2 / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by
    rw [hscale_eq]
    have hpi_sq : Real.pi / √Real.pi = √Real.pi := by
      have hp : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
      field_simp [hp_ne]; exact hp.symm
    have h1 : √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * ((Real.pi / 2) * Real.exp (-z.re)) =
        (√2 / 2 * √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re)) := by
      calc √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * ((Real.pi / 2) * Real.exp (-z.re))
          = (√2 / 2 * (Real.pi / √Real.pi)) * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re)) := by ring
        _ = (√2 / 2 * √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re)) := by rw [hpi_sq]
    calc √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * ((Real.pi / 2) * Real.exp (-z.re))
        = (√2 / 2 * √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re)) := h1
      _ ≤ (√2 / 2 * √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * (2 / z.re ^ (3 / 2 : ℝ))) := by gcongr
      _ = (√Real.pi * √2) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := by ring
      _ ≤ (√Real.pi * √2) * (1 / (κ ^ (3 / 2 : ℝ) * ‖z‖)) := by gcongr
      _ = (√Real.pi * √2 / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by ring
  calc (Real.exp z.re / Real.pi) * ‖(√2 : ℂ) * I1 - (√2 : ℂ) * I2 + I3‖
      ≤ (Real.exp z.re / Real.pi) * (√2 * ‖I1‖ + √2 * ‖I2‖ + ‖I3‖) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ ≤ (Real.exp z.re / Real.pi) *
          (√2 * ((√2 - 1) * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ))) +
            √2 * (Real.exp (-z.re) / z.re) + (Real.pi / 2) * Real.exp (-z.re)) :=
        mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ = (√(2 * Real.pi * ‖z‖) / Real.pi *
          (√2 * ((√2 - 1) * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ))) +
            √2 * (Real.exp (-z.re) / z.re) + (Real.pi / 2) * Real.exp (-z.re))) * ‖asC z‖ := by
        rw [has_eq]; ring
    _ ≤ ((√2 * (√2 - 1) / 2 / κ ^ (3 / 2 : ℝ)) / ‖z‖ +
          (2 / √Real.pi / κ ^ (3 / 2 : ℝ)) / ‖z‖ +
          (√Real.pi * √2 / κ ^ (3 / 2 : ℝ)) / ‖z‖) * ‖asC z‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [mul_add, mul_add]
        exact add_le_add (add_le_add hpiece1 hpiece2) hpiece3
    _ = (C / ‖z‖) * ‖asC z‖ := by dsimp [C]; ring

/-- **Complex sector asymptotic of `I₀`** (`lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`),
proof of (c)): uniformly in every closed sector `|arg z| ≤ π/2 - ε` (`0 < ε < π/2`),
`I₀(z) = e^z / √(2πz) · (1 + O_ε(1/|z|))`. -/
theorem besselI0C_sector_asymptotic {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ Real.pi / 2 - ε →
      ‖besselI0C z - asC z‖ ≤ (C / ‖z‖) * ‖asC z‖ := by
  have hsin_pos : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε0 (by linarith [Real.pi_pos])
  obtain ⟨C, hC_nn, hbd⟩ := besselI0C_sector_asymptotic_of_re_pos hsin_pos
  refine ⟨C, hC_nn, fun z hz harg => ?_⟩
  have hcos_ge : Real.sin ε ≤ Real.cos z.arg := by
    have h1 : Real.cos (Real.pi / 2 - ε) ≤ Real.cos (|z.arg|) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) harg
    rwa [Real.cos_pi_div_two_sub, Real.cos_abs] at h1
  have hre_eq : z.re = ‖z‖ * Real.cos z.arg := by
    have := Complex.cos_arg hz
    rw [this]; field_simp [(norm_pos_iff.mpr hz).ne']
  have hsec : Real.sin ε * ‖z‖ ≤ z.re := by
    rw [hre_eq]
    nlinarith [norm_nonneg z]
  have hz_pos : 0 < z.re := lt_of_lt_of_le (mul_pos hsin_pos (norm_pos_iff.mpr hz)) hsec
  exact hbd z hz_pos hsec

/-- **Proof of `BesselI0Asymptotic`** (`Blowup/PotentialAndWeight.lean`): uniformly for
`Re z ≥ 2` and `|Im z| ≤ Re z`, `‖I₀(z) - as(z)‖ ≤ (C_I0 / ‖z‖) * ‖as(z)‖`. -/
theorem besselI0Asymptotic : BesselI0Asymptotic := by
  obtain ⟨C, hC_nn, hbd⟩ := besselI0C_sector_asymptotic_of_re_pos (κ := 1 / √2) (by positivity)
  refine ⟨C, hC_nn, fun z hz_re hz_im => ?_⟩
  have hz_pos : 0 < z.re := by linarith
  have hnorm_sq : ‖z‖ ^ 2 ≤ 2 * z.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have him : z.im ^ 2 ≤ z.re ^ 2 := by nlinarith [abs_le.mp hz_im]
    linarith
  have hsec : (1 / √2) * ‖z‖ ≤ z.re := by
    rw [one_div_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.mpr zero_lt_two)]
    have h1 := Real.sqrt_le_sqrt hnorm_sq
    rwa [Real.sqrt_sq (norm_nonneg z), Real.sqrt_mul zero_le_two,
      Real.sqrt_sq hz_pos.le, mul_comm] at h1
  exact hbd z hz_pos hsec

/-- **Unconditional Lemma T3** (`blowup_limit.tex`, Lemma `bl:T3`, first display):
uniform complex asymptotic for `V(c' b^2 / 3)` on `|b - ξ_*| ≤ 0.1`, `c' ≥ 39`. -/
theorem lemma_T3_unconditional :
    ∃ C_V : ℝ, 0 ≤ C_V ∧
      ∀ {c' : ℝ} {b : ℂ}, 39 ≤ c' → b ∈ closedBall (xiStar : ℂ) 0.1 →
        ∃ ε_V : ℂ,
          V_C (c' : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
            asC ((c' : ℂ) * tipL b) *
              ((1 - Complex.exp (-4 * (π : ℂ) * b)) ^ 2 + ε_V) ∧
          ‖ε_V‖ ≤ C_V / c' :=
  lemma_T3 besselI0Asymptotic

/-- **Unconditional Lemma T3 (rescaled weight)** (`blowup_limit.tex`, Lemma `bl:T3`, second display):
for `c' ≥ 39` and `ε |ζ| ≤ ρ₃`,
`W_C c' (bScale c' ζ) = κ_c e^{c' L(b)} (1 + O(ε (1 + |ζ|) + 1/c'))`. -/
theorem lemma_T3_W_bound_unconditional :
    ∃ ρ₃ C_W : ℝ, 0 < ρ₃ ∧ 0 ≤ C_W ∧
      ∀ {c' : ℝ} {ζ : ℂ}, 39 ≤ c' → tipEps c' * ‖ζ‖ ≤ ρ₃ →
        let b := bScale c' ζ
        ‖W_C c' b - (kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ ≤
          C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c') *
            ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ :=
  lemma_T3_W_bound besselI0Asymptotic

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.integration_besselI0C_eq_blowup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integration_besselI0C_eq_blowup

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.besselI0C_sector_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0C_sector_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.besselI0Asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0Asymptotic

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.lemma_T3_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T3_unconditional

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.lemma_T3_W_bound_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T3_W_bound_unconditional

end FormalResearch.ModularBootstrap.ComplexBessel

