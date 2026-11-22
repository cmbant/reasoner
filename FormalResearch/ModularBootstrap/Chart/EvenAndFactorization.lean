module

public import FormalResearch.ModularBootstrap.Chart.MidpointAndUpsilon
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Even Expansion of `b(ζ)` and Exact Factorization (Lemma F)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2 & §J6:
* Real-analyticity and even Taylor expansion `b(ζ) = bEven(ζ²)` near `0`:
  `b(ζ) - ξ_* = -(π/(4√2)) ζ² (1 + O(ζ²))` with real even Taylor coefficients (`Lemma S6`, part 1).
* First derivatives `deriv chartQ 0 = -√2/2` and `deriv chartOmega 0 = -√2 π ξ* / 3` (`Lemma S3`).
* Divided-difference bivariate series `diffSeries` and **Lemma F** (`vlo:F`, lines 580–590):
  Near `(w, s) = (0, 0)`,
  `2 log(b(w)/b(s)) · ω'(w) = (π²/6)(w² - s²)(1 + η(w, s))`
  with `η` jointly holomorphic in `(w, s)` (including at `w = ±s`) and `|η(w, s)| ≤ C(|w| + |s|)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Chart

/-! ### Section 1: Real-analytic reflection and iterated derivative helpers -/

lemma hasDerivAt_conj_conj_chart {f : ℂ → ℂ} {f' z : ℂ} (hf : HasDerivAt f f' z) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') (starRingEnd ℂ z) := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have hcomp : Tendsto (fun w : ℂ => starRingEnd ℂ w)
      (𝓝[≠] (starRingEnd ℂ z)) (𝓝[≠] z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun w : ℂ => starRingEnd ℂ w) := Complex.conjCLE.continuous
      simpa using (hcont.tendsto (starRingEnd ℂ z)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro hconj
      apply hw
      simpa using congrArg (starRingEnd ℂ) hconj
  have hcont_conj : Continuous (fun w : ℂ => starRingEnd ℂ w) := Complex.conjCLE.continuous
  have ht := (hcont_conj.tendsto _).comp (hf.comp hcomp)
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w _
  simp only [Function.comp_apply, slope_def_field]
  rw [map_div₀, map_sub, map_sub, Complex.conj_conj, Complex.conj_conj]

lemma conj_of_analyticOnNhd_real {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) r))
    (hreal : ∀ x : ℝ, |x| < r → (f (x : ℂ)).im = 0) :
    ∀ z ∈ ball (0 : ℂ) r, f (starRingEnd ℂ z) = starRingEnd ℂ (f z) := by
  let g : ℂ → ℂ := fun z => starRingEnd ℂ (f (starRingEnd ℂ z))
  have hg_an : AnalyticOnNhd ℂ g (ball (0 : ℂ) r) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    have hconj_mem : starRingEnd ℂ z ∈ ball (0 : ℂ) r := by simpa using hz
    have hd := (hf _ hconj_mem).differentiableAt.hasDerivAt
    simpa [g] using (hasDerivAt_conj_conj_chart hd).differentiableAt.differentiableWithinAt
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = f z := by
    have htend : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        exact ((Complex.continuous_ofReal.tendsto 0).comp h0).congr fun n => by simp
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    refine htend.frequently ?_
    refine (eventually_gt_atTop (Nat.ceil (1 / r) + 1)).frequently.mono fun n hn => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlt_r : |1 / ((n : ℝ) + 1)| < r := by
      rw [abs_of_pos (div_pos one_pos hpos)]
      have hceil : 1 / r ≤ (Nat.ceil (1 / r) : ℝ) := Nat.le_ceil (1 / r)
      have hn_real : (Nat.ceil (1 / r) : ℝ) + 1 < (n : ℝ) := by exact_mod_cast hn
      have hdiv : 1 / r < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hpos]
      rw [div_lt_iff₀ hr] at hdiv
      linarith
    have him := hreal _ hlt_r
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] at him
    simp only [g, Complex.conj_ofReal]
    exact Complex.ext rfl (by simp [him])
  have heqOn : EqOn g f (ball (0 : ℂ) r) :=
    hg_an.eqOn_of_preconnected_of_frequently_eq hf (convex_ball 0 r).isPreconnected
      (mem_ball_self hr) hfreq
  intro z hz
  have hgz := heqOn hz
  have hres := congrArg (starRingEnd ℂ) hgz
  simpa [g] using hres

lemma deriv_real_on_ball {f : ℂ → ℂ} {r : ℝ}
    (hreal : ∀ x : ℝ, |x| < r → (f (x : ℂ)).im = 0)
    (hd : ∀ x : ℝ, |x| < r → DifferentiableAt ℂ f (x : ℂ)) :
    ∀ x : ℝ, |x| < r → (deriv f (x : ℂ)).im = 0 := by
  intro x hx
  have hd_real : HasDerivAt (fun t : ℝ => f (t : ℂ)) (deriv f (x : ℂ)) x :=
    (hd x hx).hasDerivAt.comp_ofReal
  have him_zero : HasDerivAt (fun t : ℝ => (f (t : ℂ)).im) 0 x := by
    have hev : (fun t : ℝ => (f (t : ℂ)).im) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
      have hopen : IsOpen {t : ℝ | |t| < r} := isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds hx] with t ht
      exact hreal t ht
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  have him_d : HasDerivAt (fun t : ℝ => (f (t : ℂ)).im) (deriv f (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd_real
  exact him_d.unique him_zero

lemma iteratedDeriv_real_on_ball {r : ℝ} (n : ℕ) :
    ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f (ball (0 : ℂ) r) →
      (∀ x : ℝ, |x| < r → (f (x : ℂ)).im = 0) →
      ∀ x : ℝ, |x| < r → (iteratedDeriv n f (x : ℂ)).im = 0 := by
  induction n with
  | zero =>
    intro f _ hreal x hx; simpa using hreal x hx
  | succ n ih =>
    intro f hf hreal x hx
    rw [iteratedDeriv_succ']
    refine ih (deriv f) hf.deriv (deriv_real_on_ball hreal fun y hy => ?_) x hx
    exact (hf _ (by simpa [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hy)).differentiableAt

lemma log_div_of_re_pos_chart {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log (a / b) = Complex.log a - Complex.log b := by
  have ha_ne : a ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at ha; exact lt_irrefl 0 ha
  have hb_ne : b ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have ha_arg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hb_arg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
  have harg : (Complex.log a - Complex.log b).im ∈ Ioc (-Real.pi) Real.pi := by
    simp only [Complex.sub_im, Complex.log_im, Set.mem_Ioc]
    constructor <;> linarith [ha_arg.1, ha_arg.2, hb_arg.1, hb_arg.2]
  have hexp : Complex.exp (Complex.log a - Complex.log b) = a / b := by
    rw [Complex.exp_sub, Complex.exp_log ha_ne, Complex.exp_log hb_ne]
  rw [← hexp, Complex.log_exp harg.1 harg.2]

lemma norm_taylor_coeff_le_of_analyticOnNhd {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) r)) :
    ∃ M ≥ 0, ∀ n : ℕ, ‖(n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0‖ * (2 * r / 3) ^ n ≤ M := by
  let z₀ : ℂ := ((2 * r / 3 : ℝ) : ℂ)
  have hz₀_mem : z₀ ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hsum := Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hz₀_mem
  have hnorm_sum : Summable (fun n : ℕ => ‖(n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0‖ * (2 * r / 3) ^ n) := by
    have hnorm_z0 : ‖z₀‖ = 2 * r / 3 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * r / 3)]
    refine hsum.summable.norm.congr fun n => ?_
    rw [smul_eq_mul, smul_eq_mul, sub_zero, norm_mul, norm_mul, norm_pow, hnorm_z0,
      norm_mul]
    ring
  have htend : Tendsto (fun n : ℕ => ‖(n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0‖ * (2 * r / 3) ^ n)
      atTop (𝓝 0) := hnorm_sum.tendsto_atTop_zero
  obtain ⟨M, hM⟩ := htend.bddAbove_range
  refine ⟨max M 0, le_max_right _ _, fun n => (hM ⟨n, rfl⟩).trans (le_max_left _ _)⟩

/-! ### Section 2: Even expansion of `b(ζ)` and derivatives at `0` -/

lemma chartB_neg (ζ : ℂ) : chartB (-ζ) = chartB ζ := by
  unfold chartB
  rw [mul_neg, Complex.cos_neg]

lemma exists_ball_analyticOnNhd_chartB_zero :
    ∃ r > 0, AnalyticOnNhd ℂ chartB (ball (0 : ℂ) r) ∧ r ≤ 1 / 2 := by
  have han : AnalyticAt ℂ chartB 0 := analyticAt_chartB (le_refl 0) (by norm_num) (by norm_num)
  obtain ⟨r, hr_pos, hr_an⟩ := han.exists_ball_analyticOnNhd
  refine ⟨min r (1 / 2), lt_min hr_pos (by norm_num),
    hr_an.mono (ball_subset_ball (min_le_left _ _)), min_le_right _ _⟩

noncomputable def rB0 : ℝ := Classical.choose exists_ball_analyticOnNhd_chartB_zero

lemma rB0_pos : 0 < rB0 := (Classical.choose_spec exists_ball_analyticOnNhd_chartB_zero).1

lemma analyticOnNhd_chartB_rB0 : AnalyticOnNhd ℂ chartB (ball (0 : ℂ) rB0) :=
  (Classical.choose_spec exists_ball_analyticOnNhd_chartB_zero).2.1

lemma rB0_le_half : rB0 ≤ 1 / 2 := (Classical.choose_spec exists_ball_analyticOnNhd_chartB_zero).2.2

lemma chartB_ofReal_im_zero_ball {x : ℝ} (hx : |x| < rB0) : (chartB (x : ℂ)).im = 0 := by
  have hle : |x| ≤ 1 / 2 := hx.le.trans rB0_le_half
  by_cases hx0 : 0 ≤ x
  · rw [chartB_ofReal_Icc hx0 (abs_le.mp hle).2, Complex.ofReal_im]
  · have hneg : 0 ≤ -x := by linarith
    have hneg_le : -x ≤ 1 / 2 := (neg_le_abs x).trans hle
    have heq : chartB (x : ℂ) = chartB ((-x : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg, chartB_neg]
    rw [heq, chartB_ofReal_Icc hneg hneg_le, Complex.ofReal_im]

lemma iteratedDeriv_chartB_odd_zero {n : ℕ} (hn : Odd n) : iteratedDeriv n chartB 0 = 0 := by
  have hneg : iteratedDeriv n (fun z => chartB (-z)) 0 =
      (-1 : ℂ) ^ n * iteratedDeriv n chartB 0 := by
    simpa [neg_zero] using iteratedDeriv_comp_neg n chartB (0 : ℂ)
  have heq : (fun z => chartB (-z)) = chartB := funext chartB_neg
  rw [heq, hn.neg_one_pow] at hneg
  have h2 : (2 : ℂ) * iteratedDeriv n chartB 0 = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

lemma deriv_chartB_zero : deriv chartB 0 = 0 := by
  rw [← iteratedDeriv_one]
  exact iteratedDeriv_chartB_odd_zero odd_one

lemma iteratedDeriv_chartB_im_zero (n : ℕ) : (iteratedDeriv n chartB 0).im = 0 :=
  iteratedDeriv_real_on_ball n chartB analyticOnNhd_chartB_rB0
    (fun _ hx => chartB_ofReal_im_zero_ball hx) 0 (by simpa using rB0_pos)

lemma iteratedDeriv_two_chartB_zero :
    iteratedDeriv 2 chartB 0 = -(((Real.pi / (2 * √2) : ℝ) : ℂ)) := by
  have h_id : ∀ ζ : ℂ, Complex.sinh ((Real.pi : ℂ) * chartB ζ) ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := by
    intro ζ
    rw [sinh_pi_chartB, cpow_half_sq]
  have hd_B : AnalyticOnNhd ℂ chartB (ball (0 : ℂ) rB0) := analyticOnNhd_chartB_rB0
  have hd1_eq : ∀ ζ ∈ ball (0 : ℂ) rB0,
      2 * (Real.pi : ℂ) * Complex.sinh ((Real.pi : ℂ) * chartB ζ) *
        Complex.cosh ((Real.pi : ℂ) * chartB ζ) * deriv chartB ζ =
      -((Real.pi : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ)) := by
    intro ζ hζ
    have hb_d : HasDerivAt chartB (deriv chartB ζ) ζ :=
      (hd_B ζ hζ).differentiableAt.hasDerivAt
    have hpi_d : HasDerivAt (fun z => (Real.pi : ℂ) * chartB z) ((Real.pi : ℂ) * deriv chartB ζ) ζ :=
      hb_d.const_mul _
    have hsinh_d : HasDerivAt (fun z => Complex.sinh ((Real.pi : ℂ) * chartB z))
        (Complex.cosh ((Real.pi : ℂ) * chartB ζ) * ((Real.pi : ℂ) * deriv chartB ζ)) ζ :=
      (Complex.hasDerivAt_sinh _).comp ζ hpi_d
    have hlhs : HasDerivAt (fun z => Complex.sinh ((Real.pi : ℂ) * chartB z) ^ 2)
        (2 * Complex.sinh ((Real.pi : ℂ) * chartB ζ) ^ (2 - 1) *
          (Complex.cosh ((Real.pi : ℂ) * chartB ζ) * ((Real.pi : ℂ) * deriv chartB ζ))) ζ :=
      hsinh_d.pow 2
    have hrhs : HasDerivAt (fun z => Complex.cos ((Real.pi : ℂ) * z))
        (-Complex.sin ((Real.pi : ℂ) * ζ) * (Real.pi : ℂ)) ζ := by
      have hm : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) ζ := by
        simpa using (hasDerivAt_id ζ).const_mul (Real.pi : ℂ)
      exact (Complex.hasDerivAt_cos _).comp ζ hm
    have heq_f : (fun z => Complex.sinh ((Real.pi : ℂ) * chartB z) ^ 2) =
        (fun z => Complex.cos ((Real.pi : ℂ) * z)) := funext h_id
    rw [heq_f] at hlhs
    have hu := hlhs.unique hrhs
    linear_combination hu
  let F : ℂ → ℂ := fun ζ =>
    2 * (Real.pi : ℂ) * Complex.sinh ((Real.pi : ℂ) * chartB ζ) *
      Complex.cosh ((Real.pi : ℂ) * chartB ζ)
  have hF_d : DifferentiableAt ℂ F 0 := by
    have hb0 : AnalyticAt ℂ chartB 0 := hd_B 0 (mem_ball_self rB0_pos)
    have h1 : AnalyticAt ℂ (fun ζ => Complex.sinh ((Real.pi : ℂ) * chartB ζ)) 0 := by fun_prop
    have h2 : AnalyticAt ℂ (fun ζ => Complex.cosh ((Real.pi : ℂ) * chartB ζ)) 0 := by fun_prop
    exact ((analyticAt_const.mul h1).mul h2).differentiableAt
  have hd_dB : HasDerivAt (deriv chartB) (iteratedDeriv 2 chartB 0) 0 := by
    have hd_an : AnalyticAt ℂ (deriv chartB) 0 := hd_B.deriv 0 (mem_ball_self rB0_pos)
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd_an.differentiableAt.hasDerivAt
  have hlhs2 : HasDerivAt (fun ζ => F ζ * deriv chartB ζ)
      (F 0 * iteratedDeriv 2 chartB 0) 0 := by
    have hmul := hF_d.hasDerivAt.mul hd_dB
    rw [deriv_chartB_zero, mul_zero, zero_add] at hmul
    exact hmul
  have hrhs2 : HasDerivAt (fun ζ => -((Real.pi : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ)))
      (-((Real.pi : ℂ) ^ 2 * Complex.cos 0)) 0 := by
    have hm : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)
    have hsin := (((Complex.hasDerivAt_sin _).comp (0 : ℂ) hm).const_mul (Real.pi : ℂ)).neg
    refine hsin.congr_deriv ?_
    simp only [mul_zero]
    ring
  have hev : (fun ζ => -((Real.pi : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ))) =ᶠ[𝓝 (0 : ℂ)]
      (fun ζ => F ζ * deriv chartB ζ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) rB0_pos] with ζ hζ
    exact (hd1_eq ζ hζ).symm
  have hu2 := (hlhs2.congr_of_eventuallyEq hev).unique hrhs2
  have hsinh0 : Complex.sinh ((Real.pi : ℂ) * chartB 0) = 1 := by
    rw [chartB_zero, ← Complex.ofReal_mul, ← Complex.ofReal_sinh, sinh_pi_mul_xiStar, Complex.ofReal_one]
  have hcosh0 : Complex.cosh ((Real.pi : ℂ) * chartB 0) = (√2 : ℂ) := by
    rw [chartB_zero, ← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    congr 1
    have hsq : Real.cosh (Real.pi * xiStar) ^ 2 = 2 := by
      have hch := Real.cosh_sq_sub_sinh_sq (Real.pi * xiStar)
      rw [sinh_pi_mul_xiStar] at hch
      linarith
    have hpos : 0 < Real.cosh (Real.pi * xiStar) := Real.cosh_pos _
    rw [← Real.sqrt_sq hpos.le, hsq]
  have hF0 : F 0 = 2 * (Real.pi : ℂ) * (√2 : ℂ) := by
    dsimp [F]
    rw [hsinh0, hcosh0]
    ring
  rw [hF0, Complex.cos_zero, mul_one] at hu2
  have hu2' : iteratedDeriv 2 chartB 0 = -((Real.pi : ℂ) ^ 2) / (2 * (Real.pi : ℂ) * (√2 : ℂ)) :=
    eq_div_of_mul_eq (by
      refine mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ?_
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne')
      (by linear_combination hu2)
  rw [hu2']
  push_cast
  field_simp [Real.pi_pos.ne']

noncomputable def bEvenCoeff (k : ℕ) : ℂ :=
  (((2 * k).factorial : ℝ)⁻¹ : ℂ) * iteratedDeriv (2 * k) chartB 0

lemma bEvenCoeff_im_zero (k : ℕ) : (bEvenCoeff k).im = 0 := by
  unfold bEvenCoeff
  rw [Complex.mul_im, show ((((2 * k).factorial : ℝ)⁻¹ : ℂ)).im = 0 by
    rw [← Complex.ofReal_inv, Complex.ofReal_im], iteratedDeriv_chartB_im_zero, zero_mul, mul_zero,
    add_zero]

noncomputable def bEvenSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ bEvenCoeff

noncomputable def bEven (w : ℂ) : ℂ := bEvenSeries.sum w

noncomputable def rBEven : ℝ := (rB0 / 2) ^ 2

lemma rBEven_pos : 0 < rBEven := by
  unfold rBEven
  have := rB0_pos
  positivity

lemma summable_bEvenCoeff : Summable (fun k : ℕ => ‖bEvenCoeff k‖ * rBEven ^ k) := by
  obtain ⟨M, hM0, hM⟩ := norm_taylor_coeff_le_of_analyticOnNhd rB0_pos analyticOnNhd_chartB_rB0
  have hle : ∀ k : ℕ, ‖bEvenCoeff k‖ * rBEven ^ k ≤ M * (9 / 16 : ℝ) ^ k := by
    intro k
    have hk := hM (2 * k)
    have hcoeff : ‖bEvenCoeff k‖ =
        ‖((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) chartB 0‖ := by
      unfold bEvenCoeff; push_cast; rfl
    have hpow : rBEven ^ k = (rB0 / 2) ^ (2 * k) := by
      unfold rBEven; rw [pow_mul]
    have hratio : (rB0 / 2) ^ (2 * k) = (3 / 4 : ℝ) ^ (2 * k) * (2 * rB0 / 3) ^ (2 * k) := by
      rw [← mul_pow]; congr 1; field_simp [rB0_pos.ne']; ring
    have h916 : (3 / 4 : ℝ) ^ (2 * k) = (9 / 16 : ℝ) ^ k := by
      rw [pow_mul]; norm_num
    rw [hcoeff, hpow, hratio, h916]
    calc ‖((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) chartB 0‖ *
          ((9 / 16 : ℝ) ^ k * (2 * rB0 / 3) ^ (2 * k))
        = (‖((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) chartB 0‖ * (2 * rB0 / 3) ^ (2 * k)) *
            (9 / 16 : ℝ) ^ k := by ring
      _ ≤ M * (9 / 16 : ℝ) ^ k := mul_le_mul_of_nonneg_right hk (by positivity)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg rBEven_pos.le k)) hle ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M

lemma rBEven_le_radius : ENNReal.ofReal rBEven ≤ bEvenSeries.radius := by
  let r_nn : NNReal := ⟨rBEven, rBEven_pos.le⟩
  have hs : Summable (fun n : ℕ => ‖bEvenSeries n‖ * (r_nn : ℝ) ^ n) := by
    refine summable_bEvenCoeff.congr fun n => ?_
    change ‖bEvenCoeff n‖ * rBEven ^ n = ‖FormalMultilinearSeries.ofScalars ℂ bEvenCoeff n‖ * rBEven ^ n
    rw [FormalMultilinearSeries.ofScalars_norm]
  have hle := bEvenSeries.le_radius_of_summable_norm hs
  calc ENNReal.ofReal rBEven = ENNReal.ofReal (r_nn : ℝ) := rfl
    _ = (r_nn : ENNReal) := ENNReal.ofReal_coe_nnreal
    _ ≤ bEvenSeries.radius := hle

lemma analyticOnNhd_bEven : AnalyticOnNhd ℂ bEven (ball (0 : ℂ) rBEven) := by
  have hsub : ball (0 : ℂ) rBEven ⊆ Metric.eball (0 : ℂ) bEvenSeries.radius := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ((ENNReal.ofReal_lt_ofReal_iff rBEven_pos).mpr hw).trans_le rBEven_le_radius
  exact bEvenSeries.analyticOnNhd.mono hsub

lemma bEven_sq_eq_chartB {ζ : ℂ} (hζ : ‖ζ‖ < rB0 / 2) : bEven (ζ ^ 2) = chartB ζ := by
  have hζ_mem : ζ ∈ ball (0 : ℂ) rB0 := by
    rw [mem_ball_zero_iff]; linarith [rB0_pos]
  have htaylor := Complex.taylorSeries_eq_on_ball' hζ_mem analyticOnNhd_chartB_rB0.differentiableOn
  simp only [sub_zero] at htaylor
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun k : ℕ => 2 * k) →
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n chartB 0 * ζ ^ n = 0 := by
    intro n hn
    have hodd : Odd n := by
      rw [← Nat.not_even_iff_odd]
      intro ⟨k, hk⟩
      exact hn ⟨k, by dsimp; linarith⟩
    rw [iteratedDeriv_chartB_odd_zero hodd, mul_zero, zero_mul]
  have heven_sum :
      (∑' k : ℕ, (((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) chartB 0 * ζ ^ (2 * k))) =
        ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n chartB 0 * ζ ^ n := by
    refine Function.Injective.tsum_eq
      (f := fun n : ℕ => (n.factorial : ℂ)⁻¹ * iteratedDeriv n chartB 0 * ζ ^ n)
      (g := fun k : ℕ => 2 * k) (fun _ _ h => by linarith) ?_
    intro n hn
    by_contra hnr
    exact hn (hzero n hnr)
  have hb_eq : bEven (ζ ^ 2) =
      ∑' k : ℕ, (((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) chartB 0 * ζ ^ (2 * k)) := by
    unfold bEven bEvenSeries FormalMultilinearSeries.sum
    refine tsum_congr fun k => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, bEvenCoeff, ← pow_mul]
    push_cast; ring
  rw [hb_eq, heven_sum, htaylor]

lemma bEven_zero : bEven 0 = (xiStar : ℂ) := by
  have h := bEven_sq_eq_chartB (ζ := 0) (by simpa using half_pos rB0_pos)
  simpa [chartB_zero] using h

lemma deriv_bEven_zero : deriv bEven 0 = -(((Real.pi / (4 * √2) : ℝ) : ℂ)) := by
  have hr : 0 < rB0 / 2 := half_pos rB0_pos
  have hsq_mem : ∀ ζ ∈ ball (0 : ℂ) (rB0 / 2), ζ ^ 2 ∈ ball (0 : ℂ) rBEven := by
    intro ζ hζ
    rw [mem_ball_zero_iff, norm_pow]
    rw [mem_ball_zero_iff] at hζ
    unfold rBEven
    nlinarith [norm_nonneg ζ]
  have hd1 : ∀ ζ ∈ ball (0 : ℂ) (rB0 / 2),
      deriv chartB ζ = deriv bEven (ζ ^ 2) * (2 * ζ) := by
    intro ζ hζ
    have hb_d : HasDerivAt bEven (deriv bEven (ζ ^ 2)) (ζ ^ 2) :=
      (analyticOnNhd_bEven (ζ ^ 2) (hsq_mem ζ hζ)).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun w : ℂ => bEven (w ^ 2)) (deriv bEven (ζ ^ 2) * (2 * ζ)) ζ := by
      have hsq_d : HasDerivAt (fun w : ℂ => w ^ 2) (2 * ζ) ζ := by
        simpa using hasDerivAt_pow 2 ζ
      change HasDerivAt (bEven ∘ fun w : ℂ => w ^ 2) (deriv bEven (ζ ^ 2) * (2 * ζ)) ζ
      exact hb_d.comp (h := fun w : ℂ => w ^ 2) ζ hsq_d
    have hev : chartB =ᶠ[𝓝 ζ] (fun w : ℂ => bEven (w ^ 2)) := by
      filter_upwards [(isOpen_ball (x := (0 : ℂ)) (ε := rB0 / 2)).mem_nhds hζ] with w hw
      exact (bEven_sq_eq_chartB (mem_ball_zero_iff.mp hw)).symm
    exact (hcomp.congr_of_eventuallyEq hev).deriv
  have hd_dB : HasDerivAt (deriv chartB) (iteratedDeriv 2 chartB 0) 0 := by
    have hd_an : AnalyticAt ℂ (deriv chartB) 0 :=
      analyticOnNhd_chartB_rB0.deriv 0 (mem_ball_self rB0_pos)
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd_an.differentiableAt.hasDerivAt
  have hd_prod : HasDerivAt (fun ζ : ℂ => deriv bEven (ζ ^ 2) * (2 * ζ))
      (deriv bEven 0 * 2) 0 := by
    have hdb_an : AnalyticAt ℂ (fun ζ : ℂ => deriv bEven (ζ ^ 2)) 0 := by
      have h0 : (0 : ℂ) ^ 2 ∈ ball (0 : ℂ) rBEven := by simpa using rBEven_pos
      have hd_bEven : AnalyticAt ℂ (deriv bEven) ((0 : ℂ) ^ 2) :=
        analyticOnNhd_bEven.deriv _ h0
      have hsq_an : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ 2) 0 := by fun_prop
      exact AnalyticAt.comp (f := fun ζ : ℂ => ζ ^ 2) hd_bEven hsq_an
    have h2z : HasDerivAt (fun ζ : ℂ => (2 : ℂ) * ζ) 2 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul 2
    have hm := hdb_an.differentiableAt.hasDerivAt.fun_mul h2z
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] using hm
  have hev : deriv chartB =ᶠ[𝓝 (0 : ℂ)] (fun ζ : ℂ => deriv bEven (ζ ^ 2) * (2 * ζ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with ζ hζ
    exact hd1 ζ hζ
  have hu := (hd_prod.congr_of_eventuallyEq hev).unique hd_dB
  rw [iteratedDeriv_two_chartB_zero] at hu
  push_cast at hu ⊢
  linear_combination (hu / 2)

lemma bEven_ofReal_im_zero {x : ℝ} (hx : |x| < rBEven) : (bEven (x : ℂ)).im = 0 := by
  have hx_eb : (x : ℂ) ∈ Metric.eball (0 : ℂ) bEvenSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    exact ((ENNReal.ofReal_lt_ofReal_iff rBEven_pos).mpr hx).trans_le rBEven_le_radius
  have hsum := bEvenSeries.hasSum hx_eb
  have him_sum : HasSum (fun k : ℕ => (bEvenSeries k (fun _ => (x : ℂ))).im) (bEven (x : ℂ)).im :=
    Complex.imCLM.hasSum hsum
  have hzero : ∀ k : ℕ, (bEvenSeries k (fun _ => (x : ℂ))).im = 0 := by
    intro k
    change (FormalMultilinearSeries.ofScalars ℂ bEvenCoeff k (fun _ => (x : ℂ))).im = 0
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      show (x : ℂ) ^ k = ((x ^ k : ℝ) : ℂ) by push_cast; rfl, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, bEvenCoeff_im_zero, zero_mul, mul_zero, add_zero]
  simp only [hzero] at him_sum
  exact (him_sum.unique hasSum_zero)

lemma bEven_conj {w : ℂ} (hw : w ∈ ball (0 : ℂ) rBEven) :
    bEven (starRingEnd ℂ w) = starRingEnd ℂ (bEven w) :=
  conj_of_analyticOnNhd_real rBEven_pos analyticOnNhd_bEven (fun _ hx => bEven_ofReal_im_zero hx) w hw

lemma iteratedDeriv_bEven_im_zero (k : ℕ) : (iteratedDeriv k bEven 0).im = 0 :=
  iteratedDeriv_real_on_ball k bEven analyticOnNhd_bEven
    (fun _ hx => bEven_ofReal_im_zero hx) 0 (by simpa using rBEven_pos)

lemma chartB_even_expansion :
    ∃ r > 0, ∃ C ≥ 0,
      r ≤ rB0 / 2 ∧ r ^ 2 ≤ rBEven ∧
      (∀ k : ℕ, (iteratedDeriv k bEven 0).im = 0) ∧
      (∀ ζ ∈ ball (0 : ℂ) r, chartB ζ = bEven (ζ ^ 2) ∧
        ‖chartB ζ - (xiStar : ℂ) - (-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * ζ ^ 2‖ ≤
          C * ‖ζ‖ ^ 4) := by
  let g2 : ℂ → ℂ := dslope (dslope bEven 0) 0
  have hg2_an : AnalyticOnNhd ℂ g2 (ball (0 : ℂ) rBEven) := by
    have hd1 : DifferentiableOn ℂ (dslope bEven 0) (ball (0 : ℂ) rBEven) :=
      (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self rBEven_pos))).mpr
        analyticOnNhd_bEven.differentiableOn
    have hd2 : DifferentiableOn ℂ g2 (ball (0 : ℂ) rBEven) :=
      (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self rBEven_pos))).mpr hd1
    exact hd2.analyticOnNhd isOpen_ball
  let r1 : ℝ := rB0 / 4
  have hr1_pos : 0 < r1 := by dsimp [r1]; linarith [rB0_pos]
  have hr1_sq_lt : r1 ^ 2 < rBEven := by
    dsimp [r1, rBEven]; nlinarith [rB0_pos]
  have hcl_sub : closedBall (0 : ℂ) (r1 ^ 2) ⊆ ball (0 : ℂ) rBEven :=
    closedBall_subset_ball hr1_sq_lt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (r1 ^ 2)).exists_bound_of_continuousOn
    (hg2_an.continuousOn.mono hcl_sub)
  refine ⟨r1, hr1_pos, max M 0, le_max_right _ _, by dsimp [r1]; linarith [rB0_pos], hr1_sq_lt.le,
    iteratedDeriv_bEven_im_zero, fun ζ hζ => ?_⟩
  have hζ_norm : ‖ζ‖ < rB0 / 2 := by
    rw [mem_ball_zero_iff] at hζ; dsimp [r1] at hζ; linarith [rB0_pos]
  have hsq_mem : ζ ^ 2 ∈ closedBall (0 : ℂ) (r1 ^ 2) := by
    rw [mem_closedBall_zero_iff, norm_pow]
    rw [mem_ball_zero_iff] at hζ
    nlinarith [norm_nonneg ζ]
  have hb_eq := bEven_sq_eq_chartB hζ_norm
  have h1 : (ζ ^ 2) • dslope bEven 0 (ζ ^ 2) = bEven (ζ ^ 2) - bEven 0 := by
    simpa [sub_zero] using sub_smul_dslope bEven (0 : ℂ) (ζ ^ 2)
  have h2 : (ζ ^ 2) • g2 (ζ ^ 2) = dslope bEven 0 (ζ ^ 2) - deriv bEven 0 := by
    have h0 := sub_smul_dslope (dslope bEven 0) (0 : ℂ) (ζ ^ 2)
    simpa [g2, dslope_same, sub_zero] using h0
  have hrem : chartB ζ - (xiStar : ℂ) - (-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * ζ ^ 2 =
      (ζ ^ 2) ^ 2 * g2 (ζ ^ 2) := by
    rw [← hb_eq, ← bEven_zero, ← deriv_bEven_zero]
    rw [smul_eq_mul] at h1 h2
    calc bEven (ζ ^ 2) - bEven 0 - deriv bEven 0 * ζ ^ 2
        = (ζ ^ 2 * dslope bEven 0 (ζ ^ 2)) - deriv bEven 0 * ζ ^ 2 := by rw [← h1]
      _ = ζ ^ 2 * (dslope bEven 0 (ζ ^ 2) - deriv bEven 0) := by ring
      _ = ζ ^ 2 * (ζ ^ 2 * g2 (ζ ^ 2)) := by rw [← h2]
      _ = (ζ ^ 2) ^ 2 * g2 (ζ ^ 2) := by ring
  refine ⟨hb_eq.symm, ?_⟩
  rw [hrem, norm_mul, norm_pow, norm_pow]
  have hMg : ‖g2 (ζ ^ 2)‖ ≤ max M 0 := (hM (ζ ^ 2) hsq_mem).trans (le_max_left _ _)
  calc (‖ζ‖ ^ 2) ^ 2 * ‖g2 (ζ ^ 2)‖
      = ‖g2 (ζ ^ 2)‖ * ‖ζ‖ ^ 4 := by ring
    _ ≤ max M 0 * ‖ζ‖ ^ 4 := by gcongr

lemma deriv_chartQ_zero : deriv chartQ 0 = -(((√2 / 2 : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := arccos_sin_inner_slitPlane
    (by norm_num : (0 : ℝ) ≤ (0 : ℂ).re) (by norm_num : (0 : ℂ).re ≤ 1 / 2)
    (by norm_num : (0 : ℂ) ≠ 1 / 2)
  have harc := hasDerivAt_arccosC h1 h2
  have hz_d : HasDerivAt (fun z : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2))
      ((√2 : ℂ) * (Complex.cos 0 * ((Real.pi : ℂ) / 2))) 0 := by
    have hm : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z / 2) ((Real.pi : ℂ) / 2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const 2
    have hsin0 : HasDerivAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z / 2))
        (Complex.cos ((Real.pi : ℂ) * 0 / 2) * ((Real.pi : ℂ) / 2)) 0 := by
      change HasDerivAt (Complex.sin ∘ fun z : ℂ => (Real.pi : ℂ) * z / 2) _ 0
      exact (Complex.hasDerivAt_sin _).comp 0 hm
    have hsin := hsin0.const_mul (√2 : ℂ)
    simpa only [mul_zero, zero_div] using hsin
  have hcomp : HasDerivAt
      (fun z : ℂ => (Real.pi : ℂ)⁻¹ * arccosC ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)))
      ((Real.pi : ℂ)⁻¹ * (-((1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * 0 / 2)) ^ 2) ^ (-(1 / 2 : ℂ))) *
        ((√2 : ℂ) * (Complex.cos 0 * ((Real.pi : ℂ) / 2))))) 0 := by
    have harc_c : HasDerivAt (fun z : ℂ => arccosC ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)))
        (-((1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * 0 / 2)) ^ 2) ^ (-(1 / 2 : ℂ))) *
          ((√2 : ℂ) * (Complex.cos 0 * ((Real.pi : ℂ) / 2)))) 0 := by
      change HasDerivAt (arccosC ∘ fun z : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)) _ 0
      exact harc.comp 0 hz_d
    exact harc_c.const_mul (Real.pi : ℂ)⁻¹
  change HasDerivAt chartQ _ 0 at hcomp
  rw [hcomp.deriv]
  simp only [mul_zero, zero_div, Complex.sin_zero, Complex.cos_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Complex.one_cpow]
  push_cast
  field_simp [Real.pi_pos.ne']

lemma deriv_chartOmega_zero :
    deriv chartOmega 0 = -(((Real.pi * √2 * xiStar / 3 : ℝ) : ℂ)) := by
  have hev : chartOmega =ᶠ[𝓝 (0 : ℂ)] chartOmegaHalf := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
    rw [mem_ball_zero_iff] at hz
    have hre : z.re ≤ 1 / 2 := le_trans (Complex.re_le_norm z) hz.le
    unfold chartOmega
    simp only [hre, ↓reduceIte]
  have hanB : AnalyticAt ℂ chartB 0 := analyticAt_chartB (le_refl 0) (by norm_num) (by norm_num)
  have hanQ : AnalyticAt ℂ chartQ 0 := analyticAt_chartQ (le_refl 0) (by norm_num) (by norm_num)
  have hprod : HasDerivAt chartOmegaHalf
      ((2 * (Real.pi : ℂ) / 3) * (deriv chartB 0 * chartQ 0 + chartB 0 * deriv chartQ 0)) 0 := by
    have h_eq : chartOmegaHalf = fun y : ℂ => (2 * (Real.pi : ℂ) / 3) * (chartB y * chartQ y) := by
      ext y; unfold chartOmegaHalf; ring
    rw [h_eq]
    have hmul := hanB.differentiableAt.hasDerivAt.fun_mul hanQ.differentiableAt.hasDerivAt
    exact (hmul.const_mul (2 * (Real.pi : ℂ) / 3))
  rw [hev.deriv_eq, hprod.deriv, deriv_chartB_zero, chartQ_zero, chartB_zero, deriv_chartQ_zero]
  push_cast
  ring

/-! ### Section 3: Divided-difference power series and Lemma F (`vlo:F`) -/

private noncomputable def diffProj (j n : ℕ) (i : Fin n) : (ℂ × ℂ) →L[ℂ] ℂ :=
  if (i : ℕ) < j then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ

private noncomputable def diffSeriesTerm (c : ℕ → ℂ) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × ℂ) ℂ :=
  c (n + 1) • ∑ j ∈ Finset.range (n + 1),
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (diffProj j n)

private noncomputable def diffSeries (c : ℕ → ℂ) : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ :=
  diffSeriesTerm c

private lemma diffProj_prod_apply {j n : ℕ} (hj : j ≤ n) (u v : ℂ) :
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (diffProj j n)
      (fun _ => (u, v)) = u ^ j * v ^ (n - j) := by
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  have hterm : (fun i : Fin n => diffProj j n i (u, v)) =
      fun i : Fin n => if (i : ℕ) < j then u else v := by
    ext i; dsimp [diffProj]; split_ifs <;> rfl
  rw [hterm, Finset.prod_ite]
  have heq_j : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).card = j := by
    have hbij : Finset.univ.filter (fun i : Fin n => (i : ℕ) < j) =
        Finset.map ⟨fun k : Fin j => ⟨(k : ℕ), lt_of_lt_of_le k.isLt hj⟩,
          fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩ Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨fun hi => ⟨⟨i.val, hi⟩, Fin.ext rfl⟩, fun ⟨k, hk⟩ => by rw [← hk]; exact k.isLt⟩
    rw [hbij, Finset.card_map, Finset.card_fin]
  have heq_nj : (Finset.univ.filter (fun i : Fin n => ¬ ((i : ℕ) < j))).card = n - j := by
    have hcompl : Finset.univ.filter (fun i : Fin n => ¬ ((i : ℕ) < j)) =
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j))ᶜ := by
      ext i; simp
    rw [hcompl, Finset.card_compl, Fintype.card_fin, heq_j]
  rw [Finset.prod_const, Finset.prod_const, heq_j, heq_nj]

private lemma diffSeries_apply_eq (c : ℕ → ℂ) (n : ℕ) (u v : ℂ) :
    diffSeries c n (fun _ => (u, v)) =
      c (n + 1) * ∑ j ∈ Finset.range (n + 1), u ^ j * v ^ (n - j) := by
  change (diffSeriesTerm c n) (fun _ => (u, v)) = _
  unfold diffSeriesTerm
  rw [smul_apply, sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  exact diffProj_prod_apply (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) u v

private lemma norm_diffSeries_le (c : ℕ → ℂ) (n : ℕ) :
    ‖diffSeries c n‖ ≤ ‖c (n + 1)‖ * ((n : ℝ) + 1) := by
  change ‖diffSeriesTerm c n‖ ≤ _
  unfold diffSeriesTerm
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hsum := norm_sum_le (Finset.range (n + 1)) (fun j =>
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (diffProj j n))
  refine hsum.trans ?_
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (diffProj j n)‖ ≤ 1 := by
    intro j _
    refine ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).norm_compContinuousLinearMap_le
      (diffProj j n)).trans ?_
    have hmk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖ ≤ 1 := by
      have hle := ContinuousMultilinearMap.norm_mkPiAlgebraFin_le (𝕜 := ℂ) (A := ℂ) (n := n)
      rwa [norm_one, max_self] at hle
    have hprod : ∏ i : Fin n, ‖diffProj j n i‖ ≤ 1 := by
      have hind := Finset.prod_induction (fun p : ℝ => 0 ≤ p ∧ p ≤ 1)
        (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, by nlinarith⟩)
        ⟨zero_le_one, le_rfl⟩ (s := Finset.univ) (f := fun i : Fin n => ‖diffProj j n i‖)
        (fun i _ => ⟨norm_nonneg _, by
          dsimp [diffProj]
          split_ifs
          · exact ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ
          · exact ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ⟩)
      exact hind.2
    calc ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖ * ∏ i : Fin n, ‖diffProj j n i‖
        ≤ 1 * 1 := mul_le_mul hmk hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  calc ∑ j ∈ Finset.range (n + 1),
        ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap (diffProj j n)‖
      ≤ ∑ _j ∈ Finset.range (n + 1), (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) := by simp

private lemma sub_mul_sum_pow (u v : ℂ) (n : ℕ) :
    (u - v) * ∑ j ∈ Finset.range (n + 1), u ^ j * v ^ (n - j) = u ^ (n + 1) - v ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hcongr : ∑ j ∈ Finset.range (n + 1), u ^ j * v ^ (n + 1 - j) =
        v * ∑ j ∈ Finset.range (n + 1), u ^ j * v ^ (n - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Nat.sub_add_comm hle, pow_succ']
      ring
    rw [hcongr, mul_add, mul_left_comm, ih]
    ring

private lemma summable_nat_add_one_mul_three_fourths :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n) := by
  have hbern : ∀ n : ℕ, ((n : ℝ) + 1) ≤ 6 * (7 / 6 : ℝ) ^ n := by
    intro n
    have hb := one_add_mul_le_pow (show -(2 : ℝ) ≤ 1 / 6 by norm_num) n
    rw [show (1 + 1 / 6 : ℝ) = 7 / 6 by norm_num] at hb
    linarith
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one (by positivity) (by norm_num : (7 / 8 : ℝ) < 1)).mul_left 6)
  calc ((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n
      ≤ (6 * (7 / 6 : ℝ) ^ n) * (3 / 4 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (hbern n) (by positivity)
    _ = 6 * ((7 / 6 : ℝ) ^ n * (3 / 4 : ℝ) ^ n) := by ring
    _ = 6 * ((7 / 6 : ℝ) * (3 / 4 : ℝ)) ^ n := by rw [← mul_pow]
    _ = 6 * (7 / 8 : ℝ) ^ n := by norm_num

/-- **Lemma F (`vlo:F`, `lower_o1_two_edge.tex`, lines 580–590)**:
Near `(w, s) = (0, 0)`,
`2 log(b(w)/b(s)) · ω'(w) = (π²/6)(w² - s²)(1 + η(w, s))`,
with `η` jointly holomorphic in `(w, s)` (including at `w = ±s`) and `|η(w, s)| ≤ C(|w| + |s|)`. -/
theorem lemma_F :
    ∃ η : ℂ → ℂ → ℂ, ∃ ρ > 0, ∃ C ≥ 0,
      AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ) ∧
      (∀ w ∈ ball (0 : ℂ) ρ, ∀ s ∈ ball (0 : ℂ) ρ,
        AnalyticAt ℂ (fun w' => η w' s) w ∧ AnalyticAt ℂ (fun s' => η w s') s) ∧
      (∀ w ∈ ball (0 : ℂ) ρ, ∀ s ∈ ball (0 : ℂ) ρ,
        2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
          ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s)) ∧
      (∀ w ∈ ball (0 : ℂ) ρ, ∀ s ∈ ball (0 : ℂ) ρ,
        ‖η w s‖ ≤ C * (‖w‖ + ‖s‖)) := by
  have hre_pos_ev : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) rBEven ∧ 0 < (bEven z).re := by
    refine Filter.Eventually.and (Metric.ball_mem_nhds 0 rBEven_pos) ?_
    have hc : ContinuousAt (fun z => (bEven z).re) 0 :=
      Complex.continuous_re.continuousAt.comp
        (analyticOnNhd_bEven 0 (mem_ball_self rBEven_pos)).continuousAt
    rw [ContinuousAt] at hc
    rw [show (bEven 0).re = xiStar by rw [bEven_zero, Complex.ofReal_re]] at hc
    exact hc (Ioi_mem_nhds xiStar_pos)
  obtain ⟨rH, hrH_pos, hrH⟩ := Metric.eventually_nhds_iff_ball.mp hre_pos_ev
  let hLog : ℂ → ℂ := fun z => Complex.log (bEven z)
  have hhLog_an : AnalyticOnNhd ℂ hLog (ball (0 : ℂ) rH) := fun z hz => by
    have hre : 0 < (bEven z).re := (hrH z hz).2
    have hb_an : AnalyticAt ℂ bEven z := analyticOnNhd_bEven z (hrH z hz).1
    exact hb_an.clog (Complex.mem_slitPlane_iff.mpr (Or.inl hre))
  have hhLog_deriv0 : deriv hLog 0 = -(((Real.pi / (4 * √2 * xiStar) : ℝ) : ℂ)) := by
    have hb_d : HasDerivAt bEven (deriv bEven 0) 0 :=
      (analyticOnNhd_bEven 0 (mem_ball_self rBEven_pos)).differentiableAt.hasDerivAt
    have hslit : bEven 0 ∈ Complex.slitPlane := by
      rw [bEven_zero]; exact Complex.mem_slitPlane_iff.mpr (Or.inl xiStar_pos)
    have hcomp : HasDerivAt hLog (deriv bEven 0 / bEven 0) 0 := by
      have hl := (Complex.hasDerivAt_log hslit).comp 0 hb_d
      change HasDerivAt hLog _ 0 at hl
      simpa [div_eq_mul_inv, mul_comm] using hl
    rw [hcomp.deriv, deriv_bEven_zero, bEven_zero]
    push_cast; ring
  let cH : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n hLog 0
  obtain ⟨M_H, _, hMH⟩ := norm_taylor_coeff_le_of_analyticOnNhd hrH_pos hhLog_an
  let rDiff : ℝ := rH / 2
  have hrDiff_pos : 0 < rDiff := half_pos hrH_pos
  have hDiff_summable : Summable (fun n : ℕ => ‖diffSeries cH n‖ * rDiff ^ n) := by
    have hc_le : ∀ n : ℕ, ‖diffSeries cH n‖ * rDiff ^ n ≤
        (M_H / (2 * rH / 3)) * (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n) := by
      intro n
      have hn1 := hMH (n + 1)
      have hdiv : ‖cH (n + 1)‖ * (rH / 2) ^ n ≤
          (M_H / (2 * rH / 3)) * (3 / 4 : ℝ) ^ n := by
        have hpos_den : 0 < 2 * rH / 3 := by positivity
        have hpow_eq : (rH / 2) ^ n = (3 / 4 : ℝ) ^ n * (2 * rH / 3) ^ n := by
          rw [← mul_pow]; congr 1; field_simp [hrH_pos.ne']; ring
        rw [hpow_eq, div_mul_eq_mul_div, le_div_iff₀ hpos_den]
        calc ‖cH (n + 1)‖ * ((3 / 4 : ℝ) ^ n * (2 * rH / 3) ^ n) * (2 * rH / 3)
            = (‖cH (n + 1)‖ * (2 * rH / 3) ^ (n + 1)) * (3 / 4 : ℝ) ^ n := by
              rw [pow_succ]; ring
          _ ≤ M_H * (3 / 4 : ℝ) ^ n := by gcongr
      calc ‖diffSeries cH n‖ * rDiff ^ n
          ≤ (‖cH (n + 1)‖ * ((n : ℝ) + 1)) * (rH / 2) ^ n :=
            mul_le_mul_of_nonneg_right (norm_diffSeries_le cH n) (by positivity)
        _ = ((n : ℝ) + 1) * (‖cH (n + 1)‖ * (rH / 2) ^ n) := by ring
        _ ≤ ((n : ℝ) + 1) * ((M_H / (2 * rH / 3)) * (3 / 4 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = (M_H / (2 * rH / 3)) * (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n) := by ring
    refine Summable.of_nonneg_of_le (fun _ => by positivity) hc_le ?_
    exact summable_nat_add_one_mul_three_fourths.mul_left (M_H / (2 * rH / 3))
  have hrDiff_le_rad : ENNReal.ofReal rDiff ≤ (diffSeries cH).radius := by
    let r_nn : NNReal := ⟨rDiff, hrDiff_pos.le⟩
    have hs : Summable (fun n : ℕ => ‖diffSeries cH n‖ * (r_nn : ℝ) ^ n) := hDiff_summable
    have hle := (diffSeries cH).le_radius_of_summable_norm hs
    calc ENNReal.ofReal rDiff = ENNReal.ofReal (r_nn : ℝ) := rfl
      _ = (r_nn : ENNReal) := ENNReal.ofReal_coe_nnreal
      _ ≤ (diffSeries cH).radius := hle
  have hDiff_an : AnalyticOnNhd ℂ (diffSeries cH).sum (ball (0 : ℂ × ℂ) rDiff) := by
    have hsub : ball (0 : ℂ × ℂ) rDiff ⊆ Metric.eball (0 : ℂ × ℂ) (diffSeries cH).radius := by
      intro p hp
      rw [mem_ball_zero_iff] at hp
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      exact ((ENNReal.ofReal_lt_ofReal_iff hrDiff_pos).mpr hp).trans_le hrDiff_le_rad
    exact (diffSeries cH).analyticOnNhd.mono hsub
  have hDiff_eval : ∀ u v : ℂ, u ∈ ball (0 : ℂ) rDiff → v ∈ ball (0 : ℂ) rDiff →
      (u - v) * (diffSeries cH).sum (u, v) = hLog u - hLog v := by
    intro u v hu hv
    have hp_eb : (u, v) ∈ Metric.eball (0 : ℂ × ℂ) (diffSeries cH).radius := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
      have hnorm : ‖(u, v)‖ < rDiff := by
        rw [Prod.norm_def]; exact max_lt (mem_ball_zero_iff.mp hu) (mem_ball_zero_iff.mp hv)
      exact ((ENNReal.ofReal_lt_ofReal_iff hrDiff_pos).mpr hnorm).trans_le hrDiff_le_rad
    have hsum_diff := (diffSeries cH).hasSum hp_eb
    have hsum_mul : HasSum (fun n : ℕ => (u - v) * diffSeries cH n (fun _ => (u, v)))
        ((u - v) * (diffSeries cH).sum (u, v)) := hsum_diff.mul_left (u - v)
    have hu_rH : u ∈ ball (0 : ℂ) rH := mem_ball_zero_iff.mpr
      ((mem_ball_zero_iff.mp hu).trans (by dsimp [rDiff]; linarith))
    have hv_rH : v ∈ ball (0 : ℂ) rH := mem_ball_zero_iff.mpr
      ((mem_ball_zero_iff.mp hv).trans (by dsimp [rDiff]; linarith))
    have htu := Complex.hasSum_taylorSeries_on_ball hhLog_an.differentiableOn hu_rH
    have htv := Complex.hasSum_taylorSeries_on_ball hhLog_an.differentiableOn hv_rH
    have htu' : HasSum (fun n : ℕ => cH n * u ^ n) (hLog u) := by
      refine htu.congr_fun fun n => ?_
      simp only [cH, sub_zero, smul_eq_mul]; ring
    have htv' : HasSum (fun n : ℕ => cH n * v ^ n) (hLog v) := by
      refine htv.congr_fun fun n => ?_
      simp only [cH, sub_zero, smul_eq_mul]; ring
    have hsub_sum : HasSum (fun n : ℕ => cH (n + 1) * (u ^ (n + 1) - v ^ (n + 1))) (hLog u - hLog v) := by
      have h_sub := htu'.sub htv'
      rw [← hasSum_nat_add_iff' 1] at h_sub
      simp only [Finset.sum_range_one, pow_zero, mul_one, sub_self, sub_zero] at h_sub
      refine h_sub.congr_fun fun n => by ring
    have heq_fn : (fun n : ℕ => (u - v) * diffSeries cH n (fun _ => (u, v))) =
        (fun n : ℕ => cH (n + 1) * (u ^ (n + 1) - v ^ (n + 1))) := by
      ext n
      rw [diffSeries_apply_eq, ← mul_assoc, mul_comm (u - v) (cH (n + 1)), mul_assoc,
        sub_mul_sum_pow]
    rw [heq_fn] at hsum_mul
    exact hsum_mul.unique hsub_sum
  have hDiff_zero : (diffSeries cH).sum (0, 0) = cH 1 := by
    have hrad_pos : 0 < (diffSeries cH).radius := lt_of_lt_of_le (by simpa using hrDiff_pos) hrDiff_le_rad
    have heq := (diffSeries cH).hasSum (mem_eball_self hrad_pos)
    have h0 : (fun n : ℕ => diffSeries cH n (fun _ => (0 : ℂ × ℂ))) =
        fun n => if n = 0 then cH 1 else 0 := by
      ext n
      cases n with
      | zero => simp [diffSeries_apply_eq]
      | succ n =>
        change diffSeries cH (n + 1) (fun _ => ((0 : ℂ), (0 : ℂ))) = _
        rw [diffSeries_apply_eq]
        have hzero : ∑ j ∈ Finset.range (n + 1 + 1), (0 : ℂ) ^ j * (0 : ℂ) ^ (n + 1 - j) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          rcases eq_or_ne j 0 with rfl | hj0
          · simp
          · simp [zero_pow hj0]
        simp [hzero]
    rw [h0] at heq
    change (diffSeries cH).sum (0 : ℂ × ℂ) = cH 1
    exact heq.unique (hasSum_ite_eq 0 (cH 1))
  have hanOm : AnalyticAt ℂ chartOmega 0 := analyticAt_chartOmega (le_refl 0) (by norm_num)
  obtain ⟨rOm, hrOm_pos, hrOm_an⟩ := hanOm.exists_ball_analyticOnNhd
  let ρ₁ : ℝ := min (min rOm (rB0 / 2)) (min (√rH) (√rDiff))
  have hρ₁_pos : 0 < ρ₁ := by
    dsimp [ρ₁]; have := rB0_pos; positivity
  let ρ : ℝ := ρ₁ / 2
  have hρ_pos : 0 < ρ := half_pos hρ₁_pos
  let η : ℂ → ℂ → ℂ := fun w s =>
    (2 * deriv chartOmega w / ((Real.pi ^ 2 / 6 : ℝ) : ℂ)) * (diffSeries cH).sum (w ^ 2, s ^ 2) - 1
  have hη_an : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ₁) := by
    rintro ⟨w, s⟩ hp
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff] at hp
    have hw_om : w ∈ ball (0 : ℂ) rOm := mem_ball_zero_iff.mpr
      (hp.1.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    have hw_sq_diff : w ^ 2 ∈ ball (0 : ℂ) rDiff := by
      rw [mem_ball_zero_iff, norm_pow]
      have hlt : ‖w‖ < √rDiff := hp.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [norm_nonneg w, Real.sq_sqrt hrDiff_pos.le]
    have hs_sq_diff : s ^ 2 ∈ ball (0 : ℂ) rDiff := by
      rw [mem_ball_zero_iff, norm_pow]
      have hlt : ‖s‖ < √rDiff := hp.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [norm_nonneg s, Real.sq_sqrt hrDiff_pos.le]
    have hp_sq : (w ^ 2, s ^ 2) ∈ ball (0 : ℂ × ℂ) rDiff := by
      rw [mem_ball_zero_iff, Prod.norm_def]
      exact max_lt (mem_ball_zero_iff.mp hw_sq_diff) (mem_ball_zero_iff.mp hs_sq_diff)
    have h1 : AnalyticAt ℂ (fun p : ℂ × ℂ => deriv chartOmega p.1) (w, s) := by
      change AnalyticAt ℂ (deriv chartOmega ∘ Prod.fst) (w, s)
      exact (hrOm_an.deriv w hw_om).comp analyticAt_fst
    have h2 : AnalyticAt ℂ (fun p : ℂ × ℂ => (diffSeries cH).sum (p.1 ^ 2, p.2 ^ 2)) (w, s) := by
      have hf1 : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 ^ 2) (w, s) :=
        (analyticAt_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ)).pow 2
      have hf2 : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2 ^ 2) (w, s) :=
        (analyticAt_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ)).pow 2
      exact AnalyticAt.comp (g := (diffSeries cH).sum) (f := fun p : ℂ × ℂ => (p.1 ^ 2, p.2 ^ 2))
        (hDiff_an _ hp_sq) (hf1.prod hf2)
    change AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (2 * deriv chartOmega p.1 / ((Real.pi ^ 2 / 6 : ℝ) : ℂ)) *
        (diffSeries cH).sum (p.1 ^ 2, p.2 ^ 2) - 1) (w, s)
    have hpi_ne : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    exact (((analyticAt_const.mul h1).div analyticAt_const hpi_ne).mul h2).sub analyticAt_const
  have hη_an_ρ : AnalyticOnNhd ℂ (Function.uncurry η) (ball (0 : ℂ × ℂ) ρ) :=
    hη_an.mono (ball_subset_ball (by dsimp [ρ]; linarith))
  have hη_sep : ∀ w ∈ ball (0 : ℂ) ρ, ∀ s ∈ ball (0 : ℂ) ρ,
      AnalyticAt ℂ (fun w' => η w' s) w ∧ AnalyticAt ℂ (fun s' => η w s') s := by
    intro w hw s hs
    have hp : (w, s) ∈ ball (0 : ℂ × ℂ) ρ := by
      rw [mem_ball_zero_iff, Prod.norm_def]
      exact max_lt (mem_ball_zero_iff.mp hw) (mem_ball_zero_iff.mp hs)
    have hj := hη_an_ρ (w, s) hp
    refine ⟨?_, ?_⟩
    · exact hj.comp₂ analyticAt_id analyticAt_const
    · exact hj.comp₂ analyticAt_const analyticAt_id
  have hη_00 : η 0 0 = 0 := by
    dsimp [η]
    rw [zero_pow two_ne_zero, hDiff_zero]
    have hcH1 : cH 1 = deriv hLog 0 := by
      dsimp [cH]; simp [iteratedDeriv_one]
    rw [deriv_chartOmega_zero, hcH1, hhLog_deriv0]
    push_cast
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hsq2 : √2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hxi : xiStar ≠ 0 := xiStar_pos.ne'
    field_simp [hpi, hsq2, hxi]
    ring
  have hcl_sub : closedBall (0 : ℂ × ℂ) ρ ⊆ ball (0 : ℂ × ℂ) ρ₁ :=
    closedBall_subset_ball (by dsimp [ρ]; linarith)
  obtain ⟨M_η0, hM_η0⟩ := (isCompact_closedBall (0 : ℂ × ℂ) ρ).exists_bound_of_continuousOn
    (hη_an.fderiv.continuousOn.mono hcl_sub)
  let C : ℝ := max M_η0 0
  have hC_nn : 0 ≤ C := le_max_right _ _
  have hη_mvt : ∀ w ∈ ball (0 : ℂ) ρ, ∀ s ∈ ball (0 : ℂ) ρ, ‖η w s‖ ≤ C * (‖w‖ + ‖s‖) := by
    intro w hw s hs
    have hp_cb : (w, s) ∈ closedBall (0 : ℂ × ℂ) ρ := by
      rw [mem_closedBall_zero_iff, Prod.norm_def]
      exact le_of_lt (max_lt (mem_ball_zero_iff.mp hw) (mem_ball_zero_iff.mp hs))
    have hmvt : ‖Function.uncurry η (w, s) - Function.uncurry η (0, 0)‖ ≤ C * ‖(w, s) - (0, 0)‖ :=
      (convex_closedBall (0 : ℂ × ℂ) ρ).norm_image_sub_le_of_norm_fderiv_le
        (fun p hp => (hη_an p (hcl_sub hp)).differentiableAt)
        (fun p hp => (hM_η0 p hp).trans (le_max_left M_η0 0))
        (mem_closedBall_self hρ_pos.le) hp_cb
    change ‖η w s - η 0 0‖ ≤ C * ‖(w, s) - (0, 0)‖ at hmvt
    simp only [hη_00, Prod.mk_sub_mk, sub_zero, Prod.norm_def] at hmvt
    have hmax : max ‖w‖ ‖s‖ ≤ ‖w‖ + ‖s‖ := max_le (le_add_of_nonneg_right (norm_nonneg s))
      (le_add_of_nonneg_left (norm_nonneg w))
    exact hmvt.trans (mul_le_mul_of_nonneg_left hmax hC_nn)
  have hη_fac : ∀ w ∈ ball (0 : ℂ) ρ, ∀ s ∈ ball (0 : ℂ) ρ,
      2 * Complex.log (chartB w / chartB s) * deriv chartOmega w =
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (w ^ 2 - s ^ 2) * (1 + η w s) := by
    intro w hw s hs
    have hw1 : ‖w‖ < ρ₁ := (mem_ball_zero_iff.mp hw).trans (by dsimp [ρ]; linarith)
    have hs1 : ‖s‖ < ρ₁ := (mem_ball_zero_iff.mp hs).trans (by dsimp [ρ]; linarith)
    have hw_half : ‖w‖ < rB0 / 2 := hw1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hs_half : ‖s‖ < rB0 / 2 := hs1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hw_sq_rH : w ^ 2 ∈ ball (0 : ℂ) rH := by
      rw [mem_ball_zero_iff, norm_pow]
      have hlt : ‖w‖ < √rH := hw1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      nlinarith [norm_nonneg w, Real.sq_sqrt hrH_pos.le]
    have hs_sq_rH : s ^ 2 ∈ ball (0 : ℂ) rH := by
      rw [mem_ball_zero_iff, norm_pow]
      have hlt : ‖s‖ < √rH := hs1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      nlinarith [norm_nonneg s, Real.sq_sqrt hrH_pos.le]
    have hw_sq_diff : w ^ 2 ∈ ball (0 : ℂ) rDiff := by
      rw [mem_ball_zero_iff, norm_pow]
      have hlt : ‖w‖ < √rDiff := hw1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [norm_nonneg w, Real.sq_sqrt hrDiff_pos.le]
    have hs_sq_diff : s ^ 2 ∈ ball (0 : ℂ) rDiff := by
      rw [mem_ball_zero_iff, norm_pow]
      have hlt : ‖s‖ < √rDiff := hs1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [norm_nonneg s, Real.sq_sqrt hrDiff_pos.le]
    have hbw : chartB w = bEven (w ^ 2) := (bEven_sq_eq_chartB hw_half).symm
    have hbs : chartB s = bEven (s ^ 2) := (bEven_sq_eq_chartB hs_half).symm
    have hbw_re : 0 < (chartB w).re := by rw [hbw]; exact (hrH _ hw_sq_rH).2
    have hbs_re : 0 < (chartB s).re := by rw [hbs]; exact (hrH _ hs_sq_rH).2
    have hlog_sub : Complex.log (chartB w / chartB s) = hLog (w ^ 2) - hLog (s ^ 2) := by
      rw [log_div_of_re_pos_chart hbw_re hbs_re, hbw, hbs]
    have hdiff_id := hDiff_eval (w ^ 2) (s ^ 2) hw_sq_diff hs_sq_diff
    have hpi_ne : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    rw [hlog_sub, ← hdiff_id]
    dsimp [η]
    field_simp [hpi_ne]
    ring
  refine ⟨η, ρ, hρ_pos, C, hC_nn, hη_an_ρ, hη_sep, hη_fac, hη_mvt⟩

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_F

end FormalResearch.ModularBootstrap.Chart
