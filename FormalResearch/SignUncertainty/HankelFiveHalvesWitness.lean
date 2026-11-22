module

public import FormalResearch.SignUncertainty.HardyMellinIntertwiner

/-!
# Explicit `c = 5 / 2` (`d = 5`, `J_{3/2}`) Hankel Witness (`general_theorems.tex` Proposition 7.9a)

Unconditional verification of `HankelKernelData (5 / 2)` (`hankelKernel_fiveHalves`) and
explicit feasible witness pair `hankelIntertwiner_nonvacuous`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis

/-! #### Explicit Non-Vacuity Witness at `c = 5 / 2` (`d = 5`, `J_{3/2}` Hankel Kernel) -/

noncomputable def phi52 (w : ℝ) : ℝ :=
  (3 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) * Real.cos (4 * π * Real.sqrt w * t)

private lemma phi52_zero : phi52 0 = 1 := by
  unfold phi52
  simp_rw [Real.sqrt_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x - x ^ 3 / 3) (1 - t ^ 2) t := fun t _ =>
    ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)).congr_deriv (by norm_num)
  have hint : IntervalIntegrable (fun t : ℝ => 1 - t ^ 2) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

private lemma phi52_cont : Continuous phi52 := by
  unfold phi52
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    ((continuous_const.sub (continuous_snd.pow 2)).mul
      (Real.continuous_cos.comp
        ((continuous_const.mul (Real.continuous_sqrt.comp continuous_fst)).mul continuous_snd)))
    0 1

private lemma phi52_abs_le (w : ℝ) : |phi52 w| ≤ 1 := by
  unfold phi52
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 - t ^ 2) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2).intervalIntegrable 0 1
  have hmono : ‖∫ t in (0 : ℝ)..1, (1 - t ^ 2) * Real.cos (4 * π * Real.sqrt w * t)‖ ≤
      ∫ t in (0 : ℝ)..1, (1 - t ^ 2) := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hint2
    refine Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1t : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    rw [abs_of_nonneg h1t]
    exact mul_le_of_le_one_right h1t (Real.abs_cos_le_one _)
  have hval : ∫ t in (0 : ℝ)..1, (1 - t ^ 2) = 2 / 3 := by
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x - x ^ 3 / 3) (1 - t ^ 2) t := fun t _ =>
      ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)).congr_deriv (by norm_num)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
    norm_num
  rw [Real.norm_eq_abs] at hmono
  linarith [hmono.trans_eq hval]

private lemma phi52_closed {w : ℝ} (hw : 0 < w) :
    phi52 w = 3 * (Real.sin (4 * π * √w) - 4 * π * √w * Real.cos (4 * π * √w)) / (4 * π * √w) ^ 3 := by
  let α : ℝ := 4 * π * √w
  have hα : α ≠ 0 := by positivity
  let H : ℝ → ℝ := fun t => ((1 - t ^ 2) / α + 2 / α ^ 3) * Real.sin (α * t) - (2 * t / α ^ 2) * Real.cos (α * t)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt H ((1 - t ^ 2) * Real.cos (α * t)) t := by
    intro t _
    have hA : HasDerivAt (fun x : ℝ => (1 - x ^ 2) / α + 2 / α ^ 3) (-2 * t / α) t :=
      ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_pow 2 t)).div_const α).add_const
        (2 / α ^ 3)).congr_deriv (by norm_num)
    have hs : HasDerivAt (fun x : ℝ => Real.sin (α * x)) (Real.cos (α * t) * α) t := by
      have hd := (Real.hasDerivAt_sin (α * t)).comp t (hasDerivAt_const_mul α)
      simpa [Function.comp_def] using hd
    have hB : HasDerivAt (fun x : ℝ => 2 * x / α ^ 2) (2 / α ^ 2) t := by
      have hd := ((hasDerivAt_id t).const_mul (2 : ℝ)).div_const (α ^ 2)
      simpa [id] using hd
    have hc : HasDerivAt (fun x : ℝ => Real.cos (α * x)) (-Real.sin (α * t) * α) t := by
      have hd := (Real.hasDerivAt_cos (α * t)).comp t (hasDerivAt_const_mul α)
      simpa [Function.comp_def] using hd
    exact ((hA.mul hs).sub (hB.mul hc)).congr_deriv (by field_simp [hα]; ring)
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) * Real.cos (α * t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => (1 - t ^ 2) * Real.cos (α * t)).intervalIntegrable 0 1
  unfold phi52
  change (3 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) * Real.cos (α * t) = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [H]
  simp only [mul_one, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp [hα]
  ring

private lemma integral_cos_sq_tail_bound {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |∫ t in a..b, Real.cos (t ^ 2)| ≤ 1 / a := by
  have ha0 : 0 < a := by linarith
  let u : ℝ → ℝ := fun s => (2 * s)⁻¹
  let u' : ℝ → ℝ := fun s => -1 / (2 * s ^ 2)
  let v : ℝ → ℝ := fun s => Real.sin (s ^ 2)
  let v' : ℝ → ℝ := fun s => 2 * s * Real.cos (s ^ 2)
  have hu : ContinuousOn u (uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (continuousOn_const.mul continuousOn_id).inv₀ fun x hx =>
      mul_ne_zero two_ne_zero (by dsimp; linarith [hx.1])
  have hv : ContinuousOn v (uIcc a b) := (by fun_prop : Continuous v).continuousOn
  have hu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x := fun x hx => by
    have hx0 : x ≠ 0 := by linarith [(min_eq_left hab) ▸ hx.1]
    have hd := ((hasDerivAt_id x).const_mul (2 : ℝ)).inv (by positivity : 2 * x ≠ 0)
    exact hd.congr_deriv (by dsimp [u']; field_simp [hx0])
  have hv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x := fun x _ => by
    have hd := (Real.hasDerivAt_sin (x ^ 2)).comp x (hasDerivAt_pow 2 x)
    exact hd.congr_deriv (by dsimp [v']; norm_num; ring)
  have hiu' : IntervalIntegrable u' volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div (continuousOn_const.mul (continuousOn_pow 2)) fun x hx => by
      have : 0 < x := by linarith [hx.1]
      positivity
  have hiv' : IntervalIntegrable v' volume a b :=
    (by fun_prop : Continuous v').intervalIntegrable a b
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv hu' hv' hiu' hiv'
  have heq : ∫ x in a..b, u x * v' x = ∫ t in a..b, Real.cos (t ^ 2) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    dsimp [u, v']; field_simp [hx0]
  rw [heq] at hibp
  have hibp' : ∫ t in a..b, Real.cos (t ^ 2) =
      Real.sin (b ^ 2) / (2 * b) - Real.sin (a ^ 2) / (2 * a) +
        ∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2) := by
    rw [hibp]
    have hneg : ∫ x in a..b, u' x * v x = - ∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      dsimp [u', v]; ring
    rw [hneg]
    dsimp [u, v]; ring
  have hint_pos : IntervalIntegrable (fun x : ℝ => 1 / (2 * x ^ 2)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div (continuousOn_const.mul (continuousOn_pow 2)) fun x hx => by
      have : 0 < x := by linarith [hx.1]
      positivity
  have hrem_bd : |∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2)| ≤ ∫ x in a..b, 1 / (2 * x ^ 2) := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hint_pos
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * x ^ 2)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hrem_val : ∫ x in a..b, 1 / (2 * x ^ 2) = 1 / (2 * a) - 1 / (2 * b) := by
    have hder : ∀ x ∈ uIcc a b, HasDerivAt (fun s : ℝ => -(2 * s)⁻¹) (1 / (2 * x ^ 2)) x := fun x hx => by
      rw [Set.uIcc_of_le hab] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have hd := (((hasDerivAt_id x).const_mul (2 : ℝ)).inv (by positivity : 2 * x ≠ 0)).neg
      exact hd.congr_deriv (by simp only [id, mul_one]; field_simp [hx0])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint_pos]
    ring
  rw [hibp']
  have hb0 : 0 < b := by linarith
  calc |Real.sin (b ^ 2) / (2 * b) - Real.sin (a ^ 2) / (2 * a) +
          ∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2)|
      ≤ |Real.sin (b ^ 2) / (2 * b)| + |Real.sin (a ^ 2) / (2 * a)| +
          |∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2)| := by
        calc |Real.sin (b ^ 2) / (2 * b) - Real.sin (a ^ 2) / (2 * a) +
                ∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2)|
            ≤ |Real.sin (b ^ 2) / (2 * b) - Real.sin (a ^ 2) / (2 * a)| +
                |∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2)| := abs_add_le _ _
          _ ≤ |Real.sin (b ^ 2) / (2 * b)| + |Real.sin (a ^ 2) / (2 * a)| +
                |∫ x in a..b, Real.sin (x ^ 2) / (2 * x ^ 2)| := by gcongr; exact abs_sub _ _
    _ ≤ 1 / (2 * b) + 1 / (2 * a) + (1 / (2 * a) - 1 / (2 * b)) := by
        have h1 : |Real.sin (b ^ 2) / (2 * b)| ≤ 1 / (2 * b) := by
          rw [abs_div, abs_of_pos (mul_pos zero_lt_two hb0)]
          exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (mul_pos zero_lt_two hb0).le
        have h2 : |Real.sin (a ^ 2) / (2 * a)| ≤ 1 / (2 * a) := by
          rw [abs_div, abs_of_pos (mul_pos zero_lt_two ha0)]
          exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (mul_pos zero_lt_two ha0).le
        linarith [hrem_bd.trans_eq hrem_val]
    _ = 1 / a := by field_simp [ha0.ne', hb0.ne']; ring

private lemma fresnel_exp_limit :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))
      (𝓝[>] 0) (𝓝 √(π / 8)) := by
  have hformula : ∀ {ε : ℝ}, 0 < ε →
      ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2) =
        (1 / 2 : ℝ) * (((π : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ)).re := by
    intro ε hε
    let b : ℂ := (ε : ℂ) - Complex.I
    have hb : 0 < b.re := by simp [b, hε]
    have hcint := GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I hb 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hcint
    have hre : (∫ x : ℝ, (Complex.exp (-b * (x : ℂ) ^ 2)).re) =
        (((π : ℂ) / b) ^ (1 / 2 : ℂ)).re := by
      have hint : Integrable (fun x : ℝ => Complex.exp (-b * (x : ℂ) ^ 2)) := by
        simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
          GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I hb 0
      calc (∫ x : ℝ, (Complex.exp (-b * (x : ℂ) ^ 2)).re)
          = ∫ x : ℝ, Complex.reCLM (Complex.exp (-b * (x : ℂ) ^ 2)) := rfl
        _ = Complex.reCLM (∫ x : ℝ, Complex.exp (-b * (x : ℂ) ^ 2)) :=
            ContinuousLinearMap.integral_comp_comm Complex.reCLM hint
        _ = (((π : ℂ) / b) ^ (1 / 2 : ℂ)).re := congrArg Complex.re hcint
    have hexp_re : ∀ x : ℝ, (Complex.exp (-b * (x : ℂ) ^ 2)).re =
        Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2) := fun x => by
      have heq : -b * (x : ℂ) ^ 2 = ((-ε * x ^ 2 : ℝ) : ℂ) + ((x ^ 2 : ℝ) : ℂ) * Complex.I := by
        simp only [b]; push_cast; ring
      rw [heq, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin, Complex.mul_re]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, sub_zero, mul_zero, mul_one, add_zero]
    simp_rw [hexp_re] at hre
    have heven : Integrable (fun x : ℝ => Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2)) := by
      refine (integrable_exp_neg_mul_sq hε).mono'
        (by fun_prop : Continuous fun x : ℝ => Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2)).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have hsplit : ∫ x : ℝ, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2) =
        2 * ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2) := by
      have h1 : Tendsto (fun R : ℝ => ∫ x in -R..R, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2))
          atTop (𝓝 (∫ x : ℝ, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2))) :=
        intervalIntegral_tendsto_integral heven tendsto_neg_atTop_atBot tendsto_id
      have h2 : Tendsto (fun R : ℝ => 2 * ∫ x in (0 : ℝ)..R, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2))
          atTop (𝓝 (2 * ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))) :=
        (intervalIntegral_tendsto_integral_Ioi 0 heven.integrableOn tendsto_id).const_mul 2
      have hcongr : (fun R : ℝ => ∫ x in -R..R, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2)) =
          fun R : ℝ => 2 * ∫ x in (0 : ℝ)..R, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2) := by
        ext R
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (heven.intervalIntegrable (a := -R) (b := 0))
          (heven.intervalIntegrable (a := 0) (b := R))]
        have hleft : ∫ x in -R..0, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2) =
            ∫ x in (0 : ℝ)..R, Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2) := by
          have hcomp := (intervalIntegral.integral_comp_neg (a := 0) (b := R)
            (f := fun x => Real.exp (-ε * x ^ 2) * Real.cos (x ^ 2))).symm
          simp only [neg_zero, neg_sq] at hcomp
          exact hcomp
        rw [hleft]; ring
      rw [hcongr] at h1
      exact tendsto_nhds_unique h1 h2
    linarith [hre, hsplit]
  have hlim_c : Tendsto (fun ε : ℝ => (1 / 2 : ℝ) * (((π : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ)).re)
      (𝓝[>] 0) (𝓝 √(π / 8)) := by
    have hcont : ContinuousAt (fun ε : ℝ => ((π : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ)) 0 := by
      have hdiv : ContinuousAt (fun ε : ℝ => (π : ℂ) / ((ε : ℂ) - Complex.I)) 0 :=
        continuousAt_const.div ((Complex.continuous_ofReal.continuousAt).sub continuousAt_const)
          (by simp)
      have hslit : (π : ℂ) / (((0 : ℝ) : ℂ) - Complex.I) ∈ Complex.slitPlane := by
        rw [Complex.ofReal_zero, zero_sub, div_neg, div_I]
        simp [Complex.mem_slitPlane_iff, Real.pi_pos.ne']
      exact (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hslit).comp
        (f := fun ε : ℝ => (π : ℂ) / ((ε : ℂ) - Complex.I)) hdiv
    have hval : (1 / 2 : ℝ) * (((π : ℂ) / (((0 : ℝ) : ℂ) - Complex.I)) ^ (1 / 2 : ℂ)).re = √(π / 8) := by
      have hpiI : (π : ℂ) / (((0 : ℝ) : ℂ) - Complex.I) = ((π : ℝ) : ℂ) * Complex.I := by
        rw [Complex.ofReal_zero, zero_sub, div_neg, div_I]; ring
      have hne : ((π : ℝ) : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') Complex.I_ne_zero
      rw [hpiI, Complex.cpow_def_of_ne_zero hne, Complex.log_ofReal_mul Real.pi_pos Complex.I_ne_zero,
        Complex.log_I, add_mul, Complex.exp_add]
      have hpi12 : Complex.exp (((Real.log π : ℝ) : ℂ) * (1 / 2 : ℂ)) = ((√π : ℝ) : ℂ) := by
        rw [show ((Real.log π : ℝ) : ℂ) * (1 / 2 : ℂ) = (((Real.log π * (1 / 2) : ℝ) : ℂ)) by push_cast; ring,
          ← Complex.ofReal_exp, ← Real.rpow_def_of_pos Real.pi_pos, ← Real.sqrt_eq_rpow]
      have hI12 : Complex.exp ((π / 2 * Complex.I) * (1 / 2 : ℂ)) =
          ((√2 / 2 : ℝ) : ℂ) + ((√2 / 2 : ℝ) : ℂ) * Complex.I := by
        rw [show (π / 2 * Complex.I) * (1 / 2 : ℂ) = (((π / 4 : ℝ) : ℂ)) * Complex.I by push_cast; ring,
          Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_pi_div_four, Real.sin_pi_div_four]
      rw [hpi12, hI12, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      have hsq : ((1 / 2 : ℝ) * (√π * (√2 / 2))) ^ 2 = π / 8 := by
        simp only [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [← Real.sqrt_sq (by positivity : 0 ≤ (1 / 2 : ℝ) * (√π * (√2 / 2))), hsq]
    have ht : Tendsto (fun ε : ℝ => (1 / 2 : ℝ) * (((π : ℂ) / ((ε : ℂ) - Complex.I)) ^ (1 / 2 : ℂ)).re)
        (𝓝 0) (𝓝 √(π / 8)) := by
      rw [← hval]
      exact (tendsto_const_nhds.mul (Complex.continuous_re.continuousAt.comp hcont).tendsto)
    exact ht.mono_left nhdsWithin_le_nhds
  refine hlim_c.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hformula hε).symm

private lemma tendsto_integral_cos_sq :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, Real.cos (t ^ 2)) atTop (𝓝 √(π / 8)) := by
  let F : ℝ → ℝ := fun R => ∫ t in (0 : ℝ)..R, Real.cos (t ^ 2)
  have hF_bd : ∀ R ≥ 0, |F R| ≤ 2 := fun R hR => by
    rcases le_total R 1 with hR1 | h1R
    · dsimp [F]
      have hint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 R :=
        continuous_const.intervalIntegrable 0 R
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => Real.cos (t ^ 2)) hR
        (Eventually.of_forall fun _ _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _) hint
      rw [Real.norm_eq_abs, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hnorm
      linarith
    · dsimp [F]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable 0 1)
        ((by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable 1 R)]
      have h01 : |∫ t in (0 : ℝ)..1, Real.cos (t ^ 2)| ≤ 1 := by
        have hint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
          continuous_const.intervalIntegrable 0 1
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => Real.cos (t ^ 2)) zero_le_one
          (Eventually.of_forall fun _ _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _) hint
        simpa [Real.norm_eq_abs] using hnorm
      have h1R' := integral_cos_sq_tail_bound (le_refl 1) h1R
      rw [div_one] at h1R'
      exact (abs_add_le _ _).trans (by linarith)
  have hF_cauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    let R₀ : ℝ := max 1 ((N : ℝ) + 1)
    refine ⟨R₀, fun a ha b hb => ?_⟩
    wlog hab : a ≤ b generalizing a b
    · rw [dist_comm]; exact this b hb a ha (le_of_not_ge hab)
    have ha1 : 1 ≤ a := (le_max_left _ _).trans ha
    have haN : 1 / a < δ := lt_of_le_of_lt
      (one_div_le_one_div_of_le (by positivity) ((le_max_right _ _).trans ha)) hN
    have hsub : F b - F a = ∫ t in a..b, Real.cos (t ^ 2) := by
      dsimp [F]
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        ((by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable (μ := volume) 0 a)
        ((by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable (μ := volume) a b)
      linarith
    rw [Real.dist_eq, abs_sub_comm, hsub]
    exact (integral_cos_sq_tail_bound ha1 hab).trans_lt haN
  obtain ⟨L, hFL⟩ := cauchySeq_tendsto_of_complete hF_cauchy
  suffices hL_eq : L = √(π / 8) by rwa [hL_eq] at hFL
  have hF_cont : Continuous F :=
    intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => (by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable (μ := volume) a b) 0
  have hAbel : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))
      (𝓝[>] 0) (𝓝 L) := by
    have hIBP : ∀ {ε : ℝ}, 0 < ε →
        ∫ t in Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2) =
          ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t := by
      intro ε hε
      have hfin : ∀ R ≥ 0, ∫ t in (0 : ℝ)..R, Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2) =
          Real.exp (-ε * R ^ 2) * F R + ∫ t in (0 : ℝ)..R, (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t := by
        intro R _
        let u : ℝ → ℝ := fun t => Real.exp (-ε * t ^ 2)
        let u' : ℝ → ℝ := fun t => -2 * ε * t * Real.exp (-ε * t ^ 2)
        have hu : ContinuousOn u (uIcc 0 R) := (by fun_prop : Continuous u).continuousOn
        have hv : ContinuousOn F (uIcc 0 R) := hF_cont.continuousOn
        have hu' : ∀ t ∈ Ioo (min 0 R) (max 0 R), HasDerivAt u (u' t) t := fun t _ => by
          have hd := (Real.hasDerivAt_exp (-ε * t ^ 2)).comp t ((hasDerivAt_pow 2 t).const_mul (-ε))
          exact hd.congr_deriv (by dsimp [u']; norm_num; ring)
        have hv' : ∀ t ∈ Ioo (min 0 R) (max 0 R), HasDerivAt F (Real.cos (t ^ 2)) t := fun t _ =>
          ((by fun_prop : Continuous fun s : ℝ => Real.cos (s ^ 2)).integral_hasStrictDerivAt 0 t).hasDerivAt
        have hiu' : IntervalIntegrable u' volume 0 R :=
          (by fun_prop : Continuous u').intervalIntegrable 0 R
        have hiv' : IntervalIntegrable (fun t => Real.cos (t ^ 2)) volume 0 R :=
          (by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable 0 R
        have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv hu' hv' hiu' hiv'
        have hF0 : F 0 = 0 := by simp [F]
        have hneg : ∫ t in (0 : ℝ)..R, u' t * F t =
            - ∫ t in (0 : ℝ)..R, (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t := by
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun t _ => by dsimp [u']; ring
        rw [h, hF0, mul_zero, sub_zero, hneg]
        dsimp [u]; ring
      have heven1 : IntegrableOn (fun t : ℝ => Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2)) (Ioi 0) :=
        ((integrable_exp_neg_mul_sq hε).mono'
          (by fun_prop : Continuous fun t : ℝ => Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2)).aestronglyMeasurable
          (Eventually.of_forall fun t => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _))).integrableOn
      have hexp_t_int : IntegrableOn (fun t : ℝ => 2 * ε * t * Real.exp (-ε * t ^ 2)) (Ioi 0) := by
        have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -Real.exp (-ε * x ^ 2))
            (2 * ε * t * Real.exp (-ε * t ^ 2)) t := fun t _ =>
          ((((hasDerivAt_pow 2 t).const_mul (-ε)).exp).neg).congr_deriv (by norm_num; ring)
        have ht0 : Tendsto (fun x : ℝ => -Real.exp (-ε * x ^ 2)) atTop (𝓝 0) := by
          have : Tendsto (fun x : ℝ => Real.exp (-ε * x ^ 2)) atTop (𝓝 0) :=
            Real.tendsto_exp_atBot.comp ((tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hε)
              (tendsto_pow_atTop (by norm_num : 2 ≠ 0))))
          simpa using this.neg
        exact integrableOn_Ioi_deriv_of_nonneg' hderiv
          (fun t (ht : 0 < t) => mul_nonneg (by positivity) (Real.exp_pos _).le) ht0
      have heven2 : IntegrableOn (fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t) (Ioi 0) := by
        refine (hexp_t_int.const_mul 2).mono' ?_ ?_
        · exact (by fun_prop : Continuous fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t).aestronglyMeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
          calc 2 * ε * t * Real.exp (-ε * t ^ 2) * |F t|
              ≤ 2 * ε * t * Real.exp (-ε * t ^ 2) * 2 := by gcongr; exact hF_bd t ht.le
            _ = 2 * (2 * ε * t * Real.exp (-ε * t ^ 2)) := by ring
      have hl1 : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))
          atTop (𝓝 (∫ t in Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))) :=
        intervalIntegral_tendsto_integral_Ioi 0 heven1 tendsto_id
      have hl2 : Tendsto (fun R : ℝ => Real.exp (-ε * R ^ 2) * F R +
          ∫ t in (0 : ℝ)..R, (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t)
          atTop (𝓝 (0 + ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t)) := by
        refine Tendsto.add ?_ (intervalIntegral_tendsto_integral_Ioi 0 heven2 tendsto_id)
        refine squeeze_zero_norm' (a := fun R : ℝ => 2 * Real.exp (-ε * R ^ 2)) ?_ ?_
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact (mul_le_mul_of_nonneg_left (hF_bd R hR) (Real.exp_pos _).le).trans_eq (mul_comm _ 2)
        · have : Tendsto (fun R : ℝ => 2 * Real.exp (-ε * R ^ 2)) atTop (𝓝 (2 * 0)) :=
            tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop
              (neg_lt_zero.mpr hε) (tendsto_pow_atTop (by norm_num : 2 ≠ 0))))
          simpa using this
      rw [zero_add] at hl2
      exact tendsto_nhds_unique (hl1.congr' (by filter_upwards [eventually_ge_atTop 0] with R hR; exact hfin R hR)) hl2
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hL_bd : |L| ≤ 2 := le_of_tendsto hFL.abs (by filter_upwards [eventually_ge_atTop 0] with R hR; exact hF_bd R hR)
    obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp hFL (δ / 4) (by positivity)
    let T : ℝ := max T₀ 1
    have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hexp_lim : Tendsto (fun ε : ℝ => (4 : ℝ) * (1 - Real.exp (-ε * T ^ 2))) (𝓝[>] 0) (𝓝 0) := by
      have : ContinuousAt (fun ε : ℝ => (4 : ℝ) * (1 - Real.exp (-ε * T ^ 2))) 0 := by fun_prop
      simpa using this.continuousWithinAt.tendsto
    filter_upwards [self_mem_nhdsWithin, hexp_lim (Metric.ball_mem_nhds 0 (half_pos hδ))] with ε (hε : 0 < ε) hε_small
    rw [hIBP hε, Real.dist_eq]
    have hderiv_w : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -Real.exp (-ε * x ^ 2))
        (2 * ε * t * Real.exp (-ε * t ^ 2)) t := fun t _ =>
      ((((hasDerivAt_pow 2 t).const_mul (-ε)).exp).neg).congr_deriv (by norm_num; ring)
    have ht0 : Tendsto (fun x : ℝ => -Real.exp (-ε * x ^ 2)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hε)
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)))).neg
    have hint_w : IntegrableOn (fun t : ℝ => 2 * ε * t * Real.exp (-ε * t ^ 2)) (Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg' hderiv_w
        (fun t (ht : 0 < t) => mul_nonneg (by positivity) (Real.exp_pos _).le) ht0
    have hmass_one : ∫ t in Ioi (0 : ℝ), 2 * ε * t * Real.exp (-ε * t ^ 2) = 1 := by
      have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv_w hint_w ht0
      simpa using hres
    have hwF_int : IntegrableOn (fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t) (Ioi 0) := by
      refine (hint_w.const_mul 2).mono' ?_ ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) => ?_)
      · exact (by fun_prop : Continuous fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
        calc 2 * ε * t * Real.exp (-ε * t ^ 2) * |F t|
            ≤ 2 * ε * t * Real.exp (-ε * t ^ 2) * 2 := by gcongr; exact hF_bd t ht.le
          _ = 2 * (2 * ε * t * Real.exp (-ε * t ^ 2)) := by ring
    have hwL_int : IntegrableOn (fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * L) (Ioi 0) :=
      hint_w.mul_const L
    have hL_int : ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * L = L := by
      rw [integral_mul_const, hmass_one, one_mul]
    have hdiff_eq : (∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t) - L =
        (∫ t in Ioc (0 : ℝ) T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)) +
          ∫ t in Ioi T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L) := by
      have hwsub : IntegrableOn (fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)) (Ioi 0) :=
        (hwF_int.sub hwL_int).congr_fun (fun t _ => by dsimp; ring) measurableSet_Ioi
      have hunion := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hwsub.mono_set Ioc_subset_Ioi_self) (hwsub.mono_set (Ioi_subset_Ioi hT0.le))
      rw [Set.Ioc_union_Ioi_eq_Ioi hT0.le] at hunion
      have hcongr : ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t -
            (2 * ε * t * Real.exp (-ε * t ^ 2)) * L =
          ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
      calc (∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t) - L
          = (∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t) -
              ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * L := by rw [hL_int]
        _ = ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t -
              (2 * ε * t * Real.exp (-ε * t ^ 2)) * L := (integral_sub hwF_int hwL_int).symm
        _ = ∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L) := hcongr
        _ = (∫ t in Ioc (0 : ℝ) T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)) +
              ∫ t in Ioi T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L) := hunion
    have hIoc_bd : |∫ t in Ioc (0 : ℝ) T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)| ≤
        4 * (1 - Real.exp (-ε * T ^ 2)) := by
      have hsub_int : IntegrableOn (fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)) (Ioc 0 T) :=
        ((hwF_int.sub hwL_int).congr_fun (fun t _ => by dsimp; ring) measurableSet_Ioi).mono_set Ioc_subset_Ioi_self
      have hIoc_w : ∫ t in Ioc (0 : ℝ) T, (2 * ε * t * Real.exp (-ε * t ^ 2)) = 1 - Real.exp (-ε * T ^ 2) := by
        rw [← intervalIntegral.integral_of_le hT0.le,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t ht => hderiv_w t (by rw [Set.uIcc_of_le hT0.le] at ht; exact ht.1))
            ((by fun_prop : Continuous fun t : ℝ => 2 * ε * t * Real.exp (-ε * t ^ 2)).intervalIntegrable 0 T)]
        simp; ring
      calc |∫ t in Ioc (0 : ℝ) T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)|
          ≤ ∫ t in Ioc (0 : ℝ) T, 4 * (2 * ε * t * Real.exp (-ε * t ^ 2)) := by
            rw [← Real.norm_eq_abs]
            refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hsub_int.norm
              ((hint_w.mono_set Ioc_subset_Ioi_self).const_mul 4) measurableSet_Ioc fun t ht => ?_)
            have hwt_nn : 0 ≤ 2 * ε * t * Real.exp (-ε * t ^ 2) :=
              mul_nonneg (mul_nonneg (by positivity) ht.1.le) (Real.exp_pos _).le
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwt_nn]
            have hFLt : |F t - L| ≤ 4 := (abs_sub _ _).trans (by linarith [hF_bd t ht.1.le, hL_bd])
            exact (mul_le_mul_of_nonneg_left hFLt hwt_nn).trans_eq (mul_comm _ 4)
        _ = 4 * (1 - Real.exp (-ε * T ^ 2)) := by rw [integral_const_mul, hIoc_w]
    have hIoi_bd : |∫ t in Ioi T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)| ≤ δ / 4 := by
      have hsub_int : IntegrableOn (fun t : ℝ => (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)) (Ioi T) :=
        ((hwF_int.sub hwL_int).congr_fun (fun t _ => by dsimp; ring) measurableSet_Ioi).mono_set (Ioi_subset_Ioi hT0.le)
      have hle1 : ∫ t in Ioi T, (2 * ε * t * Real.exp (-ε * t ^ 2)) ≤ 1 := by
        rw [← hmass_one]
        exact setIntegral_mono_set hint_w ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
          mul_nonneg (by positivity) (Real.exp_pos _).le) (Ioi_subset_Ioi hT0.le).eventuallyLE
      calc |∫ t in Ioi T, (2 * ε * t * Real.exp (-ε * t ^ 2)) * (F t - L)|
          ≤ ∫ t in Ioi T, (δ / 4) * (2 * ε * t * Real.exp (-ε * t ^ 2)) := by
            rw [← Real.norm_eq_abs]
            refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hsub_int.norm
              ((hint_w.mono_set (Ioi_subset_Ioi hT0.le)).const_mul (δ / 4)) measurableSet_Ioi fun t (ht : T < t) => ?_)
            have hwt_nn : 0 ≤ 2 * ε * t * Real.exp (-ε * t ^ 2) :=
              mul_nonneg (mul_nonneg (by positivity) (hT0.trans ht).le) (Real.exp_pos _).le
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwt_nn]
            have ht0' : T₀ ≤ t := le_of_lt ((le_max_left _ _).trans_lt ht)
            have hFLt : |F t - L| ≤ δ / 4 := by
              have := hT₀ t ht0'; rw [Real.dist_eq] at this; exact this.le
            exact (mul_le_mul_of_nonneg_left hFLt hwt_nn).trans_eq (mul_comm _ (δ / 4))
        _ = (δ / 4) * ∫ t in Ioi T, (2 * ε * t * Real.exp (-ε * t ^ 2)) := integral_const_mul _ _
        _ ≤ (δ / 4) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ = δ / 4 := mul_one _
    have h4_lt : 4 * (1 - Real.exp (-ε * T ^ 2)) < δ / 2 := by
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg] at hε_small
      · exact hε_small
      · have : Real.exp (-ε * T ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
    rw [show (∫ t in Ioi (0 : ℝ), 2 * ε * t * Real.exp (-ε * t ^ 2) * F t) - L =
        (∫ t in Ioi (0 : ℝ), (2 * ε * t * Real.exp (-ε * t ^ 2)) * F t) - L from rfl, hdiff_eq]
    exact (abs_add_le _ _).trans_lt (by linarith [hIoc_bd, hIoi_bd, h4_lt])
  exact tendsto_nhds_unique hAbel fresnel_exp_limit

private noncomputable def kernelAntideriv52 (w : ℝ) : ℝ :=
  -(3 / (16 * π ^ 3)) * w ^ (-(1 / 4 : ℝ)) * Real.sin (4 * π * Real.sqrt w) +
    (3 / (8 * π ^ 2 * Real.sqrt π)) * ∫ t in (0 : ℝ)..Real.sqrt (4 * π * Real.sqrt w), Real.cos (t ^ 2)

private lemma kernelAntideriv52_eq {X : ℝ} (hX : 0 ≤ X) :
    ∫ w in Ioc (0 : ℝ) X, w ^ (1 / 4 : ℝ) * phi52 w = kernelAntideriv52 X := by
  rcases eq_or_lt_of_le hX with rfl | hXpos
  · simp [kernelAntideriv52]
  have hcos_int : Continuous (fun y : ℝ => ∫ t in (0 : ℝ)..y, Real.cos (t ^ 2)) :=
    intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => (by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable (μ := volume) a b) 0
  have hder : ∀ w ∈ Ioi (0 : ℝ),
      HasDerivAt kernelAntideriv52 (w ^ (1 / 4 : ℝ) * phi52 w) w := by
    intro w (hw : 0 < w)
    have hsqw : HasDerivAt Real.sqrt (1 / (2 * √w)) w := Real.hasDerivAt_sqrt hw.ne'
    have h4sqw : HasDerivAt (fun x => 4 * π * √x) (2 * π / √w) w :=
      (hsqw.const_mul (4 * π)).congr_deriv (by field_simp [(Real.sqrt_pos.mpr hw).ne']; ring)
    have hsin : HasDerivAt (fun x => Real.sin (4 * π * √x))
        (Real.cos (4 * π * √w) * (2 * π / √w)) w := by
      have hd := (Real.hasDerivAt_sin (4 * π * √w)).comp w h4sqw
      simpa [Function.comp_def] using hd
    have hpow : HasDerivAt (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (-(1 / 4 : ℝ) * w ^ (-(5 / 4 : ℝ))) w :=
      (Real.hasDerivAt_rpow_const (Or.inl hw.ne') (p := -(1 / 4 : ℝ))).congr_deriv (by norm_num)
    have hT1 : HasDerivAt (fun x => -(3 / (16 * π ^ 3)) * x ^ (-(1 / 4 : ℝ)) * Real.sin (4 * π * √x))
        ((3 / (64 * π ^ 3)) * w ^ (-(5 / 4 : ℝ)) * Real.sin (4 * π * √w) -
          (3 / (8 * π ^ 2)) * w ^ (-(3 / 4 : ℝ)) * Real.cos (4 * π * √w)) w := by
      have hd := (hpow.const_mul (-(3 / (16 * π ^ 3)))).mul hsin
      have hw_sq : √w = w ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow w
      have hw_rel : w ^ (-(1 / 4 : ℝ)) / √w = w ^ (-(3 / 4 : ℝ)) := by
        rw [hw_sq, div_eq_mul_inv, ← Real.rpow_neg hw.le, ← Real.rpow_add hw]
        congr 1; norm_num
      refine hd.congr_deriv ?_
      calc (-(3 / (16 * π ^ 3)) * (-(1 / 4 : ℝ) * w ^ (-(5 / 4 : ℝ))) * Real.sin (4 * π * √w) +
              -(3 / (16 * π ^ 3)) * w ^ (-(1 / 4 : ℝ)) * (Real.cos (4 * π * √w) * (2 * π / √w)))
          = (3 / (64 * π ^ 3)) * w ^ (-(5 / 4 : ℝ)) * Real.sin (4 * π * √w) -
              (3 / (8 * π ^ 2)) * (w ^ (-(1 / 4 : ℝ)) / √w) * Real.cos (4 * π * √w) := by
            field_simp [Real.pi_pos.ne']; ring
        _ = (3 / (64 * π ^ 3)) * w ^ (-(5 / 4 : ℝ)) * Real.sin (4 * π * √w) -
              (3 / (8 * π ^ 2)) * w ^ (-(3 / 4 : ℝ)) * Real.cos (4 * π * √w) := by rw [hw_rel]
    have hR : HasDerivAt (fun x => Real.sqrt (4 * π * √x)) ((√π / 2) * w ^ (-(3 / 4 : ℝ))) w := by
      have hpos4 : 0 < 4 * π * √w := by positivity
      have hd := (Real.hasDerivAt_sqrt hpos4.ne').comp w h4sqw
      have h4_eq : Real.sqrt (4 * π * √w) = 2 * √π * w ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
          Real.sqrt_eq_rpow w, Real.sqrt_eq_rpow (w ^ (1 / 2 : ℝ)), ← Real.rpow_mul hw.le]
        norm_num
      have hw_rel2 : √w * w ^ (1 / 4 : ℝ) = w ^ (3 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow w, ← Real.rpow_add hw]; norm_num
      have hpi_sq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
      refine hd.congr_deriv ?_
      rw [h4_eq, one_div]
      calc (2 * (2 * √π * w ^ (1 / 4 : ℝ)))⁻¹ * (2 * π / √w)
          = (2 * (√π * √π)) / (4 * √π * (√w * w ^ (1 / 4 : ℝ))) := by rw [hpi_sq]; ring
        _ = (√π / 2) * (w ^ (3 / 4 : ℝ))⁻¹ := by
            rw [hw_rel2]; field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']; norm_num
        _ = (√π / 2) * w ^ (-(3 / 4 : ℝ)) := by rw [Real.rpow_neg hw.le]
    have hF_cos : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, Real.cos (t ^ 2))
        (Real.cos ((Real.sqrt (4 * π * √w)) ^ 2)) (Real.sqrt (4 * π * √w)) :=
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).integral_hasStrictDerivAt
        0 (Real.sqrt (4 * π * √w))).hasDerivAt
    have hT2 : HasDerivAt
        (fun x => (3 / (8 * π ^ 2 * Real.sqrt π)) * ∫ t in (0 : ℝ)..Real.sqrt (4 * π * √x), Real.cos (t ^ 2))
        ((3 / (16 * π ^ 2)) * w ^ (-(3 / 4 : ℝ)) * Real.cos (4 * π * √w)) w := by
      have hd := (hF_cos.comp w hR).const_mul (3 / (8 * π ^ 2 * Real.sqrt π))
      rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * π * √w)] at hd
      exact hd.congr_deriv (by field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']; ring)
    refine (hT1.add hT2).congr_deriv (Eq.symm ?_)
    rw [phi52_closed hw]
    have hw_14 : w ^ (1 / 4 : ℝ) * ((√w) ^ 3)⁻¹ = w ^ (-(5 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow w, ← Real.rpow_natCast (w ^ (1 / 2 : ℝ)) 3, ← Real.rpow_mul hw.le,
        ← Real.rpow_neg hw.le, ← Real.rpow_add hw]; norm_num
    have hw_34 : w ^ (1 / 4 : ℝ) * √w * ((√w) ^ 3)⁻¹ = w ^ (-(3 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow w, ← Real.rpow_natCast (w ^ (1 / 2 : ℝ)) 3, ← Real.rpow_mul hw.le,
        ← Real.rpow_neg hw.le, ← Real.rpow_add hw, ← Real.rpow_add hw]; norm_num
    have hpow3 : (4 * π * √w) ^ 3 = 64 * π ^ 3 * (√w) ^ 3 := by ring
    rw [hpow3]
    calc w ^ (1 / 4 : ℝ) * (3 * (Real.sin (4 * π * √w) - 4 * π * √w * Real.cos (4 * π * √w)) / (64 * π ^ 3 * (√w) ^ 3))
        = (3 / (64 * π ^ 3)) * (w ^ (1 / 4 : ℝ) * ((√w) ^ 3)⁻¹) * Real.sin (4 * π * √w) -
            (3 / (16 * π ^ 2)) * (w ^ (1 / 4 : ℝ) * √w * ((√w) ^ 3)⁻¹) * Real.cos (4 * π * √w) := by
          field_simp [Real.pi_pos.ne', (Real.sqrt_pos.mpr hw).ne']; ring
      _ = (3 / (64 * π ^ 3)) * w ^ (-(5 / 4 : ℝ)) * Real.sin (4 * π * √w) -
            (3 / (16 * π ^ 2)) * w ^ (-(3 / 4 : ℝ)) * Real.cos (4 * π * √w) := by
          rw [hw_14, hw_34]
      _ = (3 / (64 * π ^ 3) * w ^ (-(5 / 4 : ℝ)) * Real.sin (4 * π * √w) -
            3 / (8 * π ^ 2) * w ^ (-(3 / 4 : ℝ)) * Real.cos (4 * π * √w)) +
            3 / (16 * π ^ 2) * w ^ (-(3 / 4 : ℝ)) * Real.cos (4 * π * √w) := by ring
  have hker_int : IntervalIntegrable (fun w : ℝ => w ^ (1 / 4 : ℝ) * phi52 w) volume 0 X := by
    refine ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1 / 4)).norm).mono_fun ?_ ?_
    · have hc : ContinuousOn (fun w : ℝ => w ^ (1 / 4 : ℝ) * phi52 w) (Ioi 0) :=
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (ne_of_gt (mem_Ioi.mp hw))).mul
          phi52_cont.continuousOn
      exact (hc.aestronglyMeasurable measurableSet_Ioi).mono_measure
        (Measure.restrict_mono (by intro w hw; rw [Set.uIoc_of_le hXpos.le] at hw; exact hw.1) le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with w hw
      rw [Set.uIoc_of_le hXpos.le] at hw
      simp_rw [Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hw.1.le _),
        abs_of_nonneg (Real.rpow_nonneg hw.1.le _)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hw.1.le _) (phi52_abs_le w)
  have hmem : Ioo (0 : ℝ) X ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin.mpr ⟨Iio X, isOpen_Iio, hXpos, fun x hx => ⟨hx.2, hx.1⟩⟩
  have hlim_int : Tendsto (fun a : ℝ => ∫ w in a..X, w ^ (1 / 4 : ℝ) * phi52 w) (𝓝[>] 0)
      (𝓝 (∫ w in (0 : ℝ)..X, w ^ (1 / 4 : ℝ) * phi52 w)) := by
    have hp : ContinuousOn (fun b : ℝ => ∫ w in (0 : ℝ)..b, w ^ (1 / 4 : ℝ) * phi52 w) (uIcc 0 X) :=
      intervalIntegral.continuousOn_primitive_interval' hker_int left_mem_uIcc
    rw [Set.uIcc_of_le hXpos.le] at hp
    have ht0 : Tendsto (fun a : ℝ => ∫ w in (0 : ℝ)..a, w ^ (1 / 4 : ℝ) * phi52 w) (𝓝[>] 0) (𝓝 0) := by
      have hc0 := (hp 0 (left_mem_Icc.mpr hXpos.le)).tendsto
      rw [intervalIntegral.integral_same] at hc0
      exact hc0.mono_left (le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr
        (mem_of_superset hmem Ioo_subset_Icc_self)))
    have heq : (fun a : ℝ => ∫ w in a..X, w ^ (1 / 4 : ℝ) * phi52 w) =ᶠ[𝓝[>] 0]
        fun a : ℝ => (∫ w in (0 : ℝ)..X, w ^ (1 / 4 : ℝ) * phi52 w) -
          ∫ w in (0 : ℝ)..a, w ^ (1 / 4 : ℝ) * phi52 w := by
      filter_upwards [hmem] with a ha
      have ha0 : 0 ≤ a := ha.1.le
      have haX : a ≤ X := ha.2.le
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hker_int.mono_set (by rw [Set.uIcc_of_le ha0, Set.uIcc_of_le hXpos.le]; exact Set.Icc_subset_Icc_right haX))
        (hker_int.mono_set (by rw [Set.uIcc_of_le haX, Set.uIcc_of_le hXpos.le]; exact Set.Icc_subset_Icc_left ha0))
      linarith
    simpa using (tendsto_const_nhds.sub ht0).congr' heq.symm
  have hlim_ant : Tendsto (fun a : ℝ => kernelAntideriv52 X - kernelAntideriv52 a) (𝓝[>] 0)
      (𝓝 (kernelAntideriv52 X)) := by
    have hA0 : Tendsto kernelAntideriv52 (𝓝[>] 0) (𝓝 0) := by
      have ht1 : Tendsto (fun w : ℝ => -(3 / (16 * π ^ 3)) * w ^ (-(1 / 4 : ℝ)) * Real.sin (4 * π * √w))
          (𝓝[>] 0) (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun w : ℝ => (3 / (4 * π ^ 2)) * w ^ (1 / 4 : ℝ)) ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with w (hw : 0 < w)
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 3 / (16 * π ^ 3)),
            abs_of_nonneg (Real.rpow_nonneg hw.le _)]
          have hsin : |Real.sin (4 * π * √w)| ≤ 4 * π * √w :=
            Real.abs_sin_le_abs.trans_eq (abs_of_nonneg (by positivity))
          have hmul : w ^ (-(1 / 4 : ℝ)) * √w = w ^ (1 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hw]; norm_num
          calc (3 / (16 * π ^ 3)) * w ^ (-(1 / 4 : ℝ)) * |Real.sin (4 * π * √w)|
              ≤ (3 / (16 * π ^ 3)) * w ^ (-(1 / 4 : ℝ)) * (4 * π * √w) := by gcongr
            _ = (3 / (4 * π ^ 2)) * w ^ (1 / 4 : ℝ) := by rw [← hmul]; field_simp [Real.pi_pos.ne']; ring
        · have hc : ContinuousAt (fun w : ℝ => (3 / (4 * π ^ 2)) * w ^ (1 / 4 : ℝ)) 0 :=
            continuousAt_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num))).continuousAt
          have ht := hc.tendsto
          rw [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero] at ht
          exact ht.mono_left nhdsWithin_le_nhds
      have ht2_in : Tendsto (fun w : ℝ => Real.sqrt (4 * π * √w)) (𝓝[>] 0) (𝓝 0) := by
        have hc : ContinuousAt (fun w : ℝ => Real.sqrt (4 * π * √w)) 0 := by fun_prop
        have ht := hc.tendsto
        simp only [Real.sqrt_zero, mul_zero] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      have ht2 : Tendsto (fun w : ℝ => (3 / (8 * π ^ 2 * √π)) *
          ∫ t in (0 : ℝ)..Real.sqrt (4 * π * √w), Real.cos (t ^ 2)) (𝓝[>] 0) (𝓝 0) := by
        have hc := ((hcos_int.continuousAt.tendsto.comp ht2_in).const_mul (3 / (8 * π ^ 2 * √π)))
        simpa only [Function.comp_def, intervalIntegral.integral_same, mul_zero] using hc
      change Tendsto (fun w : ℝ =>
          -(3 / (16 * π ^ 3)) * w ^ (-(1 / 4 : ℝ)) * Real.sin (4 * π * √w) +
            (3 / (8 * π ^ 2 * √π)) * ∫ t in (0 : ℝ)..Real.sqrt (4 * π * √w), Real.cos (t ^ 2))
        (𝓝[>] 0) (𝓝 0)
      simpa only [zero_add] using ht1.add ht2
    simpa only [sub_zero] using tendsto_const_nhds.sub hA0
  have heq_ftc : (fun a : ℝ => ∫ w in a..X, w ^ (1 / 4 : ℝ) * phi52 w) =ᶠ[𝓝[>] 0]
      fun a : ℝ => kernelAntideriv52 X - kernelAntideriv52 a := by
    filter_upwards [hmem] with a ha
    have h1 : ∀ w ∈ uIcc a X, HasDerivAt kernelAntideriv52 (w ^ (1 / 4 : ℝ) * phi52 w) w := fun w hw => by
      rw [Set.uIcc_of_le ha.2.le] at hw
      exact hder w (lt_of_lt_of_le ha.1 hw.1)
    have h2 : IntervalIntegrable (fun w : ℝ => w ^ (1 / 4 : ℝ) * phi52 w) volume a X :=
      hker_int.mono_set (by rw [Set.uIcc_of_le hXpos.le, Set.uIcc_of_le ha.2.le]; exact Set.Icc_subset_Icc_left ha.1.le)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2
  rw [← intervalIntegral.integral_of_le hXpos.le]
  exact tendsto_nhds_unique (hlim_int.congr' heq_ftc) hlim_ant

private lemma coeff52_eq :
    (2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2) = (16 * √2 / 3) * π ^ 2 := by
  have hG32 : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * √π := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
  have hG52 : Real.Gamma (5 / 2 : ℝ) = (3 / 4 : ℝ) * √π := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), hG32]; ring
  have hnum : (2 * π) ^ (5 / 2 : ℝ) = 4 * √2 * π ^ 2 * √π := by
    rw [show (5 / 2 : ℝ) = (2 : ℝ) + (1 / 2 : ℝ) by norm_num, Real.rpow_add (by positivity),
      Real.rpow_two, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hnum, hG52]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']; norm_num


private lemma integral_cos_sq_abs_le {R : ℝ} (hR : 0 ≤ R) :
    |∫ t in (0 : ℝ)..R, Real.cos (t ^ 2)| ≤ 2 := by
  rcases le_total R 1 with hR1 | h1R
  · have hint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 R :=
      continuous_const.intervalIntegrable 0 R
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => Real.cos (t ^ 2)) hR
      (Eventually.of_forall fun _ _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _) hint
    rw [Real.norm_eq_abs, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hnorm
    linarith
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (t ^ 2)).intervalIntegrable 1 R)]
    have h01 : |∫ t in (0 : ℝ)..1, Real.cos (t ^ 2)| ≤ 1 := by
      have hint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
        continuous_const.intervalIntegrable 0 1
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => Real.cos (t ^ 2)) zero_le_one
        (Eventually.of_forall fun _ _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _) hint
      simpa [Real.norm_eq_abs] using hnorm
    have h1R' := integral_cos_sq_tail_bound (le_refl 1) h1R
    rw [div_one] at h1R'
    exact (abs_add_le _ _).trans (by linarith)

/-- Concrete radial Hankel kernel at `c = 5 / 2` (`d = 5`, `J_{3/2}` Bessel kernel),
providing an unconditional non-vacuity witness for `HankelKernelData`. -/
noncomputable def hankelKernel_fiveHalves : HankelKernelData (5 / 2) where
  φ := phi52
  φ_zero := by exact phi52_zero
  φ_cont := by exact phi52_cont
  φ_bound := by exact ⟨1, zero_le_one, fun w _ => phi52_abs_le w⟩
  antideriv_bound := by
    let C52 : ℝ := (2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)
    refine ⟨C52 * (3 / (4 * π ^ 2) + 3 / (4 * π ^ 2 * Real.sqrt π)), by positivity, fun X hX => ?_⟩
    rw [show (5 / 2 : ℝ) / 2 - 1 = (1 / 4 : ℝ) by norm_num, kernelAntideriv52_eq hX,
      abs_mul, abs_of_pos (div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos (by norm_num)))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    dsimp [kernelAntideriv52]
    have ht1 : |-(3 / (16 * π ^ 3)) * X ^ (-(1 / 4 : ℝ)) * Real.sin (4 * π * √X)| ≤ 3 / (4 * π ^ 2) := by
      rcases eq_or_lt_of_le hX with rfl | hXpos
      · simp; positivity
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 3 / (16 * π ^ 3)),
        abs_of_nonneg (Real.rpow_nonneg hXpos.le _)]
      have hbd : X ^ (-(1 / 4 : ℝ)) * |Real.sin (4 * π * √X)| ≤ 4 * π := by
        rcases le_or_gt X 1 with hX1 | h1X
        · have hsin : |Real.sin (4 * π * √X)| ≤ 4 * π * √X :=
            Real.abs_sin_le_abs.trans_eq (abs_of_nonneg (by positivity))
          have hmul : X ^ (-(1 / 4 : ℝ)) * √X = X ^ (1 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]; norm_num
          have hx14 : X ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hXpos.le hX1 (by norm_num)
          calc X ^ (-(1 / 4 : ℝ)) * |Real.sin (4 * π * √X)|
              ≤ X ^ (-(1 / 4 : ℝ)) * (4 * π * √X) :=
                mul_le_mul_of_nonneg_left hsin (Real.rpow_nonneg hXpos.le _)
            _ = 4 * π * (X ^ (-(1 / 4 : ℝ)) * √X) := by ring
            _ = 4 * π * X ^ (1 / 4 : ℝ) := by rw [hmul]
            _ ≤ 4 * π * 1 := mul_le_mul_of_nonneg_left hx14 (by positivity)
            _ = 4 * π := mul_one _
        · have hx_m : X ^ (-(1 / 4 : ℝ)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos h1X.le (by norm_num)
          have h1pi : (1 : ℝ) ≤ 4 * π := by linarith [Real.pi_gt_three]
          calc X ^ (-(1 / 4 : ℝ)) * |Real.sin (4 * π * √X)|
              ≤ 1 * 1 := mul_le_mul hx_m (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
            _ ≤ 4 * π := by linarith
      calc (3 / (16 * π ^ 3)) * X ^ (-(1 / 4 : ℝ)) * |Real.sin (4 * π * √X)|
          = (3 / (16 * π ^ 3)) * (X ^ (-(1 / 4 : ℝ)) * |Real.sin (4 * π * √X)|) := by ring
        _ ≤ (3 / (16 * π ^ 3)) * (4 * π) := by gcongr
        _ = 3 / (4 * π ^ 2) := by field_simp [Real.pi_pos.ne']; ring
    have ht2 : |(3 / (8 * π ^ 2 * √π)) * ∫ t in (0 : ℝ)..√(4 * π * √X), Real.cos (t ^ 2)| ≤
        3 / (4 * π ^ 2 * √π) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / (8 * π ^ 2 * √π))]
      calc (3 / (8 * π ^ 2 * √π)) * |∫ t in (0 : ℝ)..√(4 * π * √X), Real.cos (t ^ 2)|
          ≤ (3 / (8 * π ^ 2 * √π)) * 2 := by gcongr; exact integral_cos_sq_abs_le (Real.sqrt_nonneg _)
        _ = 3 / (4 * π ^ 2 * √π) := by ring
    exact (abs_add_le _ _).trans (add_le_add ht1 ht2)
  antideriv_tendsto := by
    have hev : (fun X : ℝ => (2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2) *
        ∫ w in Ioc (0 : ℝ) X, w ^ ((5 / 2 : ℝ) / 2 - 1) * phi52 w) =ᶠ[atTop]
        fun X : ℝ => ((16 * √2 / 3) * π ^ 2) * kernelAntideriv52 X := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
      rw [show (5 / 2 : ℝ) / 2 - 1 = (1 / 4 : ℝ) by norm_num, kernelAntideriv52_eq hX, coeff52_eq]
    refine Tendsto.congr' hev.symm ?_
    have ht1 : Tendsto (fun X : ℝ => -(3 / (16 * π ^ 3)) * X ^ (-(1 / 4 : ℝ)) * Real.sin (4 * π * √X))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun X : ℝ => (3 / (16 * π ^ 3)) * X ^ (-(1 / 4 : ℝ))) ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 3 / (16 * π ^ 3)),
          abs_of_nonneg (Real.rpow_nonneg hX.le _)]
        calc (3 / (16 * π ^ 3)) * X ^ (-(1 / 4 : ℝ)) * |Real.sin (4 * π * √X)|
            ≤ (3 / (16 * π ^ 3)) * X ^ (-(1 / 4 : ℝ)) * 1 := by gcongr; exact Real.abs_sin_le_one _
          _ = (3 / (16 * π ^ 3)) * X ^ (-(1 / 4 : ℝ)) := mul_one _
      · have hr : Tendsto (fun X : ℝ => X ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
          tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
        simpa using hr.const_mul (3 / (16 * π ^ 3))
    have ht2_arg : Tendsto (fun X : ℝ => Real.sqrt (4 * π * √X)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp
        (Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 4 * π) Real.tendsto_sqrt_atTop)
    have ht2 : Tendsto (fun X : ℝ => (3 / (8 * π ^ 2 * √π)) *
        ∫ t in (0 : ℝ)..Real.sqrt (4 * π * √X), Real.cos (t ^ 2))
        atTop (𝓝 ((3 / (8 * π ^ 2 * √π)) * √(π / 8))) :=
      (tendsto_integral_cos_sq.comp ht2_arg).const_mul _
    have hsum : Tendsto kernelAntideriv52 atTop (𝓝 (0 + (3 / (8 * π ^ 2 * √π)) * √(π / 8))) :=
      ht1.add ht2
    rw [zero_add] at hsum
    have hprod : ((16 * √2 / 3) * π ^ 2) * ((3 / (8 * π ^ 2 * √π)) * √(π / 8)) = 1 := by
      have hsq : √(π / 8) = √π / (2 * √2) := by
        have h22 : (2 * √2) ^ 2 = (8 : ℝ) := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
        rw [Real.sqrt_div Real.pi_pos.le, show (8 : ℝ) = (2 * √2) ^ 2 from h22.symm,
          Real.sqrt_sq (by positivity)]
      rw [hsq]
      field_simp [Real.pi_pos.ne', (Real.sqrt_pos.mpr Real.pi_pos).ne',
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
      ring
    rw [← hprod]
    exact hsum.const_mul _


private noncomputable def gaussPhi (k : ℝ) (n : ℕ) : ℂ :=
  ∫ u : ℝ, (u : ℂ) ^ n * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ))

private lemma gaussPhi_integrable (k : ℝ) (n : ℕ) :
    Integrable (fun u : ℝ =>
      (u : ℂ) ^ n * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ))) := by
  let C : ℝ := 1 + (4 : ℝ) ^ n * (n.factorial : ℝ)
  refine ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun u => ?_)
  have hnorm_exp : ‖Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ))‖ =
      Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by
    rw [Complex.norm_exp, show -(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ) =
      (((-(1 / 2 : ℝ) * u ^ 2 : ℝ) : ℂ)) + ((k * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
    congr 1
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs, hnorm_exp]
  have hpow : |u| ^ n ≤ C * Real.exp ((1 / 4 : ℝ) * u ^ 2) := by
    have h2 : |u| ^ n ≤ 1 + |u| ^ (2 * n) := by
      rcases le_or_gt |u| 1 with hu1 | h1u
      · exact (pow_le_one₀ (abs_nonneg u) hu1).trans (le_add_of_nonneg_right (by positivity))
      · have hle : |u| ^ n ≤ |u| ^ (2 * n) := pow_le_pow_right₀ h1u.le (by omega)
        exact hle.trans (le_add_of_nonneg_left zero_le_one)
    have hfact : ((1 / 4 : ℝ) * u ^ 2) ^ n / (n.factorial : ℝ) ≤ Real.exp ((1 / 4 : ℝ) * u ^ 2) :=
      Real.pow_div_factorial_le_exp ((1 / 4 : ℝ) * u ^ 2) (by positivity) n
    have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have h2n : |u| ^ (2 * n) ≤ (4 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp ((1 / 4 : ℝ) * u ^ 2) := by
      rw [pow_mul, sq_abs]
      have hmul : ((1 / 4 : ℝ) * u ^ 2) ^ n ≤ (n.factorial : ℝ) * Real.exp ((1 / 4 : ℝ) * u ^ 2) := by
        rw [div_le_iff₀ hfac_pos, mul_comm _ (n.factorial : ℝ)] at hfact
        exact hfact
      rw [mul_pow, show ((1 / 4 : ℝ) ^ n) = ((4 : ℝ) ^ n)⁻¹ by rw [one_div, inv_pow]] at hmul
      calc (u ^ 2) ^ n = (4 : ℝ) ^ n * ((4 ^ n)⁻¹ * (u ^ 2) ^ n) := by field_simp
        _ ≤ (4 : ℝ) ^ n * ((n.factorial : ℝ) * Real.exp ((1 / 4 : ℝ) * u ^ 2)) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = (4 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp ((1 / 4 : ℝ) * u ^ 2) := by ring
    have hexp1 : (1 : ℝ) ≤ Real.exp ((1 / 4 : ℝ) * u ^ 2) := Real.one_le_exp (by positivity)
    calc |u| ^ n ≤ 1 + (4 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp ((1 / 4 : ℝ) * u ^ 2) := by linarith
      _ ≤ 1 * Real.exp ((1 / 4 : ℝ) * u ^ 2) +
            (4 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp ((1 / 4 : ℝ) * u ^ 2) := by linarith
      _ = C * Real.exp ((1 / 4 : ℝ) * u ^ 2) := by dsimp [C]; ring
  have hexp_mul : Real.exp ((1 / 4 : ℝ) * u ^ 2) * Real.exp (-(1 / 2 : ℝ) * u ^ 2) =
      Real.exp (-(1 / 4 : ℝ) * u ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |u| ^ n * Real.exp (-(1 / 2 : ℝ) * u ^ 2)
      ≤ C * Real.exp ((1 / 4 : ℝ) * u ^ 2) * Real.exp (-(1 / 2 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = C * Real.exp (-(1 / 4 : ℝ) * u ^ 2) := by rw [mul_assoc, hexp_mul]

private lemma gaussPhi_zero (k : ℝ) :
    gaussPhi k 0 = ((√(2 * π) : ℝ) : ℂ) * Complex.exp (-((k : ℂ) ^ 2 / 2)) := by
  unfold gaussPhi
  simp only [pow_zero, one_mul]
  have hsq : ∀ u : ℝ, -(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ) =
      -(1 / 2 : ℂ) * ((u : ℂ) + (-k : ℝ) * Complex.I) ^ 2 - (k : ℂ) ^ 2 / 2 := fun u => by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    calc -(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ)
        = -(1 / 2 : ℂ) * ((u : ℂ) + (-k : ℝ) * Complex.I) ^ 2 +
            (1 / 2 : ℂ) * ((-k : ℝ) * Complex.I) ^ 2 := by
          push_cast; ring
      _ = -(1 / 2 : ℂ) * ((u : ℂ) + (-k : ℝ) * Complex.I) ^ 2 - (k : ℂ) ^ 2 / 2 := by
          rw [mul_pow, hI]; push_cast; ring
  have hcongr : (fun u : ℝ => Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ))) =
      fun u : ℝ => Complex.exp (-((k : ℂ) ^ 2 / 2)) *
        Complex.exp (-(1 / 2 : ℂ) * ((u : ℂ) + (-k : ℝ) * Complex.I) ^ 2) := by
    ext u; rw [hsq, sub_eq_add_neg, add_comm, Complex.exp_add]
  rw [hcongr, integral_const_mul]
  have hg := GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I
    (b := (1 / 2 : ℂ)) (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re) (-k)
  rw [hg]
  have hpi : ((π : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = ((√(2 * π) : ℝ) : ℂ) := by
    have : (π : ℂ) / (1 / 2 : ℂ) = (((2 * π : ℝ)) : ℂ) := by push_cast; ring
    rw [this, show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num,
      ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * π), ← Real.sqrt_eq_rpow]
  rw [hpi, mul_comm]

private lemma gaussPhi_succ (k : ℝ) :
    ∀ n : ℕ, gaussPhi k (n + 1) =
      (Complex.I * (k : ℂ)) * gaussPhi k n +
        if n = 0 then 0 else (n : ℂ) * gaussPhi k (n - 1) := by
  intro n
  let v : ℝ → ℂ := fun u => Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (k : ℂ) * (u : ℂ))
  let v' : ℝ → ℂ := fun u => (-(u : ℂ) + Complex.I * (k : ℂ)) * v u
  have hv_der : ∀ u : ℝ, HasDerivAt v (v' u) u := fun u => by
    have hpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (u : ℂ)) u := by
      simpa using ((hasDerivAt_pow 2 (u : ℂ)).comp_ofReal)
    have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have hexp_arg : HasDerivAt (fun x : ℝ => -(1 / 2 : ℂ) * (x : ℂ) ^ 2 + Complex.I * (k : ℂ) * (x : ℂ))
        (-(u : ℂ) + Complex.I * (k : ℂ)) u :=
      ((hpow.const_mul (-(1 / 2 : ℂ))).add (hid.const_mul (Complex.I * (k : ℂ)))).congr_deriv (by ring)
    exact ((Complex.hasDerivAt_exp _).comp u hexp_arg).congr_deriv (by dsimp [v, v']; ring)
  have hu_der : ∀ u : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) ^ n)
      (if n = 0 then 0 else (n : ℂ) * (u : ℂ) ^ (n - 1)) u := fun u => by
    cases n with
    | zero => simpa using hasDerivAt_const u (1 : ℂ)
    | succ m =>
      simpa [Nat.succ_ne_zero] using ((hasDerivAt_pow (m + 1) (u : ℂ)).comp_ofReal)
  have huv' : Integrable (fun u : ℝ => (u : ℂ) ^ n * v' u) := by
    have : (fun u : ℝ => (u : ℂ) ^ n * v' u) =
        fun u : ℝ => -((u : ℂ) ^ (n + 1) * v u) + (Complex.I * (k : ℂ)) * ((u : ℂ) ^ n * v u) := by
      ext u; dsimp [v']; rw [pow_succ]; ring
    rw [this]
    exact (gaussPhi_integrable k (n + 1)).neg.add ((gaussPhi_integrable k n).const_mul _)
  have hu'v : Integrable (fun u : ℝ => (if n = 0 then 0 else (n : ℂ) * (u : ℂ) ^ (n - 1)) * v u) := by
    cases n with
    | zero => simp only [↓reduceIte, zero_mul]; exact integrable_zero _ _ _
    | succ m =>
      refine ((gaussPhi_integrable k m).const_mul ((m + 1 : ℕ) : ℂ)).congr (Eventually.of_forall fun u => ?_)
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; dsimp [v]; ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun u _ => hu_der u) (fun u _ => hv_der u) huv' hu'v (gaussPhi_integrable k n)
  have h1 : ∫ u : ℝ, (u : ℂ) ^ n * v' u = -gaussPhi k (n + 1) + (Complex.I * (k : ℂ)) * gaussPhi k n := by
    have heq : (fun u : ℝ => (u : ℂ) ^ n * v' u) =
        fun u : ℝ => -((u : ℂ) ^ (n + 1) * v u) + (Complex.I * (k : ℂ)) * ((u : ℂ) ^ n * v u) := by
      ext u; dsimp [v']; rw [pow_succ]; ring
    have hneg_i : Integrable (fun u : ℝ => -((u : ℂ) ^ (n + 1) * v u)) :=
      (gaussPhi_integrable k (n + 1)).neg
    have hmul_i : Integrable (fun u : ℝ => (Complex.I * (k : ℂ)) * ((u : ℂ) ^ n * v u)) :=
      (gaussPhi_integrable k n).const_mul _
    rw [heq, integral_add hneg_i hmul_i, integral_neg, integral_const_mul]
    rfl
  have h2 : ∫ u : ℝ, (if n = 0 then 0 else (n : ℂ) * (u : ℂ) ^ (n - 1)) * v u =
      if n = 0 then 0 else (n : ℂ) * gaussPhi k (n - 1) := by
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, mul_assoc]
      rw [integral_const_mul]
      rfl
  rw [h1, h2] at hibp
  linear_combination -hibp

private lemma gaussPhi_four_re (k : ℝ) :
    (gaussPhi k 4).re = √(2 * π) * (k ^ 4 - 6 * k ^ 2 + 3) * Real.exp (-k ^ 2 / 2) := by
  have h1 : gaussPhi k 1 = (Complex.I * k) * gaussPhi k 0 := by simp [gaussPhi_succ]
  have h2 : gaussPhi k 2 = (1 - (k : ℂ) ^ 2) * gaussPhi k 0 := by
    rw [gaussPhi_succ k 1]; simp only [one_ne_zero, ↓reduceIte, Nat.cast_one, one_mul, Nat.sub_self, h1]
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (k : ℂ) ^ 2 * gaussPhi k 0 * this
  have h3 : gaussPhi k 3 = (Complex.I * (3 * (k : ℂ) - (k : ℂ) ^ 3)) * gaussPhi k 0 := by
    rw [gaussPhi_succ k 2]; simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, h1, h2]; ring
  have h4 : gaussPhi k 4 = ((k : ℂ) ^ 4 - 6 * (k : ℂ) ^ 2 + 3) * gaussPhi k 0 := by
    rw [gaussPhi_succ k 3]; simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, h2, h3]
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination ((3 * (k : ℂ) ^ 2 - (k : ℂ) ^ 4) * gaussPhi k 0) * this
  rw [h4, gaussPhi_zero]
  have hre : (((k : ℂ) ^ 4 - 6 * (k : ℂ) ^ 2 + 3) * (((√(2 * π) : ℝ) : ℂ) *
      Complex.exp (-((k : ℂ) ^ 2 / 2)))).re =
      √(2 * π) * (k ^ 4 - 6 * k ^ 2 + 3) * Real.exp (-k ^ 2 / 2) := by
    rw [show -((k : ℂ) ^ 2 / 2) = (((-k ^ 2 / 2 : ℝ) : ℂ)) by push_cast; ring, ← Complex.ofReal_exp]
    have heq : (((k : ℂ) ^ 4 - 6 * (k : ℂ) ^ 2 + 3) * (((√(2 * π) : ℝ) : ℂ) *
        ((Real.exp (-k ^ 2 / 2) : ℝ) : ℂ))) =
        ((√(2 * π) * (k ^ 4 - 6 * k ^ 2 + 3) * Real.exp (-k ^ 2 / 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [heq, Complex.ofReal_re]
  exact hre

private lemma hankelTransform_exp_fiveHalves {α : ℝ} (hα : 0 < α) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    hankelTransform (5 / 2) hankelKernel_fiveHalves (fun s => Real.exp (-2 * π * α * s)) Δ =
      α ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * Δ / α) := by
  unfold hankelTransform
  change ∫ s in Ioi (0 : ℝ), Real.exp (-2 * π * α * s) * hankelRho0 (5 / 2) s * phi52 (Δ * s) = _
  rcases eq_or_lt_of_le hΔ with rfl | hΔpos
  · simp only [zero_mul, phi52_zero, mul_one]
    rw [mul_zero, zero_div, Real.exp_zero, mul_one]
    unfold hankelRho0
    have hcongr : ∫ s in Ioi (0 : ℝ), Real.exp (-2 * π * α * s) * ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2) *
        s ^ ((5 / 2 : ℝ) - 1)) =
        ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)) *
          ∫ s in Ioi (0 : ℝ), s ^ ((5 / 2 : ℝ) - 1) * Real.exp (-(2 * π * α * s)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
    rw [hcongr, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 5 / 2) (by positivity)]
    have hGne : Real.Gamma (5 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have hmul_pow : (1 / (2 * π * α)) ^ (5 / 2 : ℝ) = (2 * π) ^ (-(5 / 2 : ℝ)) * α ^ (-(5 / 2 : ℝ)) := by
      rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) hα.le]
    have hinv : (2 * π) ^ (5 / 2 : ℝ) * (2 * π) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 2 * π), add_neg_cancel, Real.rpow_zero]
    rw [hmul_pow]
    calc (2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2) * (((2 * π) ^ (-(5 / 2 : ℝ)) * α ^ (-(5 / 2 : ℝ))) * Real.Gamma (5 / 2))
        = (Real.Gamma (5 / 2) / Real.Gamma (5 / 2)) * ((2 * π) ^ (5 / 2 : ℝ) * (2 * π) ^ (-(5 / 2 : ℝ))) * α ^ (-(5 / 2 : ℝ)) := by
          ring
      _ = α ^ (-(5 / 2 : ℝ)) := by rw [div_self hGne, hinv]; ring
  · have hr_int : IntegrableOn (fun s : ℝ => Real.exp (-2 * π * α * s) * hankelRho0 (5 / 2) s) (Ioi 0) := by
      unfold hankelRho0
      have hdom : IntegrableOn (fun s : ℝ => ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)) *
          (s ^ (5 / 2 - 1 : ℝ) * Real.exp (-(2 * π * α) * s))) (Ioi 0) :=
        (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 5 / 2 - 1)
          (by positivity : 0 < 2 * π * α)).const_mul _
      exact hdom.congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
    let F : ℝ → ℝ → ℝ := fun s t =>
      Real.exp (-2 * π * α * s) * hankelRho0 (5 / 2) s * ((3 / 2 : ℝ) * (1 - t ^ 2) * Real.cos (4 * π * √(Δ * s) * t))
    let μ := volume.restrict (Ioi (0 : ℝ))
    let ν := volume.restrict (Ioc (0 : ℝ) 1)
    have hprod : μ.prod ν = volume.restrict (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) 1) := by
      dsimp [μ, ν]; rw [Measure.volume_eq_prod ℝ ℝ]
      exact Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (Ioi (0 : ℝ)) (Ioc (0 : ℝ) 1)
    have hF_aesm : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := by
      rw [hprod]
      refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioc)
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-2 * π * α * p.1) * hankelRho0 (5 / 2) p.1)
          (Ioi 0 ×ˢ Ioc 0 1) :=
        (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-2 * π * α * p.1)).continuousOn.mul
          ((continuousOn_hankelRho0 (5 / 2)).comp continuous_fst.continuousOn fun _ hp => hp.1)
      have h2 : ContinuousOn (fun p : ℝ × ℝ =>
          (3 / 2 : ℝ) * (1 - p.2 ^ 2) * Real.cos (4 * π * √(Δ * p.1) * p.2)) (Ioi 0 ×ˢ Ioc 0 1) :=
        (by fun_prop : Continuous fun p : ℝ × ℝ =>
          (3 / 2 : ℝ) * (1 - p.2 ^ 2) * Real.cos (4 * π * √(Δ * p.1) * p.2)).continuousOn
      exact h1.mul h2
    have hF_int : Integrable (Function.uncurry F) (μ.prod ν) := by
      have hnu : Integrable (fun _ : ℝ => (3 / 2 : ℝ)) ν := integrable_const _
      refine (hr_int.mul_prod hnu).mono' hF_aesm ?_
      rw [hprod]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
      dsimp [F, Function.uncurry]
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hankelRho0_nonneg (by norm_num) hp.1.le))]
      have h1t : 0 ≤ 1 - p.2 ^ 2 := by nlinarith [hp.2.1, hp.2.2]
      have h1t_le : |1 - p.2 ^ 2| ≤ 1 := by rw [abs_of_nonneg h1t]; nlinarith [hp.2.1]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      calc Real.exp (-2 * π * α * p.1) * hankelRho0 (5 / 2) p.1 * ((3 / 2) * |1 - p.2 ^ 2| * |Real.cos (4 * π * √(Δ * p.1) * p.2)|)
          ≤ Real.exp (-2 * π * α * p.1) * hankelRho0 (5 / 2) p.1 * ((3 / 2) * 1 * 1) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul_of_nonneg_left h1t_le (by positivity))
                (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity))
              (mul_nonneg (Real.exp_pos _).le (hankelRho0_nonneg (by norm_num) hp.1.le))
        _ = (Real.exp (-2 * π * α * p.1) * hankelRho0 (5 / 2) p.1) * (3 / 2) := by ring
    have hLHS : ∫ s in Ioi (0 : ℝ), Real.exp (-2 * π * α * s) * hankelRho0 (5 / 2) s * phi52 (Δ * s) =
        ∫ s, ∫ t, F s t ∂ν ∂μ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      dsimp [phi52, F]
      rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => by ring
    rw [hLHS, integral_integral_swap hF_int]
    let x : ℝ := 2 * π * Δ / α
    let k : ℝ := 2 * √(π * Δ / α)
    have hk_sq : k ^ 2 = 2 * x := by
      dsimp [k, x]
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hinner : ∀ t ∈ Ioc (0 : ℝ) 1,
        ∫ s in Ioi (0 : ℝ), F s t =
          α ^ (-(5 / 2 : ℝ)) * ((1 - t ^ 2) *
            ((4 * x ^ 2 * t ^ 4 - 12 * x * t ^ 2 + 3) / 2) * Real.exp (-x * t ^ 2)) := by
      intro t _
      have hpull : ∫ s in Ioi (0 : ℝ), F s t =
          ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)) * (3 / 2 : ℝ) * (1 - t ^ 2) *
            ∫ s in Ioi (0 : ℝ), s ^ (3 / 2 : ℝ) * Real.exp (-2 * π * α * s) * Real.cos (4 * π * √(Δ * s) * t) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        dsimp [F]; unfold hankelRho0; rw [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num]; ring
      let σ : ℝ := (√(4 * π * α))⁻¹
      have hσ : 0 < σ := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
      have hσ_sq : 4 * π * α * σ ^ 2 = 1 := by
        dsimp [σ]; rw [inv_pow, Real.sq_sqrt (by positivity)]; field_simp
      have hs_sub : ∫ s in Ioi (0 : ℝ), s ^ (3 / 2 : ℝ) * Real.exp (-2 * π * α * s) * Real.cos (4 * π * √(Δ * s) * t) =
          2 * σ ^ 5 * ∫ u in Ioi (0 : ℝ), u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) := by
        have hr := integral_comp_rpow_Ioi_of_pos
          (g := fun s : ℝ => s ^ (3 / 2 : ℝ) * Real.exp (-2 * π * α * s) * Real.cos (4 * π * √(Δ * s) * t))
          (by norm_num : (0 : ℝ) < 2)
        have hstep1 : ∫ r in Ioi (0 : ℝ), 2 * r ^ 4 * Real.exp (-2 * π * α * r ^ 2) * Real.cos (4 * π * √Δ * t * r) =
            ∫ s in Ioi (0 : ℝ), s ^ (3 / 2 : ℝ) * Real.exp (-2 * π * α * s) * Real.cos (4 * π * √(Δ * s) * t) := by
          rw [← hr]
          refine setIntegral_congr_fun measurableSet_Ioi fun r (hr0 : 0 < r) => ?_
          simp only [smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
          have hr3 : (r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 := by
            rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le,
              show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have hsqrt : √(Δ * r ^ 2) = √Δ * r := by
            rw [Real.sqrt_mul hΔpos.le, Real.sqrt_sq hr0.le]
          rw [hr3, hsqrt]; ring
        rw [← hstep1]
        have hu := integral_comp_mul_right_Ioi'
          (fun r : ℝ => 2 * r ^ 4 * Real.exp (-2 * π * α * r ^ 2) * Real.cos (4 * π * √Δ * t * r)) 0 hσ
        rw [zero_mul, smul_eq_mul] at hu
        calc ∫ r in Ioi (0 : ℝ), 2 * r ^ 4 * Real.exp (-2 * π * α * r ^ 2) * Real.cos (4 * π * √Δ * t * r)
            = σ * ∫ u in Ioi (0 : ℝ), 2 * (u * σ) ^ 4 * Real.exp (-2 * π * α * (u * σ) ^ 2) *
                Real.cos (4 * π * √Δ * t * (u * σ)) := hu.symm
          _ = ∫ u in Ioi (0 : ℝ), σ * (2 * (u * σ) ^ 4 * Real.exp (-2 * π * α * (u * σ) ^ 2) *
                Real.cos (4 * π * √Δ * t * (u * σ))) := (integral_const_mul _ _).symm
          _ = ∫ u in Ioi (0 : ℝ), (2 * σ ^ 5) * (u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u)) := by
              refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
              have hexp_arg : -2 * π * α * (u * σ) ^ 2 = -(1 / 2 : ℝ) * u ^ 2 := by
                calc -2 * π * α * (u * σ) ^ 2 = -(1 / 2 : ℝ) * u ^ 2 * (4 * π * α * σ ^ 2) := by ring
                  _ = -(1 / 2 : ℝ) * u ^ 2 := by rw [hσ_sq, mul_one]
              have hcos_arg : 4 * π * √Δ * t * (u * σ) = k * t * u := by
                dsimp [k, σ]
                have hsq4 : √(4 * π * α) = 2 * √π * √α := by
                  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
                    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
                have hsqd : √(π * Δ / α) = √π * √Δ / √α := by
                  rw [Real.sqrt_div (by positivity), Real.sqrt_mul Real.pi_pos.le]
                have hpi2 : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
                rw [hsq4, hsqd]
                calc 4 * π * √Δ * t * (u * (2 * √π * √α)⁻¹)
                    = 2 * ((√π * √π) * √Δ / (√π * √α)) * t * u := by rw [hpi2]; ring
                  _ = 2 * (√π * √Δ / √α) * t * u := by
                      field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne', (Real.sqrt_pos.mpr hα).ne']
              rw [hexp_arg, hcos_arg]; ring
          _ = 2 * σ ^ 5 * ∫ u in Ioi (0 : ℝ), u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) :=
              integral_const_mul _ _
      have hgauss_half : ∫ u in Ioi (0 : ℝ), u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) =
          (1 / 2 : ℝ) * (gaussPhi (k * t) 4).re := by
        have hint_g := gaussPhi_integrable (k * t) 4
        have hre_g : ∫ u : ℝ, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) =
            (gaussPhi (k * t) 4).re := by
          unfold gaussPhi
          have hcomp : ∫ u : ℝ, Complex.reCLM
              ((u : ℂ) ^ 4 * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ))) =
              Complex.reCLM (∫ u : ℝ,
                (u : ℂ) ^ 4 * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ))) :=
            ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_g
          calc ∫ u : ℝ, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u)
              = ∫ u : ℝ, ((u : ℂ) ^ 4 * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ))).re := by
                refine integral_congr_ae (Eventually.of_forall fun u => ?_)
                dsimp only
                have hexp_eq : Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ)) =
                    ((Real.exp (-(1 / 2 : ℝ) * u ^ 2) : ℝ) : ℂ) *
                      (Complex.cos (((k * t * u : ℝ) : ℂ)) + Complex.sin (((k * t * u : ℝ) : ℂ)) * Complex.I) := by
                  have he1 : -(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ) =
                      (((-(1 / 2 : ℝ) * u ^ 2 : ℝ) : ℂ)) + (((k * t * u : ℝ) : ℂ)) * Complex.I := by
                    push_cast; ring
                  rw [he1, Complex.exp_add_mul_I, ← Complex.ofReal_exp]
                rw [hexp_eq, ← Complex.ofReal_pow, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
                simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
                  zero_mul, sub_zero, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
                ring
            _ = ∫ u : ℝ, Complex.reCLM
                  ((u : ℂ) ^ 4 * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ))) := rfl
            _ = (∫ u : ℝ, (u : ℂ) ^ 4 * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ))).re := hcomp
        have hint_real : Integrable (fun u : ℝ => u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u)) := by
          have := Complex.reCLM.integrable_comp hint_g
          refine this.congr (Eventually.of_forall fun u => ?_)
          change ((u : ℂ) ^ 4 * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ))).re = _
          have hexp_eq : Complex.exp (-(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ)) =
              ((Real.exp (-(1 / 2 : ℝ) * u ^ 2) : ℝ) : ℂ) *
                (Complex.cos (((k * t * u : ℝ) : ℂ)) + Complex.sin (((k * t * u : ℝ) : ℂ)) * Complex.I) := by
            have he1 : -(1 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * ((k * t : ℝ) : ℂ) * (u : ℂ) =
                (((-(1 / 2 : ℝ) * u ^ 2 : ℝ) : ℂ)) + (((k * t * u : ℝ) : ℂ)) * Complex.I := by
              push_cast; ring
            rw [he1, Complex.exp_add_mul_I, ← Complex.ofReal_exp]
          rw [hexp_eq, ← Complex.ofReal_pow, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
          simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
          ring
        have heven : ∫ u : ℝ, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) =
            2 * ∫ u in Ioi (0 : ℝ), u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) := by
          have h1 : Tendsto (fun R : ℝ => ∫ u in -R..R, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u))
              atTop (𝓝 (∫ u : ℝ, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u))) :=
            intervalIntegral_tendsto_integral hint_real tendsto_neg_atTop_atBot tendsto_id
          have h2 : Tendsto (fun R : ℝ => 2 * ∫ u in (0 : ℝ)..R, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u))
              atTop (𝓝 (2 * ∫ u in Ioi (0 : ℝ), u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u))) :=
            (intervalIntegral_tendsto_integral_Ioi 0 hint_real.integrableOn tendsto_id).const_mul 2
          have hcongr : (fun R : ℝ => ∫ u in -R..R, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u)) =
              fun R : ℝ => 2 * ∫ u in (0 : ℝ)..R, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) := by
            ext R
            rw [← intervalIntegral.integral_add_adjacent_intervals
              (hint_real.intervalIntegrable (a := -R) (b := 0))
              (hint_real.intervalIntegrable (a := 0) (b := R))]
            have hleft : ∫ u in -R..0, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) =
                ∫ u in (0 : ℝ)..R, u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u) := by
              have hcomp := (intervalIntegral.integral_comp_neg (a := 0) (b := R)
                (f := fun u => u ^ 4 * Real.exp (-(1 / 2 : ℝ) * u ^ 2) * Real.cos (k * t * u))).symm
              simp only [neg_zero] at hcomp
              rw [hcomp]
              refine intervalIntegral.integral_congr fun u _ => ?_
              rw [show (-u) ^ 4 = u ^ 4 by ring, neg_sq, show k * t * (-u) = -(k * t * u) by ring, Real.cos_neg]
            rw [hleft]; ring
          rw [hcongr] at h1
          exact tendsto_nhds_unique h1 h2
        linarith [hre_g, heven]
      have hcoeff_prod : (2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2) * (3 / 2 : ℝ) * (2 * σ ^ 5) * √(2 * π) =
          α ^ (-(5 / 2 : ℝ)) := by
        rw [coeff52_eq]
        have hσ5 : σ ^ 5 = 1 / (32 * π ^ 2 * √π * α ^ 2 * √α) := by
          dsimp [σ]
          have hsq4 : √(4 * π * α) = 2 * √π * √α := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
              show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          rw [inv_pow, hsq4]
          have hpi : √π ^ 5 = π ^ 2 * √π := by
            have := Real.sq_sqrt Real.pi_pos.le
            calc √π ^ 5 = (√π ^ 2) ^ 2 * √π := by ring
              _ = π ^ 2 * √π := by rw [this]
          have hal : √α ^ 5 = α ^ 2 * √α := by
            have := Real.sq_sqrt hα.le
            calc √α ^ 5 = (√α ^ 2) ^ 2 * √α := by ring
              _ = α ^ 2 * √α := by rw [this]
          rw [mul_pow, mul_pow, hpi, hal]; ring
        have hα52 : α ^ (-(5 / 2 : ℝ)) = 1 / (α ^ 2 * √α) := by
          rw [Real.rpow_neg hα.le, show (5 / 2 : ℝ) = (2 : ℝ) + 1 / 2 by norm_num,
            Real.rpow_add hα, Real.rpow_two, ← Real.sqrt_eq_rpow]; ring
        have h2π : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) π
        rw [hσ5, hα52, h2π]
        have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
        have hsp : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
        calc (16 * √2 / 3 * π ^ 2) * (3 / 2) * (2 * (1 / (32 * π ^ 2 * √π * α ^ 2 * √α))) * (√2 * √π)
            = ((16 * (√2 * √2) / 3) * (3 / 2) * 2 / 32) * (π ^ 2 / π ^ 2) * (√π / √π) * (1 / (α ^ 2 * √α)) := by ring
          _ = 1 / (α ^ 2 * √α) := by
              rw [hs2, div_self (sq_pos_of_pos Real.pi_pos).ne', div_self (Real.sqrt_pos.mpr Real.pi_pos).ne']
              norm_num
      rw [hpull, hs_sub, hgauss_half, gaussPhi_four_re]
      have hk4 : (k * t) ^ 4 - 6 * (k * t) ^ 2 + 3 = 4 * x ^ 2 * t ^ 4 - 12 * x * t ^ 2 + 3 := by
        have hk2 : (k * t) ^ 2 = 2 * x * t ^ 2 := by rw [mul_pow, hk_sq]
        have hk4' : (k * t) ^ 4 = (2 * x * t ^ 2) ^ 2 := by rw [← hk2]; ring
        rw [hk2, hk4']; ring
      have hexp_t : -(k * t) ^ 2 / 2 = -x * t ^ 2 := by
        rw [mul_pow, hk_sq]; ring
      rw [hk4, hexp_t]
      calc (2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2) * (3 / 2) * (1 - t ^ 2) *
              (2 * σ ^ 5 * ((1 / 2) * (√(2 * π) * (4 * x ^ 2 * t ^ 4 - 12 * x * t ^ 2 + 3) * Real.exp (-x * t ^ 2))))
          = ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2) * (3 / 2) * (2 * σ ^ 5) * √(2 * π)) *
              ((1 - t ^ 2) * ((4 * x ^ 2 * t ^ 4 - 12 * x * t ^ 2 + 3) / 2) * Real.exp (-x * t ^ 2)) := by
            ring
        _ = α ^ (-(5 / 2 : ℝ)) * ((1 - t ^ 2) * ((4 * x ^ 2 * t ^ 4 - 12 * x * t ^ 2 + 3) / 2) *
              Real.exp (-x * t ^ 2)) := by
            rw [hcoeff_prod]
    rw [setIntegral_congr_fun measurableSet_Ioc hinner, integral_const_mul,
      ← intervalIntegral.integral_of_le zero_le_one]
    let H : ℝ → ℝ := fun t => ((3 / 2 : ℝ) * t - (1 / 2 + x) * t ^ 3 + x * t ^ 5) * Real.exp (-x * t ^ 2)
    have hH_der : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt H ((1 - t ^ 2) * ((4 * x ^ 2 * t ^ 4 - 12 * x * t ^ 2 + 3) / 2) *
          Real.exp (-x * t ^ 2)) t := by
      intro t _
      have hp : HasDerivAt (fun s : ℝ => (3 / 2 : ℝ) * s - (1 / 2 + x) * s ^ 3 + x * s ^ 5)
          (3 / 2 - 3 * (1 / 2 + x) * t ^ 2 + 5 * x * t ^ 4) t := by
        have d1 := (hasDerivAt_id t).const_mul (3 / 2 : ℝ)
        have d3 := (hasDerivAt_pow 3 t).const_mul (1 / 2 + x)
        have d5 := (hasDerivAt_pow 5 t).const_mul x
        exact ((d1.sub d3).add d5).congr_deriv (by norm_num; ring)
      have he : HasDerivAt (fun s : ℝ => Real.exp (-x * s ^ 2)) (-2 * x * t * Real.exp (-x * t ^ 2)) t :=
        ((hasDerivAt_pow 2 t).const_mul (-x)).exp.congr_deriv (by norm_num; ring)
      exact (hp.mul he).congr_deriv (by ring)
    have hH_int : IntervalIntegrable (fun t : ℝ =>
        (1 - t ^ 2) * ((4 * x ^ 2 * t ^ 4 - 12 * x * t ^ 2 + 3) / 2) * Real.exp (-x * t ^ 2)) volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hH_der hH_int]
    dsimp [H, x]
    simp only [one_pow, zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 5 ≠ 0), sq,
      mul_zero, sub_zero, add_zero, Real.exp_zero, mul_one]
    ring

private lemma isRadialEigenfn_expDiff {α : ℝ} (hα : 0 < α) :
    IsRadialEigenfn (5 / 2) hankelKernel_fiveHalves (-1)
      (fun Δ => Real.exp (-2 * π * α * Δ) - α ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * (1 / α) * Δ)) := by
  refine ⟨by fun_prop, ?_, fun Δ hΔ => ?_⟩
  · unfold hankelRho0
    have h1_base : IntegrableOn (fun Δ : ℝ => ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)) *
        (Δ ^ (5 / 2 - 1 : ℝ) * Real.exp (-(2 * π * α) * Δ))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 5 / 2 - 1)
        (by positivity : 0 < 2 * π * α)).const_mul ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2))
    have h1 : IntegrableOn (fun Δ : ℝ => ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)) *
        (Δ ^ (5 / 2 - 1 : ℝ) * Real.exp (-2 * π * α * Δ))) (Ioi 0) :=
      h1_base.congr_fun (fun Δ _ => by dsimp only; congr 2; congr 1; ring) measurableSet_Ioi
    have h2_base : IntegrableOn (fun Δ : ℝ => (α ^ (-(5 / 2 : ℝ)) * ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2))) *
        (Δ ^ (5 / 2 - 1 : ℝ) * Real.exp (-(2 * π * (1 / α)) * Δ))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 5 / 2 - 1)
        (by positivity : 0 < 2 * π * (1 / α))).const_mul
        (α ^ (-(5 / 2 : ℝ)) * ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)))
    have h2 : IntegrableOn (fun Δ : ℝ => (α ^ (-(5 / 2 : ℝ)) * ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2))) *
        (Δ ^ (5 / 2 - 1 : ℝ) * Real.exp (-2 * π * (1 / α) * Δ))) (Ioi 0) :=
      h2_base.congr_fun (fun Δ _ => by dsimp only; congr 2; congr 1; ring) measurableSet_Ioi
    exact (h1.sub h2).congr_fun (fun Δ _ => by dsimp; ring) measurableSet_Ioi
  · have hI1 : IntegrableOn (fun s => Real.exp (-2 * π * α * s) * hankelRho0 (5 / 2) s *
        hankelKernel_fiveHalves.φ (Δ * s)) (Ioi 0) := by
      refine hankelTransform_integrand_integrableOn ?_ hΔ
      unfold hankelRho0
      have hdom1 : IntegrableOn (fun s : ℝ => ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)) *
          (s ^ (5 / 2 - 1 : ℝ) * Real.exp (-(2 * π * α) * s))) (Ioi 0) :=
        (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 5 / 2 - 1)
          (by positivity : 0 < 2 * π * α)).const_mul ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2))
      exact hdom1.congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
    have hI2 : IntegrableOn (fun s => (α ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * (1 / α) * s)) *
        hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s)) (Ioi 0) := by
      refine hankelTransform_integrand_integrableOn ?_ hΔ
      unfold hankelRho0
      have hdom2 : IntegrableOn (fun s : ℝ => (α ^ (-(5 / 2 : ℝ)) * ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2))) *
          (s ^ (5 / 2 - 1 : ℝ) * Real.exp (-(2 * π * (1 / α)) * s))) (Ioi 0) :=
        (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (-1 : ℝ) < 5 / 2 - 1)
          (by positivity : 0 < 2 * π * (1 / α))).const_mul
          (α ^ (-(5 / 2 : ℝ)) * ((2 * π) ^ (5 / 2 : ℝ) / Real.Gamma (5 / 2)))
      exact hdom2.congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
    unfold hankelTransform
    have hlin : ∫ s in Ioi (0 : ℝ), (Real.exp (-2 * π * α * s) -
          α ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * (1 / α) * s)) *
          hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s) =
        (∫ s in Ioi (0 : ℝ), Real.exp (-2 * π * α * s) * hankelRho0 (5 / 2) s *
          hankelKernel_fiveHalves.φ (Δ * s)) -
        ∫ s in Ioi (0 : ℝ), (α ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * (1 / α) * s)) *
          hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s) := by
      rw [← integral_sub hI1 hI2]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
    have hpull2 : ∫ s in Ioi (0 : ℝ), (α ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * (1 / α) * s)) *
          hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s) =
        α ^ (-(5 / 2 : ℝ)) * ∫ s in Ioi (0 : ℝ), Real.exp (-2 * π * (1 / α) * s) *
          hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
    rw [hlin, hpull2]
    have hT1 := hankelTransform_exp_fiveHalves hα hΔ
    have hT2 := hankelTransform_exp_fiveHalves (one_div_pos.mpr hα) hΔ
    unfold hankelTransform at hT1 hT2
    rw [hT1, hT2]
    have hpow_inv : α ^ (-(5 / 2 : ℝ)) * (1 / α) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [one_div, Real.inv_rpow hα.le, Real.rpow_neg hα.le, inv_inv,
        inv_mul_cancel₀ (Real.rpow_pos_of_pos hα _).ne']
    have hdiv_inv : -2 * π * Δ / (1 / α) = -2 * π * α * Δ := by
      field_simp [hα.ne']
    have hdiv_1 : -2 * π * Δ / α = -2 * π * (1 / α) * Δ := by ring
    rw [hdiv_inv, hdiv_1, ← mul_assoc, hpow_inv, one_mul]
    ring

/-- Proposition 7.9a non-vacuity witness: `c = 5 / 2` (`d = 5`) admits a `(-1)`-feasible radial
eigenfunction at `T = 4` and its `+1`-feasible intertwiner at `T = 4`. -/
theorem hankelIntertwiner_nonvacuous :
    ∃ (f : ℝ → ℝ),
      IsFeasible (5 / 2) hankelKernel_fiveHalves (-1) 4 f ∧
        IsFeasible (5 / 2) hankelKernel_fiveHalves 1 4 (intertwiner (5 / 2) f) := by
  let g₂ : ℝ → ℝ := fun Δ => Real.exp (-2 * π * 2 * Δ) - (2 : ℝ) ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * (1 / 2) * Δ)
  let g₄ : ℝ → ℝ := fun Δ => Real.exp (-2 * π * 4 * Δ) - (4 : ℝ) ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * π * (1 / 4) * Δ)
  let f : ℝ → ℝ := fun Δ => g₂ Δ - (1 / 2 : ℝ) * g₄ Δ
  have hg₂ := isRadialEigenfn_expDiff (by norm_num : (0 : ℝ) < 2)
  have hg₄ := isRadialEigenfn_expDiff (by norm_num : (0 : ℝ) < 4)
  have hf_eig : IsRadialEigenfn (5 / 2) hankelKernel_fiveHalves (-1) f := by
    refine ⟨hg₂.cont.sub (hg₄.cont.const_mul _), ?_, fun Δ hΔ => ?_⟩
    · exact (hg₂.int.sub (hg₄.int.const_mul (1 / 2 : ℝ))).congr_fun
        (fun s _ => by dsimp [f, g₂, g₄]; ring) measurableSet_Ioi
    · have hI1 := hankelTransform_integrand_integrableOn (K := hankelKernel_fiveHalves) hg₂.int hΔ
      have hI2 := hankelTransform_integrand_integrableOn (K := hankelKernel_fiveHalves) hg₄.int hΔ
      unfold hankelTransform
      have hlin : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s) =
          (∫ s in Ioi (0 : ℝ), g₂ s * hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s)) -
            (1 / 2 : ℝ) * ∫ s in Ioi (0 : ℝ), g₄ s * hankelRho0 (5 / 2) s * hankelKernel_fiveHalves.φ (Δ * s) := by
        rw [← integral_const_mul, ← integral_sub hI1 (hI2.const_mul _)]
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by dsimp [f]; ring
      rw [hlin]
      have e2 := hg₂.eigen Δ hΔ
      have e4 := hg₄.eigen Δ hΔ
      unfold hankelTransform at e2 e4
      rw [e2, e4]; dsimp [f]; ring
  have h252 : (2 : ℝ) ^ (-(5 / 2 : ℝ)) < 1 / 4 := by
    have h4sqrt2 : (4 : ℝ) < 4 * √2 := by
      have : (1 : ℝ) < √2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    have hpow52 : (2 : ℝ) ^ (5 / 2 : ℝ) = 4 * √2 := by
      rw [show (5 / 2 : ℝ) = (2 : ℝ) + (1 / 2 : ℝ) by norm_num, Real.rpow_add (by norm_num),
        Real.rpow_two, ← Real.sqrt_eq_rpow]; norm_num
    rw [Real.rpow_neg (by norm_num), hpow52, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) h4sqrt2
  have h452 : (4 : ℝ) ^ (-(5 / 2 : ℝ)) = 1 / 32 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hf0 : 0 ≤ f 0 := by
    dsimp [f, g₂, g₄]
    simp only [mul_zero, Real.exp_zero, mul_one]
    rw [h452]
    linarith
  have hexp_2pi : Real.exp (-2 * π) < 1 / 64 := by
    have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    have hpow6 : (64 : ℝ) < Real.exp 6 := by
      have : (2 : ℝ) ^ 6 < (Real.exp 1) ^ 6 := pow_lt_pow_left₀ he2 (by norm_num) (by norm_num)
      rw [← Real.exp_nat_mul] at this
      norm_num at this
      exact this
    have h6pi : (6 : ℝ) < 2 * π := by linarith [Real.pi_gt_three]
    have hlt : (64 : ℝ) < Real.exp (2 * π) := hpow6.trans (Real.exp_lt_exp.mpr h6pi)
    rw [show (-2 * π : ℝ) = -(2 * π) by ring, Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hlt
  have htail : ∀ Δ ≥ (4 : ℝ), 0 < f Δ := fun Δ hΔ => by
    have hslow : 0 < Real.exp (-(π / 2) * Δ) := Real.exp_pos _
    have h1 : Real.exp (-π * Δ) ≤ (1 / 64 : ℝ) * Real.exp (-(π / 2) * Δ) := by
      have hmul : Real.exp (-π * Δ) = Real.exp (-(π / 2) * Δ) * Real.exp (-(π / 2) * Δ) := by
        rw [← Real.exp_add]; congr 1; ring
      have hle : Real.exp (-(π / 2) * Δ) ≤ Real.exp (-2 * π) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      rw [hmul]
      exact mul_le_mul_of_nonneg_right (hle.trans hexp_2pi.le) (Real.exp_pos _).le
    have h2 : Real.exp (-8 * π * Δ) ≤ (1 / 64 : ℝ) * Real.exp (-(π / 2) * Δ) := by
      have hmul : Real.exp (-8 * π * Δ) = Real.exp (-((15 / 2 : ℝ) * π * Δ)) * Real.exp (-(π / 2) * Δ) := by
        rw [← Real.exp_add]; congr 1; ring
      have hle : Real.exp (-((15 / 2 : ℝ) * π * Δ)) ≤ Real.exp (-2 * π) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      rw [hmul]
      exact mul_le_mul_of_nonneg_right (hle.trans hexp_2pi.le) (Real.exp_pos _).le
    have hf_rewrite : f Δ = (1 / 64 : ℝ) * Real.exp (-(π / 2) * Δ) + Real.exp (-4 * π * Δ) -
        (2 : ℝ) ^ (-(5 / 2 : ℝ)) * Real.exp (-π * Δ) - (1 / 2 : ℝ) * Real.exp (-8 * π * Δ) := by
      dsimp [f, g₂, g₄]
      rw [h452, show (-2 * π * 2 * Δ : ℝ) = -4 * π * Δ by ring,
        show (-2 * π * (1 / 2) * Δ : ℝ) = -π * Δ by ring,
        show (-2 * π * 4 * Δ : ℝ) = -8 * π * Δ by ring,
        show (-2 * π * (1 / 4) * Δ : ℝ) = -(π / 2) * Δ by ring]
      ring
    rw [hf_rewrite]
    have hb1 : (2 : ℝ) ^ (-(5 / 2 : ℝ)) * Real.exp (-π * Δ) ≤ (1 / 4 : ℝ) * ((1 / 64 : ℝ) * Real.exp (-(π / 2) * Δ)) :=
      mul_le_mul h252.le h1 (Real.exp_pos _).le (by norm_num)
    have hb2 : (1 / 2 : ℝ) * Real.exp (-8 * π * Δ) ≤ (1 / 2 : ℝ) * ((1 / 64 : ℝ) * Real.exp (-(π / 2) * Δ)) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 256) hslow, Real.exp_pos (-4 * π * Δ)]
  have hf_feas : IsFeasible (5 / 2) hankelKernel_fiveHalves (-1) 4 f :=
    ⟨hf_eig, ⟨4, by norm_num, (htail 4 le_rfl).ne'⟩, by linarith, fun Δ hΔ => (htail Δ hΔ).le⟩
  exact ⟨f, hf_feas, intertwiner_feasible (by norm_num) hf_feas⟩


end FormalResearch.SignUncertainty

/-! ### Axiom Checks (`#guard_msgs`) -/

/-- info: 'FormalResearch.SignUncertainty.hankelKernel_fiveHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelKernel_fiveHalves

/-- info: 'FormalResearch.SignUncertainty.hankelIntertwiner_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelIntertwiner_nonvacuous
