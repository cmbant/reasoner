module

public import FormalResearch.ModularBootstrap.Chart.Basic
public import FormalResearch.ModularBootstrap.Chart.EdgeFunctions
public import FormalResearch.ModularBootstrap.ComplexBessel.LemmaS2
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Midpoint Analyticity, Strip Extension, and Primitive `Υ(ζ)` (Lemma S3, `vlo:S3`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S3 (`vlo:S3`,
lines 412–439).

Defines:
* `midpointA s := π⁻¹ ∫_0^1 (1 + t^2 s)^{-1/2} dt`, analytic on `ball 0 1` with `A(0) = 1/π`,
  real on `(-1, 1)`, satisfying `b(ζ) = √s · A(s)` and `q(ζ) = √s · A(-s)` near `ζ = 1/2`
  (`s = cos(πζ)`).
* `midpointOmega` and strip extension of `chartOmega` across `ζ = 1/2` and `Re ζ = 1/2`, proving
  analyticity and continuity on the closed strip `{0 ≤ Re ζ ≤ 1}` plus conjugation symmetry.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Chart

private lemma one_sub_two_sin_sq_eq_cos (ζ : ℂ) :
    1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2 =
      Complex.cos ((Real.pi : ℂ) * ζ) := by
  have h2 : (√2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcos : Complex.cos ((Real.pi : ℂ) * ζ) =
      1 - 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 := by
    have h := Complex.cos_two_mul ((Real.pi : ℂ) * ζ / 2)
    rw [show 2 * ((Real.pi : ℂ) * ζ / 2) = (Real.pi : ℂ) * ζ by ring] at h
    have hsc := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * ζ / 2)
    linear_combination h + 2 * hsc
  rw [mul_pow, h2, hcos]

/-! ### Section 1: Analytic midpoint factor `A(s)` on `ball 0 1` -/

private lemma norm_cpow_ofReal_exp {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    ‖z ^ (p : ℂ)‖ = ‖z‖ ^ p := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  have hre : (Complex.log z * (p : ℂ)).re = Real.log ‖z‖ * p := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re]
  rw [hre, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

private lemma one_add_t_sq_mul_re_pos {s : ℂ} {r : ℝ} (hs : ‖s‖ ≤ 1 - r) {t : ℝ}
    (ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    r ≤ (1 + (t : ℂ) ^ 2 * s).re := by
  have hts : ‖(t : ℂ) ^ 2 * s‖ ≤ 1 - r := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    calc t ^ 2 * ‖s‖ ≤ 1 * ‖s‖ := mul_le_mul_of_nonneg_right ht2 (norm_nonneg s)
      _ = ‖s‖ := one_mul _
      _ ≤ 1 - r := hs
  have hre_le : -((t : ℂ) ^ 2 * s).re ≤ ‖(t : ℂ) ^ 2 * s‖ :=
    neg_le.mp (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  rw [Complex.add_re, Complex.one_re]
  linarith

/-- Analytic midpoint factor `A(s) = π⁻¹ ∫_0^1 (1 + t^2 s)^{-1/2} dt` on `‖s‖ < 1`
(`lower_o1_two_edge.tex`, Lemma S3 proof). -/
noncomputable def midpointA (s : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..1, (1 + (t : ℂ) ^ 2 * s) ^ (-(1 / 2 : ℂ))

lemma midpointA_zero : midpointA 0 = ((1 / Real.pi : ℝ) : ℂ) := by
  unfold midpointA
  simp

lemma midpointA_ofReal_im_zero {x : ℝ} (hx : |x| < 1) : (midpointA (x : ℂ)).im = 0 := by
  unfold midpointA
  have hpi : (Real.pi : ℂ)⁻¹ = ((Real.pi⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hpi, Complex.im_ofReal_mul]
  have hint : ∫ t in (0 : ℝ)..1, (1 + (t : ℂ) ^ 2 * (x : ℂ)) ^ (-(1 / 2 : ℂ)) =
      ((∫ t in (0 : ℝ)..1, (1 + t ^ 2 * x) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have hcongr : ∫ t in (0 : ℝ)..1, (1 + (t : ℂ) ^ 2 * (x : ℂ)) ^ (-(1 / 2 : ℂ)) =
        ∫ t in (0 : ℝ)..1, (((1 + t ^ 2 * x) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht_icc : t ∈ Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
      have hx1 : -1 < x := (abs_lt.mp hx).1
      have hpos : 0 ≤ 1 + t ^ 2 * x := by
        have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht_icc.1, ht_icc.2]
        nlinarith [sq_nonneg t]
      rw [show 1 + (t : ℂ) ^ 2 * (x : ℂ) = ((1 + t ^ 2 * x : ℝ) : ℂ) by push_cast; ring,
        show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hpos]
    rw [hcongr]
    exact intervalIntegral.integral_ofReal (f := fun t : ℝ => (1 + t ^ 2 * x) ^ (-(1 / 2 : ℝ)))
  rw [hint, Complex.ofReal_im, mul_zero]

lemma analyticOnNhd_midpointA : AnalyticOnNhd ℂ midpointA (ball (0 : ℂ) 1) := by
  have hdiff : DifferentiableOn ℂ midpointA (ball (0 : ℂ) 1) := by
    intro s₀ hs₀
    rw [mem_ball_zero_iff] at hs₀
    let r : ℝ := (1 - ‖s₀‖) / 2
    have hr_pos : 0 < r := by dsimp [r]; linarith
    let F : ℂ → ℝ → ℂ := fun s t => (1 + (t : ℂ) ^ 2 * s) ^ (-(1 / 2 : ℂ))
    let F' : ℂ → ℝ → ℂ := fun s t =>
      -(1 / 2 : ℂ) * (t : ℂ) ^ 2 * (1 + (t : ℂ) ^ 2 * s) ^ (-(3 / 2 : ℂ))
    have h_slit : ∀ s ∈ ball s₀ r, ∀ t ∈ Icc (0 : ℝ) 1,
        r ≤ (1 + (t : ℂ) ^ 2 * s).re ∧ (1 + (t : ℂ) ^ 2 * s) ∈ Complex.slitPlane := by
      intro s hs t ht
      have hs_norm : ‖s‖ ≤ 1 - r := by
        rw [mem_ball, dist_eq_norm] at hs
        calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
          _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
          _ ≤ ‖s₀‖ + r := by linarith
          _ = 1 - r := by dsimp [r]; ring
      have hre := one_add_t_sq_mul_re_pos hs_norm ht.1 ht.2
      exact ⟨hre, Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hr_pos hre))⟩
    have hF_cont : ∀ s ∈ ball s₀ r, ContinuousOn (F s) (Icc (0 : ℝ) 1) := by
      intro s hs
      refine ContinuousOn.cpow ?_ continuousOn_const (fun t ht => (h_slit s hs t ht).2)
      fun_prop
    have hF'_cont : ContinuousOn (F' s₀) (Icc (0 : ℝ) 1) := by
      refine ContinuousOn.mul (by fun_prop) ?_
      refine ContinuousOn.cpow ?_ continuousOn_const
        (fun t ht => (h_slit s₀ (mem_ball_self hr_pos) t ht).2)
      fun_prop
    have hderiv : DifferentiableAt ℂ (fun s => ∫ t in (0 : ℝ)..1, F s t) s₀ := by
      have h_res := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume) (a := (0 : ℝ)) (b := 1) (F := F) (F' := F')
        (bound := fun _ : ℝ => (1 / 2 : ℝ) * r ^ (-(3 / 2 : ℝ)))
        (Metric.ball_mem_nhds s₀ hr_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact h_res.2.differentiableAt
      · refine Filter.eventually_of_mem (Metric.ball_mem_nhds s₀ hr_pos) fun s hs => ?_
        rw [Set.uIoc_of_le zero_le_one]
        exact (hF_cont s hs).mono Set.Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
      · exact (hF_cont s₀ (mem_ball_self hr_pos)).intervalIntegrable_of_Icc zero_le_one
      · rw [Set.uIoc_of_le zero_le_one]
        exact (hF'_cont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      · filter_upwards with t ht s hs
        rw [Set.uIoc_of_le zero_le_one] at ht
        have ht_icc : t ∈ Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
        obtain ⟨hre, hslit⟩ := h_slit s hs t ht_icc
        have hz_ne : 1 + (t : ℂ) ^ 2 * s ≠ 0 := Complex.slitPlane_ne_zero hslit
        have hnorm_ge : r ≤ ‖1 + (t : ℂ) ^ 2 * s‖ := le_trans hre (Complex.re_le_norm _)
        have hcpow_norm : ‖(1 + (t : ℂ) ^ 2 * s) ^ (-(3 / 2 : ℂ))‖ =
            ‖1 + (t : ℂ) ^ 2 * s‖ ^ (-(3 / 2 : ℝ)) := by
          rw [show -(3 / 2 : ℂ) = ((-(3 / 2 : ℝ) : ℝ) : ℂ) by norm_num]
          exact norm_cpow_ofReal_exp hz_ne _
        have hrpow_le : ‖1 + (t : ℂ) ^ 2 * s‖ ^ (-(3 / 2 : ℝ)) ≤ r ^ (-(3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hr_pos hnorm_ge (by norm_num)
        dsimp [F']
        rw [norm_mul, norm_mul, norm_neg, norm_div, norm_one,
          Complex.norm_ofNat, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht_icc.1, hcpow_norm]
        have ht2_le : t ^ 2 ≤ 1 := by nlinarith [ht_icc.1, ht_icc.2]
        calc (1 / 2 : ℝ) * t ^ 2 * ‖1 + (t : ℂ) ^ 2 * s‖ ^ (-(3 / 2 : ℝ))
            ≤ (1 / 2 : ℝ) * 1 * r ^ (-(3 / 2 : ℝ)) := by gcongr
          _ = (1 / 2 : ℝ) * r ^ (-(3 / 2 : ℝ)) := by ring
      · exact intervalIntegrable_const
      · filter_upwards with t ht s hs
        rw [Set.uIoc_of_le zero_le_one] at ht
        have ht_icc : t ∈ Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
        obtain ⟨_, hslit⟩ := h_slit s hs t ht_icc
        have hlin : HasDerivAt (fun z : ℂ => 1 + (t : ℂ) ^ 2 * z) ((t : ℂ) ^ 2) s := by
          simpa using ((hasDerivAt_id s).const_mul ((t : ℂ) ^ 2)).const_add 1
        have hpow := hlin.cpow_const hslit (c := -(1 / 2 : ℂ))
        refine hpow.congr_deriv ?_
        dsimp [F']
        have hpow_eq : (-(1 / 2 : ℂ) - 1) = -(3 / 2 : ℂ) := by norm_num
        rw [hpow_eq]; ring
    exact (hderiv.const_mul _).differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_ball

lemma arsinhC_mem_slitPlane_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    w ^ 2 + 1 ∈ Complex.slitPlane ∧ w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane := by
  have hre_sq : w.re ^ 2 + w.im ^ 2 < 1 := by
    rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, sq]
    nlinarith [norm_nonneg w]
  have hw2_re : 0 < (w ^ 2 + 1).re := by
    rw [Complex.add_re, Complex.one_re, sq, Complex.mul_re]
    nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  have hw2_slit : w ^ 2 + 1 ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hw2_re)
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hs_re : 0 < s.re := cpow_half_re_pos hw2_slit
  have hs2 : s ^ 2 = w ^ 2 + 1 := cpow_half_sq _
  have hs2_re : s.re ^ 2 - s.im ^ 2 = w.re ^ 2 - w.im ^ 2 + 1 := by
    have := congrArg Complex.re hs2
    rw [sq, sq, Complex.mul_re, Complex.add_re, Complex.mul_re, Complex.one_re] at this
    linarith
  have hw_lt_s : w.re ^ 2 < s.re ^ 2 := by
    nlinarith [sq_nonneg s.im, sq_nonneg w.im]
  have habs : |w.re| < s.re := by
    rw [← Real.sqrt_sq hs_re.le, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hw_lt_s
  refine ⟨hw2_slit, Complex.mem_slitPlane_iff.mpr (Or.inl ?_)⟩
  rw [Complex.add_re]
  linarith [neg_abs_le w.re]

lemma arsinhC_eq_mul_midpointA_sq {w : ℂ} (hw : ‖w‖ < 1) :
    arsinhC w = (Real.pi : ℂ) * w * midpointA (w ^ 2) := by
  let G : ℝ → ℂ := fun t => arsinhC ((t : ℂ) * w)
  let G' : ℝ → ℂ := fun t => w * (1 + (t : ℂ) ^ 2 * w ^ 2) ^ (-(1 / 2 : ℂ))
  have hG_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (G' t) t := by
    intro t ht
    have htw_norm : ‖(t : ℂ) * w‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      nlinarith [norm_nonneg w, ht.2]
    obtain ⟨h1, h2⟩ := arsinhC_mem_slitPlane_of_norm_lt_one htw_norm
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
    have hcomp := (hasDerivAt_arsinhC h1 h2).comp t hlin
    refine hcomp.congr_deriv ?_
    dsimp [G']
    rw [show ((t : ℂ) * w) ^ 2 + 1 = 1 + (t : ℂ) ^ 2 * w ^ 2 by ring]
    ring
  have hG'_cont : ContinuousOn G' (Icc (0 : ℝ) 1) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.cpow ?_ continuousOn_const fun t ht => ?_
    · fun_prop
    · have htw_norm : ‖(t : ℂ) * w‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
        nlinarith [norm_nonneg w, ht.2]
      have h1 := (arsinhC_mem_slitPlane_of_norm_lt_one htw_norm).1
      rwa [show 1 + (t : ℂ) ^ 2 * w ^ 2 = ((t : ℂ) * w) ^ 2 + 1 by ring]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hG_deriv t (by rwa [Set.uIcc_of_le zero_le_one] at ht))
    (hG'_cont.intervalIntegrable_of_Icc zero_le_one)
  have hG0 : G 0 = 0 := by dsimp [G, arsinhC]; simp
  have hG1 : G 1 = arsinhC w := by dsimp [G]; simp
  rw [hG1, hG0, sub_zero] at hftc
  have hpull : ∫ t in (0 : ℝ)..1, G' t =
      w * ∫ t in (0 : ℝ)..1, (1 + (t : ℂ) ^ 2 * w ^ 2) ^ (-(1 / 2 : ℂ)) :=
    intervalIntegral.integral_const_mul w _
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  unfold midpointA
  rw [← hftc, hpull]
  field_simp [hpi]

private lemma cpow_half_eq_of_re_pos {Z z : ℂ} (hz : z ∈ Complex.slitPlane) (hZ : Z ^ 2 = z)
    (hre : 0 < Z.re) : Z = z ^ (1 / 2 : ℂ) := by
  set s := z ^ (1 / 2 : ℂ)
  have hs_re : 0 < s.re := cpow_half_re_pos hz
  have hs2 : s ^ 2 = z := cpow_half_sq z
  have hprod : (Z - s) * (Z + s) = 0 := by linear_combination hZ - hs2
  have hne : Z + s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [Complex.add_re, Complex.zero_re] at this
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hne)

lemma chartB_eq_midpointA {ζ : ℂ} (hcos_norm : ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ < 1) :
    chartB ζ = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) *
      midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) := by
  set s : ℂ := Complex.cos ((Real.pi : ℂ) * ζ)
  set w : ℂ := s ^ (1 / 2 : ℂ)
  have hw_norm : ‖w‖ < 1 := by
    rcases eq_or_ne s 0 with hs0 | hs0
    · simp [w, hs0]
    · have hnorm : ‖w‖ = ‖s‖ ^ (1 / 2 : ℝ) := by
        dsimp [w]
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
        exact norm_cpow_ofReal_exp hs0 _
      rw [hnorm, ← Real.sqrt_eq_rpow]
      exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hcos_norm)
  have hw2 : w ^ 2 = s := cpow_half_sq s
  unfold chartB
  rw [arsinhC_eq_mul_midpointA_sq hw_norm, hw2]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp [hpi]

lemma chartQ_eq_midpointA {ζ : ℂ} (hcos_norm : ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ < 1)
    (hZ_re : 0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)).re) :
    chartQ ζ = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) *
      midpointA (-Complex.cos ((Real.pi : ℂ) * ζ)) := by
  set s : ℂ := Complex.cos ((Real.pi : ℂ) * ζ)
  set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)
  have hs_re : 0 < (1 - s).re := by
    have hre_le : s.re ≤ ‖s‖ := Complex.re_le_norm s
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h1s_slit : 1 - s ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hs_re)
  have hZ2 : Z ^ 2 = 1 - s := by
    have h := one_sub_two_sin_sq_eq_cos ζ
    linear_combination -h
  have hZ_eq : Z = (1 - s) ^ (1 / 2 : ℂ) := cpow_half_eq_of_re_pos h1s_slit hZ2 hZ_re
  set w : ℂ := Complex.I * s ^ (1 / 2 : ℂ)
  have hw_norm : ‖w‖ < 1 := by
    dsimp [w]
    rw [norm_mul, Complex.norm_I, one_mul]
    rcases eq_or_ne s 0 with hs0 | hs0
    · simp [hs0]
    · have hnorm : ‖s ^ (1 / 2 : ℂ)‖ = ‖s‖ ^ (1 / 2 : ℝ) := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
        exact norm_cpow_ofReal_exp hs0 _
      rw [hnorm, ← Real.sqrt_eq_rpow]
      exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hcos_norm)
  have hw2 : w ^ 2 = -s := by
    dsimp [w]; rw [mul_pow, Complex.I_sq, cpow_half_sq s]; ring
  have h_arsinh := arsinhC_eq_mul_midpointA_sq hw_norm
  rw [hw2] at h_arsinh
  have h_log_eq : arsinhC w = Complex.log (Z + Complex.I * s ^ (1 / 2 : ℂ)) := by
    unfold arsinhC
    rw [hw2, show -s + 1 = 1 - s by ring, ← hZ_eq]
    dsimp [w]
    ring_nf
  have h_arccos : arccosC Z = -Complex.I * arsinhC w := by
    unfold arccosC
    rw [one_sub_two_sin_sq_eq_cos ζ, ← h_log_eq]
  unfold chartQ
  change (Real.pi : ℂ)⁻¹ * arccosC Z = s ^ (1 / 2 : ℂ) * midpointA (-s)
  rw [h_arccos, h_arsinh]
  dsimp [w]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  calc (Real.pi : ℂ)⁻¹ * (-Complex.I * ((Real.pi : ℂ) * (Complex.I * s ^ (1 / 2 : ℂ)) * midpointA (-s)))
      = ((Real.pi : ℂ)⁻¹ * (Real.pi : ℂ)) * (-Complex.I * Complex.I) * s ^ (1 / 2 : ℂ) * midpointA (-s) := by
        ring
    _ = 1 * 1 * s ^ (1 / 2 : ℂ) * midpointA (-s) := by
        rw [inv_mul_cancel₀ hpi, neg_mul, Complex.I_mul_I, neg_neg]
    _ = s ^ (1 / 2 : ℂ) * midpointA (-s) := by ring

/-! ### Section 2: Midpoint analyticity, midline relation, and reflection extension of `ω(ζ)` -/

/-- Local analytic extension of `ω(ζ)` across the midpoint `ζ = 1/2`:
`ω_mid(ζ) = (2π/3) cos(πζ) A(cos πζ) A(-cos πζ)`. -/
noncomputable def midpointOmega (ζ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) / 3) * Complex.cos ((Real.pi : ℂ) * ζ) *
    midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) *
    midpointA (-Complex.cos ((Real.pi : ℂ) * ζ))

lemma midpointOmega_reflect (ζ : ℂ) : midpointOmega (1 - ζ) = -midpointOmega ζ := by
  unfold midpointOmega
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - ζ)) = -Complex.cos ((Real.pi : ℂ) * ζ) := by
    rw [mul_sub, mul_one, Complex.cos_pi_sub]
  rw [hcos]
  ring

lemma chartOmegaHalf_eq_midpointOmega {ζ : ℂ} (hcos_norm : ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ < 1)
    (hZ_re : 0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)).re) :
    chartOmegaHalf ζ = midpointOmega ζ := by
  unfold chartOmegaHalf midpointOmega
  rw [chartB_eq_midpointA hcos_norm, chartQ_eq_midpointA hcos_norm hZ_re]
  have hsq : ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) :=
    cpow_half_sq _
  rw [show (2 * (Real.pi : ℂ) / 3) * ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) *
      midpointA (Complex.cos ((Real.pi : ℂ) * ζ))) *
      ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) *
      midpointA (-Complex.cos ((Real.pi : ℂ) * ζ))) =
      (2 * (Real.pi : ℂ) / 3) * (((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) ^ 2) *
      midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) *
      midpointA (-Complex.cos ((Real.pi : ℂ) * ζ)) by ring, hsq]

private lemma cos_pi_half_eq_zero : Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) = 0 := by
  rw [show (Real.pi : ℂ) * (1 / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]

lemma exists_midpoint_ball :
    ∃ r_mid : ℝ, 0 < r_mid ∧
      (∀ ζ ∈ ball (1 / 2 : ℂ) r_mid,
        ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ < 1 ∧
        0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)).re ∧
        0 < (midpointA (Complex.cos ((Real.pi : ℂ) * ζ))).re ∧
        0 < (midpointA (-Complex.cos ((Real.pi : ℂ) * ζ))).re) := by
  have h1 : ∀ᶠ ζ in 𝓝 (1 / 2 : ℂ), ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ < 1 := by
    have hcont : ContinuousAt (fun ζ : ℂ => ‖Complex.cos ((Real.pi : ℂ) * ζ)‖) (1 / 2 : ℂ) := by
      fun_prop
    refine hcont.eventually (gt_mem_nhds ?_)
    have hzero : ‖Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ))‖ = 0 := by
      rw [cos_pi_half_eq_zero, norm_zero]
    change ‖Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ))‖ < 1
    rw [hzero]
    exact zero_lt_one
  have h2 : ∀ᶠ ζ in 𝓝 (1 / 2 : ℂ), 0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)).re := by
    have hcont : ContinuousAt (fun ζ : ℂ => ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)).re) (1 / 2 : ℂ) := by
      fun_prop
    refine hcont.eventually (lt_mem_nhds ?_)
    have hsin : (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ) / 2) = 1 := by
      rw [show (Real.pi : ℂ) * (1 / 2 : ℂ) / 2 = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_sin, Real.sin_pi_div_four]
      have hsq : √2 * (√2 / 2) = 1 := by
        rw [mul_div_assoc', Real.mul_self_sqrt (by norm_num)]; norm_num
      rw [← Complex.ofReal_mul, hsq, Complex.ofReal_one]
    change 0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ) / 2)).re
    rw [hsin, Complex.one_re]
    exact zero_lt_one
  have hA0_re : 0 < (midpointA 0).re := by
    rw [midpointA_zero, Complex.ofReal_re]
    exact one_div_pos.mpr Real.pi_pos
  have hA_cont : ContinuousAt midpointA 0 :=
    (analyticOnNhd_midpointA 0 (mem_ball_self zero_lt_one)).continuousAt
  have hcos_tend : Tendsto (fun ζ : ℂ => Complex.cos ((Real.pi : ℂ) * ζ)) (𝓝 (1 / 2 : ℂ)) (𝓝 0) := by
    have h := (by fun_prop : ContinuousAt (fun ζ : ℂ => Complex.cos ((Real.pi : ℂ) * ζ)) (1 / 2 : ℂ)).tendsto
    rwa [cos_pi_half_eq_zero] at h
  have hneg_cos_tend : Tendsto (fun ζ : ℂ => -Complex.cos ((Real.pi : ℂ) * ζ)) (𝓝 (1 / 2 : ℂ)) (𝓝 0) := by
    simpa [neg_zero] using hcos_tend.neg
  have h3 : ∀ᶠ ζ in 𝓝 (1 / 2 : ℂ), 0 < (midpointA (Complex.cos ((Real.pi : ℂ) * ζ))).re :=
    (Complex.continuous_re.continuousAt.comp hA_cont).eventually (lt_mem_nhds hA0_re)
      |>.filter_mono hcos_tend
  have h4 : ∀ᶠ ζ in 𝓝 (1 / 2 : ℂ), 0 < (midpointA (-Complex.cos ((Real.pi : ℂ) * ζ))).re :=
    (Complex.continuous_re.continuousAt.comp hA_cont).eventually (lt_mem_nhds hA0_re)
      |>.filter_mono hneg_cos_tend
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and (h2.and (h3.and h4)))
  exact ⟨r, hr, fun ζ hζ => hball ζ hζ⟩

noncomputable def rMid : ℝ := Classical.choose exists_midpoint_ball

lemma rMid_pos : 0 < rMid := (Classical.choose_spec exists_midpoint_ball).1

lemma mem_rMid_ball {ζ : ℂ} (hζ : ζ ∈ ball (1 / 2 : ℂ) rMid) :
    ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ < 1 ∧
    0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)).re ∧
    0 < (midpointA (Complex.cos ((Real.pi : ℂ) * ζ))).re ∧
    0 < (midpointA (-Complex.cos ((Real.pi : ℂ) * ζ))).re :=
  (Classical.choose_spec exists_midpoint_ball).2 ζ hζ

lemma sin_pi_chartQ (ζ : ℂ) :
    Complex.sin ((Real.pi : ℂ) * chartQ ζ) = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) := by
  unfold chartQ
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [mul_inv_cancel_left₀ hpi]
  set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)
  set s : ℂ := (1 - Z ^ 2) ^ (1 / 2 : ℂ)
  set u : ℂ := Z + Complex.I * s
  have hu : u ≠ 0 := arccosC_inner_ne_zero Z
  have hs2 : s ^ 2 = 1 - Z ^ 2 := cpow_half_sq _
  have hu_inv : u⁻¹ = Z - Complex.I * s := by
    refine inv_eq_of_mul_eq_one_right ?_
    dsimp [u]
    calc (Z + Complex.I * s) * (Z - Complex.I * s)
        = Z ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
      _ = Z ^ 2 + (1 - Z ^ 2) := by rw [Complex.I_sq, hs2]; ring
      _ = 1 := by ring
  unfold arccosC
  rw [Complex.sin]
  have hII : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have h1 : Complex.exp (-(-Complex.I * Complex.log u) * Complex.I) = u⁻¹ := by
    rw [show -(-Complex.I * Complex.log u) * Complex.I = -Complex.log u * (-Complex.I * Complex.I) by ring,
      hII, mul_one, Complex.exp_neg, Complex.exp_log hu]
  have h2 : Complex.exp (-Complex.I * Complex.log u * Complex.I) = u := by
    rw [show -Complex.I * Complex.log u * Complex.I = Complex.log u * (-Complex.I * Complex.I) by ring,
      hII, mul_one, Complex.exp_log hu]
  have hs_eq : s = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) := by
    dsimp [s, Z]; rw [one_sub_two_sin_sq_eq_cos]
  change (Complex.exp (-(-Complex.I * Complex.log u) * Complex.I) -
      Complex.exp (-Complex.I * Complex.log u * Complex.I)) * Complex.I / 2 =
    (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  rw [h1, h2, hu_inv]
  dsimp [u]
  rw [hs_eq]
  calc ((Z - Complex.I * (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) -
        (Z + Complex.I * (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ))) * Complex.I / 2
      = -((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) * (Complex.I * Complex.I) := by ring
    _ = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring

lemma sinh_pi_chartB (ζ : ℂ) :
    Complex.sinh ((Real.pi : ℂ) * chartB ζ) = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) := by
  unfold chartB
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [mul_inv_cancel_left₀ hpi, sinh_arsinhC]

private lemma chartQ_midline_pos {τ : ℝ} (hτ : 0 < τ) :
    chartQ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
      -Complex.I * starRingEnd ℂ (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))) := by
  set ζ : ℂ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
  have hζ_re : ζ.re = 1 / 2 := by simp [ζ]
  have hζ_im : ζ.im = τ := by simp [ζ]
  have hζ_ne : ζ ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h
    simp [ζ] at this
    exact hτ.ne' this
  set b := chartB ζ
  set q := chartQ ζ
  have hb_re : 0 < b.re := re_chartB_pos (by linarith) (by linarith) hζ_ne
  have hq_Ioo := re_chartQ_Ioo (by linarith) (by linarith) hζ_ne
  have hcos_eq : Complex.cos ((Real.pi : ℂ) * ζ) = -Complex.I * (Real.sinh (Real.pi * τ) : ℝ) := by
    rw [show (Real.pi : ℂ) * ζ = ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp [ζ]; ring]
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero,
      zero_mul, zero_sub, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one,
      one_mul, ← Complex.ofReal_sinh]
    ring
  have hsh_pos : 0 < Real.sinh (Real.pi * τ) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hτ)
  have hcos_im_neg : (Complex.cos ((Real.pi : ℂ) * ζ)).im < 0 := by
    rw [hcos_eq]
    simp only [Complex.neg_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    linarith
  have hs_arg : (Complex.cos ((Real.pi : ℂ) * ζ)).arg = -(Real.pi / 2) := by
    rw [hcos_eq, show -Complex.I * (Real.sinh (Real.pi * τ) : ℂ) =
      ((Real.sinh (Real.pi * τ) : ℝ) : ℂ) * (-Complex.I) by ring,
      Complex.arg_real_mul _ hsh_pos, Complex.arg_neg_I]
  set s := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  have hcos_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 := by
    intro h0; rw [h0, Complex.zero_im] at hcos_im_neg; exact lt_irrefl 0 hcos_im_neg
  have hs_re : 0 < s.re :=
    cpow_half_re_pos (cos_pi_mem_slitPlane (by linarith) (by linarith) hζ_ne)
  have hs_im_eq : s.im = -s.re := by
    have hpow : s = ((Real.exp (Real.log ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ / 2) : ℝ) : ℂ) *
        ((Real.cos (-(Real.pi / 4)) : ℂ) + (Real.sin (-(Real.pi / 4)) : ℂ) * Complex.I) := by
      dsimp [s]
      rw [Complex.cpow_def_of_ne_zero hcos_ne]
      have hmul : Complex.log (Complex.cos ((Real.pi : ℂ) * ζ)) * (1 / 2 : ℂ) =
          ((Real.log ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ / 2 : ℝ) : ℂ) +
            ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.log_re]; ring
        · simp [Complex.log_im, hs_arg]; ring
      have hexp1 : Complex.exp ((Real.log ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ / 2 : ℝ) : ℂ) =
          ((Real.exp (Real.log ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ / 2) : ℝ) : ℂ) :=
        (Complex.ofReal_exp _).symm
      rw [hmul, Complex.exp_add_mul_I, hexp1]
      congr 2 <;> push_cast <;> rfl
    have hcs : ((Real.cos (-(Real.pi / 4)) : ℂ) + (Real.sin (-(Real.pi / 4)) : ℂ) * Complex.I) =
        ((√2 / 2 : ℝ) : ℂ) - ((√2 / 2 : ℝ) : ℂ) * Complex.I := by
      rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
      push_cast; ring
    rw [hpow, hcs]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, zero_sub, add_zero]
    ring
  have hs_im_neg : s.im < 0 := by linarith
  have hb_im_neg : ((Real.pi : ℂ) * b).im < 0 ∧ -(Real.pi / 2) < ((Real.pi : ℂ) * b).im := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hpb : (Real.pi : ℂ) * b = arsinhC s := by
      dsimp [b]; unfold chartB; rw [mul_inv_cancel_left₀ hpi]
    rw [hpb]
    unfold arsinhC
    set u := s + (s ^ 2 + 1) ^ (1 / 2 : ℂ)
    have hs2_eq : s ^ 2 + 1 = 1 - Complex.I * (Real.sinh (Real.pi * τ) : ℂ) := by
      rw [cpow_half_sq, hcos_eq]; ring
    have hu_re_s2 : 0 < (s ^ 2 + 1).re := by
      rw [hs2_eq]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self, sub_zero]
      exact zero_lt_one
    have hu_im_s2 : (s ^ 2 + 1).im < 0 := by
      rw [hs2_eq]
      simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add, zero_sub]
      linarith
    have hrt_slit : s ^ 2 + 1 ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hu_re_s2)
    have hrt_re : 0 < ((s ^ 2 + 1) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hrt_slit
    have hrt_im : ((s ^ 2 + 1) ^ (1 / 2 : ℂ)).im < 0 := by
      set r := (s ^ 2 + 1) ^ (1 / 2 : ℂ)
      have hr2 : r ^ 2 = s ^ 2 + 1 := cpow_half_sq _
      have him2 : 2 * r.re * r.im = (s ^ 2 + 1).im := by
        have := congrArg Complex.im hr2; rw [sq, Complex.mul_im] at this; linarith
      nlinarith
    have hu_re : 0 < u.re := by
      have : u.re = s.re + ((s ^ 2 + 1) ^ (1 / 2 : ℂ)).re := Complex.add_re _ _
      linarith
    have hu_im : u.im < 0 := by
      have : u.im = s.im + ((s ^ 2 + 1) ^ (1 / 2 : ℂ)).im := Complex.add_im _ _
      linarith
    have hu_arg := Complex.arg_of_re_nonneg hu_re.le
    rw [Complex.log_im, hu_arg]
    have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr (arsinhC_inner_ne_zero s)
    have hlt0 : u.im / ‖u‖ < 0 := div_neg_of_neg_of_pos hu_im hnorm_pos
    have hgt_neg1 : -1 < u.im / ‖u‖ := by
      rw [lt_div_iff₀ hnorm_pos]
      have hnsq : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by
        rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, sq]
      nlinarith [sq_pos_of_pos hu_re, norm_nonneg u]
    exact ⟨Real.arcsin_lt_zero.mpr hlt0,
      by rw [← Real.arcsin_neg_one]; exact Real.arcsin_lt_arcsin le_rfl hgt_neg1 (by linarith)⟩
  have hq_im_neg : ((Real.pi : ℂ) * q).im < 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hpq : (Real.pi : ℂ) * q = arccosC ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) := by
      dsimp [q]; unfold chartQ; rw [mul_inv_cancel_left₀ hpi]
    rw [hpq]
    unfold arccosC
    set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)
    set u := Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)
    have hZ_eq : Z = (Real.cosh (Real.pi * τ / 2) : ℂ) + Complex.I * (Real.sinh (Real.pi * τ / 2) : ℂ) := by
      dsimp [Z]
      rw [show (Real.pi : ℂ) * ζ / 2 = ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * τ / 2 : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp [ζ]; ring]
      rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
        ← Complex.ofReal_cos, ← Complex.ofReal_sinh, Real.sin_pi_div_four, Real.cos_pi_div_four]
      have hsq : √2 * (√2 / 2) = 1 := by
        rw [mul_div_assoc', Real.mul_self_sqrt (by norm_num)]; norm_num
      have hsq_c : (√2 : ℂ) * ((√2 / 2 : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, hsq, Complex.ofReal_one]
      calc (√2 : ℂ) * (((√2 / 2 : ℝ) : ℂ) * (Real.cosh (Real.pi * τ / 2) : ℂ) +
            ((√2 / 2 : ℝ) : ℂ) * (Real.sinh (Real.pi * τ / 2) : ℂ) * Complex.I)
          = ((√2 : ℂ) * ((√2 / 2 : ℝ) : ℂ)) * (Real.cosh (Real.pi * τ / 2) : ℂ) +
              ((√2 : ℂ) * ((√2 / 2 : ℝ) : ℂ)) * (Real.sinh (Real.pi * τ / 2) : ℂ) * Complex.I := by ring
        _ = (Real.cosh (Real.pi * τ / 2) : ℂ) + Complex.I * (Real.sinh (Real.pi * τ / 2) : ℂ) := by
            rw [hsq_c]; ring
    have hZ_re : 0 < Z.re := by
      rw [hZ_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero]
      linarith [Real.cosh_pos (Real.pi * τ / 2)]
    have hZ_im : 0 < Z.im := by
      rw [hZ_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [Real.sinh_pos_iff.mpr (by positivity : 0 < Real.pi * τ / 2)]
    have hIs : Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) = Complex.I * s := by
      dsimp [s]; rw [one_sub_two_sin_sq_eq_cos]
    have hIs_re : 0 < (Complex.I * s).re := by simp [hs_im_neg]
    have hIs_im : 0 < (Complex.I * s).im := by simp [hs_re]
    have hu_nsq : 1 < ‖u‖ ^ 2 := by
      have hu_re : Z.re < u.re := by
        have : u.re = Z.re + (Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)).re := Complex.add_re _ _
        rw [hIs] at this; linarith
      have hu_im : Z.im < u.im := by
        have : u.im = Z.im + (Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)).im := Complex.add_im _ _
        rw [hIs] at this; linarith
      have hnsq_Z : Z.re ^ 2 + Z.im ^ 2 = Real.cosh (Real.pi * τ) := by
        rw [hZ_eq]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, one_mul,
          zero_add]
        have hc2 := Real.cosh_two_mul (Real.pi * τ / 2)
        have hch2 := Real.cosh_sq_sub_sinh_sq (Real.pi * τ / 2)
        rw [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at hc2
        linarith
      have hcosh_gt1 : 1 ≤ Real.cosh (Real.pi * τ) := Real.one_le_cosh _
      have hnsq_u : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by
        rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, sq]
      nlinarith
    have hnorm_gt1 : 1 < ‖u‖ := by nlinarith [norm_nonneg u]
    have hlog_re : 0 < (Complex.log u).re := by rw [Complex.log_re]; exact Real.log_pos hnorm_gt1
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    linarith
  set z₁ : ℂ := (Real.pi : ℂ) * q
  set z₂ : ℂ := (Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ b)
  have hsin_eq : Complex.sin z₁ = Complex.sin z₂ := by
    have hq_sin : Complex.sin z₁ = s := sin_pi_chartQ ζ
    have hb_sin : Complex.sin z₂ = -Complex.I * starRingEnd ℂ s := by
      have hz2_eq : z₂ = -(starRingEnd ℂ ((Real.pi : ℂ) * b) * Complex.I) := by
        dsimp [z₂]; rw [map_mul, Complex.conj_ofReal]; ring
      rw [hz2_eq, Complex.sin_neg, Complex.sin_mul_I, Complex.sinh_conj,
        sinh_pi_chartB ζ]
      ring
    rw [hq_sin, hb_sin]
    apply Complex.ext
    · simp [hs_im_eq]
    · simp [hs_im_eq]
  have hz2_im : z₂.im < 0 := by
    dsimp [z₂]
    rw [show (Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ b) =
      -Complex.I * starRingEnd ℂ ((Real.pi : ℂ) * b) by rw [map_mul, Complex.conj_ofReal]; ring]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im, zero_mul, neg_zero, zero_add]
    have hpi_pb : ((Real.pi : ℂ) * b).re = Real.pi * b.re := by rw [Complex.re_ofReal_mul]
    linarith [mul_pos Real.pi_pos hb_re]
  have hz1_re : 0 < z₁.re ∧ z₁.re < Real.pi := by
    dsimp [z₁]; rw [Complex.re_ofReal_mul]
    exact ⟨mul_pos Real.pi_pos hq_Ioo.1, by nlinarith [Real.pi_pos, hq_Ioo.2]⟩
  have hz2_re : 0 < z₂.re ∧ z₂.re < Real.pi / 2 := by
    dsimp [z₂]
    rw [show (Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ b) =
      -Complex.I * starRingEnd ℂ ((Real.pi : ℂ) * b) by rw [map_mul, Complex.conj_ofReal]; ring]
    have hre : (-Complex.I * starRingEnd ℂ ((Real.pi : ℂ) * b)).re = -((Real.pi : ℂ) * b).im := by
      simp [Complex.mul_re, Complex.conj_im]
    rw [hre]
    exact ⟨by linarith [hb_im_neg.1], by linarith [hb_im_neg.2]⟩
  obtain ⟨k, hk⟩ := Complex.sin_eq_sin_iff.mp hsin_eq
  rcases hk with hk1 | hk2
  · have hre_eq : z₂.re = 2 * (k : ℝ) * Real.pi + z₁.re := by
      have h := congrArg Complex.re hk1
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] at h
      exact h
    have hlt : |2 * (k : ℝ) * Real.pi| < Real.pi := by
      rw [show 2 * (k : ℝ) * Real.pi = z₂.re - z₁.re by linarith, abs_lt]
      exact ⟨by linarith [hz1_re.2, hz2_re.1], by linarith [hz1_re.1, hz2_re.2]⟩
    have hk_abs : |(k : ℝ)| < 1 / 2 := by
      rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos Real.pi_pos] at hlt
      nlinarith [Real.pi_pos]
    have hk0 : k = 0 := by
      by_contra hne0
      have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hne0
      linarith
    rw [hk0, Int.cast_zero, mul_zero, zero_mul, zero_add] at hk1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    exact mul_left_cancel₀ hpi hk1.symm
  · have him_eq : z₂.im = -z₁.im := by
      have h := congrArg Complex.im hk2
      simp only [Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.intCast_re, Complex.intCast_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_sub] at h
      exact h
    linarith [hq_im_neg, hz2_im]

lemma chartOmegaHalf_midline_re_zero {τ : ℝ} (hτ : τ ≠ 0) :
    (chartOmegaHalf ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re = 0 := by
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · have hpos' : 0 < -τ := neg_pos.mpr hneg
    have hq_pos := chartQ_midline_pos hpos'
    set ζp : ℂ := (1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)
    set ζm : ℂ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
    have hconj_ζ : ζm = starRingEnd ℂ ζp := by
      apply Complex.ext <;> simp [ζm, ζp]
    have h0 : 0 ≤ ζp.re := by simp [ζp]
    have h1 : ζp.re ≤ 1 / 2 := by simp [ζp]
    have hne : ζp ≠ 1 / 2 := fun h => by
      have := congrArg Complex.im h; simp [ζp] at this; linarith
    have hb_conj : chartB ζm = starRingEnd ℂ (chartB ζp) := hconj_ζ ▸ chartB_conj h0 h1 hne
    have hq_conj : chartQ ζm = starRingEnd ℂ (chartQ ζp) := hconj_ζ ▸ chartQ_conj h0 h1 hne
    unfold chartOmegaHalf
    rw [hb_conj, hq_conj, hq_pos]
    have hprod : chartB ζp * (-Complex.I * starRingEnd ℂ (chartB ζp)) =
        -Complex.I * (((Complex.normSq (chartB ζp) : ℝ) : ℂ)) := by
      rw [mul_comm (-Complex.I) (starRingEnd ℂ (chartB ζp)), ← mul_assoc, Complex.mul_conj]
      ring
    rw [mul_assoc, ← map_mul, hprod]
    rw [show starRingEnd ℂ (-Complex.I * ((Complex.normSq (chartB ζp) : ℝ) : ℂ)) =
      Complex.I * ((Complex.normSq (chartB ζp) : ℝ) : ℂ) from by
        rw [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]; ring]
    rw [show (2 * (Real.pi : ℂ) / 3) * (Complex.I * ((Complex.normSq (chartB ζp) : ℝ) : ℂ)) =
      Complex.I * (((2 * Real.pi / 3 * Complex.normSq (chartB ζp) : ℝ) : ℂ)) by push_cast; ring]
    simp
  · exact False.elim (hτ rfl)
  · have hq_pos := chartQ_midline_pos hpos
    unfold chartOmegaHalf
    rw [hq_pos]
    set ζp : ℂ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
    have hprod : chartB ζp * (-Complex.I * starRingEnd ℂ (chartB ζp)) =
        -Complex.I * (((Complex.normSq (chartB ζp) : ℝ) : ℂ)) := by
      rw [mul_comm (-Complex.I) (starRingEnd ℂ (chartB ζp)), ← mul_assoc, Complex.mul_conj]
      ring
    rw [mul_assoc, hprod]
    rw [show (2 * (Real.pi : ℂ) / 3) * (-Complex.I * ((Complex.normSq (chartB ζp) : ℝ) : ℂ)) =
      -Complex.I * (((2 * Real.pi / 3 * Complex.normSq (chartB ζp) : ℝ) : ℂ)) by push_cast; ring]
    simp

lemma chartOmega_reflect (ζ : ℂ) : chartOmega (1 - ζ) = -chartOmega ζ := by
  unfold chartOmega
  rcases lt_trichotomy ζ.re (1 / 2) with hlt | heq | hgt
  · have h1 : ¬ (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    have h2 : ζ.re ≤ 1 / 2 := hlt.le
    simp only [h1, h2, ↓reduceIte, sub_sub_cancel]
  · have h1 : (1 - ζ).re ≤ 1 / 2 := by
      rw [Complex.sub_re, Complex.one_re, heq]; norm_num
    have h2 : ζ.re ≤ 1 / 2 := heq.le
    simp only [h1, h2, ↓reduceIte]
    by_cases him : ζ.im = 0
    · have hhalf : ζ = 1 / 2 := Complex.ext (by simp [heq]) (by simp [him])
      subst hhalf
      have hsub : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
      have h0 : chartOmegaHalf (1 / 2 : ℂ) = 0 := by
        unfold chartOmegaHalf; rw [chartB_half, mul_zero, zero_mul]
      rw [hsub, h0, neg_zero]
    · have hconj : 1 - ζ = starRingEnd ℂ ζ := by
        apply Complex.ext
        · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, heq]; norm_num
        · simp
      have hre_zero : (chartOmegaHalf ζ).re = 0 := by
        have hζ_eq : ζ = (1 / 2 : ℂ) + Complex.I * (ζ.im : ℂ) := by
          apply Complex.ext <;> simp [heq]
        rw [hζ_eq]
        exact chartOmegaHalf_midline_re_zero him
      have hne : ζ ≠ 1 / 2 := fun h => him (by simp [h])
      rw [hconj, chartOmegaHalf_conj (by linarith) (by linarith) hne]
      apply Complex.ext
      · simp [hre_zero]
      · simp
  · have h1 : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    have h2 : ¬ ζ.re ≤ 1 / 2 := not_le.mpr hgt
    simp only [h1, h2, ↓reduceIte, neg_neg]

lemma chartOmega_eq_midpointOmega_of_mem_rMid {ζ : ℂ} (hζ : ζ ∈ ball (1 / 2 : ℂ) rMid) :
    chartOmega ζ = midpointOmega ζ := by
  by_cases hle : ζ.re ≤ 1 / 2
  · unfold chartOmega
    simp only [hle, ↓reduceIte]
    exact chartOmegaHalf_eq_midpointOmega (mem_rMid_ball hζ).1 (mem_rMid_ball hζ).2.1
  · have h1ζ : 1 - ζ ∈ ball (1 / 2 : ℂ) rMid := by
      rw [mem_ball, dist_eq_norm] at hζ ⊢
      have heq : (1 - ζ) - 1 / 2 = -(ζ - 1 / 2) := by ring
      rwa [heq, norm_neg]
    have hlt : (1 - ζ).re ≤ 1 / 2 := by simp; linarith [not_le.mp hle]
    rw [← neg_neg (chartOmega ζ), ← neg_neg (midpointOmega ζ),
      ← chartOmega_reflect, ← midpointOmega_reflect]
    unfold chartOmega
    simp only [hlt, ↓reduceIte]
    rw [chartOmegaHalf_eq_midpointOmega (mem_rMid_ball h1ζ).1 (mem_rMid_ball h1ζ).2.1]

lemma analyticAt_midpointOmega (ζ : ℂ) (hcos_norm : ‖Complex.cos ((Real.pi : ℂ) * ζ)‖ < 1) :
    AnalyticAt ℂ midpointOmega ζ := by
  unfold midpointOmega
  have hcos_an : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z)) ζ := by fun_prop
  have hA1 : AnalyticAt ℂ (fun z : ℂ => midpointA (Complex.cos ((Real.pi : ℂ) * z))) ζ :=
    (analyticOnNhd_midpointA _ (mem_ball_zero_iff.mpr hcos_norm)).comp
      (f := fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z)) hcos_an
  have hA2 : AnalyticAt ℂ (fun z : ℂ => midpointA (-Complex.cos ((Real.pi : ℂ) * z))) ζ :=
    (analyticOnNhd_midpointA _ (mem_ball_zero_iff.mpr (by simpa using hcos_norm))).comp
      (f := fun z : ℂ => -Complex.cos ((Real.pi : ℂ) * z)) hcos_an.neg
  exact ((analyticAt_const.mul hcos_an).mul hA1).mul hA2

private lemma cos_pi_im_ne_zero_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1)
    (him : ζ.im ≠ 0) : (Complex.cos ((Real.pi : ℂ) * ζ)).im ≠ 0 := by
  have hcos_im : (Complex.cos ((Real.pi : ℂ) * ζ)).im =
      -Real.sin (Real.pi * ζ.re) * Real.sinh (Real.pi * ζ.im) := by
    rw [show (Real.pi : ℂ) * ζ = ((Real.pi * ζ.re : ℝ) : ℂ) + ((Real.pi * ζ.im : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp]
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, sub_zero, zero_sub]
    ring
  rw [hcos_im]
  have hsin : 0 < Real.sin (Real.pi * ζ.re) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])
  have hsh : Real.sinh (Real.pi * ζ.im) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_pos.ne' him)
  exact mul_ne_zero (neg_ne_zero.mpr hsin.ne') hsh

lemma cos_pi_mem_slitPlane_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1)
    (him : ζ.im ≠ 0) : Complex.cos ((Real.pi : ℂ) * ζ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (cos_pi_im_ne_zero_of_im_ne_zero h0 h1 him))

lemma arsinh_cos_inner_slitPlane_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1)
    (him : ζ.im ≠ 0) :
    ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) ^ 2 + 1 ∈ Complex.slitPlane ∧
    (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) +
      (((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane := by
  set w : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  have hcos := cos_pi_mem_slitPlane_of_im_ne_zero h0 h1 him
  have hw_re : 0 < w.re := cpow_half_re_pos hcos
  have hw2_slit : w ^ 2 + 1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    rw [Complex.add_im, Complex.one_im, add_zero, show w ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) from
      cpow_half_sq _]
    exact cos_pi_im_ne_zero_of_im_ne_zero h0 h1 him
  have hs_re : 0 < ((w ^ 2 + 1) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hw2_slit
  refine ⟨hw2_slit, Complex.mem_slitPlane_iff.mpr (Or.inl ?_)⟩
  have hsum_re : (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)).re = w.re + ((w ^ 2 + 1) ^ (1 / 2 : ℂ)).re :=
    Complex.add_re _ _
  linarith

lemma re_chartB_pos_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) (him : ζ.im ≠ 0) :
    0 < (chartB ζ).re := by
  unfold chartB arsinhC
  set s := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  have hs_re : 0 < s.re := cpow_half_re_pos (cos_pi_mem_slitPlane_of_im_ne_zero h0 h1 him)
  set w := s + (s ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hsq_slit : s ^ 2 + 1 ∈ Complex.slitPlane :=
    (arsinh_cos_inner_slitPlane_of_im_ne_zero h0 h1 him).1
  have hsqrt_re : 0 < ((s ^ 2 + 1) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hsq_slit
  have hw_re : 0 < w.re := by
    have : w.re = s.re + ((s ^ 2 + 1) ^ (1 / 2 : ℂ)).re := Complex.add_re _ _
    linarith
  have hw_inv : w⁻¹ = (s ^ 2 + 1) ^ (1 / 2 : ℂ) - s := by
    refine inv_eq_of_mul_eq_one_right ?_
    dsimp [w]
    calc (s + (s ^ 2 + 1) ^ (1 / 2 : ℂ)) * ((s ^ 2 + 1) ^ (1 / 2 : ℂ) - s)
        = ((s ^ 2 + 1) ^ (1 / 2 : ℂ)) ^ 2 - s ^ 2 := by ring
      _ = (s ^ 2 + 1) - s ^ 2 := by rw [cpow_half_sq]
      _ = 1 := by ring
  have hnorm_gt1 : 1 < ‖w‖ := by
    have hdiff_re : (w - w⁻¹).re = 2 * s.re := by
      have : w - w⁻¹ = 2 * s := by dsimp [w]; rw [hw_inv]; ring
      rw [this]; simp [Complex.re_ofNat]
    have hwinv_lt : (w⁻¹).re < w.re := by
      have hsub : (w - w⁻¹).re = w.re - (w⁻¹).re := Complex.sub_re _ _
      linarith
    have hinv_re : (w⁻¹).re = w.re / Complex.normSq w := Complex.inv_re w
    have h0sq : 0 < Complex.normSq w := Complex.normSq_pos.mpr (by
      intro h0w; rw [h0w, Complex.zero_re] at hw_re; exact lt_irrefl 0 hw_re)
    have hnsq_gt1 : 1 < Complex.normSq w := by
      by_contra hle
      push Not at hle
      have hge : w.re ≤ w.re / Complex.normSq w := (le_div_iff₀ h0sq).mpr (by nlinarith)
      rw [← hinv_re] at hge
      linarith
    rw [Complex.normSq_eq_norm_sq] at hnsq_gt1
    nlinarith [norm_nonneg w]
  have hlog_re : 0 < (Complex.log w).re := by rw [Complex.log_re]; exact Real.log_pos hnorm_gt1
  rw [show (Real.pi : ℂ)⁻¹ = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  exact mul_pos (inv_pos.mpr Real.pi_pos) hlog_re

lemma chartQ_inner_im_pos_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1)
    (him : ζ.im ≠ 0) :
    0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2) +
      Complex.I * (1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2) ^ (1 / 2 : ℂ)).im := by
  set x := ζ.re
  set y := ζ.im
  set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)
  set s : ℂ := (1 - Z ^ 2) ^ (1 / 2 : ℂ)
  have h1z : 1 - Z ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := one_sub_two_sin_sq_eq_cos ζ
  have hs_re : 0 < s.re := by
    dsimp [s]; rw [h1z]
    exact cpow_half_re_pos (cos_pi_mem_slitPlane_of_im_ne_zero h0 h1 him)
  have hZ_im : Z.im = √2 * Real.cos (Real.pi * x / 2) * Real.sinh (Real.pi * y / 2) := by
    have harg : (Real.pi : ℂ) * ζ / 2 =
        ((Real.pi * x / 2 : ℝ) : ℂ) + ((Real.pi * y / 2 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [x, y]
    dsimp [Z]
    rw [harg, show (√2 : ℂ) = ((√2 : ℝ) : ℂ) from rfl, Complex.im_ofReal_mul,
      Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, sub_zero, zero_add]
    ring
  have him_add : (Z + Complex.I * s).im = Z.im + s.re := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  change 0 < (Z + Complex.I * s).im
  rw [him_add]
  have hs2 : s ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := by dsimp [s]; rw [h1z, cpow_half_sq]
  have hcos_re : (Complex.cos ((Real.pi : ℂ) * ζ)).re = Real.cos (Real.pi * x) * Real.cosh (Real.pi * y) := by
    have harg : (Real.pi : ℂ) * ζ = ((Real.pi * x : ℝ) : ℂ) + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [x, y]
    rw [harg, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
  have hcos_im : (Complex.cos ((Real.pi : ℂ) * ζ)).im = -Real.sin (Real.pi * x) * Real.sinh (Real.pi * y) := by
    have harg : (Real.pi : ℂ) * ζ = ((Real.pi * x : ℝ) : ℂ) + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [x, y]
    rw [harg, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, sub_zero, zero_sub]
    ring
  have hs2_re : s.re ^ 2 - s.im ^ 2 = Real.cos (Real.pi * x) * Real.cosh (Real.pi * y) := by
    have := congrArg Complex.re hs2; rw [sq, Complex.mul_re, hcos_re] at this; linarith
  have hs2_im : 2 * s.re * s.im = -Real.sin (Real.pi * x) * Real.sinh (Real.pi * y) := by
    have := congrArg Complex.im hs2; rw [sq, Complex.mul_im, hcos_im] at this; linarith
  suffices hlt : Z.im ^ 2 < s.re ^ 2 by
    have habs : |Z.im| < s.re := by
      rw [← Real.sqrt_sq hs_re.le, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    linarith [neg_abs_le Z.im]
  have hnorm_sq : (s.re ^ 2 + s.im ^ 2) ^ 2 =
      Real.cosh (Real.pi * y) ^ 2 - Real.sin (Real.pi * x) ^ 2 := by
    have hsc : Real.sin (Real.pi * x) ^ 2 + Real.cos (Real.pi * x) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    have hhc : Real.cosh (Real.pi * y) ^ 2 - Real.sinh (Real.pi * y) ^ 2 = 1 :=
      Real.cosh_sq_sub_sinh_sq _
    calc (s.re ^ 2 + s.im ^ 2) ^ 2
        = (s.re ^ 2 - s.im ^ 2) ^ 2 + (2 * s.re * s.im) ^ 2 := by ring
      _ = (Real.cos (Real.pi * x) * Real.cosh (Real.pi * y)) ^ 2 +
            (-Real.sin (Real.pi * x) * Real.sinh (Real.pi * y)) ^ 2 := by rw [hs2_re, hs2_im]
      _ = Real.cos (Real.pi * x) ^ 2 * Real.cosh (Real.pi * y) ^ 2 +
            Real.sin (Real.pi * x) ^ 2 * (Real.cosh (Real.pi * y) ^ 2 - 1) := by
          have : Real.sinh (Real.pi * y) ^ 2 = Real.cosh (Real.pi * y) ^ 2 - 1 := by linarith
          rw [mul_pow, mul_pow, neg_sq, this]
      _ = (Real.cos (Real.pi * x) ^ 2 + Real.sin (Real.pi * x) ^ 2) * Real.cosh (Real.pi * y) ^ 2 -
            Real.sin (Real.pi * x) ^ 2 := by ring
      _ = Real.cosh (Real.pi * y) ^ 2 - Real.sin (Real.pi * x) ^ 2 := by rw [add_comm, hsc, one_mul]
  have hZ_sq : 2 * Z.im ^ 2 = (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by
    rw [hZ_im]
    have h2cos : 2 * Real.cos (Real.pi * x / 2) ^ 2 = 1 + Real.cos (Real.pi * x) := by
      have := Real.cos_two_mul (Real.pi * x / 2)
      rw [show 2 * (Real.pi * x / 2) = Real.pi * x by ring] at this; linarith
    have h2sinh : 2 * Real.sinh (Real.pi * y / 2) ^ 2 = Real.cosh (Real.pi * y) - 1 := by
      have := Real.cosh_two_mul (Real.pi * y / 2)
      rw [show 2 * (Real.pi * y / 2) = Real.pi * y by ring] at this
      have h1 := Real.cosh_sq_sub_sinh_sq (Real.pi * y / 2); linarith
    calc 2 * (√2 * Real.cos (Real.pi * x / 2) * Real.sinh (Real.pi * y / 2)) ^ 2
        = (2 * Real.cos (Real.pi * x / 2) ^ 2) * (2 * Real.sinh (Real.pi * y / 2) ^ 2) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
      _ = (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by rw [h2cos, h2sinh]
  have hcosh_gt1 : 1 < Real.cosh (Real.pi * y) := by
    have hne0 : Real.pi * y ≠ 0 := mul_ne_zero Real.pi_pos.ne' him
    have hsq : Real.cosh (Real.pi * y) ^ 2 = 1 + Real.sinh (Real.pi * y) ^ 2 := by
      linarith [Real.cosh_sq_sub_sinh_sq (Real.pi * y)]
    have hsh : 0 < Real.sinh (Real.pi * y) ^ 2 := sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr hne0)
    nlinarith [Real.cosh_pos (Real.pi * y)]
  have h1cos_pos : 0 < 1 + Real.cos (Real.pi * x) := by
    have hsin : 0 < Real.sin (Real.pi * x) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])
    have hsc : Real.sin (Real.pi * x) ^ 2 + Real.cos (Real.pi * x) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    have hcos_lt : Real.cos (Real.pi * x) ^ 2 < 1 := by nlinarith [sq_pos_of_pos hsin]
    nlinarith [sq_nonneg (1 + Real.cos (Real.pi * x))]
  suffices hdiff : Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x) < s.re ^ 2 + s.im ^ 2 by
    linarith
  have hr_pos : 0 ≤ s.re ^ 2 + s.im ^ 2 := by positivity
  by_cases hrhs : Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x) < 0
  · exact lt_of_lt_of_le hrhs hr_pos
  · push Not at hrhs
    have hsq_lt : (Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x)) ^ 2 <
        (s.re ^ 2 + s.im ^ 2) ^ 2 := by
      rw [hnorm_sq]
      have hsc : Real.sin (Real.pi * x) ^ 2 = 1 - Real.cos (Real.pi * x) ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
      rw [hsc]
      have hdiff_id : (Real.cosh (Real.pi * y) ^ 2 - (1 - Real.cos (Real.pi * x) ^ 2)) -
          (Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x)) ^ 2 =
          2 * (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by ring
      have hpos : 0 < 2 * (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by positivity
      linarith
    nlinarith

lemma re_chartQ_Ioo_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) (him : ζ.im ≠ 0) :
    0 < (chartQ ζ).re ∧ (chartQ ζ).re < 1 := by
  unfold chartQ arccosC
  set u : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2) +
    Complex.I * (1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2) ^ (1 / 2 : ℂ)
  have him_u : 0 < u.im := chartQ_inner_im_pos_of_im_ne_zero h0 h1 him
  have hu_ne : u ≠ 0 := by intro h; rw [h, Complex.zero_im] at him_u; exact lt_irrefl 0 him_u
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have harg_eq : u.arg = Real.arccos (u.re / ‖u‖) := Complex.arg_of_im_pos him_u
  have hnsq : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by
    rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, sq]
  have hlt1 : u.re / ‖u‖ < 1 := by
    rw [div_lt_one hnorm_pos]
    have hsq : u.re ^ 2 < u.re ^ 2 + u.im ^ 2 := by linarith [sq_pos_of_pos him_u]
    nlinarith [norm_nonneg u]
  have hgt_neg1 : -1 < u.re / ‖u‖ := by
    rw [lt_div_iff₀ hnorm_pos]
    have hsq : u.re ^ 2 < u.re ^ 2 + u.im ^ 2 := by linarith [sq_pos_of_pos him_u]
    nlinarith [norm_nonneg u]
  have harg_pos : 0 < u.arg := by rw [harg_eq]; exact Real.arccos_pos.mpr hlt1
  have harg_lt : u.arg < Real.pi := by rw [harg_eq]; exact Real.arccos_lt_pi.mpr hgt_neg1
  have hre : ((Real.pi : ℂ)⁻¹ * (-Complex.I * Complex.log u)).re = u.arg / Real.pi := by
    rw [show (Real.pi : ℂ)⁻¹ = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.log_im]
    ring
  rw [hre]
  exact ⟨div_pos harg_pos Real.pi_pos, (div_lt_one Real.pi_pos).mpr harg_lt⟩

lemma arccos_sin_inner_slitPlane_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1)
    (him : ζ.im ≠ 0) :
    1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2 ∈ Complex.slitPlane ∧
    (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2) +
      Complex.I * (1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2) ^ (1 / 2 : ℂ) ∈
        Complex.slitPlane := by
  refine ⟨?_, Complex.mem_slitPlane_iff.mpr (Or.inr (chartQ_inner_im_pos_of_im_ne_zero h0 h1 him).ne')⟩
  rw [one_sub_two_sin_sq_eq_cos ζ]
  exact cos_pi_mem_slitPlane_of_im_ne_zero h0 h1 him

lemma analyticAt_chartB_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) (him : ζ.im ≠ 0) :
    AnalyticAt ℂ chartB ζ := by
  obtain ⟨h1', h2'⟩ := arsinh_cos_inner_slitPlane_of_im_ne_zero h0 h1 him
  have hcos_slit := cos_pi_mem_slitPlane_of_im_ne_zero h0 h1 him
  have hcos_an : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z)) ζ := by fun_prop
  have hsqrt_an : AnalyticAt ℂ (fun z : ℂ => (Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) ζ :=
    hcos_an.cpow analyticAt_const hcos_slit
  have hcomp : AnalyticAt ℂ (fun z : ℂ => arsinhC ((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ))) ζ :=
    (analyticAt_arsinhC h1' h2').comp (f := fun z : ℂ => (Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) hsqrt_an
  exact analyticAt_const.mul hcomp

lemma analyticAt_chartQ_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) (him : ζ.im ≠ 0) :
    AnalyticAt ℂ chartQ ζ := by
  obtain ⟨h1', h2'⟩ := arccos_sin_inner_slitPlane_of_im_ne_zero h0 h1 him
  have hZ_an : AnalyticAt ℂ (fun z : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)) ζ := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z : ℂ => arccosC ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2))) ζ :=
    (analyticAt_arccosC h1' h2').comp (f := fun z : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)) hZ_an
  exact analyticAt_const.mul hcomp

lemma analyticAt_chartOmegaHalf_of_im_ne_zero {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) (him : ζ.im ≠ 0) :
    AnalyticAt ℂ chartOmegaHalf ζ :=
  (analyticAt_const.mul (analyticAt_chartB_of_im_ne_zero h0 h1 him)).mul
    (analyticAt_chartQ_of_im_ne_zero h0 h1 him)

lemma analyticAt_chartOmega {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    AnalyticAt ℂ chartOmega ζ := by
  by_cases hmid : ζ = 1 / 2
  · subst hmid
    have hev : chartOmega =ᶠ[𝓝 (1 / 2 : ℂ)] midpointOmega := by
      filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) rMid_pos] with w hw
      exact chartOmega_eq_midpointOmega_of_mem_rMid hw
    exact (analyticAt_midpointOmega (1 / 2) (mem_rMid_ball (mem_ball_self rMid_pos)).1).congr
      hev.symm
  rcases lt_trichotomy ζ.re (1 / 2) with hlt | heq | hgt
  · have hev : chartOmega =ᶠ[𝓝 ζ] chartOmegaHalf := by
      have hopen : ∀ᶠ w in 𝓝 ζ, w.re < 1 / 2 :=
        Complex.continuous_re.continuousAt.eventually (gt_mem_nhds hlt)
      filter_upwards [hopen] with w hw
      unfold chartOmega; simp only [hw.le, ↓reduceIte]
    exact (analyticAt_chartOmegaHalf h0 hlt.le hmid).congr hev.symm
  · have him : ζ.im ≠ 0 := fun h0im => hmid (Complex.ext (by simp [heq]) (by simp [h0im]))
    let r : ℝ := min (|ζ.im| / 2) (1 / 4)
    have hr_pos : 0 < r := lt_min (by positivity) (by norm_num)
    have hsub_strip : ∀ w ∈ ball ζ r, 0 < w.re ∧ w.re < 1 ∧ w.im ≠ 0 := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      have hre_le : |w.re - ζ.re| ≤ ‖w - ζ‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - ζ)
      have him_le : |w.im - ζ.im| ≤ ‖w - ζ‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - ζ)
      have hr1 : r ≤ 1 / 4 := min_le_right _ _
      have hr2 : r ≤ |ζ.im| / 2 := min_le_left _ _
      have hre_abs : |w.re - 1 / 2| < 1 / 4 := by
        rw [← heq]; exact lt_of_le_of_lt hre_le (lt_of_lt_of_le hw hr1)
      have him_abs : |w.im - ζ.im| < |ζ.im| / 2 := lt_of_le_of_lt him_le (lt_of_lt_of_le hw hr2)
      refine ⟨by linarith [(abs_lt.mp hre_abs).1], by linarith [(abs_lt.mp hre_abs).2], ?_⟩
      intro hw0
      rw [hw0, zero_sub, abs_neg] at him_abs
      linarith
    let f : ℂ → ℂ := chartOmegaHalf
    let g : ℂ → ℂ := fun w => -chartOmegaHalf (1 - w)
    have hf : AnalyticOnNhd ℂ f (ball ζ r) := by
      intro w hw
      obtain ⟨hw0, hw1, hwim⟩ := hsub_strip w hw
      exact analyticAt_chartOmegaHalf_of_im_ne_zero hw0 hw1 hwim
    have hg : AnalyticOnNhd ℂ g (ball ζ r) := by
      intro w hw
      obtain ⟨hw0, hw1, hwim⟩ := hsub_strip w hw
      have h1w0 : 0 < (1 - w).re := by simp; linarith
      have h1w1 : (1 - w).re < 1 := by simp; linarith
      have h1wim : (1 - w).im ≠ 0 := by simp; exact hwim
      have hcomp : AnalyticAt ℂ (fun z => chartOmegaHalf (1 - z)) w :=
        (analyticAt_chartOmegaHalf_of_im_ne_zero h1w0 h1w1 h1wim).comp (by fun_prop)
      exact hcomp.neg
    have hfreq : ∃ᶠ w in 𝓝[≠] ζ, f w = g w := by
      by_contra hnot
      rw [Filter.not_frequently, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnot
      obtain ⟨ε, hε, hne⟩ := hnot
      let t : ℝ := min ε r / 2
      have ht_pos : 0 < t := by positivity
      let w : ℂ := ζ + (t : ℂ) * Complex.I
      have hw_dist : dist w ζ < ε := by
        rw [dist_eq_norm, show w - ζ = (t : ℂ) * Complex.I by ring, norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
        exact lt_of_lt_of_le (half_lt_self (lt_min hε hr_pos)) (min_le_left _ _)
      have hw_ne : w ≠ ζ := by
        intro h
        have := congrArg Complex.im h
        simp [w] at this
        linarith
      have hw_re : w.re = 1 / 2 := by simp [w, heq]
      have hw_im : w.im ≠ 0 := by
        have hw_ball : w ∈ ball ζ r := by
          rw [mem_ball, dist_eq_norm, show w - ζ = (t : ℂ) * Complex.I by ring, norm_mul,
            Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
          exact lt_of_lt_of_le (half_lt_self (lt_min hε hr_pos)) (min_le_right _ _)
        exact (hsub_strip w hw_ball).2.2
      have hfg_w : f w = g w := by
        have h1w_conj : 1 - w = starRingEnd ℂ w := by
          apply Complex.ext
          · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hw_re]; norm_num
          · simp
        have hw_mid : w = (1 / 2 : ℂ) + Complex.I * (w.im : ℂ) := by
          apply Complex.ext <;> simp [hw_re]
        have hre_zero : (chartOmegaHalf w).re = 0 := by
          rw [hw_mid]; exact chartOmegaHalf_midline_re_zero hw_im
        have hne_half : w ≠ 1 / 2 := fun h => hw_im (by simp [h])
        have hconj_val := chartOmegaHalf_conj (by linarith) (by linarith) hne_half
        dsimp [f, g]
        rw [h1w_conj, hconj_val]
        apply Complex.ext <;> simp [hre_zero]
      exact absurd hfg_w (hne hw_dist hw_ne)
    have heqOn : EqOn f g (ball ζ r) :=
      hf.eqOn_of_preconnected_of_frequently_eq hg (convex_ball ζ r).isPreconnected
        (mem_ball_self hr_pos) hfreq
    have hev : chartOmega =ᶠ[𝓝 ζ] f := by
      filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with w hw
      by_cases hle : w.re ≤ 1 / 2
      · unfold chartOmega; simp only [hle, ↓reduceIte]; rfl
      · unfold chartOmega; simp only [hle, ↓reduceIte]; exact (heqOn hw).symm
    exact (hf ζ (mem_ball_self hr_pos)).congr hev.symm
  · have h10 : 0 ≤ (1 - ζ).re := by simp; linarith
    have h1lt : (1 - ζ).re < 1 / 2 := by simp; linarith
    have hev_rev : chartOmega =ᶠ[𝓝 (1 - ζ)] chartOmegaHalf := by
      have hopen : ∀ᶠ w in 𝓝 (1 - ζ), w.re < 1 / 2 :=
        Complex.continuous_re.continuousAt.eventually (gt_mem_nhds h1lt)
      filter_upwards [hopen] with w hw
      unfold chartOmega; simp only [hw.le, ↓reduceIte]
    have h1ne : (1 - ζ) ≠ 1 / 2 := fun h => by
      have := congrArg Complex.re h
      simp at this; linarith
    have han_at : AnalyticAt ℂ chartOmega (1 - ζ) :=
      (analyticAt_chartOmegaHalf h10 h1lt.le h1ne).congr hev_rev.symm
    have hcomp : AnalyticAt ℂ (fun w => -chartOmega (1 - w)) ζ :=
      (han_at.comp (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) ζ)).neg
    exact hcomp.congr (Filter.Eventually.of_forall fun w => by dsimp only; rw [chartOmega_reflect, neg_neg])

lemma continuousOn_chartOmega :
    ContinuousOn chartOmega {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
  fun _ hζ => (analyticAt_chartOmega hζ.1 hζ.2).continuousAt.continuousWithinAt

lemma chartOmega_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    chartOmega (starRingEnd ℂ ζ) = starRingEnd ℂ (chartOmega ζ) := by
  by_cases hle : ζ.re ≤ 1 / 2
  · have hconj_re : (starRingEnd ℂ ζ).re ≤ 1 / 2 := by simpa using hle
    unfold chartOmega
    simp only [hle, hconj_re, ↓reduceIte]
    by_cases hmid : ζ = 1 / 2
    · subst hmid
      have hconj_half : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
        apply Complex.ext <;> simp
      rw [hconj_half]
      have h0_val : chartOmegaHalf (1 / 2 : ℂ) = 0 := by
        unfold chartOmegaHalf; rw [chartB_half, mul_zero, zero_mul]
      rw [h0_val, map_zero]
    · exact chartOmegaHalf_conj h0 hle hmid
  · push Not at hle
    have hconj_gt : ¬ (starRingEnd ℂ ζ).re ≤ 1 / 2 := by simp; linarith
    have h10 : 0 ≤ (1 - ζ).re := by simp; linarith
    have h1le : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    have h1ne : 1 - ζ ≠ 1 / 2 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    unfold chartOmega
    simp only [hle.not_ge, hconj_gt, ↓reduceIte]
    rw [show 1 - starRingEnd ℂ ζ = starRingEnd ℂ (1 - ζ) by simp]
    rw [chartOmegaHalf_conj h10 h1le h1ne, map_neg]

lemma chartB_div_chartQ_midline_norm {τ : ℝ} (hτ : τ ≠ 0) :
    ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) /
      chartQ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ = 1 := by
  have hnorm_eq : ∀ {t : ℝ}, 0 < t →
      ‖chartB ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ =
        ‖chartQ ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ := by
    intro t ht
    rw [chartQ_midline_pos ht, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_conj]
  have hq_ne : chartQ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) ≠ 0 := by
    have hne : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) ≠ 1 / 2 := fun h => by
      have := congrArg Complex.im h; simp at this; exact hτ this
    have hre := (re_chartQ_Ioo (by simp) (by simp) hne).1
    intro h0; rw [h0, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hq_ne)]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · set ζp : ℂ := (1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)
    have hconj_ζ : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) = starRingEnd ℂ ζp := by
      apply Complex.ext <;> simp [ζp]
    have h0 : 0 ≤ ζp.re := by simp [ζp]
    have h1 : ζp.re ≤ 1 / 2 := by simp [ζp]
    have hne : ζp ≠ 1 / 2 := fun h => by
      have := congrArg Complex.im h; simp [ζp] at this; linarith
    rw [hconj_ζ, chartB_conj h0 h1 hne, chartQ_conj h0 h1 hne,
      Complex.norm_conj, Complex.norm_conj]
    exact hnorm_eq (neg_pos.mpr hneg)
  · exact hnorm_eq hpos

end FormalResearch.ModularBootstrap.Chart
