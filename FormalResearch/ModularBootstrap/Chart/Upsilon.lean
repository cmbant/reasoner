module

public import FormalResearch.ModularBootstrap.Chart.MidpointAndUpsilon

/-!
# Logarithmic Integrand, Primitive `Υ(ζ)`, and Lemma S3 (`vlo:S3`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S3 (`vlo:S3`,
lines 412–439).

Defines:
* `chartLogBQ`: the analytic continuation of `log(b(ζ)/q(ζ))` across `ζ = 1/2` and by
  odd reflection `ζ ↦ 1 - ζ` to the closed strip `{0 ≤ Re ζ ≤ 1}`.
* `chartIntegrand ζ := chartLogBQ ζ * deriv chartOmega ζ` and
  `chartUpsilon ζ := B(μ*) + ∫_0^ζ log(b/q) dω` (`Υ(ζ)`), via `Complex.wedgeIntegral 0 ζ`.

Proves **Lemma S3**:
* `lemma_S3_positivity`: positivity of `b`, `q`, `ω` on `(0, 1/2)` and midpoint representation
  `b = √s · A(s)`, `q = √s · A(-s)` (`A(0) = 1/π`).
* `lemma_S3_strip`: holomorphy of `ω` and `Υ` on `0 < Re ζ < 1`, continuity on `0 ≤ Re ζ ≤ 1`,
  reflections `ω(1 - ζ) = -ω(ζ)`, `Υ(1 - ζ) = Υ(ζ)`, and conjugation symmetries.
* `lemma_S3_left_edge`: left-edge identities `b(iτ) = x₀(τ)`, `q(iτ) = 1/2 - i y₀(τ)`,
  `sinh(π x₀) = √(cosh πτ)`, `sinh(π y₀) = √2 sinh(πτ/2)`, `ω(iτ) = μ(τ) - i ν(τ)`,
  and edge contact `Re Υ(iτ) = B(ω(iτ))`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Chart

/-- Closed vertical strip `0 ≤ Re ζ ≤ 1`. -/
def stripClosed : Set ℂ := {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1}

/-- Open vertical strip `0 < Re ζ < 1`. -/
def stripOpen : Set ℂ := {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1}

private lemma isOpen_stripOpen : IsOpen stripOpen :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private lemma convex_stripOpen : Convex ℝ stripOpen := by
  intro x hx y hy a b ha hb hab
  have h := convex_Ioo (0 : ℝ) 1 hx hy ha hb hab
  simpa [stripOpen, Complex.add_re, Complex.real_smul] using h

private lemma isPreconnected_stripOpen : IsPreconnected stripOpen :=
  convex_stripOpen.isPreconnected

/-! ### Section 1: Analytic extension of `log(b(ζ)/q(ζ))` on `0 ≤ Re ζ ≤ 1` -/

lemma div_mem_slitPlane_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    a / b ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hb_ne : b ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have hreal : a / b = ((a / b).re : ℂ) := Complex.ext rfl h.2
  have ha_eq : a = ((a / b).re : ℂ) * b := by
    rw [show ((a / b).re : ℂ) = a / b from hreal.symm, div_mul_cancel₀ _ hb_ne]
  have ha_re : a.re = (a / b).re * b.re := by
    conv_lhs => rw [ha_eq]
    rw [Complex.re_ofReal_mul]
  have hnonpos : (a / b).re * b.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.1 hb.le
  linarith

lemma log_div_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log (a / b) = Complex.log a - Complex.log b := by
  have ha_ne : a ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at ha; exact lt_irrefl 0 ha
  have hb_ne : b ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have ha_arg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hb_arg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have him_gt : -Real.pi < (Complex.log a - Complex.log b).im := by
    rw [Complex.sub_im, Complex.log_im, Complex.log_im]
    linarith [(abs_lt.mp ha_arg).1, (abs_lt.mp hb_arg).2]
  have him_le : (Complex.log a - Complex.log b).im ≤ Real.pi := by
    rw [Complex.sub_im, Complex.log_im, Complex.log_im]
    linarith [(abs_lt.mp ha_arg).2, (abs_lt.mp hb_arg).1]
  have hexp : Complex.exp (Complex.log a - Complex.log b) = a / b := by
    rw [Complex.exp_sub, Complex.exp_log ha_ne, Complex.exp_log hb_ne]
  rw [← hexp, Complex.log_exp him_gt him_le]

/-- Analytic continuation of `log(b(ζ)/q(ζ))` to the closed strip `0 ≤ Re ζ ≤ 1` via odd
reflection `ζ ↦ 1 - ζ`. -/
noncomputable def chartLogBQ (ζ : ℂ) : ℂ :=
  if ζ.re ≤ 1 / 2 then Complex.log (chartB ζ / chartQ ζ)
  else -Complex.log (chartB (1 - ζ) / chartQ (1 - ζ))

/-- Midpoint factor `log(A(cos πζ) / A(-cos πζ))` matching `chartLogBQ` near `ζ = 1/2`. -/
noncomputable def midpointLogBQ (ζ : ℂ) : ℂ :=
  Complex.log (midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) /
    midpointA (-Complex.cos ((Real.pi : ℂ) * ζ)))

lemma chartLogBQ_eq_sub {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    chartLogBQ ζ = Complex.log (chartB ζ) - Complex.log (chartQ ζ) := by
  unfold chartLogBQ
  simp only [h1, ↓reduceIte]
  exact log_div_of_re_pos (re_chartB_pos h0 h1 hne) (re_chartQ_Ioo h0 h1 hne).1

lemma chartLogBQ_reflect (ζ : ℂ) : chartLogBQ (1 - ζ) = -chartLogBQ ζ := by
  unfold chartLogBQ
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
      rw [hsub, chartB_half, zero_div, Complex.log_zero, neg_zero]
    · have hconj : 1 - ζ = starRingEnd ℂ ζ := by
        apply Complex.ext
        · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, heq]; norm_num
        · simp
      have hne : ζ ≠ 1 / 2 := fun h => him (by simp [h])
      have h0 : 0 ≤ ζ.re := by linarith
      have hb_re : 0 < (chartB ζ).re := re_chartB_pos h0 h2 hne
      have hq_re : 0 < (chartQ ζ).re := (re_chartQ_Ioo h0 h2 hne).1
      have hslit : chartB ζ / chartQ ζ ∈ Complex.slitPlane :=
        div_mem_slitPlane_of_re_pos hb_re hq_re
      have harg : (chartB ζ / chartQ ζ).arg ≠ Real.pi :=
        (Complex.mem_slitPlane_iff_arg.mp hslit).1
      have hζ_mid : ζ = (1 / 2 : ℂ) + Complex.I * (ζ.im : ℂ) := by
        apply Complex.ext <;> simp [heq]
      have hnorm : ‖chartB ζ / chartQ ζ‖ = 1 := by
        rw [hζ_mid]; exact chartB_div_chartQ_midline_norm him
      have hlog_re : (Complex.log (chartB ζ / chartQ ζ)).re = 0 := by
        rw [Complex.log_re, hnorm, Real.log_one]
      rw [hconj, chartB_conj h0 h2 hne, chartQ_conj h0 h2 hne, ← map_div₀,
        Complex.log_conj _ harg]
      apply Complex.ext <;> simp [hlog_re]
  · have h1 : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    have h2 : ¬ ζ.re ≤ 1 / 2 := not_le.mpr hgt
    simp only [h1, h2, ↓reduceIte, neg_neg]

private lemma rMid_le_half : rMid ≤ 1 / 2 := by
  by_contra hgt
  push Not at hgt
  have h1_mem : (1 : ℂ) ∈ ball (1 / 2 : ℂ) rMid := by
    rw [mem_ball, dist_eq_norm, show (1 : ℂ) - 1 / 2 = (1 / 2 : ℝ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    exact hgt
  have hcos_lt := (mem_rMid_ball h1_mem).1
  have hcos_eq : Complex.cos ((Real.pi : ℂ) * (1 : ℂ)) = -1 := by simp
  rw [hcos_eq, norm_neg, norm_one] at hcos_lt
  exact lt_irrefl 1 hcos_lt

lemma chartLogBQ_eq_midpointLogBQ_of_mem_rMid {ζ : ℂ} (hζ : ζ ∈ ball (1 / 2 : ℂ) rMid) :
    chartLogBQ ζ = midpointLogBQ ζ := by
  have hstrip : 0 < ζ.re ∧ ζ.re < 1 := by
    rw [mem_ball, dist_eq_norm] at hζ
    have hre_le : |ζ.re - 1 / 2| ≤ ‖ζ - 1 / 2‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (ζ - 1 / 2)
    have hlt : |ζ.re - 1 / 2| < 1 / 2 := lt_of_le_of_lt hre_le (lt_of_lt_of_le hζ rMid_le_half)
    exact ⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩
  by_cases hmid : ζ = 1 / 2
  · subst hmid
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) = 0 := by
      rw [show (Real.pi : ℂ) * (1 / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
    have hre_half : (1 / 2 : ℂ).re ≤ 1 / 2 := by simp
    unfold chartLogBQ midpointLogBQ
    simp only [hre_half, ↓reduceIte, chartB_half, zero_div, Complex.log_zero, hcos, neg_zero]
    rw [div_self (by rw [midpointA_zero]; simp [Real.pi_pos.ne']), Complex.log_one]
  · by_cases hle : ζ.re ≤ 1 / 2
    · obtain ⟨hcos_norm, hZ_re, _, _⟩ := mem_rMid_ball hζ
      have hcos_slit := cos_pi_mem_slitPlane hstrip.1.le hle hmid
      have hrt_ne : (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) ≠ 0 := by
        intro h0
        have hsq := congrArg (fun z : ℂ => z ^ 2) h0
        rw [cpow_half_sq, zero_pow two_ne_zero] at hsq
        exact Complex.slitPlane_ne_zero hcos_slit hsq
      unfold chartLogBQ midpointLogBQ
      simp only [hle, ↓reduceIte]
      rw [chartB_eq_midpointA hcos_norm, chartQ_eq_midpointA hcos_norm hZ_re,
        mul_div_mul_left _ _ hrt_ne]
    · push Not at hle
      have h1ζ : 1 - ζ ∈ ball (1 / 2 : ℂ) rMid := by
        rw [mem_ball, dist_eq_norm] at hζ ⊢
        rwa [show (1 - ζ) - 1 / 2 = -(ζ - 1 / 2) by ring, norm_neg]
      obtain ⟨hcos_norm1, hZ_re1, _, _⟩ := mem_rMid_ball h1ζ
      obtain ⟨_, _, hA1_re, hA2_re⟩ := mem_rMid_ball hζ
      have h1_le : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
      have h1_ge : 0 ≤ (1 - ζ).re := by simp; linarith [hstrip.2]
      have h1_ne : 1 - ζ ≠ 1 / 2 := fun h => hmid (by linear_combination -h)
      have hcos_slit1 := cos_pi_mem_slitPlane h1_ge h1_le h1_ne
      have hrt_ne1 : (Complex.cos ((Real.pi : ℂ) * (1 - ζ))) ^ (1 / 2 : ℂ) ≠ 0 := by
        intro h0
        have hsq := congrArg (fun z : ℂ => z ^ 2) h0
        rw [cpow_half_sq, zero_pow two_ne_zero] at hsq
        exact Complex.slitPlane_ne_zero hcos_slit1 hsq
      have hcos1 : Complex.cos ((Real.pi : ℂ) * (1 - ζ)) = -Complex.cos ((Real.pi : ℂ) * ζ) := by
        rw [mul_sub, mul_one, Complex.cos_pi_sub]
      have hslit_q : midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) /
          midpointA (-Complex.cos ((Real.pi : ℂ) * ζ)) ∈ Complex.slitPlane :=
        div_mem_slitPlane_of_re_pos hA1_re hA2_re
      have harg_q : (midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) /
          midpointA (-Complex.cos ((Real.pi : ℂ) * ζ))).arg ≠ Real.pi :=
        (Complex.mem_slitPlane_iff_arg.mp hslit_q).1
      unfold chartLogBQ midpointLogBQ
      simp only [hle.not_ge, ↓reduceIte]
      rw [chartB_eq_midpointA hcos_norm1, chartQ_eq_midpointA hcos_norm1 hZ_re1,
        mul_div_mul_left _ _ hrt_ne1, hcos1, neg_neg]
      rw [show midpointA (-Complex.cos ((Real.pi : ℂ) * ζ)) /
          midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) =
          (midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) /
            midpointA (-Complex.cos ((Real.pi : ℂ) * ζ)))⁻¹ by rw [inv_div],
        Complex.log_inv _ harg_q, neg_neg]

lemma analyticAt_chartLogBQ {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    AnalyticAt ℂ chartLogBQ ζ := by
  by_cases hmid : ζ = 1 / 2
  · subst hmid
    have hev : chartLogBQ =ᶠ[𝓝 (1 / 2 : ℂ)] midpointLogBQ := by
      filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) rMid_pos] with w hw
      exact chartLogBQ_eq_midpointLogBQ_of_mem_rMid hw
    have han_mid : AnalyticAt ℂ midpointLogBQ (1 / 2 : ℂ) := by
      obtain ⟨hcos_norm, _, hA1_re, hA2_re⟩ := mem_rMid_ball (mem_ball_self rMid_pos)
      have hcos_an : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z)) (1 / 2 : ℂ) := by
        fun_prop
      have hA1_an : AnalyticAt ℂ (fun z : ℂ => midpointA (Complex.cos ((Real.pi : ℂ) * z))) (1 / 2 : ℂ) :=
        (analyticOnNhd_midpointA _ (mem_ball_zero_iff.mpr hcos_norm)).comp
          (f := fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z)) hcos_an
      have hA2_an : AnalyticAt ℂ (fun z : ℂ => midpointA (-Complex.cos ((Real.pi : ℂ) * z))) (1 / 2 : ℂ) :=
        (analyticOnNhd_midpointA _ (mem_ball_zero_iff.mpr (by simpa using hcos_norm))).comp
          (f := fun z : ℂ => -Complex.cos ((Real.pi : ℂ) * z)) hcos_an.neg
      have hA2_ne : midpointA (-Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ))) ≠ 0 := by
        intro h0'; rw [h0', Complex.zero_re] at hA2_re; exact lt_irrefl 0 hA2_re
      exact (hA1_an.div hA2_an hA2_ne).clog (div_mem_slitPlane_of_re_pos hA1_re hA2_re)
    exact han_mid.congr hev.symm
  rcases lt_trichotomy ζ.re (1 / 2) with hlt | heq | hgt
  · have hev : chartLogBQ =ᶠ[𝓝 ζ] fun w => Complex.log (chartB w / chartQ w) := by
      have hopen : ∀ᶠ w in 𝓝 ζ, w.re < 1 / 2 :=
        Complex.continuous_re.continuousAt.eventually (gt_mem_nhds hlt)
      filter_upwards [hopen] with w hw
      unfold chartLogBQ; simp only [hw.le, ↓reduceIte]
    have hq_ne : chartQ ζ ≠ 0 := by
      have hq := (re_chartQ_Ioo h0 hlt.le hmid).1
      intro h0'; rw [h0', Complex.zero_re] at hq; exact lt_irrefl 0 hq
    have hslit := div_mem_slitPlane_of_re_pos (re_chartB_pos h0 hlt.le hmid)
      (re_chartQ_Ioo h0 hlt.le hmid).1
    have han_div : AnalyticAt ℂ (fun w => chartB w / chartQ w) ζ :=
      (analyticAt_chartB h0 hlt.le hmid).div (analyticAt_chartQ h0 hlt.le hmid) hq_ne
    exact (han_div.clog hslit).congr hev.symm
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
    let f : ℂ → ℂ := fun w => Complex.log (chartB w / chartQ w)
    let g : ℂ → ℂ := fun w => -Complex.log (chartB (1 - w) / chartQ (1 - w))
    have hf : AnalyticOnNhd ℂ f (ball ζ r) := by
      intro w hw
      obtain ⟨hw0, hw1, hwim⟩ := hsub_strip w hw
      have hb_re := re_chartB_pos_of_im_ne_zero hw0 hw1 hwim
      have hq_re := (re_chartQ_Ioo_of_im_ne_zero hw0 hw1 hwim).1
      have hq_ne : chartQ w ≠ 0 := by intro h0'; rw [h0', Complex.zero_re] at hq_re; exact lt_irrefl 0 hq_re
      exact ((analyticAt_chartB_of_im_ne_zero hw0 hw1 hwim).div
        (analyticAt_chartQ_of_im_ne_zero hw0 hw1 hwim) hq_ne).clog
        (div_mem_slitPlane_of_re_pos hb_re hq_re)
    have hg : AnalyticOnNhd ℂ g (ball ζ r) := by
      intro w hw
      obtain ⟨hw0, hw1, hwim⟩ := hsub_strip w hw
      have h1w0 : 0 < (1 - w).re := by simp; linarith
      have h1w1 : (1 - w).re < 1 := by simp; linarith
      have h1wim : (1 - w).im ≠ 0 := by simp; exact hwim
      have hb_re := re_chartB_pos_of_im_ne_zero h1w0 h1w1 h1wim
      have hq_re := (re_chartQ_Ioo_of_im_ne_zero h1w0 h1w1 h1wim).1
      have hq_ne : chartQ (1 - w) ≠ 0 := by
        intro h0'; rw [h0', Complex.zero_re] at hq_re; exact lt_irrefl 0 hq_re
      have hcomp_b : AnalyticAt ℂ (fun z => chartB (1 - z)) w :=
        (analyticAt_chartB_of_im_ne_zero h1w0 h1w1 h1wim).comp (by fun_prop)
      have hcomp_q : AnalyticAt ℂ (fun z => chartQ (1 - z)) w :=
        (analyticAt_chartQ_of_im_ne_zero h1w0 h1w1 h1wim).comp (by fun_prop)
      exact ((hcomp_b.div hcomp_q hq_ne).clog (div_mem_slitPlane_of_re_pos hb_re hq_re)).neg
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
        intro h; have := congrArg Complex.im h; simp [w] at this; linarith
      have hw_re : w.re = 1 / 2 := by simp [w, heq]
      have hfg_w : f w = g w := by
        have hle1 : w.re ≤ 1 / 2 := hw_re.le
        have hle2 : (1 - w).re ≤ 1 / 2 := by
          rw [Complex.sub_re, Complex.one_re, hw_re]; norm_num
        have h1 : f w = chartLogBQ w := by
          dsimp [f]; unfold chartLogBQ; simp only [hle1, ↓reduceIte]
        have h2 : g w = -chartLogBQ (1 - w) := by
          dsimp [g]; unfold chartLogBQ; simp only [hle2, ↓reduceIte]
        rw [h1, h2, chartLogBQ_reflect, neg_neg]
      exact absurd hfg_w (hne hw_dist hw_ne)
    have heqOn : EqOn f g (ball ζ r) :=
      hf.eqOn_of_preconnected_of_frequently_eq hg (convex_ball ζ r).isPreconnected
        (mem_ball_self hr_pos) hfreq
    have hev : chartLogBQ =ᶠ[𝓝 ζ] f := by
      filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with w hw
      by_cases hle : w.re ≤ 1 / 2
      · unfold chartLogBQ; simp only [hle, ↓reduceIte]; rfl
      · unfold chartLogBQ; simp only [hle, ↓reduceIte]; exact (heqOn hw).symm
    exact (hf ζ (mem_ball_self hr_pos)).congr hev.symm
  · have h10 : 0 ≤ (1 - ζ).re := by simp; linarith
    have h1lt : (1 - ζ).re < 1 / 2 := by simp; linarith
    have hev_rev : chartLogBQ =ᶠ[𝓝 (1 - ζ)] fun w => Complex.log (chartB w / chartQ w) := by
      have hopen : ∀ᶠ w in 𝓝 (1 - ζ), w.re < 1 / 2 :=
        Complex.continuous_re.continuousAt.eventually (gt_mem_nhds h1lt)
      filter_upwards [hopen] with w hw
      unfold chartLogBQ; simp only [hw.le, ↓reduceIte]
    have h1ne : 1 - ζ ≠ 1 / 2 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hq_ne : chartQ (1 - ζ) ≠ 0 := by
      have hq := (re_chartQ_Ioo h10 h1lt.le h1ne).1
      intro h0'; rw [h0', Complex.zero_re] at hq; exact lt_irrefl 0 hq
    have hslit := div_mem_slitPlane_of_re_pos (re_chartB_pos h10 h1lt.le h1ne)
      (re_chartQ_Ioo h10 h1lt.le h1ne).1
    have han_at : AnalyticAt ℂ chartLogBQ (1 - ζ) :=
      (((analyticAt_chartB h10 h1lt.le h1ne).div
        (analyticAt_chartQ h10 h1lt.le h1ne) hq_ne).clog hslit).congr hev_rev.symm
    have hcomp : AnalyticAt ℂ (fun w => -chartLogBQ (1 - w)) ζ :=
      (han_at.comp (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) ζ)).neg
    exact hcomp.congr (Filter.Eventually.of_forall fun w => by dsimp only; rw [chartLogBQ_reflect, neg_neg])

lemma chartLogBQ_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    chartLogBQ (starRingEnd ℂ ζ) = starRingEnd ℂ (chartLogBQ ζ) := by
  by_cases hle : ζ.re ≤ 1 / 2
  · have hconj_re : (starRingEnd ℂ ζ).re ≤ 1 / 2 := by simpa using hle
    unfold chartLogBQ
    simp only [hle, hconj_re, ↓reduceIte]
    by_cases hmid : ζ = 1 / 2
    · subst hmid
      have hconj_half : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by apply Complex.ext <;> simp
      rw [hconj_half, chartB_half, zero_div, Complex.log_zero, map_zero]
    · have hslit := div_mem_slitPlane_of_re_pos (re_chartB_pos h0 hle hmid)
        (re_chartQ_Ioo h0 hle hmid).1
      have harg : (chartB ζ / chartQ ζ).arg ≠ Real.pi :=
        (Complex.mem_slitPlane_iff_arg.mp hslit).1
      rw [chartB_conj h0 hle hmid, chartQ_conj h0 hle hmid, ← map_div₀, Complex.log_conj _ harg]
  · push Not at hle
    have hconj_gt : ¬ (starRingEnd ℂ ζ).re ≤ 1 / 2 := by simp; linarith
    have h10 : 0 ≤ (1 - ζ).re := by simp; linarith
    have h1le : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    have h1ne : 1 - ζ ≠ 1 / 2 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hslit := div_mem_slitPlane_of_re_pos (re_chartB_pos h10 h1le h1ne)
      (re_chartQ_Ioo h10 h1le h1ne).1
    have harg : (chartB (1 - ζ) / chartQ (1 - ζ)).arg ≠ Real.pi :=
      (Complex.mem_slitPlane_iff_arg.mp hslit).1
    unfold chartLogBQ
    simp only [hle.not_ge, hconj_gt, ↓reduceIte]
    rw [show 1 - starRingEnd ℂ ζ = starRingEnd ℂ (1 - ζ) by simp]
    rw [chartB_conj h10 h1le h1ne, chartQ_conj h10 h1le h1ne, ← map_div₀,
      Complex.log_conj _ harg, map_neg]

/-! ### Section 2: Holomorphic primitive `Υ(ζ)` on the strip -/

/-- Logarithmic differential coefficient `log(b(ζ)/q(ζ)) ω'(ζ)` defining `Υ(ζ)`. -/
noncomputable def chartIntegrand (ζ : ℂ) : ℂ :=
  chartLogBQ ζ * deriv chartOmega ζ

/-- Holomorphic primitive `Υ(ζ) = B(μ*) + ∫_0^ζ log(b/q) dω` (`lower_o1_two_edge.tex`,
Lemma S3). -/
noncomputable def chartUpsilon (ζ : ℂ) : ℂ :=
  (ComplexBessel.crudeExponentB muStar : ℂ) + Complex.wedgeIntegral 0 ζ chartIntegrand

lemma analyticAt_chartIntegrand {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    AnalyticAt ℂ chartIntegrand ζ :=
  (analyticAt_chartLogBQ h0 h1).mul (analyticAt_chartOmega h0 h1).deriv

lemma continuousOn_chartIntegrand : ContinuousOn chartIntegrand stripClosed :=
  fun _ hζ => (analyticAt_chartIntegrand hζ.1 hζ.2).continuousAt.continuousWithinAt

lemma isConservativeOn_chartIntegrand : Complex.IsConservativeOn chartIntegrand stripClosed :=
  DifferentiableOn.isConservativeOn fun _ hζ =>
    (analyticAt_chartIntegrand hζ.1 hζ.2).differentiableAt.differentiableWithinAt

private lemma mem_stripClosed_of_re_mem_uIcc {z w u : ℂ} (hz : z ∈ stripClosed)
    (hw : w ∈ stripClosed) (hu : u.re ∈ Set.uIcc z.re w.re) : u ∈ stripClosed := by
  have hsub : Set.uIcc z.re w.re ⊆ Icc (0 : ℝ) 1 := Set.uIcc_subset_Icc hz hw
  exact hsub hu

lemma wedgeIntegral_chartIntegrand_add {z w : ℂ} (hz : z ∈ stripClosed) (hw : w ∈ stripClosed) :
    Complex.wedgeIntegral 0 w chartIntegrand - Complex.wedgeIntegral 0 z chartIntegrand =
      Complex.wedgeIntegral z w chartIntegrand := by
  have h0 : (0 : ℂ) ∈ stripClosed := ⟨le_refl 0, zero_le_one⟩
  set I₁ := ∫ x in (0 : ℝ)..w.re, chartIntegrand (x + (0 : ℂ).im * Complex.I)
  set I₂ := Complex.I • ∫ y in (0 : ℝ)..w.im, chartIntegrand (w.re + y * Complex.I)
  set I₃ := ∫ x in (0 : ℝ)..z.re, chartIntegrand (x + (0 : ℂ).im * Complex.I)
  set I₄ := Complex.I • ∫ y in (0 : ℝ)..z.im, chartIntegrand (z.re + y * Complex.I)
  set I₅ := ∫ x in z.re..w.re, chartIntegrand (x + z.im * Complex.I)
  set I₆ := Complex.I • ∫ y in z.im..w.im, chartIntegrand (w.re + y * Complex.I)
  set I₇ := ∫ x in z.re..w.re, chartIntegrand (x + (0 : ℂ).im * Complex.I)
  set I₈ := Complex.I • ∫ y in (0 : ℝ)..z.im, chartIntegrand (w.re + y * Complex.I)
  have h_horiz : ∀ a₁ a₂ b : ℝ, a₁ ∈ Icc (0 : ℝ) 1 → a₂ ∈ Icc (0 : ℝ) 1 →
      IntervalIntegrable (fun x : ℝ => chartIntegrand (x + b * Complex.I)) volume a₁ a₂ := by
    intro a₁ a₂ b ha₁ ha₂
    refine (continuousOn_chartIntegrand.comp (by fun_prop) (fun x hx => ?_)).intervalIntegrable
    have hx_icc : x ∈ Icc (0 : ℝ) 1 := Set.uIcc_subset_Icc ha₁ ha₂ hx
    simpa [stripClosed] using hx_icc
  have h_vert : ∀ a : ℝ, a ∈ Icc (0 : ℝ) 1 → ∀ b₁ b₂ : ℝ,
      IntervalIntegrable (fun y : ℝ => chartIntegrand (a + y * Complex.I)) volume b₁ b₂ := by
    intro a ha b₁ b₂
    refine (continuousOn_chartIntegrand.comp (by fun_prop) (fun y _ => ?_)).intervalIntegrable
    simpa [stripClosed] using ha
  have hI₁ : I₁ = I₃ + I₇ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (h_horiz 0 z.re 0 h0 hz) (h_horiz z.re w.re 0 hz hw)).symm
  have hI₂ : I₂ = I₈ + I₆ := by
    dsimp [I₂, I₈, I₆]
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
      (h_vert w.re hw 0 z.im) (h_vert w.re hw z.im w.im)]
  have hrect_sub : Complex.Rectangle (z.re + (0 : ℂ).im * Complex.I) (w.re + z.im * Complex.I) ⊆
      stripClosed := by
    rintro u ⟨hu1, _⟩
    exact mem_stripClosed_of_re_mem_uIcc hz hw (by simpa using hu1)
  have hcons := isConservativeOn_chartIntegrand _ _ hrect_sub
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq] at hcons
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by simpa [I₄, I₅, I₇, I₈] using hcons
  change (I₁ + I₂) - (I₃ + I₄) = I₅ + I₆
  rw [hI₁, hI₂]
  linear_combination hI₀

lemma hasDerivAt_chartUpsilon {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    HasDerivAt chartUpsilon (chartIntegrand ζ) ζ := by
  let r : ℝ := min ζ.re (1 - ζ.re)
  have hr_pos : 0 < r := lt_min h0 (sub_pos.mpr h1)
  have hball_sub : ball ζ r ⊆ stripClosed := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hre_le : |w.re - ζ.re| ≤ ‖w - ζ‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - ζ)
    have hr1 : r ≤ ζ.re := min_le_left _ _
    have hr2 : r ≤ 1 - ζ.re := min_le_right _ _
    have hlt := abs_lt.mp (lt_of_le_of_lt hre_le hw)
    exact ⟨by linarith, by linarith⟩
  have hcons_ball : Complex.IsConservativeOn chartIntegrand (ball ζ r) :=
    isConservativeOn_chartIntegrand.mono hball_sub
  have hcont_ball : ContinuousOn chartIntegrand (ball ζ r) :=
    continuousOn_chartIntegrand.mono hball_sub
  have hd_wedge := hcons_ball.hasDerivAt_wedgeIntegral hcont_ball (mem_ball_self hr_pos)
  have hd_add := hd_wedge.const_add
    ((ComplexBessel.crudeExponentB muStar : ℂ) + Complex.wedgeIntegral 0 ζ chartIntegrand)
  refine hd_add.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with w hw
  unfold chartUpsilon
  have hw_strip : w ∈ stripClosed := hball_sub hw
  have hζ_strip : ζ ∈ stripClosed := ⟨h0.le, h1.le⟩
  have hadd := wedgeIntegral_chartIntegrand_add hζ_strip hw_strip
  linear_combination hadd

lemma analyticOnNhd_chartUpsilon : AnalyticOnNhd ℂ chartUpsilon stripOpen :=
  (DifferentiableOn.analyticOnNhd
    (fun _z hz => (hasDerivAt_chartUpsilon hz.1 hz.2).differentiableAt.differentiableWithinAt)
    isOpen_stripOpen)

lemma continuousOn_chartUpsilon : ContinuousOn chartUpsilon stripClosed := by
  intro ζ hζ
  obtain ⟨r, hr_pos, hf_ball⟩ := (analyticAt_chartIntegrand hζ.1 hζ.2).exists_ball_analyticOnNhd
  have hdiff_ball : DifferentiableOn ℂ chartIntegrand (ball ζ r) := hf_ball.differentiableOn
  have hcons_ball : Complex.IsConservativeOn chartIntegrand (ball ζ r) := hdiff_ball.isConservativeOn
  have hd_wedge := hcons_ball.hasDerivAt_wedgeIntegral hdiff_ball.continuousOn (mem_ball_self hr_pos)
  have hcont_local : ContinuousAt (fun w => chartUpsilon ζ + Complex.wedgeIntegral ζ w chartIntegrand) ζ :=
    hd_wedge.continuousAt.const_add _
  have hev : ∀ᶠ w in 𝓝[stripClosed] ζ,
      chartUpsilon w = chartUpsilon ζ + Complex.wedgeIntegral ζ w chartIntegrand := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with w hw hw_strip
    have hadd := wedgeIntegral_chartIntegrand_add hζ hw_strip
    unfold chartUpsilon
    linear_combination hadd
  exact hcont_local.continuousWithinAt.congr_of_eventuallyEq hev (by
    unfold chartUpsilon; simp [Complex.wedgeIntegral])

private lemma deriv_chartOmega_reflect {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    deriv chartOmega (1 - ζ) = deriv chartOmega ζ := by
  have h10 : 0 ≤ (1 - ζ).re := by simp; linarith
  have h11 : (1 - ζ).re ≤ 1 := by simp; linarith
  have hd1 : HasDerivAt chartOmega (deriv chartOmega (1 - ζ)) (1 - ζ) :=
    (analyticAt_chartOmega h10 h11).differentiableAt.hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => 1 - w) (-1) ζ := by
    simpa using (hasDerivAt_id ζ).const_sub (1 : ℂ)
  have hcomp : HasDerivAt (fun w : ℂ => chartOmega (1 - w)) (deriv chartOmega (1 - ζ) * (-1)) ζ :=
    hd1.comp ζ hlin
  have hcomp2 : HasDerivAt (fun w : ℂ => -chartOmega w) (-(deriv chartOmega ζ)) ζ :=
    (analyticAt_chartOmega h0 h1).differentiableAt.hasDerivAt.neg
  have heq : (fun w : ℂ => chartOmega (1 - w)) = (fun w : ℂ => -chartOmega w) :=
    funext chartOmega_reflect
  rw [heq] at hcomp
  have hu := hcomp.unique hcomp2
  linear_combination -hu

private lemma stripOpen_approx_tendsto (ζ : ℂ) (hζ : ζ ∈ stripClosed) :
    ∃ z : ℕ → ℂ, (∀ n, z n ∈ stripOpen) ∧ Tendsto z atTop (𝓝 ζ) := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  let z : ℕ → ℂ := fun n => ((1 - t n : ℝ) : ℂ) * ζ + (t n : ℂ) * (1 / 2 : ℂ)
  refine ⟨z, fun n => ?_, ?_⟩
  · have ht0 : 0 < t n := by dsimp [t]; positivity
    have ht1 : t n < 1 := by dsimp [t]; rw [div_lt_one (by positivity)]; linarith
    refine ⟨?_, ?_⟩
    · simp only [z, Complex.add_re, Complex.re_ofReal_mul, Complex.div_ofNat_re,
        Complex.one_re]
      nlinarith [hζ.1]
    · simp only [z, Complex.add_re, Complex.re_ofReal_mul, Complex.div_ofNat_re,
        Complex.one_re]
      nlinarith [hζ.2]
  · have ht_tend : Tendsto t atTop (𝓝 (0 : ℝ)) := by
      have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine (h0.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      dsimp [t]; push_cast; ring
    have h1_sub : Continuous (fun r : ℝ => 1 - r) := continuous_const.sub continuous_id
    have h1 : Tendsto (fun n => ((1 - t n : ℝ) : ℂ) * ζ) atTop (𝓝 (((1 - 0 : ℝ) : ℂ) * ζ)) :=
      ((Complex.continuous_ofReal.comp h1_sub).tendsto 0 |>.comp ht_tend).mul_const ζ
    have h2 : Tendsto (fun n => (t n : ℂ) * (1 / 2 : ℂ)) atTop (𝓝 ((0 : ℂ) * (1 / 2 : ℂ))) :=
      ((Complex.continuous_ofReal.tendsto 0).comp ht_tend).mul_const _
    simpa [z] using h1.add h2

lemma chartUpsilon_reflect {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    chartUpsilon (1 - ζ) = chartUpsilon ζ := by
  have h_open : ∀ w ∈ stripOpen, chartUpsilon (1 - w) = chartUpsilon w := by
    let g : ℂ → ℂ := fun w => chartUpsilon (1 - w) - chartUpsilon w
    have hg_deriv : ∀ w ∈ stripOpen, HasDerivAt g 0 w := by
      intro w hw
      have hw1 : 1 - w ∈ stripOpen := ⟨by simp; linarith [hw.2], by simp; linarith [hw.1]⟩
      have hd1 : HasDerivAt chartUpsilon (chartIntegrand (1 - w)) (1 - w) :=
        hasDerivAt_chartUpsilon hw1.1 hw1.2
      have hlin : HasDerivAt (fun u : ℂ => 1 - u) (-1) w := by
        simpa using (hasDerivAt_id w).const_sub (1 : ℂ)
      have hcomp := hd1.comp w hlin
      have hd2 := hasDerivAt_chartUpsilon hw.1 hw.2
      have hval : chartIntegrand (1 - w) * (-1) - chartIntegrand w = 0 := by
        unfold chartIntegrand
        rw [chartLogBQ_reflect, deriv_chartOmega_reflect hw.1.le hw.2.le]
        ring
      exact hval ▸ hcomp.sub hd2
    have hg_diff : DifferentiableOn ℂ g stripOpen :=
      fun w hw => (hg_deriv w hw).differentiableAt.differentiableWithinAt
    have hg_eq0 : stripOpen.EqOn (deriv g) 0 := fun w hw => (hg_deriv w hw).deriv
    have hhalf : (1 / 2 : ℂ) ∈ stripOpen := by constructor <;> norm_num
    intro w hw
    have hc := isOpen_stripOpen.is_const_of_deriv_eq_zero isPreconnected_stripOpen hg_diff hg_eq0 hw hhalf
    have hhalf_val : g (1 / 2 : ℂ) = 0 := by
      dsimp [g]; rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, sub_self]
    exact sub_eq_zero.mp (hc.trans hhalf_val)
  obtain ⟨z, hz_open, hz_tend⟩ := stripOpen_approx_tendsto ζ ⟨h0, h1⟩
  have h1z_tend : Tendsto (fun n => 1 - z n) atTop (𝓝 (1 - ζ)) := tendsto_const_nhds.sub hz_tend
  have hz_closed : ∀ n, z n ∈ stripClosed := fun n => ⟨(hz_open n).1.le, (hz_open n).2.le⟩
  have h1z_closed : ∀ n, 1 - z n ∈ stripClosed := fun n =>
    ⟨by simp; linarith [(hz_open n).2], by simp; linarith [(hz_open n).1]⟩
  have h_lhs : Tendsto (fun n => chartUpsilon (1 - z n)) atTop (𝓝 (chartUpsilon (1 - ζ))) :=
    (continuousOn_chartUpsilon _ ⟨by simp; linarith, by simp; linarith⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1z_tend
        (Filter.Eventually.of_forall h1z_closed))
  have h_rhs : Tendsto (fun n => chartUpsilon (z n)) atTop (𝓝 (chartUpsilon ζ)) :=
    (continuousOn_chartUpsilon _ ⟨h0, h1⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz_tend
        (Filter.Eventually.of_forall hz_closed))
  have h_eq : (fun n => chartUpsilon (1 - z n)) = (fun n => chartUpsilon (z n)) :=
    funext fun n => h_open (z n) (hz_open n)
  exact tendsto_nhds_unique h_lhs (h_eq ▸ h_rhs)

private lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z : ℂ} (hf : HasDerivAt f f' z) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') (starRingEnd ℂ z) := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  rw [Asymptotics.isLittleO_iff] at hf ⊢
  intro c hc
  have hconj_tend : Tendsto (starRingEnd ℂ) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto 0)
  filter_upwards [hf hc |>.filter_mono hconj_tend] with h hh
  have hh' : ‖f (z + starRingEnd ℂ h) - f z - starRingEnd ℂ h • f'‖ ≤ c * ‖starRingEnd ℂ h‖ := hh
  have hmap : starRingEnd ℂ (f (starRingEnd ℂ (starRingEnd ℂ z + h))) -
      starRingEnd ℂ (f (starRingEnd ℂ (starRingEnd ℂ z))) - h • starRingEnd ℂ f' =
      starRingEnd ℂ (f (z + starRingEnd ℂ h) - f z - starRingEnd ℂ h • f') := by
    simp only [map_sub, map_add, Complex.conj_conj, smul_eq_mul, map_mul]
  rw [hmap, Complex.norm_conj]
  simpa only [Complex.norm_conj] using hh'

private lemma chartIntegrand_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    chartIntegrand (starRingEnd ℂ ζ) = starRingEnd ℂ (chartIntegrand ζ) := by
  have h_open : ∀ w ∈ stripOpen, chartIntegrand (starRingEnd ℂ w) = starRingEnd ℂ (chartIntegrand w) := by
    intro w hw
    let r : ℝ := min w.re (1 - w.re)
    have hr_pos : 0 < r := lt_min hw.1 (sub_pos.mpr hw.2)
    have hd_w : HasDerivAt chartOmega (deriv chartOmega w) w :=
      (analyticAt_chartOmega hw.1.le hw.2.le).differentiableAt.hasDerivAt
    have hd_conj := hasDerivAt_conj_conj hd_w
    have hev : (fun u => starRingEnd ℂ (chartOmega (starRingEnd ℂ u))) =ᶠ[𝓝 (starRingEnd ℂ w)]
        chartOmega := by
      filter_upwards [Metric.ball_mem_nhds (starRingEnd ℂ w) hr_pos] with u hu
      rw [mem_ball, dist_eq_norm] at hu
      have hre_le : |u.re - (starRingEnd ℂ w).re| ≤ ‖u - starRingEnd ℂ w‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (u - starRingEnd ℂ w)
      have hlt := abs_lt.mp (lt_of_le_of_lt hre_le hu)
      have hu0 : 0 ≤ u.re := by simp at hlt; linarith [min_le_left w.re (1 - w.re)]
      have hu1 : u.re ≤ 1 := by simp at hlt; linarith [min_le_right w.re (1 - w.re)]
      rw [chartOmega_conj hu0 hu1, Complex.conj_conj]
    have hd_om : HasDerivAt chartOmega (starRingEnd ℂ (deriv chartOmega w)) (starRingEnd ℂ w) :=
      hd_conj.congr_of_eventuallyEq hev.symm
    have hderiv_eq : deriv chartOmega (starRingEnd ℂ w) = starRingEnd ℂ (deriv chartOmega w) :=
      hd_om.deriv
    unfold chartIntegrand
    rw [chartLogBQ_conj hw.1.le hw.2.le, hderiv_eq, map_mul]
  obtain ⟨z, hz_open, hz_tend⟩ := stripOpen_approx_tendsto ζ ⟨h0, h1⟩
  have hcz_tend : Tendsto (fun n => starRingEnd ℂ (z n)) atTop (𝓝 (starRingEnd ℂ ζ)) :=
    (Complex.continuous_conj.tendsto ζ).comp hz_tend
  have hz_closed : ∀ n, z n ∈ stripClosed := fun n => ⟨(hz_open n).1.le, (hz_open n).2.le⟩
  have hcz_closed : ∀ n, starRingEnd ℂ (z n) ∈ stripClosed := fun n =>
    ⟨by simp [(hz_open n).1.le], by simp [(hz_open n).2.le]⟩
  have h_lhs : Tendsto (fun n => chartIntegrand (starRingEnd ℂ (z n))) atTop
      (𝓝 (chartIntegrand (starRingEnd ℂ ζ))) :=
    (continuousOn_chartIntegrand _ ⟨by simp [h0], by simp [h1]⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcz_tend
        (Filter.Eventually.of_forall hcz_closed))
  have h_rhs : Tendsto (fun n => starRingEnd ℂ (chartIntegrand (z n))) atTop
      (𝓝 (starRingEnd ℂ (chartIntegrand ζ))) :=
    (Complex.continuous_conj.tendsto _).comp ((continuousOn_chartIntegrand _ ⟨h0, h1⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz_tend
        (Filter.Eventually.of_forall hz_closed)))
  have h_eq : (fun n => chartIntegrand (starRingEnd ℂ (z n))) =
      (fun n => starRingEnd ℂ (chartIntegrand (z n))) :=
    funext fun n => h_open (z n) (hz_open n)
  exact tendsto_nhds_unique h_lhs (h_eq ▸ h_rhs)

lemma chartUpsilon_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    chartUpsilon (starRingEnd ℂ ζ) = starRingEnd ℂ (chartUpsilon ζ) := by
  unfold chartUpsilon
  rw [map_add, Complex.conj_ofReal]
  congr 1
  unfold Complex.wedgeIntegral
  simp only [Complex.zero_re, Complex.zero_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_zero,
    zero_mul, add_zero, smul_eq_mul]
  rw [map_add, map_mul, Complex.conj_I]
  have h1_int : ∫ x in (0 : ℝ)..ζ.re, chartIntegrand (x : ℂ) =
      starRingEnd ℂ (∫ x in (0 : ℝ)..ζ.re, chartIntegrand (x : ℂ)) := by
    have hcongr : ∫ x in (0 : ℝ)..ζ.re, starRingEnd ℂ (chartIntegrand (x : ℂ)) =
        ∫ x in (0 : ℝ)..ζ.re, chartIntegrand (x : ℂ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hx_icc : x ∈ Icc (0 : ℝ) 1 := Set.uIcc_subset_Icc ⟨le_refl 0, zero_le_one⟩ ⟨h0, h1⟩ hx
      have hconj := chartIntegrand_conj (ζ := (x : ℂ)) (by simpa using hx_icc.1)
        (by simpa using hx_icc.2)
      have hconj_x : starRingEnd ℂ (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
      rw [hconj_x] at hconj
      exact hconj.symm
    have hc := Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm (μ := volume)
      (fun x : ℝ => chartIntegrand (x : ℂ)) (a := (0 : ℝ)) (b := ζ.re)
    change ∫ x in (0 : ℝ)..ζ.re, starRingEnd ℂ (chartIntegrand (x : ℂ)) =
      starRingEnd ℂ (∫ x in (0 : ℝ)..ζ.re, chartIntegrand (x : ℂ)) at hc
    rw [← hc]
    exact hcongr.symm
  have h2_int : ∫ y in (0 : ℝ)..(-ζ.im), chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I) =
      -(starRingEnd ℂ (∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I))) := by
    have hsub := intervalIntegral.integral_comp_neg
      (fun y : ℝ => chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)) (a := (0 : ℝ)) (b := ζ.im)
    rw [neg_zero] at hsub
    rw [intervalIntegral.integral_symm (-ζ.im) 0, ← hsub]
    have hcongr : ∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) =
        ∫ y in (0 : ℝ)..ζ.im, starRingEnd ℂ (chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      have harg : (ζ.re : ℂ) + ((-y : ℝ) : ℂ) * Complex.I =
          starRingEnd ℂ ((ζ.re : ℂ) + (y : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      rw [harg]
      exact chartIntegrand_conj (ζ := (ζ.re : ℂ) + (y : ℂ) * Complex.I)
        (by simpa using h0) (by simpa using h1)
    have hc := Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm (μ := volume)
      (fun y : ℝ => chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)) (a := (0 : ℝ)) (b := ζ.im)
    change ∫ y in (0 : ℝ)..ζ.im, starRingEnd ℂ (chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)) =
      starRingEnd ℂ (∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)) at hc
    rw [hcongr, hc]
  rw [← h1_int, h2_int]
  ring

/-! ### Section 3: Left-edge contact and Lemma S3 headlines -/

private lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have hz_ne : z ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have harg_lt : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hsin := Complex.sin_arg z
  have hcos := Complex.cos_arg hz_ne
  have htan : Real.tan z.arg = z.im / z.re := by
    rw [Real.tan_eq_sin_div_cos, hsin, hcos]
    have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    field_simp [hnorm]
  rw [← htan, Real.arctan_tan (abs_lt.mp harg_lt).1 (abs_lt.mp harg_lt).2]

private lemma edgeMu_pos_all (τ : ℝ) : 0 < edgeMu τ := by
  unfold edgeMu edgeX0
  have hch : 0 < √(Real.cosh (Real.pi * τ)) := Real.sqrt_pos.mpr (Real.cosh_pos _)
  have hsh : 0 < Real.arsinh √(Real.cosh (Real.pi * τ)) := Real.arsinh_pos_iff.mpr hch
  positivity

private lemma hasDerivAt_crudeExponentB_left_edge (τ : ℝ) :
    HasDerivAt (fun t : ℝ => ComplexBessel.crudeExponentB (chartOmega (Complex.I * (t : ℂ))))
      (edgeMuDeriv τ * Real.log (6 * edgeMu τ ^ 2 / (Real.pi * ‖chartOmega (Complex.I * (τ : ℂ))‖)) -
        edgeNuDeriv τ * (chartOmega (Complex.I * (τ : ℂ))).arg) τ := by
  have h_eq : (fun t : ℝ => ComplexBessel.crudeExponentB (chartOmega (Complex.I * (t : ℂ)))) =
      (fun t : ℝ => edgeMu t * (Real.log (6 / Real.pi) + 2 * Real.log (edgeMu t) -
          (1 / 2 : ℝ) * Real.log (edgeMu t ^ 2 + edgeNu t ^ 2)) -
        edgeMu t + edgeNu t * Real.arctan (edgeNu t / edgeMu t)) := by
    ext t
    rw [chartOmega_left_edge t]
    set μ := edgeMu t
    set ν := edgeNu t
    set ω := (μ : ℂ) - Complex.I * (ν : ℂ)
    have hμ_pos : 0 < μ := edgeMu_pos_all t
    have hr2_pos : 0 < μ ^ 2 + ν ^ 2 := by positivity
    have hω_re : ω.re = μ := by simp [ω]
    have hω_im : ω.im = -ν := by simp [ω]
    have hω_norm : ‖ω‖ = √(μ ^ 2 + ν ^ 2) := by
      have hsq : ‖ω‖ ^ 2 = μ ^ 2 + ν ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hω_re, hω_im]
        ring
      rw [← Real.sqrt_sq (norm_nonneg ω), hsq]
    have hω_arg : ω.arg = -Real.arctan (ν / μ) := by
      rw [arg_eq_arctan_of_re_pos (by rw [hω_re]; exact hμ_pos), hω_re, hω_im,
        neg_div, Real.arctan_neg]
    have hlog_eq : Real.log (6 * μ ^ 2 / (Real.pi * √(μ ^ 2 + ν ^ 2))) =
        Real.log (6 / Real.pi) + 2 * Real.log μ - (1 / 2 : ℝ) * Real.log (μ ^ 2 + ν ^ 2) := by
      have hs_pos : 0 < √(μ ^ 2 + ν ^ 2) := Real.sqrt_pos.mpr hr2_pos
      rw [show 6 * μ ^ 2 / (Real.pi * √(μ ^ 2 + ν ^ 2)) =
          (6 / Real.pi) * (μ ^ 2) / √(μ ^ 2 + ν ^ 2) by ring,
        Real.log_div (by positivity) hs_pos.ne',
        Real.log_mul (by positivity) (pow_pos hμ_pos 2).ne',
        Real.log_pow, Real.log_sqrt hr2_pos.le]
      push_cast; ring
    unfold ComplexBessel.crudeExponentB
    rw [hω_re, hω_im, hω_norm, hω_arg, hlog_eq]
    ring
  rw [h_eq]
  set μ := edgeMu τ
  set ν := edgeNu τ
  set μ' := edgeMuDeriv τ
  set ν' := edgeNuDeriv τ
  have hμ_pos : 0 < μ := edgeMu_pos_all τ
  have hμd : HasDerivAt edgeMu μ' τ := hasDerivAt_edgeMu τ
  have hνd : HasDerivAt edgeNu ν' τ := hasDerivAt_edgeNu τ
  have hr2_pos : 0 < μ ^ 2 + ν ^ 2 := by positivity
  have hr2d : HasDerivAt (fun t => edgeMu t ^ 2 + edgeNu t ^ 2) (2 * μ * μ' + 2 * ν * ν') τ := by
    simpa [two_mul] using (hμd.fun_pow 2).fun_add (hνd.fun_pow 2)
  have hlogμ_d : HasDerivAt (fun t => Real.log (edgeMu t)) (μ' / μ) τ :=
    hμd.log hμ_pos.ne'
  have hlogr2_d : HasDerivAt (fun t => Real.log (edgeMu t ^ 2 + edgeNu t ^ 2))
      ((2 * μ * μ' + 2 * ν * ν') / (μ ^ 2 + ν ^ 2)) τ :=
    hr2d.log hr2_pos.ne'
  have hlog_expr_d : HasDerivAt (fun t => Real.log (6 / Real.pi) + 2 * Real.log (edgeMu t) -
        (1 / 2 : ℝ) * Real.log (edgeMu t ^ 2 + edgeNu t ^ 2))
      (2 * (μ' / μ) - (1 / 2 : ℝ) * ((2 * μ * μ' + 2 * ν * ν') / (μ ^ 2 + ν ^ 2))) τ := by
    refine (((hasDerivAt_const τ (Real.log (6 / Real.pi))).fun_add
      (hlogμ_d.const_mul 2)).fun_sub (hlogr2_d.const_mul (1 / 2 : ℝ))).congr_deriv ?_
    ring
  have hterm1 : HasDerivAt (fun t => edgeMu t * (Real.log (6 / Real.pi) + 2 * Real.log (edgeMu t) -
        (1 / 2 : ℝ) * Real.log (edgeMu t ^ 2 + edgeNu t ^ 2)) - edgeMu t)
      (μ' * (Real.log (6 / Real.pi) + 2 * Real.log μ - (1 / 2 : ℝ) * Real.log (μ ^ 2 + ν ^ 2)) +
        μ * (2 * (μ' / μ) - (1 / 2 : ℝ) * ((2 * μ * μ' + 2 * ν * ν') / (μ ^ 2 + ν ^ 2))) - μ') τ :=
    (hμd.mul hlog_expr_d).sub hμd
  have hdiv_d : HasDerivAt (fun t => edgeNu t / edgeMu t) ((ν' * μ - ν * μ') / μ ^ 2) τ :=
    hνd.fun_div hμd hμ_pos.ne'
  have hatan_d : HasDerivAt (fun t => Real.arctan (edgeNu t / edgeMu t))
      ((ν' * μ - ν * μ') / (μ ^ 2 + ν ^ 2)) τ := by
    refine ((Real.hasDerivAt_arctan (ν / μ)).comp τ hdiv_d).congr_deriv ?_
    field_simp [hμ_pos.ne', hr2_pos.ne']
  have hterm2 := hνd.mul hatan_d
  refine (hterm1.add hterm2).congr_deriv ?_
  have hω_re : (chartOmega (Complex.I * (τ : ℂ))).re = μ := by
    rw [chartOmega_left_edge τ]; simp [μ]
  have hω_im : (chartOmega (Complex.I * (τ : ℂ))).im = -ν := by
    rw [chartOmega_left_edge τ]; simp [ν]
  have hω_norm : ‖chartOmega (Complex.I * (τ : ℂ))‖ = √(μ ^ 2 + ν ^ 2) := by
    have hsq : ‖chartOmega (Complex.I * (τ : ℂ))‖ ^ 2 = μ ^ 2 + ν ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hω_re, hω_im]
      ring
    rw [← Real.sqrt_sq (norm_nonneg _), hsq]
  have hω_arg : (chartOmega (Complex.I * (τ : ℂ))).arg = -Real.arctan (ν / μ) := by
    rw [arg_eq_arctan_of_re_pos (by rw [hω_re]; exact hμ_pos), hω_re, hω_im,
      neg_div, Real.arctan_neg]
  have hlog_eq : Real.log (6 * μ ^ 2 / (Real.pi * √(μ ^ 2 + ν ^ 2))) =
      Real.log (6 / Real.pi) + 2 * Real.log μ - (1 / 2 : ℝ) * Real.log (μ ^ 2 + ν ^ 2) := by
    have hs_pos : 0 < √(μ ^ 2 + ν ^ 2) := Real.sqrt_pos.mpr hr2_pos
    rw [show 6 * μ ^ 2 / (Real.pi * √(μ ^ 2 + ν ^ 2)) =
        (6 / Real.pi) * (μ ^ 2) / √(μ ^ 2 + ν ^ 2) by ring,
      Real.log_div (by positivity) hs_pos.ne',
      Real.log_mul (by positivity) (pow_pos hμ_pos 2).ne',
      Real.log_pow, Real.log_sqrt hr2_pos.le]
    push_cast; ring
  rw [hω_norm, hω_arg, hlog_eq]
  field_simp [hμ_pos.ne', hr2_pos.ne']
  ring

private lemma log_ofReal_div_of_re_pos {r : ℝ} (hr : 0 < r) {ω : ℂ} (hω : 0 < ω.re) :
    Complex.log ((r : ℂ) / ω) = (Real.log (r / ‖ω‖) : ℂ) - Complex.I * (ω.arg : ℂ) := by
  have hω_ne : ω ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hω; exact lt_irrefl 0 hω
  have hnorm_pos : 0 < ‖ω‖ := norm_pos_iff.mpr hω_ne
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hω))
  have him_gt : -Real.pi < ((Real.log (r / ‖ω‖) : ℂ) - Complex.I * (ω.arg : ℂ)).im := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_sub]
    linarith [harg.2, Real.pi_pos]
  have him_le : ((Real.log (r / ‖ω‖) : ℂ) - Complex.I * (ω.arg : ℂ)).im ≤ Real.pi := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_sub]
    linarith [harg.1, Real.pi_pos]
  have hnorm_mul : (‖ω‖ : ℂ) * ((Real.cos ω.arg : ℂ) + (Real.sin ω.arg : ℂ) * Complex.I) = ω := by
    have hcos := Complex.cos_arg hω_ne
    have hsin := Complex.sin_arg ω
    apply Complex.ext
    · simp [hcos]; exact mul_div_cancel₀ _ hnorm_pos.ne'
    · simp [hsin]; exact mul_div_cancel₀ _ hnorm_pos.ne'
  have hexp : Complex.exp ((Real.log (r / ‖ω‖) : ℂ) - Complex.I * (ω.arg : ℂ)) = (r : ℂ) / ω := by
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log (div_pos hr hnorm_pos),
      show Complex.I * (ω.arg : ℂ) = (ω.arg : ℂ) * Complex.I by ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hunit : (Real.cos ω.arg : ℂ) + (Real.sin ω.arg : ℂ) * Complex.I = ω / (‖ω‖ : ℂ) :=
      eq_div_of_mul_eq (Complex.ofReal_ne_zero.mpr hnorm_pos.ne') (by simpa [mul_comm] using hnorm_mul)
    rw [hunit, Complex.ofReal_div]
    field_simp [hnorm_pos.ne', hω_ne]
  rw [← hexp, Complex.log_exp him_gt him_le]

lemma re_chartUpsilon_left_edge (τ : ℝ) :
    (chartUpsilon (Complex.I * (τ : ℂ))).re =
      ComplexBessel.crudeExponentB (chartOmega (Complex.I * (τ : ℂ))) := by
  have hwedge : Complex.wedgeIntegral 0 (Complex.I * (τ : ℂ)) chartIntegrand =
      Complex.I * ∫ t in (0 : ℝ)..τ, chartIntegrand (Complex.I * (t : ℂ)) := by
    unfold Complex.wedgeIntegral
    simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.mul_im,
      one_mul, zero_add, intervalIntegral.integral_same, Complex.ofReal_zero, add_zero, smul_eq_mul]
    congr 2
    ext t
    rw [mul_comm (t : ℂ) Complex.I]
  have hint_cont : Continuous (fun t : ℝ => chartIntegrand (Complex.I * (t : ℂ))) := by
    refine continuousOn_chartIntegrand.comp_continuous (by fun_prop) fun t => ?_
    simp [stripClosed]
  have hint_re : (Complex.I * ∫ t in (0 : ℝ)..τ, chartIntegrand (Complex.I * (t : ℂ))).re =
      ∫ t in (0 : ℝ)..τ, (Complex.I * chartIntegrand (Complex.I * (t : ℂ))).re := by
    rw [← intervalIntegral.integral_const_mul Complex.I]
    exact (Complex.reCLM.intervalIntegral_comp_comm
      ((hint_cont.const_mul Complex.I).intervalIntegrable 0 τ)).symm
  have h_integrand_eq : ∀ t : ℝ, (Complex.I * chartIntegrand (Complex.I * (t : ℂ))).re =
      edgeMuDeriv t * Real.log (6 * edgeMu t ^ 2 / (Real.pi * ‖chartOmega (Complex.I * (t : ℂ))‖)) -
        edgeNuDeriv t * (chartOmega (Complex.I * (t : ℂ))).arg := by
    intro t
    have ht0 : 0 ≤ (Complex.I * (t : ℂ)).re := by simp
    have ht1 : (Complex.I * (t : ℂ)).re ≤ 1 / 2 := by simp
    have hd_om : HasDerivAt chartOmega (deriv chartOmega (Complex.I * (t : ℂ))) (Complex.I * (t : ℂ)) :=
      (analyticAt_chartOmega ht0 (by simp)).differentiableAt.hasDerivAt
    have hlin : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
    have hcomp := hd_om.comp t hlin
    have h_edge_d : HasDerivAt (fun s : ℝ => chartOmega (Complex.I * (s : ℂ)))
        ((edgeMuDeriv t : ℂ) - Complex.I * (edgeNuDeriv t : ℂ)) t := by
      have heq_fun : (fun s : ℝ => chartOmega (Complex.I * (s : ℂ))) =
          (fun s : ℝ => (edgeMu s : ℂ) - Complex.I * (edgeNu s : ℂ)) := by
        ext s; exact chartOmega_left_edge s
      rw [heq_fun]
      exact (hasDerivAt_edgeMu t).ofReal_comp.sub ((hasDerivAt_edgeNu t).ofReal_comp.const_mul Complex.I)
    have hderiv_I : deriv chartOmega (Complex.I * (t : ℂ)) * Complex.I =
        (edgeMuDeriv t : ℂ) - Complex.I * (edgeNuDeriv t : ℂ) := hcomp.unique h_edge_d
    have hμ_pos : 0 < edgeMu t := edgeMu_pos_all t
    have hdiv_eq : chartB (Complex.I * (t : ℂ)) / chartQ (Complex.I * (t : ℂ)) =
        ((6 * edgeMu t ^ 2 / Real.pi : ℝ) : ℂ) / chartOmega (Complex.I * (t : ℂ)) := by
      rw [chartB_left_edge t, chartQ_left_edge t, chartOmega_left_edge t]
      have hx : edgeX0 t = 3 * edgeMu t / Real.pi := by
        unfold edgeMu; field_simp [Real.pi_pos.ne']
      have hy : edgeY0 t = edgeNu t / (2 * edgeMu t) := by
        unfold edgeNu
        have hx0 : edgeX0 t ≠ 0 := by
          unfold edgeX0
          have := Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr (Real.cosh_pos (Real.pi * t)))
          positivity
        unfold edgeMu
        field_simp [Real.pi_pos.ne', hμ_pos.ne', hx0]
      rw [hx, hy]
      push_cast
      have hω_ne : (edgeMu t : ℂ) - Complex.I * (edgeNu t : ℂ) ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      field_simp [Real.pi_pos.ne', hμ_pos.ne', hω_ne]
      ring
    have hω_re : 0 < (chartOmega (Complex.I * (t : ℂ))).re := by
      rw [chartOmega_left_edge t]; simpa using hμ_pos
    have hlog_eq : chartLogBQ (Complex.I * (t : ℂ)) =
        (Real.log (6 * edgeMu t ^ 2 / (Real.pi * ‖chartOmega (Complex.I * (t : ℂ))‖)) : ℂ) -
          Complex.I * ((chartOmega (Complex.I * (t : ℂ))).arg : ℂ) := by
      unfold chartLogBQ
      simp only [ht1, ↓reduceIte]
      rw [hdiv_eq, log_ofReal_div_of_re_pos (by positivity) hω_re]
      congr 2
      rw [div_div]
    calc (Complex.I * chartIntegrand (Complex.I * (t : ℂ))).re
        = (chartLogBQ (Complex.I * (t : ℂ)) * (deriv chartOmega (Complex.I * (t : ℂ)) * Complex.I)).re := by
          unfold chartIntegrand; congr 1; ring
      _ = (((Real.log (6 * edgeMu t ^ 2 / (Real.pi * ‖chartOmega (Complex.I * (t : ℂ))‖)) : ℂ) -
            Complex.I * ((chartOmega (Complex.I * (t : ℂ))).arg : ℂ)) *
            ((edgeMuDeriv t : ℂ) - Complex.I * (edgeNuDeriv t : ℂ))).re := by
          rw [hlog_eq, hderiv_I]
      _ = edgeMuDeriv t * Real.log (6 * edgeMu t ^ 2 / (Real.pi * ‖chartOmega (Complex.I * (t : ℂ))‖)) -
            edgeNuDeriv t * (chartOmega (Complex.I * (t : ℂ))).arg := by
          simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
            mul_zero, zero_add, sub_zero, zero_sub]
          ring
  have hB_deriv : ∀ t ∈ [[(0 : ℝ), τ]],
      HasDerivAt (fun s : ℝ => ComplexBessel.crudeExponentB (chartOmega (Complex.I * (s : ℂ))))
        (Complex.I * chartIntegrand (Complex.I * (t : ℂ))).re t :=
    fun t _ => (h_integrand_eq t) ▸ hasDerivAt_crudeExponentB_left_edge t
  have hB_cont : IntervalIntegrable (fun t : ℝ => (Complex.I * chartIntegrand (Complex.I * (t : ℂ))).re)
      volume 0 τ :=
    (Complex.continuous_re.comp (continuous_const.mul hint_cont)).intervalIntegrable 0 τ
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hB_deriv hB_cont
  unfold chartUpsilon
  rw [hwedge, Complex.add_re, Complex.ofReal_re, hint_re, hftc]
  simp only [Complex.ofReal_zero, mul_zero, chartOmega_zero]
  ring

/-- **Lemma S3 (positivity and midpoint factorization, `vlo:S3`, `lower_o1_two_edge.tex`,
lines 412–439)**:
`b`, `q`, `ω` are positive on `(0, 1/2)` with `b = √s · A(s)` and `q = √s · A(-s)` near
`ζ = 1/2` (`s = cos πζ`), where `A` is holomorphic on `ball 0 1`, real on `(-1, 1)`, and
`A(0) = 1/π`. -/
theorem lemma_S3_positivity :
    (∀ x ∈ Ioo (0 : ℝ) (1 / 2), 0 < (chartB x).re ∧ (chartB x).im = 0) ∧
    (∀ x ∈ Ioo (0 : ℝ) (1 / 2), 0 < (chartQ x).re ∧ (chartQ x).im = 0) ∧
    (∀ x ∈ Ioo (0 : ℝ) (1 / 2), 0 < (chartOmega x).re ∧ (chartOmega x).im = 0) ∧
    AnalyticOnNhd ℂ midpointA (ball (0 : ℂ) 1) ∧
    midpointA 0 = ((1 / Real.pi : ℝ) : ℂ) ∧
    (∀ x : ℝ, |x| < 1 → (midpointA (x : ℂ)).im = 0) ∧
    (∀ ζ ∈ ball (1 / 2 : ℂ) rMid,
      chartB ζ = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) *
        midpointA (Complex.cos ((Real.pi : ℂ) * ζ)) ∧
      chartQ ζ = (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) *
        midpointA (-Complex.cos ((Real.pi : ℂ) * ζ))) := by
  refine ⟨fun _ hx => chartB_pos_of_mem_Ioo hx, fun _ hx => chartQ_pos_of_mem_Ioo hx,
    fun x hx => chartOmega_ofReal_pos hx, analyticOnNhd_midpointA, midpointA_zero,
    fun x hx => midpointA_ofReal_im_zero hx, fun ζ hζ => ?_⟩
  exact ⟨chartB_eq_midpointA (mem_rMid_ball hζ).1,
    chartQ_eq_midpointA (mem_rMid_ball hζ).1 (mem_rMid_ball hζ).2.1⟩

/-- **Lemma S3 (strip extension and symmetries, `vlo:S3`, `lower_o1_two_edge.tex`,
lines 412–439)**:
`ω` and `Υ` extend holomorphically to the open strip `0 < Re ζ < 1` and continuously to the
closed strip `0 ≤ Re ζ ≤ 1`, with `ω(1 - ζ) = -ω(ζ)`, `Υ(1 - ζ) = Υ(ζ)`, and conjugation
symmetry. -/
theorem lemma_S3_strip :
    AnalyticOnNhd ℂ chartOmega stripOpen ∧
    ContinuousOn chartOmega stripClosed ∧
    AnalyticOnNhd ℂ chartUpsilon stripOpen ∧
    ContinuousOn chartUpsilon stripClosed ∧
    (∀ ζ : ℂ, chartOmega (1 - ζ) = -chartOmega ζ) ∧
    (∀ ζ ∈ stripClosed, chartUpsilon (1 - ζ) = chartUpsilon ζ) ∧
    (∀ ζ ∈ stripClosed, chartOmega (starRingEnd ℂ ζ) = starRingEnd ℂ (chartOmega ζ)) ∧
    (∀ ζ ∈ stripClosed, chartUpsilon (starRingEnd ℂ ζ) = starRingEnd ℂ (chartUpsilon ζ)) :=
  ⟨fun _ hζ => analyticAt_chartOmega hζ.1.le hζ.2.le, continuousOn_chartOmega,
    analyticOnNhd_chartUpsilon, continuousOn_chartUpsilon, chartOmega_reflect,
    fun _ hζ => chartUpsilon_reflect hζ.1 hζ.2, fun _ hζ => chartOmega_conj hζ.1 hζ.2,
    fun _ hζ => chartUpsilon_conj hζ.1 hζ.2⟩

/-- **Lemma S3 (left edge and contact, `vlo:S3`, `lower_o1_two_edge.tex`, lines 412–439)**:
on `ζ = iτ`, `b(iτ) = x₀(τ)`, `q(iτ) = 1/2 - i y₀(τ)`, `sinh πx₀ = √(cosh πτ)`,
`sinh πy₀ = √2 sinh(πτ/2)`, `ω(iτ) = μ(τ) - i ν(τ)`, and `Re Υ(iτ) = B(ω(iτ))`. -/
theorem lemma_S3_left_edge :
    (∀ τ : ℝ, chartB (Complex.I * (τ : ℂ)) = (edgeX0 τ : ℂ)) ∧
    (∀ τ : ℝ, chartQ (Complex.I * (τ : ℂ)) = (1 / 2 : ℂ) - Complex.I * (edgeY0 τ : ℂ)) ∧
    (∀ τ : ℝ, Real.sinh (Real.pi * edgeX0 τ) = √(Real.cosh (Real.pi * τ))) ∧
    (∀ τ : ℝ, Real.sinh (Real.pi * edgeY0 τ) = √2 * Real.sinh (Real.pi * τ / 2)) ∧
    (∀ τ : ℝ, chartOmega (Complex.I * (τ : ℂ)) = (edgeMu τ : ℂ) - Complex.I * (edgeNu τ : ℂ)) ∧
    (∀ τ : ℝ, (chartUpsilon (Complex.I * (τ : ℂ))).re =
      ComplexBessel.crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) :=
  ⟨chartB_left_edge, chartQ_left_edge, sinh_pi_edgeX0, sinh_pi_edgeY0, chartOmega_left_edge,
    re_chartUpsilon_left_edge⟩

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_S3_positivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S3_positivity

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_S3_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S3_strip

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_S3_left_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S3_left_edge

end FormalResearch.ModularBootstrap.Chart
