module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3Strip
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3a

/-!
# FIVE-S, S3 (step 1b): boundary values of `ΔΦ_δ` and `ℰ_δ` on `ℝ` (`cts:smooth-env` (2))

For `δ ∈ (0, 1/4)` and every `x : ℝ`, as `b → (x : ℂ)` from the upper half-plane `{b : ℂ | 0 < b.im}`:
1. `DeltaPhi δ b → DeltaPhi δ (x : ℂ)`, where `DeltaPhi δ (x : ℂ)` is a well-defined Lebesgue integral;
2. `(DeltaPhi δ (x : ℂ)).im = -dphi δ x` for `xiStar ≤ x`, `0` for `|x| < xiStar`, and `dphi δ (-x)` for `x < -xiStar`;
3. `(DeltaPhi δ (x : ℂ)).re = (1/π) ∫_{ξ_*}^∞ δφ_δ'(y) log |tanh(π(x-y)/2) tanh(π(x+y)/2)| dy`;
4. `zetaD b → -i y(x)` for `x > xiStar`, `zetaD b → 0` for `x = xiStar`, `zetaD b → √((√2 - cosh πx)/(√2 + cosh πx))`
   for `|x| < xiStar`, and `zetaD b → i y(-x)` for `x < -xiStar`;
5. `Estripped δ b` has a positive real limit `EeBdry δ x` for every `x : ℝ`, satisfying
   `‖EeBdry δ x‖ * Real.exp (DeltaPhi δ (x : ℂ)).re = ‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖` for `xiStar ≤ x`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- The open upper half-plane `{b : ℂ | 0 < b.im}`. -/
def upperHalf : Set ℂ := {b : ℂ | 0 < b.im}

/-! ### 1. Boundary values of `φ_y` as `Im b → 0+` -/

private lemma sinh_ne_zero_of_im_lt_pi {w : ℂ} (h0 : 0 ≤ w.im) (h1 : w.im < π) (hne : w ≠ 0) :
    Complex.sinh w ≠ 0 := by
  intro h
  have hsq := norm_sinh_sq w
  rw [h, norm_zero] at hsq
  have hsin : Real.sin w.im = 0 := by nlinarith [sq_nonneg (Real.sinh w.re), sq_nonneg (Real.sin w.im)]
  have hsinh : Real.sinh w.re = 0 := by nlinarith [sq_nonneg (Real.sinh w.re), sq_nonneg (Real.sin w.im)]
  have hre : w.re = 0 := Real.sinh_eq_zero.mp hsinh
  have him : w.im = 0 := by
    rcases eq_or_lt_of_le h0 with h0' | h0'
    · exact h0'.symm
    · exfalso; exact (Real.sin_pos_of_pos_of_lt_pi h0' h1).ne' hsin
  exact hne (Complex.ext hre him)

lemma tendsto_phiY_real {x y : ℝ} (h1 : x ≠ y) (h2 : x ≠ -y) :
    Tendsto (phiY y) (𝓝[upperHalf] (x : ℂ)) (𝓝 (phiY y (x : ℂ))) := by
  set r : ℝ := min |x - y| |x + y| / 2 with hrdef
  have hr : 0 < r := by
    have h1' : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr h1)
    have h2' : 0 < |x + y| := abs_pos.mpr (by intro h; apply h2; linarith)
    positivity
  set S : Set ℂ := closedBall (x : ℂ) r ∩ {b : ℂ | 0 ≤ b.im ∧ b.im ≤ 1 / 2} with hSdef
  have hS_comp : IsCompact S := by
    refine (isCompact_closedBall (x : ℂ) r).inter_right ?_
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const)
  set F : ℂ → ℝ → ℂ := fun b t => phiYDeriv y (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) * (b - Complex.I / 2)
  have h_arg_ne : ∀ b ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.sinh ((π : ℂ) * (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2) - y)) ≠ 0 ∧
      Complex.sinh ((π : ℂ) * (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2) + y)) ≠ 0 := by
    intro b hb t ht
    have him_b0 : 0 ≤ b.im := hb.2.1
    have him_b1 : b.im ≤ 1 / 2 := hb.2.2
    have hpi := Real.pi_pos
    have him_w : (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)).im = (1 - t) / 2 + t * b.im := by
      simp [Complex.add_im, Complex.mul_im]; ring
    have him_ge : 0 ≤ (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)).im := by
      rw [him_w]; nlinarith [ht.1, ht.2]
    have him_lt : (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)).im < 1 := by
      rw [him_w]; nlinarith [ht.1, ht.2]
    have hne : ∀ s : ℝ, |x - s| ≥ 2 * r → Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2) - (s : ℂ) ≠ 0 := by
      intro s hs hzero
      rcases eq_or_lt_of_le ht.2 with ht1 | ht1
      · rw [ht1] at hzero
        have hb_eq : b = (s : ℂ) := by
          have : Complex.I / 2 + ((1 : ℝ) : ℂ) * (b - Complex.I / 2) = b := by simp
          rw [← this]; linear_combination hzero
        have hdist : ‖b - (x : ℂ)‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hb.1
        rw [hb_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hdist
        linarith
      · have him0 : (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2) - (s : ℂ)).im = 0 := by rw [hzero]; simp
        have him_pos : 0 < (1 - t) / 2 + t * b.im := by nlinarith [ht.1, ht1, him_b0]
        simp [Complex.add_im, Complex.mul_im] at him0
        linarith
    constructor
    · refine sinh_ne_zero_of_im_lt_pi (by rw [Complex.mul_im]; simp; nlinarith [ht.1, ht.2, him_b0])
        (by rw [Complex.mul_im]; simp; nlinarith [ht.1, ht.2, him_b0]) ?_
      intro h0
      apply hne y (by rw [hrdef]; linarith [min_le_left |x - y| |x + y|])
      have hpi_c : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_eq_zero.mp h0 |>.resolve_left hpi_c
    · refine sinh_ne_zero_of_im_lt_pi (by rw [Complex.mul_im]; simp; nlinarith [ht.1, ht.2, him_b0])
        (by rw [Complex.mul_im]; simp; nlinarith [ht.1, ht.2, him_b0]) ?_
      intro h0
      apply hne (-y) (by rw [hrdef, sub_neg_eq_add]; linarith [min_le_right |x - y| |x + y|])
      have hpi_c : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have := mul_eq_zero.mp h0 |>.resolve_left hpi_c
      push_cast; linear_combination this
  have hF_cont : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1) := by
    unfold F phiYDeriv
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (ContinuousOn.add ?_ ?_)) (by fun_prop)
    · refine ContinuousOn.div continuousOn_const (Complex.continuous_sinh.comp (by fun_prop)).continuousOn ?_
      intro p hp; exact (h_arg_ne p.1 hp.1 p.2 hp.2).1
    · refine ContinuousOn.div continuousOn_const (Complex.continuous_sinh.comp (by fun_prop)).continuousOn ?_
      intro p hp; exact (h_arg_ne p.1 hp.1 p.2 hp.2).2
  obtain ⟨M, hM⟩ := (hS_comp.prod isCompact_Icc).exists_bound_of_continuousOn hF_cont
  have hxS : (x : ℂ) ∈ S := ⟨mem_closedBall_self hr.le, by simp⟩
  have hev_S : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b ∈ S := by
    have h1' : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b ∈ closedBall (x : ℂ) r :=
      nhdsWithin_le_nhds (closedBall_mem_nhds (x : ℂ) hr)
    have h2' : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), 0 < b.im := self_mem_nhdsWithin
    have h3' : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.im ≤ 1 / 2 :=
      nhdsWithin_le_nhds (((Complex.continuous_im.tendsto (x : ℂ)).eventually
        (gt_mem_nhds (by simp : (x : ℂ).im < 1 / 2))).mono fun _ h => h.le)
    filter_upwards [h1', h2', h3'] with b hb1 hb2 hb3
    exact ⟨hb1, hb2.le, hb3⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hev_S] with b hb
    have hc : ContinuousOn (F b) (Icc 0 1) := by
      unfold F phiYDeriv
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (ContinuousOn.add ?_ ?_)) continuousOn_const
      · refine ContinuousOn.div continuousOn_const (Complex.continuous_sinh.comp (by fun_prop)).continuousOn ?_
        intro t ht; exact (h_arg_ne b hb t ht).1
      · refine ContinuousOn.div continuousOn_const (Complex.continuous_sinh.comp (by fun_prop)).continuousOn ?_
        intro t ht; exact (h_arg_ne b hb t ht).2
    rw [uIoc_of_le zero_le_one]
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hev_S] with b hb
    rw [uIoc_of_le zero_le_one]
    exact Eventually.of_forall fun t ht => hM (b, t) ⟨hb, Ioc_subset_Icc_self ht⟩
  · refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht' := Ioc_subset_Icc_self ht
    have hc : ContinuousWithinAt (fun b => F b t) S (x : ℂ) := by
      unfold F phiYDeriv
      refine ContinuousWithinAt.mul (ContinuousWithinAt.mul continuousWithinAt_const (ContinuousWithinAt.add ?_ ?_))
        (by fun_prop)
      · refine ContinuousWithinAt.div continuousWithinAt_const
          (Complex.continuous_sinh.continuousAt.comp_continuousWithinAt (by fun_prop)) ?_
        exact (h_arg_ne (x : ℂ) hxS t ht').1
      · refine ContinuousWithinAt.div continuousWithinAt_const
          (Complex.continuous_sinh.continuousAt.comp_continuousWithinAt (by fun_prop)) ?_
        exact (h_arg_ne (x : ℂ) hxS t ht').2
    exact hc.tendsto.mono_left (nhdsWithin_le_iff.mpr hev_S)

private lemma real_tanh_pos_of_pos {u : ℝ} (hu : 0 < u) : 0 < Real.tanh u := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hu) (Real.cosh_pos u)

private lemma real_tanh_neg_of_neg {u : ℝ} (hu : u < 0) : Real.tanh u < 0 := by
  rw [Real.tanh_eq_sinh_div_cosh, ← neg_neg u, Real.sinh_neg, Real.cosh_neg]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (Real.sinh_pos_iff.mpr (neg_pos.mpr hu))) (Real.cosh_pos (-u))

private lemma real_tanh_ne_zero_of_ne_zero {u : ℝ} (hu : u ≠ 0) : Real.tanh u ≠ 0 := by
  rcases lt_or_gt_of_ne hu with h | h
  · exact (real_tanh_neg_of_neg h).ne
  · exact (real_tanh_pos_of_pos h).ne'

private lemma re_tanh_pos {w : ℂ} (hre : 0 < w.re) (him0 : 0 < w.im) (him1 : w.im < π / 2) :
    0 < (Complex.tanh w).re := by
  have hc := cosh_ne_zero_of (by linarith [Real.pi_pos]) him1
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.div_re, re_sinh', im_sinh', re_cosh', im_cosh']
  have hn : 0 < Complex.normSq (Complex.cosh w) := Complex.normSq_pos.mpr hc
  have hnum : Real.sinh w.re * Real.cos w.im * (Real.cosh w.re * Real.cos w.im) +
      Real.cosh w.re * Real.sin w.im * (Real.sinh w.re * Real.sin w.im) =
      Real.sinh w.re * Real.cosh w.re := by
    have hsc := Real.sin_sq_add_cos_sq w.im
    calc Real.sinh w.re * Real.cos w.im * (Real.cosh w.re * Real.cos w.im) +
          Real.cosh w.re * Real.sin w.im * (Real.sinh w.re * Real.sin w.im)
        = Real.sinh w.re * Real.cosh w.re * (Real.sin w.im ^ 2 + Real.cos w.im ^ 2) := by ring
      _ = Real.sinh w.re * Real.cosh w.re := by rw [hsc, mul_one]
  rw [← add_div, hnum]
  have hs : 0 < Real.sinh w.re := Real.sinh_pos_iff.mpr hre
  have hch : 0 < Real.cosh w.re := Real.cosh_pos w.re
  refine div_pos (mul_pos hs hch) ?_
  rw [Complex.normSq_apply, re_cosh', im_cosh'] at hn ⊢
  exact hn

private lemma re_tanh_neg {w : ℂ} (hre : w.re < 0) (him0 : 0 < w.im) (him1 : w.im < π / 2) :
    (Complex.tanh w).re < 0 := by
  have hpos : 0 < (Complex.tanh (-w)).re := by
    have hc := cosh_ne_zero_of (w := -w) (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])
    rw [Complex.tanh_eq_sinh_div_cosh, Complex.div_re, re_sinh', im_sinh', re_cosh', im_cosh']
    have hn : 0 < Complex.normSq (Complex.cosh (-w)) := Complex.normSq_pos.mpr hc
    have hnum : Real.sinh (-w).re * Real.cos (-w).im * (Real.cosh (-w).re * Real.cos (-w).im) +
        Real.cosh (-w).re * Real.sin (-w).im * (Real.sinh (-w).re * Real.sin (-w).im) =
        Real.sinh (-w).re * Real.cosh (-w).re := by
      have hsc := Real.sin_sq_add_cos_sq (-w).im
      calc Real.sinh (-w).re * Real.cos (-w).im * (Real.cosh (-w).re * Real.cos (-w).im) +
            Real.cosh (-w).re * Real.sin (-w).im * (Real.sinh (-w).re * Real.sin (-w).im)
          = Real.sinh (-w).re * Real.cosh (-w).re * (Real.sin (-w).im ^ 2 + Real.cos (-w).im ^ 2) := by ring
        _ = Real.sinh (-w).re * Real.cosh (-w).re := by rw [hsc, mul_one]
    rw [← add_div, hnum]
    have hs : 0 < Real.sinh (-w).re := Real.sinh_pos_iff.mpr (by simp; linarith)
    have hch : 0 < Real.cosh (-w).re := Real.cosh_pos _
    refine div_pos (mul_pos hs hch) ?_
    rw [Complex.normSq_apply, re_cosh', im_cosh'] at hn ⊢
    exact hn
  rw [Complex.tanh_neg, Complex.neg_re] at hpos
  linarith

private lemma Tcx_ofReal (x y : ℝ) :
    Tcx y (x : ℂ) = ((Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
  unfold Tcx
  rw [show (π : ℂ) * ((x : ℂ) - y) / 2 = ((π * (x - y) / 2 : ℝ) : ℂ) by push_cast; ring,
    show (π : ℂ) * ((x : ℂ) + y) / 2 = ((π * (x + y) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_tanh, ← Complex.ofReal_tanh, ← Complex.ofReal_mul]

private lemma tendsto_Tcx_real (x y : ℝ) :
    Tendsto (Tcx y) (𝓝[upperHalf] (x : ℂ)) (𝓝 (Tcx y (x : ℂ))) := by
  unfold Tcx
  have hc1 : Complex.cosh ((π : ℂ) * ((x : ℂ) - y) / 2) ≠ 0 := by
    rw [show (π : ℂ) * ((x : ℂ) - y) / 2 = ((π * (x - y) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact cosh_ne_zero_of (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])
  have hc2 : Complex.cosh ((π : ℂ) * ((x : ℂ) + y) / 2) ≠ 0 := by
    rw [show (π : ℂ) * ((x : ℂ) + y) / 2 = ((π * (x + y) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact cosh_ne_zero_of (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])
  have hc : ContinuousAt (fun b : ℂ =>
      Complex.tanh ((π : ℂ) * (b - y) / 2) * Complex.tanh ((π : ℂ) * (b + y) / 2)) (x : ℂ) := by
    simp only [Complex.tanh_eq_sinh_div_cosh]
    refine ContinuousAt.mul ?_ ?_
    · exact (Complex.continuous_sinh.continuousAt.comp (by fun_prop)).div
        (Complex.continuous_cosh.continuousAt.comp (by fun_prop)) hc1
    · exact (Complex.continuous_sinh.continuousAt.comp (by fun_prop)).div
        (Complex.continuous_cosh.continuousAt.comp (by fun_prop)) hc2
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

private lemma hev_imStrip_of_upperHalf (x : ℝ) : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b ∈ imStrip := by
  have h1 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), 0 < b.im := self_mem_nhdsWithin
  have h2 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.im < 1 :=
    nhdsWithin_le_nhds ((Complex.continuous_im.tendsto (x : ℂ)).eventually (gt_mem_nhds (by simp : (x : ℂ).im < 1)))
  filter_upwards [h1, h2] with b hb1 hb2
  exact ⟨hb1, hb2⟩

lemma re_phiY_real {x y : ℝ} (h1 : x ≠ y) (h2 : x ≠ -y) :
    (phiY y (x : ℂ)).re = Real.log |Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2)| := by
  have hlim1 : Tendsto (fun b => (phiY y b).re) (𝓝[upperHalf] (x : ℂ)) (𝓝 (phiY y (x : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp (tendsto_phiY_real h1 h2)
  have hne : Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) ≠ 0 := by
    have hpi := Real.pi_pos
    apply mul_ne_zero
    · exact real_tanh_ne_zero_of_ne_zero (by intro h; apply h1; nlinarith)
    · exact real_tanh_ne_zero_of_ne_zero (by intro h; apply h2; nlinarith)
  have hlim2 : Tendsto (fun b => (phiY y b).re) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (Real.log |Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2)|)) := by
    have hT : Tendsto (fun b => Real.log ‖-(Tcx y b)‖) (𝓝[upperHalf] (x : ℂ))
        (𝓝 (Real.log ‖-(Tcx y (x : ℂ))‖)) := by
      refine (Real.continuousAt_log ?_).tendsto.comp ((tendsto_Tcx_real x y).neg.norm)
      rw [norm_neg, Tcx_ofReal, Complex.norm_real, Real.norm_eq_abs]
      exact abs_ne_zero.mpr hne
    rw [norm_neg, Tcx_ofReal, Complex.norm_real, Real.norm_eq_abs] at hT
    refine hT.congr' ?_
    filter_upwards [hev_imStrip_of_upperHalf x] with b hb
    rw [phiY_eq hb, Complex.log_re]
  haveI : NeBot (𝓝[upperHalf] (x : ℂ)) := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
      by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩
  exact tendsto_nhds_unique hlim1 hlim2

lemma im_phiY_real_of_abs_lt {x y : ℝ} (h1 : -y < x) (h2 : x < y) :
    (phiY y (x : ℂ)).im = 0 := by
  have hne1 : x ≠ y := h2.ne
  have hne2 : x ≠ -y := h1.ne'
  have hlim1 : Tendsto (fun b => (phiY y b).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 (phiY y (x : ℂ)).im) :=
    (Complex.continuous_im.tendsto _).comp (tendsto_phiY_real hne1 hne2)
  have hpos : 0 < -(Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2)) := by
    have hpi := Real.pi_pos
    have ht1 : Real.tanh (π * (x - y) / 2) < 0 := real_tanh_neg_of_neg (by nlinarith)
    have ht2 : 0 < Real.tanh (π * (x + y) / 2) := real_tanh_pos_of_pos (by nlinarith)
    nlinarith
  have hlim2 : Tendsto (fun b => (phiY y b).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 0) := by
    have hslit : -(Tcx y (x : ℂ)) ∈ Complex.slitPlane := by
      rw [Tcx_ofReal, ← Complex.ofReal_neg]
      exact Complex.ofReal_mem_slitPlane.mpr hpos
    have harg : Tendsto (fun b => Complex.arg (-(Tcx y b))) (𝓝[upperHalf] (x : ℂ))
        (𝓝 (Complex.arg (-(Tcx y (x : ℂ))))) :=
      (Complex.continuousAt_arg hslit).tendsto.comp (tendsto_Tcx_real x y).neg
    rw [Tcx_ofReal, ← Complex.ofReal_neg, Complex.arg_ofReal_of_nonneg hpos.le] at harg
    refine harg.congr' ?_
    filter_upwards [hev_imStrip_of_upperHalf x] with b hb
    rw [phiY_eq hb, Complex.log_im]
  haveI : NeBot (𝓝[upperHalf] (x : ℂ)) := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
      by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩
  exact tendsto_nhds_unique hlim1 hlim2

lemma im_phiY_real_of_gt {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    (phiY y (x : ℂ)).im = -π := by
  have hne1 : x ≠ y := hxy.ne'
  have hne2 : x ≠ -y := by linarith
  have hlim1 : Tendsto (fun b => (phiY y b).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 (phiY y (x : ℂ)).im) :=
    (Complex.continuous_im.tendsto _).comp (tendsto_phiY_real hne1 hne2)
  have hpos : 0 < Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) := by
    have hpi := Real.pi_pos
    exact mul_pos (real_tanh_pos_of_pos (by nlinarith)) (real_tanh_pos_of_pos (by nlinarith))
  have hev_re : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), y < b.re :=
    nhdsWithin_le_nhds ((Complex.continuous_re.tendsto (x : ℂ)).eventually (lt_mem_nhds (by simpa)))
  have hlim2 : Tendsto (fun b => (phiY y b).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 (-π)) := by
    have hslit : Tcx y (x : ℂ) ∈ Complex.slitPlane := by
      rw [Tcx_ofReal]
      exact Complex.ofReal_mem_slitPlane.mpr hpos
    have harg : Tendsto (fun b => Complex.arg (Tcx y b) - π) (𝓝[upperHalf] (x : ℂ))
        (𝓝 (Complex.arg (Tcx y (x : ℂ)) - π)) :=
      ((Complex.continuousAt_arg hslit).tendsto.comp (tendsto_Tcx_real x y)).sub_const π
    rw [Tcx_ofReal, Complex.arg_ofReal_of_nonneg hpos.le, zero_sub] at harg
    refine harg.congr' ?_
    filter_upwards [hev_imStrip_of_upperHalf x, hev_re] with b hb hbre
    rw [phiY_eq hb, Complex.log_im]
    have hpi := Real.pi_pos
    have him1 : 0 < (Complex.tanh ((π : ℂ) * (b - y) / 2)).im :=
      im_tanh_pos (by rw [im_w₁]; have := hb.1; positivity) (by rw [im_w₁]; nlinarith [hb.2])
    have him2 : 0 < (Complex.tanh ((π : ℂ) * (b + y) / 2)).im :=
      im_tanh_pos (by rw [im_w₂]; have := hb.1; positivity) (by rw [im_w₂]; nlinarith [hb.2])
    have hre1 : 0 < (Complex.tanh ((π : ℂ) * (b - y) / 2)).re :=
      re_tanh_pos (by simp; nlinarith) (by rw [im_w₁]; have := hb.1; positivity) (by rw [im_w₁]; nlinarith [hb.2])
    have hre2 : 0 < (Complex.tanh ((π : ℂ) * (b + y) / 2)).re :=
      re_tanh_pos (by simp; nlinarith) (by rw [im_w₂]; have := hb.1; positivity) (by rw [im_w₂]; nlinarith [hb.2])
    have him_neg : (-(Tcx y b)).im < 0 := by
      unfold Tcx
      rw [Complex.neg_im, Complex.mul_im]
      nlinarith
    have := Complex.arg_neg_eq_arg_add_pi_of_im_neg him_neg
    rw [neg_neg] at this
    linarith
  haveI : NeBot (𝓝[upperHalf] (x : ℂ)) := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
      by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩
  exact tendsto_nhds_unique hlim1 hlim2

lemma im_phiY_real_of_lt_neg {x y : ℝ} (hy : 0 < y) (hxy : x < -y) :
    (phiY y (x : ℂ)).im = π := by
  have hne1 : x ≠ y := by linarith
  have hne2 : x ≠ -y := hxy.ne
  have hlim1 : Tendsto (fun b => (phiY y b).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 (phiY y (x : ℂ)).im) :=
    (Complex.continuous_im.tendsto _).comp (tendsto_phiY_real hne1 hne2)
  have hpos : 0 < Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) := by
    have hpi := Real.pi_pos
    have ht1 : Real.tanh (π * (x - y) / 2) < 0 := real_tanh_neg_of_neg (by nlinarith)
    have ht2 : Real.tanh (π * (x + y) / 2) < 0 := real_tanh_neg_of_neg (by nlinarith)
    nlinarith
  have hev_re : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.re < -y :=
    nhdsWithin_le_nhds ((Complex.continuous_re.tendsto (x : ℂ)).eventually (gt_mem_nhds (by simpa)))
  have hlim2 : Tendsto (fun b => (phiY y b).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 π) := by
    have hslit : Tcx y (x : ℂ) ∈ Complex.slitPlane := by
      rw [Tcx_ofReal]
      exact Complex.ofReal_mem_slitPlane.mpr hpos
    have harg : Tendsto (fun b => Complex.arg (Tcx y b) + π) (𝓝[upperHalf] (x : ℂ))
        (𝓝 (Complex.arg (Tcx y (x : ℂ)) + π)) :=
      ((Complex.continuousAt_arg hslit).tendsto.comp (tendsto_Tcx_real x y)).add_const π
    rw [Tcx_ofReal, Complex.arg_ofReal_of_nonneg hpos.le, zero_add] at harg
    refine harg.congr' ?_
    filter_upwards [hev_imStrip_of_upperHalf x, hev_re] with b hb hbre
    rw [phiY_eq hb, Complex.log_im]
    have hpi := Real.pi_pos
    have him1 : 0 < (Complex.tanh ((π : ℂ) * (b - y) / 2)).im :=
      im_tanh_pos (by rw [im_w₁]; have := hb.1; positivity) (by rw [im_w₁]; nlinarith [hb.2])
    have him2 : 0 < (Complex.tanh ((π : ℂ) * (b + y) / 2)).im :=
      im_tanh_pos (by rw [im_w₂]; have := hb.1; positivity) (by rw [im_w₂]; nlinarith [hb.2])
    have hre1 : (Complex.tanh ((π : ℂ) * (b - y) / 2)).re < 0 :=
      re_tanh_neg (by simp; nlinarith) (by rw [im_w₁]; have := hb.1; positivity) (by rw [im_w₁]; nlinarith [hb.2])
    have hre2 : (Complex.tanh ((π : ℂ) * (b + y) / 2)).re < 0 :=
      re_tanh_neg (by simp; nlinarith) (by rw [im_w₂]; have := hb.1; positivity) (by rw [im_w₂]; nlinarith [hb.2])
    have him_pos : 0 < (-(Tcx y b)).im := by
      unfold Tcx
      rw [Complex.neg_im, Complex.mul_im]
      nlinarith
    have := Complex.arg_neg_eq_arg_sub_pi_of_im_pos him_pos
    rw [neg_neg] at this
    linarith
  haveI : NeBot (𝓝[upperHalf] (x : ℂ)) := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
      by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩
  exact tendsto_nhds_unique hlim1 hlim2


/-! ### 2. Logarithmic majorant and dominated convergence for `DeltaPhi` -/

private lemma norm_tanh_ge_tanh_abs {w : ℂ} (h0 : 0 < w.im) (h1 : w.im ≤ π / 4) :
    Real.tanh |w.re| ≤ ‖Complex.tanh w‖ ∧ ‖Complex.tanh w‖ ≤ 1 := by
  have hpi := Real.pi_pos
  have h2 := norm_tanh_sq w
  have hsin_le_cos : Real.sin w.im ≤ Real.cos w.im := by
    have hc1 : Real.sin w.im ≤ Real.sin (π / 4) :=
      Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h1
    have hc2 : Real.sin (π / 4) = Real.cos (π / 4) := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hc3 : Real.cos (π / 4) ≤ Real.cos w.im :=
      Real.strictAntiOn_cos.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h1
    linarith
  have hsin0 : 0 ≤ Real.sin w.im := (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)).le
  have hsq1 : Real.sin w.im ^ 2 ≤ Real.cos w.im ^ 2 := pow_le_pow_left₀ hsin0 hsin_le_cos 2
  have hc1 : Real.cos w.im ^ 2 ≤ 1 := Real.cos_sq_le_one _
  have hd : 0 < Real.sinh w.re ^ 2 + Real.cos w.im ^ 2 := by
    have : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    positivity
  have hn := norm_nonneg (Complex.tanh w)
  constructor
  · have ht : Real.tanh |w.re| ^ 2 = Real.sinh w.re ^ 2 / (Real.sinh w.re ^ 2 + 1) := by
      rw [Real.tanh_eq_sinh_div_cosh, div_pow, Real.cosh_sq', add_comm 1 _]
      rcases le_total 0 w.re with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, Real.sinh_neg, neg_sq]
    have hle : Real.tanh |w.re| ^ 2 ≤ ‖Complex.tanh w‖ ^ 2 := by
      rw [ht, h2, div_le_div_iff₀ (by positivity) hd]
      have hs0 : 0 ≤ Real.sinh w.re ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (Real.sin w.im)]
    exact le_of_pow_le_pow_left₀ (by norm_num) hn hle
  · have hle : ‖Complex.tanh w‖ ^ 2 ≤ 1 ^ 2 := by
      rw [h2, one_pow, div_le_one hd]; linarith [hsq1]
    exact le_of_pow_le_pow_left₀ (by norm_num) zero_le_one hle

private lemma neg_log_tanh_le {u : ℝ} (hu : 0 < u) :
    -Real.log (Real.tanh u) ≤ Real.log 5 + 4 * u ^ (-(1 : ℝ) / 4) := by
  have ht0 : 0 < Real.tanh u := real_tanh_pos_of_pos hu
  have hexp_pos : 0 < Real.exp (2 * u) + 1 := by positivity
  have ht_eq : Real.tanh u = (Real.exp (2 * u) - 1) / (Real.exp (2 * u) + 1) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have hexp2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    have h2' : Real.exp (-u) * Real.exp u = 1 := by rw [mul_comm, h2]
    rw [hexp2]
    have hd1 : (Real.exp u + Real.exp (-u)) / 2 ≠ 0 := by positivity
    have hd2 : Real.exp u * Real.exp u + 1 ≠ 0 := by positivity
    rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [div_eq_div_iff (by positivity) hd2]
    calc (Real.exp u - Real.exp (-u)) * (Real.exp u * Real.exp u + 1)
        = Real.exp u * (Real.exp u * Real.exp u) + Real.exp u - Real.exp (-u) * Real.exp u * Real.exp u - Real.exp (-u) := by ring
      _ = Real.exp u * (Real.exp u * Real.exp u) + Real.exp u - 1 * Real.exp u - Real.exp (-u) := by rw [h2']
      _ = Real.exp u * (Real.exp u * Real.exp u) - Real.exp u + 1 * Real.exp u - Real.exp (-u) := by ring
      _ = Real.exp u * (Real.exp u * Real.exp u) - Real.exp u + Real.exp (-u) * Real.exp u * Real.exp u - Real.exp (-u) := by rw [h2']
      _ = (Real.exp u * Real.exp u - 1) * (Real.exp u + Real.exp (-u)) := by ring
  rcases le_total u 1 with hu1 | hu1
  · have hnum : 2 * u ≤ Real.exp (2 * u) - 1 := by linarith [Real.add_one_le_exp (2 * u)]
    have hden : Real.exp (2 * u) + 1 ≤ 10 := by
      have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have he2 : Real.exp (2 * u) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
      have he2' : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos 1]
    have hlo : u / 5 ≤ Real.tanh u := by
      rw [ht_eq, div_le_div_iff₀ (by norm_num) hexp_pos]
      nlinarith
    have hlog1 : -Real.log (Real.tanh u) ≤ Real.log 5 - Real.log u := by
      have := Real.log_le_log (by positivity) hlo
      rw [Real.log_div hu.ne' (by norm_num)] at this
      linarith
    have hlog2 : -Real.log u ≤ 4 * u ^ (-(1 : ℝ) / 4) := by
      have hp : 0 < u ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hu _
      have hl := Real.log_le_sub_one_of_pos hp
      have heq : Real.log (u ^ (-(1 : ℝ) / 4)) = -(1 / 4) * Real.log u := by
        rw [Real.log_rpow hu]; ring
      linarith
    linarith
  · have he1 : 2 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have he2 : 4 < Real.exp (2 * u) := by
      have : Real.exp 2 ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
      have he2' : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith
    have hlo : 1 / 5 ≤ Real.tanh u := by
      rw [ht_eq, div_le_div_iff₀ (by norm_num) hexp_pos]
      linarith
    have hlog1 : -Real.log (Real.tanh u) ≤ Real.log 5 := by
      have := Real.log_le_log (by norm_num) hlo
      rw [one_div, Real.log_inv] at this
      linarith
    have hp : 0 ≤ 4 * u ^ (-(1 : ℝ) / 4) := by positivity
    linarith

private lemma norm_phiY_le_upperHalf {y : ℝ} {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im ≤ 1 / 2)
    (h1 : b.re ≠ y) (h2 : b.re ≠ -y) :
    ‖phiY y b‖ ≤ π + 2 * Real.log 5 +
      4 * (π * |b.re - y| / 2) ^ (-(1 : ℝ) / 4) + 4 * (π * |b.re + y| / 2) ^ (-(1 : ℝ) / 4) := by
  have hbs : b ∈ imStrip := ⟨hb0, by linarith⟩
  rw [phiY_eq hbs]
  have hpi := Real.pi_pos
  have h_re_1 : (π * (b - y) / 2).re = π * (b.re - y) / 2 := by simp
  have h_re_2 : (π * (b + y) / 2).re = π * (b.re + y) / 2 := by simp
  have h_im_1 : 0 < ((π : ℂ) * (b - y) / 2).im ∧ ((π : ℂ) * (b - y) / 2).im ≤ π / 4 := by
    rw [im_w₁]; exact ⟨by positivity, by nlinarith⟩
  have h_im_2 : 0 < ((π : ℂ) * (b + y) / 2).im ∧ ((π : ℂ) * (b + y) / 2).im ≤ π / 4 := by
    rw [im_w₂]; exact ⟨by positivity, by nlinarith⟩
  obtain ⟨l1, u1⟩ := norm_tanh_ge_tanh_abs h_im_1.1 h_im_1.2
  obtain ⟨l2, u2⟩ := norm_tanh_ge_tanh_abs h_im_2.1 h_im_2.2
  have ha1 : 0 < |(π * (b - y) / 2).re| := by
    rw [h_re_1, abs_pos]
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr h1)) (by norm_num)
  have ha2 : 0 < |(π * (b + y) / 2).re| := by
    rw [h_re_2, abs_pos]
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (by intro h; apply h2; linarith)) (by norm_num)
  have ht1 : 0 < Real.tanh |(π * (b - y) / 2).re| := real_tanh_pos_of_pos ha1
  have ht2 : 0 < Real.tanh |(π * (b + y) / 2).re| := real_tanh_pos_of_pos ha2
  have hT_le : ‖-(Tcx y b)‖ ≤ 1 := by
    rw [norm_neg]; unfold Tcx; rw [norm_mul]; exact mul_le_one₀ u1 (norm_nonneg _) u2
  have hT_ge : Real.tanh |(π * (b - y) / 2).re| * Real.tanh |(π * (b + y) / 2).re| ≤ ‖-(Tcx y b)‖ := by
    rw [norm_neg]; unfold Tcx; rw [norm_mul]
    exact mul_le_mul l1 l2 ht2.le (norm_nonneg _)
  have hT_pos : 0 < ‖-(Tcx y b)‖ := lt_of_lt_of_le (mul_pos ht1 ht2) hT_ge
  have hlog : |Real.log ‖-(Tcx y b)‖| ≤
      -Real.log (Real.tanh |(π * (b - y) / 2).re|) + (-Real.log (Real.tanh |(π * (b + y) / 2).re|)) := by
    rw [abs_of_nonpos (Real.log_nonpos hT_pos.le hT_le)]
    have := Real.log_le_log (mul_pos ht1 ht2) hT_ge
    rw [Real.log_mul ht1.ne' ht2.ne'] at this
    linarith
  have h1' := neg_log_tanh_le ha1
  have h2' := neg_log_tanh_le ha2
  have e1 : |(π * (b - y) / 2).re| = π * |b.re - y| / 2 := by
    rw [h_re_1, abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have e2 : |(π * (b + y) / 2).re| = π * |b.re + y| / 2 := by
    rw [h_re_2, abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [e1] at h1' hlog
  rw [e2] at h2' hlog
  have harg := Complex.abs_arg_le_pi (-(Tcx y b))
  calc ‖Complex.log (-(Tcx y b))‖
      = ‖((Real.log ‖-(Tcx y b)‖ : ℝ) : ℂ) + ((Complex.arg (-(Tcx y b)) : ℝ) : ℂ) * Complex.I‖ := rfl
    _ ≤ ‖((Real.log ‖-(Tcx y b)‖ : ℝ) : ℂ)‖ + ‖((Complex.arg (-(Tcx y b)) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |Real.log ‖-(Tcx y b)‖| + |Complex.arg (-(Tcx y b))| := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ _ := by linarith [hlog, harg, h1', h2']

private lemma norm_phiY_real_le {x y : ℝ} (h1 : x ≠ y) (h2 : x ≠ -y) :
    ‖phiY y (x : ℂ)‖ ≤ π + 2 * Real.log 5 +
      4 * (π * |x - y| / 2) ^ (-(1 : ℝ) / 4) + 4 * (π * |x + y| / 2) ^ (-(1 : ℝ) / 4) := by
  have hlim : Tendsto (fun t : ℝ => ‖phiY y ((x : ℂ) + (t : ℂ) * Complex.I)‖) (𝓝[>] (0 : ℝ))
      (𝓝 ‖phiY y (x : ℂ)‖) := by
    refine (tendsto_phiY_real h1 h2).norm.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp [upperHalf, mem_Ioi.mp ht]
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
  have hb := norm_phiY_le_upperHalf (y := y) (b := (x : ℂ) + (t : ℂ) * Complex.I)
    (by simp; exact ht.1) (by simp; linarith [ht.2]) (by simpa using h1) (by simpa using h2)
  simpa using hb

private lemma young_three_halves {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A * B ≤ A ^ ((3 : ℝ) / 2) + B ^ (3 : ℝ) := by
  rcases eq_or_lt_of_le hA with rfl | hA'
  · simp; positivity
  rcases eq_or_lt_of_le hB with rfl | hB'
  · simp; positivity
  rcases le_total (B ^ (2 : ℝ)) A with h | h
  · have hB1 : B ≤ A ^ ((1 : ℝ) / 2) := by
      have := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [← Real.rpow_mul hB, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at this
    have hAB : A * B ≤ A * A ^ ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hB1 hA
    have hpow : A * A ^ ((1 : ℝ) / 2) = A ^ ((3 : ℝ) / 2) := by
      nth_rw 1 [← Real.rpow_one A]
      rw [← Real.rpow_add hA']
      norm_num
    linarith [Real.rpow_nonneg hB (3 : ℝ)]
  · have hAB : A * B ≤ B ^ (2 : ℝ) * B := mul_le_mul_of_nonneg_right h hB
    have hpow : B ^ (2 : ℝ) * B = B ^ (3 : ℝ) := by
      conv_rhs => rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hB', Real.rpow_one]
    rw [hpow] at hAB
    linarith [Real.rpow_nonneg hA ((3 : ℝ) / 2)]

private lemma integrableOn_rpow_neg_three_quarter (c a b : ℝ) (hab : a ≤ b) :
    IntegrableOn (fun y : ℝ => |y - c| ^ (-(3 : ℝ) / 4)) (Ioc a b) := by
  have hsub : ∀ u v : ℝ, u ≤ v → IntegrableOn (fun y : ℝ => |y - c| ^ (-(3 : ℝ) / 4)) (Ioc u v) := by
    intro u v huv
    rcases le_total c u with hcu | hcu
    · have h0 := (intervalIntegral.intervalIntegrable_rpow' (a := u - c) (b := v - c) (r := -(3 : ℝ) / 4)
        (by norm_num)).comp_sub_right c
      simp only [sub_add_cancel] at h0
      have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mp h0
      refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioc
      simp [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - c)]
    · rcases le_total v c with hvc | hvc
      · have h0 := ((intervalIntegral.intervalIntegrable_rpow' (a := c - v) (b := c - u) (r := -(3 : ℝ) / 4)
          (by norm_num)).comp_sub_left c).symm
        simp only [sub_sub_cancel] at h0
        have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mp h0
        refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioc
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hy.2] : 0 ≤ c - y)]
      · have hleft : IntegrableOn (fun y : ℝ => |y - c| ^ (-(3 : ℝ) / 4)) (Ioc u c) := by
          have h0 := ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c - u) (r := -(3 : ℝ) / 4)
            (by norm_num)).comp_sub_left c).symm
          simp only [sub_zero, sub_sub_cancel] at h0
          have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hcu).mp h0
          refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioc
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hy.2] : 0 ≤ c - y)]
        have hright : IntegrableOn (fun y : ℝ => |y - c| ^ (-(3 : ℝ) / 4)) (Ioc c v) := by
          have h0 := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := v - c) (r := -(3 : ℝ) / 4)
            (by norm_num)).comp_sub_right c
          simp only [zero_add, sub_add_cancel] at h0
          have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hvc).mp h0
          refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioc
          rw [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - c)]
        rw [← Ioc_union_Ioc_eq_Ioc hcu hvc]
        exact hleft.union hright
  exact hsub a b hab

private lemma dphi_deriv_ae_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, xiStar < y →
      |deriv (dphi δ) y| * 1 ≤ C * (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y)) := by
  obtain ⟨C, hC, hb⟩ := outerS4a
  exact ⟨C, hC, fun y hy => by simpa using (hb δ hδ0 hδ1 y hy).1⟩

/-- For `δ ∈ (0, 1/4)` and `x : ℝ`, `y ↦ δφ_δ'(y) φ_y(x)` is Lebesgue integrable on `(ξ_*, ∞)`. -/
lemma integrableOn_dphi_phiY_real {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (x : ℝ) :
    IntegrableOn (fun y => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)) (Ioi xiStar) := by
  obtain ⟨C0, hC0, hb⟩ := outerS4a
  have hg := integrableOn_dphi_deriv hδ0 hδ1
  have hmeas_g := continuousOn_dphi_deriv δ
  have hmeas_phi : AEStronglyMeasurable (fun y => phiY y (x : ℂ)) (volume.restrict (Ioi xiStar)) := by
    have hlim : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)),
        Tendsto (fun n : ℕ => phiY y ((x : ℂ) + ((1 / ((n : ℝ) + 3) : ℝ) : ℂ) * Complex.I)) atTop
          (𝓝 (phiY y (x : ℂ))) := by
      have hne1 : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), y ≠ x := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton x)
      have hne2 : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), y ≠ -x := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-x))
      filter_upwards [hne1, hne2] with y hy1 hy2
      refine (tendsto_phiY_real hy1.symm (by intro h; apply hy2; linarith)).comp ?_
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (x : ℂ) + ((1 / ((n : ℝ) + 3) : ℝ) : ℂ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
          have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3)) atTop (𝓝 0) := by
            have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
            refine this.congr (fun n => ?_)
            simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]; ring_nf
          simpa using tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1).mul
            (tendsto_const_nhds (x := Complex.I)))
        exact h0
      · filter_upwards with n
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 3) := by positivity
        simp only [upperHalf, Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
        exact hpos
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => ?_) hlim
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 3) := by positivity
    have hlt : (1 : ℝ) / ((n : ℝ) + 3) < 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [div_lt_one (by linarith)]; linarith
    have hb_in : ((x : ℂ) + ((1 / ((n : ℝ) + 3) : ℝ) : ℂ) * Complex.I) ∈ imStrip := by
      simp only [imStrip, Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
      exact ⟨hpos, hlt⟩
    exact (continuous_phiY_y hb_in).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun y => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ))
      (volume.restrict (Ioi xiStar)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (hmeas_g.aestronglyMeasurable measurableSet_Ioi)).mul hmeas_phi
  -- Split Ioi xiStar into Ioc xiStar (max (xiStar + 1) (|x| + 1)) and Ioi (max (xiStar + 1) (|x| + 1))
  set R : ℝ := max (xiStar + 1) (|x| + 2) with hRdef
  have hxiR : xiStar ≤ R := by linarith [le_max_left (xiStar + 1) (|x| + 2)]
  have h1R : xiStar + 1 ≤ R := le_max_left _ _
  have hxR : |x| + 2 ≤ R := le_max_right _ _
  have hpi := Real.pi_pos
  rw [← Ioc_union_Ioi_eq_Ioi hxiR]
  refine IntegrableOn.union ?_ ?_
  · -- On Ioc xiStar R, bound by C_R * (|y - xiStar|^{-3/4} + |y - x|^{-3/4} + |y + x|^{-3/4}) + C_R' * |g y|
    set C1 : ℝ := C0 * max 1 (R - xiStar) ^ ((1 : ℝ) / 2) with hC1def
    have hC1 : 0 ≤ C1 := by positivity
    set K : ℝ := C1 * (4 * (π / 2) ^ (-(1 : ℝ) / 4)) with hKdef
    have hK : 0 ≤ K := by positivity
    have hI0 : IntegrableOn (fun y => (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖) (Ioc xiStar R) :=
      (hg.mono_set Ioc_subset_Ioi_self).norm.const_mul _
    have hI1 : IntegrableOn (fun y => (2 * K) * |y - xiStar| ^ (-(3 : ℝ) / 4)) (Ioc xiStar R) :=
      (integrableOn_rpow_neg_three_quarter xiStar xiStar R hxiR).const_mul _
    have hI2 : IntegrableOn (fun y => K * |y - x| ^ (-(3 : ℝ) / 4)) (Ioc xiStar R) :=
      (integrableOn_rpow_neg_three_quarter x xiStar R hxiR).const_mul _
    have hI3 : IntegrableOn (fun y => K * |y - (-x)| ^ (-(3 : ℝ) / 4)) (Ioc xiStar R) :=
      (integrableOn_rpow_neg_three_quarter (-x) xiStar R hxiR).const_mul _
    refine Integrable.mono' (((hI0.add hI1).add hI2).add hI3) (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    have hne1 : ∀ᵐ y ∂(volume.restrict (Ioc xiStar R)), y ≠ x := by
      rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton x)
    have hne2 : ∀ᵐ y ∂(volume.restrict (Ioc xiStar R)), y ≠ -x := by
      rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-x))
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1, hne2] with y hy hnx1 hnx2
    have hyx : xiStar < y := hy.1
    have hyR : y ≤ R := hy.2
    have hphi := norm_phiY_real_le hnx1.symm (by intro h; apply hnx2; linarith)
    have h_abs1 : |x - y| = |y - x| := abs_sub_comm x y
    have h_abs2 : |x + y| = |y - (-x)| := by rw [sub_neg_eq_add, add_comm]
    rw [h_abs1, h_abs2] at hphi
    have hg_bd : |deriv (dphi δ) y| ≤ C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) := by
      have hbd := (hb δ hδ0 hδ1 y hyx).1
      have he : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by have := xiStar_pos; have := Real.pi_pos; nlinarith)
      have hm_le : (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) ≤
          max 1 (R - xiStar) ^ ((1 : ℝ) / 2) * (y - xiStar) ^ (-(1 : ℝ) / 2) := by
        rcases le_total (y - xiStar) 1 with hm | hm
        · rw [min_eq_left hm]
          have hmax : (1 : ℝ) ≤ max 1 (R - xiStar) ^ ((1 : ℝ) / 2) :=
            Real.one_le_rpow (le_max_left (1 : ℝ) (R - xiStar)) (by norm_num)
          exact le_mul_of_one_le_left (Real.rpow_nonneg (by linarith : 0 ≤ y - xiStar) _) hmax
        · rw [min_eq_right hm, Real.one_rpow]
          have h1 : 0 < y - xiStar := by linarith
          have h2 : y - xiStar ≤ max 1 (R - xiStar) := le_trans (by linarith) (le_max_right _ _)
          have h3 : (y - xiStar) ^ ((1 : ℝ) / 2) ≤ max 1 (R - xiStar) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow h1.le h2 (by norm_num)
          have h4 : (y - xiStar) ^ ((1 : ℝ) / 2) * (y - xiStar) ^ (-(1 : ℝ) / 2) = 1 := by
            rw [← Real.rpow_add h1]; norm_num
          nlinarith [Real.rpow_pos_of_pos h1 (-(1 : ℝ) / 2)]
      calc |deriv (dphi δ) y|
          ≤ C0 * (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y)) := hbd
        _ ≤ C0 * (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * 1 :=
            mul_le_mul_of_nonneg_left he (mul_nonneg hC0.le (Real.rpow_nonneg (lt_min (by linarith) one_pos).le _))
        _ ≤ C0 * (max 1 (R - xiStar) ^ ((1 : ℝ) / 2) * (y - xiStar) ^ (-(1 : ℝ) / 2)) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hm_le hC0.le
        _ = C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) := by rw [hC1def]; ring
    have hyx_pos : 0 < y - xiStar := by linarith
    have hyx1_pos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hnx1)
    have hyx2_pos : 0 < |y - (-x)| := abs_pos.mpr (sub_ne_zero.mpr hnx2)
    have hY1 := young_three_halves (Real.rpow_nonneg hyx_pos.le (-(1 : ℝ) / 2))
      (Real.rpow_nonneg hyx1_pos.le (-(1 : ℝ) / 4))
    have hY2 := young_three_halves (Real.rpow_nonneg hyx_pos.le (-(1 : ℝ) / 2))
      (Real.rpow_nonneg hyx2_pos.le (-(1 : ℝ) / 4))
    have hp1 : ((y - xiStar) ^ (-(1 : ℝ) / 2)) ^ ((3 : ℝ) / 2) = |y - xiStar| ^ (-(3 : ℝ) / 4) := by
      rw [← Real.rpow_mul hyx_pos.le, abs_of_pos hyx_pos]; norm_num
    have hp2 : (|y - x| ^ (-(1 : ℝ) / 4)) ^ (3 : ℝ) = |y - x| ^ (-(3 : ℝ) / 4) := by
      rw [← Real.rpow_mul hyx1_pos.le]; norm_num
    have hp3 : (|y - (-x)| ^ (-(1 : ℝ) / 4)) ^ (3 : ℝ) = |y - (-x)| ^ (-(3 : ℝ) / 4) := by
      rw [← Real.rpow_mul hyx2_pos.le]; norm_num
    rw [hp1, hp2] at hY1
    rw [hp1, hp3] at hY2
    have hrpow1 : (π * |y - x| / 2) ^ (-(1 : ℝ) / 4) = (π / 2) ^ (-(1 : ℝ) / 4) * |y - x| ^ (-(1 : ℝ) / 4) := by
      rw [show π * |y - x| / 2 = (π / 2) * |y - x| by ring, Real.mul_rpow (by positivity) (abs_nonneg _)]
    have hrpow2 : (π * |y - (-x)| / 2) ^ (-(1 : ℝ) / 4) = (π / 2) ^ (-(1 : ℝ) / 4) * |y - (-x)| ^ (-(1 : ℝ) / 4) := by
      rw [show π * |y - (-x)| / 2 = (π / 2) * |y - (-x)| by ring, Real.mul_rpow (by positivity) (abs_nonneg _)]
    rw [hrpow1, hrpow2] at hphi
    rw [norm_mul, Complex.norm_real]
    have hprod1 : |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - x| ^ (-(1 : ℝ) / 4))) ≤
        K * (|y - xiStar| ^ (-(3 : ℝ) / 4) + |y - x| ^ (-(3 : ℝ) / 4)) := by
      calc |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - x| ^ (-(1 : ℝ) / 4)))
          ≤ C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - x| ^ (-(1 : ℝ) / 4))) := by
            gcongr
        _ = K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - x| ^ (-(1 : ℝ) / 4)) := by rw [hKdef]; ring
        _ ≤ K * (|y - xiStar| ^ (-(3 : ℝ) / 4) + |y - x| ^ (-(3 : ℝ) / 4)) := by gcongr
    have hprod2 : |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-x)| ^ (-(1 : ℝ) / 4))) ≤
        K * (|y - xiStar| ^ (-(3 : ℝ) / 4) + |y - (-x)| ^ (-(3 : ℝ) / 4)) := by
      calc |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-x)| ^ (-(1 : ℝ) / 4)))
          ≤ C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-x)| ^ (-(1 : ℝ) / 4))) := by
            gcongr
        _ = K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - (-x)| ^ (-(1 : ℝ) / 4)) := by rw [hKdef]; ring
        _ ≤ K * (|y - xiStar| ^ (-(3 : ℝ) / 4) + |y - (-x)| ^ (-(3 : ℝ) / 4)) := by gcongr
    have hnorm_g : ‖deriv (dphi δ) y‖ = |deriv (dphi δ) y| := Real.norm_eq_abs _
    calc ‖deriv (dphi δ) y‖ * ‖phiY y (x : ℂ)‖
        ≤ |deriv (dphi δ) y| * (π + 2 * Real.log 5 +
            4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - x| ^ (-(1 : ℝ) / 4)) +
            4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-x)| ^ (-(1 : ℝ) / 4))) := by
          rw [hnorm_g]; exact mul_le_mul_of_nonneg_left hphi (abs_nonneg _)
      _ ≤ (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖ + 2 * K * |y - xiStar| ^ (-(3 : ℝ) / 4) +
            K * |y - x| ^ (-(3 : ℝ) / 4) + K * |y - (-x)| ^ (-(3 : ℝ) / 4) := by
          rw [hnorm_g]; linarith
  · -- On Ioi R, |x - y| ≥ 2 and |x + y| ≥ 2, so ‖phiY y (x : ℂ)‖ ≤ M_far
    set M_far : ℝ := π + 2 * Real.log 5 + 8 * (π / 2) ^ (-(1 : ℝ) / 4) with hMfar
    refine Integrable.mono' ((hg.mono_set (Ioi_subset_Ioi hxiR)).norm.mul_const M_far)
      (hmeas.mono_set (Ioi_subset_Ioi hxiR)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyR : R < y := hy
    have h1 : x < y := by linarith [le_abs_self x]
    have h2 : -x < y := by linarith [neg_le_abs x]
    have hphi := norm_phiY_real_le h1.ne (by linarith)
    have hge1 : 1 ≤ |x - y| := by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith [le_abs_self x]
    have hge2 : 1 ≤ |x + y| := by rw [abs_of_pos (by linarith)]; linarith [neg_le_abs x]
    have hp1 : (π * |x - y| / 2) ^ (-(1 : ℝ) / 4) ≤ (π / 2) ^ (-(1 : ℝ) / 4) := by
      rw [show π * |x - y| / 2 = (π / 2) * |x - y| by ring, Real.mul_rpow (by positivity) (abs_nonneg _)]
      have : |x - y| ^ (-(1 : ℝ) / 4) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hge1 (by norm_num)
      nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < π / 2) (-(1 : ℝ) / 4)]
    have hp2 : (π * |x + y| / 2) ^ (-(1 : ℝ) / 4) ≤ (π / 2) ^ (-(1 : ℝ) / 4) := by
      rw [show π * |x + y| / 2 = (π / 2) * |x + y| by ring, Real.mul_rpow (by positivity) (abs_nonneg _)]
      have : |x + y| ^ (-(1 : ℝ) / 4) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hge2 (by norm_num)
      nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < π / 2) (-(1 : ℝ) / 4)]
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)


private lemma integral_rpow_neg_three_quarter_ball (c r : ℝ) (hr : 0 < r) :
    ∫ y in Ioc (c - r) (c + r), |y - c| ^ (-(3 : ℝ) / 4) = 8 * r ^ ((1 : ℝ) / 4) := by
  have hle : c - r ≤ c + r := by linarith
  rw [← intervalIntegral.integral_of_le hle]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := c - r) (b := c) (c := c + r) (f := fun y : ℝ => |y - c| ^ (-(3 : ℝ) / 4))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
      (integrableOn_rpow_neg_three_quarter c (c - r) c (by linarith)))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
      (integrableOn_rpow_neg_three_quarter c c (c + r) (by linarith)))
  rw [← hsplit]
  have h1 : ∫ y in (c - r)..c, |y - c| ^ (-(3 : ℝ) / 4) = 4 * r ^ ((1 : ℝ) / 4) := by
    have heq : EqOn (fun y : ℝ => |y - c| ^ (-(3 : ℝ) / 4)) (fun y : ℝ => (c - y) ^ (-(3 : ℝ) / 4)) (uIcc (c - r) c) := by
      intro y hy; dsimp only; rw [uIcc_of_le (by linarith)] at hy; rw [abs_sub_comm, abs_of_nonneg (by linarith [hy.2])]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_comp_sub_left (fun t => t ^ (-(3 : ℝ) / 4)) c]
    simp only [sub_self, sub_sub_cancel]
    rw [integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num), sub_zero]
    ring_nf
  have h2 : ∫ y in c..(c + r), |y - c| ^ (-(3 : ℝ) / 4) = 4 * r ^ ((1 : ℝ) / 4) := by
    have heq : EqOn (fun y : ℝ => |y - c| ^ (-(3 : ℝ) / 4)) (fun y : ℝ => (y - c) ^ (-(3 : ℝ) / 4)) (uIcc c (c + r)) := by
      intro y hy; dsimp only; rw [uIcc_of_le (by linarith)] at hy; rw [abs_of_nonneg (by linarith [hy.1])]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_comp_sub_right (fun t => t ^ (-(3 : ℝ) / 4)) c]
    simp only [sub_self, add_sub_cancel_left]
    rw [integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num), sub_zero]
    ring_nf
  rw [h1, h2]; ring

private lemma norm_integral_B_le {δ C0 : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hC0 : 0 < C0)
    (hbd : ∀ y > xiStar, |deriv (dphi δ) y| ≤ C0 * (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y)))
    (x R r0 : ℝ) (hr0_gt : 0 < r0) (b : ℂ) (hb0 : 0 < b.im) (hb1 : b.im ≤ 1 / 2)
    {h_tail : ℝ → ℝ} (h_tail_int : IntegrableOn h_tail (Ioc xiStar R))
    (hh_tail_le : ∀ y : ℝ, (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖ +
      2 * (C0 * max 1 (R - xiStar) ^ ((1 : ℝ) / 2) * (4 * (π / 2) ^ (-(1 : ℝ) / 4))) *
        |y - xiStar| ^ (-(3 : ℝ) / 4) ≤ h_tail y)
    (hint_b : IntegrableOn (fun y => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) (Ioi xiStar)) :
    ‖∫ y in (Ioc xiStar R ∩ (Ioo (x - 2 * r0) (x + 2 * r0) ∪ Ioo (-x - 2 * r0) (-x + 2 * r0))),
        ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b‖ ≤
      (∫ y in (Ioc xiStar R ∩ (Ioo (x - 2 * r0) (x + 2 * r0) ∪ Ioo (-x - 2 * r0) (-x + 2 * r0))), h_tail y) +
        32 * (C0 * max 1 (R - xiStar) ^ ((1 : ℝ) / 2) * (4 * (π / 2) ^ (-(1 : ℝ) / 4))) * r0 ^ ((1 : ℝ) / 4) := by
  set B_set : Set ℝ := Ioc xiStar R ∩ (Ioo (x - 2 * r0) (x + 2 * r0) ∪ Ioo (-x - 2 * r0) (-x + 2 * r0))
  set C1 : ℝ := C0 * max 1 (R - xiStar) ^ ((1 : ℝ) / 2) with hC1def
  set K : ℝ := C1 * (4 * (π / 2) ^ (-(1 : ℝ) / 4)) with hKdef
  have hK : 0 ≤ K := by positivity
  have hB_meas : MeasurableSet B_set := measurableSet_Ioc.inter (measurableSet_Ioo.union measurableSet_Ioo)
  have hB_sub : B_set ⊆ Ioi xiStar := fun _ hy => hy.1.1
  have h_meas_B_le : volume.real B_set ≤ 8 * r0 := by
    have h1 : B_set ⊆ Ioo (x - 2 * r0) (x + 2 * r0) ∪ Ioo (-x - 2 * r0) (-x + 2 * r0) := inter_subset_right
    have h2 := (measureReal_mono (μ := volume) h1
      (measure_union_lt_top measure_Ioo_lt_top measure_Ioo_lt_top).ne).trans
      (measureReal_union_le (Ioo (x - 2 * r0) (x + 2 * r0)) (Ioo (-x - 2 * r0) (-x + 2 * r0)))
    rw [Real.volume_real_Ioo, Real.volume_real_Ioo,
      max_eq_left (by linarith : 0 ≤ x + 2 * r0 - (x - 2 * r0)),
      max_eq_left (by linarith : 0 ≤ -x + 2 * r0 - (-x - 2 * r0))] at h2
    linarith
  have h_int_ball : ∀ c : ℝ,
      ∫ y in B_set, ((Ioc (c - r0) (c + r0)).indicator (fun z => |z - c| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)) ≤
        16 * r0 ^ ((1 : ℝ) / 4) := by
    intro c
    have h_int_ind : IntegrableOn (fun y => (Ioc (c - r0) (c + r0)).indicator (fun z => |z - c| ^ (-(3 : ℝ) / 4)) y) B_set :=
      ((integrableOn_rpow_neg_three_quarter c (c - r0) (c + r0) (by linarith)).integrable_indicator
        measurableSet_Ioc).integrableOn
    have h_int_c : IntegrableOn (fun _ : ℝ => r0 ^ (-(3 : ℝ) / 4)) B_set :=
      (integrableOn_const (hs := (measure_Ioc_lt_top (a := xiStar) (b := R)).ne)).mono_set inter_subset_left
    rw [integral_add h_int_ind h_int_c]
    have hA : ∫ y in B_set, (Ioc (c - r0) (c + r0)).indicator (fun z => |z - c| ^ (-(3 : ℝ) / 4)) y ≤
        8 * r0 ^ ((1 : ℝ) / 4) := by
      calc ∫ y in B_set, (Ioc (c - r0) (c + r0)).indicator (fun z => |z - c| ^ (-(3 : ℝ) / 4)) y
          ≤ ∫ y : ℝ, (Ioc (c - r0) (c + r0)).indicator (fun z => |z - c| ^ (-(3 : ℝ) / 4)) y :=
            setIntegral_le_integral
              ((integrableOn_rpow_neg_three_quarter c (c - r0) (c + r0) (by linarith)).integrable_indicator measurableSet_Ioc)
              (ae_of_all _ fun y => Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _)
        _ = ∫ y in Ioc (c - r0) (c + r0), |y - c| ^ (-(3 : ℝ) / 4) := integral_indicator measurableSet_Ioc
        _ = 8 * r0 ^ ((1 : ℝ) / 4) := integral_rpow_neg_three_quarter_ball c r0 hr0_gt
    have hB : ∫ _ in B_set, r0 ^ (-(3 : ℝ) / 4) ≤ 8 * r0 ^ ((1 : ℝ) / 4) := by
      rw [setIntegral_const, smul_eq_mul]
      calc volume.real B_set * r0 ^ (-(3 : ℝ) / 4)
          ≤ (8 * r0) * r0 ^ (-(3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right h_meas_B_le (Real.rpow_nonneg hr0_gt.le _)
        _ = 8 * (r0 ^ (1 : ℝ) * r0 ^ (-(3 : ℝ) / 4)) := by rw [Real.rpow_one]; ring
        _ = 8 * r0 ^ ((1 : ℝ) / 4) := by rw [← Real.rpow_add hr0_gt]; norm_num
    linarith
  have h_i1 : IntegrableOn (fun y => (Ioc (b.re - r0) (b.re + r0)).indicator (fun z => |z - b.re| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)) B_set :=
    ((integrableOn_rpow_neg_three_quarter b.re (b.re - r0) (b.re + r0) (by linarith)).integrable_indicator
      measurableSet_Ioc).integrableOn.add
      ((integrableOn_const (hs := (measure_Ioc_lt_top (a := xiStar) (b := R)).ne)).mono_set inter_subset_left)
  have h_i2 : IntegrableOn (fun y => (Ioc (-b.re - r0) (-b.re + r0)).indicator (fun z => |z - (-b.re)| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)) B_set :=
    ((integrableOn_rpow_neg_three_quarter (-b.re) (-b.re - r0) (-b.re + r0) (by linarith)).integrable_indicator
      measurableSet_Ioc).integrableOn.add
      ((integrableOn_const (hs := (measure_Ioc_lt_top (a := xiStar) (b := R)).ne)).mono_set inter_subset_left)
  have h_dom_B : IntegrableOn (fun y : ℝ =>
      h_tail y + K * ((Ioc (b.re - r0) (b.re + r0)).indicator (fun z => |z - b.re| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)) +
        K * ((Ioc (-b.re - r0) (-b.re + r0)).indicator (fun z => |z - (-b.re)| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)))
      B_set :=
    ((h_tail_int.mono_set inter_subset_left).add (h_i1.const_mul K)).add (h_i2.const_mul K)
  have h_mono : ‖∫ y in B_set, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b‖ ≤
      ∫ y in B_set, (h_tail y + K * ((Ioc (b.re - r0) (b.re + r0)).indicator (fun z => |z - b.re| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)) +
        K * ((Ioc (-b.re - r0) (-b.re + r0)).indicator (fun z => |z - (-b.re)| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_ae_restrict ((hint_b.mono_set hB_sub).norm) h_dom_B ?_
    have hne1 : ∀ᵐ y ∂(volume.restrict B_set), y ≠ b.re := by
      rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton b.re)
    have hne2 : ∀ᵐ y ∂(volume.restrict B_set), y ≠ -b.re := by
      rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-b.re))
    filter_upwards [ae_restrict_mem hB_meas, hne1, hne2] with y hy hnb1 hnb2
    have hyx : xiStar < y := hy.1.1
    have hyR : y ≤ R := hy.1.2
    have hphi := norm_phiY_le_upperHalf hb0 hb1 hnb1.symm (by intro h; apply hnb2; linarith)
    rw [abs_sub_comm b.re y, show |b.re + y| = |y - (-b.re)| by rw [sub_neg_eq_add, add_comm]] at hphi
    have hg_bd : |deriv (dphi δ) y| ≤ C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) := by
      have hbd_y := hbd y hyx
      have he : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by have := xiStar_pos; have := Real.pi_pos; nlinarith)
      have hm_le : (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) ≤
          max 1 (R - xiStar) ^ ((1 : ℝ) / 2) * (y - xiStar) ^ (-(1 : ℝ) / 2) := by
        rcases le_total (y - xiStar) 1 with hm | hm
        · rw [min_eq_left hm]
          have hmax : (1 : ℝ) ≤ max 1 (R - xiStar) ^ ((1 : ℝ) / 2) :=
            Real.one_le_rpow (le_max_left (1 : ℝ) (R - xiStar)) (by norm_num)
          exact le_mul_of_one_le_left (Real.rpow_nonneg (by linarith : 0 ≤ y - xiStar) _) hmax
        · rw [min_eq_right hm, Real.one_rpow]
          have h1 : 0 < y - xiStar := by linarith
          have h2 : y - xiStar ≤ max 1 (R - xiStar) := le_trans (by linarith) (le_max_right _ _)
          have h3 : (y - xiStar) ^ ((1 : ℝ) / 2) ≤ max 1 (R - xiStar) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow h1.le h2 (by norm_num)
          have h4 : (y - xiStar) ^ ((1 : ℝ) / 2) * (y - xiStar) ^ (-(1 : ℝ) / 2) = 1 := by
            rw [← Real.rpow_add h1]; norm_num
          nlinarith [Real.rpow_pos_of_pos h1 (-(1 : ℝ) / 2)]
      calc |deriv (dphi δ) y|
          ≤ C0 * (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y)) := hbd_y
        _ ≤ C0 * (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * 1 := by gcongr
        _ ≤ C0 * (max 1 (R - xiStar) ^ ((1 : ℝ) / 2) * (y - xiStar) ^ (-(1 : ℝ) / 2)) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hm_le hC0.le
        _ = C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) := by rw [hC1def]; ring
    have hyx_pos : 0 < y - xiStar := by linarith
    have hyx1_pos : 0 < |y - b.re| := abs_pos.mpr (sub_ne_zero.mpr hnb1)
    have hyx2_pos : 0 < |y - (-b.re)| := abs_pos.mpr (sub_ne_zero.mpr hnb2)
    have hY1 := young_three_halves (Real.rpow_nonneg hyx_pos.le (-(1 : ℝ) / 2))
      (Real.rpow_nonneg hyx1_pos.le (-(1 : ℝ) / 4))
    have hY2 := young_three_halves (Real.rpow_nonneg hyx_pos.le (-(1 : ℝ) / 2))
      (Real.rpow_nonneg hyx2_pos.le (-(1 : ℝ) / 4))
    have hp1 : ((y - xiStar) ^ (-(1 : ℝ) / 2)) ^ ((3 : ℝ) / 2) = |y - xiStar| ^ (-(3 : ℝ) / 4) := by
      rw [← Real.rpow_mul hyx_pos.le, abs_of_pos hyx_pos]; norm_num
    have hp2 : (|y - b.re| ^ (-(1 : ℝ) / 4)) ^ (3 : ℝ) = |y - b.re| ^ (-(3 : ℝ) / 4) := by
      rw [← Real.rpow_mul hyx1_pos.le]; norm_num
    have hp3 : (|y - (-b.re)| ^ (-(1 : ℝ) / 4)) ^ (3 : ℝ) = |y - (-b.re)| ^ (-(3 : ℝ) / 4) := by
      rw [← Real.rpow_mul hyx2_pos.le]; norm_num
    rw [hp1, hp2] at hY1
    rw [hp1, hp3] at hY2
    have h_ind_le : ∀ c : ℝ, |y - c| ^ (-(3 : ℝ) / 4) ≤
        (Ioc (c - r0) (c + r0)).indicator (fun z => |z - c| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4) := by
      intro c
      by_cases hc : y ∈ Ioc (c - r0) (c + r0)
      · rw [Set.indicator_of_mem hc]; linarith [Real.rpow_nonneg hr0_gt.le (-(3 : ℝ) / 4)]
      · rw [Set.indicator_of_notMem hc, zero_add]
        have hge : r0 ≤ |y - c| := by
          rcases le_or_gt y (c - r0) with h | h
          · rw [abs_of_nonpos (by linarith)]; linarith
          · have : c + r0 < y := by by_contra h'; exact hc ⟨h, not_lt.mp h'⟩
            rw [abs_of_pos (by linarith)]; linarith
        exact Real.rpow_le_rpow_of_nonpos hr0_gt hge (by norm_num)
    have hrpow1 : (π * |y - b.re| / 2) ^ (-(1 : ℝ) / 4) = (π / 2) ^ (-(1 : ℝ) / 4) * |y - b.re| ^ (-(1 : ℝ) / 4) := by
      rw [show π * |y - b.re| / 2 = (π / 2) * |y - b.re| by ring, Real.mul_rpow (by positivity) (abs_nonneg _)]
    have hrpow2 : (π * |y - (-b.re)| / 2) ^ (-(1 : ℝ) / 4) = (π / 2) ^ (-(1 : ℝ) / 4) * |y - (-b.re)| ^ (-(1 : ℝ) / 4) := by
      rw [show π * |y - (-b.re)| / 2 = (π / 2) * |y - (-b.re)| by ring, Real.mul_rpow (by positivity) (abs_nonneg _)]
    rw [hrpow1, hrpow2] at hphi
    rw [norm_mul, Complex.norm_real]
    have hnorm_g : ‖deriv (dphi δ) y‖ = |deriv (dphi δ) y| := Real.norm_eq_abs _
    have hp_tail := hh_tail_le y
    have hprod1 : |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - b.re| ^ (-(1 : ℝ) / 4))) ≤
        K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - b.re| ^ (-(1 : ℝ) / 4)) := by
      calc |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - b.re| ^ (-(1 : ℝ) / 4)))
          ≤ C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - b.re| ^ (-(1 : ℝ) / 4))) := by
            gcongr
        _ = K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - b.re| ^ (-(1 : ℝ) / 4)) := by rw [hKdef]; ring
    have hprod2 : |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-b.re)| ^ (-(1 : ℝ) / 4))) ≤
        K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - (-b.re)| ^ (-(1 : ℝ) / 4)) := by
      calc |deriv (dphi δ) y| * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-b.re)| ^ (-(1 : ℝ) / 4)))
          ≤ C1 * (y - xiStar) ^ (-(1 : ℝ) / 2) * (4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-b.re)| ^ (-(1 : ℝ) / 4))) := by
            gcongr
        _ = K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - (-b.re)| ^ (-(1 : ℝ) / 4)) := by rw [hKdef]; ring
    calc ‖deriv (dphi δ) y‖ * ‖phiY y b‖
        ≤ |deriv (dphi δ) y| * (π + 2 * Real.log 5 +
            4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - b.re| ^ (-(1 : ℝ) / 4)) +
            4 * ((π / 2) ^ (-(1 : ℝ) / 4) * |y - (-b.re)| ^ (-(1 : ℝ) / 4))) := by
          rw [hnorm_g]; exact mul_le_mul_of_nonneg_left hphi (abs_nonneg _)
      _ ≤ (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖ +
            K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - b.re| ^ (-(1 : ℝ) / 4)) +
            K * ((y - xiStar) ^ (-(1 : ℝ) / 2) * |y - (-b.re)| ^ (-(1 : ℝ) / 4)) := by
          rw [hnorm_g]; linarith
      _ ≤ (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖ + 2 * K * |y - xiStar| ^ (-(3 : ℝ) / 4) +
            K * |y - b.re| ^ (-(3 : ℝ) / 4) + K * |y - (-b.re)| ^ (-(3 : ℝ) / 4) := by
          have hKY1 := mul_le_mul_of_nonneg_left hY1 hK
          have hKY2 := mul_le_mul_of_nonneg_left hY2 hK
          linarith
      _ ≤ h_tail y + K * ((Ioc (b.re - r0) (b.re + r0)).indicator (fun z => |z - b.re| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)) +
            K * ((Ioc (-b.re - r0) (-b.re + r0)).indicator (fun z => |z - (-b.re)| ^ (-(3 : ℝ) / 4)) y + r0 ^ (-(3 : ℝ) / 4)) := by
          have hKi1 := mul_le_mul_of_nonneg_left (h_ind_le b.re) hK
          have hKi2 := mul_le_mul_of_nonneg_left (h_ind_le (-b.re)) hK
          linarith
  refine h_mono.trans ?_
  have h1 := integral_add (h_tail_int.mono_set inter_subset_left) (h_i1.const_mul K)
  have h2 := integral_add ((h_tail_int.mono_set inter_subset_left).add (h_i1.const_mul K)) (h_i2.const_mul K)
  simp only [Pi.add_apply] at h1 h2
  rw [h2, h1, integral_const_mul, integral_const_mul]
  nlinarith [h_int_ball b.re, h_int_ball (-b.re)]

/-- **`ΔΦ_δ` boundary limit as `Im b → 0+`** (`cts:smooth-env` (2)):
for every `δ ∈ (0, 1/4)` and every `x : ℝ`, `DeltaPhi δ b → DeltaPhi δ (x : ℂ)` as `b → x` in `Im b > 0`. -/
theorem tendsto_DeltaPhi_real {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (x : ℝ) :
    Tendsto (DeltaPhi δ) (𝓝[upperHalf] (x : ℂ)) (𝓝 (DeltaPhi δ (x : ℂ))) := by
  unfold DeltaPhi
  refine Tendsto.const_mul (1 / (π : ℂ)) ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C0, hC0, hb_a⟩ := outerS4a
  have hg := integrableOn_dphi_deriv hδ0 hδ1
  have hint_x := integrableOn_dphi_phiY_real hδ0 hδ1 x
  set R : ℝ := max (xiStar + 1) (|x| + 2) with hRdef
  have hxiR : xiStar ≤ R := by linarith [le_max_left (xiStar + 1) (|x| + 2)]
  set C1 : ℝ := C0 * max 1 (R - xiStar) ^ ((1 : ℝ) / 2) with hC1def
  have hC1 : 0 ≤ C1 := by positivity
  set K : ℝ := C1 * (4 * (π / 2) ^ (-(1 : ℝ) / 4)) with hKdef
  have hK : 0 ≤ K := by positivity
  -- On B_r = Ioc xiStar R ∩ (Ioo (x - 2r) (x + 2r) ∪ Ioo (-x - 2r) (-x + 2r)),
  -- the singular integral is O(r^{1/4}) + ∫_{B_r} (|g| + |y-xiStar|^{-3/4}) → 0 as r → 0+.
  set B : ℝ → Set ℝ := fun r => Ioc xiStar R ∩ (Ioo (x - 2 * r) (x + 2 * r) ∪ Ioo (-x - 2 * r) (-x + 2 * r))
  have hB_meas : ∀ r, MeasurableSet (B r) := fun r =>
    measurableSet_Ioc.inter (measurableSet_Ioo.union measurableSet_Ioo)
  have hB_sub : ∀ r, B r ⊆ Ioi xiStar := fun r _ hy => hy.1.1
  -- Function for shrinking tail:
  set h_tail : ℝ → ℝ := fun y =>
    (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖ + 2 * K * |y - xiStar| ^ (-(3 : ℝ) / 4) +
      ‖((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)‖ with hh_tail
  have h_tail_int : IntegrableOn h_tail (Ioc xiStar R) := by
    have h0 : IntegrableOn (fun y => (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖) (Ioc xiStar R) :=
      (hg.mono_set Ioc_subset_Ioi_self).norm.const_mul _
    have h1 : IntegrableOn (fun y => 2 * K * |y - xiStar| ^ (-(3 : ℝ) / 4)) (Ioc xiStar R) :=
      (integrableOn_rpow_neg_three_quarter xiStar xiStar R hxiR).const_mul _
    exact (h0.add h1).add ((hint_x.mono_set Ioc_subset_Ioi_self).norm)
  have h_tail_lim : Tendsto (fun r : ℝ => ∫ y in B r, h_tail y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h_ae : ∀ᵐ y ∂(volume.restrict (Ioc xiStar R)),
        Tendsto (fun r : ℝ => (B r).indicator h_tail y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hne1 : ∀ᵐ y ∂(volume.restrict (Ioc xiStar R)), y ≠ x := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton x)
      have hne2 : ∀ᵐ y ∂(volume.restrict (Ioc xiStar R)), y ≠ -x := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-x))
      filter_upwards [hne1, hne2] with y hy1 hy2
      set d0 : ℝ := min |y - x| |y - (-x)| / 2 with hd0def
      have hd0 : 0 < d0 := by
        have a1 : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hy1)
        have a2 : 0 < |y - (-x)| := abs_pos.mpr (sub_ne_zero.mpr hy2)
        positivity
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hd0] with r hr
      have hnot : y ∉ B r := by
        intro ⟨_, hmem⟩
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have : |y - x| < 2 * r := abs_lt.mpr ⟨by linarith, by linarith⟩
          linarith [min_le_left |y - x| |y - (-x)|, hr.2, hd0def]
        · have : |y - (-x)| < 2 * r := abs_lt.mpr ⟨by linarith, by linarith⟩
          linarith [min_le_right |y - x| |y - (-x)|, hr.2, hd0def]
      simp [Set.indicator_of_notMem hnot]
    have h_dct : Tendsto (fun r : ℝ => ∫ y in Ioc xiStar R, (B r).indicator h_tail y) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ _ in Ioc xiStar R, (0 : ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖h_tail y‖) ?_ ?_ h_tail_int.norm h_ae
      · filter_upwards with r
        exact (h_tail_int.aestronglyMeasurable).indicator (hB_meas r)
      · filter_upwards with r
        exact Eventually.of_forall fun y => by
          by_cases hy : y ∈ B r
          · simp [Set.indicator_of_mem hy]
          · simp [Set.indicator_of_notMem hy]
    simp only [integral_zero] at h_dct
    refine h_dct.congr (fun r => ?_)
    rw [setIntegral_indicator (hB_meas r), inter_eq_right.mpr inter_subset_left]
  have h_rpow_lim : Tendsto (fun r : ℝ => 32 * K * r ^ ((1 : ℝ) / 4)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => r ^ ((1 : ℝ) / 4)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun r : ℝ => r ^ ((1 : ℝ) / 4)) :=
        continuous_id.rpow_const (fun _ => Or.inr (by norm_num))
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h0.const_mul (32 * K)
  have h_sum_lim := h_tail_lim.add h_rpow_lim
  simp only [add_zero] at h_sum_lim
  obtain ⟨r0, hr0_pos, hr0_mem⟩ : ∃ r0 ∈ Ioo (0 : ℝ) (1 / 2),
      (∫ y in B r0, h_tail y) + 32 * K * r0 ^ ((1 : ℝ) / 4) < ε / 3 := by
    have hev := (h_sum_lim.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).and
      (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨r0, hr0⟩ := hev.exists
    exact ⟨r0, hr0.2, hr0.1⟩
  have hr0_gt : 0 < r0 := hr0_pos.1
  have hr0_lt : r0 < 1 / 2 := hr0_pos.2
  -- Define S = Ioi xiStar \ B r0
  set S : Set ℝ := Ioi xiStar \ B r0 with hSdef
  have hS_meas : MeasurableSet S := measurableSet_Ioi.diff (hB_meas r0)
  have hS_union : B r0 ∪ S = Ioi xiStar := union_diff_cancel (hB_sub r0)
  have hS_disj : Disjoint (B r0) S := disjoint_sdiff_self_right
  -- On S, for |b.re - x| < r0 and 0 < b.im ≤ 1/2, ‖phiY y b‖ is uniformly bounded by a constant M_S!
  set M_S : ℝ := π + 2 * Real.log 5 + 8 * (π * r0 / 2) ^ (-(1 : ℝ) / 4) with hMSdef
  have hMS_pos : 0 ≤ M_S := by
    have : 0 < π * r0 / 2 := by positivity
    have : 0 < Real.log 5 := Real.log_pos (by norm_num)
    positivity
  have h_unif_S : ∀ b : ℂ, |b.re - x| < r0 → 0 < b.im → b.im ≤ 1 / 2 →
      ∀ y ∈ S, y ≠ b.re ∧ y ≠ -b.re → ‖phiY y b‖ ≤ M_S := by
    intro b hbre hb0 hb1 y hy ⟨hne1, hne2⟩
    have hy_gt : xiStar < y := hy.1
    have hy_not : y ∉ B r0 := hy.2
    have hphi := norm_phiY_le_upperHalf hb0 hb1 hne1.symm (by intro h; apply hne2; linarith)
    have hge_r0 : r0 ≤ |b.re - y| ∧ r0 ≤ |b.re + y| := by
      rcases le_or_gt y R with hyR | hyR
      · have hy_out : ¬ (y ∈ Ioo (x - 2 * r0) (x + 2 * r0) ∨ y ∈ Ioo (-x - 2 * r0) (-x + 2 * r0)) := by
          intro hmem; exact hy_not ⟨⟨hy_gt, hyR⟩, hmem⟩
        rw [not_or] at hy_out
        constructor
        · have h1 : ¬ (x - 2 * r0 < y ∧ y < x + 2 * r0) := hy_out.1
          rcases le_or_gt y (x - 2 * r0) with h | h
          · rw [abs_sub_comm, abs_of_nonpos (by linarith [abs_lt.mp hbre])]; linarith [abs_lt.mp hbre]
          · have : x + 2 * r0 ≤ y := by by_contra h'; exact h1 ⟨h, not_le.mp h'⟩
            rw [abs_sub_comm, abs_of_pos (by linarith [abs_lt.mp hbre])]; linarith [abs_lt.mp hbre]
        · have h2 : ¬ (-x - 2 * r0 < y ∧ y < -x + 2 * r0) := hy_out.2
          rcases le_or_gt y (-x - 2 * r0) with h | h
          · rw [abs_of_nonpos (by linarith [abs_lt.mp hbre])]; linarith [abs_lt.mp hbre]
          · have : -x + 2 * r0 ≤ y := by by_contra h'; exact h2 ⟨h, not_le.mp h'⟩
            rw [abs_of_pos (by linarith [abs_lt.mp hbre])]; linarith [abs_lt.mp hbre]
      · have h1 : 1 ≤ y - b.re := by linarith [abs_lt.mp hbre, le_max_right (xiStar + 1) (|x| + 2), le_abs_self x, hRdef, hr0_lt]
        have h2 : 1 ≤ b.re + y := by linarith [abs_lt.mp hbre, le_max_right (xiStar + 1) (|x| + 2), neg_le_abs x, hRdef, hr0_lt]
        constructor
        · rw [abs_sub_comm, abs_of_pos (by linarith [h1])]; linarith [h1, hr0_lt]
        · rw [abs_of_pos (by linarith [h2])]; linarith [h2, hr0_lt]
    have hp1 : (π * |b.re - y| / 2) ^ (-(1 : ℝ) / 4) ≤ (π * r0 / 2) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by have := Real.pi_pos; nlinarith [hge_r0.1]) (by norm_num)
    have hp2 : (π * |b.re + y| / 2) ^ (-(1 : ℝ) / 4) ≤ (π * r0 / 2) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by have := Real.pi_pos; nlinarith [hge_r0.2]) (by norm_num)
    linarith
  -- By DCT on S, ∫ y in S, g(y) * phiY y b → ∫ y in S, g(y) * phiY y x
  have h_S_lim : Tendsto (fun b : ℂ => ∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b)
      (𝓝[upperHalf] (x : ℂ)) (𝓝 (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ))) := by
    have hev_b : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), |b.re - x| < r0 ∧ 0 < b.im ∧ b.im ≤ 1 / 2 := by
      have h1 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), |b.re - x| < r0 := by
        refine nhdsWithin_le_nhds ?_
        filter_upwards [Metric.tendsto_nhds.mp (Complex.continuous_re.tendsto (x : ℂ)) r0 hr0_gt] with b hb
        simpa [Real.dist_eq] using hb
      have h2 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), 0 < b.im := self_mem_nhdsWithin
      have h3 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.im ≤ 1 / 2 :=
        nhdsWithin_le_nhds (((Complex.continuous_im.tendsto (x : ℂ)).eventually
          (gt_mem_nhds (by simp : (x : ℂ).im < 1 / 2))).mono fun _ h => h.le)
      filter_upwards [h1, h2, h3] with b hb1 hb2 hb3
      exact ⟨hb1, hb2, hb3⟩
    refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖deriv (dphi δ) y‖ * M_S) ?_ ?_
      ((hg.mono_set sdiff_subset).norm.mul_const M_S) ?_
    · filter_upwards [hev_b] with b ⟨_, hb0, hb1⟩
      have hbs : b ∈ imStrip := ⟨hb0, by linarith⟩
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((continuousOn_dphi_deriv δ).mono sdiff_subset).aestronglyMeasurable hS_meas)).mul
        (continuous_phiY_y hbs).aestronglyMeasurable
    · filter_upwards [hev_b] with b ⟨hbre, hb0, hb1⟩
      have hne1 : ∀ᵐ y ∂(volume.restrict S), y ≠ b.re := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton b.re)
      have hne2 : ∀ᵐ y ∂(volume.restrict S), y ≠ -b.re := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-b.re))
      filter_upwards [ae_restrict_mem hS_meas, hne1, hne2] with y hy h1 h2
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (h_unif_S b hbre hb0 hb1 y hy ⟨h1, h2⟩) (norm_nonneg _)
    · have hne1 : ∀ᵐ y ∂(volume.restrict S), y ≠ x := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton x)
      have hne2 : ∀ᵐ y ∂(volume.restrict S), y ≠ -x := by
        rw [ae_iff]; exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-x))
      filter_upwards [hne1, hne2] with y hy1 hy2
      exact Tendsto.const_mul _ (tendsto_phiY_real hy1.symm (by intro h; apply hy2; linarith))
  -- Combine S and B r0
  have hev_S_close : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ),
      ‖(∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) -
        (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ))‖ < ε / 3 := by
    rw [Metric.tendsto_nhds] at h_S_lim
    filter_upwards [h_S_lim (ε / 3) (by positivity)] with b hb
    rwa [dist_eq_norm] at hb
  have hev_b_loc : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), |b.re - x| < r0 ∧ 0 < b.im ∧ b.im ≤ 1 / 2 := by
    have h1 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), |b.re - x| < r0 := by
      refine nhdsWithin_le_nhds ?_
      filter_upwards [Metric.tendsto_nhds.mp (Complex.continuous_re.tendsto (x : ℂ)) r0 hr0_gt] with b hb
      simpa [Real.dist_eq] using hb
    have h2 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), 0 < b.im := self_mem_nhdsWithin
    have h3 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.im ≤ 1 / 2 :=
      nhdsWithin_le_nhds (((Complex.continuous_im.tendsto (x : ℂ)).eventually
        (gt_mem_nhds (by simp : (x : ℂ).im < 1 / 2))).mono fun _ h => h.le)
    filter_upwards [h1, h2, h3] with b hb1 hb2 hb3
    exact ⟨hb1, hb2, hb3⟩
  filter_upwards [hev_S_close, hev_b_loc] with b hS_close ⟨hbre, hb0, hb1⟩
  have hbs : b ∈ imStrip := ⟨hb0, by linarith⟩
  have hint_b : IntegrableOn (fun y => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) (Ioi xiStar) := by
    set εb := min (b.im / 2) ((1 - b.im) / 2)
    have hεb0 : 0 < εb := lt_min (by linarith) (by linarith)
    have hεb1 : εb < 1 / 2 := by
      have h1 : εb ≤ b.im / 2 := min_le_left _ _
      have h2 : εb ≤ (1 - b.im) / 2 := min_le_right _ _
      linarith
    have hbb : b ∈ stripEps εb := ⟨by linarith [min_le_left (b.im / 2) ((1 - b.im) / 2)],
      by linarith [min_le_right (b.im / 2) ((1 - b.im) / 2)]⟩
    exact integrable_param hg (continuous_phiY_y hbs) (fun y => norm_phiY_le_of_stripEps hεb0 hεb1 hbb)
  have h_split_b : (∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) =
      (∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) +
      (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) := by
    rw [← hS_union]
    exact setIntegral_union hS_disj hS_meas (hint_b.mono_set (hB_sub r0)) (hint_b.mono_set diff_subset)
  have h_split_x : (∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)) =
      (∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)) +
      (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)) := by
    rw [← hS_union]
    exact setIntegral_union hS_disj hS_meas (hint_x.mono_set (hB_sub r0)) (hint_x.mono_set diff_subset)
  -- Bound ∫_{B r0} |g * phiY b| + ∫_{B r0} |g * phiY x| < 2ε/3
  have h_Bx : ‖∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)‖ ≤ ∫ y in B r0, h_tail y := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on (hint_x.mono_set (hB_sub r0)).norm (h_tail_int.mono_set inter_subset_left) (hB_meas r0) ?_
    intro y _
    simp only [hh_tail]
    have hp1 : 0 ≤ (π + 2 * Real.log 5) * ‖deriv (dphi δ) y‖ :=
      mul_nonneg (by have : 0 < Real.log 5 := Real.log_pos (by norm_num); positivity) (norm_nonneg _)
    have hp2 : 0 ≤ 2 * K * |y - xiStar| ^ (-(3 : ℝ) / 4) := by positivity
    linarith
  have h_Bb : ‖∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b‖ ≤
      (∫ y in B r0, h_tail y) + 32 * K * r0 ^ ((1 : ℝ) / 4) := by
    simpa only [← hC1def, ← hKdef] using
      norm_integral_B_le hδ0 hδ1 hC0 (fun y hy => (hb_a δ hδ0 hδ1 y hy).1) x R r0 hr0_gt b hb0 hb1
        h_tail_int (fun y => by simp only [hh_tail, hKdef, hC1def]; linarith [norm_nonneg (((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ))])
        hint_b
  have h_rpow_nonneg : 0 ≤ 32 * K * r0 ^ ((1 : ℝ) / 4) := by positivity
  rw [dist_eq_norm, h_split_b, h_split_x]
  calc ‖(∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) +
          (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) -
          ((∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)) +
          (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)))‖
      = ‖(∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) -
          (∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)) +
          ((∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) -
          (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)))‖ := by congr 1; ring
    _ ≤ ‖∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b‖ +
          ‖∫ y in B r0, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)‖ +
          ‖(∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) -
          (∫ y in S, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ))‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring


/-! ### 3. Exact real and imaginary parts of `ΔΦ_δ(x)` on `ℝ` -/

lemma tauOfX_xiStar : tauOfX xiStar = 0 := by
  unfold tauOfX
  rw [cosh_pi_xiStar, div_self (Real.sqrt_pos.mpr (by norm_num)).ne', ← Real.cosh_zero,
    Real.arcosh_cosh (le_refl 0), mul_zero]

lemma yOfX_xiStar : yOfX xiStar = 0 := by
  unfold yOfX
  rw [cosh_pi_xiStar, sub_self, zero_div, Real.sqrt_zero]

lemma dphi_xiStar (δ : ℝ) : dphi δ xiStar = 0 := by
  unfold dphi thetaOutX
  rw [tauOfX_xiStar, thetaOutT_zero, yOfX_xiStar, mul_zero, Real.arctan_zero, sub_self, mul_zero, neg_zero, add_zero]

private lemma continuousOn_dphi (δ : ℝ) : ContinuousOn (dphi δ) (Ici xiStar) := by
  unfold dphi thetaOutX yOfX tauOfX
  obtain ⟨_, -, _, _, hd1, -, -⟩ := thetaOutT_data
  have hc_theta : Continuous thetaOutT := continuous_iff_continuousAt.mpr fun x => (hd1 x).continuousAt
  have hc_arcosh : ContinuousOn (fun x : ℝ => (2 / π) * Real.arcosh (Real.cosh (π * x) / √2)) (Ici xiStar) := by
    refine ContinuousOn.mul continuousOn_const ?_
    have h_eq : EqOn (fun x : ℝ => Real.arcosh (Real.cosh (π * x) / √2))
        (fun x : ℝ => Real.log (Real.cosh (π * x) / √2 + √((Real.cosh (π * x) / √2) ^ 2 - 1))) (Ici xiStar) := by
      intro x _
      rfl
    refine ContinuousOn.congr ?_ h_eq
    refine ContinuousOn.log (by fun_prop) (fun x hx => ?_)
    have hge : 1 ≤ Real.cosh (π * x) / √2 := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num)), one_mul, ← cosh_pi_xiStar, Real.cosh_le_cosh]
      have hpi := Real.pi_pos
      rw [abs_of_pos (mul_pos hpi xiStar_pos), abs_of_pos (mul_pos hpi (lt_of_lt_of_le xiStar_pos hx))]
      exact mul_le_mul_of_nonneg_left hx hpi.le
    have hsq : 0 ≤ √((Real.cosh (π * x) / √2) ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  have hc_y : Continuous (fun x : ℝ => √((Real.cosh (π * x) - √2) / (Real.cosh (π * x) + √2))) := by
    refine Continuous.sqrt (Continuous.div (by fun_prop) (by fun_prop) (fun x => ?_))
    have := Real.cosh_pos (π * x); have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2); positivity
  exact (hc_theta.comp_continuousOn hc_arcosh).neg.add
    (continuousOn_const.mul ((Real.continuous_arctan.comp (continuous_const.mul hc_y)).sub
      (Real.continuous_arctan.comp hc_y)).continuousOn)

private lemma hasDerivAt_dphi {δ y : ℝ} (hy : xiStar < y) :
    HasDerivAt (dphi δ) (deriv (dphi δ) y) y := by
  obtain ⟨_, -, Θ1, _, hd1, -, -⟩ := thetaOutT_data
  have h1 : HasDerivAt (fun τ => -thetaOutT τ + gfun (1 - δ) τ) (-Θ1 (tauOfX y) + g1 (1 - δ) (tauOfX y)) (tauOfX y) :=
    (hd1 (tauOfX y)).neg.add (hasDerivAt_gfun _ (tauOfX y))
  have hth : HasDerivAt (fun w => -thetaOutT (tauOfX w) + gfun (1 - δ) (tauOfX w))
      ((-Θ1 (tauOfX y) + g1 (1 - δ) (tauOfX y)) * tx y) y :=
    h1.scomp y (hasDerivAt_tauOfX hy) |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hev : ∀ᶠ w in 𝓝 y, xiStar < w := Ioi_mem_nhds hy
  have hF : dphi δ =ᶠ[𝓝 y] fun w => -thetaOutT (tauOfX w) + gfun (1 - δ) (tauOfX w) :=
    hev.mono fun w hw => dphi_eq hw
  exact (hth.congr_of_eventuallyEq hF).differentiableAt.hasDerivAt

/-- **`Im ΔΦ_δ(x + i0) = -δφ_δ(x)` for `x ≥ ξ_*`** (`cts:smooth-env` (2)). -/
theorem im_DeltaPhi_real_ge {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : xiStar ≤ x) :
    (DeltaPhi δ (x : ℂ)).im = -dphi δ x := by
  have hint := integrableOn_dphi_phiY_real hδ0 hδ1 x
  have hpi := Real.pi_pos
  have h_im_eq : (DeltaPhi δ (x : ℂ)).im =
      (1 / π) * ∫ y in Ioi xiStar, deriv (dphi δ) y * (phiY y (x : ℂ)).im := by
    unfold DeltaPhi
    rw [show (1 / (π : ℂ)) = (((1 / π : ℝ)) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul]
    congr 1
    have hcomm := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply] at hcomm
    rw [← hcomm]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp [Complex.mul_im]
  rw [h_im_eq]
  rcases eq_or_lt_of_le hx with rfl | hx_gt
  · -- x = xiStar: for all y > xiStar, -y < xiStar < y, so (phiY y xiStar).im = 0
    have h0 : ∀ y ∈ Ioi xiStar, deriv (dphi δ) y * (phiY y (xiStar : ℂ)).im = 0 := by
      intro y hy
      have hyx : xiStar < y := hy
      have hneg : -y < xiStar := by have := xiStar_pos; linarith
      rw [im_phiY_real_of_abs_lt hneg hyx, mul_zero]
    rw [setIntegral_eq_zero_of_forall_eq_zero h0, mul_zero, dphi_xiStar, neg_zero]
  · -- xiStar < x: integrand is (-π) * deriv (dphi δ) y on (xiStar, x) and 0 on (x, ∞)
    have hsplit := setIntegral_union (s := Ioc xiStar x) (t := Ioi x)
      Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.im.mono_set (Ioc_subset_Ioi_self))
      (hint.im.mono_set (Ioi_subset_Ioi hx_gt.le))
    have hunion : Ioc xiStar x ∪ Ioi x = Ioi xiStar := Ioc_union_Ioi_eq_Ioi hx_gt.le
    have hint_im : IntegrableOn (fun y => deriv (dphi δ) y * (phiY y (x : ℂ)).im) (Ioi xiStar) := by
      have hcomm := Complex.imCLM.integral_comp_comm hint
      -- Actually let's just use hint.im? No, hint is complex, let's get IntegrableOn of im directly:
      have : (fun y => deriv (dphi δ) y * (phiY y (x : ℂ)).im) =
          fun y => (((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)).im := by
        funext y; simp [Complex.mul_im]
      rw [this]
      exact Complex.imCLM.integrable_comp hint
    have hsplit' := setIntegral_union (s := Ioc xiStar x) (t := Ioi x)
      Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint_im.mono_set Ioc_subset_Ioi_self)
      (hint_im.mono_set (Ioi_subset_Ioi hx_gt.le))
    rw [hunion] at hsplit'
    rw [hsplit']
    have h_zero_tail : ∫ y in Ioi x, deriv (dphi δ) y * (phiY y (x : ℂ)).im = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      have hyx : x < y := hy
      have hneg : -y < x := by have := xiStar_pos; linarith
      rw [im_phiY_real_of_abs_lt hneg hyx, mul_zero]
    have h_left : ∫ y in Ioc xiStar x, deriv (dphi δ) y * (phiY y (x : ℂ)).im =
        (-π) * ∫ y in Ioc xiStar x, deriv (dphi δ) y := by
      rw [← integral_const_mul]
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      have hne : ∀ᵐ y, y ∈ Ioc xiStar x → y ≠ x := by
        rw [← ae_restrict_iff' measurableSet_Ioc, ae_iff]
        exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton x)
      filter_upwards [hne] with y hny hy
      have hy_pos : 0 < y := lt_trans xiStar_pos hy.1
      have hy_lt : y < x := lt_of_le_of_ne hy.2 (hny hy)
      rw [im_phiY_real_of_gt hy_pos hy_lt, mul_comm]
    have hFTC : ∫ y in Ioc xiStar x, deriv (dphi δ) y = dphi δ x := by
      rw [← intervalIntegral.integral_of_le hx_gt.le]
      have h_int : IntervalIntegrable (deriv (dphi δ)) volume xiStar x :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hx_gt.le).mpr
          ((integrableOn_dphi_deriv hδ0 hδ1).mono_set Ioc_subset_Ioi_self)
      have h_sub := intervalIntegral.integral_eq_sub_of_hasDeriv_right
        ((continuousOn_dphi δ).mono (by rw [uIcc_of_le hx_gt.le]; exact Icc_subset_Ici_self))
        (fun y hy => by rw [min_eq_left hx_gt.le] at hy; exact (hasDerivAt_dphi hy.1).hasDerivWithinAt)
        h_int
      rw [h_sub, dphi_xiStar, sub_zero]
    rw [h_zero_tail, add_zero, h_left, hFTC]
    field_simp

/-- **`Im ΔΦ_δ(x + i0) = 0` for `|x| < ξ_*`** (`cts:smooth-env` (2)). -/
theorem im_DeltaPhi_real_abs_lt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : |x| < xiStar) :
    (DeltaPhi δ (x : ℂ)).im = 0 := by
  have hint := integrableOn_dphi_phiY_real hδ0 hδ1 x
  unfold DeltaPhi
  rw [show (1 / (π : ℂ)) = (((1 / π : ℝ)) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul]
  have hcomm := Complex.imCLM.integral_comp_comm hint
  simp only [Complex.imCLM_apply] at hcomm
  rw [← hcomm]
  have h0 : ∀ y ∈ Ioi xiStar, (((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)).im = 0 := by
    intro y hy
    have hyx : xiStar < y := hy
    have h1 : -y < x := by linarith [neg_le_abs x, abs_lt.mp hx]
    have h2 : x < y := by linarith [le_abs_self x, abs_lt.mp hx]
    simp [Complex.mul_im, im_phiY_real_of_abs_lt h1 h2]
  rw [setIntegral_eq_zero_of_forall_eq_zero h0, mul_zero]

/-- **`Im ΔΦ_δ(x + i0) = δφ_δ(-x)` for `x < -ξ_*`** (`cts:smooth-env` (2)). -/
theorem im_DeltaPhi_real_lt_neg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : x < -xiStar) :
    (DeltaPhi δ (x : ℂ)).im = dphi δ (-x) := by
  have hint := integrableOn_dphi_phiY_real hδ0 hδ1 x
  have hpi := Real.pi_pos
  have hx_gt : xiStar < -x := by linarith
  have h_im_eq : (DeltaPhi δ (x : ℂ)).im =
      (1 / π) * ∫ y in Ioi xiStar, deriv (dphi δ) y * (phiY y (x : ℂ)).im := by
    unfold DeltaPhi
    rw [show (1 / (π : ℂ)) = (((1 / π : ℝ)) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul]
    congr 1
    have hcomm := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply] at hcomm
    rw [← hcomm]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp [Complex.mul_im]
  rw [h_im_eq]
  have hint_im : IntegrableOn (fun y => deriv (dphi δ) y * (phiY y (x : ℂ)).im) (Ioi xiStar) := by
    have : (fun y => deriv (dphi δ) y * (phiY y (x : ℂ)).im) =
        fun y => (((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (x : ℂ)).im := by
      funext y; simp [Complex.mul_im]
    rw [this]
    exact Complex.imCLM.integrable_comp hint
  have hsplit := setIntegral_union (s := Ioc xiStar (-x)) (t := Ioi (-x))
    Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint_im.mono_set Ioc_subset_Ioi_self)
    (hint_im.mono_set (Ioi_subset_Ioi hx_gt.le))
  rw [Ioc_union_Ioi_eq_Ioi hx_gt.le] at hsplit
  rw [hsplit]
  have h_zero_tail : ∫ y in Ioi (-x), deriv (dphi δ) y * (phiY y (x : ℂ)).im = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hyx : -x < y := hy
    have h1 : -y < x := by linarith
    have h2 : x < y := by have := xiStar_pos; linarith
    rw [im_phiY_real_of_abs_lt h1 h2, mul_zero]
  have h_left : ∫ y in Ioc xiStar (-x), deriv (dphi δ) y * (phiY y (x : ℂ)).im =
      π * ∫ y in Ioc xiStar (-x), deriv (dphi δ) y := by
    rw [← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hne : ∀ᵐ y, y ∈ Ioc xiStar (-x) → y ≠ -x := by
      rw [← ae_restrict_iff' measurableSet_Ioc, ae_iff]
      exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-x))
    filter_upwards [hne] with y hny hy
    have hy_pos : 0 < y := lt_trans xiStar_pos hy.1
    have hy_lt : x < -y := by
      have : y < -x := lt_of_le_of_ne hy.2 (hny hy)
      linarith
    rw [im_phiY_real_of_lt_neg hy_pos hy_lt, mul_comm]
  have hFTC : ∫ y in Ioc xiStar (-x), deriv (dphi δ) y = dphi δ (-x) := by
    rw [← intervalIntegral.integral_of_le hx_gt.le]
    have h_int : IntervalIntegrable (deriv (dphi δ)) volume xiStar (-x) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx_gt.le).mpr
        ((integrableOn_dphi_deriv hδ0 hδ1).mono_set Ioc_subset_Ioi_self)
    have h_sub := intervalIntegral.integral_eq_sub_of_hasDeriv_right
      ((continuousOn_dphi δ).mono (by rw [uIcc_of_le hx_gt.le]; exact Icc_subset_Ici_self))
      (fun y hy => by rw [min_eq_left hx_gt.le] at hy; exact (hasDerivAt_dphi hy.1).hasDerivWithinAt)
      h_int
    rw [h_sub, dphi_xiStar, sub_zero]
  rw [h_zero_tail, add_zero, h_left, hFTC]
  field_simp

/-- **`Re ΔΦ_δ(x + i0)` as an ordinary Lebesgue integral** (`cts:smooth-env` (2)):
equals `(1/π) ∫_{ξ_*}^∞ δφ_δ'(y) log |tanh(π(x-y)/2) tanh(π(x+y)/2)| dy` (hence also its principal value). -/
theorem re_DeltaPhi_real {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (x : ℝ) :
    (DeltaPhi δ (x : ℂ)).re =
      (1 / π) * ∫ y in Ioi xiStar, deriv (dphi δ) y * Real.log |Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2)| := by
  have hint := integrableOn_dphi_phiY_real hδ0 hδ1 x
  unfold DeltaPhi
  rw [show (1 / (π : ℂ)) = (((1 / π : ℝ)) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  congr 1
  have hcomm := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hcomm
  rw [← hcomm]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  have hne1 : ∀ᵐ y, y ∈ Ioi xiStar → y ≠ x := by
    rw [← ae_restrict_iff' measurableSet_Ioi, ae_iff]
    exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton x)
  have hne2 : ∀ᵐ y, y ∈ Ioi xiStar → y ≠ -x := by
    rw [← ae_restrict_iff' measurableSet_Ioi, ae_iff]
    exact measure_mono_null (fun y hy => by simpa using hy) (measure_singleton (-x))
  filter_upwards [hne1, hne2] with y hy1 hy2 hy
  simp [Complex.mul_re, re_phiY_real (hy1 hy).symm (by intro h; apply hy2 hy; linarith)]


/-! ### 4. Boundary limits of `ζ_D(b)` as `Im b → 0+` -/

/-- `ζ_D` on `(-ξ_*, ξ_*)`: `√((√2 - cosh πx)/(√2 + cosh πx)) ∈ (0, 1)`. -/
noncomputable def zetaDReal (x : ℝ) : ℝ :=
  √((√2 - Real.cosh (π * x)) / (√2 + Real.cosh (π * x)))

private lemma cosh_lt_sqrt_two_of_abs_lt {x : ℝ} (hx : |x| < xiStar) :
    Real.cosh (π * x) < √2 := by
  rw [← cosh_pi_xiStar, Real.cosh_lt_cosh]
  have hpi := Real.pi_pos
  rw [abs_mul, abs_of_pos hpi, abs_of_pos (mul_pos hpi xiStar_pos)]
  exact mul_lt_mul_of_pos_left hx hpi

private lemma sqrt_two_lt_cosh_of_gt {x : ℝ} (hx : xiStar < x) :
    √2 < Real.cosh (π * x) := by
  rw [← cosh_pi_xiStar, Real.cosh_lt_cosh]
  have hpi := Real.pi_pos
  rw [abs_of_pos (mul_pos hpi (lt_trans xiStar_pos hx)), abs_of_pos (mul_pos hpi xiStar_pos)]
  exact mul_lt_mul_of_pos_left hx hpi

lemma zetaDReal_mem {x : ℝ} (hx : |x| < xiStar) : zetaDReal x ∈ Ioo (0 : ℝ) 1 := by
  have hc := cosh_lt_sqrt_two_of_abs_lt hx
  have hc0 : 0 < Real.cosh (π * x) := Real.cosh_pos _
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  unfold zetaDReal
  constructor
  · exact Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    linarith

/-- `ζ_D(b) ∈ halfDisc` for `0 < Im b < 1/2`. -/
lemma zetaD_mem_halfDisc {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) : zetaD b ∈ halfDisc := by
  have hpi := Real.pi_pos
  set c := Complex.cosh ((π : ℂ) * b) with hcdef
  have hcre : 0 < c.re := by
    rw [hcdef, re_cosh']
    have hch : 0 < Real.cosh ((π : ℂ) * b).re := Real.cosh_pos _
    have hcos : 0 < Real.cos ((π : ℂ) * b).im := by
      apply Real.cos_pos_of_mem_Ioo
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact ⟨by nlinarith, by nlinarith⟩
    exact mul_pos hch hcos
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (√2 : ℂ) + c ≠ 0 := by
    intro h
    have : ((√2 : ℂ) + c).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  set w := ((√2 : ℂ) - c) / ((√2 : ℂ) + c) with hwdef
  have hwnorm : ‖w‖ < 1 := by
    rw [hwdef, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  have hwne : w ≠ 0 := by
    intro h
    have hnum : (√2 : ℂ) - c = 0 := (div_eq_zero_iff.mp h).resolve_right hden
    have hc_eq : c = (√2 : ℂ) := by linear_combination -hnum
    have him : c.im = 0 := by rw [hc_eq]; simp
    have hsin : Real.sin (π * b.im) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)).ne'
    rw [hcdef, im_cosh'] at him
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero] at him
    have hsh : Real.sinh (π * b.re) = 0 := (mul_eq_zero.mp him).resolve_right hsin
    have hbre : b.re = 0 := by
      have := Real.sinh_eq_zero.mp hsh
      exact (mul_eq_zero.mp this).resolve_left Real.pi_ne_zero
    have hb_eq : ((b.im : ℂ) * Complex.I) = b := by apply Complex.ext <;> simp [hbre]
    have hre_eq : (Complex.cosh ((π : ℂ) * ((b.im : ℂ) * Complex.I))).re = √2 := by
      rw [hb_eq, ← hcdef, hc_eq]; simp
    rw [show (π : ℂ) * ((b.im : ℂ) * Complex.I) = ((π * b.im : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cosh_mul_I, ← Complex.ofReal_cos, Complex.ofReal_re] at hre_eq
    have : Real.cos (π * b.im) ≤ 1 := Real.cos_le_one _
    have : 1 < √2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  have hzeta_norm : ‖zetaD b‖ < 1 := by
    unfold zetaD
    rw [← hwdef, Complex.cpow_def_of_ne_zero hwne, Complex.norm_exp, Complex.mul_re, Complex.log_re]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im,
      Complex.im_ofNat, neg_zero, zero_div, mul_zero, sub_zero, Complex.log_im]
    norm_num
    exact mul_neg_of_neg_of_pos (Real.log_neg (norm_pos_iff.mpr hwne) hwnorm) (by norm_num)
  have hw_slit : w ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hre0 : b.re = 0
    · left
      have hcos : Real.cos (π * b.im) < 1 := by
        rw [← Real.cos_zero]
        exact Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩ ⟨by positivity, by nlinarith⟩ (by positivity)
      have hc_eq : c = ((Real.cos (π * b.im) : ℝ) : ℂ) := by
        have hb_eq : ((b.im : ℂ) * Complex.I) = b := by apply Complex.ext <;> simp [hre0]
        rw [hcdef, ← hb_eq, show (π : ℂ) * ((b.im : ℂ) * Complex.I) = ((π * b.im : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.cosh_mul_I, ← Complex.ofReal_cos]
        simp
      rw [hwdef, hc_eq, ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
      have h1 : 1 < √2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
      exact div_pos (by linarith) (by linarith [Real.cos_pos_of_mem_Ioo (⟨by nlinarith, by nlinarith⟩ : π * b.im ∈ Ioo (-(π/2)) (π/2))])
    · right
      have him_c : c.im ≠ 0 := by
        rw [hcdef, im_cosh']
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.mul_im, add_zero]
        exact mul_ne_zero (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hre0))
          (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)).ne'
      rw [hwdef, Complex.div_im]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_sub, zero_add]
      have hn : 0 < Complex.normSq ((√2 : ℂ) + c) := Complex.normSq_pos.mpr hden
      rw [Complex.normSq_apply] at hn
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, zero_add] at hn
      intro h0
      rw [← sub_div] at h0
      have hnum : -c.im * (√2 + c.re) - (√2 - c.re) * c.im = 0 :=
        (div_eq_zero_iff.mp h0).resolve_right (by rw [Complex.normSq_apply]; simp only [Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_add]; linarith)
      have : -2 * √2 * c.im = 0 := by linarith
      have : c.im = 0 := by nlinarith
      exact him_c this
  have hre_pos : 0 < (zetaD b).re := by
    unfold zetaD
    rw [← hwdef, Complex.cpow_def_of_ne_zero hwne, Complex.exp_re, Complex.mul_re, Complex.log_re, Complex.log_im]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im, Complex.im_ofNat,
      neg_zero, zero_div, mul_zero, sub_zero]
    norm_num
    have harg_ne : Complex.arg w ≠ π := (Complex.mem_slitPlane_iff_arg.mp hw_slit).1
    have harg1 : -π < Complex.arg w := Complex.neg_pi_lt_arg w
    have harg2 : Complex.arg w < π := lt_of_le_of_ne (Complex.arg_le_pi w) harg_ne
    have hcos : 0 < Real.cos (Complex.arg w * (1 / 2)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith
    have hexp : 0 < Real.exp (Real.log ‖w‖ * (1 / 2)) := Real.exp_pos _
    rw [Complex.log_im]
    exact mul_pos hexp hcos
  exact ⟨hzeta_norm, hre_pos⟩

private lemma tendsto_zetaD_w {x : ℝ} :
    Tendsto (fun b : ℂ => ((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b)))
      (𝓝[upperHalf] (x : ℂ))
      (𝓝 (((√2 - Real.cosh (π * x)) / (√2 + Real.cosh (π * x)) : ℝ) : ℂ)) := by
  have hden : (√2 : ℂ) + Complex.cosh ((π : ℂ) * (x : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by have := Real.cosh_pos (π * x); have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2); linarith)
  have hc : ContinuousAt (fun b : ℂ => ((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))) (x : ℂ) :=
    (continuousAt_const.sub (Complex.continuous_cosh.continuousAt.comp (by fun_prop))).div
      (continuousAt_const.add (Complex.continuous_cosh.continuousAt.comp (by fun_prop))) hden
  have heq : ((√2 : ℂ) - Complex.cosh ((π : ℂ) * (x : ℂ))) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * (x : ℂ))) =
      (((√2 - Real.cosh (π * x)) / (√2 + Real.cosh (π * x)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]; push_cast; rfl
  rw [← heq]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- **`ζ_D(b) → -i y(x)` for `x > ξ_*`** as `Im b → 0+`. -/
theorem tendsto_zetaD_slit {x : ℝ} (hx : xiStar < x) :
    Tendsto zetaD (𝓝[upperHalf] (x : ℂ)) (𝓝 (-Complex.I * (yOfX x : ℂ))) := by
  have hpi := Real.pi_pos
  have hc := sqrt_two_lt_cosh_of_gt hx
  have hc0 : 0 < Real.cosh (π * x) := Real.cosh_pos _
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hy_pos : 0 < yOfX x := Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  set r : ℝ := (Real.cosh (π * x) - √2) / (√2 + Real.cosh (π * x)) with hrdef
  have hr_pos : 0 < r := div_pos (by linarith) (by linarith)
  have hr_sq : √r = yOfX x := by
    unfold yOfX; rw [hrdef, add_comm (Real.cosh (π * x)) √2]
  have hw_lim : Tendsto (fun b : ℂ => -(((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))))
      (𝓝[upperHalf] (x : ℂ)) (𝓝 (r : ℂ)) := by
    have heq : -(((√2 - Real.cosh (π * x)) / (√2 + Real.cosh (π * x)) : ℝ) : ℂ) = (r : ℂ) := by
      rw [← Complex.ofReal_neg, hrdef]; congr 1; ring
    rw [← heq]
    exact (tendsto_zetaD_w (x := x)).neg
  have h_norm : Tendsto (fun b : ℂ => ‖((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))‖)
      (𝓝[upperHalf] (x : ℂ)) (𝓝 r) := by
    have := hw_lim.norm
    simpa [norm_neg, Complex.norm_real, abs_of_pos hr_pos] using this
  have h_arg : Tendsto (fun b : ℂ => Complex.arg (((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))))
      (𝓝[upperHalf] (x : ℂ)) (𝓝 (-π)) := by
    have hslit : (r : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hr_pos
    have h1 : Tendsto (fun b : ℂ => Complex.arg (-(((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b)))) - π)
        (𝓝[upperHalf] (x : ℂ)) (𝓝 (Complex.arg (r : ℂ) - π)) :=
      ((Complex.continuousAt_arg hslit).tendsto.comp hw_lim).sub_const π
    rw [Complex.arg_ofReal_of_nonneg hr_pos.le, zero_sub] at h1
    refine h1.congr' ?_
    have hev_re : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), 0 < b.re :=
      nhdsWithin_le_nhds ((Complex.continuous_re.tendsto (x : ℂ)).eventually (lt_mem_nhds (by simpa using lt_trans xiStar_pos hx)))
    filter_upwards [hev_imStrip_of_upperHalf x, hev_re] with b hb hbre
    have him_c : 0 < (Complex.cosh ((π : ℂ) * b)).im := by
      rw [im_cosh']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero]
      exact mul_pos (Real.sinh_pos_iff.mpr (mul_pos hpi hbre))
        (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hb.1) (by nlinarith [hb.2]))
    have hden : (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 := by
      intro h
      have : ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)).im = 0 := by rw [h]; simp
      simp at this; linarith
    have him_neg : (((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))).im < 0 := by
      rw [Complex.div_im]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_sub, zero_add]
      have hn : 0 < Complex.normSq ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) := Complex.normSq_pos.mpr hden
      have hnum : -(Complex.cosh ((π : ℂ) * b)).im * (√2 + (Complex.cosh ((π : ℂ) * b)).re) -
          (√2 - (Complex.cosh ((π : ℂ) * b)).re) * (Complex.cosh ((π : ℂ) * b)).im =
          -(2 * √2 * (Complex.cosh ((π : ℂ) * b)).im) := by ring
      rw [← sub_div, hnum]
      exact div_neg_of_neg_of_pos (by nlinarith) hn
    have := Complex.arg_neg_eq_arg_add_pi_of_im_neg him_neg
    linarith
  have h_cpow : Tendsto (fun b : ℂ =>
      ((‖((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp ((Complex.arg (((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))) * (1 / 2 : ℝ) : ℝ) * Complex.I))
      (𝓝[upperHalf] (x : ℂ))
      (𝓝 (((r ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp ((((-π) * (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I))) := by
    refine Tendsto.mul ?_ ?_
    · exact Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((continuousAt_id.rpow_const (Or.inl hr_pos.ne')).tendsto.comp h_norm)
    · exact Complex.continuous_exp.continuousAt.tendsto.comp
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp (h_arg.mul_const (1 / 2))).mul tendsto_const_nhds)
  have h_target : (((r ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp ((((-π) * (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I)) =
      -Complex.I * (yOfX x : ℂ) := by
    rw [← Real.sqrt_eq_rpow, hr_sq]
    have hexp : Complex.exp ((((-π) * (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
      rw [show ((-π) * (1 / 2 : ℝ) : ℝ) = -(π / 2) by ring, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_ofNat, neg_mul, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]
    rw [hexp]; ring
  rw [h_target] at h_cpow
  refine h_cpow.congr' ?_
  have hev_ne : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ),
      ((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b)) ≠ 0 := by
    filter_upwards [hw_lim.eventually (isOpen_ne.mem_nhds (Complex.ofReal_ne_zero.mpr hr_pos.ne'))] with b hb
    exact neg_ne_zero.mp hb
  filter_upwards [hev_ne] with b hb
  unfold zetaD
  rw [Complex.cpow_def_of_ne_zero hb]
  have hlog : Complex.log (((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))) * (1 / 2 : ℂ) =
      ((Real.log ‖((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))‖ * (1 / 2 : ℝ) : ℝ) : ℂ) +
      ((Complex.arg (((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))) * (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    set z := ((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))
    conv_lhs => rw [← Complex.re_add_im (Complex.log z), Complex.log_re, Complex.log_im]
    push_cast; ring
  rw [hlog, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos (norm_pos_iff.mpr hb)]

/-- **`ζ_D(b) → 0` at `x = ξ_*`** as `Im b → 0+`. -/
theorem tendsto_zetaD_xiStar :
    Tendsto zetaD (𝓝[upperHalf] (xiStar : ℂ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hw0 : Tendsto (fun b : ℂ => ‖((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))‖)
      (𝓝[upperHalf] (xiStar : ℂ)) (𝓝 0) := by
    have h1 := (tendsto_zetaD_w (x := xiStar)).norm
    have h0 : ((√2 - Real.cosh (π * xiStar)) / (√2 + Real.cosh (π * xiStar)) : ℝ) = 0 := by
      rw [cosh_pi_xiStar, sub_self, zero_div]
    rw [h0] at h1
    simpa using h1
  have hpow : Tendsto (fun b : ℂ =>
      ‖((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b))‖ ^ (1 / 2 : ℝ))
      (𝓝[upperHalf] (xiStar : ℂ)) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => r ^ (1 / 2 : ℝ)) :=
      continuous_id.rpow_const (fun _ => Or.inr (by norm_num))
    have h0' : ((0 : ℝ) ^ (1 / 2 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
    have hcomp := (hc.tendsto 0).comp hw0
    rw [h0'] at hcomp
    exact hcomp
  refine hpow.congr' ?_
  filter_upwards with b
  unfold zetaD
  by_cases hb : ((√2 : ℂ) - Complex.cosh (π * b)) / ((√2 : ℂ) + Complex.cosh (π * b)) = 0
  · rw [hb, Complex.zero_cpow (by norm_num), norm_zero, Real.zero_rpow (by norm_num)]
  · rw [Complex.cpow_def_of_ne_zero hb, Complex.norm_exp, Complex.mul_re, Complex.log_re]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im,
      Complex.im_ofNat, neg_zero, zero_div, mul_zero, sub_zero, Complex.log_im]
    norm_num
    rw [← norm_div, Real.rpow_def_of_pos (norm_pos_iff.mpr hb)]

/-- **`ζ_D(b) → ζ_D(x)` for `|x| < ξ_*`** as `Im b → 0+`. -/
theorem tendsto_zetaD_real {x : ℝ} (hx : |x| < xiStar) :
    Tendsto zetaD (𝓝[upperHalf] (x : ℂ)) (𝓝 (zetaDReal x : ℂ)) := by
  have hmem := zetaDReal_mem hx
  have hc := cosh_lt_sqrt_two_of_abs_lt hx
  have hc0 : 0 < Real.cosh (π * x) := Real.cosh_pos _
  set r : ℝ := (√2 - Real.cosh (π * x)) / (√2 + Real.cosh (π * x)) with hrdef
  have hr_pos : 0 < r := div_pos (by linarith) (by linarith)
  have hslit : (r : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hr_pos
  have hcpow : ContinuousAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) (r : ℂ) :=
    ((hasDerivAt_id (r : ℂ)).cpow_const hslit).continuousAt
  have hlim : Tendsto zetaD (𝓝[upperHalf] (x : ℂ)) (𝓝 ((r : ℂ) ^ (1 / 2 : ℂ))) :=
    hcpow.tendsto.comp (tendsto_zetaD_w (x := x))
  have heq : (r : ℂ) ^ (1 / 2 : ℂ) = (zetaDReal x : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hr_pos.le]
    simp [zetaDReal, hrdef, Real.sqrt_eq_rpow]
  rwa [heq] at hlim


/-! ### 5. Boundary limit of `ℰ_δ` and the modulus identity (`cts:smooth-env` (2)) -/

/-- Boundary value of `ℰ_δ` on `ℝ`: `lim_{Im b → 0+} Estripped δ b`. -/
noncomputable def EeBdry (δ x : ℝ) : ℂ := limUnder (𝓝[upperHalf] (x : ℂ)) (Estripped δ)

private lemma fDelta_slit_conj {δ x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hx : xiStar < x) :
    fDelta Gout δ (-Complex.I * (yOfX x : ℂ)) = starRingEnd ℂ (fDelta Gout δ (Complex.I * (yOfX x : ℂ))) := by
  have hy := yOfX_mem hx
  have h1 : Complex.I * (yOfX x : ℂ) ∈ closure halfDisc \ singPts := slit_mem_diff hy
  have h2 : -Complex.I * (yOfX x : ℂ) ∈ closure halfDisc \ singPts := by
    refine ⟨mem_closure_halfDisc (by simp [abs_of_pos hy.1]; exact hy.2.le) (by simp), ?_⟩
    rw [mem_singPts_iff]
    intro h
    rcases h with h | h | h
    · have : (-Complex.I * (yOfX x : ℂ)).im = Complex.I.im := by rw [h]
      simp at this; linarith [hy.1, hy.2]
    · have : (-Complex.I * (yOfX x : ℂ)).im = (-Complex.I).im := by rw [h]
      simp at this; linarith [hy.1, hy.2]
    · have : (-Complex.I * (yOfX x : ℂ)).re = (1 : ℂ).re := by rw [h]
      simp at this
  have hcont := (fDelta_hAdm gout_outerDatum_g1Out hδ0 hδ1).cont
  have hlim1 : Tendsto (fun t : ℝ => fDelta Gout δ ((t : ℂ) + Complex.I * (yOfX x : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (fDelta Gout δ (Complex.I * (yOfX x : ℂ)))) := by
    refine (hcont _ h1).tendsto.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((Complex.continuous_ofReal.tendsto 0).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · have ht_small : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < √(1 - yOfX x ^ 2) :=
        nhdsWithin_le_nhds (gt_mem_nhds (Real.sqrt_pos.mpr (by nlinarith [hy.1, hy.2])))
      filter_upwards [self_mem_nhdsWithin, ht_small] with t ht0 ht1
      have hmem : ((t : ℂ) + Complex.I * (yOfX x : ℂ)) ∈ halfDisc := by
        refine ⟨?_, by simp; exact ht0⟩
        rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, one_pow, Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
          Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, one_mul, zero_add]
        have : t ^ 2 < 1 - yOfX x ^ 2 := by
          have := pow_lt_pow_left₀ ht1 ht0.le (by norm_num : 2 ≠ 0)
          rwa [Real.sq_sqrt (by nlinarith [hy.1, hy.2])] at this
        linarith
      exact ⟨subset_closure hmem, not_mem_singPts_of_halfDisc hmem⟩
  have hlim2 : Tendsto (fun t : ℝ => starRingEnd ℂ (fDelta Gout δ ((t : ℂ) + Complex.I * (yOfX x : ℂ)))) (𝓝[>] (0 : ℝ))
      (𝓝 (starRingEnd ℂ (fDelta Gout δ (Complex.I * (yOfX x : ℂ))))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp hlim1
  have hlim3 : Tendsto (fun t : ℝ => fDelta Gout δ ((t : ℂ) - Complex.I * (yOfX x : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (fDelta Gout δ (-Complex.I * (yOfX x : ℂ)))) := by
    refine (hcont _ h2).tendsto.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (t : ℂ) - Complex.I * (yOfX x : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (-Complex.I * (yOfX x : ℂ))) := by
        simpa [sub_eq_add_neg, neg_mul] using (Complex.continuous_ofReal.tendsto 0).sub tendsto_const_nhds
      exact this.mono_left nhdsWithin_le_nhds
    · have ht_small : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < √(1 - yOfX x ^ 2) :=
        nhdsWithin_le_nhds (gt_mem_nhds (Real.sqrt_pos.mpr (by nlinarith [hy.1, hy.2])))
      filter_upwards [self_mem_nhdsWithin, ht_small] with t ht0 ht1
      have ht0' : 0 < t := mem_Ioi.mp ht0
      have hmem : ((t : ℂ) - Complex.I * (yOfX x : ℂ)) ∈ halfDisc := by
        refine ⟨?_, by simp; exact ht0'⟩
        rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, one_pow, Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_im, Complex.mul_im, one_mul, zero_add]
        have : t ^ 2 < 1 - yOfX x ^ 2 := by
          have := pow_lt_pow_left₀ ht1 ht0'.le (by norm_num : 2 ≠ 0)
          rwa [Real.sq_sqrt (by nlinarith [hy.1, hy.2])] at this
        linarith
      exact ⟨subset_closure hmem, not_mem_singPts_of_halfDisc hmem⟩
  refine tendsto_nhds_unique hlim3 ?_
  refine hlim2.congr' ?_
  have ht_small : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < √(1 - yOfX x ^ 2) :=
    nhdsWithin_le_nhds (gt_mem_nhds (Real.sqrt_pos.mpr (by nlinarith [hy.1, hy.2])))
  filter_upwards [self_mem_nhdsWithin, ht_small] with t ht0 ht1
  have ht0' : 0 < t := mem_Ioi.mp ht0
  have hmem : ((t : ℂ) + Complex.I * (yOfX x : ℂ)) ∈ halfDisc := by
    refine ⟨?_, by simp; exact ht0'⟩
    rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, one_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, one_mul, zero_add]
    have : t ^ 2 < 1 - yOfX x ^ 2 := by
      have := pow_lt_pow_left₀ ht1 ht0'.le (by norm_num : 2 ≠ 0)
      rwa [Real.sq_sqrt (by nlinarith [hy.1, hy.2])] at this
    linarith
  have hc := fDelta_conj gout_outerDatum_g1Out hδ0 (by linarith) hmem
  have hconj : starRingEnd ℂ ((t : ℂ) + Complex.I * (yOfX x : ℂ)) = (t : ℂ) - Complex.I * (yOfX x : ℂ) := by
    simp [Complex.conj_ofReal]; ring
  rw [hconj] at hc
  exact hc.symm

private lemma hev_zetaD_mem_halfDisc (x : ℝ) :
    ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), zetaD b ∈ closure halfDisc \ singPts := by
  have h1 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), 0 < b.im := self_mem_nhdsWithin
  have h2 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.im < 1 / 2 :=
    nhdsWithin_le_nhds ((Complex.continuous_im.tendsto (x : ℂ)).eventually (gt_mem_nhds (by simp : (x : ℂ).im < 1 / 2)))
  filter_upwards [h1, h2] with b hb0 hb1
  have hm := zetaD_mem_halfDisc hb0 hb1
  exact ⟨subset_closure hm, not_mem_singPts_of_halfDisc hm⟩

/-- **`ℰ_δ(b)` boundary limit for `x > ξ_*`** (`cts:smooth-env` (2)):
the phases cancel, leaving the positive real limit `‖F_δ(i y(x))‖ e^{-Re ΔΦ_δ(x)}`. -/
theorem tendsto_Estripped_real_gt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : xiStar < x) :
    Tendsto (Estripped δ) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (((‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ * Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℝ) : ℂ))) := by
  have hy := yOfX_mem hx
  have h2 : -Complex.I * (yOfX x : ℂ) ∈ closure halfDisc \ singPts := by
    refine ⟨mem_closure_halfDisc (by simp [abs_of_pos hy.1]; exact hy.2.le) (by simp), ?_⟩
    rw [mem_singPts_iff]
    intro h
    rcases h with h | h | h
    · have : (-Complex.I * (yOfX x : ℂ)).im = Complex.I.im := by rw [h]
      simp at this; linarith [hy.1, hy.2]
    · have : (-Complex.I * (yOfX x : ℂ)).im = (-Complex.I).im := by rw [h]
      simp at this; linarith [hy.1, hy.2]
    · have : (-Complex.I * (yOfX x : ℂ)).re = (1 : ℂ).re := by rw [h]
      simp at this
  have hcont := (fDelta_hAdm gout_outerDatum_g1Out hδ0 (by linarith)).cont
  have hf_lim : Tendsto (fun b => fDelta Gout δ (zetaD b)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (fDelta Gout δ (-Complex.I * (yOfX x : ℂ)))) := by
    refine (hcont _ h2).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨tendsto_zetaD_slit hx, hev_zetaD_mem_halfDisc x⟩)
  have hexp_lim : Tendsto (fun b => Complex.exp (-DeltaPhi δ b)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (Complex.exp (-DeltaPhi δ (x : ℂ)))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_DeltaPhi_real hδ0 hδ1 x).neg
  have hmul := hf_lim.mul hexp_lim
  obtain ⟨ρ, hρ0, hρeq⟩ := fDelta_slit_dphi (δ := δ) hx
  have hnorm_eq : ‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ = ρ := by
    rw [hρeq, norm_mul, Complex.norm_real, Complex.norm_exp_I_mul_ofReal, mul_one, Real.norm_eq_abs, abs_of_pos hρ0]
  have hf_conj := fDelta_slit_conj hδ0 (by linarith) hx
  rw [hρeq] at hf_conj
  have h_star : starRingEnd ℂ ((ρ : ℂ) * Complex.exp (Complex.I * (dphi δ x : ℂ))) =
      (ρ : ℂ) * Complex.exp (-Complex.I * (dphi δ x : ℂ)) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    simp [Complex.conj_ofReal]
  rw [h_star] at hf_conj
  have h_delta : -DeltaPhi δ (x : ℂ) =
      ((-(DeltaPhi δ (x : ℂ)).re : ℝ) : ℂ) + ((dphi δ x : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp [im_DeltaPhi_real_ge hδ0 hδ1 hx.le]
  have h_prod : fDelta Gout δ (-Complex.I * (yOfX x : ℂ)) * Complex.exp (-DeltaPhi δ (x : ℂ)) =
      (((‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ * Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℝ) : ℂ)) := by
    rw [hf_conj, h_delta, hnorm_eq, Complex.exp_add, ← Complex.ofReal_exp]
    have : (ρ : ℂ) * Complex.exp (-Complex.I * (dphi δ x : ℂ)) *
        ((Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℂ) * Complex.exp ((dphi δ x : ℂ) * Complex.I)) =
        (ρ : ℂ) * (Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℂ) *
        (Complex.exp (-Complex.I * (dphi δ x : ℂ)) * Complex.exp ((dphi δ x : ℂ) * Complex.I)) := by ring
    rw [this, ← Complex.exp_add, show -Complex.I * (dphi δ x : ℂ) + (dphi δ x : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero, mul_one]
    push_cast; rfl
  rw [h_prod] at hmul
  exact hmul

/-- **`ℰ_δ(b)` boundary limit at `x = ξ_*`** (`cts:smooth-env` (2)). -/
theorem tendsto_Estripped_real_xiStar {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    Tendsto (Estripped δ) (𝓝[upperHalf] (xiStar : ℂ))
      (𝓝 (((‖fDelta Gout δ (Complex.I * (yOfX xiStar : ℂ))‖ * Real.exp (-(DeltaPhi δ (xiStar : ℂ)).re) : ℝ) : ℂ))) := by
  have h0 : (0 : ℂ) ∈ closure halfDisc \ singPts := by
    refine ⟨mem_closure_halfDisc (by simp) (by simp), ?_⟩
    rw [mem_singPts_iff]; norm_num [Complex.ext_iff]
  have hcont := (fDelta_hAdm gout_outerDatum_g1Out hδ0 (by linarith)).cont
  have hf_lim : Tendsto (fun b => fDelta Gout δ (zetaD b)) (𝓝[upperHalf] (xiStar : ℂ))
      (𝓝 (fDelta Gout δ 0)) :=
    (hcont _ h0).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨tendsto_zetaD_xiStar, hev_zetaD_mem_halfDisc xiStar⟩)
  have hexp_lim : Tendsto (fun b => Complex.exp (-DeltaPhi δ b)) (𝓝[upperHalf] (xiStar : ℂ))
      (𝓝 (Complex.exp (-DeltaPhi δ (xiStar : ℂ)))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_DeltaPhi_real hδ0 hδ1 xiStar).neg
  have hmul := hf_lim.mul hexp_lim
  have hf0 : fDelta Gout δ 0 = 1 := fDelta_zero gout_outerDatum_g1Out hδ0 (by linarith)
  have hy0 : Complex.I * (yOfX xiStar : ℂ) = 0 := by rw [yOfX_xiStar]; simp
  have him0 : (DeltaPhi δ (xiStar : ℂ)).im = 0 := by
    rw [im_DeltaPhi_real_ge hδ0 hδ1 le_rfl, dphi_xiStar, neg_zero]
  have h_delta : -DeltaPhi δ (xiStar : ℂ) = ((-(DeltaPhi δ (xiStar : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  have h_prod : fDelta Gout δ 0 * Complex.exp (-DeltaPhi δ (xiStar : ℂ)) =
      (((‖fDelta Gout δ (Complex.I * (yOfX xiStar : ℂ))‖ * Real.exp (-(DeltaPhi δ (xiStar : ℂ)).re) : ℝ) : ℂ)) := by
    rw [hy0, hf0, one_mul, norm_one, one_mul, h_delta, ← Complex.ofReal_exp]
  rw [h_prod] at hmul
  exact hmul

/-- **`EeBdry` modulus identity on `x ≥ ξ_*`** (`cts:smooth-env` (2), `OuterS3` last-but-one conjunct):
`‖EeBdry δ x‖ * exp(Re ΔΦ_δ(x)) = ‖F_δ(i y(x))‖`. -/
theorem EeBdry_modulus_identity {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : xiStar ≤ x) :
    0 < (EeBdry δ x).re ∧ (EeBdry δ x).im = 0 ∧
    ‖EeBdry δ x‖ * Real.exp (DeltaPhi δ (x : ℂ)).re = ‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ := by
  have hlim : Tendsto (Estripped δ) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (((‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ * Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℝ) : ℂ))) := by
    rcases eq_or_lt_of_le hx with rfl | hx_gt
    · exact tendsto_Estripped_real_xiStar hδ0 hδ1
    · exact tendsto_Estripped_real_gt hδ0 hδ1 hx_gt
  have hEe : EeBdry δ x =
      (((‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ * Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℝ) : ℂ)) := by
    have : NeBot (𝓝[upperHalf] (x : ℂ)) := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [Metric.mem_closure_iff]
      intro ε hε
      exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
        by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩
    exact hlim.limUnder_eq
  rw [hEe]
  have hnorm_pos : 0 < ‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ := by
    rcases eq_or_lt_of_le hx with rfl | hx_gt
    · rw [yOfX_xiStar, Complex.ofReal_zero, mul_zero, fDelta_zero gout_outerDatum_g1Out hδ0 (by linarith), norm_one]
      norm_num
    · obtain ⟨ρ, hρ0, hρeq⟩ := fDelta_slit_dphi (δ := δ) hx_gt
      rw [hρeq, norm_mul, Complex.norm_real, Complex.norm_exp_I_mul_ofReal, mul_one, Real.norm_eq_abs, abs_of_pos hρ0]
      exact hρ0
  have hexp_pos : 0 < Real.exp (-(DeltaPhi δ (x : ℂ)).re) := Real.exp_pos _
  refine ⟨by rw [Complex.ofReal_re]; exact mul_pos hnorm_pos hexp_pos, by rw [Complex.ofReal_im], ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hnorm_pos hexp_pos),
    mul_assoc, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne', mul_one]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.tendsto_DeltaPhi_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_DeltaPhi_real

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.im_DeltaPhi_real_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms im_DeltaPhi_real_ge

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.im_DeltaPhi_real_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms im_DeltaPhi_real_abs_lt

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.re_DeltaPhi_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_DeltaPhi_real

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeBdry_modulus_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EeBdry_modulus_identity

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
