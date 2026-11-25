module

public import FormalResearch.SignUncertainty.CtOuterPoisson

/-!
# Holomorphic continuation of `h` across the edge `Re ζ = 0` (`ct:outer` (1)-(2))

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (2) ("analytic
continuation at `0`") and the boundary behaviour of `h` used in (1).  **Proved.**

With `w = -iζ`, the kernel is `1/sin(π(ζ - it)) = i (1/(π(t - w)) + κ(t - w))` with `κ` holomorphic on `|s| < 1`.
If `u_r` extends holomorphically to a ball `B(y₀, R)`, then for `δ < R`, `δ ≤ 1/2`, the integral over `|t - y₀| ≤ δ`
splits into the holomorphic pieces `∫ (v(t) - v(w))/(t - w) dt`, `∫ v κ(t - w) dt` and the Cauchy part
`v(w) ∫_{y₀-δ}^{y₀+δ} dt/(t - w)`, whose analytic form is `Log(y₀+δ - w) - Log(w - y₀ + δ) - iπ` for `Im w < 0`
(i.e. `Re ζ > 0`).  The far part is holomorphic for `|Im ζ - y₀| < δ`.  Hence `h` coincides on `S ∩ B(i y₀, δ)`
with a function `H` holomorphic on the whole ball `B(i y₀, δ)` (`exists_local_continuation`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- Holomorphy of an interval parameter integral with uniform local bounds. -/
theorem differentiableOn_intervalParam {Φ : ℂ → ℝ → ℂ} {U : Set ℂ} (hU : IsOpen U) {a b : ℝ}
    (hcont : ∀ w ∈ U, ContinuousOn (Φ w) (Icc a b))
    (hdiff : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun w => Φ w t) U)
    (hbd : ∀ w₀ ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ t ∈ Icc a b, ∀ w ∈ ball w₀ r, ‖Φ w t‖ ≤ M) :
    DifferentiableOn ℂ (fun w => ∫ t in Icc a b, Φ w t) U := by
  refine differentiableOn_integral_param (μ := volume.restrict (Icc a b)) hU ?_ ?_ ?_
  · intro w hw
    exact (hcont w hw).aestronglyMeasurable measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hdiff t ht
  · intro w₀ hw₀
    obtain ⟨r, hr, M, hM⟩ := hbd w₀ hw₀
    refine ⟨r, hr, fun _ => M, integrable_const _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht w hw using hM t ht w hw

lemma dslope_symm (f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a := by
  by_cases h : a = b
  · rw [h]
  · rw [dslope_of_ne f (Ne.symm h), dslope_of_ne f h, slope_comm]

/-- Uniform bound for the divided differences of `v` on a closed ball inside its domain. -/
lemma exists_dslope_bound {v : ℂ → ℂ} {c : ℂ} {R δ : ℝ} (hδR : δ < R)
    (hv : DifferentiableOn ℂ v (ball c R)) :
    ∃ M : ℝ, ∀ t ∈ closedBall c δ, ∀ w ∈ closedBall c δ, ‖dslope v t w‖ ≤ M := by
  have hsub : closedBall c δ ⊆ ball c R := closedBall_subset_ball hδR
  have hopen : IsOpen (ball c R) := isOpen_ball
  have hderiv : ContinuousOn (deriv v) (closedBall c δ) :=
    (hv.deriv hopen).continuousOn.mono hsub
  obtain ⟨M, hM⟩ := (isCompact_closedBall c δ).exists_bound_of_continuousOn hderiv
  refine ⟨M, fun t ht w hw => ?_⟩
  by_cases hwt : w = t
  · subst hwt
    rw [dslope_same]
    exact hM w hw
  · rw [dslope_of_ne _ hwt, slope_def_module, norm_smul, norm_inv]
    have h1 : ‖v w - v t‖ ≤ M * ‖w - t‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := v) (C := M)
        (s := closedBall c δ) (fun z hz => ?_) (fun z hz => hM z hz) (convex_closedBall c δ) ht hw
        |> fun h => by simpa [norm_sub_rev] using h
      exact (hv z (hsub hz)).differentiableAt (hopen.mem_nhds (hsub hz))
    have hn : 0 < ‖w - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwt)
    rw [inv_mul_le_iff₀ hn]
    linarith

/-- Cauchy part: `∫_{a}^{b} dt/(t - w) = Log(b - w) - Log(w - a) - iπ` for `Im w < 0`, in a form
holomorphic across `Im w = 0` for `a < Re w < b`. -/
noncomputable def logPart (a b : ℝ) (w : ℂ) : ℂ :=
  Complex.log ((b : ℂ) - w) - Complex.log (w - (a : ℂ)) - Complex.I * π

lemma log_neg_of_im_neg {z : ℂ} (h : z.im < 0) : Complex.log (-z) = Complex.log z + π * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg h]

lemma integral_inv_sub {a b : ℝ} (hab : a ≤ b) {w : ℂ} (hw : w.im < 0) :
    ∫ t in Icc a b, 1 / ((t : ℂ) - w) = logPart a b w := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hslit : ∀ t : ℝ, ((t : ℂ) - w) ∈ slitPlane := fun t =>
    Or.inr (by simp; exact hw.ne)
  have hder : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => Complex.log ((t : ℂ) - w)) (1 / ((t : ℂ) - w)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) - w) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).sub_const w
    exact h1.clog_real (hslit t)
  have hint : IntervalIntegrable (fun t : ℝ => 1 / ((t : ℂ) - w)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun t _ => ?_)
    exact Complex.slitPlane_ne_zero (hslit t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  unfold logPart
  have : Complex.log ((a : ℂ) - w) = Complex.log (w - a) + π * Complex.I := by
    have h2 : (w - (a : ℂ)).im < 0 := by simpa using hw
    have := log_neg_of_im_neg h2
    rw [neg_sub] at this
    exact this
  rw [this]
  ring

lemma differentiableOn_logPart {y₀ δ : ℝ} :
    DifferentiableOn ℂ (logPart (y₀ - δ) (y₀ + δ)) (ball (y₀ : ℂ) δ) := by
  intro w hw
  have hd : ‖w - y₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hw
  have hre : |w.re - y₀| < δ := by
    have := Complex.abs_re_le_norm (w - y₀)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  rw [abs_lt] at hre
  have h1 : ((y₀ + δ : ℝ) : ℂ) - w ∈ slitPlane := Or.inl (by simp; linarith)
  have h2 : w - ((y₀ - δ : ℝ) : ℂ) ∈ slitPlane := Or.inl (by simp; linarith)
  have l1 := (differentiableAt_const ((y₀ + δ : ℝ) : ℂ)).sub differentiableAt_id |>.clog h1
  have l2 := (differentiableAt_id.sub (differentiableAt_const ((y₀ - δ : ℝ) : ℂ))).clog h2
  exact ((l1.sub l2).sub (differentiableAt_const _)).differentiableWithinAt

/-- Far-part kernel bound: if `|Im ζ - t| ≥ m > 0` then `‖1/sin(π(ζ - it))‖ ≤ c_m e^{-π|Im ζ - t|}`. -/
lemma kernel_norm_le_far {ζ : ℂ} (t : ℝ) {m : ℝ} (hm : 0 < m) (h : m ≤ |ζ.im - t|) :
    ‖(Complex.sin (π * (ζ - Complex.I * t)))⁻¹‖ ≤
      2 / (1 - Real.exp (-(2 * π * m))) * Real.exp (-(π * |ζ.im - t|)) := by
  set s : ℝ := |ζ.im - t| with hs
  have hsh : Real.sinh (π * (ζ.im - t)) ^ 2 = Real.sinh (π * s) ^ 2 := by
    rcases abs_cases (ζ.im - t) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hs, h1]
    · rw [hs, h1, mul_neg, Real.sinh_neg, neg_sq]
  have hn : Real.sinh (π * s) ^ 2 ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ ^ 2 := by
    rw [norm_sin_arg_sq, hsh]; nlinarith [sq_nonneg (Real.sin (π * ζ.re))]
  set q : ℝ := Real.exp (-(2 * π * m)) with hqdef
  have hq : 0 < 1 - q := by
    have : q < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
    linarith
  have hexp : Real.exp (-(2 * π * s)) ≤ q :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  set E : ℝ := Real.exp (π * s) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE' : Real.exp (-(π * s)) = E⁻¹ := Real.exp_neg _
  have hsq : Real.exp (-(2 * π * s)) = E⁻¹ ^ 2 := by
    rw [← hE', ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsinh : (1 - q) / 2 * E ≤ Real.sinh (π * s) := by
    rw [Real.sinh_eq, hE']
    have h1 : E⁻¹ ≤ q * E := by
      have : E⁻¹ ^ 2 ≤ q := hsq ▸ hexp
      have e : E⁻¹ = E⁻¹ ^ 2 * E := by field_simp
      calc E⁻¹ = E⁻¹ ^ 2 * E := e
        _ ≤ q * E := mul_le_mul_of_nonneg_right this hEpos.le
    nlinarith
  have hpos : 0 < (1 - q) / 2 * E := by positivity
  have h3 : (1 - q) / 2 * E ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    refine le_trans ?_ hn
    exact pow_le_pow_left₀ hpos.le hsinh 2
  rw [norm_inv, hE']
  calc ‖Complex.sin (π * (ζ - Complex.I * t))‖⁻¹ ≤ ((1 - q) / 2 * E)⁻¹ :=
        inv_anti₀ hpos h3
    _ = 2 / (1 - q) * E⁻¹ := by field_simp

/-- The far part `∫_{|t - y₀| > δ} u_r(t) / sin(π(ζ - it)) dt`. -/
noncomputable def farPart (a b : ℝ) (ζ : ℂ) : ℂ :=
  ∫ t in (Icc a b)ᶜ, (uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))

lemma abs_sub_gt_of_notMem {y₀ δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ (Icc (y₀ - δ) (y₀ + δ))ᶜ) : δ < |t - y₀| := by
  simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma im_ball_close {y₀ δ : ℝ} {ζ : ℂ} (hζ : ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ) : |ζ.im - y₀| < δ := by
  have h1 : ‖ζ - Complex.I * (y₀ : ℂ)‖ < δ := by simpa [mem_ball, dist_eq_norm] using hζ
  have := Complex.abs_im_le_norm (ζ - Complex.I * (y₀ : ℂ))
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add] at this
  linarith

lemma differentiableOn_farPart {y₀ δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (farPart (y₀ - δ) (y₀ + δ)) (ball (Complex.I * (y₀ : ℂ)) δ) := by
  have hne : ∀ ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ, ∀ t ∈ (Icc (y₀ - δ) (y₀ + δ))ᶜ,
      Complex.sin (π * (ζ - Complex.I * t)) ≠ 0 := by
    intro ζ hζ t ht h
    have h1 := norm_sin_arg_sq ζ t
    rw [h, norm_zero] at h1
    have h2 := im_ball_close hζ
    have h3 := abs_sub_gt_of_notMem hδ ht
    have hne : ζ.im - t ≠ 0 := by
      intro h0
      have : |t - y₀| ≤ |ζ.im - y₀| := by
        have : t - y₀ = ζ.im - y₀ := by linarith
        rw [this]
      linarith
    have : Real.sinh (π * (ζ.im - t)) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' hne)
    nlinarith [sq_nonneg (Real.sin (π * ζ.re)), pow_pos (abs_pos.mpr this) 2, sq_abs (Real.sinh (π * (ζ.im - t)))]
  unfold farPart
  refine differentiableOn_integral_param (μ := volume.restrict (Icc (y₀ - δ) (y₀ + δ))ᶜ)
    (Φ := fun w t => (uR t : ℂ) / Complex.sin (π * (w - Complex.I * t))) isOpen_ball ?_ ?_ ?_
  · intro w hw
    have : ContinuousOn (fun t : ℝ => (uR t : ℂ) / Complex.sin (π * (w - Complex.I * t)))
        (Icc (y₀ - δ) (y₀ + δ))ᶜ := by
      refine ContinuousOn.div (Complex.continuous_ofReal.comp continuous_uR).continuousOn
        (by fun_prop) (fun t ht => hne w hw t ht)
    exact this.aestronglyMeasurable measurableSet_Icc.compl
  · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht w hw
    exact ((differentiableAt_const (uR t : ℂ)).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.sin (π * (w - Complex.I * t))) w)
      (hne w hw t ht)).differentiableWithinAt
  · intro ζ₀ hζ₀
    have h0 := im_ball_close hζ₀
    set m : ℝ := (δ - |ζ₀.im - y₀|) / 2 with hm
    have hmpos : 0 < m := by rw [hm]; linarith
    set σ : ℝ := 2 / (1 - Real.exp (-(2 * π * m))) with hσ
    have hq : 0 < 1 - Real.exp (-(2 * π * m)) := by
      have : Real.exp (-(2 * π * m)) < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
      linarith
    have hσpos : 0 < σ := by positivity
    refine ⟨min m 1, lt_min hmpos one_pos, fun t => (Real.log (1 + t ^ 2) + 2 * C0) * σ *
      Real.exp (π * (|ζ₀.im| + 1)) * Real.exp (-(π * |t|)), ?_, ?_⟩
    · have := (integrable_log_weight (C := 2 * C0) (by have := C0_nonneg; positivity)).const_mul
        (σ * Real.exp (π * (|ζ₀.im| + 1)))
      refine (this.congr (Eventually.of_forall fun t => ?_)).restrict
      simp only
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht w hw
      have him : |w.im - ζ₀.im| < min m 1 := by
        have := Complex.abs_im_le_norm (w - ζ₀)
        rw [mem_ball, dist_eq_norm] at hw
        simp only [Complex.sub_im] at this
        linarith
      have hy : |w.im| ≤ |ζ₀.im| + 1 := by
        calc |w.im| = |(w.im - ζ₀.im) + ζ₀.im| := by ring_nf
          _ ≤ |w.im - ζ₀.im| + |ζ₀.im| := abs_add_le _ _
          _ ≤ _ := by linarith [min_le_right m 1]
      have hgap : m ≤ |w.im - t| := by
        have h3 := abs_sub_gt_of_notMem hδ ht
        have : |t - y₀| ≤ |t - w.im| + |w.im - y₀| := by
          calc |t - y₀| = |(t - w.im) + (w.im - y₀)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        have h4 : |w.im - y₀| ≤ |w.im - ζ₀.im| + |ζ₀.im - y₀| := by
          calc |w.im - y₀| = |(w.im - ζ₀.im) + (ζ₀.im - y₀)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        rw [abs_sub_comm t w.im] at this
        linarith [min_le_left m 1]
      have hk := kernel_norm_le_far (ζ := w) t hmpos hgap
      have hexp : Real.exp (-(π * |w.im - t|)) ≤ Real.exp (π * (|ζ₀.im| + 1)) * Real.exp (-(π * |t|)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : |t| ≤ |w.im - t| + |w.im| := by
          calc |t| = |w.im - (w.im - t)| := by ring_nf
            _ ≤ |w.im| + |w.im - t| := abs_sub _ _
            _ = _ := by ring
        nlinarith [Real.pi_pos]
      have hu : ‖(uR t : ℂ)‖ ≤ Real.log (1 + t ^ 2) + 2 * C0 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_uR_le' t
      rw [norm_div, div_eq_mul_inv, ← norm_inv]
      have h1 : ‖(Complex.sin (π * (w - Complex.I * t)))⁻¹‖ ≤
          σ * (Real.exp (π * (|ζ₀.im| + 1)) * Real.exp (-(π * |t|))) :=
        hk.trans (mul_le_mul_of_nonneg_left hexp hσpos.le)
      calc ‖(uR t : ℂ)‖ * ‖(Complex.sin (π * (w - Complex.I * t)))⁻¹‖
          ≤ (Real.log (1 + t ^ 2) + 2 * C0) * (σ * (Real.exp (π * (|ζ₀.im| + 1)) *
              Real.exp (-(π * |t|)))) :=
            mul_le_mul hu h1 (norm_nonneg _) ((norm_nonneg _).trans hu)
        _ = _ := by ring

/-- The holomorphic near part of the segment integral. -/
noncomputable def nearJ (v : ℂ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in Icc a b, ((1 / (π : ℂ)) * dslope v (t : ℂ) w + v (t : ℂ) * kappaFn ((t : ℂ) - w))

lemma differentiableOn_nearJ {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδR : δ < R)
    (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R)) :
    DifferentiableOn ℂ (nearJ v (y₀ - δ) (y₀ + δ)) (ball (y₀ : ℂ) δ) := by
  have hball : IsOpen (ball (y₀ : ℂ) R) := isOpen_ball
  have hcb : closedBall (y₀ : ℂ) δ ⊆ ball (y₀ : ℂ) R := closedBall_subset_ball hδR
  have hIcc : ∀ t ∈ Icc (y₀ - δ) (y₀ + δ), (t : ℂ) ∈ closedBall (y₀ : ℂ) δ := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    have : ‖(t : ℂ) - y₀‖ = |t - y₀| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [this, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨M₁, hM₁⟩ := exists_dslope_bound hδR hv
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall (y₀ : ℂ) δ).exists_bound_of_continuousOn
    (hv.continuousOn.mono hcb)
  have hκc : ContinuousOn kappaFn (ball 0 1) := differentiableOn_kappaFn.continuousOn
  have hts : ∀ t ∈ Icc (y₀ - δ) (y₀ + δ), ∀ w ∈ ball (y₀ : ℂ) δ, ‖(t : ℂ) - w‖ < 1 := by
    intro t ht w hw
    have h1 := mem_closedBall.mp (hIcc t ht)
    have h2 := mem_ball.mp hw
    rw [dist_eq_norm] at h1 h2
    calc ‖(t : ℂ) - w‖ = ‖((t : ℂ) - y₀) + (y₀ - w)‖ := by ring_nf
      _ ≤ ‖(t : ℂ) - y₀‖ + ‖(y₀ : ℂ) - w‖ := norm_add_le _ _
      _ < δ + δ := by
        rw [norm_sub_rev (y₀ : ℂ) w]; linarith
      _ ≤ 1 := by linarith
  refine differentiableOn_intervalParam (Φ := fun w t =>
    (1 / (π : ℂ)) * dslope v (t : ℂ) w + v (t : ℂ) * kappaFn ((t : ℂ) - w)) isOpen_ball ?_ ?_ ?_
  · intro w hw
    have hwR : w ∈ ball (y₀ : ℂ) R := ball_subset_ball hδR.le hw
    have h1 : ContinuousOn (fun t : ℝ => dslope v (t : ℂ) w) (Icc (y₀ - δ) (y₀ + δ)) := by
      have hd : DifferentiableOn ℂ (dslope v w) (ball (y₀ : ℂ) R) :=
        (differentiableOn_dslope (hball.mem_nhds hwR)).mpr hv
      have hc : ContinuousOn (dslope v w) (ball (y₀ : ℂ) R) := hd.continuousOn
      refine (hc.comp Complex.continuous_ofReal.continuousOn (fun t ht => hcb (hIcc t ht))).congr
        (fun t _ => ?_)
      simp [dslope_symm v (t : ℂ) w]
    have h2 : ContinuousOn (fun t : ℝ => v (t : ℂ)) (Icc (y₀ - δ) (y₀ + δ)) :=
      hv.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun t ht => hcb (hIcc t ht))
    have h3 : ContinuousOn (fun t : ℝ => kappaFn ((t : ℂ) - w)) (Icc (y₀ - δ) (y₀ + δ)) :=
      hκc.comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) - w).continuousOn
        (fun t ht => mem_ball_zero_iff.mpr (hts t ht w hw))
    exact (continuousOn_const.mul h1).add (h2.mul h3)
  · intro t ht
    have htR : (t : ℂ) ∈ ball (y₀ : ℂ) R := hcb (hIcc t ht)
    have hd : DifferentiableOn ℂ (dslope v (t : ℂ)) (ball (y₀ : ℂ) R) :=
      (differentiableOn_dslope (hball.mem_nhds htR)).mpr hv
    have hk : DifferentiableOn ℂ (fun w : ℂ => kappaFn ((t : ℂ) - w)) (ball (y₀ : ℂ) δ) := by
      refine differentiableOn_kappaFn.comp (by fun_prop : Differentiable ℂ fun w : ℂ => (t : ℂ) - w).differentiableOn
        (fun w hw => mem_ball_zero_iff.mpr (hts t ht w hw))
    exact (differentiableOn_const _ |>.mul (hd.mono (ball_subset_ball hδR.le))).add
      (differentiableOn_const _ |>.mul hk)
  · intro w₀ hw₀
    have hw₀' := mem_ball.mp hw₀
    rw [dist_eq_norm] at hw₀'
    set d : ℝ := ‖w₀ - y₀‖ with hd
    set r : ℝ := min (δ - d) ((1 - δ - d) / 2) with hr
    have hrpos : 0 < r := lt_min (by linarith) (by linarith)
    set ρ : ℝ := δ + d + r with hρ
    have hρ1 : ρ < 1 := by
      have : r ≤ (1 - δ - d) / 2 := min_le_right _ _
      linarith
    obtain ⟨M₃, hM₃⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
      (hκc.mono (closedBall_subset_ball hρ1))
    refine ⟨r, hrpos, (1 / π) * M₁ + M₂ * M₃, fun t ht w hw => ?_⟩
    have hwδ : w ∈ ball (y₀ : ℂ) δ := by
      rw [mem_ball, dist_eq_norm]
      have h1 := mem_ball.mp hw
      rw [dist_eq_norm] at h1
      have : r ≤ δ - d := min_le_left _ _
      calc ‖w - y₀‖ = ‖(w - w₀) + (w₀ - y₀)‖ := by ring_nf
        _ ≤ ‖w - w₀‖ + ‖w₀ - y₀‖ := norm_add_le _ _
        _ < r + d := by linarith
        _ ≤ δ := by linarith
    have hts' : (t : ℂ) - w ∈ closedBall (0 : ℂ) ρ := by
      rw [mem_closedBall, dist_zero_right]
      have h1 := mem_closedBall.mp (hIcc t ht)
      rw [dist_eq_norm] at h1
      have h2 := mem_ball.mp hw
      rw [dist_eq_norm] at h2
      calc ‖(t : ℂ) - w‖ = ‖((t : ℂ) - y₀) + ((y₀ : ℂ) - w₀) + (w₀ - w)‖ := by ring_nf
        _ ≤ ‖(t : ℂ) - y₀‖ + ‖(y₀ : ℂ) - w₀‖ + ‖w₀ - w‖ := norm_add₃_le
        _ ≤ δ + d + r := by
          rw [norm_sub_rev (y₀ : ℂ) w₀]
          rw [norm_sub_rev w₀ w]
          linarith
    have e1 : ‖dslope v (t : ℂ) w‖ ≤ M₁ := hM₁ _ (hIcc t ht) _ (ball_subset_closedBall hwδ)
    have e2 : ‖v (t : ℂ)‖ ≤ M₂ := hM₂ _ (hIcc t ht)
    have e3 : ‖kappaFn ((t : ℂ) - w)‖ ≤ M₃ := by
      have := hM₃ _ hts'
      simpa using this
    calc ‖(1 / (π : ℂ)) * dslope v (t : ℂ) w + v (t : ℂ) * kappaFn ((t : ℂ) - w)‖
        ≤ ‖(1 / (π : ℂ)) * dslope v (t : ℂ) w‖ + ‖v (t : ℂ) * kappaFn ((t : ℂ) - w)‖ := norm_add_le _ _
      _ ≤ (1 / π) * M₁ + M₂ * M₃ := by
        rw [norm_mul, norm_mul]
        have : ‖(1 / (π : ℂ))‖ = 1 / π := by
          rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [this]
        have hM2nn : 0 ≤ M₂ := (norm_nonneg _).trans e2
        gcongr

/-- The coordinate `w = -iζ`. -/
noncomputable def wOf (ζ : ℂ) : ℂ := -(Complex.I * ζ)

lemma wOf_im (ζ : ℂ) : (wOf ζ).im = -ζ.re := by simp [wOf]

lemma norm_wOf_sub (ζ : ℂ) (y₀ : ℝ) : ‖wOf ζ - (y₀ : ℂ)‖ = ‖ζ - Complex.I * (y₀ : ℂ)‖ := by
  have : wOf ζ - (y₀ : ℂ) = -Complex.I * (ζ - Complex.I * (y₀ : ℂ)) := by
    unfold wOf; ring_nf; simp; ring
  rw [this, norm_mul, norm_neg, Complex.norm_I, one_mul]

lemma sin_arg_eq (ζ : ℂ) (t : ℝ) :
    Complex.sin (π * (ζ - Complex.I * t)) = -(Complex.sinh (π * ((t : ℂ) - wOf ζ)) * Complex.I) := by
  have h1 : (π : ℂ) * (ζ - Complex.I * t) = (-(π * ((t : ℂ) - wOf ζ))) * Complex.I := by
    unfold wOf; ring_nf; simp
  rw [h1, Complex.sin_mul_I, Complex.sinh_neg]
  ring

lemma integrand_eq {ζ : ℂ} (hζ : ζ ∈ strip) {t : ℝ} {v : ℂ → ℂ} (hvt : v (t : ℂ) = (uR t : ℂ)) :
    (uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)) =
      Complex.I * ((1 / (π : ℂ)) * dslope v (t : ℂ) (wOf ζ) + v (t : ℂ) * kappaFn ((t : ℂ) - wOf ζ)
        + (1 / (π : ℂ)) * v (wOf ζ) * (1 / ((t : ℂ) - wOf ζ))) := by
  have hs : (t : ℂ) - wOf ζ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, wOf_im, Complex.zero_im] at this
    have := hζ.1
    linarith
  have hd : dslope v (t : ℂ) (wOf ζ) = ((t : ℂ) - wOf ζ)⁻¹ * (v (t : ℂ) - v (wOf ζ)) := by
    rw [dslope_symm v (t : ℂ) (wOf ζ), dslope_of_ne v (sub_ne_zero.mp hs), slope_def_module, smul_eq_mul]
  rw [sin_arg_eq, hd, ← hvt]
  unfold kappaFn
  simp only [div_eq_mul_inv, one_mul, mul_inv, inv_neg, Complex.inv_I]
  ring

lemma continuousOn_nearIntegrand {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ2 : δ ≤ 1 / 2) (hδR : δ < R)
    (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R)) {w : ℂ} (hw : w ∈ ball (y₀ : ℂ) δ) :
    ContinuousOn (fun t : ℝ => (1 / (π : ℂ)) * dslope v (t : ℂ) w + v (t : ℂ) * kappaFn ((t : ℂ) - w))
      (Icc (y₀ - δ) (y₀ + δ)) := by
  have hball : IsOpen (ball (y₀ : ℂ) R) := isOpen_ball
  have hcb : closedBall (y₀ : ℂ) δ ⊆ ball (y₀ : ℂ) R := closedBall_subset_ball hδR
  have hIcc : ∀ t ∈ Icc (y₀ - δ) (y₀ + δ), (t : ℂ) ∈ closedBall (y₀ : ℂ) δ := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    have : ‖(t : ℂ) - y₀‖ = |t - y₀| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [this, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hκc : ContinuousOn kappaFn (ball 0 1) := differentiableOn_kappaFn.continuousOn
  have hts : ∀ t ∈ Icc (y₀ - δ) (y₀ + δ), ‖(t : ℂ) - w‖ < 1 := by
    intro t ht
    have h1 := mem_closedBall.mp (hIcc t ht)
    have h2 := mem_ball.mp hw
    rw [dist_eq_norm] at h1 h2
    calc ‖(t : ℂ) - w‖ = ‖((t : ℂ) - y₀) + (y₀ - w)‖ := by ring_nf
      _ ≤ ‖(t : ℂ) - y₀‖ + ‖(y₀ : ℂ) - w‖ := norm_add_le _ _
      _ < δ + δ := by
        rw [norm_sub_rev (y₀ : ℂ) w]; linarith
      _ ≤ 1 := by linarith
  have hwR : w ∈ ball (y₀ : ℂ) R := ball_subset_ball hδR.le hw
  have h1 : ContinuousOn (fun t : ℝ => dslope v (t : ℂ) w) (Icc (y₀ - δ) (y₀ + δ)) := by
    have hd : DifferentiableOn ℂ (dslope v w) (ball (y₀ : ℂ) R) :=
      (differentiableOn_dslope (hball.mem_nhds hwR)).mpr hv
    have hc : ContinuousOn (dslope v w) (ball (y₀ : ℂ) R) := hd.continuousOn
    refine (hc.comp Complex.continuous_ofReal.continuousOn (fun t ht => hcb (hIcc t ht))).congr
      (fun t _ => ?_)
    simp [dslope_symm v (t : ℂ) w]
  have h2 : ContinuousOn (fun t : ℝ => v (t : ℂ)) (Icc (y₀ - δ) (y₀ + δ)) :=
    hv.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun t ht => hcb (hIcc t ht))
  have h3 : ContinuousOn (fun t : ℝ => kappaFn ((t : ℂ) - w)) (Icc (y₀ - δ) (y₀ + δ)) :=
    hκc.comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) - w).continuousOn
      (fun t ht => mem_ball_zero_iff.mpr (hts t ht))
  exact (continuousOn_const.mul h1).add (h2.mul h3)

/-- The explicit continuation `H = far + i (near + (1/π) v(w) logPart)` with `w = -iζ`. -/
noncomputable def contH (v : ℂ → ℂ) (y₀ δ : ℝ) (ζ : ℂ) : ℂ :=
  farPart (y₀ - δ) (y₀ + δ) ζ + Complex.I * (nearJ v (y₀ - δ) (y₀ + δ) (wOf ζ) +
    (1 / (π : ℂ)) * v (wOf ζ) * logPart (y₀ - δ) (y₀ + δ) (wOf ζ))

lemma wOf_mem_ball {y₀ δ : ℝ} {ζ : ℂ} (hζ : ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ) :
    wOf ζ ∈ ball (y₀ : ℂ) δ := by
  rw [mem_ball, dist_eq_norm, norm_wOf_sub]
  simpa [mem_ball, dist_eq_norm] using hζ

lemma differentiable_wOf : Differentiable ℂ wOf := by unfold wOf; fun_prop

theorem differentiableOn_contH {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hδR : δ < R) (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R)) :
    DifferentiableOn ℂ (contH v y₀ δ) (ball (Complex.I * (y₀ : ℂ)) δ) := by
  have hw : ∀ ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ, wOf ζ ∈ ball (y₀ : ℂ) δ := fun ζ hζ => wOf_mem_ball hζ
  have hwd := differentiable_wOf
  have h1 := differentiableOn_nearJ hδ hδ2 hδR hv
  have h2 : DifferentiableOn ℂ (fun ζ => v (wOf ζ)) (ball (Complex.I * (y₀ : ℂ)) δ) :=
    (hv.mono (ball_subset_ball hδR.le)).comp hwd.differentiableOn hw
  have h3 := (differentiableOn_logPart (y₀ := y₀) (δ := δ)).comp hwd.differentiableOn hw
  exact (differentiableOn_farPart hδ).add
    (((h1.comp hwd.differentiableOn hw).add ((differentiableOn_const _).mul h2 |>.mul h3)).const_mul _)

/-- **Local holomorphic continuation of `h` across the edge `Re ζ = 0`.**  If `u_r` extends holomorphically to
`B(y₀, R)`, then for `δ < R`, `δ ≤ 1/2`, `h = contH` on `S ∩ B(i y₀, δ)` and `contH` is holomorphic on `B(i y₀, δ)`. -/
theorem outerH_eq_contH {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ2 : δ ≤ 1 / 2)
    (hδR : δ < R) (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R))
    (hvu : ∀ t : ℝ, |t - y₀| < R → v (t : ℂ) = (uR t : ℂ)) {ζ : ℂ} (hζ : ζ ∈ strip)
    (hζb : ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ) : outerH ζ = contH v y₀ δ ζ := by
  have hwζ := wOf_mem_ball hζb
  have himw : (wOf ζ).im < 0 := by rw [wOf_im]; linarith [hζ.1]
  have hδ : 0 < δ := by
    have := mem_ball.mp hζb
    rw [dist_eq_norm] at this
    exact lt_of_le_of_lt (norm_nonneg _) this
  have hint := integrable_integrand hζ
  have hsplit := integral_add_compl (measurableSet_Icc (a := y₀ - δ) (b := y₀ + δ)) hint
  unfold outerH contH
  rw [← hsplit, add_comm]
  refine congrArg₂ (· + ·) rfl ?_
  have hcont1 := continuousOn_nearIntegrand hδ2 hδR hv hwζ
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / ((t : ℂ) - wOf ζ)) (Icc (y₀ - δ) (y₀ + δ)) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun t _ h => ?_)
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
    linarith
  have hi1 : IntegrableOn (fun t : ℝ => (1 / (π : ℂ)) * dslope v (t : ℂ) (wOf ζ) +
      v (t : ℂ) * kappaFn ((t : ℂ) - wOf ζ)) (Icc (y₀ - δ) (y₀ + δ)) :=
    hcont1.integrableOn_Icc
  have hi2 : IntegrableOn (fun t : ℝ => (1 / (π : ℂ)) * v (wOf ζ) * (1 / ((t : ℂ) - wOf ζ)))
      (Icc (y₀ - δ) (y₀ + δ)) :=
    (continuousOn_const.mul hcont2).integrableOn_Icc
  calc ∫ t in Icc (y₀ - δ) (y₀ + δ), (uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))
      = ∫ t in Icc (y₀ - δ) (y₀ + δ), Complex.I * (((1 / (π : ℂ)) * dslope v (t : ℂ) (wOf ζ) +
          v (t : ℂ) * kappaFn ((t : ℂ) - wOf ζ)) +
          (1 / (π : ℂ)) * v (wOf ζ) * (1 / ((t : ℂ) - wOf ζ))) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
        have htR : |t - y₀| < R := by
          have : |t - y₀| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
          linarith
        have := integrand_eq hζ (hvu t htR)
        simpa [add_assoc] using this
    _ = Complex.I * (nearJ v (y₀ - δ) (y₀ + δ) (wOf ζ) +
          (1 / (π : ℂ)) * v (wOf ζ) * logPart (y₀ - δ) (y₀ + δ) (wOf ζ)) := by
        rw [integral_const_mul, integral_add hi1 hi2, integral_const_mul]
        unfold nearJ
        rw [integral_inv_sub (by linarith) himw]

lemma wOf_center (y₀ : ℝ) : wOf (Complex.I * (y₀ : ℂ)) = (y₀ : ℂ) := by
  unfold wOf; ring_nf; simp

lemma farPart_center_re (a b y₀ : ℝ) : (farPart a b (Complex.I * (y₀ : ℂ))).re = 0 := by
  unfold farPart
  have : ∀ t : ℝ, (uR t : ℂ) / Complex.sin (π * (Complex.I * (y₀ : ℂ) - Complex.I * t)) =
      Complex.I * ((uR t / Real.sinh (π * (t - y₀)) : ℝ) : ℂ) := by
    intro t
    rw [sin_arg_eq, wOf_center]
    have : Complex.sinh (π * ((t : ℂ) - y₀)) = ((Real.sinh (π * (t - y₀)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sinh]; push_cast; ring_nf
    rw [this]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, inv_neg, Complex.inv_I]
    ring
  simp_rw [this]
  rw [integral_const_mul, integral_complex_ofReal]
  simp

lemma nearJ_center_im {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδR : δ < R)
    (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R))
    (hvu : ∀ t : ℝ, |t - y₀| < R → v (t : ℂ) = (uR t : ℂ)) :
    (nearJ v (y₀ - δ) (y₀ + δ) (y₀ : ℂ)).im = 0 := by
  unfold nearJ
  have hw : (y₀ : ℂ) ∈ ball (y₀ : ℂ) δ := mem_ball_self hδ
  have hint : IntegrableOn (fun t : ℝ => (1 / (π : ℂ)) * dslope v (t : ℂ) (y₀ : ℂ) +
      v (t : ℂ) * kappaFn ((t : ℂ) - y₀)) (Icc (y₀ - δ) (y₀ + δ)) :=
    (continuousOn_nearIntegrand hδ2 hδR hv hw).integrableOn_Icc
  have h1 := integral_im (μ := volume.restrict (Icc (y₀ - δ) (y₀ + δ))) hint
  simp only [RCLike.im_to_complex] at h1
  rw [← h1]
  refine integral_eq_zero_of_ae ?_
  have hne : ∀ᵐ t ∂(volume.restrict (Icc (y₀ - δ) (y₀ + δ))), t ≠ y₀ := by
    have : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ y₀ := by
      simpa using (Set.countable_singleton y₀).ae_notMem volume
    exact ae_restrict_of_ae this
  filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t ht htI
  have htR : |t - y₀| < R := by
    have : |t - y₀| ≤ δ := abs_le.mpr ⟨by linarith [htI.1], by linarith [htI.2]⟩
    linarith
  have hy : |y₀ - y₀| < R := by simp; linarith
  have e1 := hvu t htR
  have e2 := hvu y₀ hy
  have hne' : (t : ℂ) ≠ (y₀ : ℂ) := by exact_mod_cast ht
  have hd : dslope v (t : ℂ) (y₀ : ℂ) = ((t : ℂ) - y₀)⁻¹ * (v (t : ℂ) - v (y₀ : ℂ)) := by
    rw [dslope_symm v (t : ℂ) (y₀ : ℂ), dslope_of_ne v hne', slope_def_module, smul_eq_mul]
  rw [hd, e1, e2]
  unfold kappaFn
  have : ((1 / (π : ℂ)) * (((t : ℂ) - y₀)⁻¹ * ((uR t : ℂ) - (uR y₀ : ℂ))) +
      (uR t : ℂ) * (1 / Complex.sinh (π * ((t : ℂ) - y₀)) - 1 / (π * ((t : ℂ) - y₀)))) =
      (((1 / π) * ((t - y₀)⁻¹ * (uR t - uR y₀)) + uR t * (1 / Real.sinh (π * (t - y₀)) -
        1 / (π * (t - y₀))) : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [this]
  exact Complex.ofReal_im _

lemma logPart_center (y₀ δ : ℝ) (hδ : 0 < δ) :
    logPart (y₀ - δ) (y₀ + δ) (y₀ : ℂ) = -(Complex.I * π) := by
  unfold logPart
  have h1 : ((y₀ + δ : ℝ) : ℂ) - (y₀ : ℂ) = (δ : ℂ) := by push_cast; ring
  have h2 : (y₀ : ℂ) - ((y₀ - δ : ℝ) : ℂ) = (δ : ℂ) := by push_cast; ring
  rw [h1, h2]
  ring

/-- The boundary real part: `Re H(i y₀) = u_r(y₀)`. -/
theorem re_contH_center {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδR : δ < R)
    (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R))
    (hvu : ∀ t : ℝ, |t - y₀| < R → v (t : ℂ) = (uR t : ℂ)) :
    (contH v y₀ δ (Complex.I * (y₀ : ℂ))).re = uR y₀ := by
  unfold contH
  rw [wOf_center, logPart_center y₀ δ hδ]
  have hy : |y₀ - y₀| < R := by simp; linarith
  have e2 := hvu y₀ hy
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hnear := nearJ_center_im hδ hδ2 hδR hv hvu
  have : Complex.I * (nearJ v (y₀ - δ) (y₀ + δ) (y₀ : ℂ) +
      1 / (π : ℂ) * v (y₀ : ℂ) * (-(Complex.I * π))) =
      Complex.I * nearJ v (y₀ - δ) (y₀ + δ) (y₀ : ℂ) + (uR y₀ : ℂ) := by
    rw [e2]; field_simp; ring_nf; simp
  rw [this, Complex.add_re, Complex.add_re, farPart_center_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, hnear]
  simp

end FormalResearch.SignUncertainty.CtOuter
