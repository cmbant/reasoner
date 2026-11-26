/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymbolsG0

/-!
# Lemma `fct:inner-symbols` (FCT.5b) (a), closed form: the contour rotation of the regularised integral

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (a), last sentence: "rotate the contour by `arg u = -π/6`".

For `s, a, ε > 0` and `0 ≤ θ ≤ π/6` put `z = e^{-iθ} t` and
`F_ε(θ) = ∫_0^∞ e^{-iθ} z^{s-1} e^{-i a z³ - ε z²} dt = ∫_0^∞ t^{s-1} e^{E(θ,t)} dt`, `E = -iθs - i a e^{-3iθ} t³ - ε e^{-2iθ} t²`.
Then `∂_θ (t^{s-1} e^{E}) = -i ∂_t (t^{s} e^{E})`, the boundary terms vanish (`s > 0`, and `|e^{E}| ≤ e^{-ε t²/2}` on `[0, π/6]`), so
`F_ε` is constant on `[0, π/6]` (`rot_const`): the rotated integral equals the real-axis integral.  At `θ = π/6` the cubic term is
`-a t³`; dominated convergence in `ε ↓ 0` gives the Abel limit (`rot_tendsto`).  No contour estimate is needed: the rotation is the
vanishing of an `θ`-derivative.

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.FctRot

/-- The exponent `E(θ, t) = -iθs - i a e^{-3iθ} t³ - ε e^{-2iθ} t²` of the rotated integrand. -/
noncomputable def rotE (s a ε θ t : ℝ) : ℂ :=
  -(Complex.I * ((θ * s : ℝ) : ℂ)) - Complex.I * (a : ℂ) * Complex.exp (-(3 * Complex.I * (θ : ℂ))) * (t : ℂ) ^ 3
    - (ε : ℂ) * Complex.exp (-(2 * Complex.I * (θ : ℂ))) * (t : ℂ) ^ 2

/-- The rotated integrand `t^{s-1} e^{E(θ,t)}`. -/
noncomputable def rotF (s a ε θ t : ℝ) : ℂ := ((t ^ (s - 1) : ℝ) : ℂ) * Complex.exp (rotE s a ε θ t)

lemma re_rotE (s a ε θ t : ℝ) :
    (rotE s a ε θ t).re = -(a * Real.sin (3 * θ) * t ^ 3) - ε * Real.cos (2 * θ) * t ^ 2 := by
  have h3 : Complex.exp (-(3 * Complex.I * (θ : ℂ))) = ⟨Real.cos (3 * θ), -Real.sin (3 * θ)⟩ := by
    apply Complex.ext
    · simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
    · simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have h2 : Complex.exp (-(2 * Complex.I * (θ : ℂ))) = ⟨Real.cos (2 * θ), -Real.sin (2 * θ)⟩ := by
    apply Complex.ext
    · simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
    · simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]
  unfold rotE
  rw [h3, h2]
  simp [Complex.mul_re, Complex.mul_im, pow_succ]

lemma norm_exp_rotE_le {s a ε θ t : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 6) (ht : 0 ≤ t) :
    ‖Complex.exp (rotE s a ε θ t)‖ ≤ Real.exp (-(ε / 2) * t ^ 2) := by
  rw [Complex.norm_exp, re_rotE]
  refine Real.exp_le_exp.2 ?_
  have hs : 0 ≤ Real.sin (3 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hc : 1 / 2 ≤ Real.cos (2 * θ) := by
    have : Real.cos (π / 3) ≤ Real.cos (2 * θ) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith)
    rwa [Real.cos_pi_div_three] at this
  have h1 : 0 ≤ a * Real.sin (3 * θ) * t ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hc (mul_nonneg hε (sq_nonneg t))]

lemma norm_rotF {s a ε θ t : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 6) (ht : 0 < t) :
    ‖rotF s a ε θ t‖ ≤ t ^ (s - 1) * Real.exp (-(ε / 2) * t ^ 2) := by
  unfold rotF
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  exact mul_le_mul_of_nonneg_left (norm_exp_rotE_le ha hε hθ0 hθ ht.le) (Real.rpow_nonneg ht.le _)

/-- `∂_θ E`. -/
noncomputable def dθE (s a ε θ t : ℝ) : ℂ :=
  -(Complex.I * (s : ℂ)) - 3 * (a : ℂ) * Complex.exp (-(3 * Complex.I * (θ : ℂ))) * (t : ℂ) ^ 3
    + 2 * Complex.I * (ε : ℂ) * Complex.exp (-(2 * Complex.I * (θ : ℂ))) * (t : ℂ) ^ 2

/-- `∂_t E`. -/
noncomputable def dtE (a ε θ t : ℝ) : ℂ :=
  -(3 * Complex.I * (a : ℂ) * Complex.exp (-(3 * Complex.I * (θ : ℂ))) * (t : ℂ) ^ 2)
    - 2 * (ε : ℂ) * Complex.exp (-(2 * Complex.I * (θ : ℂ))) * (t : ℂ)

lemma hasDerivAt_exp_rot (k : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Complex.exp (-(k * (θ : ℂ)))) (-k * Complex.exp (-(k * (θ : ℂ)))) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.const_mul k).neg.cexp
  simpa [mul_comm] using h

lemma hasDerivAt_rotE_θ (s a ε θ t : ℝ) :
    HasDerivAt (fun θ : ℝ => rotE s a ε θ t) (dθE s a ε θ t) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => ((θ * s : ℝ) : ℂ)) (s : ℂ) θ := by
    have := ((hasDerivAt_id θ).mul_const s).ofReal_comp
    simpa using this
  have e3 := hasDerivAt_exp_rot (3 * Complex.I) θ
  have e2 := hasDerivAt_exp_rot (2 * Complex.I) θ
  have := (((h1.const_mul Complex.I).neg).sub
    ((e3.const_mul (Complex.I * (a : ℂ))).mul_const ((t : ℂ) ^ 3))).sub ((e2.const_mul (ε : ℂ)).mul_const ((t : ℂ) ^ 2))
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun θ => ?_)
  · unfold dθE
    have hI := Complex.I_sq
    linear_combination (3 * (a : ℂ) * Complex.exp (-(3 * Complex.I * (θ : ℂ))) * (t : ℂ) ^ 3) * hI
  · simp only [rotE, Pi.sub_apply, Pi.neg_apply]

lemma hasDerivAt_rotE_t (s a ε θ t : ℝ) :
    HasDerivAt (fun t : ℝ => rotE s a ε θ t) (dtE a ε θ t) t := by
  have h3 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 3) (3 * (t : ℂ) ^ 2) t := by
    have := (hasDerivAt_pow 3 t).ofReal_comp
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (t : ℂ)) t := by
    have := (hasDerivAt_pow 2 t).ofReal_comp
    simpa using this
  have := ((h3.const_mul (Complex.I * (a : ℂ) * Complex.exp (-(3 * Complex.I * (θ : ℂ))))).const_sub
      (-(Complex.I * ((θ * s : ℝ) : ℂ)))).sub (h2.const_mul ((ε : ℂ) * Complex.exp (-(2 * Complex.I * (θ : ℂ)))))
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · unfold dtE; ring
  · simp only [rotE, Pi.sub_apply]

/-- `∂_θ` of `rotF`. -/
noncomputable def rotF' (s a ε θ t : ℝ) : ℂ :=
  ((t ^ (s - 1) : ℝ) : ℂ) * (dθE s a ε θ t * Complex.exp (rotE s a ε θ t))

lemma hasDerivAt_rotF_θ (s a ε θ t : ℝ) :
    HasDerivAt (fun θ : ℝ => rotF s a ε θ t) (rotF' s a ε θ t) θ := by
  have := (hasDerivAt_rotE_θ s a ε θ t).cexp.const_mul (((t ^ (s - 1) : ℝ) : ℂ))
  unfold rotF rotF'
  refine this.congr_deriv ?_
  ring

/-- The `t`-antiderivative `A = t^s e^{E}`: `∂_θ (t^{s-1} e^E) = -i ∂_t A`. -/
noncomputable def rotA (s a ε θ t : ℝ) : ℂ := ((t ^ s : ℝ) : ℂ) * Complex.exp (rotE s a ε θ t)

lemma hasDerivAt_rotA (s a ε θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (rotA s a ε θ) (Complex.I * rotF' s a ε θ t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((t ^ s : ℝ) : ℂ)) (((s * t ^ (s - 1) : ℝ) : ℂ)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).ofReal_comp
  have := h1.mul (hasDerivAt_rotE_t s a ε θ t).cexp
  unfold rotA
  refine this.congr_deriv ?_
  have hts : t ^ s = t ^ (s - 1) * t := by
    rw [← Real.rpow_add_one ht.ne']; ring_nf
  unfold rotF' dθE dtE
  rw [hts]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring


lemma measurable_rotF (s a ε θ : ℝ) : Measurable (fun t : ℝ => rotF s a ε θ t) := by
  unfold rotF rotE; fun_prop

lemma measurable_rotF' (s a ε θ : ℝ) : Measurable (fun t : ℝ => rotF' s a ε θ t) := by
  unfold rotF' dθE rotE; fun_prop

/-- Integrable majorant of the `θ`-derivative. -/
noncomputable def rotBd (s a ε t : ℝ) : ℝ :=
  s * (t ^ (s - 1) * Real.exp (-(ε / 2) * t ^ 2)) + 3 * a * (t ^ (s + 2) * Real.exp (-(ε / 2) * t ^ 2))
    + 2 * ε * (t ^ (s + 1) * Real.exp (-(ε / 2) * t ^ 2))

lemma integrableOn_rotBd {s a ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    IntegrableOn (rotBd s a ε) (Ioi 0) := by
  have hb : 0 < ε / 2 := by positivity
  have h1 := (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := s - 1) (by linarith)).const_mul s
  have h2 := (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := s + 2) (by linarith)).const_mul (3 * a)
  have h3 := (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := s + 1) (by linarith)).const_mul (2 * ε)
  exact (h1.add h2).add h3

lemma integrableOn_rotMaj {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(ε / 2) * t ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq (by positivity) (by linarith)

lemma norm_rotF'_le {s a ε θ t : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hε : 0 ≤ ε) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 6)
    (ht : 0 < t) : ‖rotF' s a ε θ t‖ ≤ rotBd s a ε t := by
  have hexp := norm_exp_rotE_le (s := s) (t := t) ha hε hθ0 hθ ht.le
  have e3 : ‖Complex.exp (-(3 * Complex.I * (θ : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (-(2 * Complex.I * (θ : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hd : ‖dθE s a ε θ t‖ ≤ s + 3 * a * t ^ 3 + 2 * ε * t ^ 2 := by
    unfold dθE
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
    · refine add_le_add ?_ ?_
      · simp [abs_of_pos hs]
      · simp [e3, abs_of_nonneg ha, abs_of_pos ht]
    · simp [e2, abs_of_nonneg hε, abs_of_pos ht]
  unfold rotF' rotBd
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), norm_mul]
  have hp : 0 ≤ t ^ (s - 1) := Real.rpow_nonneg ht.le _
  have h3 : t ^ (s + 2) = t ^ (s - 1) * t ^ 3 := by
    rw [show s + 2 = (s - 1) + (3 : ℕ) by push_cast; ring, Real.rpow_add ht, Real.rpow_natCast]
  have h2 : t ^ (s + 1) = t ^ (s - 1) * t ^ 2 := by
    rw [show s + 1 = (s - 1) + (2 : ℕ) by push_cast; ring, Real.rpow_add ht, Real.rpow_natCast]
  rw [h3, h2]
  calc t ^ (s - 1) * (‖dθE s a ε θ t‖ * ‖Complex.exp (rotE s a ε θ t)‖)
      ≤ t ^ (s - 1) * ((s + 3 * a * t ^ 3 + 2 * ε * t ^ 2) * Real.exp (-(ε / 2) * t ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hd hexp (norm_nonneg _) (by positivity)) hp
    _ = _ := by ring


/-- `F_ε(θ) = ∫_0^∞ t^{s-1} e^{E(θ,t)} dt`. -/
noncomputable def rotI (s a ε θ : ℝ) : ℂ := ∫ t in Ioi (0 : ℝ), rotF s a ε θ t

lemma continuous_rotA (s a ε θ : ℝ) (hs : 0 < s) : Continuous (rotA s a ε θ) := by
  have : Continuous fun t : ℝ => t ^ s := Real.continuous_rpow_const hs.le
  unfold rotA rotE
  fun_prop

lemma rotA_zero (s a ε θ : ℝ) (hs : 0 < s) : rotA s a ε θ 0 = 0 := by
  simp [rotA, Real.zero_rpow hs.ne']

lemma tendsto_rotA {s a ε θ : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 6) :
    Tendsto (rotA s a ε θ) atTop (𝓝 0) := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (ε / 2) (by positivity)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  unfold rotA
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
  refine mul_le_mul_of_nonneg_left ((norm_exp_rotE_le ha hε.le hθ0 hθ ht0.le).trans
    (Real.exp_le_exp.2 ?_)) (Real.rpow_nonneg ht0.le _)
  nlinarith [mul_nonneg hε.le (mul_nonneg ht0.le (sub_nonneg.2 ht))]

lemma integrable_rotF {s a ε θ : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hε : 0 < ε) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 6) :
    Integrable (fun t => rotF s a ε θ t) (volume.restrict (Ioi (0 : ℝ))) := by
  refine Integrable.mono' (integrableOn_rotMaj hs hε) (measurable_rotF s a ε θ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_rotF ha hε.le hθ0 hθ ht

/-- `F_ε' = 0` in the interior of `[0, π/6]`: `∂_θ F = -i [t^s e^E]_0^∞ = 0`. -/
lemma hasDerivAt_rotI {s a ε θ : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hε : 0 < ε) (hθ0 : 0 < θ) (hθ : θ < π / 6) :
    HasDerivAt (rotI s a ε) 0 θ := by
  set r := min θ (π / 6 - θ) with hr
  have hrpos : 0 < r := lt_min hθ0 (by linarith)
  have hball : ∀ x ∈ Metric.ball θ r, 0 ≤ x ∧ x ≤ π / 6 := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have h1 : r ≤ θ := min_le_left _ _
    have h2 : r ≤ π / 6 - θ := min_le_right _ _
    constructor <;> linarith [hx.1, hx.2]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := rotBd s a ε) (F := rotF s a ε) (F' := rotF' s a ε) (x₀ := θ) (s := Metric.ball θ r)
    (Metric.ball_mem_nhds θ hrpos)
    (Eventually.of_forall fun x => (measurable_rotF s a ε x).aestronglyMeasurable)
    (integrable_rotF hs ha hε hθ0.le hθ.le) (measurable_rotF' s a ε θ).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
      exact norm_rotF'_le hs ha hε.le (hball x hx).1 (hball x hx).2 ht)
    (integrableOn_rotBd hs hε)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
      exact hasDerivAt_rotF_θ s a ε x t)
  have hint : IntegrableOn (fun t => Complex.I * rotF' s a ε θ t) (Ioi 0) := key.1.const_mul Complex.I
  have hFTC : ∫ t in Ioi (0 : ℝ), Complex.I * rotF' s a ε θ t = 0 := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto (f := rotA s a ε θ) (f' := fun t => Complex.I * rotF' s a ε θ t)
      (a := 0) (m := 0) (continuous_rotA s a ε θ hs).continuousWithinAt
      (fun t ht => hasDerivAt_rotA s a ε θ ht) hint (tendsto_rotA ha hε hθ0.le hθ.le)
    rw [this, rotA_zero s a ε θ hs]; simp
  have hzero : ∫ t in Ioi (0 : ℝ), rotF' s a ε θ t = 0 := by
    have h : ∀ t, rotF' s a ε θ t = -Complex.I * (Complex.I * rotF' s a ε θ t) := fun t => by
      rw [← mul_assoc, neg_mul, ← sq, Complex.I_sq]; simp
    calc ∫ t in Ioi (0 : ℝ), rotF' s a ε θ t
        = ∫ t in Ioi (0 : ℝ), -Complex.I * (Complex.I * rotF' s a ε θ t) := integral_congr_ae (Eventually.of_forall h)
      _ = 0 := by rw [integral_const_mul, hFTC, mul_zero]
  have := key.2
  rw [hzero] at this
  exact this

lemma continuousOn_rotI {s a ε : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hε : 0 < ε) :
    ContinuousOn (rotI s a ε) (Icc 0 (π / 6)) := by
  refine continuousOn_of_dominated (bound := fun t => t ^ (s - 1) * Real.exp (-(ε / 2) * t ^ 2))
    (fun θ hθ => (measurable_rotF s a ε θ).aestronglyMeasurable) ?_ (integrableOn_rotMaj hs hε) ?_
  · intro θ hθ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_rotF ha hε.le hθ.1 hθ.2 ht
  · refine Eventually.of_forall fun t => ?_
    exact continuousOn_of_forall_continuousAt fun θ _ => (hasDerivAt_rotF_θ s a ε θ t).continuousAt

/-- **Rotation of the contour:** `F_ε(0) = F_ε(π/6)`. -/
theorem rot_const {s a ε : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hε : 0 < ε) :
    rotI s a ε 0 = rotI s a ε (π / 6) := by
  have hπ := Real.pi_pos
  have hc := continuousOn_rotI hs ha hε
  have hOpen : ∀ x ∈ Ioo (0 : ℝ) (π / 6), rotI s a ε x = rotI s a ε (π / 12) := by
    intro x hx
    refine (isOpen_Ioo (a := (0 : ℝ)) (b := π / 6)).is_const_of_deriv_eq_zero isPreconnected_Ioo ?_ ?_ hx
      (show π / 12 ∈ Ioo (0 : ℝ) (π / 6) from ⟨by linarith, by linarith⟩)
    · exact fun y hy => (hasDerivAt_rotI hs ha hε hy.1 hy.2).differentiableAt.differentiableWithinAt
    · exact fun y hy => (hasDerivAt_rotI hs ha hε hy.1 hy.2).deriv
  have hcl : IsClosed (Icc (0 : ℝ) (π / 6) ∩ rotI s a ε ⁻¹' {rotI s a ε (π / 12)}) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hsub : closure (Ioo (0 : ℝ) (π / 6)) ⊆ Icc (0 : ℝ) (π / 6) ∩ rotI s a ε ⁻¹' {rotI s a ε (π / 12)} :=
    closure_minimal (fun x hx => ⟨Ioo_subset_Icc_self hx, hOpen x hx⟩) hcl
  rw [closure_Ioo (by linarith)] at hsub
  have h0 := (hsub ⟨le_refl _, by linarith⟩).2
  have h1 := (hsub ⟨by linarith, le_refl _⟩).2
  simp only [mem_preimage, mem_singleton_iff] at h0 h1
  rw [h0, h1]


lemma exp_rot_three : Complex.exp (-(3 * Complex.I * ((π / 6 : ℝ) : ℂ))) = -Complex.I := by
  have : -(3 * Complex.I * ((π / 6 : ℝ) : ℂ)) = -((π / 2 : ℝ) * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_neg, show ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 by push_cast; ring, Complex.exp_pi_div_two_mul_I]
  simp

lemma rotF_pi_six_zero (s a t : ℝ) :
    rotF s a 0 (π / 6) t = Complex.exp (-(Complex.I * ((π / 6 * s : ℝ) : ℂ))) * (((t ^ (s - 1) * Real.exp (-(a * t ^ 3)) : ℝ) : ℂ)) := by
  have hE : rotE s a 0 (π / 6) t = -(Complex.I * ((π / 6 * s : ℝ) : ℂ)) + ((-(a * t ^ 3) : ℝ) : ℂ) := by
    unfold rotE
    rw [exp_rot_three]
    have hI := Complex.I_sq
    push_cast
    linear_combination ((a : ℂ) * (t : ℂ) ^ 3) * hI
  unfold rotF
  rw [hE, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

lemma norm_rotF_pi_six {s a ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    ‖rotF s a ε (π / 6) t‖ ≤ t ^ (s - 1) * Real.exp (-(a * t ^ 3)) := by
  unfold rotF
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Complex.norm_exp, re_rotE]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht.le _)
  have h3 : Real.sin (3 * (π / 6)) = 1 := by
    rw [show 3 * (π / 6) = π / 2 by ring, Real.sin_pi_div_two]
  have : 0 ≤ ε * Real.cos (2 * (π / 6)) * t ^ 2 := by
    have : 0 ≤ Real.cos (2 * (π / 6)) := by
      rw [show 2 * (π / 6) = π / 3 by ring, Real.cos_pi_div_three]; norm_num
    positivity
  rw [h3]; linarith

/-- **Abel limit of the rotated integral:** for `s, a > 0`,
`lim_{ε↓0} F_ε(0) = e^{-iπs/6} ∫_0^∞ t^{s-1} e^{-a t³} dt`. -/
theorem rot_tendsto {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    Tendsto (fun ε : ℝ => rotI s a ε 0) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp (-(Complex.I * ((π / 6 * s : ℝ) : ℂ))) *
        ∫ t in Ioi (0 : ℝ), (((t ^ (s - 1) * Real.exp (-(a * t ^ 3)) : ℝ) : ℂ)))) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(a * t ^ 3))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 3) (s := s - 1) (b := a) (by linarith) (by norm_num) ha
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    have h3 : t ^ (3 : ℝ) = t ^ 3 := by exact_mod_cast Real.rpow_natCast t 3
    beta_reduce
    rw [h3, neg_mul]
  have hlim : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), rotF s a ε (π / 6) t) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Ioi (0 : ℝ), rotF s a 0 (π / 6) t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => t ^ (s - 1) * Real.exp (-(a * t ^ 3)))
      (Eventually.of_forall fun ε => (measurable_rotF s a ε (π / 6)).aestronglyMeasurable) ?_ hint ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_rotF_pi_six (le_of_lt hε) ht
    · refine Eventually.of_forall fun t => ?_
      have : Continuous fun ε : ℝ => rotF s a ε (π / 6) t := by unfold rotF rotE; fun_prop
      exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : (∫ t in Ioi (0 : ℝ), rotF s a 0 (π / 6) t) =
      Complex.exp (-(Complex.I * ((π / 6 * s : ℝ) : ℂ))) *
        ∫ t in Ioi (0 : ℝ), (((t ^ (s - 1) * Real.exp (-(a * t ^ 3)) : ℝ) : ℂ)) := by
    simp_rw [rotF_pi_six_zero]
    rw [integral_const_mul]
  rw [← h2]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (rot_const hs ha.le hε).symm

/-- info: 'FormalResearch.SignUncertainty.FctRot.rot_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rot_tendsto

end FormalResearch.SignUncertainty.FctRot
