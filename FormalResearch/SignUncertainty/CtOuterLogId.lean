module

public import FormalResearch.SignUncertainty.CtOuterBdryIm

/-!
# The explicit strip integral of `log(t) + ½log(1+t²)`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (3): `h̃ - h = log(√(π²/6) ζ(1-ζ))`.
**Proved.**  For `ζ` in the open strip, `∫ w(t)/sin(π(ζ-it)) dt = Log ζ + Log(1-ζ) + ½ log(π²/6)` with
`w(t) = ½ log((π²/6) t² (1+t²))` (a Cauchy-rectangle argument for the regularised `g_δ(z) = Log(z+δ) + Log(1+δ-z) + c`,
then `δ ↓ 0`).  Together with `tendsto_im_genH` this gives `∫ (w(t) - w(τ))/sinh(π(t-τ)) dt = π/2 - arctan τ`
for `τ > 0`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOuter

lemma integrable_sech : Integrable fun t : ℝ => 1 / Real.cosh (π * t) := by
  have hint := (integrable_exp_neg_abs' (c := π) Real.pi_pos).const_mul 2
  refine Integrable.mono' hint ?_ (Eventually.of_forall fun t => ?_)
  · exact (Continuous.div continuous_const (by fun_prop) (fun t => (Real.cosh_pos _).ne')).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have hc : Real.exp (π * |t|) / 2 ≤ Real.cosh (π * t) := by
      have : Real.cosh (π * t) = Real.cosh (π * |t|) := by
        rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
        · rw [h, mul_neg, Real.cosh_neg]
      rw [this, Real.cosh_eq]
      have := Real.exp_pos (-(π * |t|))
      linarith
    rw [one_div]
    calc (Real.cosh (π * t))⁻¹ ≤ (Real.exp (π * |t|) / 2)⁻¹ := inv_anti₀ (by positivity) hc
      _ = 2 * Real.exp (-π * |t|) := by rw [neg_mul, Real.exp_neg]; field_simp

lemma integral_sech : ∫ t : ℝ, 1 / Real.cosh (π * t) = 1 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 2 / π * Real.arctan (Real.exp (π * t)))
      (1 / Real.cosh (π * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (π * t)) (Real.exp (π * t) * π) t :=
      ((Real.hasDerivAt_exp (π * t)).comp t ((hasDerivAt_id t).const_mul π)).congr_deriv (by simp)
    have h2 := ((Real.hasDerivAt_arctan (Real.exp (π * t))).comp t h1).const_mul (2 / π)
    refine h2.congr_deriv ?_
    have hpi := Real.pi_pos.ne'
    have hE := (Real.exp_pos (π * t)).ne'
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  have hbot : Tendsto (fun t : ℝ => 2 / π * Real.arctan (Real.exp (π * t))) atBot (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (π * t)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_const_mul_atBot_of_pos Real.pi_pos |>.mpr tendsto_id)
    have h2 := (Real.continuous_arctan.tendsto 0).comp h1
    simpa using h2.const_mul (2 / π)
  have htop : Tendsto (fun t : ℝ => 2 / π * Real.arctan (Real.exp (π * t))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (π * t)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)
    have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    have h3 := h2.const_mul (2 / π)
    have : 2 / π * (π / 2) = 1 := by field_simp
    rwa [this] at h3
  have := integral_of_hasDerivAt_of_tendsto hd integrable_sech hbot htop
  simpa using this

/-- `∫_ℝ kern0(ζ, t) dt = 1` on the open strip. -/
theorem integral_kern0_eq_one {ζ : ℂ} (hζ : ζ ∈ strip) : ∫ t : ℝ, kern0 ζ t = 1 := by
  -- the function `ζ ↦ ∫ kern0` has derivative `∫ kern1 = 0`
  have hJ : ∀ z ∈ strip, HasDerivAt (genH (fun _ => (1 : ℝ))) 0 z := by
    intro z hz
    have h := hasDerivAt_genH (v := fun _ => (1 : ℝ)) continuous_const
      ⟨1, fun t => by simp [Real.one_le_exp (abs_nonneg t)]⟩ hz
    have e : (∫ t : ℝ, (((fun _ => (1 : ℝ)) t : ℝ) : ℂ) * kern1 z t) = 0 := by
      simpa using integral_kern1_eq_zero hz
    rwa [e] at h
  have hconst : genH (fun _ => (1 : ℝ)) ζ = genH (fun _ => (1 : ℝ)) (1 / 2 : ℂ) := by
    have hs : IsPreconnected strip := by
      have : Convex ℝ strip := (convex_Ioo (0 : ℝ) 1).linear_preimage (Complex.reCLM.toLinearMap)
      exact this.isPreconnected
    refine IsOpen.is_const_of_deriv_eq_zero isOpen_strip hs
      (fun z hz => (hJ z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hJ z hz).deriv) hζ ?_
    exact ⟨by norm_num, by norm_num⟩
  have hhalf : genH (fun _ => (1 : ℝ)) (1 / 2 : ℂ) = 1 := by
    unfold genH
    have e : ∀ t : ℝ, (((fun _ => (1 : ℝ)) t : ℝ) : ℂ) * kern0 (1 / 2 : ℂ) t = ((1 / Real.cosh (π * t) : ℝ) : ℂ) := by
      intro t
      simp only [Complex.ofReal_one, one_mul, kern0]
      have : (π : ℂ) * ((1 / 2 : ℂ) - Complex.I * t) = (π / 2 : ℂ) - ((π * t : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.sin_pi_div_two_sub, Complex.cos_mul_I, ← Complex.ofReal_cosh]
      simp
    simp_rw [e]
    rw [integral_complex_ofReal, integral_sech]
    simp
  have : ∫ t : ℝ, kern0 ζ t = genH (fun _ => (1 : ℝ)) ζ := by
    unfold genH; simp
  rw [this, hconst, hhalf]


/-- **Equality of the two vertical boundary integrals** of a function holomorphic on the closed strip
and decaying on horizontal sections (Cauchy's theorem on rectangles, `Y → ∞`). -/
theorem vertical_lines_eq {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f closedStrip) {B : ℝ → ℝ}
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B y)
    (hBint : Integrable B) (hB1 : Tendsto B atTop (𝓝 0)) (hB2 : Tendsto B atBot (𝓝 0)) :
    ∫ y : ℝ, f (1 + (y : ℂ) * Complex.I) = ∫ y : ℝ, f ((y : ℂ) * Complex.I) := by
  have hcont : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Continuous fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x hx
    refine hd.continuousOn.comp_continuous (by fun_prop) (fun y => ?_)
    exact ⟨by simpa using hx.1, by simpa using hx.2⟩
  have hint : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Integrable fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x hx
    exact Integrable.mono' hBint (hcont x hx).aestronglyMeasurable (Eventually.of_forall fun y => hB x hx y)
  have hrect : ∀ Y : ℝ, 0 < Y →
      (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (-Y : ℝ) * Complex.I)) - (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (Y : ℝ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-Y)..Y, f ((1 : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ in (-Y)..Y, f ((0 : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro Y hY
    have hsub : [[((-Y : ℝ) * Complex.I : ℂ).re, ((1 : ℂ) + (Y : ℝ) * Complex.I).re]] ×ℂ
        [[((-Y : ℝ) * Complex.I : ℂ).im, ((1 : ℂ) + (Y : ℝ) * Complex.I).im]] ⊆ closedStrip := by
      intro z hz
      have h1 := hz.1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, Complex.add_re, Complex.one_re] at h1
      rw [Set.uIcc_of_le (by norm_num)] at h1
      exact ⟨h1.1, by simpa using h1.2⟩
    have := integral_boundary_rect_eq_zero_of_differentiableOn f ((-Y : ℝ) * Complex.I) ((1 : ℂ) + (Y : ℝ) * Complex.I)
      (hd.mono hsub)
    simpa using this
  -- limits
  have hH1 : Tendsto (fun Y : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (-Y : ℝ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun Y => ?_) (hB2.comp tendsto_neg_atTop_atBot)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := B (-Y)) (f := fun x : ℝ => f ((x : ℂ) + (-Y : ℝ) * Complex.I)) (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        exact hB x ⟨hx.1.le, hx.2⟩ (-Y))
    simpa using this
  have hH2 : Tendsto (fun Y : ℝ => ∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (Y : ℝ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun Y => ?_) hB1
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := B Y) (f := fun x : ℝ => f ((x : ℂ) + (Y : ℝ) * Complex.I)) (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num)] at hx
        exact hB x ⟨hx.1.le, hx.2⟩ Y)
    simpa using this
  have hV1 : Tendsto (fun Y : ℝ => ∫ y : ℝ in (-Y)..Y, f ((1 : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f (1 + (y : ℂ) * Complex.I))) := by
    have h := hint 1 ⟨by norm_num, le_rfl⟩
    simp only [Complex.ofReal_one] at h
    exact intervalIntegral_tendsto_integral h tendsto_neg_atTop_atBot tendsto_id
  have hV0 : Tendsto (fun Y : ℝ => ∫ y : ℝ in (-Y)..Y, f ((0 : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((y : ℂ) * Complex.I))) := by
    have h := hint 0 ⟨le_rfl, by norm_num⟩
    simp only [Complex.ofReal_zero, zero_add] at h ⊢
    exact intervalIntegral_tendsto_integral h tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hH1.sub hH2).add (hV1.const_mul Complex.I)).sub (hV0.const_mul Complex.I)
  have hev : (fun Y : ℝ => (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (-Y : ℝ) * Complex.I)) -
      (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + (Y : ℝ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-Y)..Y, f ((1 : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-Y)..Y, f ((0 : ℂ) + (y : ℂ) * Complex.I))) =ᶠ[atTop] fun _ => (0 : ℂ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY using hrect Y hY
  have h0 := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  simp only [zero_sub] at h0
  have : Complex.I * ((∫ y : ℝ, f (1 + (y : ℂ) * Complex.I)) - ∫ y : ℝ, f ((y : ℂ) * Complex.I)) = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h Complex.I_ne_zero
  · exact sub_eq_zero.mp h


lemma norm_log_le (w : ℂ) : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + π := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re]
  have := Complex.abs_arg_le_pi w
  rw [Complex.log_im]
  linarith only [this]

lemma exp_div_four_le_sinh {t : ℝ} (ht : 1 ≤ t) : Real.exp t / 4 ≤ Real.sinh t := by
  rw [Real.sinh_eq]
  have h1 : (2 : ℝ) ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t)
    linarith only [this, ht]
  have h2 : Real.exp (2 * t) = Real.exp t * Real.exp t := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos t
  have hE' := Real.exp_pos (-t)
  nlinarith only [h1, h2, h3, hE, hE']

lemma sin_lower {u : ℂ} (hu : 1 ≤ |u.im|) : Real.exp (π * |u.im|) / 4 ≤ ‖Complex.sin (π * u)‖ := by
  have h1 := norm_sin_sq (π * u)
  have him : (↑π * u).im = π * u.im := by simp [Complex.mul_im]
  rw [him] at h1
  have habs : |π * u.im| = π * |u.im| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  have hge : 1 ≤ π * |u.im| := by nlinarith only [Real.pi_gt_three, hu]
  have h2 := exp_div_four_le_sinh hge
  have h3 : Real.sinh (π * |u.im|) = |Real.sinh (π * u.im)| := by rw [abs_sinh_pi]
  have h4 : ‖Complex.sin (↑π * u)‖ ^ 2 ≥ Real.sinh (π * u.im) ^ 2 := by
    rw [h1]; nlinarith only [sq_nonneg (Real.sin (π * u).re)]
  have h5 : |Real.sinh (π * u.im)| ≤ ‖Complex.sin (↑π * u)‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [sq_abs]; exact h4
  rw [← h3] at h5
  exact h2.trans h5


/-- `c = ½ log(π²/6)`. -/
noncomputable def cLog : ℝ := (1 / 2) * Real.log (π ^ 2 / 6)

/-- The regularised logarithm `g_δ(z) = Log(z+δ) + Log(1+δ-z) + c`. -/
noncomputable def gδ (δ : ℝ) (z : ℂ) : ℂ :=
  Complex.log (z + δ) + Complex.log (1 + δ - z) + (cLog : ℂ)

/-- Its real part on the imaginary axis. -/
noncomputable def aδ (δ t : ℝ) : ℝ :=
  (1 / 2) * Real.log (δ ^ 2 + t ^ 2) + (1 / 2) * Real.log ((1 + δ) ^ 2 + t ^ 2) + cLog

lemma re_log_eq (a b : ℝ) (h : 0 < a ^ 2 + b ^ 2) :
    (Complex.log ((a : ℂ) + (b : ℂ) * Complex.I)).re = (1 / 2) * Real.log (a ^ 2 + b ^ 2) := by
  rw [Complex.log_re]
  have : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_add_mul_I]
  rw [this, Real.log_sqrt h.le]
  ring

lemma re_gδ_imag {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : (gδ δ ((t : ℂ) * Complex.I)).re = aδ δ t := by
  unfold gδ aδ
  have e1 : (t : ℂ) * Complex.I + (δ : ℂ) = (δ : ℂ) + (t : ℂ) * Complex.I := by ring
  have e2 : (1 : ℂ) + (δ : ℂ) - (t : ℂ) * Complex.I = ((1 + δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [e1, e2, re_log_eq δ t (by positivity), re_log_eq (1 + δ) (-t) (by positivity)]
  simp

lemma gδ_one_add {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    gδ δ (1 + (y : ℂ) * Complex.I) = starRingEnd ℂ (gδ δ ((y : ℂ) * Complex.I)) := by
  unfold gδ
  have e1 : (1 : ℂ) + (y : ℂ) * Complex.I + (δ : ℂ) = starRingEnd ℂ ((1 + δ : ℝ) + ((-y : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  have e2 : (1 : ℂ) + (δ : ℂ) - (1 + (y : ℂ) * Complex.I) = starRingEnd ℂ ((δ : ℂ) + (y : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  have e3 : (y : ℂ) * Complex.I + (δ : ℂ) = (δ : ℂ) + (y : ℂ) * Complex.I := by ring
  have e4 : (1 : ℂ) + (δ : ℂ) - (y : ℂ) * Complex.I = ((1 + δ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e3, e4]
  have a1 : ((1 + δ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I = ((1 : ℂ) + δ - y * Complex.I) := by
    push_cast; ring
  rw [map_add, map_add, Complex.conj_ofReal]
  have h1 : (starRingEnd ℂ) (Complex.log ((δ : ℂ) + (y : ℂ) * Complex.I)) =
      Complex.log (starRingEnd ℂ ((δ : ℂ) + (y : ℂ) * Complex.I)) := by
    rw [Complex.log_conj]
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    simp at this
    linarith [this.1]
  have h2 : (starRingEnd ℂ) (Complex.log (((1 + δ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) =
      Complex.log (starRingEnd ℂ (((1 + δ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.log_conj]
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    simp at this
    linarith [this.1]
  rw [h1, h2]
  have e5 : starRingEnd ℂ (((1 + δ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) = (1 : ℂ) + (y : ℂ) * Complex.I + (δ : ℂ) := by
    apply Complex.ext <;> simp
  rw [e5, e2]
  ring


lemma dslope_sin_ne {u : ℂ} (hu : |u.re| < 1) :
    dslope (fun u : ℂ => Complex.sin (π * u)) 0 u ≠ 0 := by
  by_cases h0 : u = 0
  · subst h0
    rw [dslope_same]
    have : HasDerivAt (fun u : ℂ => Complex.sin (π * u)) (Complex.cos (π * 0) * π) 0 := by
      have h1 : HasDerivAt (fun u : ℂ => (π : ℂ) * u) (π : ℂ) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)
      exact h1.csin
    rw [this.deriv]
    simp [Real.pi_pos.ne']
  · rw [dslope_of_ne _ h0, slope_def_field]
    have hs : Complex.sin (π * u) ≠ 0 := by
      intro h
      have h1 := norm_sin_sq (π * u)
      rw [h, norm_zero] at h1
      have hre : (↑π * u).re = π * u.re := by simp [Complex.mul_re]
      have him : (↑π * u).im = π * u.im := by simp [Complex.mul_im]
      rw [hre, him] at h1
      have h2 : Real.sin (π * u.re) = 0 := by nlinarith only [h1, sq_nonneg (Real.sin (π * u.re)), sq_nonneg (Real.sinh (π * u.im))]
      have h3 : Real.sinh (π * u.im) = 0 := by nlinarith only [h1, sq_nonneg (Real.sin (π * u.re)), sq_nonneg (Real.sinh (π * u.im))]
      have hr : u.re = 0 := by
        have := (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos, (abs_lt.mp hu).1])
          (by nlinarith [Real.pi_pos, (abs_lt.mp hu).2])).mp h2
        exact (mul_eq_zero.mp this).resolve_left Real.pi_pos.ne'
      have hi : u.im = 0 := by
        have := Real.sinh_eq_zero.mp h3
        exact (mul_eq_zero.mp this).resolve_left Real.pi_pos.ne'
      exact h0 (Complex.ext hr hi)
    simpa using div_ne_zero hs h0

/-- The function with the removable singularity at `ζ` removed. -/
noncomputable def fδ (δ : ℝ) (ζ z : ℂ) : ℂ :=
  dslope (gδ δ) ζ z / dslope (fun u : ℂ => Complex.sin (π * u)) 0 (z - ζ)

lemma fδ_eq {δ : ℝ} {ζ z : ℂ} (hz : z ≠ ζ) :
    fδ δ ζ z = (gδ δ z - gδ δ ζ) / Complex.sin (π * (z - ζ)) := by
  unfold fδ
  have hz' : z - ζ ≠ 0 := sub_ne_zero.mpr hz
  rw [dslope_of_ne _ hz, dslope_of_ne _ hz', slope_def_field, slope_def_field]
  simp only [sub_zero, mul_zero, Complex.sin_zero]
  by_cases hs : Complex.sin (π * (z - ζ)) = 0
  · simp [hs]
  · field_simp


lemma differentiableOn_gδ {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (gδ δ) {z : ℂ | -(δ / 2) < z.re ∧ z.re < 1 + δ / 2} := by
  intro z hz
  have h1 : (z + (δ : ℂ)) ∈ slitPlane := Or.inl (by simp; linarith [hz.1])
  have h2 : ((1 : ℂ) + δ - z) ∈ slitPlane := Or.inl (by simp; linarith [hz.2])
  have l1 := (differentiableAt_id.add_const (δ : ℂ)).clog h1
  have l2 := ((differentiableAt_const ((1 : ℂ) + δ)).sub differentiableAt_id).clog h2
  unfold gδ
  exact ((l1.add l2).add_const _).differentiableWithinAt

lemma differentiableOn_fδ {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ} (hζ : ζ ∈ strip) :
    DifferentiableOn ℂ (fδ δ ζ) closedStrip := by
  set s : Set ℂ := {z : ℂ | -(δ / 2) < z.re ∧ z.re < 1 + δ / 2} with hs
  have hso : IsOpen s := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hζs : ζ ∈ s := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  have h1 : DifferentiableOn ℂ (dslope (gδ δ) ζ) s :=
    (differentiableOn_dslope (hso.mem_nhds hζs)).mpr (differentiableOn_gδ hδ)
  have h2 : Differentiable ℂ (dslope (fun u : ℂ => Complex.sin (π * u)) 0) := by
    have : DifferentiableOn ℂ (dslope (fun u : ℂ => Complex.sin (π * u)) 0) univ :=
      (differentiableOn_dslope Filter.univ_mem).mpr (by
        refine Differentiable.differentiableOn ?_
        fun_prop)
    exact differentiableOn_univ.mp this
  have hsub : closedStrip ⊆ s := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  intro z hz
  unfold fδ
  refine DifferentiableWithinAt.div ((h1.mono hsub) z hz) ?_ ?_
  · exact ((h2 (z - ζ)).comp z ((differentiableAt_id.sub_const ζ))).differentiableWithinAt
  · apply dslope_sin_ne
    have : (z - ζ).re = z.re - ζ.re := by simp
    rw [this, abs_lt]
    constructor <;> linarith [hz.1, hz.2, hζ.1, hζ.2]


lemma norm_gδ_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (y : ℝ) :
    ‖gδ δ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (2 * (|Real.log δ| + π) + |cLog|) + 2 * Real.log (3 + |y|) := by
  have hlog3 : 0 ≤ Real.log (3 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
  have hb : ∀ w : ℂ, δ ≤ ‖w‖ → ‖w‖ ≤ 3 + |y| → ‖Complex.log w‖ ≤ |Real.log δ| + Real.log (3 + |y|) + π := by
    intro w h1 h2
    have := norm_log_le w
    have hw : 0 < ‖w‖ := lt_of_lt_of_le hδ h1
    have h3 : |Real.log ‖w‖| ≤ |Real.log δ| + Real.log (3 + |y|) := by
      rw [abs_le]
      constructor
      · have := Real.log_le_log hδ h1
        linarith [neg_abs_le (Real.log δ)]
      · have := Real.log_le_log hw h2
        linarith [le_abs_self (Real.log δ), abs_nonneg (Real.log δ)]
    linarith only [this, h3]
  have n1 : δ ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I + (δ : ℂ)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp; linarith
  have n1' : ‖(x : ℂ) + (y : ℂ) * Complex.I + (δ : ℂ)‖ ≤ 3 + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : ((x : ℂ) + (y : ℂ) * Complex.I + (δ : ℂ)).re = x + δ := by simp
    have e2 : ((x : ℂ) + (y : ℂ) * Complex.I + (δ : ℂ)).im = y := by simp
    rw [e1, e2, abs_of_nonneg (by linarith)]
    linarith
  have n2 : δ ≤ ‖(1 : ℂ) + (δ : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp; linarith
  have n2' : ‖(1 : ℂ) + (δ : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 3 + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : ((1 : ℂ) + (δ : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)).re = 1 + δ - x := by simp
    have e2 : ((1 : ℂ) + (δ : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I)).im = -y := by simp
    rw [e1, e2, abs_of_nonneg (by linarith), abs_neg]
    linarith
  unfold gδ
  have := hb _ n1 n1'
  have := hb _ n2 n2'
  have hc : ‖(cLog : ℂ)‖ = |cLog| := by simp
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [hc]
  linarith


lemma fδ_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ζ : ℂ} (hζ : ζ ∈ strip) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y : ℝ,
      ‖fδ δ ζ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * ((1 + Real.log (3 + |y|)) * Real.exp (-π * |y|)) := by
  have hd := differentiableOn_fδ hδ hζ
  set η : ℝ := ζ.im with hη
  have hR : (Icc (0 : ℝ) 1 ×ℂ Icc (η - 1) (η + 1)) ⊆ closedStrip := fun z hz => ⟨hz.1.1, hz.1.2⟩
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn
    (hd.continuousOn.mono hR)
  set A : ℝ := (2 * (|Real.log δ| + π) + |cLog|) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set Aζ : ℝ := ‖gδ δ ζ‖ with hAζ
  have hK0 : 0 ≤ K₁ := by
    have := hK₁ (0 + (η : ℂ) * Complex.I) ⟨⟨by simp, by simp⟩, by simp⟩
    exact (norm_nonneg _).trans this
  refine ⟨max (K₁ * Real.exp (π * (|η| + 1))) (4 * Real.exp (π * |η|) * (A + Aζ + 2)), by positivity, ?_⟩
  intro x hx y
  have hL3 : 0 ≤ Real.log (3 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
  have hE : 0 < Real.exp (-π * |y|) := Real.exp_pos _
  by_cases hnear : |y - η| < 1
  · have hmem : ((x : ℂ) + (y : ℂ) * Complex.I) ∈ (Icc (0 : ℝ) 1 ×ℂ Icc (η - 1) (η + 1)) := by
      refine ⟨by simpa using hx, ?_⟩
      have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
      show ((x : ℂ) + (y : ℂ) * Complex.I).im ∈ Icc (η - 1) (η + 1)
      rw [him]
      constructor <;> linarith [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
    have h1 := hK₁ _ hmem
    have hy : |y| ≤ |η| + 1 := by
      calc |y| = |(y - η) + η| := by ring_nf
        _ ≤ |y - η| + |η| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hlow : Real.exp (-π * (|η| + 1)) ≤ Real.exp (-π * |y|) :=
      Real.exp_le_exp.mpr (by nlinarith only [hy, Real.pi_pos])
    have hprod : Real.exp (-π * (|η| + 1)) ≤ (1 + Real.log (3 + |y|)) * Real.exp (-π * |y|) := by
      calc _ ≤ Real.exp (-π * |y|) := hlow
        _ ≤ (1 + Real.log (3 + |y|)) * Real.exp (-π * |y|) := by nlinarith only [hL3, hE]
    have hexp : K₁ ≤ K₁ * Real.exp (π * (|η| + 1)) * Real.exp (-π * (|η| + 1)) := by
      rw [mul_assoc, ← Real.exp_add, show π * (|η| + 1) + -π * (|η| + 1) = 0 by ring, Real.exp_zero, mul_one]
    calc ‖fδ δ ζ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K₁ := h1
      _ ≤ K₁ * Real.exp (π * (|η| + 1)) * Real.exp (-π * (|η| + 1)) := hexp
      _ ≤ K₁ * Real.exp (π * (|η| + 1)) * ((1 + Real.log (3 + |y|)) * Real.exp (-π * |y|)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hfar : 1 ≤ |y - η| := not_lt.mp hnear
    set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
    have hzne : z ≠ ζ := by
      intro h
      have : y = η := by
        have h1 := congrArg Complex.im h
        have h2 : z.im = y := by simp [hz]
        rw [h2] at h1
        exact h1
      rw [this, sub_self, abs_zero] at hfar
      exact absurd hfar (by norm_num)
    rw [fδ_eq hzne, norm_div]
    have him : (z - ζ).im = y - η := by simp [hz, hη]
    have hsin := sin_lower (u := z - ζ) (by rw [him]; exact hfar)
    rw [him] at hsin
    have hpos : 0 < Real.exp (π * |y - η|) / 4 := by positivity
    have hg := norm_gδ_le hδ hδ1 hx.1 hx.2 y
    have hnum : ‖gδ δ z - gδ δ ζ‖ ≤ (A + Aζ + 2) * (1 + Real.log (3 + |y|)) := by
      refine (norm_sub_le _ _).trans ?_
      rw [← hA] at hg
      nlinarith only [hg, hA0, norm_nonneg (gδ δ ζ), hL3]
    have hexp : Real.exp (-π * |y - η|) ≤ Real.exp (π * |η|) * Real.exp (-π * |y|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : |y| ≤ |y - η| + |η| := by
        calc |y| = |(y - η) + η| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      nlinarith only [this, Real.pi_pos]
    calc ‖gδ δ z - gδ δ ζ‖ / ‖Complex.sin (↑π * (z - ζ))‖
        ≤ ((A + Aζ + 2) * (1 + Real.log (3 + |y|))) / (Real.exp (π * |y - η|) / 4) := by
          apply div_le_div₀ (by positivity) hnum hpos hsin
      _ = 4 * (A + Aζ + 2) * (1 + Real.log (3 + |y|)) * Real.exp (-π * |y - η|) := by
          rw [neg_mul, Real.exp_neg]; field_simp
      _ ≤ 4 * (A + Aζ + 2) * (1 + Real.log (3 + |y|)) * (Real.exp (π * |η|) * Real.exp (-π * |y|)) := by
          apply mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (4 * Real.exp (π * |η|) * (A + Aζ + 2)) * ((1 + Real.log (3 + |y|)) * Real.exp (-π * |y|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)


lemma aδ_bound_ne {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {y : ℝ} (hy0 : y ≠ 0) :
    |aδ δ y| ≤ (3 + |cLog|) * wlog y := by
  have hw : 1 ≤ wlog y := by unfold wlog; linarith [abs_nonneg (Real.log (|y|)), abs_nonneg y]
  have hlogy : |Real.log (|y|)| ≤ wlog y := by unfold wlog; linarith [abs_nonneg y]
  have hy : |y| ≤ wlog y := by unfold wlog; linarith [abs_nonneg (Real.log (|y|))]
  have h1 : (1 / 2 : ℝ) * Real.log (y ^ 2) ≤ (1 / 2) * Real.log (δ ^ 2 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg δ])
  have h2 : (1 / 2 : ℝ) * Real.log (δ ^ 2 + y ^ 2) ≤ (1 / 2) * Real.log (1 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg δ])
  have h3 : (1 / 2 : ℝ) * Real.log (1 + y ^ 2) ≤ |y| := by
    have := log_one_add_sq_le y; linarith
  have h4 : (1 / 2 : ℝ) * Real.log (y ^ 2) = Real.log (|y|) := by
    rw [Real.log_pow]; push_cast; rw [Real.log_abs]; ring
  have h5 : (1 / 2 : ℝ) * Real.log (1 + y ^ 2) ≤ (1 / 2) * Real.log ((1 + δ) ^ 2 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.log_le_log (by positivity) (by nlinarith)
  have h6 : (1 / 2 : ℝ) * Real.log ((1 + δ) ^ 2 + y ^ 2) ≤ 1 + |y| := by
    have hle : (1 + δ) ^ 2 + y ^ 2 ≤ 4 * (1 + y ^ 2) := by nlinarith
    have h7 := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (by positivity)] at h7
    have h8 : Real.log 4 ≤ 2 := by
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      linarith
    have := log_one_add_sq_le y
    linarith
  have h0 : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + y ^ 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + y ^ 2 by nlinarith [sq_nonneg y]); linarith
  unfold aδ
  rw [abs_le]
  have hc := abs_nonneg cLog
  have hlg := abs_nonneg (Real.log δ)
  have hcl := neg_abs_le cLog
  have hcl' := le_abs_self cLog
  have hly := neg_abs_le (Real.log (|y|))
  constructor <;> nlinarith only [h1, h2, h3, h4, h5, h6, h0, hw, hlogy, hy, hc, hlg, hcl, hcl', hly]

lemma aδ_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (y : ℝ) :
    |aδ δ y| ≤ (3 + |cLog| + |Real.log δ|) * wlog y := by
  have hw : 1 ≤ wlog y := by unfold wlog; linarith [abs_nonneg (Real.log (|y|)), abs_nonneg y]
  have hlogy : |Real.log (|y|)| ≤ wlog y := by unfold wlog; linarith [abs_nonneg y]
  have hy : |y| ≤ wlog y := by unfold wlog; linarith [abs_nonneg (Real.log (|y|))]
  by_cases hy0 : y = 0
  · subst hy0
    unfold aδ
    have h1 : |Real.log (1 + δ)| ≤ 1 := by
      rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + δ by linarith)
      linarith
    have e1 : (1 / 2 : ℝ) * Real.log (δ ^ 2 + 0 ^ 2) = Real.log δ := by
      rw [show δ ^ 2 + (0 : ℝ) ^ 2 = δ ^ 2 by ring, Real.log_pow]; push_cast; ring
    have e2 : (1 / 2 : ℝ) * Real.log ((1 + δ) ^ 2 + 0 ^ 2) = Real.log (1 + δ) := by
      rw [show (1 + δ) ^ 2 + (0 : ℝ) ^ 2 = (1 + δ) ^ 2 by ring, Real.log_pow]; push_cast; ring
    rw [e1, e2]
    have : wlog 0 = 1 := by simp [wlog]
    rw [this]
    calc |Real.log δ + Real.log (1 + δ) + cLog| ≤ |Real.log δ| + |Real.log (1 + δ)| + |cLog| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ (3 + |cLog| + |Real.log δ|) * 1 := by linarith
  · have := aδ_bound_ne hδ.le hδ1 hy0
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
    linarith [abs_nonneg (Real.log δ)]

/-- `(1 + log(3+|y|)) e^{-π|y|}`. -/
noncomputable def bshape (y : ℝ) : ℝ := (1 + Real.log (3 + |y|)) * Real.exp (-π * |y|)

lemma bshape_le (y : ℝ) : bshape y ≤ 4 * Real.exp (-π * |y|) + |y| * Real.exp (-π * |y|) := by
  unfold bshape
  have h1 : Real.log (3 + |y|) ≤ 3 + |y| := Real.log_le_self (by positivity)
  have := Real.exp_pos (-π * |y|)
  nlinarith only [h1, this]

lemma bshape_nonneg (y : ℝ) : 0 ≤ bshape y := by
  unfold bshape
  have : 0 ≤ Real.log (3 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
  positivity

lemma integrable_bshape : Integrable bshape := by
  have h := ((integrable_exp_neg_abs' Real.pi_pos).const_mul 4).add (integrable_abs_exp Real.pi_pos)
  refine Integrable.mono' h ?_ (Eventually.of_forall fun y => ?_)
  · have : Continuous bshape := by
      unfold bshape
      refine Continuous.mul (continuous_const.add (Continuous.log (by fun_prop) (fun y => by positivity))) (by fun_prop)
    exact this.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (bshape_nonneg y)]
    exact bshape_le y

lemma bshape_neg (y : ℝ) : bshape (-y) = bshape y := by simp [bshape]

lemma tendsto_bshape : Tendsto bshape atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.exp (-π * y)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop Real.pi_pos)
    refine this.congr (fun y => ?_)
    simp [neg_mul]
  have h2 : Tendsto (fun y : ℝ => y * Real.exp (-π * y)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop Real.pi_pos)
    have h' := h.const_mul (1 / π)
    simp only [pow_one, mul_zero, Function.comp] at h'
    refine h'.congr (fun y => ?_)
    have := Real.pi_pos.ne'
    rw [show -π * y = -(π * y) by ring]
    simp only [id]
    field_simp
  have h3 := (h1.const_mul 4).add h2
  simp only [mul_zero, add_zero] at h3
  refine squeeze_zero' (Eventually.of_forall bshape_nonneg) ?_ h3
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  have := bshape_le y
  rwa [abs_of_nonneg hy] at this

lemma tendsto_bshape_atBot : Tendsto bshape atBot (𝓝 0) := by
  have := tendsto_bshape.comp tendsto_neg_atBot_atTop
  refine this.congr (fun y => ?_)
  simp [bshape_neg]


lemma integrable_kern0_const {ζ : ℂ} (hζ : ζ ∈ strip) :
    ∃ C : ℝ, ∀ t : ℝ, ‖kern0 ζ t‖ ≤ C * Real.exp (-π * |t|) := by
  obtain ⟨r, hr, C, hC0, hrs, hCb⟩ := kern_ball_bound hζ
  exact ⟨C, fun t => by simpa [neg_mul] using (hCb ζ (mem_ball_self hr) t).1⟩

/-- **The regularised logarithm identity**: `∫ a_δ(t) kern0(ζ,t) dt = g_δ(ζ)` on the open strip. -/
theorem genH_aδ {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ζ : ℂ} (hζ : ζ ∈ strip) :
    genH (aδ δ) ζ = gδ δ ζ := by
  obtain ⟨C, hC0, hC⟩ := fδ_bound hδ hδ1 hζ
  have hd := differentiableOn_fδ hδ hζ
  have hBd : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y : ℝ,
      ‖fδ δ ζ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * bshape y := fun x hx y => hC x hx y
  have hv := vertical_lines_eq hd hBd (integrable_bshape.const_mul C)
    (by simpa using tendsto_bshape.const_mul C) (by simpa using tendsto_bshape_atBot.const_mul C)
  have hcont : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 → Continuous fun y : ℝ => fδ δ ζ ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x hx
    refine hd.continuousOn.comp_continuous (by fun_prop) (fun y => ?_)
    exact ⟨by simpa using hx.1, by simpa using hx.2⟩
  have hint : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 →
      Integrable fun y : ℝ => fδ δ ζ ((x : ℂ) + (y : ℂ) * Complex.I) := fun x hx =>
    Integrable.mono' (integrable_bshape.const_mul C) (hcont x hx).aestronglyMeasurable
      (Eventually.of_forall fun y => hBd x hx y)
  have h1 := hint 1 ⟨by norm_num, le_rfl⟩
  have h0 := hint 0 ⟨le_rfl, by norm_num⟩
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_add] at h1 h0
  -- pointwise identity
  have hS : ∀ y : ℝ, Complex.sin (π * (ζ - Complex.I * y)) ≠ 0 := fun y => sin_arg_ne_zero y hζ
  have hpt : ∀ y : ℝ, fδ δ ζ (1 + (y : ℂ) * Complex.I) - fδ δ ζ ((y : ℂ) * Complex.I) =
      (((2 * aδ δ y : ℝ) : ℂ) - 2 * gδ δ ζ) * kern0 ζ y := by
    intro y
    have hz1 : (1 : ℂ) + (y : ℂ) * Complex.I ≠ ζ := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hζ.2]
    have hz0 : (y : ℂ) * Complex.I ≠ ζ := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hζ.1]
    rw [fδ_eq hz1, fδ_eq hz0]
    have s1 : Complex.sin (π * ((1 : ℂ) + (y : ℂ) * Complex.I - ζ)) = Complex.sin (π * (ζ - Complex.I * y)) := by
      rw [show (π : ℂ) * ((1 : ℂ) + (y : ℂ) * Complex.I - ζ) = π - π * (ζ - Complex.I * y) by ring,
        Complex.sin_pi_sub]
    have s0 : Complex.sin (π * ((y : ℂ) * Complex.I - ζ)) = -Complex.sin (π * (ζ - Complex.I * y)) := by
      rw [show (π : ℂ) * ((y : ℂ) * Complex.I - ζ) = -(π * (ζ - Complex.I * y)) by ring, Complex.sin_neg]
    rw [s1, s0]
    have hSy := hS y
    have hg : gδ δ (1 + (y : ℂ) * Complex.I) + gδ δ ((y : ℂ) * Complex.I) = ((2 * aδ δ y : ℝ) : ℂ) := by
      rw [gδ_one_add hδ y, add_comm, Complex.add_conj, ← re_gδ_imag hδ y]
    unfold kern0
    rw [← hg]
    field_simp
    ring
  have hI : ∫ y : ℝ, (fδ δ ζ (1 + (y : ℂ) * Complex.I) - fδ δ ζ ((y : ℂ) * Complex.I)) = 0 := by
    rw [integral_sub h1 h0, hv, sub_self]
  simp_rw [hpt] at hI
  -- integrability of the two pieces
  obtain ⟨Ck, hCk⟩ := integrable_kern0_const hζ
  have hkc := continuous_kern0 hζ
  have iA : Integrable fun y : ℝ => ((aδ δ y : ℝ) : ℂ) * kern0 ζ y :=
    integrable_amp_mul_k (a := aδ δ) (by unfold aδ; exact (by fun_prop : Measurable fun y : ℝ => (1 / 2 : ℝ) * Real.log (δ ^ 2 + y ^ 2) + (1 / 2) * Real.log ((1 + δ) ^ 2 + y ^ 2) + cLog))
      (aδ_bound hδ hδ1) hkc.aestronglyMeasurable Real.pi_pos hCk
  have iK : Integrable fun y : ℝ => kern0 ζ y := by
    have := integrable_amp_mul_k (a := fun _ => (1 : ℝ)) measurable_const (M := 1)
      (fun t => by simp [wlog]; linarith [abs_nonneg (Real.log t), abs_nonneg t]) hkc.aestronglyMeasurable Real.pi_pos hCk
    simpa using this
  have e : ∀ y : ℝ, (((2 * aδ δ y : ℝ) : ℂ) - 2 * gδ δ ζ) * kern0 ζ y =
      2 * (((aδ δ y : ℝ) : ℂ) * kern0 ζ y) - 2 * gδ δ ζ * kern0 ζ y := fun y => by push_cast; ring
  simp_rw [e] at hI
  rw [integral_sub (iA.const_mul 2) (iK.const_mul _), integral_const_mul, integral_const_mul,
    integral_kern0_eq_one hζ] at hI
  unfold genH
  have : 2 * (∫ y : ℝ, ((aδ δ y : ℝ) : ℂ) * kern0 ζ y) = 2 * gδ δ ζ := by
    linear_combination hI
  exact mul_left_cancel₀ two_ne_zero this


/-- `w(t) = log|t| + ½ log(1+t²) + ½ log(π²/6) = ½ log((π²/6) t² (1+t²))`. -/
noncomputable def wpl (t : ℝ) : ℝ := Real.log (|t|) + (1 / 2) * Real.log (1 + t ^ 2) + cLog

lemma aδ_zero (t : ℝ) : aδ 0 t = wpl t := by
  unfold aδ wpl
  have h1 : (1 / 2 : ℝ) * Real.log ((0 : ℝ) ^ 2 + t ^ 2) = Real.log (|t|) := by
    rw [show (0 : ℝ) ^ 2 + t ^ 2 = t ^ 2 by ring, Real.log_pow, Real.log_abs]; push_cast; ring
  rw [h1]
  simp

lemma wpl_bound (t : ℝ) : |wpl t| ≤ (3 + |cLog|) * wlog t := by
  by_cases h : t = 0
  · subst h
    simp [wpl, wlog]
  · rw [← aδ_zero]
    exact aδ_bound_ne le_rfl (by norm_num) h

/-- **`∫ w(t)/sin(π(ζ-it)) dt = Log ζ + Log(1-ζ) + ½ log(π²/6)`** on the open strip. -/
theorem genH_wpl {ζ : ℂ} (hζ : ζ ∈ strip) :
    genH wpl ζ = Complex.log ζ + Complex.log (1 - ζ) + (cLog : ℂ) := by
  obtain ⟨Ck, hCk⟩ := integrable_kern0_const hζ
  have hkc := continuous_kern0 hζ
  have hCk0 : 0 ≤ Ck := by
    have := (norm_nonneg (kern0 ζ 0)).trans (hCk 0)
    simpa using this
  have hmeas : ∀ δ : ℝ, Measurable (aδ δ) := fun δ => by
    unfold aδ; fun_prop
  have hlim : Tendsto (fun δ : ℝ => genH (aδ δ) ζ) (𝓝[>] 0) (𝓝 (genH wpl ζ)) := by
    unfold genH
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ((3 + |cLog|) * Ck) * (wlog y * Real.exp (-π * |y|))) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun δ => ((Complex.measurable_ofReal.comp (hmeas δ)).aestronglyMeasurable.mul
        hkc.aestronglyMeasurable)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
      have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
        simpa using (Set.countable_singleton (0 : ℝ)).ae_notMem volume
      filter_upwards [hne] with y hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hw : 0 ≤ wlog y := by unfold wlog; positivity
      calc |aδ δ y| * ‖kern0 ζ y‖ ≤ ((3 + |cLog|) * wlog y) * (Ck * Real.exp (-π * |y|)) :=
            mul_le_mul (aδ_bound_ne hδ.1.le hδ.2.le hy) (hCk y) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · exact ((integrable_wlog_exp Real.pi_pos).const_mul ((3 + |cLog|) * Ck))
    · have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
        simpa using (Set.countable_singleton (0 : ℝ)).ae_notMem volume
      filter_upwards [hne] with y hy
      have hc : ContinuousAt (fun δ : ℝ => aδ δ y) 0 := by
        unfold aδ
        have h1 : ContinuousAt (fun δ : ℝ => Real.log (δ ^ 2 + y ^ 2)) 0 :=
          ContinuousAt.log (by fun_prop) (by positivity)
        have h2 : ContinuousAt (fun δ : ℝ => Real.log ((1 + δ) ^ 2 + y ^ 2)) 0 :=
          ContinuousAt.log (by fun_prop) (by positivity)
        exact ((continuousAt_const.mul h1).add (continuousAt_const.mul h2)).add continuousAt_const
      have := (Complex.continuous_ofReal.continuousAt.comp hc).tendsto.mul_const (kern0 ζ y)
      simp only [Function.comp] at this
      rw [aδ_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun δ : ℝ => gδ δ ζ) (𝓝[>] 0) (𝓝 (Complex.log ζ + Complex.log (1 - ζ) + (cLog : ℂ))) := by
    have hs1 : ζ ∈ slitPlane := Or.inl hζ.1
    have hs2 : (1 - ζ) ∈ slitPlane := Or.inl (by simp; linarith [hζ.2])
    have c1 : ContinuousAt (fun δ : ℝ => Complex.log (ζ + (δ : ℂ))) 0 :=
      ContinuousAt.clog (by fun_prop) (by simpa using hs1)
    have c2 : ContinuousAt (fun δ : ℝ => Complex.log (1 + (δ : ℂ) - ζ)) 0 :=
      ContinuousAt.clog (by fun_prop) (by simpa using hs2)
    have := ((c1.add c2).add (continuousAt_const (y := (cLog : ℂ)))).tendsto
    simp only [Pi.add_apply, Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique (hlim.congr' ?_) hg
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  exact (genH_aδ hδ.1 hδ.2.le hζ)


lemma arg_one_sub_I_mul {τ : ℝ} : Complex.arg (1 - Complex.I * (τ : ℂ)) = -Real.arctan τ := by
  rw [Complex.arg_of_re_nonneg (by simp)]
  have hn : ‖(1 : ℂ) - Complex.I * (τ : ℂ)‖ = Real.sqrt (1 + τ ^ 2) := by
    have : (1 : ℂ) - Complex.I * (τ : ℂ) = (1 : ℝ) + ((-τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_def, Complex.normSq_add_mul_I]
    congr 1; ring
  rw [hn, Real.arctan_eq_arcsin, ← Real.arcsin_neg]
  simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add, zero_sub]
  rw [neg_div]

lemma wpl_lipschitz {τ : ℝ} (hτ : 0 < τ) :
    ∃ L : ℝ, ∀ t : ℝ, |t - τ| ≤ τ / 2 → |wpl t - wpl τ| ≤ L * |t - τ| := by
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt wpl (1 / t + t / (1 + t ^ 2)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => Real.log (|s|)) (1 / t) t := by
      have : (fun s : ℝ => Real.log (|s|)) =ᶠ[𝓝 t] Real.log := by
        filter_upwards [Ioi_mem_nhds ht] with s hs using by simp [abs_of_pos (mem_Ioi.mp hs)]
      have h0 : HasDerivAt Real.log (1 / t) t := by simpa [one_div] using Real.hasDerivAt_log ht.ne'
      exact h0.congr_of_eventuallyEq this
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s ^ 2)) (2 * t / (1 + t ^ 2)) t := by
      have h3 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
        simpa using ((hasDerivAt_pow 2 t).const_add 1)
      exact h3.log (by positivity)
    have := (h1.add (h2.const_mul (1 / 2))).add_const cLog
    unfold wpl
    refine this.congr_deriv ?_
    ring
  -- bound the derivative on [τ/2, 3τ/2]
  have hb : ∀ t ∈ Icc (τ / 2) (3 * τ / 2), |1 / t + t / (1 + t ^ 2)| ≤ 2 / τ + 2 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : 1 / t ≤ 2 / τ := by
      rw [div_le_div_iff₀ ht0 hτ]; nlinarith [ht.1]
    have h2 : t / (1 + t ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (t - 1)]
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine ⟨2 / τ + 2, fun t ht => ?_⟩
  have hmem : ∀ x : ℝ, |x - τ| ≤ τ / 2 → x ∈ Icc (τ / 2) (3 * τ / 2) := fun x hx =>
    ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := wpl) (f' := fun t => 1 / t + t / (1 + t ^ 2))
    (s := Icc (τ / 2) (3 * τ / 2)) (C := 2 / τ + 2)
    (fun y hy => (hd y (by linarith [hy.1])).hasDerivWithinAt)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hb y hy) (convex_Icc _ _)
    (x := τ) (y := t) (hmem τ (by simp; linarith)) (hmem t ht)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this


lemma measurable_wpl : Measurable wpl := by
  unfold wpl
  have : Measurable fun t : ℝ => Real.log (|t|) := Real.measurable_log.comp measurable_abs
  fun_prop

/-- **`∫ (w(t) - w(τ))/sinh(π(t-τ)) dt = π/2 - arctan τ`** for `τ > 0` (`w = ½ log((π²/6) t² (1+t²))`). -/
theorem bdryF_wpl {τ : ℝ} (hτ : 0 < τ) : bdryF wpl τ = π / 2 - Real.arctan τ := by
  obtain ⟨L, hL⟩ := wpl_lipschitz hτ
  have h1 := tendsto_im_genH measurable_wpl wpl_bound (half_pos hτ) hL
  have h2 : Tendsto (fun σ : ℝ => (genH wpl ((σ : ℂ) + Complex.I * τ)).im) (𝓝[>] 0) (𝓝 (π / 2 - Real.arctan τ)) := by
    have hI : (Complex.I * (τ : ℂ)) ∈ slitPlane := Or.inr (by simp; exact hτ.ne')
    have hI' : (1 - Complex.I * (τ : ℂ)) ∈ slitPlane := Or.inl (by simp)
    have c1 : ContinuousAt (fun σ : ℝ => Complex.arg ((σ : ℂ) + Complex.I * τ)) 0 :=
      (Complex.continuousAt_arg (by simpa using hI)).comp (f := fun σ : ℝ => (σ : ℂ) + Complex.I * τ)
        (by fun_prop)
    have c2 : ContinuousAt (fun σ : ℝ => Complex.arg (1 - ((σ : ℂ) + Complex.I * τ))) 0 :=
      (Complex.continuousAt_arg (by simpa using hI')).comp (f := fun σ : ℝ => 1 - ((σ : ℂ) + Complex.I * τ))
        (by fun_prop)
    have := (c1.add c2).tendsto
    have e0 : Complex.arg (((0 : ℝ) : ℂ) + Complex.I * τ) + Complex.arg (1 - (((0 : ℝ) : ℂ) + Complex.I * τ)) =
        π / 2 - Real.arctan τ := by
      have a1 : Complex.arg (((0 : ℝ) : ℂ) + Complex.I * τ) = π / 2 := by
        apply Complex.arg_eq_pi_div_two_iff.mpr; simp [hτ]
      rw [a1, show (1 : ℂ) - (((0 : ℝ) : ℂ) + Complex.I * τ) = 1 - Complex.I * τ by simp, arg_one_sub_I_mul]
      ring
    simp only [Pi.add_apply] at this
    rw [e0] at this
    refine (this.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
    have hζ : ((σ : ℂ) + Complex.I * τ) ∈ strip := ⟨by simpa using hσ.1, by simpa using hσ.2⟩
    rw [genH_wpl hζ]
    simp [Complex.log_im]
  exact tendsto_nhds_unique h1 h2

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_kern0_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_kern0_eq_one

/-- info: 'FormalResearch.SignUncertainty.CtOuter.vertical_lines_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vertical_lines_eq

/-- info: 'FormalResearch.SignUncertainty.CtOuter.genH_aδ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms genH_aδ

/-- info: 'FormalResearch.SignUncertainty.CtOuter.genH_wpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms genH_wpl

/-- info: 'FormalResearch.SignUncertainty.CtOuter.bdryF_wpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bdryF_wpl

end FormalResearch.SignUncertainty.CtOuter
