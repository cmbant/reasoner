module

public import FormalResearch.CohnElkies.MellinKernel
public import FormalResearch.CohnElkies.MellinPhaseBounds
public import FormalResearch.CohnElkies.ComplexEdgePhase

/-!
# Lemma T.3 completed (`mat:T3`): vertical-line identities and integrated bounds

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.3 (`mat:T3`), parts (3)-(5).
Part (1), (2) and the first identity of part (3) are not proved here (see the report of this
file's task); the strip derivative below is what parts (3)-(5) need.

## Main declarations
* `hasDerivAt_stripS0Tilde`: `d/dζ S̃₀(ζ) = g(ζ)` on the strip `|Re ζ| < 1`, by differentiation
  under the integral sign in `S̃₀(ζ) = ∫₀¹ g(sζ) ζ ds` (no primitive on the strip is assumed).
* `hasDerivAt_stripH`: `ℋ'(ζ) = log(1 - ζ) + g(ζ) + log(π/2)` on `0 < Re ζ < 1`.
* `mellinUpsilon`: `Υ(μ,ν) = Re ℋ(1-μ-iν) + Re(z log z - z) + 1`, `z = μ + iν`.
* `mellinUpsilon_hasDerivAt`: `-∂_ν Υ(1-σ,ν) = Im g(σ+iν)` (part (4), identity).
* `mellinUpsilon_gaussian_bound`: part (4) bound in the `Υ` form.
* `mellinUpsilon_integrated_bound`: part (5) bound in the `Υ` form.
* `mellinUpsilon_zero_eq`: `S₀(σ) = Υ(1-σ,0) = ∫₀^σ log(tan(πt/2)/t) dt` (part (5)).
-/

@[expose] public section

open Set MeasureTheory Filter Topology Metric Complex
open scoped Real Interval

namespace FormalResearch.CohnElkies

/-- Scaling by a real `s ∈ [0,1]` keeps the strip `|Re ζ| < 1`. -/
lemma re_ofReal_mul_abs_lt {s : ℝ} {x : ℂ} (hs : s ∈ Icc (0 : ℝ) 1) (hx : |x.re| < 1) :
    |((s : ℂ) * x).re| < 1 := by
  rw [Complex.re_ofReal_mul, abs_mul, abs_of_nonneg hs.1]
  have := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg x.re)
  linarith

/-- The derivative of the holomorphic `g` is continuous on the strip. -/
lemma continuousOn_deriv_stripG : ContinuousOn (deriv stripG) edgeStrip :=
  (differentiableOn_stripG.deriv isOpen_edgeStrip).continuousOn

/-- `s ↦ g(s x)` is continuous on `[0,1]` when `|Re x| < 1`. -/
lemma continuousOn_stripG_seg {x : ℂ} (hx : |x.re| < 1) :
    ContinuousOn (fun s : ℝ => stripG ((s : ℂ) * x)) (Icc 0 1) := by
  have hc : ContinuousOn (fun s : ℝ => (s : ℂ) * x) (Icc 0 1) :=
    (Complex.continuous_ofReal.mul continuous_const).continuousOn
  exact continuousOn_stripG.comp hc (fun s hs => re_ofReal_mul_abs_lt hs hx)

/-- The integrand of the derivative of `S̃₀`, `s ↦ g'(s x) s x + g(s x)`, is continuous on `[0,1]`. -/
lemma continuousOn_stripS0_deriv_seg {x : ℂ} (hx : |x.re| < 1) :
    ContinuousOn (fun s : ℝ => deriv stripG ((s : ℂ) * x) * (s : ℂ) * x + stripG ((s : ℂ) * x))
      (Icc 0 1) := by
  have hc : ContinuousOn (fun s : ℝ => (s : ℂ) * x) (Icc 0 1) :=
    (Complex.continuous_ofReal.mul continuous_const).continuousOn
  have hd : ContinuousOn (fun s : ℝ => deriv stripG ((s : ℂ) * x)) (Icc 0 1) :=
    continuousOn_deriv_stripG.comp hc (fun s hs => re_ofReal_mul_abs_lt hs hx)
  exact ((hd.mul (Complex.continuous_ofReal.continuousOn)).mul continuousOn_const).add
    (continuousOn_stripG_seg hx)

/-- **Lemma T.3 (vertical derivative of `S̃₀`).** For `|Re ζ₀| < 1`, `S̃₀` is complex
differentiable at `ζ₀` with derivative `g(ζ₀)` (`mat:T3`, used in parts (3)-(5)). Proof: the
integrand `F(ζ,s) = g(sζ) ζ` is differentiated in `ζ` under the integral over `s ∈ [0,1]`, the
derivative is bounded on a closed ball by compactness, and `∫₀¹ (s g(sζ₀))' ds = g(ζ₀)`. -/
theorem hasDerivAt_stripS0Tilde {ζ₀ : ℂ} (h₀ : |ζ₀.re| < 1) :
    HasDerivAt stripS0Tilde (stripG ζ₀) ζ₀ := by
  obtain ⟨δ, hδ0, hρ⟩ : ∃ δ : ℝ, 0 < δ ∧ |ζ₀.re| + δ < 1 :=
    ⟨(1 - |ζ₀.re|) / 2, by linarith, by linarith⟩
  -- points of the closed ball of radius `δ` keep `|Re| ≤ |Re ζ₀| + δ < 1`
  have hball_re : ∀ x ∈ closedBall ζ₀ δ, |x.re| < 1 := by
    intro x hx
    have hx' : ‖x - ζ₀‖ ≤ δ := by simpa [dist_eq_norm] using hx
    have h1 : |x.re - ζ₀.re| ≤ δ := by
      have := Complex.abs_re_le_norm (x - ζ₀)
      rw [Complex.sub_re] at this
      linarith
    have h2 := abs_le.mp h1
    have h3 := le_abs_self ζ₀.re
    have h4 := neg_abs_le ζ₀.re
    rw [abs_lt]
    constructor <;> linarith [h2.1, h2.2]
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ δ) :=
    isCompact_Icc.prod (isCompact_closedBall ζ₀ δ)
  have hq : ContinuousOn (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ δ) :=
    ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd).continuousOn
  have hqmaps : MapsTo (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)
      (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ δ) edgeStrip := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact re_ofReal_mul_abs_lt hs (hball_re x hx)
  have hG : ContinuousOn (fun p : ℝ × ℂ => deriv stripG ((p.1 : ℂ) * p.2) * (p.1 : ℂ) * p.2
      + stripG ((p.1 : ℂ) * p.2)) (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ δ) := by
    have hfst : ContinuousOn (fun p : ℝ × ℂ => (p.1 : ℂ)) (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ δ) :=
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn
    have hd : ContinuousOn (fun p : ℝ × ℂ => deriv stripG ((p.1 : ℂ) * p.2))
        (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ δ) :=
      continuousOn_deriv_stripG.comp hq hqmaps
    have hg : ContinuousOn (fun p : ℝ × ℂ => stripG ((p.1 : ℂ) * p.2))
        (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ δ) :=
      continuousOn_stripG.comp hq hqmaps
    exact ((hd.mul hfst).mul continuousOn_snd).add hg
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hG
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  have hmem : ball ζ₀ δ ∈ 𝓝 ζ₀ := ball_mem_nhds ζ₀ hδ0
  have hball_sub : ball ζ₀ δ ⊆ closedBall ζ₀ δ := ball_subset_closedBall
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
    (F := fun (x : ℂ) (s : ℝ) => stripG ((s : ℂ) * x) * x)
    (F' := fun (x : ℂ) (s : ℝ) => deriv stripG ((s : ℂ) * x) * (s : ℂ) * x + stripG ((s : ℂ) * x))
    (x₀ := ζ₀) (s := ball ζ₀ δ) hmem
    (Filter.eventually_of_mem hmem fun x hx => by
      exact ((((continuousOn_stripG_seg (hball_re x (hball_sub hx))).mul continuousOn_const).mono
        hsub).aestronglyMeasurable measurableSet_uIoc))
    (((continuousOn_stripG_seg h₀).mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
    ((continuousOn_stripS0_deriv_seg h₀).mono hsub |>.aestronglyMeasurable measurableSet_uIoc)
    (ae_of_all _ fun t ht x hx => by
      have htI : t ∈ Icc (0 : ℝ) 1 := hsub ht
      exact hB (t, x) ⟨htI, hball_sub hx⟩)
    intervalIntegrable_const
    (ae_of_all _ fun t ht x hx => by
      have htI : t ∈ Icc (0 : ℝ) 1 := hsub ht
      have hx1 : |x.re| < 1 := hball_re x (hball_sub hx)
      have hmt : ((t : ℂ) * x) ∈ edgeStrip := re_ofReal_mul_abs_lt htI hx1
      have h1 : HasDerivAt (fun y : ℂ => (t : ℂ) * y) (t : ℂ) x := by
        simpa using (hasDerivAt_id x).const_mul (t : ℂ)
      have h2 : HasDerivAt stripG (deriv stripG ((t : ℂ) * x)) ((t : ℂ) * x) :=
        (differentiableOn_stripG.differentiableAt (isOpen_edgeStrip.mem_nhds hmt)).hasDerivAt
      have h3 : HasDerivAt (fun y : ℂ => stripG ((t : ℂ) * y))
          (deriv stripG ((t : ℂ) * x) * (t : ℂ)) x := h2.comp x h1
      have h4 : HasDerivAt (fun y : ℂ => stripG ((t : ℂ) * y) * y)
          (deriv stripG ((t : ℂ) * x) * (t : ℂ) * x + stripG ((t : ℂ) * x) * 1) x :=
        h3.mul (hasDerivAt_id' x)
      exact h4.congr_deriv (by ring))
  -- the derivative of `S̃₀` is the integral of the derivative of the integrand
  have hD : HasDerivAt stripS0Tilde
      (∫ t in (0 : ℝ)..1, deriv stripG ((t : ℂ) * ζ₀) * (t : ℂ) * ζ₀ + stripG ((t : ℂ) * ζ₀)) ζ₀ :=
    key.2
  have hftc : ∫ t in (0 : ℝ)..1, deriv stripG ((t : ℂ) * ζ₀) * (t : ℂ) * ζ₀ + stripG ((t : ℂ) * ζ₀)
      = stripG ζ₀ := by
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun s : ℝ => (s : ℂ) * stripG ((s : ℂ) * ζ₀))
        (deriv stripG ((t : ℂ) * ζ₀) * (t : ℂ) * ζ₀ + stripG ((t : ℂ) * ζ₀)) t := by
      intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
      have hmt : ((t : ℂ) * ζ₀) ∈ edgeStrip := re_ofReal_mul_abs_lt htI h₀
      have ha : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
        simpa using (hasDerivAt_id t).ofReal_comp
      have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * ζ₀) ζ₀ t := by
        simpa using ha.mul_const ζ₀
      have hstrip : HasDerivAt stripG (deriv stripG ((t : ℂ) * ζ₀)) ((t : ℂ) * ζ₀) :=
        (differentiableOn_stripG.differentiableAt (isOpen_edgeStrip.mem_nhds hmt)).hasDerivAt
      have hg := hstrip.scomp t hl
      have hprod : HasDerivAt (fun s : ℝ => (s : ℂ) * stripG ((s : ℂ) * ζ₀))
          (1 * stripG ((t : ℂ) * ζ₀) + (t : ℂ) * (ζ₀ * deriv stripG ((t : ℂ) * ζ₀))) t :=
        ha.mul hg
      exact hprod.congr_deriv (by ring)
    have hint : IntervalIntegrable
        (fun t : ℝ => deriv stripG ((t : ℂ) * ζ₀) * (t : ℂ) * ζ₀ + stripG ((t : ℂ) * ζ₀))
        volume 0 1 :=
      (continuousOn_stripS0_deriv_seg h₀).intervalIntegrable_of_Icc zero_le_one
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  rw [hftc] at hD
  exact hD


/-! ### Derivative of `ℋ` and the function `Υ` (part (4)) -/

lemma re_sigma_add_mul_I (σ t : ℝ) : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp

/-- **Lemma T.3(4) auxiliary (`mat:T3`).** Derivative of `ℋ` on `0 < Re ζ < 1`:
`ℋ'(ζ) = log(1 - ζ) + g(ζ) + log(π/2)` (from `stripH_eq`). -/
theorem hasDerivAt_stripH {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    HasDerivAt stripH (Complex.log (1 - ζ) + stripG ζ + Complex.log ((Real.pi : ℂ) / 2)) ζ := by
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : stripH =ᶠ[𝓝 ζ] fun w : ℂ => -((1 - w) * Complex.log (1 - w) + w)
      + stripS0Tilde w + w * Complex.log ((Real.pi : ℂ) / 2) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with w hw
    exact stripH_eq hw.1.le hw.2
  have hslit : (1 - ζ) ∈ slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))
  have hu : HasDerivAt (fun w : ℂ => 1 - w) (-1) ζ := (hasDerivAt_id ζ).const_sub 1
  have hl : HasDerivAt (fun w : ℂ => Complex.log (1 - w)) ((-1) / (1 - ζ)) ζ := hu.clog hslit
  have hA : HasDerivAt (fun w : ℂ => -((1 - w) * Complex.log (1 - w) + w))
      (-((-1) * Complex.log (1 - ζ) + (1 - ζ) * ((-1) / (1 - ζ)) + 1)) ζ :=
    ((hu.mul hl).add (hasDerivAt_id' ζ)).neg
  have hw : HasDerivAt (fun w : ℂ => w * Complex.log ((Real.pi : ℂ) / 2))
      (Complex.log ((Real.pi : ℂ) / 2)) ζ := by
    simpa using (hasDerivAt_id' ζ).mul_const (Complex.log ((Real.pi : ℂ) / 2))
  have hS : HasDerivAt stripS0Tilde (stripG ζ) ζ :=
    hasDerivAt_stripS0Tilde (by rw [abs_lt]; constructor <;> linarith)
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  refine ((hA.add hS).add hw).congr_deriv ?_
  have hdiv : (1 - ζ) * ((-1) / (1 - ζ)) = -1 := by
    have hne : (1 - ζ) ≠ 0 := Complex.slitPlane_ne_zero hslit
    field_simp
  rw [hdiv]
  ring

/-- `z(w) = (1 - σ) + i w` for complex `w`: the variable of `Υ(1 - σ, ·)`. -/
noncomputable def upsZ (σ : ℝ) (w : ℂ) : ℂ := ((1 - σ : ℝ) : ℂ) + w * Complex.I

theorem hasDerivAt_upsZ (σ : ℝ) (w : ℂ) : HasDerivAt (upsZ σ) Complex.I w := by
  unfold upsZ
  simpa using ((hasDerivAt_id' w).mul_const Complex.I).const_add ((1 - σ : ℝ) : ℂ)

lemma upsZ_re (σ t : ℝ) : (upsZ σ (t : ℂ)).re = 1 - σ := by
  simp [upsZ]

/-- **Lemma T.3(4) function `Υ` (`mat:T3`(4)).** `Υ(μ, ν) = Re 𝓗(1 - μ - iν) + Re(z log z - z) + 1`
at `z = μ + iν`, with the Mellin-strip function `𝓗 = stripH` of `(e33)`. -/
noncomputable def mellinUpsilon (μ ν : ℝ) : ℝ :=
  (stripH (1 - ((μ : ℂ) + (ν : ℂ) * Complex.I))).re
    + (((μ : ℂ) + (ν : ℂ) * Complex.I) * Complex.log ((μ : ℂ) + (ν : ℂ) * Complex.I)
        - ((μ : ℂ) + (ν : ℂ) * Complex.I)).re + 1

/-- `Im log(π/2) = 0`, so `log(π/2)` is real. -/
lemma im_log_pi_div_two : (Complex.log ((Real.pi : ℂ) / 2)).im = 0 := by
  have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.log_im, Complex.arg_ofReal_of_nonneg (by positivity)]

/-- **Lemma T.3(4) identity (`mat:T3`(4)): `-∂_ν Υ(1 - σ, ν) = Im g(σ + iν)`.** For `0 < σ < 1`
and every real `t`, `ν ↦ Υ(1 - σ, ν)` has derivative `-Im g(σ + i t)` at `t`. -/
theorem mellinUpsilon_hasDerivAt {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (t : ℝ) :
    HasDerivAt (fun x : ℝ => mellinUpsilon (1 - σ) x)
      (-(stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im) t := by
  have hzre : (upsZ σ (t : ℂ)).re = 1 - σ := upsZ_re σ t
  have hslit : upsZ σ (t : ℂ) ∈ slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hzre]; linarith))
  have hzne : upsZ σ (t : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hG_re0 : 0 < (1 - upsZ σ (t : ℂ)).re := by simp only [Complex.sub_re, Complex.one_re, hzre]; linarith
  have hG_re1 : (1 - upsZ σ (t : ℂ)).re < 1 := by simp only [Complex.sub_re, Complex.one_re, hzre]; linarith
  have he1 := (hasDerivAt_stripH hG_re0 hG_re1).comp (t : ℂ)
    ((hasDerivAt_upsZ σ (t : ℂ)).const_sub 1)
  rw [sub_sub_cancel] at he1
  have he2 : HasDerivAt (fun w : ℂ => upsZ σ w * Complex.log (upsZ σ w) - upsZ σ w)
      (Complex.I * Complex.log (upsZ σ (t : ℂ))) (t : ℂ) := by
    have hl : HasDerivAt (fun w : ℂ => Complex.log (upsZ σ w))
        (Complex.I / upsZ σ (t : ℂ)) (t : ℂ) := (hasDerivAt_upsZ σ (t : ℂ)).clog hslit
    have h : HasDerivAt (fun w : ℂ => upsZ σ w * Complex.log (upsZ σ w) - upsZ σ w)
        (Complex.I * Complex.log (upsZ σ (t : ℂ)) + upsZ σ (t : ℂ) * (Complex.I / upsZ σ (t : ℂ))
          - Complex.I) (t : ℂ) :=
      ((hasDerivAt_upsZ σ (t : ℂ)).mul hl).sub (hasDerivAt_upsZ σ (t : ℂ))
    refine h.congr_deriv ?_
    have hdiv : upsZ σ (t : ℂ) * (Complex.I / upsZ σ (t : ℂ)) = Complex.I := by
      field_simp
    rw [hdiv]
    ring
  have hsum := (he1.real_of_complex.add he2.real_of_complex).add_const 1
  have hconj : (1 - upsZ σ (t : ℂ)) = (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [upsZ]
  have hcond : |((σ : ℂ) + (t : ℂ) * Complex.I).re| < 1 := by
    rw [re_sigma_add_mul_I σ t, abs_lt]; constructor <;> linarith
  have hG : (stripG (1 - upsZ σ (t : ℂ))).im = -(stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im := by
    rw [hconj, stripG_conj hcond, Complex.conj_im]
  have hval : ((Complex.log (upsZ σ (t : ℂ)) + stripG (1 - upsZ σ (t : ℂ))
        + Complex.log ((Real.pi : ℂ) / 2)) * (-Complex.I)).re
      + (Complex.I * Complex.log (upsZ σ (t : ℂ))).re
      = -(stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im := by
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, im_log_pi_div_two, hG]
    ring
  exact hsum.congr_deriv hval

/-- **Lemma T.3(3) (`mat:T3`, `cel:5.5` identity).** For `0 < σ < 1` and `t > 0`,
`Im g(σ + it) = arctan(sinh(πt)/sin(πσ)) - arctan(t/σ)`. -/
theorem im_stripG_eq {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 0 < t) :
    (stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im =
      Real.arctan (Real.sinh (π * t) / Real.sin (π * σ)) - Real.arctan (t / σ) := by
  have hne : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  unfold stripG
  simp only [hne, ↓reduceIte]
  exact im_log_tan_div_eq hσ0 hσ1 ht

/-- **Lemma T.3(4) bound in the `Υ` form (`mat:T3`(4)).** For `0 < σ ≤ 1/2`, `ν > 0`:
`-∂_ν Υ(1 - σ, ν) ≥ 2 κ_V σ min(ν, 1/ν)` with `κ_V = 3/56`. -/
theorem mellinUpsilon_gaussian_bound {σ ν : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hν : 0 < ν) :
    2 * (3 / 56 : ℝ) * σ * min ν ν⁻¹ ≤ -deriv (fun x : ℝ => mellinUpsilon (1 - σ) x) ν := by
  rw [(mellinUpsilon_hasDerivAt hσ0 (by linarith) ν).deriv, neg_neg,
    im_stripG_eq hσ0 (by linarith) hν]
  exact im_stripG_ge_gaussian hσ0 hσ1 hν

lemma stripG_ofReal_im {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : (stripG (x : ℂ)).im = 0 := by
  rw [stripG_ofReal h0 h1, Complex.ofReal_im]

lemma stripS0Tilde_zero : stripS0Tilde 0 = 0 := by
  simp [stripS0Tilde]

/-- **Lemma T.3(5) integrated bound in the `Υ` form (`mat:T3`(5)).** For `0 < σ ≤ 1/2`, `ν > 0`:
`Υ(1-σ,0) - Υ(1-σ,ν) ≥ 2 κ_V σ [ (1/2) min(ν², 1) + log₊ ν ]`. -/
theorem mellinUpsilon_integrated_bound {σ ν : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hν : 0 < ν) :
    2 * (3 / 56 : ℝ) * σ * ((1 / 2 : ℝ) * min (ν ^ 2) 1 + max 0 (Real.log ν))
      ≤ mellinUpsilon (1 - σ) 0 - mellinUpsilon (1 - σ) ν := by
  have hσ1' : σ < 1 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => (stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im)
      (uIcc 0 ν) := by
    have hc : ContinuousOn (fun t : ℝ => stripG ((σ : ℂ) + (t : ℂ) * Complex.I)) (uIcc 0 ν) := by
      refine continuousOn_stripG.comp
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn) ?_
      intro t _
      show |((σ : ℂ) + (t : ℂ) * Complex.I).re| < 1
      rw [re_sigma_add_mul_I σ t, abs_lt]
      constructor <;> linarith
    exact Complex.continuous_im.comp_continuousOn hc
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) ν, HasDerivAt (fun x : ℝ => mellinUpsilon (1 - σ) x)
      (-(stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im) t :=
    fun t _ => mellinUpsilon_hasDerivAt hσ0 hσ1' t
  have hint : IntervalIntegrable
      (fun t : ℝ => -(stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im) volume 0 ν :=
    (hcont.neg).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : ∫ t in (0 : ℝ)..ν, (stripG ((σ : ℂ) + (t : ℂ) * Complex.I)).im =
      ∫ t in (0 : ℝ)..ν, (Real.arctan (Real.sinh (π * t) / Real.sin (π * σ))
        - Real.arctan (t / σ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hν.le] at ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      have hz0 : (σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = (σ : ℂ) := by simp
      show (stripG ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)).im = _
      rw [hz0, stripG_ofReal_im hσ0 hσ1']
      simp
    · exact im_stripG_eq hσ0 hσ1' h
  have hlow := integral_im_stripG_ge hσ0 hσ1 hν
  rw [intervalIntegral.integral_neg, hcongr] at hFTC
  linarith


/-- **Lemma T.3(5) identity (`mat:T3`(5)): `S₀(σ) = Υ(1 - σ, 0) = ∫₀^σ log(tan(πt/2)/t) dt`**
for `0 < σ < 1`. Proof: `ℋ(σ)` from `stripH_eq`, and `S̃₀` on the real segment by the
fundamental theorem of calculus for `hasDerivAt_stripS0Tilde`. -/
theorem mellinUpsilon_zero_eq {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    mellinUpsilon (1 - σ) 0 = ∫ t in (0 : ℝ)..σ, Real.log (Real.tan (Real.pi * t / 2) / t) := by
  have hH := stripH_eq (ζ := (σ : ℂ)) (by simpa using h0.le) (by simpa using h1)
  have hl1 : Complex.log (1 - (σ : ℂ)) = ((Real.log (1 - σ) : ℝ) : ℂ) := by
    rw [show (1 - (σ : ℂ)) = ((1 - σ : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_log (by linarith)]
  have hlc : Complex.log ((Real.pi : ℂ) / 2) = ((Real.log (Real.pi / 2) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_log (by positivity)]
  have hre : (stripH (σ : ℂ)).re = -((1 - σ) * Real.log (1 - σ) + σ)
      + (stripS0Tilde (σ : ℂ)).re + σ * Real.log (Real.pi / 2) := by
    rw [hH, hl1, hlc]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im, mul_zero, sub_zero,
      sub_self]
  -- `S̃₀` along the real segment
  have hu : ∀ x ∈ uIcc (0 : ℝ) σ, |x| < 1 := by
    intro x hx
    rw [uIcc_of_le h0.le] at hx
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hcont : ContinuousOn (fun x : ℝ => (stripG (x : ℂ)).re) (uIcc 0 σ) := by
    have hc : ContinuousOn (fun x : ℝ => stripG (x : ℂ)) (uIcc 0 σ) :=
      continuousOn_stripG.comp (Complex.continuous_ofReal.continuousOn) (fun x hx => by
        show |((x : ℂ)).re| < 1
        simpa using hu x hx)
    exact Complex.continuous_re.comp_continuousOn hc
  have hR : ∀ x ∈ uIcc (0 : ℝ) σ,
      HasDerivAt (fun y : ℝ => (stripS0Tilde (y : ℂ)).re) (stripG (x : ℂ)).re x := by
    intro x hx
    have hx1 : |((x : ℂ)).re| < 1 := by simpa using hu x hx
    exact (hasDerivAt_stripS0Tilde hx1).real_of_complex
  have hS_int : ∫ t in (0 : ℝ)..σ, (stripG (t : ℂ)).re = (stripS0Tilde (σ : ℂ)).re := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hR hcont.intervalIntegrable]
    simp [stripS0Tilde_zero]
  -- the integrand on `(0, σ]`
  have hintg : ∫ t in (0 : ℝ)..σ, Real.log (Real.tan (Real.pi * t / 2) / t)
      = ∫ t in (0 : ℝ)..σ, ((stripG (t : ℂ)).re + Real.log (Real.pi / 2)) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    have ht' : t ∈ Ioc (0 : ℝ) σ := by rwa [uIoc_of_le h0.le] at ht
    have htpos : 0 < t := ht'.1
    have hst : (stripG (t : ℂ)).re
        = Real.log (Real.tan (Real.pi * t / 2) / (Real.pi * t / 2)) := by
      rw [stripG_ofReal_re htpos (by linarith [ht'.2]), stripGReal]
      simp only [htpos.ne', ↓reduceIte]
    have ht1 : t < 1 := by linarith [ht'.2]
    have hA : 0 < Real.tan (Real.pi * t / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [Real.pi_pos])
    have hq : 0 < Real.tan (Real.pi * t / 2) / (Real.pi * t / 2) := div_pos hA (by positivity)
    show Real.log (Real.tan (Real.pi * t / 2) / t)
      = (stripG (t : ℂ)).re + Real.log (Real.pi / 2)
    rw [hst, ← Real.log_mul hq.ne' (by positivity)]
    congr 1
    field_simp
  have hsplit : ∫ t in (0 : ℝ)..σ, ((stripG (t : ℂ)).re + Real.log (Real.pi / 2))
      = (stripS0Tilde (σ : ℂ)).re + σ * Real.log (Real.pi / 2) := by
    rw [intervalIntegral.integral_add hcont.intervalIntegrable intervalIntegrable_const, hS_int]
    simp
  rw [hintg, hsplit]
  -- assemble `Υ(1 - σ, 0)`
  have hz : (((1 - σ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = ((1 - σ : ℝ) : ℂ) := by simp
  have hz1 : (1 - (((1 - σ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) = (σ : ℂ) := by
    push_cast
    ring
  unfold mellinUpsilon
  rw [hz1, hz, hre]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.log_ofReal_re,
    Complex.ofReal_im, sub_zero, zero_mul]
  ring


/-- info: 'FormalResearch.CohnElkies.hasDerivAt_stripS0Tilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.hasDerivAt_stripS0Tilde

/-- info: 'FormalResearch.CohnElkies.hasDerivAt_stripH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.hasDerivAt_stripH

/-- info: 'FormalResearch.CohnElkies.mellinUpsilon_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.mellinUpsilon_hasDerivAt

/-- info: 'FormalResearch.CohnElkies.im_stripG_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.im_stripG_eq

/-- info: 'FormalResearch.CohnElkies.mellinUpsilon_gaussian_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.mellinUpsilon_gaussian_bound

/-- info: 'FormalResearch.CohnElkies.mellinUpsilon_integrated_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.mellinUpsilon_integrated_bound

/-- info: 'FormalResearch.CohnElkies.mellinUpsilon_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.mellinUpsilon_zero_eq

end FormalResearch.CohnElkies
