module

public import Mathlib
public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.HankelBesselMellin
public import FormalResearch.SignUncertainty.CtOuterParam

/-!
# The Hankel--Gaussian modular identity (`ct:boas`, Step 1; `gt:7.9a` Gaussian identity)

Sources: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:boas` Step 1, and
`general_theorems.tex`, `gt:7.9a`.  **Proved.**

* `hankel_laplace_complex`: for `c > 1/2`, `Δ ≥ 0`, `Re p > 0`,
  `∫_0^∞ e^{-ps} ρ₀(s) φ_c(Δ s) ds = (2π/p)^c e^{-4π²Δ/p}` (the analytic continuation of the
  real-`p` identity `hankel_laplace` = the Gaussian identity `ĝ_b = b^{-c} g_{1/b}`, `p = 2πb`).
* `hankelF c f z = ∫_0^∞ f ρ₀ e^{2πizs} ds` and, for `f ∈ 𝒜_c^ε` (`IsHankelEigenfn`),
  the exact modular identity `F(z) = ε(-iz)^{-c} F(-1/z)` on `Im z > 0` (`hankelF_modular`),
  its boundary form on `ℝ∖{0}` (`hankelF_modular_real`) and
  `|F(x)| ≤ M[f] |x|^{-c}` (`hankelF_bound`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty.HankelModular

/-- The weighted kernel `s ↦ ρ₀(s) φ_c(Δ s)` (real). -/
noncomputable def gK (c Δ s : ℝ) : ℝ := hankelRho0 c s * hankelPhi c (Δ * s)

lemma measurable_rho0 (c : ℝ) : Measurable (hankelRho0 c) := by
  unfold hankelRho0
  exact measurable_const.mul (measurable_id.pow_const _)

lemma measurable_gK (c Δ : ℝ) : Measurable (gK c Δ) :=
  (measurable_rho0 c).mul ((hankelPhi_continuous c).comp (continuous_const.mul continuous_id)).measurable

lemma integrableOn_exp_rho0_pos {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => Real.exp (-(a * s)) * hankelRho0 c s) (Ioi 0) := by
  have hI : IntegrableOn (fun x : ℝ => x ^ (c - 1) * Real.exp (-a * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := c - 1) (b := a) (by linarith) one_pos ha
  have this : IntegrableOn (fun x : ℝ => ((2 * π) ^ c / Real.Gamma c) *
      (x ^ (c - 1) * Real.exp (-a * x ^ (1 : ℝ)))) (Ioi 0) := Integrable.const_mul hI _
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  simp only [hankelRho0, Real.rpow_one]
  ring_nf

lemma norm_gK_le {c : ℝ} (hc : 1 / 2 < c) (Δ s : ℝ) (hs : 0 < s) : |gK c Δ s| ≤ hankelRho0 c s := by
  unfold gK
  have h0 : 0 ≤ hankelRho0 c s := (hankelRho0_pos (by linarith) hs).le
  rw [abs_mul, abs_of_nonneg h0]
  calc hankelRho0 c s * |hankelPhi c (Δ * s)| ≤ hankelRho0 c s * 1 :=
        mul_le_mul_of_nonneg_left (abs_hankelPhi_le_one hc _) h0
    _ = _ := mul_one _

/-- Left side of the complex Laplace identity. -/
noncomputable def laplaceL (c Δ : ℝ) (p : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), Complex.exp (-(p * s)) * (gK c Δ s : ℂ)

/-- Right side of the complex Laplace identity. -/
noncomputable def laplaceR (c Δ : ℝ) (p : ℂ) : ℂ :=
  (((2 * π : ℝ) : ℂ) / p) ^ (c : ℂ) * Complex.exp (-(((4 * π ^ 2 * Δ : ℝ) : ℂ) / p))

lemma laplaceL_diff {c : ℝ} (hc : 1 / 2 < c) (Δ : ℝ) :
    DifferentiableOn ℂ (laplaceL c Δ) {p : ℂ | 0 < p.re} := by
  have hc0 : 0 < c := by linarith
  refine CtOuter.differentiableOn_integral_param (μ := volume.restrict (Ioi (0 : ℝ)))
    (Φ := fun p s => Complex.exp (-(p * s)) * (gK c Δ s : ℂ)) (isOpen_lt continuous_const Complex.continuous_re)
    ?_ ?_ ?_
  · intro w _
    exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
      (Complex.measurable_ofReal.comp (measurable_gK c Δ)).aestronglyMeasurable
  · exact ae_of_all _ fun s => by
      refine Differentiable.differentiableOn ?_
      exact ((differentiable_id.mul_const _).neg.cexp).mul_const _
  · intro w0 hw0
    have hw0' : 0 < w0.re := hw0
    refine ⟨w0.re / 2, by positivity, fun s => Real.exp (-((w0.re / 2) * s)) * hankelRho0 c s,
      integrableOn_exp_rho0_pos hc0 (by positivity), ?_⟩
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun s hs w hw => ?_
    have hs' : 0 < s := hs
    have hre : w0.re / 2 ≤ w.re := by
      have h1 : |w.re - w0.re| ≤ ‖w - w0‖ := by
        simpa using Complex.abs_re_le_norm (w - w0)
      have h2 : ‖w - w0‖ < w0.re / 2 := by simpa [dist_eq_norm] using hw
      have := (abs_le.mp h1).1
      linarith
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have h3 : (-(w * (s : ℂ))).re = -(w.re * s) := by simp
    rw [h3]
    have h4 : Real.exp (-(w.re * s)) ≤ Real.exp (-((w0.re / 2) * s)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc Real.exp (-(w.re * s)) * |gK c Δ s| ≤ Real.exp (-((w0.re / 2) * s)) * hankelRho0 c s :=
        mul_le_mul h4 (norm_gK_le hc Δ s hs') (abs_nonneg _) (Real.exp_pos _).le

lemma laplaceR_diff (c Δ : ℝ) : DifferentiableOn ℂ (laplaceR c Δ) {p : ℂ | 0 < p.re} := by
  intro p hp
  have hp' : 0 < p.re := hp
  have hp0 : p ≠ 0 := fun h => by rw [h] at hp'; simp at hp'
  have h1 : DifferentiableAt ℂ (fun p : ℂ => ((2 * π : ℝ) : ℂ) / p) p :=
    (differentiableAt_const _).div differentiableAt_id hp0
  have hslit : (((2 * π : ℝ) : ℂ) / p) ∈ Complex.slitPlane := by
    refine Or.inl ?_
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have : 0 < Complex.normSq p := Complex.normSq_pos.mpr hp0
    positivity
  have h2 := DifferentiableAt.cpow h1 (differentiableAt_const (c : ℂ)) hslit
  have h3 : DifferentiableAt ℂ (fun p : ℂ => Complex.exp (-(((4 * π ^ 2 * Δ : ℝ) : ℂ) / p))) p :=
    (((differentiableAt_const _).div differentiableAt_id hp0).neg).cexp
  exact (h2.mul h3).differentiableWithinAt

lemma laplace_real {c : ℝ} (hc : 1 / 2 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) {q : ℝ} (hq : 0 < q) :
    laplaceL c Δ (q : ℂ) = laplaceR c Δ (q : ℂ) := by
  have hc0 : 0 < c := by linarith
  unfold laplaceL laplaceR
  have e : ∀ s : ℝ, Complex.exp (-((q : ℂ) * s)) * (gK c Δ s : ℂ) =
      ((Real.exp (-(q * s)) * gK c Δ s : ℝ) : ℂ) := by
    intro s; push_cast; ring_nf
  simp_rw [e]
  rw [integral_complex_ofReal]
  have h := hankel_laplace hc0 hΔ hq
  have h' : ∫ s in Ioi (0 : ℝ), Real.exp (-(q * s)) * gK c Δ s =
      (2 * π / q) ^ c * Real.exp (-(4 * π ^ 2 * Δ / q)) := h
  rw [h']
  have hb : (0 : ℝ) ≤ 2 * π / q := by positivity
  have e2 : (((2 * π : ℝ) : ℂ) / (q : ℂ)) = ((2 * π / q : ℝ) : ℂ) := by push_cast; ring
  rw [e2, ← Complex.ofReal_cpow hb, ← Complex.ofReal_div, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  push_cast
  rfl

/-- **Complex Hankel--Gaussian (Laplace) identity**: for `c > 1/2`, `Δ ≥ 0`, `Re p > 0`,
`∫_0^∞ e^{-ps} ρ₀(s) φ_c(Δ s) ds = (2π/p)^c e^{-4π²Δ/p}` (principal power). -/
theorem hankel_laplace_complex {c : ℝ} (hc : 1 / 2 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) {p : ℂ}
    (hp : 0 < p.re) :
    ∫ s in Ioi (0 : ℝ), Complex.exp (-(p * s)) * (hankelRho0 c s * hankelPhi c (Δ * s) : ℝ) =
      (((2 * π : ℝ) : ℂ) / p) ^ (c : ℂ) * Complex.exp (-(((4 * π ^ 2 * Δ : ℝ) : ℂ) / p)) := by
  have hU : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {p : ℂ | 0 < p.re} := convex_halfSpace_re_gt 0
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), laplaceL c Δ z = laplaceR c Δ z := by
    have ht : Tendsto (fun q : ℝ => (q : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with q hq
        simpa using hq
    refine ht.frequently ?_
    have : ∀ᶠ q in 𝓝[≠] (1 : ℝ), 0 < q :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    exact (this.mono fun q hq => laplace_real hc hΔ hq).frequently
  have := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    ((laplaceL_diff hc Δ).analyticOnNhd hU) ((laplaceR_diff c Δ).analyticOnNhd hU)
    hconv.isPreconnected (show (1 : ℂ) ∈ {p : ℂ | 0 < p.re} by simp) hfreq hp
  exact this

/-- The exponential `e^{2πizs}`. -/
noncomputable def eK (z : ℂ) (s : ℝ) : ℂ := Complex.exp (2 * (π : ℂ) * Complex.I * z * (s : ℂ))

lemma norm_eK (z : ℂ) (s : ℝ) : ‖eK z s‖ = Real.exp (-(2 * π * z.im * s)) := by
  unfold eK
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma continuous_eK (s : ℝ) : Continuous (fun z : ℂ => eK z s) := by
  unfold eK; fun_prop

/-- `F(z) = ∫_0^∞ f(s) ρ₀(s) e^{2πizs} ds`. -/
noncomputable def hankelF (c : ℝ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), ((f s * hankelRho0 c s : ℝ) : ℂ) * eK z s

lemma kernelB {c : ℝ} (hc : 1 / 2 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) {z : ℂ} (hz : 0 < z.im) :
    ∫ s in Ioi (0 : ℝ), (gK c Δ s : ℂ) * eK z s =
      (-(Complex.I * z)) ^ (-(c : ℂ)) * eK (-1 / z) Δ := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hp : 0 < (-(2 * (π : ℂ) * Complex.I * z)).re := by
    simp [Complex.mul_re, Complex.mul_im]
    have := Real.pi_pos
    nlinarith
  have h : ∫ s in Ioi (0 : ℝ), Complex.exp (-(-(2 * (π : ℂ) * Complex.I * z) * (s : ℂ))) *
      (gK c Δ s : ℂ) = (((2 * π : ℝ) : ℂ) / (-(2 * (π : ℂ) * Complex.I * z))) ^ (c : ℂ) *
        Complex.exp (-(((4 * π ^ 2 * Δ : ℝ) : ℂ) / (-(2 * (π : ℂ) * Complex.I * z)))) :=
    hankel_laplace_complex hc hΔ hp
  have e1 : ∀ s : ℝ, Complex.exp (-(-(2 * (π : ℂ) * Complex.I * z) * (s : ℂ))) * (gK c Δ s : ℂ) =
      (gK c Δ s : ℂ) * eK z s := by
    intro s; unfold eK; rw [mul_comm]; congr 2; ring
  have h2 : ∫ s in Ioi (0 : ℝ), Complex.exp (-(-(2 * (π : ℂ) * Complex.I * z) * (s : ℂ))) *
      (gK c Δ s : ℂ) = ∫ s in Ioi (0 : ℝ), (gK c Δ s : ℂ) * eK z s :=
    integral_congr_ae (ae_of_all _ fun s => e1 s)
  have h3 : (((2 * π : ℝ) : ℂ) / (-(2 * (π : ℂ) * Complex.I * z))) = (-(Complex.I * z))⁻¹ := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hre : 0 < (-(Complex.I * z)).re := by simp; exact hz
  have harg : (-(Complex.I * z)).arg ≠ π := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith [h.1]
  have h4 : (((2 * π : ℝ) : ℂ) / (-(2 * (π : ℂ) * Complex.I * z))) ^ (c : ℂ) =
      (-(Complex.I * z)) ^ (-(c : ℂ)) := by
    rw [h3, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  have h5 : -(((4 * π ^ 2 * Δ : ℝ) : ℂ) / (-(2 * (π : ℂ) * Complex.I * z))) =
      2 * (π : ℂ) * Complex.I * (-1 / z) * (Δ : ℂ) := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← h2, h, h4, h5]
  rfl

lemma hankelF_integrand_integrable {c : ℝ} {f : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hf : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0))
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun s : ℝ => ((f s * hankelRho0 c s : ℝ) : ℂ) * eK z s) (Ioi 0) := by
  refine Integrable.mono' hf.norm ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hfm.mul (measurable_rho0 c).aestronglyMeasurable)).mul
      (by unfold eK; exact (Continuous.aestronglyMeasurable (by fun_prop)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun s hs => ?_
    have hs' : 0 < s := hs
    rw [norm_mul, Complex.norm_real, norm_eK]
    have : Real.exp (-(2 * π * z.im * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.pi_pos
      have : 0 ≤ 2 * π * z.im * s := by positivity
      linarith
    calc ‖f s * hankelRho0 c s‖ * Real.exp (-(2 * π * z.im * s)) ≤ ‖f s * hankelRho0 c s‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_one _

/-- **ct:boas Step 1 (exact modular identity).** For `c > 1/2`, `ε² = 1`, `f ∈ 𝒜_c^ε` and
`Im z > 0`: `F(z) = ε(-iz)^{-c} F(-1/z)`, where `F(z) = ∫_0^∞ f ρ₀ e^{2πizs} ds`. -/
theorem hankelF_modular {c ε : ℝ} (hc : 1 / 2 < c) (hε : ε * ε = 1) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) {z : ℂ} (hz : 0 < z.im) :
    hankelF c f z = (ε : ℂ) * (-(Complex.I * z)) ^ (-(c : ℂ)) * hankelF c f (-1 / z) := by
  have hc0 : 0 < c := by linarith
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have hfm : AEStronglyMeasurable f μ :=
    (hf.cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  -- the double integrand
  set H : ℝ → ℝ → ℂ := fun s t => ((hankelRho0 c s : ℝ) : ℂ) * eK z s *
      ((f t * hankelRho0 c t * hankelPhi c (s * t) : ℝ) : ℂ) with hH
  -- Step 1: the eigen relation
  have hstep1 : ∀ s ∈ Ioi (0 : ℝ), ((f s * hankelRho0 c s : ℝ) : ℂ) * eK z s =
      (ε : ℂ) * ∫ t, H s t ∂μ := by
    intro s hs
    have he := hf.eigen s (le_of_lt hs)
    unfold besselHankelTransform hankelKernel at he
    have hfs : f s = ε * ∫ t in Ioi (0 : ℝ), f t * hankelRho0 c t * hankelPhi c (s * t) := by
      rw [he]; calc f s = (ε * ε) * f s := by rw [hε, one_mul]
        _ = _ := by ring
    have hint : ∫ t, H s t ∂μ = (((hankelRho0 c s : ℝ) : ℂ) * eK z s) *
        ∫ t in Ioi (0 : ℝ), ((f t * hankelRho0 c t * hankelPhi c (s * t) : ℝ) : ℂ) :=
      integral_const_mul _ _
    have hc' : ((f s : ℝ) : ℂ) = (ε : ℂ) *
        ((∫ t in Ioi (0 : ℝ), f t * hankelRho0 c t * hankelPhi c (s * t) : ℝ) : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hfs
      simpa only [Complex.ofReal_mul] using this
    rw [hint, integral_complex_ofReal, Complex.ofReal_mul, hc']
    ring
  have hF1 : hankelF c f z = (ε : ℂ) * ∫ s, ∫ t, H s t ∂μ ∂μ := by
    unfold hankelF
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi hstep1
  -- integrability on the product
  have hu : Integrable (fun s : ℝ => |hankelRho0 c s| * Real.exp (-(2 * π * z.im * s))) μ := by
    have := integrableOn_exp_rho0_pos (c := c) (a := 2 * π * z.im) hc0 (by
      have := Real.pi_pos; positivity)
    refine IntegrableOn.congr_fun this (fun s hs => ?_) measurableSet_Ioi
    have hs' : 0 < s := hs
    rw [abs_of_nonneg (hankelRho0_pos hc0 hs').le, mul_comm]
  have hv : Integrable (fun t : ℝ => ‖f t * hankelRho0 c t‖) μ := hf.int.norm
  have hprod : Integrable (Function.uncurry H) (μ.prod μ) := by
    refine Integrable.mono' (hu.mul_prod hv) ?_ (ae_of_all _ fun p => ?_)
    · have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ((hankelRho0 c p.1 : ℝ) : ℂ)) (μ.prod μ) :=
        (Complex.measurable_ofReal.comp ((measurable_rho0 c).comp measurable_fst)).aestronglyMeasurable
      have m2 : AEStronglyMeasurable (fun p : ℝ × ℝ => eK z p.1) (μ.prod μ) :=
        (by unfold eK; fun_prop : Continuous fun p : ℝ × ℝ => eK z p.1).aestronglyMeasurable
      have mf : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (μ.prod μ) := hfm.comp_snd
      have mr : AEStronglyMeasurable (fun p : ℝ × ℝ => hankelRho0 c p.2) (μ.prod μ) :=
        ((measurable_rho0 c).comp measurable_snd).aestronglyMeasurable
      have mφ : AEStronglyMeasurable (fun p : ℝ × ℝ => hankelPhi c (p.1 * p.2)) (μ.prod μ) :=
        ((hankelPhi_continuous c).comp (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 * p.2)).aestronglyMeasurable
      have m3 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * hankelRho0 c p.2 *
          hankelPhi c (p.1 * p.2)) (μ.prod μ) := (mf.mul mr).mul mφ
      exact (m1.mul m2).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable m3)
    · obtain ⟨s, t⟩ := p
      have h1 : |hankelPhi c (s * t)| ≤ 1 := abs_hankelPhi_le_one hc _
      have h2 : 0 ≤ |hankelRho0 c s| * Real.exp (-(2 * π * z.im * s)) := by positivity
      have h3 : |f t * hankelRho0 c t * hankelPhi c (s * t)| ≤ |f t * hankelRho0 c t| := by
        rw [abs_mul]
        calc |f t * hankelRho0 c t| * |hankelPhi c (s * t)| ≤ |f t * hankelRho0 c t| * 1 :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = _ := mul_one _
      have key : ‖H s t‖ = |hankelRho0 c s| * Real.exp (-(2 * π * z.im * s)) *
          |f t * hankelRho0 c t * hankelPhi c (s * t)| := by
        simp only [hH, norm_mul, Complex.norm_real, norm_eK, Real.norm_eq_abs]
        rw [abs_mul, abs_mul]
      show ‖H s t‖ ≤ (|hankelRho0 c s| * Real.exp (-(2 * π * z.im * s))) * ‖f t * hankelRho0 c t‖
      rw [key, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h3 h2
  -- Step 3: swap and evaluate the inner integral
  have hswap : ∫ s, ∫ t, H s t ∂μ ∂μ = ∫ t, ∫ s, H s t ∂μ ∂μ := integral_integral_swap hprod
  have hinner : ∀ t ∈ Ioi (0 : ℝ), ∫ s, H s t ∂μ =
      ((f t * hankelRho0 c t : ℝ) : ℂ) *
        ((-(Complex.I * z)) ^ (-(c : ℂ)) * eK (-1 / z) t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have e : ∀ s : ℝ, H s t = ((f t * hankelRho0 c t : ℝ) : ℂ) * ((gK c t s : ℂ) * eK z s) := by
      intro s
      simp only [hH, gK]
      rw [mul_comm s t]
      push_cast
      ring
    simp_rw [e]
    rw [integral_const_mul, kernelB hc ht0 hz]
  have hF2 : ∫ t, ∫ s, H s t ∂μ ∂μ =
      (-(Complex.I * z)) ^ (-(c : ℂ)) * hankelF c f (-1 / z) := by
    unfold hankelF
    rw [← integral_const_mul]
    rw [hμ]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hinner t ht]; ring
  rw [hF1, hswap, hF2]
  ring

lemma integrand_norm_le {c : ℝ} {f : ℝ → ℝ} {z : ℂ} (hz : 0 ≤ z.im) {s : ℝ} (hs : 0 ≤ s) :
    ‖((f s * hankelRho0 c s : ℝ) : ℂ) * eK z s‖ ≤ ‖f s * hankelRho0 c s‖ := by
  rw [norm_mul, Complex.norm_real, norm_eK]
  have : Real.exp (-(2 * π * z.im * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := Real.pi_pos
    have : 0 ≤ 2 * π * z.im * s := by positivity
    linarith
  calc ‖f s * hankelRho0 c s‖ * Real.exp (-(2 * π * z.im * s)) ≤ ‖f s * hankelRho0 c s‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

/-- `F` is continuous on the closed upper half-plane. -/
lemma continuousOn_hankelF {c : ℝ} {f : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hf : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0)) :
    ContinuousOn (hankelF c f) {z : ℂ | 0 ≤ z.im} := by
  unfold hankelF
  refine continuousOn_of_dominated (bound := fun s => ‖f s * hankelRho0 c s‖) ?_ ?_ hf.norm ?_
  · intro z hz
    exact (hankelF_integrand_integrable hfm hf hz).aestronglyMeasurable
  · intro z hz
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun s hs => integrand_norm_le hz (le_of_lt hs)
  · exact ae_of_all _ fun s => (by unfold eK; fun_prop : Continuous fun z : ℂ =>
      ((f s * hankelRho0 c s : ℝ) : ℂ) * eK z s).continuousOn

lemma norm_hankelF_le {c : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0)) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖hankelF c f z‖ ≤ ∫ s in Ioi (0 : ℝ), ‖f s * hankelRho0 c s‖ := by
  unfold hankelF
  refine norm_integral_le_of_norm_le hf.norm ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ fun s hs => integrand_norm_le hz (le_of_lt hs)

lemma neg_inv_im (z : ℂ) : (-1 / z).im = z.im / Complex.normSq z := by
  simp [Complex.div_im]
  ring

/-- **ct:boas Step 1, boundary form.** For `x ∈ ℝ∖{0}`, `F(x) = ε(-ix)^{-c} F(-1/x)`. -/
theorem hankelF_modular_real {c ε : ℝ} (hc : 1 / 2 < c) (hε : ε * ε = 1) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) {x : ℝ} (hx : x ≠ 0) :
    hankelF c f (x : ℂ) = (ε : ℂ) * (-(Complex.I * x)) ^ (-(c : ℂ)) * hankelF c f (-1 / (x : ℂ)) := by
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
    (hf.cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hS : ContinuousOn (hankelF c f) {z : ℂ | 0 ≤ z.im} := continuousOn_hankelF hfm hf.int
  set Sp : Set ℂ := {z : ℂ | 0 < z.im} with hSp
  have hxS : (x : ℂ) ∈ closure Sp := by
    rw [hSp, Complex.closure_setOfPred_lt_im]; simp
  have : (𝓝[Sp] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hxS
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hc1 : ContinuousWithinAt (hankelF c f) Sp x :=
    (hS x (by simp)).mono (fun z hz => show 0 ≤ z.im from le_of_lt (show 0 < z.im from hz))
  have hinv : ContinuousWithinAt (fun z : ℂ => -1 / z) Sp x :=
    (continuousAt_const.div continuousAt_id hx').continuousWithinAt
  have hmaps : MapsTo (fun z : ℂ => -1 / z) Sp {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    have hz' : 0 < z.im := hz
    show 0 ≤ (-1 / z).im
    rw [neg_inv_im]
    exact div_nonneg hz'.le (Complex.normSq_nonneg z)
  have hmem : (-1 / (x : ℂ)) ∈ {z : ℂ | 0 ≤ z.im} := by
    show 0 ≤ (-1 / (x : ℂ)).im
    rw [neg_inv_im]; simp
  have hc2 : ContinuousWithinAt (fun z : ℂ => hankelF c f (-1 / z)) Sp x :=
    ContinuousWithinAt.comp (g := hankelF c f) (hS _ hmem) hinv hmaps
  have hslit : (-(Complex.I * (x : ℂ))) ∈ Complex.slitPlane := by
    refine Or.inr ?_
    simp [hx]
  have hpow : ContinuousAt (fun z : ℂ => (-(Complex.I * z)) ^ (-(c : ℂ))) x :=
    ContinuousAt.cpow (by fun_prop) continuousAt_const hslit
  have hG2 : ContinuousWithinAt (fun z : ℂ => (ε : ℂ) * (-(Complex.I * z)) ^ (-(c : ℂ)) *
      hankelF c f (-1 / z)) Sp x :=
    (continuousWithinAt_const.mul hpow.continuousWithinAt).mul hc2
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[Sp] (x : ℂ)) hc1 hG2 ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact hankelF_modular hc hε hf hz

/-- **ct:boas Step 1, the bound** `|F(x)| ≤ M[f] |x|^{-c}` for real `x ≠ 0` (`M[f] = ∫|f|ρ₀`),
in particular `|F(x)| ≤ |x|^{-c}` for `M[f] = 1`, `|x| ≥ 1`. -/
theorem hankelF_bound {c ε : ℝ} (hc : 1 / 2 < c) (hε : ε * ε = 1) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) {x : ℝ} (hx : x ≠ 0) :
    ‖hankelF c f (x : ℂ)‖ ≤ (∫ s in Ioi (0 : ℝ), ‖f s * hankelRho0 c s‖) * |x| ^ (-c) := by
  rw [hankelF_modular_real hc hε hf hx, norm_mul, norm_mul]
  have hε1 : ‖(ε : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : |ε| * |ε| = 1 := by rw [← abs_mul, hε, abs_one]
    nlinarith [abs_nonneg ε]
  have hpow : ‖(-(Complex.I * (x : ℂ))) ^ (-(c : ℂ))‖ = |x| ^ (-c) := by
    have := Complex.norm_cpow_real (-(Complex.I * (x : ℂ))) (-c)
    rw [show (-(c : ℂ)) = ((-c : ℝ) : ℂ) by push_cast; ring, this]
    congr 1
    simp
  have hF : ‖hankelF c f (-1 / (x : ℂ))‖ ≤ ∫ s in Ioi (0 : ℝ), ‖f s * hankelRho0 c s‖ := by
    refine norm_hankelF_le hf.int ?_
    rw [neg_inv_im]; simp
  rw [hε1, hpow, one_mul]
  calc |x| ^ (-c) * ‖hankelF c f (-1 / (x : ℂ))‖ ≤ |x| ^ (-c) * ∫ s in Ioi (0 : ℝ), ‖f s * hankelRho0 c s‖ :=
        mul_le_mul_of_nonneg_left hF (by positivity)
    _ = _ := mul_comm _ _

/-- info: 'FormalResearch.SignUncertainty.HankelModular.hankel_laplace_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_laplace_complex

/-- info: 'FormalResearch.SignUncertainty.HankelModular.hankelF_modular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelF_modular

/-- info: 'FormalResearch.SignUncertainty.HankelModular.hankelF_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelF_bound

end FormalResearch.SignUncertainty.HankelModular
