module

public import FormalResearch.ModularBootstrap.Mixtures.JetsOuter
public import FormalResearch.ModularBootstrap.Mixtures.JetsJensen
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Main

/-!
# Linearity of `hbarA` and the regularised integrals `I₁(A)`, `I₃(A)` (`ctu:jets`)

`constant_term_universality.tex`, Lemma ctu.2 (`ctu:jets`), eqs. `ctu:IA13` and `pmix:f-ell`:

* `hbarA_add`, `hbarA_smul`: linearity of the strip Schwarz integral `hbarA` on `closedStrip` in `Amp`.
* `ellAmp`, `I1Amp`, `I3Amp`: the regularised integrals `I₁(A) = ∫₀^∞ ℓ_A(t) dt` and
  `I₃(A) = ∫₀^∞ (ℓ_A(t) - ℓ_A(0))/t² dt` and their absolute integrability for any `JetAmplitude A`.
* `integrableOn_logAmp_div_sq`, `integral_logAmp_div_sq_eq_I1Amp`:
  `logAmp A t / t²` is integrable on `(0, ∞)` with integral `I₁(A)` (discharging the integrability
  hypotheses of `MixtureData.pmix_jensen`).
* `h1_aRel_eq`, `d1_aRel_eq`: for `aRel A τ = log(A(x_T(τ))/A(ξ_*))` and its quotient `bRel`,
  `∫_ℝ (aRel A τ - aRel A 0) π kern τ = 2 I₁(A)` and `∫_ℝ (bRel τ - bRel 0) π kern τ = (2/3) I₃(A)`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory Asymptotics
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
  FormalResearch.ModularBootstrap.FiveTerm
  FormalResearch.ModularBootstrap.FiveTerm.StripOuter

/-! ### 1. Linearity of `genH` and `hbarA` -/

lemma genH_add {a b : ℝ → ℝ} (_ha : Amp a) (_hb : Amp b) {ζ : ℂ} (_hζ : ζ ∈ strip) :
    genH (fun t => a t + b t) ζ = genH a ζ + genH b ζ := by
  unfold genH
  have h1 := integrable_genH_integrand _ha _hζ
  have h2 := integrable_genH_integrand _hb _hζ
  have heq : (fun t : ℝ => ((a t + b t : ℝ) : ℂ) * kern0 ζ t) =
      fun t => (a t : ℂ) * kern0 ζ t + (b t : ℂ) * kern0 ζ t := by
    ext t; push_cast; ring
  rw [heq, integral_add h1 h2]

lemma genH_smul (c : ℝ) {a : ℝ → ℝ} (_ha : Amp a) {ζ : ℂ} (_hζ : ζ ∈ strip) :
    genH (fun t => c * a t) ζ = (c : ℂ) * genH a ζ := by
  unfold genH
  have heq : (fun t : ℝ => ((c * a t : ℝ) : ℂ) * kern0 ζ t) =
      fun t => (c : ℂ) * ((a t : ℂ) * kern0 ζ t) := by
    ext t; push_cast; ring
  rw [heq, integral_const_mul]

lemma hbarA_add {a b : ℝ → ℝ} (ha : Amp a) (hb : Amp b) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    hbarA (fun t => a t + b t) ζ = hbarA a ζ + hbarA b ζ := by
  have := neBot_nhdsWithin_strip hζ
  have h1 := hbarA_tendsto ha hζ
  have h2 := hbarA_tendsto hb hζ
  have h12 := h1.add h2
  have hev : (fun ξ => genH a ξ + genH b ξ) =ᶠ[𝓝[strip] ζ] genH (fun t => a t + b t) := by
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    exact (genH_add ha hb hξ).symm
  exact (h12.congr' hev).limUnder_eq

lemma hbarA_smul (c : ℝ) {a : ℝ → ℝ} (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    hbarA (fun t => c * a t) ζ = (c : ℂ) * hbarA a ζ := by
  have := neBot_nhdsWithin_strip hζ
  have h1 := (hbarA_tendsto ha hζ).const_mul (c : ℂ)
  have hev : (fun ξ => (c : ℂ) * genH a ξ) =ᶠ[𝓝[strip] ζ] genH (fun t => c * a t) := by
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    exact (genH_smul c ha hξ).symm
  exact (h1.congr' hev).limUnder_eq

/-! ### 2. The regularised integrals `I₁(A)` and `I₃(A)` -/

/-- The integrand `ℓ_A(t) = (A'(x(t)) / A(x(t))) · (x'(t) / t)` of `ctu:jets` (`pmix:f-ell`). -/
noncomputable def ellAmp (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  (deriv A (xChart t) / A (xChart t)) * shiftDensity t

/-- `I₁(A) = ∫₀^∞ ℓ_A(t) dt` (`ctu:IA13`). -/
noncomputable def I1Amp (A : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ellAmp A t

/-- `I₃(A) = ∫₀^∞ (ℓ_A(t) - ℓ_A(0)) / t² dt` (`ctu:IA13`). -/
noncomputable def I3Amp (A : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (ellAmp A t - ellAmp A 0) / t ^ 2

lemma shiftDensity_pos (t : ℝ) : 0 < shiftDensity t := by
  unfold shiftDensity
  have := qChart_pos t
  positivity

lemma shiftDensity_le (t : ℝ) : shiftDensity t ≤ 1 / (2 * π * (1 + t ^ 2)) := by
  have hpi := Real.pi_pos
  have hq := qChart_pos t
  have hq1 : qChart t ≤ 1 + qChart t := by linarith
  have hsq : √(qChart t) ≤ √(1 + qChart t) := Real.sqrt_le_sqrt hq1
  have hsq_pos : 0 < √(qChart t) := Real.sqrt_pos.mpr hq
  have hprod : 1 + t ^ 2 ≤ qChart t * √(qChart t) * √(1 + qChart t) := by
    calc 1 + t ^ 2 = qChart t ^ 2 := (qChart_sq t).symm
      _ = qChart t * (√(qChart t) * √(qChart t)) := by rw [Real.mul_self_sqrt hq.le]; ring
      _ = qChart t * √(qChart t) * √(qChart t) := by ring
      _ ≤ qChart t * √(qChart t) * √(1 + qChart t) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  unfold shiftDensity
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [hpi]

lemma continuous_shiftDensity : Continuous shiftDensity := by
  unfold shiftDensity
  have hq : Continuous qChart := Real.continuous_sqrt.comp (by fun_prop)
  refine continuous_const.div ?_ fun t => by
    have := qChart_pos t; positivity
  exact ((continuous_const.mul (hq.mul (Real.continuous_sqrt.comp hq))).mul
    (Real.continuous_sqrt.comp (continuous_const.add hq)))

lemma shiftDensity_even (t : ℝ) : shiftDensity (-t) = shiftDensity t := by
  unfold shiftDensity qChart
  simp

lemma ellAmp_even (A : ℝ → ℝ) (t : ℝ) : ellAmp A (-t) = ellAmp A t := by
  unfold ellAmp xChart
  have hq : qChart (-t) = qChart t := by unfold qChart; simp
  rw [hq, shiftDensity_even]

lemma continuous_ellAmp {A : ℝ → ℝ} (hA : JetAmplitude A) : Continuous (ellAmp A) := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hdA : ContinuousOn (deriv A) (Ici xiStar) := fun x hx =>
    (hA.analytic x hx).deriv.continuousAt.continuousWithinAt
  have hA_cont : ContinuousOn A (Ici xiStar) := fun x hx =>
    (hA.analytic x hx).continuousAt.continuousWithinAt
  unfold ellAmp
  refine ((hdA.comp_continuous continuous_xChart fun t => xiStar_le_xChart t).div
    (hA_cont.comp_continuous continuous_xChart fun t => xiStar_le_xChart t) fun t =>
      (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xChart t))).ne').mul continuous_shiftDensity

lemma ellAmp_abs_le {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |ellAmp A t| ≤ C / (1 + t ^ 2) := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  obtain ⟨D, hD⟩ := hA.deriv_bdd
  have hpi := Real.pi_pos
  refine ⟨max D 0 / (2 * π * lo), by positivity, fun t => ?_⟩
  have h1 : |deriv A (xChart t)| ≤ max D 0 := (hD _ (xiStar_le_xChart t)).trans (le_max_left _ _)
  have h2 : lo ≤ A (xChart t) := hAlo _ (xiStar_le_xChart t)
  have hsd := shiftDensity_le t
  have hsd0 := shiftDensity_pos t
  unfold ellAmp
  rw [abs_mul, abs_div, abs_of_pos (lt_of_lt_of_le hlo h2), abs_of_pos hsd0]
  calc |deriv A (xChart t)| / A (xChart t) * shiftDensity t
      ≤ (max D 0 / lo) * (1 / (2 * π * (1 + t ^ 2))) := by
        apply mul_le_mul (div_le_div₀ (by positivity) h1 hlo h2) hsd hsd0.le (by positivity)
    _ = (max D 0 / (2 * π * lo)) / (1 + t ^ 2) := by field_simp

/-- `ℓ_A` is integrable on `(0, ∞)`. -/
theorem integrableOn_ellAmp {A : ℝ → ℝ} (hA : JetAmplitude A) :
    IntegrableOn (ellAmp A) (Ioi 0) := by
  obtain ⟨C, hC, hle⟩ := ellAmp_abs_le hA
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul C).integrableOn)
    (continuous_ellAmp hA).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => ?_)
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using hle t

lemma ellAmp_contDiffAt_zero {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ContDiffAt ℝ 2 (ellAmp A) 0 := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hq : ContDiffAt ℝ 2 qChart 0 := by
    unfold qChart
    exact ((contDiffAt_const.add (contDiffAt_id.pow 2)).sqrt (by norm_num))
  have hsqq : ContDiffAt ℝ 2 (fun t => √(qChart t)) 0 :=
    hq.sqrt (qChart_pos 0).ne'
  have hx : ContDiffAt ℝ 2 xChart 0 := by
    have har : ContDiffAt ℝ 2 Real.arsinh (√(qChart 0)) := by
      have heq : (Real.arsinh : ℝ → ℝ) = fun x => Real.log (x + √(1 + x ^ 2)) :=
        funext fun _ => rfl
      rw [heq]
      have hp : 0 < 1 + (√(qChart 0)) ^ 2 := by positivity
      have hsq : ContDiffAt ℝ 2 (fun x : ℝ => √(1 + x ^ 2)) (√(qChart 0)) :=
        (contDiffAt_const.add (contDiffAt_id.pow 2)).sqrt hp.ne'
      have hsum : 0 < √(qChart 0) + √(1 + (√(qChart 0)) ^ 2) := by
        have := Real.sqrt_pos.mpr (qChart_pos 0); positivity
      exact (contDiffAt_id.add hsq).log hsum.ne'
    unfold xChart
    exact (har.comp 0 hsqq).div_const π
  have hA0 : ContDiffAt ℝ 2 A (xChart 0) :=
    (hA.analytic (xChart 0) (xiStar_le_xChart 0)).contDiffAt
  have hdA0 : ContDiffAt ℝ 2 (deriv A) (xChart 0) :=
    (hA.analytic (xChart 0) (xiStar_le_xChart 0)).deriv.contDiffAt
  have hsd : ContDiffAt ℝ 2 shiftDensity 0 := by
    unfold shiftDensity
    have hden : ContDiffAt ℝ 2 (fun t => 2 * π * (qChart t * √(qChart t)) * √(1 + qChart t)) 0 :=
      ((contDiffAt_const.mul (hq.mul hsqq)).mul
        ((contDiffAt_const.add hq).sqrt (by linarith [qChart_pos 0])))
    exact contDiffAt_const.div hden (by have := qChart_pos 0; positivity)
  have hA_ne : A (xChart 0) ≠ 0 := (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xChart 0))).ne'
  unfold ellAmp
  exact ((hdA0.comp 0 hx).div (hA0.comp 0 hx) hA_ne).mul hsd

lemma ellAmp_sub_sq_bound {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ K r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → |ellAmp A t - ellAmp A 0| ≤ K * t ^ 2 := by
  have hcd : ContDiffAt ℝ (2 : ℕ) (ellAmp A) 0 := ellAmp_contDiffAt_zero hA
  obtain ⟨U, hU, hcdU⟩ := hcd.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hc2 : ContDiffOn ℝ 2 (ellAmp A) (ball (0 : ℝ) r) := hcdU.mono hrU
  have hd1 : DifferentiableOn ℝ (ellAmp A) (ball (0 : ℝ) r) := hc2.differentiableOn (by norm_num)
  have hc1 : ContDiffOn ℝ 1 (deriv (ellAmp A)) (ball (0 : ℝ) r) :=
    hc2.deriv_of_isOpen isOpen_ball (m := 1) (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv (ellAmp A))) (closedBall (0 : ℝ) (r / 2)) :=
    (hc1.deriv_of_isOpen isOpen_ball (m := 0) (by norm_num)).continuousOn.mono
      (closedBall_subset_ball (by linarith))
  obtain ⟨M, hM⟩ := isCompact_closedBall (0 : ℝ) (r / 2) |>.exists_bound_of_continuousOn hcont2
  have hder0 : deriv (ellAmp A) 0 = 0 := by
    have h1 : HasDerivAt (ellAmp A) (deriv (ellAmp A) 0) 0 :=
      (hd1.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have h2 : HasDerivAt (fun t => ellAmp A (-t)) (-deriv (ellAmp A) 0) 0 := by
      have h1' : HasDerivAt (ellAmp A) (deriv (ellAmp A) 0) (-0) := by rwa [neg_zero]
      exact (h1'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).congr_deriv (by ring)
    have heq : (fun t => ellAmp A (-t)) = ellAmp A := funext (ellAmp_even A)
    rw [heq] at h2
    linarith [h1.unique h2]
  have hnonneg : ∀ t : ℝ, 0 ≤ t → t < r / 2 → |ellAmp A t - ellAmp A 0| ≤ max M 0 * t ^ 2 := by
    intro t ht0 htr
    have hsub : ∀ x ∈ Icc 0 t, x ∈ ball (0 : ℝ) r := fun x hx =>
      mem_ball_zero_iff.2 (by rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; linarith [hx.2])
    have hmvt1 : ∀ s ∈ Icc 0 t, |deriv (ellAmp A) s| ≤ max M 0 * s := fun s hs => by
      have hdiff_s : ∀ x ∈ Icc 0 s,
          HasDerivWithinAt (deriv (ellAmp A)) (deriv (deriv (ellAmp A)) x) (Icc 0 s) x := fun x hx =>
        ((hc1.differentiableOn (by norm_num)).differentiableAt
          (isOpen_ball.mem_nhds (hsub x ⟨hx.1, hx.2.trans hs.2⟩))).hasDerivAt.hasDerivWithinAt
      have hbd_s : ∀ x ∈ Ico 0 s, ‖deriv (deriv (ellAmp A)) x‖ ≤ max M 0 := fun x hx => by
        have hxc : x ∈ closedBall (0 : ℝ) (r / 2) := by
          rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_nonneg hx.1]
          linarith [hx.2, hs.2]
        exact (hM x hxc).trans (le_max_left _ _)
      have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hdiff_s hbd_s s (right_mem_Icc.2 hs.1)
      simpa [hder0, Real.norm_eq_abs] using hmv
    have hdiff_t : ∀ x ∈ Icc 0 t, HasDerivWithinAt (ellAmp A) (deriv (ellAmp A) x) (Icc 0 t) x :=
      fun x hx => (hd1.differentiableAt (isOpen_ball.mem_nhds (hsub x hx))).hasDerivAt.hasDerivWithinAt
    have hbd_t : ∀ x ∈ Ico 0 t, ‖deriv (ellAmp A) x‖ ≤ max M 0 * t := fun x hx => by
      simpa [Real.norm_eq_abs] using
        (hmvt1 x ⟨hx.1, hx.2.le⟩).trans (mul_le_mul_of_nonneg_left hx.2.le (le_max_right _ _))
    have hmv2 := norm_image_sub_le_of_norm_deriv_le_segment' hdiff_t hbd_t t (right_mem_Icc.2 ht0)
    have : ‖ellAmp A t - ellAmp A 0‖ ≤ (max M 0 * t) * (t - 0) := hmv2
    rw [Real.norm_eq_abs, sub_zero] at this
    nlinarith
  refine ⟨max M 0, r / 2, by positivity, fun t ht => ?_⟩
  rcases le_total 0 t with ht0 | ht0
  · exact hnonneg t ht0 (by rwa [abs_of_nonneg ht0] at ht)
  · rw [← ellAmp_even A t, ← neg_sq t]
    exact hnonneg (-t) (neg_nonneg.mpr ht0) (by rwa [abs_of_nonpos ht0] at ht)

/-- `(ℓ_A(t) - ℓ_A(0)) / t²` is integrable on `(0, ∞)`. -/
theorem integrableOn_ellAmp_sub {A : ℝ → ℝ} (hA : JetAmplitude A) :
    IntegrableOn (fun t => (ellAmp A t - ellAmp A 0) / t ^ 2) (Ioi 0) := by
  obtain ⟨K, r, hr, hK⟩ := ellAmp_sub_sq_bound hA
  obtain ⟨C, hC, hle⟩ := ellAmp_abs_le hA
  have hcont : ContinuousOn (fun t => (ellAmp A t - ellAmp A 0) / t ^ 2) (Ioi 0) :=
    ((continuous_ellAmp hA).sub continuous_const).continuousOn.div (continuous_id.pow 2).continuousOn
      fun t ht => pow_ne_zero 2 (ne_of_gt ht)
  have h1 : IntegrableOn (fun t => (ellAmp A t - ellAmp A 0) / t ^ 2) (Ioo 0 r) := by
    refine Integrable.mono' ((integrableOn_const (hs := measure_Ioo_lt_top.ne)
        (C := max K 0)).mono_set le_rfl)
      ((hcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht0 2), div_le_iff₀ (pow_pos ht0 2)]
    simpa [Real.norm_eq_abs] using (hK t (by rw [abs_of_pos ht0]; exact ht.2)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg t))
  have h2 : IntegrableOn (fun t => (ellAmp A t - ellAmp A 0) / t ^ 2) (Ioi r) := by
    have hinv : IntegrableOn (fun t : ℝ => (C + |ellAmp A 0|) * t ^ (-2 : ℝ)) (Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr).const_mul (C + |ellAmp A 0|)
    refine Integrable.mono' hinv
      ((hcont.mono (Ioi_subset_Ioi hr.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hr ht
    have h1t : 1 ≤ 1 + t ^ 2 := by linarith [sq_nonneg t]
    have hl : |ellAmp A t| ≤ C := (hle t).trans (div_le_self hC h1t)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht0 2)]
    have hsub : |ellAmp A t - ellAmp A 0| ≤ C + |ellAmp A 0| :=
      (abs_sub _ _).trans (by linarith)
    rw [show (C + |ellAmp A 0|) * t ^ (-2 : ℝ) = (C + |ellAmp A 0|) / t ^ 2 by
      rw [Real.rpow_neg ht0.le, Real.rpow_two, div_eq_mul_inv]]
    exact div_le_div_of_nonneg_right hsub (sq_nonneg t)
  have hu : Ioi (0 : ℝ) = Ioo 0 r ∪ ({r} ∪ Ioi r) := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioo, mem_singleton_iff]; constructor <;> intro h
    · rcases lt_trichotomy x r with h1 | rfl | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h1)
    · rcases h with h | rfl | h <;> linarith
  have hsing : IntegrableOn (fun t => (ellAmp A t - ellAmp A 0) / t ^ 2) {r} volume :=
    integrableOn_singleton (hx := isCompact_singleton.measure_lt_top)
  rw [hu]
  exact h1.union (hsing.union h2)

/-! ### 3. `logAmp A` derivative, integrability, and integration by parts -/

lemma hasDerivAt_logAmp {A : ℝ → ℝ} (hA : JetAmplitude A) (t : ℝ) :
    HasDerivAt (logAmp A) (t * ellAmp A t) t := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  have hAx : 0 < A (xChart t) := lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xChart t))
  have hdA : HasDerivAt A (deriv A (xChart t)) (xChart t) :=
    (hA.analytic (xChart t) (xiStar_le_xChart t)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun s => A (xChart s) / A xiStar)
      (deriv A (xChart t) * (t * shiftDensity t) / A xiStar) t := by
    have hx := xChart_hasDerivAt t
    have hx' : HasDerivAt xChart (t * shiftDensity t) t := by
      refine hx.congr_deriv ?_; unfold shiftDensity; ring
    exact (hdA.comp t hx').div_const _
  have hlog := hcomp.log (div_pos hAx hAξ).ne'
  refine hlog.congr_deriv ?_
  unfold ellAmp
  field_simp

lemma logAmp_zero (A : ℝ → ℝ) {lo : ℝ} (hlo : 0 < lo) (hAlo : ∀ x, xiStar ≤ x → lo ≤ A x) :
    logAmp A 0 = 0 := by
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  unfold logAmp
  rw [xChart_zero, div_self hAξ.ne', Real.log_one]

lemma logAmp_abs_le_sq {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |logAmp A t| ≤ C * t ^ 2 := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  obtain ⟨C, hC, hle⟩ := ellAmp_abs_le hA
  refine ⟨C / 2, by positivity, fun t => ?_⟩
  have hid : logAmp A t = ∫ s in (0 : ℝ)..t, s * ellAmp A s := by
    have hcont : Continuous (fun s => s * ellAmp A s) := continuous_id.mul (continuous_ellAmp hA)
    have hint : IntervalIntegrable (fun s => s * ellAmp A s) volume 0 t := hcont.intervalIntegrable 0 t
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_logAmp hA s) hint
    rw [logAmp_zero A hlo hAlo, sub_zero] at hftc
    exact hftc.symm
  rw [hid]
  rcases le_total 0 t with ht0 | ht0
  · have hm : ∫ s in (0 : ℝ)..t, |s * ellAmp A s| ≤ ∫ s in (0 : ℝ)..t, C * s := by
      refine intervalIntegral.integral_mono_on ht0 ?_ ?_ fun s hs => ?_
      · exact ((continuous_id.mul (continuous_ellAmp hA)).abs).intervalIntegrable 0 t
      · exact (continuous_const.mul (continuous_id : Continuous fun s : ℝ => s)).intervalIntegrable 0 t
      · rw [abs_mul, abs_of_nonneg hs.1]
        have h1 : |ellAmp A s| ≤ C := (hle s).trans (div_le_self hC (by linarith [sq_nonneg s]))
        exact (mul_le_mul_of_nonneg_left h1 hs.1).trans_eq (mul_comm _ _)
    have hcs : ∫ s in (0 : ℝ)..t, C * s = C / 2 * t ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    calc |∫ s in (0 : ℝ)..t, s * ellAmp A s|
        ≤ ∫ s in (0 : ℝ)..t, |s * ellAmp A s| := intervalIntegral.abs_integral_le_integral_abs ht0
      _ ≤ ∫ s in (0 : ℝ)..t, C * s := hm
      _ = C / 2 * t ^ 2 := hcs
  · rw [intervalIntegral.integral_symm, abs_neg]
    have hm : ∫ s in t..0, |s * ellAmp A s| ≤ ∫ s in t..0, C * (-s) := by
      refine intervalIntegral.integral_mono_on ht0 ?_ ?_ fun s hs => ?_
      · exact ((continuous_id.mul (continuous_ellAmp hA)).abs).intervalIntegrable t 0
      · exact (continuous_const.mul (continuous_id : Continuous fun s : ℝ => s).neg).intervalIntegrable t 0
      · rw [abs_mul, abs_of_nonpos hs.2]
        have h1 : |ellAmp A s| ≤ C := (hle s).trans (div_le_self hC (by linarith [sq_nonneg s]))
        exact (mul_le_mul_of_nonneg_left h1 (neg_nonneg.mpr hs.2)).trans_eq (mul_comm _ _)
    have hcs : ∫ s in t..0, C * (-s) = C / 2 * t ^ 2 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, integral_id]; ring
    calc |∫ s in t..0, s * ellAmp A s|
        ≤ ∫ s in t..0, |s * ellAmp A s| := intervalIntegral.abs_integral_le_integral_abs ht0
      _ ≤ ∫ s in t..0, C * (-s) := hm
      _ = C / 2 * t ^ 2 := hcs

lemma logAmp_abs_le_const {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |logAmp A t| ≤ M := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  obtain ⟨hi, hAhi⟩ := hA.upper
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  refine ⟨max |Real.log (lo / A xiStar)| |Real.log (hi / A xiStar)|, by positivity, fun t => ?_⟩
  have hx := xiStar_le_xChart t
  have hpos : 0 < A (xChart t) := lt_of_lt_of_le hlo (hAlo _ hx)
  have h1 : Real.log (lo / A xiStar) ≤ logAmp A t :=
    Real.log_le_log (div_pos hlo hAξ) (div_le_div_of_nonneg_right (hAlo _ hx) hAξ.le)
  have h2 : logAmp A t ≤ Real.log (hi / A xiStar) :=
    Real.log_le_log (div_pos hpos hAξ) (div_le_div_of_nonneg_right (hAhi _ hx) hAξ.le)
  rw [abs_le]
  exact ⟨(neg_le_neg (le_max_left _ _)).trans (by linarith [neg_abs_le (Real.log (lo / A xiStar))]),
    h2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

/-- `logAmp A t / t²` is integrable on `(0, ∞)` for any `JetAmplitude A`. -/
theorem integrableOn_logAmp_div_sq {A : ℝ → ℝ} (hA : JetAmplitude A) :
    IntegrableOn (fun t => logAmp A t / t ^ 2) (Ioi 0) := by
  obtain ⟨C, hC, hsq⟩ := logAmp_abs_le_sq hA
  obtain ⟨M, hM, hconst⟩ := logAmp_abs_le_const hA
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  have hcont : ContinuousOn (fun t => logAmp A t / t ^ 2) (Ioi 0) := by
    refine ContinuousOn.div ?_ (continuous_id.pow 2).continuousOn fun t ht =>
      pow_ne_zero 2 (ne_of_gt ht)
    unfold logAmp
    refine ContinuousOn.log ?_ fun t _ => (div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xChart t))) hAξ).ne'
    have hA_cont : ContinuousOn A (Ici xiStar) := fun x hx =>
      (hA.analytic x hx).continuousAt.continuousWithinAt
    exact (hA_cont.comp_continuous continuous_xChart fun t => xiStar_le_xChart t).div_const _ |>.continuousOn
  have h1 : IntegrableOn (fun t => logAmp A t / t ^ 2) (Ioo 0 1) := by
    refine Integrable.mono' (integrableOn_const (hs := measure_Ioo_lt_top.ne) (C := C))
      ((hcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht.1 2), div_le_iff₀ (pow_pos ht.1 2)]
    simpa [Real.norm_eq_abs] using hsq t
  have h2 : IntegrableOn (fun t => logAmp A t / t ^ 2) (Ioi 1) := by
    have hinv : IntegrableOn (fun t : ℝ => M * t ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul M
    refine Integrable.mono' hinv
      ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht0 2),
      show M * t ^ (-2 : ℝ) = M / t ^ 2 by rw [Real.rpow_neg ht0.le, Real.rpow_two, div_eq_mul_inv]]
    exact div_le_div_of_nonneg_right (hconst t) (sq_nonneg t)
  have hu : Ioi (0 : ℝ) = Ioo 0 1 ∪ ({1} ∪ Ioi 1) := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioo, mem_singleton_iff]; constructor <;> intro h
    · rcases lt_trichotomy x 1 with h1 | rfl | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h1)
    · rcases h with h | rfl | h <;> linarith
  have hsing : IntegrableOn (fun t => logAmp A t / t ^ 2) {1} volume :=
    integrableOn_singleton (hx := isCompact_singleton.measure_lt_top)
  rw [hu]
  exact h1.union (hsing.union h2)

/-- Integration by parts: `∫₀^∞ logAmp A t / t² dt = I₁(A)`. -/
theorem integral_logAmp_div_sq_eq_I1Amp {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∫ t in Ioi (0 : ℝ), logAmp A t / t ^ 2 = I1Amp A := by
  obtain ⟨C, hC, hsq⟩ := logAmp_abs_le_sq hA
  obtain ⟨M, hM, hconst⟩ := logAmp_abs_le_const hA
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (logAmp A) (t * ellAmp A t) t := fun t _ =>
    hasDerivAt_logAmp hA t
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -t⁻¹) (t ^ 2)⁻¹ t := fun t ht => by
    have ht0 : t ≠ 0 := ne_of_gt ht
    exact (hasDerivAt_inv ht0).neg.congr_deriv (by ring)
  have huv' : IntegrableOn (logAmp A * fun t : ℝ => (t ^ 2)⁻¹) (Ioi 0) :=
    (integrableOn_logAmp_div_sq hA).congr_fun (fun t _ => by simp [div_eq_mul_inv]) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun t => t * ellAmp A t) * fun t : ℝ => -t⁻¹) (Ioi 0) := by
    refine (integrableOn_ellAmp hA).neg.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    show -ellAmp A t = (t * ellAmp A t) * -t⁻¹
    field_simp
  have h0 : Tendsto (logAmp A * fun t : ℝ => -t⁻¹) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) by
      have : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_of_pos ht0]
    calc |logAmp A t| * t⁻¹ ≤ (C * t ^ 2) * t⁻¹ := mul_le_mul_of_nonneg_right (hsq t) (inv_nonneg.mpr ht0.le)
      _ = C * t := by field_simp
  have hinf : Tendsto (logAmp A * fun t : ℝ => -t⁻¹) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun t : ℝ => M / t) atTop (𝓝 0))
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_of_pos ht]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hconst t) (inv_nonneg.mpr ht.le)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  simp only [sub_zero, zero_sub] at hibp
  have heq1 : ∫ t in Ioi (0 : ℝ), logAmp A t / t ^ 2 =
      ∫ t in Ioi (0 : ℝ), logAmp A t * (t ^ 2)⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp [div_eq_mul_inv]
  have heq2 : ∫ t in Ioi (0 : ℝ), t * ellAmp A t * -t⁻¹ = -I1Amp A := by
    unfold I1Amp
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
  rw [heq1, hibp, heq2, neg_neg]

private lemma logAmp_sub_abs_le_pow_four {A : ℝ → ℝ} (hA : JetAmplitude A) {K r : ℝ}
    (hK : ∀ t : ℝ, |t| < r → |ellAmp A t - ellAmp A 0| ≤ K * t ^ 2) {t : ℝ} (ht0 : 0 < t) (htr : t < r) :
    |logAmp A t - ellAmp A 0 / 2 * t ^ 2| ≤ max K 0 / 4 * t ^ 4 := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hid : logAmp A t - ellAmp A 0 / 2 * t ^ 2 =
      ∫ s in (0 : ℝ)..t, s * (ellAmp A s - ellAmp A 0) := by
    have hd : ∀ s, HasDerivAt (fun s => logAmp A s - ellAmp A 0 / 2 * s ^ 2)
        (s * (ellAmp A s - ellAmp A 0)) s := fun s => by
      have h1 := hasDerivAt_logAmp hA s
      have h2 := ((hasDerivAt_pow 2 s).const_mul (ellAmp A 0 / 2))
      refine (h1.sub h2).congr_deriv ?_; ring
    have hc : Continuous (fun s => s * (ellAmp A s - ellAmp A 0)) :=
      continuous_id.mul ((continuous_ellAmp hA).sub continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable 0 t)
    rw [logAmp_zero A hlo hAlo, zero_pow two_ne_zero, mul_zero, sub_zero, sub_zero] at hftc
    exact hftc.symm
  rw [hid]
  have hmono : ∫ s in (0 : ℝ)..t, |s * (ellAmp A s - ellAmp A 0)| ≤
      ∫ s in (0 : ℝ)..t, max K 0 * s ^ 3 := by
    refine intervalIntegral.integral_mono_on ht0.le ?_ ?_ fun s hs => ?_
    · exact ((continuous_id.mul ((continuous_ellAmp hA).sub continuous_const)).abs).intervalIntegrable 0 t
    · exact (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 t
    · rw [abs_mul, abs_of_nonneg hs.1]
      have hs' : |s| < r := by rw [abs_of_nonneg hs.1]; linarith [hs.2]
      have hKs : |ellAmp A s - ellAmp A 0| ≤ max K 0 * s ^ 2 :=
        (hK s hs').trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (sq_nonneg s))
      calc s * |ellAmp A s - ellAmp A 0| ≤ s * (max K 0 * s ^ 2) :=
            mul_le_mul_of_nonneg_left hKs hs.1
        _ = max K 0 * s ^ 3 := by ring
  have hpow : ∫ s in (0 : ℝ)..t, max K 0 * s ^ 3 = max K 0 / 4 * t ^ 4 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; ring
  exact (intervalIntegral.abs_integral_le_integral_abs ht0.le).trans (hmono.trans hpow.le)

lemma integrableOn_logAmp_sub_div_pow_four {A : ℝ → ℝ} (hA : JetAmplitude A) :
    IntegrableOn (fun t => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) (Ioi 0) := by
  obtain ⟨K, r, hr, hK⟩ := ellAmp_sub_sq_bound hA
  obtain ⟨M, hM, hconst⟩ := logAmp_abs_le_const hA
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  have hcont : ContinuousOn (fun t => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) (Ioi 0) := by
    refine ContinuousOn.div ?_ (continuous_id.pow 4).continuousOn fun t ht =>
      pow_ne_zero 4 (ne_of_gt ht)
    refine ContinuousOn.sub ?_ (continuous_const.mul (continuous_id.pow 2)).continuousOn
    unfold logAmp
    refine ContinuousOn.log ?_ fun t _ => (div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xChart t))) hAξ).ne'
    have hA_cont : ContinuousOn A (Ici xiStar) := fun x hx =>
      (hA.analytic x hx).continuousAt.continuousWithinAt
    exact (hA_cont.comp_continuous continuous_xChart fun t => xiStar_le_xChart t).div_const _ |>.continuousOn
  have h1 : IntegrableOn (fun t => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) (Ioo 0 r) := by
    refine Integrable.mono' (integrableOn_const (hs := measure_Ioo_lt_top.ne) (C := max K 0 / 4))
      ((hcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht.1 4), div_le_iff₀ (pow_pos ht.1 4)]
    simpa [Real.norm_eq_abs] using logAmp_sub_abs_le_pow_four hA hK ht.1 ht.2
  have h2 : IntegrableOn (fun t => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) (Ioi r) := by
    have hinv : IntegrableOn (fun t : ℝ => M * t ^ (-4 : ℝ) + |ellAmp A 0| / 2 * t ^ (-2 : ℝ)) (Ioi r) :=
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hr).const_mul M).add
        ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr).const_mul (|ellAmp A 0| / 2))
    refine Integrable.mono' hinv
      ((hcont.mono (Ioi_subset_Ioi hr.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hr ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht0 4)]
    have hsub : |logAmp A t - ellAmp A 0 / 2 * t ^ 2| ≤ M + |ellAmp A 0| / 2 * t ^ 2 := by
      refine (abs_sub _ _).trans (add_le_add (hconst t) ?_)
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (pow_pos ht0 2)]
    rw [div_le_iff₀ (pow_pos ht0 4)]
    have hpow4 : t ^ (-4 : ℝ) * t ^ 4 = 1 := by
      rw [Real.rpow_neg ht0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero 4 ht0.ne')]
    have hpow2 : t ^ (-2 : ℝ) * t ^ 4 = t ^ 2 := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two]; field_simp
    calc |logAmp A t - ellAmp A 0 / 2 * t ^ 2|
        ≤ M + |ellAmp A 0| / 2 * t ^ 2 := hsub
      _ = (M * t ^ (-4 : ℝ) + |ellAmp A 0| / 2 * t ^ (-2 : ℝ)) * t ^ 4 := by
          rw [add_mul, mul_assoc, hpow4, mul_assoc, hpow2, mul_one]
  have hu : Ioi (0 : ℝ) = Ioo 0 r ∪ ({r} ∪ Ioi r) := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioo, mem_singleton_iff]; constructor <;> intro h
    · rcases lt_trichotomy x r with h1 | rfl | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h1)
    · rcases h with h | rfl | h <;> linarith
  have hsing : IntegrableOn (fun t => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) {r} volume :=
    integrableOn_singleton (hx := isCompact_singleton.measure_lt_top)
  rw [hu]
  exact h1.union (hsing.union h2)

/-- Integration by parts: `∫₀^∞ (logAmp A t - ℓ_A(0)/2 * t²) / t⁴ dt = I₃(A) / 3`. -/
theorem integral_logAmp_sub_div_pow_four_eq_I3Amp {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∫ t in Ioi (0 : ℝ), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 = I3Amp A / 3 := by
  obtain ⟨K, r, hr, hK⟩ := ellAmp_sub_sq_bound hA
  obtain ⟨M, hM, hconst⟩ := logAmp_abs_le_const hA
  have hu : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s => logAmp A s - ellAmp A 0 / 2 * s ^ 2) (t * (ellAmp A t - ellAmp A 0)) t :=
    fun t _ => ((hasDerivAt_logAmp hA t).sub ((hasDerivAt_pow 2 t).const_mul (ellAmp A 0 / 2))).congr_deriv
      (by ring)
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => -(3 * s ^ 3)⁻¹) (t ^ 4)⁻¹ t := fun t ht => by
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h1 : HasDerivAt (fun s : ℝ => 3 * s ^ 3) (3 * (3 * t ^ 2)) t := by
      simpa using (hasDerivAt_pow 3 t).const_mul 3
    exact (h1.inv (by positivity)).neg.congr_deriv (by field_simp)
  have huv' : IntegrableOn ((fun s => logAmp A s - ellAmp A 0 / 2 * s ^ 2) * fun s : ℝ => (s ^ 4)⁻¹)
      (Ioi 0) :=
    (integrableOn_logAmp_sub_div_pow_four hA).congr_fun
      (fun t _ => by simp [div_eq_mul_inv]) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun s => s * (ellAmp A s - ellAmp A 0)) * fun s : ℝ => -(3 * s ^ 3)⁻¹)
      (Ioi 0) := by
    have hcm : IntegrableOn (fun s => (-1 / 3 : ℝ) * ((ellAmp A s - ellAmp A 0) / s ^ 2)) (Ioi 0) :=
      (integrableOn_ellAmp_sub hA).const_mul (-1 / 3 : ℝ)
    refine hcm.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    show -1 / 3 * ((ellAmp A t - ellAmp A 0) / t ^ 2) =
      t * (ellAmp A t - ellAmp A 0) * -(3 * t ^ 3)⁻¹
    field_simp
  have h0 : Tendsto ((fun s => logAmp A s - ellAmp A 0 / 2 * s ^ 2) * fun s : ℝ => -(3 * s ^ 3)⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun t : ℝ => (max K 0 / 12) * t) (𝓝[>] 0) (𝓝 0) by
      have : Tendsto (fun t : ℝ => (max K 0 / 12) * t) (𝓝 0) (𝓝 ((max K 0 / 12) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    have ht0 : 0 < t := ht.1
    have hsub4 := logAmp_sub_abs_le_pow_four hA hK ht0 ht.2
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (pow_pos ht0 3)]
    calc |logAmp A t - ellAmp A 0 / 2 * t ^ 2| * (3 * t ^ 3)⁻¹
        ≤ (max K 0 / 4 * t ^ 4) * (3 * t ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right hsub4 (by positivity)
      _ = max K 0 / 12 * t := by field_simp; ring
  have hinf : Tendsto ((fun s => logAmp A s - ellAmp A 0 / 2 * s ^ 2) * fun s : ℝ => -(3 * s ^ 3)⁻¹)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun t : ℝ => M / (3 * t ^ 3) + |ellAmp A 0| / (6 * t))
        atTop (𝓝 0) by
      have h1 : Tendsto (fun t : ℝ => M / (3 * t ^ 3)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).const_mul_atTop (by norm_num))
      have h2 : Tendsto (fun t : ℝ => |ellAmp A 0| / (6 * t)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
      simpa using h1.add h2)
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (pow_pos ht 3)]
    have hsub : |logAmp A t - ellAmp A 0 / 2 * t ^ 2| ≤ M + |ellAmp A 0| / 2 * t ^ 2 := by
      refine (abs_sub _ _).trans (add_le_add (hconst t) ?_)
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (pow_pos ht 2)]
    calc |logAmp A t - ellAmp A 0 / 2 * t ^ 2| * (3 * t ^ 3)⁻¹
        ≤ (M + |ellAmp A 0| / 2 * t ^ 2) * (3 * t ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right hsub (by positivity)
      _ = M / (3 * t ^ 3) + |ellAmp A 0| / (6 * t) := by field_simp; ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  simp only [sub_zero, zero_sub] at hibp
  have heq1 : ∫ t in Ioi (0 : ℝ), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 =
      ∫ t in Ioi (0 : ℝ), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) * (t ^ 4)⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp [div_eq_mul_inv]
  have heq2 : ∫ t in Ioi (0 : ℝ), t * (ellAmp A t - ellAmp A 0) * -(3 * t ^ 3)⁻¹ =
      -(I3Amp A / 3) := by
    unfold I3Amp
    rw [← integral_div, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
  rw [heq1, hibp, heq2, neg_neg]

/-! ### 4. Change of variables `t = sinh(πτ)` for `aRel A` -/

lemma xChart_sinh_pi (τ : ℝ) : xChart (Real.sinh (π * τ)) = xT τ := by
  have hq : qChart (Real.sinh (π * τ)) = Real.cosh (π * τ) := by
    unfold qChart
    have h : 1 + Real.sinh (π * τ) ^ 2 = Real.cosh (π * τ) ^ 2 := by linarith [Real.cosh_sq (π * τ)]
    rw [h, Real.sqrt_sq (Real.cosh_pos _).le]
  unfold xChart xT
  rw [hq]

lemma aRel_eq_logAmp_sinh (A : ℝ → ℝ) (τ : ℝ) : aRel A τ = logAmp A (Real.sinh (π * τ)) := by
  unfold aRel logAmp
  rw [xChart_sinh_pi]

lemma hasDerivAt_aRel {A : ℝ → ℝ} (hA : JetAmplitude A) (τ : ℝ) :
    HasDerivAt (aRel A) (Real.sinh (π * τ) * ellAmp A (Real.sinh (π * τ)) * (π * Real.cosh (π * τ))) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => Real.sinh (π * τ)) (π * Real.cosh (π * τ)) τ := hd_sinh1 τ
  have h2 := (hasDerivAt_logAmp hA (Real.sinh (π * τ))).comp τ h1
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun s =>
    aRel_eq_logAmp_sinh A s)).congr_deriv (by ring)

/-- Change of variables `t = sinh(πτ)` on `(0, ∞)` for a continuous integrable function. -/
theorem integral_comp_sinh_pi {f : ℝ → ℝ} (hfc : Continuous f)
    (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (fun τ : ℝ => f (Real.sinh (π * τ)) * (π * Real.cosh (π * τ))) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), f (Real.sinh (π * τ)) * (π * Real.cosh (π * τ)) = ∫ t in Ioi (0 : ℝ), f t := by
  have hpi := Real.pi_pos
  have hsh_lim : Tendsto (fun R : ℝ => Real.sinh (π * R)) atTop atTop :=
    tendsto_sinh_atTop'.comp (tendsto_id.const_mul_atTop hpi)
  have hsh_mono : ∀ {a b : ℝ}, a ≤ b → Real.sinh (π * a) ≤ Real.sinh (π * b) := fun hab =>
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hab hpi.le)
  have hcomp : ∀ (g : ℝ → ℝ), Continuous g → ∀ R : ℝ, 0 ≤ R →
      ∫ τ in (0 : ℝ)..R, g (Real.sinh (π * τ)) * (π * Real.cosh (π * τ)) =
        ∫ t in (0 : ℝ)..Real.sinh (π * R), g t := fun g hg R _hR => by
    have h := intervalIntegral.integral_comp_mul_deriv' (a := (0 : ℝ)) (b := R)
      (f := fun τ => Real.sinh (π * τ)) (f' := fun τ => π * Real.cosh (π * τ)) (g := g)
      (fun τ _ => hd_sinh1 τ)
      (continuous_const.mul (Real.continuous_cosh.comp (by fun_prop))).continuousOn
      hg.continuousOn
    simpa [mul_zero, Real.sinh_zero] using h
  have hint_g : IntegrableOn (fun τ : ℝ => f (Real.sinh (π * τ)) * (π * Real.cosh (π * τ))) (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (∫ t in Ioi (0 : ℝ), ‖f t‖) 0
      (fun R => ((hfc.comp (Real.continuous_sinh.comp (by fun_prop))).mul
        (continuous_const.mul (Real.continuous_cosh.comp (by fun_prop)))).integrableOn_Ioc)
      tendsto_id ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    dsimp only [id]
    have heq : ∫ τ in (0 : ℝ)..R, ‖f (Real.sinh (π * τ)) * (π * Real.cosh (π * τ))‖ =
        ∫ τ in (0 : ℝ)..R, (‖f ·‖) (Real.sinh (π * τ)) * (π * Real.cosh (π * τ)) := by
      refine intervalIntegral.integral_congr fun τ _ => ?_
      have hpos : 0 < π * Real.cosh (π * τ) := mul_pos hpi (Real.cosh_pos _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]; rfl
    rw [heq, hcomp (fun t => ‖f t‖) hfc.norm R hR, intervalIntegral.integral_of_le (by
      simpa [Real.sinh_zero] using hsh_mono hR)]
    exact setIntegral_mono_set hf.norm (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun t ht => ht.1)
  refine ⟨hint_g, ?_⟩
  have hL : Tendsto (fun R : ℝ => ∫ τ in (0 : ℝ)..R,
        f (Real.sinh (π * τ)) * (π * Real.cosh (π * τ))) atTop
      (𝓝 (∫ τ in Ioi (0 : ℝ), f (Real.sinh (π * τ)) * (π * Real.cosh (π * τ)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint_g tendsto_id
  have hR : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..Real.sinh (π * R), f t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), f t)) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id).comp hsh_lim
  have heq : ∀ᶠ R : ℝ in atTop,
      (∫ τ in (0 : ℝ)..R, f (Real.sinh (π * τ)) * (π * Real.cosh (π * τ))) =
        ∫ t in (0 : ℝ)..Real.sinh (π * R), f t := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR0
    exact hcomp f hfc R hR0
  exact tendsto_nhds_unique (hL.congr' heq) hR

/-- **`ctu:jets` (first-order slope of `aRel A`)**:
`∫_ℝ (aRel A τ - aRel A 0) · (π kern τ) dτ = 2 I₁(A)`. -/
theorem h1_aRel_eq {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∫ τ : ℝ, (aRel A τ - aRel A 0) * (π * kern τ) = 2 * I1Amp A := by
  have hpi := Real.pi_pos
  obtain ⟨hint, hval⟩ := integral_comp_sinh_pi (continuous_ellAmp hA) (integrableOn_ellAmp hA)
  let a' : ℝ → ℝ := fun τ =>
    Real.sinh (π * τ) * ellAmp A (Real.sinh (π * τ)) * (π * Real.cosh (π * τ))
  have hint' : IntegrableOn (fun τ => a' τ / Real.sinh (π * τ)) (Ioi 0) := by
    refine hint.congr_fun ?_ measurableSet_Ioi
    intro τ hτ
    have hsh : Real.sinh (π * τ) ≠ 0 := (sinh_pos_of_pos hτ).ne'
    dsimp only [a']
    field_simp
  have hibp := slope_ibp (amp_aRel hA) (fun τ _ => hasDerivAt_aRel hA τ) hint'
  have heq : ∫ τ in Ioi (0 : ℝ), a' τ / Real.sinh (π * τ) = I1Amp A := by
    unfold I1Amp
    rw [← hval]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have hsh : Real.sinh (π * τ) ≠ 0 := (sinh_pos_of_pos hτ).ne'
    dsimp only [a']
    field_simp
  rw [hibp, heq]

/-- **`ctu:jets` (third-order quotient slope of `aRel A`)**:
for `bRel` with `bRel τ = aRel A τ / sinh²(πτ)`, `∫_ℝ (bRel τ - bRel 0) · (π kern τ) dτ = (2/3) I₃(A)`. -/
theorem d1_aRel_eq {A : ℝ → ℝ} (hA : JetAmplitude A) {b : ℝ → ℝ} (hb : Amp b)
    (hab : ∀ τ : ℝ, τ ≠ 0 → b τ = (aRel A τ - aRel A 0) / Real.sinh (π * τ) ^ 2) :
    ∫ τ : ℝ, (b τ - b 0) * (π * kern τ) = (2 / 3) * I3Amp A := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hpi := Real.pi_pos
  have ha0 : aRel A 0 = 0 := aRel_zero A hlo hAlo
  -- First identify `b 0 = ellAmp A 0 / 2` by taking `τ → 0⁺`
  have hb0 : b 0 = ellAmp A 0 / 2 := by
    obtain ⟨K, r, hr, hK⟩ := ellAmp_sub_sq_bound hA
    have h1 : Tendsto b (𝓝[>] 0) (𝓝 (b 0)) := hb.cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto b (𝓝[>] 0) (𝓝 (ellAmp A 0 / 2)) := by
      have hsub : Tendsto (fun τ : ℝ => (logAmp A (Real.sinh (π * τ)) -
            ellAmp A 0 / 2 * Real.sinh (π * τ) ^ 2) / Real.sinh (π * τ) ^ 2) (𝓝[>] 0) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hsh_lim : Tendsto (fun τ : ℝ => Real.sinh (π * τ)) (𝓝[>] 0) (𝓝 0) := by
          have : Continuous (fun τ : ℝ => Real.sinh (π * τ)) := Real.continuous_sinh.comp (by fun_prop)
          simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
        have hsmall : ∀ᶠ τ : ℝ in 𝓝[>] 0, Real.sinh (π * τ) < r ∧ 0 < Real.sinh (π * τ) := by
          filter_upwards [Metric.tendsto_nhds.mp hsh_lim r hr, self_mem_nhdsWithin] with τ hτ1 hτ2
          have hs0 := sinh_pos_of_pos hτ2
          exact ⟨by simpa [Real.norm_eq_abs, abs_of_pos hs0] using hτ1, hs0⟩
        refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
          (by simpa using (tendsto_const_nhds (x := max K 0 / 4)).mul (hsh_lim.pow 2))
        · filter_upwards [hsmall] with τ ⟨hsr, hs0⟩
          have h4 := logAmp_sub_abs_le_pow_four hA hK hs0 hsr
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hs0 2), div_le_iff₀ (pow_pos hs0 2)]
          calc |logAmp A (Real.sinh (π * τ)) - ellAmp A 0 / 2 * Real.sinh (π * τ) ^ 2|
              ≤ max K 0 / 4 * Real.sinh (π * τ) ^ 4 := h4
            _ = (max K 0 / 4 * Real.sinh (π * τ) ^ 2) * Real.sinh (π * τ) ^ 2 := by ring
      have hev : (fun τ : ℝ => ellAmp A 0 / 2 +
            (logAmp A (Real.sinh (π * τ)) - ellAmp A 0 / 2 * Real.sinh (π * τ) ^ 2) /
              Real.sinh (π * τ) ^ 2) =ᶠ[𝓝[>] 0] b := by
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hs0 := sinh_pos_of_pos hτ
        rw [hab τ hτ.ne', ha0, sub_zero, aRel_eq_logAmp_sinh]
        field_simp
        ring
      simpa using (tendsto_const_nhds.add hsub).congr' hev
    exact tendsto_nhds_unique h1 h2
  -- Evenness: ∫_ℝ = 2 ∫_{Ioi 0}
  have hev : ∀ τ, (b τ - b 0) * (π * kern τ) = (b (-τ) - b 0) * (π * kern (-τ)) := fun τ => by
    rw [hb.even, kern_neg]
  have hf2 : ∫ τ : ℝ, (b τ - b 0) * (π * kern τ) =
      2 * ∫ τ in Ioi (0 : ℝ), (b τ - b 0) * (π * kern τ) :=
    integral_eq_two_Ioi fun τ => (hev τ).symm
  -- Change of variables on [δ, R] for 0 < δ ≤ R
  have hcomp_seg : ∀ {δ R : ℝ}, 0 < δ → δ ≤ R →
      ∫ τ in δ..R, (b τ - b 0) * (π * kern τ) =
        ∫ t in Real.sinh (π * δ)..Real.sinh (π * R), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 := by
    intro δ R hδ hδR
    have hcont_g : ContinuousOn (fun t : ℝ => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4)
        (Icc (Real.sinh (π * δ)) (Real.sinh (π * R))) := by
      have hsδ : 0 < Real.sinh (π * δ) := sinh_pos_of_pos hδ
      have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
      refine ContinuousOn.div ?_ (continuous_id.pow 4).continuousOn fun t ht =>
        pow_ne_zero 4 (lt_of_lt_of_le hsδ ht.1).ne'
      refine ContinuousOn.sub ?_ (continuous_const.mul (continuous_id.pow 2)).continuousOn
      unfold logAmp
      refine ContinuousOn.log ?_ fun t _ =>
        (div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xChart t))) hAξ).ne'
      have hA_cont : ContinuousOn A (Ici xiStar) := fun x hx =>
        (hA.analytic x hx).continuousAt.continuousWithinAt
      exact (hA_cont.comp_continuous continuous_xChart fun t => xiStar_le_xChart t).div_const _ |>.continuousOn
    have hmaps : MapsTo (fun τ => Real.sinh (π * τ)) (uIcc δ R)
        (Icc (Real.sinh (π * δ)) (Real.sinh (π * R))) := fun τ hτ => by
      rw [uIcc_of_le hδR] at hτ
      exact ⟨Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hτ.1 hpi.le),
        Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hτ.2 hpi.le)⟩
    have hsub := intervalIntegral.integral_comp_mul_deriv' (a := δ) (b := R)
      (f := fun τ => Real.sinh (π * τ)) (f' := fun τ => π * Real.cosh (π * τ))
      (g := fun t => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4)
      (fun τ _ => hd_sinh1 τ)
      (continuous_const.mul (Real.continuous_cosh.comp (by fun_prop))).continuousOn
      (hcont_g.mono (Set.image_subset_iff.mpr hmaps))
    rw [← hsub]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le hδR] at hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le hδ hτ.1
    have hs0 : Real.sinh (π * τ) ≠ 0 := (sinh_pos_of_pos hτ0).ne'
    dsimp only [Function.comp_def]
    rw [hab τ hτ0.ne', ha0, sub_zero, aRel_eq_logAmp_sinh, hb0]
    unfold kern
    field_simp
  -- Take R → ∞, then δ → 0⁺
  have hint_L : Integrable (fun τ : ℝ => (b τ - b 0) * (π * kern τ)) :=
    integrable_slope_integrand hb
  have hint_R : IntegrableOn (fun t : ℝ => (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) (Ioi 0) :=
    integrableOn_logAmp_sub_div_pow_four hA
  have hIoi_δ : ∀ δ : ℝ, 0 < δ →
      ∫ τ in Ioi δ, (b τ - b 0) * (π * kern τ) =
        ∫ t in Ioi (Real.sinh (π * δ)), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 := by
    intro δ hδ
    have hsh_lim : Tendsto (fun R : ℝ => Real.sinh (π * R)) atTop atTop :=
      tendsto_sinh_atTop'.comp (tendsto_id.const_mul_atTop hpi)
    have hL : Tendsto (fun R => ∫ τ in δ..R, (b τ - b 0) * (π * kern τ)) atTop
        (𝓝 (∫ τ in Ioi δ, (b τ - b 0) * (π * kern τ))) :=
      intervalIntegral_tendsto_integral_Ioi δ hint_L.integrableOn tendsto_id
    have hR : Tendsto (fun R => ∫ t in Real.sinh (π * δ)..Real.sinh (π * R),
          (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) atTop
        (𝓝 (∫ t in Ioi (Real.sinh (π * δ)), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4)) :=
      (intervalIntegral_tendsto_integral_Ioi (Real.sinh (π * δ))
        (hint_R.mono_set (Ioi_subset_Ioi (sinh_pos_of_pos hδ).le)) tendsto_id).comp hsh_lim
    have hev' : ∀ᶠ R in atTop,
        (∫ τ in δ..R, (b τ - b 0) * (π * kern τ)) =
          ∫ t in Real.sinh (π * δ)..Real.sinh (π * R),
            (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 := by
      filter_upwards [Filter.eventually_ge_atTop δ] with R hR0
      exact hcomp_seg hδ hR0
    exact tendsto_nhds_unique (hL.congr' hev') hR
  have hlim_L : Tendsto (fun δ : ℝ => ∫ τ in Ioi δ, (b τ - b 0) * (π * kern τ)) (𝓝[>] 0)
      (𝓝 (∫ τ in Ioi (0 : ℝ), (b τ - b 0) * (π * kern τ))) :=
    tendsto_setIntegral_Ioi hint_L
  have hsh_0 : Tendsto (fun δ : ℝ => Real.sinh (π * δ)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Continuous (fun δ : ℝ => Real.sinh (π * δ)) := Real.continuous_sinh.comp (by fun_prop)
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact sinh_pos_of_pos hδ
  have hlim_R : Tendsto (fun δ : ℝ => ∫ t in Ioi (Real.sinh (π * δ)),
        (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4)) := by
    have hbase : Tendsto (fun a : ℝ => ∫ t in Ioi a,
          (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) (𝓝[>] 0)
        (𝓝 (∫ t in Ioi (0 : ℝ), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4)) := by
      -- extend by 0 on `Iic 0` to apply `tendsto_setIntegral_Ioi`
      let g : ℝ → ℝ := fun t => if 0 < t then (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 else 0
      have hg_int : Integrable g := by
        rw [← integrableOn_univ, show (univ : Set ℝ) = Iic 0 ∪ Ioi 0 from (Iic_union_Ioi).symm]
        refine IntegrableOn.union ?_ ?_
        · exact (integrableOn_zero.congr_fun (fun t ht => by
            simp [g, not_lt.mpr ht]) measurableSet_Iic)
        · exact hint_R.congr_fun (fun t ht => by
            dsimp [g]; split_ifs with h
            · rfl
            · exact absurd ht h) measurableSet_Ioi
      have hts := tendsto_setIntegral_Ioi hg_int
      have hge : ∫ t in Ioi (0 : ℝ), g t = ∫ t in Ioi (0 : ℝ), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht => by
          dsimp [g]; split_ifs with h; exact rfl; exact absurd ht h
      rw [hge] at hts
      refine hts.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        dsimp [g]; split_ifs with h; exact rfl; exact absurd (lt_trans ha ht) h
    have h0 := hbase.comp hsh_0
    exact h0
  have hev0 : (fun δ : ℝ => ∫ τ in Ioi δ, (b τ - b 0) * (π * kern τ)) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ => ∫ t in Ioi (Real.sinh (π * δ)), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hIoi_δ δ hδ
  have hIoi_eq : ∫ τ in Ioi (0 : ℝ), (b τ - b 0) * (π * kern τ) =
      ∫ t in Ioi (0 : ℝ), (logAmp A t - ellAmp A 0 / 2 * t ^ 2) / t ^ 4 :=
    tendsto_nhds_unique (hlim_L.congr' hev0) hlim_R
  rw [hf2, hIoi_eq, integral_logAmp_sub_div_pow_four_eq_I3Amp hA]
  ring

end FormalResearch.ModularBootstrap.Mixtures

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.integral_logAmp_div_sq_eq_I1Amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.integral_logAmp_div_sq_eq_I1Amp

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.h1_aRel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.h1_aRel_eq

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.d1_aRel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.d1_aRel_eq

