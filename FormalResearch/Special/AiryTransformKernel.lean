module

public import FormalResearch.Special.AiryTransformDef
public import FormalResearch.Special.AiryGram
public import FormalResearch.Special.AiryCftWeights

/-!
# The kernel of the Airy transform on Schwartz functions

For a Schwartz function `f`, `(𝒜 f)(u) = ∫ f(t) Ai(u - t) dt` (`airyTransform_schwartz_apply`), hence
`(A f)(u) = ∫ f(t) Ai(u + t) dt` (`airyA_schwartz_apply`).

Proof: `𝒜 f = 𝓕⁻¹(m · 𝓕 f)` (Mathlib's `𝓕` on Schwartz functions and `L²` agree), so
`(𝒜 f)(u) = ∫ m(ξ) f̂(ξ) e^{2πi uξ} dξ`.  Abel regularisation: for `c > 0` the tilted function
`e^{cx} Ai(x) = 𝓕 h_c`, `h_c(ξ) = exp((c+2πiξ)³/3)` (`AiryFourier`), is integrable, and Fubini gives
`∫ f(t) e^{c(u-t)} Ai(u-t) dt = ∫ h_c(-ξ) f̂(ξ) e^{2πiuξ} dξ`.  As `c → 0⁺` the left side tends to
`∫ f(t) Ai(u-t) dt` by dominated convergence (`|e^{cx} Ai(x)| ≤ C` uniformly for `0 < c ≤ 1`) and the right
side to `∫ m(ξ) f̂(ξ) e^{2πi uξ} dξ` (`|h_c| ≤ e^{c³/3}`).

Numerical check (mpmath, 30 digits): `f(t) = e^{-t²}`, `u = 0.7, -1.3`: `∫ e^{2πiuξ} e^{i(2πξ)³/3} f̂(ξ) dξ` and
`∫ f(t) Ai(u-t) dt` both equal `0.3774914224908578168830376`, `0.6751522004004783603266278`, difference `< 10⁻³⁸`.

**Not formalised:** the general `L²` kernel statement (see `AiryTransformWeak` for `φ` supported in a half line; for general
`φ ∈ L²(ℝ)` the integral `∫ φ(t) Ai(u+t) dt` need not converge).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set SchwartzMap
open scoped ENNReal ComplexInnerProductSpace FourierTransform Real

namespace FormalResearch.Special

lemma abs_airyAi_le_three (x : ℝ) : |airyAi x| ≤ 3 := by
  have h := airyAiC_norm_sq_le (x : ℂ)
  have h1 := airyEnv_ofReal_le_one x
  have h2 : (1 + ‖(x : ℂ)‖) ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (x : ℂ)]) (by norm_num)
  have h3 := airyEnv_pos (x : ℂ)
  have h4 : 0 < (1 + ‖(x : ℂ)‖) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  have h5 : (1 + ‖(x : ℂ)‖) ^ (-(1 / 2) : ℝ) * airyEnv (x : ℂ) ≤ 1 := by nlinarith
  nlinarith [abs_nonneg (airyAi x)]

lemma airyMult_hasTemperateGrowth : airyMult.HasTemperateGrowth := by
  have h : airyMult = (fun y : ℝ => cexp (y * I)) ∘ (fun ξ : ℝ => ((2 * π * ξ) ^ 3 / 3 : ℝ)) := by
    funext ξ; simp only [airyMult, Function.comp]; rw [mul_comm]
  rw [h]
  refine Function.HasTemperateGrowth.comp Complex.hasTemperateGrowth_exp_mul_I ?_
  have : (fun ξ : ℝ => (2 * π * ξ) ^ 3 / 3) = fun ξ => ((2 * π) ^ 3 / 3) * ξ ^ 3 := by
    funext ξ; ring
  rw [this]
  fun_prop

/-- On a Schwartz function, `𝒜 f` is the Schwartz function `𝓕⁻ (m · 𝓕 f)`. -/
lemma airyTransform_toLp (f : 𝓢(ℝ, ℂ)) :
    airyTransform (f.toLp 2) = (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ airyMult (𝓕 f))).toLp 2 := by
  rw [airyTransform_apply]
  have h1 : airyF (f.toLp 2) = (𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq f
  rw [h1]
  have h2 : airyM ((𝓕 f).toLp 2) = (SchwartzMap.smulLeftCLM ℂ airyMult (𝓕 f)).toLp 2 := by
    refine Lp.ext ?_
    filter_upwards [airyM_coeFn ((𝓕 f).toLp 2), SchwartzMap.coeFn_toLp (𝓕 f) 2 (volume : Measure ℝ),
      SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM ℂ airyMult (𝓕 f)) 2 (volume : Measure ℝ)]
      with ξ h1 h2 h3
    rw [h1, h2, h3, SchwartzMap.smulLeftCLM_apply_apply airyMult_hasTemperateGrowth]
    rfl
  rw [h2]
  exact SchwartzMap.toLp_fourierInv_eq _

lemma airyTransform_schwartz_eq (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ airyMult (𝓕 f))) u =
      ∫ ξ : ℝ, cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) * (airyMult ξ * (𝓕 f) ξ) := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have hin : inner ℝ ξ u = ξ * u := by simp [mul_comm]
  simp only [smul_eq_mul, hin]
  rw [SchwartzMap.smulLeftCLM_apply_apply airyMult_hasTemperateGrowth, smul_eq_mul]

/-! ### Abel regularisation -/

lemma integrable_airyFourierH {c : ℝ} (hc : 0 < c) : Integrable (airyFourierH c) := by
  unfold airyFourierH
  exact (integrable_airyFourierSymbol hc).comp_mul_left' (by positivity)

lemma continuous_airyFourierH (c : ℝ) : Continuous (airyFourierH c) := by
  unfold airyFourierH
  exact (continuous_airyFourierSymbol c).comp (by fun_prop)

lemma airyTilt_eq_integral {c : ℝ} (hc : 0 < c) (x : ℝ) :
    airyTilt c x = ∫ ξ : ℝ, cexp (((-2 * π * ξ * x : ℝ) : ℂ) * I) * airyFourierH c ξ := by
  have h := fourier_airyFourierH hc x
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  simpa only [smul_eq_mul] using h.symm

/-- Fubini step: `∫ f(t) e^{c(u-t)} Ai(u-t) dt = ∫ h_c(-ξ) f̂(ξ) e^{2πiuξ} dξ`. -/
lemma airy_abel_fubini {c : ℝ} (hc : 0 < c) (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ∫ t : ℝ, f t * airyTilt c (u - t) =
      ∫ ξ : ℝ, cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) * (airyFourierH c (-ξ) * (𝓕 f) ξ) := by
  have hH := integrable_airyFourierH hc
  have hHc := continuous_airyFourierH c
  have e1 : ∀ t : ℝ, f t * airyTilt c (u - t) =
      ∫ ξ : ℝ, f t * (cexp (((-2 * π * ξ * (u - t) : ℝ) : ℂ) * I) * airyFourierH c ξ) := by
    intro t; rw [airyTilt_eq_integral hc, integral_const_mul]
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun (t ξ : ℝ) =>
      f t * (cexp (((-2 * π * ξ * (u - t) : ℝ) : ℂ) * I) * airyFourierH c ξ)) (volume.prod volume) := by
    refine (((f.integrable (μ := volume)).mul_prod hH).norm).mono' ?_ (Eventually.of_forall fun z => ?_)
    · have : Continuous (Function.uncurry fun (t ξ : ℝ) =>
          f t * (cexp (((-2 * π * ξ * (u - t) : ℝ) : ℂ) * I) * airyFourierH c ξ)) := by
        have := f.continuous
        have := hHc
        show Continuous fun z : ℝ × ℝ =>
          f z.1 * (cexp (((-2 * π * z.2 * (u - z.1) : ℝ) : ℂ) * I) * airyFourierH c z.2)
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  rw [integral_integral_swap hint]
  have e2 : ∀ ξ : ℝ, ∫ t : ℝ, f t * (cexp (((-2 * π * ξ * (u - t) : ℝ) : ℂ) * I) * airyFourierH c ξ) =
      (airyFourierH c ξ * cexp (((-2 * π * ξ * u : ℝ) : ℂ) * I)) * (𝓕 f) (-ξ) := by
    intro ξ
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    have : cexp (((-2 * π * ξ * (u - t) : ℝ) : ℂ) * I) =
        cexp (((-2 * π * ξ * u : ℝ) : ℂ) * I) * cexp (((-2 * π * t * (-ξ) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [e2]
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [neg_neg, airyFourierH]
  have : cexp (((-2 * π * (-ξ) * u : ℝ) : ℂ) * I) = cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [this]; ring

lemma norm_airyFourierSymbol (c s : ℝ) : ‖airyFourierSymbol c s‖ = Real.exp (c ^ 3 / 3 - c * s ^ 2) := by
  have : airyFourierSymbol c s = airyKernel c 0 s := by simp [airyFourierSymbol, airyKernel]
  rw [this, norm_airyKernel]; simp

lemma norm_airyFourierH_le {c : ℝ} (h0 : 0 ≤ c) (hc : c ≤ 1) (ξ : ℝ) :
    ‖airyFourierH c ξ‖ ≤ Real.exp 1 := by
  unfold airyFourierH
  rw [norm_airyFourierSymbol]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [sq_nonneg (2 * π * ξ), pow_le_one₀ h0 hc (n := 3), mul_nonneg h0 (sq_nonneg (2 * π * ξ))]

lemma norm_airyTilt_eq (c x : ℝ) : ‖airyTilt c x‖ = |airyAi x| * Real.exp (c * x) := by
  unfold airyTilt
  rw [norm_mul, Complex.norm_real, Complex.norm_exp]
  simp

lemma norm_airyTilt_le_const : ∃ B : ℝ, ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ x : ℝ, ‖airyTilt c x‖ ≤ B := by
  refine ⟨3 + ((1 / (2 * π)) * (Real.exp ((2 * 1) ^ 3 / 3) * √(π / (2 * 1))) +
      (1 / (2 * π)) * (Real.exp ((1 / 2) ^ 3 / 3) * √(π / (1 / 2)))), fun c hc hc1 x => ?_⟩
  have hK := norm_airyTilt_le (c := 1) one_pos x
  have hK0 : 0 ≤ ((1 / (2 * π)) * (Real.exp ((2 * 1) ^ 3 / 3) * √(π / (2 * 1))) +
      (1 / (2 * π)) * (Real.exp ((1 / 2) ^ 3 / 3) * √(π / (1 / 2)))) := by positivity
  have hE : Real.exp (-(1 / 2) * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := abs_nonneg x; nlinarith)
  rw [norm_airyTilt_eq]
  rcases le_total 0 x with hx | hx
  · have h1 : |airyAi x| * Real.exp (c * x) ≤ |airyAi x| * Real.exp (1 * x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)
    rw [norm_airyTilt_eq] at hK
    have := mul_le_of_le_one_right hK0 hE
    nlinarith
  · have h1 : Real.exp (c * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have := abs_airyAi_le_three x
    have h2 : |airyAi x| * Real.exp (c * x) ≤ 3 := by
      calc _ ≤ |airyAi x| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ 3 := by linarith
    linarith

/-- Left limit: `∫ f(t) e^{c(u-t)} Ai(u-t) dt → ∫ f(t) Ai(u-t) dt` as `c → 0⁺`. -/
lemma tendsto_airy_abel_left (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    Tendsto (fun c : ℝ => ∫ t : ℝ, f t * airyTilt c (u - t)) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, f t * (airyAi (u - t) : ℂ))) := by
  obtain ⟨B, hB⟩ := norm_airyTilt_le_const
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖ * B) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun c => (f.continuous.mul ((continuous_airyTilt c).comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with c hc
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB c hc.1 hc.2.le _) (norm_nonneg _)
  · exact (f.integrable.norm).mul_const B
  · refine Eventually.of_forall fun t => ?_
    have hc : Continuous fun c : ℝ => f t * airyTilt c (u - t) := by
      unfold airyTilt; have := continuous_airyAi; fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [airyTilt] using this

/-- Right limit: `∫ h_c(-ξ) f̂(ξ) e^{2πiuξ} dξ → ∫ m(ξ) f̂(ξ) e^{2πiuξ} dξ`. -/
lemma tendsto_airy_abel_right (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    Tendsto (fun c : ℝ => ∫ ξ : ℝ, cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) *
        (airyFourierH c (-ξ) * (𝓕 f) ξ)) (𝓝[>] 0)
      (𝓝 (∫ ξ : ℝ, cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) * (airyMult ξ * (𝓕 f) ξ))) := by
  have hf : Integrable (fun ξ => (𝓕 f) ξ) := (𝓕 f).integrable (μ := volume)
  refine tendsto_integral_filter_of_dominated_convergence (fun ξ => Real.exp 1 * ‖(𝓕 f) ξ‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun c => ?_
    have := (𝓕 f).continuous
    have := continuous_airyFourierH c
    exact (by fun_prop : Continuous fun ξ : ℝ => cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) *
        (airyFourierH c (-ξ) * (𝓕 f) ξ)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with c hc
    refine Eventually.of_forall fun ξ => ?_
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul_of_nonneg_right (norm_airyFourierH_le hc.1.le hc.2.le _) (norm_nonneg _)
  · exact hf.norm.const_mul _
  · refine Eventually.of_forall fun ξ => ?_
    have hc : Continuous fun c : ℝ => cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) *
        (airyFourierH c (-ξ) * (𝓕 f) ξ) := by
      unfold airyFourierH airyFourierSymbol airyLine; fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have e : airyFourierH 0 (-ξ) = airyMult ξ := by
      unfold airyFourierH airyFourierSymbol airyLine airyMult
      congr 1
      have hI : (I : ℂ) ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
      push_cast
      linear_combination (-(2 * (π : ℂ) * ξ) ^ 3 / 3) * hI
    rw [e] at h0
    exact h0

/-- **Abel identity**: for a Schwartz function `f`,
`∫ m(ξ) f̂(ξ) e^{2πiuξ} dξ = ∫ f(t) Ai(u-t) dt`. -/
theorem airy_abel_identity (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ∫ ξ : ℝ, cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) * (airyMult ξ * (𝓕 f) ξ) =
      ∫ t : ℝ, f t * (airyAi (u - t) : ℂ) := by
  have h1 := tendsto_airy_abel_left f u
  have h2 := tendsto_airy_abel_right f u
  have h3 : (fun c : ℝ => ∫ t : ℝ, f t * airyTilt c (u - t)) =ᶠ[𝓝[>] 0]
      fun c : ℝ => ∫ ξ : ℝ, cexp (((2 * π * (ξ * u) : ℝ) : ℂ) * I) *
        (airyFourierH c (-ξ) * (𝓕 f) ξ) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact airy_abel_fubini hc f u
  exact tendsto_nhds_unique (h1.congr' h3) h2 |>.symm

/-- **Kernel of `𝒜` on Schwartz functions**: `(𝒜 f)(u) = ∫ f(t) Ai(u-t) dt` (a.e., indeed for the
continuous representative). -/
theorem airyTransform_schwartz_ae (f : 𝓢(ℝ, ℂ)) :
    airyTransform (f.toLp 2) =ᵐ[volume] fun u => ∫ t : ℝ, f t * (airyAi (u - t) : ℂ) := by
  rw [airyTransform_toLp]
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ airyMult (𝓕 f))) 2
    (volume : Measure ℝ)] with u hu
  rw [hu, airyTransform_schwartz_eq, airy_abel_identity]

/-- The reflected Schwartz function `t ↦ f(-t)`. -/
noncomputable def airySchwartzNeg (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

lemma airySchwartzNeg_apply (f : 𝓢(ℝ, ℂ)) (t : ℝ) : airySchwartzNeg f t = f (-t) := by
  simp [airySchwartzNeg]

lemma airyReflect_toLp (f : 𝓢(ℝ, ℂ)) :
    airyReflect (f.toLp 2) = (airySchwartzNeg f).toLp 2 := by
  refine Lp.ext ?_
  have e1 := airyReflect_coeFn (f.toLp 2)
  have e2 := SchwartzMap.coeFn_toLp f 2 (volume : Measure ℝ)
  have e3 : (fun x : ℝ => ((f.toLp 2 : AiryL2)) (-x)) =ᵐ[volume] fun x => f (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp e2
  filter_upwards [e1, e3, SchwartzMap.coeFn_toLp (airySchwartzNeg f) 2 (volume : Measure ℝ)]
    with x h1 h3 h4
  rw [h1, h3, h4, airySchwartzNeg_apply]

/-- **Kernel of `A` on Schwartz functions**: `(A f)(u) = ∫ f(t) Ai(u+t) dt`. -/
theorem airyA_schwartz_ae (f : 𝓢(ℝ, ℂ)) :
    airyA (f.toLp 2) =ᵐ[volume] fun u => ∫ t : ℝ, f t * (airyAi (u + t) : ℂ) := by
  rw [airyA_apply, airyReflect_toLp]
  filter_upwards [airyTransform_schwartz_ae (airySchwartzNeg f)] with u hu
  rw [hu]
  simp_rw [airySchwartzNeg_apply]
  have := integral_neg_eq_self (fun t : ℝ => f t * (airyAi (u + t) : ℂ)) volume
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [sub_eq_add_neg]

/-- info: 'FormalResearch.Special.airy_abel_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_abel_identity

/-- info: 'FormalResearch.Special.airyTransform_schwartz_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyTransform_schwartz_ae

/-- info: 'FormalResearch.Special.airyA_schwartz_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyA_schwartz_ae

end FormalResearch.Special
