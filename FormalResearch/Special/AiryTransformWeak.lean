module

public import FormalResearch.Special.AiryTransformKernel
public import FormalResearch.Special.AiryKernelOpFormula
public import FormalResearch.Special.AiryKernelOpL2

/-!
# The Airy transform of `L²(0,∞)` functions: the kernel `Ai(u+t)`

`airyHalf u ∈ L²(ℝ)` is the class of `t ↦ 1_{t>0} Ai(u+t)`; `‖airyHalf u‖² = K(u,u)` and
`⟨airyHalf u, airyHalf v⟩ = K(u,v)` (the Gram form of the Airy kernel, `airyKer_eq_integral`).

For `φ ∈ L²(ℝ)` the function `Ψφ(u) = ∫_{t>0} φ(t) Ai(u+t) dt = ⟨airyHalf u, φ⟩` is defined for **every** `u`
(Cauchy–Schwarz) and **`A(Pφ) = Ψφ` almost everywhere** (`airyA_indProj_ae`), `P` the projection onto `L²(0,∞)`:
the Airy transform of an `L²(0,∞)` function is given by the kernel `Ai(u+t)`.

Proof: both sides are locally integrable; for a test function `g ∈ C_c^∞(ℝ; ℝ)` (a Schwartz function) the
Schwartz kernel formula (`airyA_schwartz_ae`) and self-adjointness of `A` give
`∫ g (A φ) = ⟨ĝ, A φ⟩ = ⟨A ĝ, φ⟩ = ∫ φ(t) ∫ g(u) Ai(u+t) du dt`, and Fubini
(dominated by `|g(u)| ‖φ‖ √K(u,u)`) turns this into `∫ g Ψφ`; then `ae_eq_of_integral_contDiff_smul_eq`.

**Not formalised:** `Ψφ` for `φ` not supported on a half line; continuity/analyticity of `Ψφ` is in
`AiryTransformEval`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set SchwartzMap
open scoped ContDiff ComplexInnerProductSpace FourierTransform Real

namespace FormalResearch.Special

lemma airyHalf_memLp (u : ℝ) :
    MemLp (fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (airyAi (u + t) : ℂ)) t) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (airyAi (u + t) : ℂ)) t)
      volume := by
    refine (Continuous.aestronglyMeasurable ?_).indicator measurableSet_Ioi
    have := continuous_airyAi; fun_prop
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h := (integrableOn_airyAi_shift_sq u)
  rw [← integrable_indicator_iff measurableSet_Ioi] at h
  refine h.congr (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht, Complex.norm_real, sq_abs]

/-- `t ↦ 1_{t>0} Ai(u+t)` as an element of `L²(ℝ)`. -/
noncomputable def airyHalf (u : ℝ) : AiryL2 := (airyHalf_memLp u).toLp _

lemma airyHalf_coeFn (u : ℝ) :
    airyHalf u =ᵐ[volume] fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (airyAi (u + t) : ℂ)) t :=
  (airyHalf_memLp u).coeFn_toLp

/-- `⟨airyHalf u, φ⟩ = ∫_{t>0} φ(t) Ai(u+t) dt`. -/
lemma inner_airyHalf (u : ℝ) (φ : AiryL2) :
    inner ℂ (airyHalf u) φ = ∫ t in Ioi 0, φ t * (airyAi (u + t) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [airyHalf_coeFn u] with t ht
  rw [ht]
  by_cases h : t ∈ Ioi (0 : ℝ)
  · simp [h, mul_comm]
  · simp [h]

lemma inner_airyHalf_airyHalf (u v : ℝ) : inner ℂ (airyHalf u) (airyHalf v) = (airyKer u v : ℂ) := by
  rw [inner_airyHalf, airyKer_eq_integral, ← integral_complex_ofReal]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [airyHalf_coeFn v] with t ht h
  rw [ht]
  simp [h, mul_comm]

lemma norm_airyHalf_sq (u : ℝ) : ‖airyHalf u‖ ^ 2 = airyKer u u := by
  have h := inner_airyHalf_airyHalf u u
  rw [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  rw [← h]
  simp

/-- `Ψφ(u) = ∫_{t>0} φ(t) Ai(u+t) dt`. -/
noncomputable def airyPsi (φ : AiryL2) (u : ℝ) : ℂ := ∫ t in Ioi 0, φ t * (airyAi (u + t) : ℂ)

lemma airyPsi_eq_inner (φ : AiryL2) (u : ℝ) : airyPsi φ u = inner ℂ (airyHalf u) φ :=
  (inner_airyHalf u φ).symm

lemma norm_airyPsi_le (φ : AiryL2) (u : ℝ) : ‖airyPsi φ u‖ ≤ ‖φ‖ * √(airyKer u u) := by
  rw [airyPsi_eq_inner]
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  rw [mul_comm]
  gcongr
  rw [← norm_airyHalf_sq, Real.sqrt_sq (norm_nonneg _)]

lemma integrableOn_airyPsi_integrand (φ : AiryL2) (u : ℝ) :
    IntegrableOn (fun t => φ t * (airyAi (u + t) : ℂ)) (Ioi 0) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (airyHalf u) φ
  rw [← integrable_indicator_iff measurableSet_Ioi]
  refine h.congr ?_
  filter_upwards [airyHalf_coeFn u] with t ht
  rw [ht]
  by_cases hh : t ∈ Ioi (0 : ℝ)
  · simp [hh, mul_comm]
  · simp [hh]

lemma stronglyMeasurable_airy_uncurry (φ : AiryL2) :
    StronglyMeasurable (fun p : ℝ × ℝ => φ p.2 * (airyAi (p.1 + p.2) : ℂ)) := by
  have h1 : StronglyMeasurable (fun p : ℝ × ℝ => (φ : ℝ → ℂ) p.2) :=
    (Lp.stronglyMeasurable φ).comp_measurable measurable_snd
  have h2 : StronglyMeasurable (fun p : ℝ × ℝ => (airyAi (p.1 + p.2) : ℂ)) := by
    have := continuous_airyAi
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => (airyAi (p.1 + p.2) : ℂ)).stronglyMeasurable
  exact h1.mul h2

lemma measurable_airyPsi (φ : AiryL2) : Measurable (airyPsi φ) := by
  have h := (stronglyMeasurable_airy_uncurry φ).indicator
    (s := {p : ℝ × ℝ | 0 < p.2}) (measurableSet_lt measurable_const measurable_snd)
  have h' := h.integral_prod_right (ν := (volume : Measure ℝ))
    (f := fun u t => ({p : ℝ × ℝ | 0 < p.2}.indicator (fun p : ℝ × ℝ => φ p.2 * (airyAi (p.1 + p.2) : ℂ))) (u, t))
  convert h'.measurable using 1
  funext u
  unfold airyPsi
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : (0 : ℝ) < t <;> simp [ht]

lemma continuous_airyKer_diag : Continuous fun u : ℝ => airyKer u u := by
  have h : (fun u : ℝ => airyKer u u) = fun u => airyAi' u ^ 2 - u * airyAi u ^ 2 := by
    funext u; exact airyKer_self u
  rw [h]
  have := continuous_airyAi'
  have := continuous_airyAi
  fun_prop

lemma integrable_norm_sq_lp (φ : AiryL2) : Integrable (fun t => ‖φ t‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable φ)).mp (Lp.memLp φ)

/-- AM-GM bound for the inner integral. -/
lemma airy_inner_norm_le (φ : AiryL2) (u : ℝ) :
    ∫ t in Ioi 0, ‖φ t * (airyAi (u + t) : ℂ)‖ ≤ ((∫ t, ‖φ t‖ ^ 2) + airyKer u u) / 2 := by
  have h1 := (integrable_norm_sq_lp φ).integrableOn (s := Ioi 0)
  have h2 := integrableOn_airyAi_shift_sq u
  have h3 : ∫ t in Ioi 0, ‖φ t * (airyAi (u + t) : ℂ)‖ ≤
      ∫ t in Ioi 0, ((‖φ t‖ ^ 2 + airyAi (u + t) ^ 2) / 2) := by
    refine integral_mono (integrableOn_airyPsi_integrand φ u).norm ((h1.add h2).div_const 2) ?_
    intro t
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [sq_nonneg (‖φ t‖ - |airyAi (u + t)|), sq_abs (airyAi (u + t))]
  refine h3.trans ?_
  rw [integral_div, integral_add h1 h2, ← airyKer_self_eq_integral]
  have := setIntegral_le_integral (μ := volume) (s := Ioi 0) (integrable_norm_sq_lp φ)
    (Eventually.of_forall fun t => sq_nonneg ‖φ t‖)
  linarith

lemma airy_weak_integrable (φ : AiryL2) {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => (g p.1 : ℂ) * (φ p.2 * (airyAi (p.1 + p.2) : ℂ)))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hmeas : StronglyMeasurable (fun p : ℝ × ℝ => (g p.1 : ℂ) * (φ p.2 * (airyAi (p.1 + p.2) : ℂ))) := by
    have h1 : StronglyMeasurable (fun p : ℝ × ℝ => (g p.1 : ℂ)) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => (g p.1 : ℂ)).stronglyMeasurable
    exact h1.mul (stronglyMeasurable_airy_uncurry φ)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun u => ?_, ?_⟩
  · exact (integrableOn_airyPsi_integrand φ u).const_mul (g u : ℂ)
  · set N := ∫ t, ‖φ t‖ ^ 2 with hN
    have hb : Continuous fun u : ℝ => |g u| * ((N + airyKer u u) / 2) := by
      have := continuous_airyKer_diag
      fun_prop
    have hbc : HasCompactSupport fun u : ℝ => |g u| * ((N + airyKer u u) / 2) :=
      (hgc.abs).mul_right
    refine (hb.integrable_of_hasCompactSupport hbc).mono' ?_ (Eventually.of_forall fun u => ?_)
    · exact hmeas.aestronglyMeasurable.norm.integral_prod_right'
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      have : ∀ t : ℝ, ‖(g (u, t).1 : ℂ) * (φ (u, t).2 * (airyAi ((u, t).1 + (u, t).2) : ℂ))‖ =
          |g u| * ‖φ t * (airyAi (u + t) : ℂ)‖ := by
        intro t; simp
      simp_rw [this]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (airy_inner_norm_le φ u) (abs_nonneg _)

/-- The test function `g` as a Schwartz function. -/
noncomputable def airyTestSchwartz {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun u => (g u : ℂ))
    (hgc.comp_left (g := Complex.ofReal) (by simp)) (Complex.ofRealCLM.contDiff.comp hg)

lemma airyTestSchwartz_apply {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (u : ℝ) :
    airyTestSchwartz hg hgc u = (g u : ℂ) := rfl

/-- **Weak form**: `∫ g (A φ) = ∫ g Ψφ` for `φ ∈ L²(0,∞)` and smooth compactly supported real `g`. -/
lemma airy_weak_test (φ : AiryL2) (hφ : airyIndProj (measurableSet_Ioi (a := (0 : ℝ))) φ = φ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ u, g u • airyA φ u = ∫ u, g u • airyPsi φ u := by
  set G := airyTestSchwartz hg hgc with hG
  have hgcont : Continuous g := hg.continuous
  -- left side as an inner product
  have h1 : ∫ u, g u • airyA φ u = inner ℂ (G.toLp 2) (airyA φ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp G 2 (volume : Measure ℝ)] with u hu
    rw [hu, hG, airyTestSchwartz_apply, Complex.real_smul]
    simp [mul_comm]
  have h2 := airyA_inner_left (G.toLp 2) φ
  have h3 : inner ℂ (airyA (G.toLp 2)) φ =
      ∫ t, (∫ u, (g u : ℂ) * (airyAi (t + u) : ℂ)) * φ t := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [airyA_schwartz_ae G] with t ht
    rw [ht]
    have hr : starRingEnd ℂ (∫ u, G u * (airyAi (t + u) : ℂ)) = ∫ u, G u * (airyAi (t + u) : ℂ) := by
      have : ∫ u, G u * (airyAi (t + u) : ℂ) = ((∫ u, g u * airyAi (t + u) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp [hG, airyTestSchwartz_apply]
      rw [this]; exact Complex.conj_ofReal _
    simp only [RCLike.inner_apply, hr]
    simp only [hG, airyTestSchwartz_apply]
    ring
  have h4 : ∫ t, (∫ u, (g u : ℂ) * (airyAi (t + u) : ℂ)) * φ t =
      ∫ t in Ioi 0, (∫ u, (g u : ℂ) * (airyAi (t + u) : ℂ)) * φ t := by
    symm
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    have := (airyIndProj_eq_self_iff _ φ).mp hφ
    filter_upwards [this] with t ht htc
    rw [ht htc, mul_zero]
  have h5 : ∫ t in Ioi 0, (∫ u, (g u : ℂ) * (airyAi (t + u) : ℂ)) * φ t =
      ∫ u, g u • airyPsi φ u := by
    have hint := airy_weak_integrable φ hgcont hgc
    have swap := integral_integral_swap (μ := (volume : Measure ℝ)) (ν := volume.restrict (Ioi (0 : ℝ)))
      (f := fun (u t : ℝ) => (g u : ℂ) * (φ t * (airyAi (u + t) : ℂ))) hint
    have e1 : ∀ u : ℝ, g u • airyPsi φ u = ∫ t in Ioi 0, (g u : ℂ) * (φ t * (airyAi (u + t) : ℂ)) := by
      intro u
      rw [airyPsi, integral_const_mul, Complex.real_smul]
    simp_rw [e1]
    rw [swap]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [add_comm t u]
    ring
  rw [h1, ← h2, h3, h4, h5]

lemma locallyIntegrable_airyPsi (φ : AiryL2) : LocallyIntegrable (airyPsi φ) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hc : Continuous fun u : ℝ => ‖φ‖ * √(airyKer u u) := by
    have := continuous_airyKer_diag
    fun_prop
  refine (hc.continuousOn.integrableOn_compact hK).mono' (measurable_airyPsi φ).aestronglyMeasurable ?_
  exact (ae_restrict_of_forall_mem hK.measurableSet fun u _ => norm_airyPsi_le φ u)

lemma airyPsi_indProj (φ : AiryL2) :
    airyPsi (airyIndProj (measurableSet_Ioi (a := (0 : ℝ))) φ) = airyPsi φ := by
  funext u
  unfold airyPsi
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [airyIndProj_coeFn (measurableSet_Ioi (a := (0 : ℝ))) φ] with t ht htm
  rw [ht]; simp [htm]

/-- **The Airy transform of an `L²(0,∞)` function is given by the kernel `Ai(u+t)`**:
`A(Pφ)(u) = ∫_{t>0} φ(t) Ai(u+t) dt` for almost every `u`. -/
theorem airyA_indProj_ae (φ : AiryL2) :
    airyA (airyIndProj (measurableSet_Ioi (a := (0 : ℝ))) φ) =ᵐ[volume] airyPsi φ := by
  set φ₀ := airyIndProj (measurableSet_Ioi (a := (0 : ℝ))) φ with hφ₀
  have hidem : airyIndProj (measurableSet_Ioi (a := (0 : ℝ))) φ₀ = φ₀ := airyIndProj_idem _ φ
  have h := ae_eq_of_integral_contDiff_smul_eq
    (((Lp.memLp (airyA φ₀)).locallyIntegrable (by norm_num)) : LocallyIntegrable (airyA φ₀) volume)
    (locallyIntegrable_airyPsi φ₀) (fun g hg hgc => airy_weak_test φ₀ hidem hg hgc)
  rw [hφ₀, airyPsi_indProj] at h
  exact h

/-- Corollary: if `φ ∈ L²(ℝ)` vanishes a.e. on `(-∞, 0]`, then `(Aφ)(u) = ∫ φ(t) Ai(u+t) dt` a.e. -/
theorem airyA_ae_of_support (φ : AiryL2) (hφ : ∀ᵐ t ∂volume, t ∉ Ioi (0 : ℝ) → φ t = 0) :
    airyA φ =ᵐ[volume] airyPsi φ := by
  have h := (airyIndProj_eq_self_iff (measurableSet_Ioi (a := (0 : ℝ))) φ).mpr hφ
  have := airyA_indProj_ae φ
  rwa [h] at this

/-- info: 'FormalResearch.Special.airyA_indProj_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyA_indProj_ae

end FormalResearch.Special
