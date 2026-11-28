module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BandBoundW
public import FormalResearch.ModularBootstrap.Mixtures.CommonSource
public import FormalResearch.ModularBootstrap.Mixtures.WeightAxioms

/-!
# Proposition `Y_V` for Signed Common Sources (`pmix:o1`, `lower_o1_two_edge.tex`, §J4)

Adapts `FixedWeightBand.proposition_YV_of_spec_W` to `CommonSource` without duplicating
`LemmaS4W`, `LemmaJ4`, `EdgeKernelWFactor`, `BandBoundWAux`, or `StripBand`:
since `C.F.prob.w = C.src.w` and `C.F.d * C.F.prob.cardyV a t ≤ C.src.cardyV a t`,
the signed-source Mellin transform `tildeWW C.src.w c' g` satisfies the exact edge identity
with kernel `edgeKernelKWSrc C.src c' τ t = (Q₀.cardyV / src.cardyV) * edgeKernelKW C.F.prob c' τ t`,
and the resulting `BandReductionInstance` shares `a_0, R_0, Phi, ν, m, τ_0, u_tilde, Delta`
with `ywBandInstance C.F.prob pg`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Mixtures

open Crossing Chart StripMultiplier StripBand FixedWeightBand WeightAxioms

/-! ### Section 1: Signed-source band measures -/

/-- Normalized positive part density of `g * src.cardyV a` on `Ioi 0`:
`(g₊ * src.V) / M_src[g]`. -/
noncomputable def bandPosSrc (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (g t) 0 * src.cardyV a t / src.cardyNorm a g

/-- Normalized negative part density of `g * src.cardyV a` on `Ioi 0`:
`(g₋ * src.V) / M_src[g]`. -/
noncomputable def bandNegSrc (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (-g t) 0 * src.cardyV a t / src.cardyNorm a g

/-- Positive band measure `dmPosSrc = bandPosSrc · dVol|_{Ioi 0}`. -/
noncomputable def bandMeasPosSrc (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (bandPosSrc src a g t))

/-- Negative band measure `dmNegSrc = bandNegSrc · dVol|_{Ioi 0}`. -/
noncomputable def bandMeasNegSrc (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (bandNegSrc src a g t))

lemma cardyNorm_src_nonneg {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) (g : ℝ → ℝ) :
    0 ≤ C.src.cardyNorm a g := by
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  exact mul_nonneg (abs_nonneg _) ((C.at_ ha).nonneg_V (mem_Ioi.mp ht).le)

lemma bandPosSrc_nonneg {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) (g : ℝ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ bandPosSrc C.src a g t :=
  div_nonneg (mul_nonneg (le_max_right _ _) ((C.at_ ha).nonneg_V ht))
    (cardyNorm_src_nonneg ha g)

lemma bandNegSrc_nonneg {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) (g : ℝ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ bandNegSrc C.src a g t :=
  div_nonneg (mul_nonneg (le_max_right _ _) ((C.at_ ha).nonneg_V ht))
    (cardyNorm_src_nonneg ha g)

lemma bandPosSrc_add_bandNegSrc (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    bandPosSrc src a g t + bandNegSrc src a g t =
      |g t| * src.cardyV a t / src.cardyNorm a g := by
  unfold bandPosSrc bandNegSrc
  have habs : max (g t) 0 + max (-g t) 0 = |g t| := by
    rcases le_total 0 (g t) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero, abs_of_nonneg h]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add, abs_of_nonpos h]
  rw [← add_div, ← add_mul, habs]

lemma bandPosSrc_aemeasurable {src : ShiftSource} {a : ℝ} {g : ℝ → ℝ} (hg : TestClass src a g) :
    AEMeasurable (bandPosSrc src a g) (volume.restrict (Ioi 0)) := by
  have hV_cont := src.continuous_cardyV a
  have hcont : ContinuousOn (bandPosSrc src a g) (Ioi 0) := fun t ht =>
    (((hg.cont.mono Ioi_subset_Ici_self t ht).sup continuousWithinAt_const).mul
      hV_cont.continuousWithinAt).div_const _
  exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable

lemma bandNegSrc_aemeasurable {src : ShiftSource} {a : ℝ} {g : ℝ → ℝ} (hg : TestClass src a g) :
    AEMeasurable (bandNegSrc src a g) (volume.restrict (Ioi 0)) := by
  have hV_cont := src.continuous_cardyV a
  have hcont : ContinuousOn (bandNegSrc src a g) (Ioi 0) := fun t ht =>
    (((hg.cont.mono Ioi_subset_Ici_self t ht).neg.sup continuousWithinAt_const).mul
      hV_cont.continuousWithinAt).div_const _
  exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable

lemma bandPosSrc_integrableOn {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) {g : ℝ → ℝ}
    (hg : TestClass C.src a g) :
    IntegrableOn (bandPosSrc C.src a g) (Ioi 0) := by
  refine (hg.int_cardy.div_const (C.src.cardyNorm a g)).mono'
    (bandPosSrc_aemeasurable hg).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_of_nonneg (bandPosSrc_nonneg ha g (mem_Ioi.mp ht).le),
    ← bandPosSrc_add_bandNegSrc]
  linarith [bandNegSrc_nonneg ha g (mem_Ioi.mp ht).le]

lemma bandNegSrc_integrableOn {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) {g : ℝ → ℝ}
    (hg : TestClass C.src a g) :
    IntegrableOn (bandNegSrc C.src a g) (Ioi 0) := by
  refine (hg.int_cardy.div_const (C.src.cardyNorm a g)).mono'
    (bandNegSrc_aemeasurable hg).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_of_nonneg (bandNegSrc_nonneg ha g (mem_Ioi.mp ht).le),
    ← bandPosSrc_add_bandNegSrc]
  linarith [bandPosSrc_nonneg ha g (mem_Ioi.mp ht).le]

lemma bandMeasPosSrc_univ {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) {g : ℝ → ℝ}
    (hg : TestClass C.src a g) :
    bandMeasPosSrc C.src a g univ = ENNReal.ofReal (∫ t in Ioi 0, bandPosSrc C.src a g t) := by
  unfold bandMeasPosSrc
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (bandPosSrc_integrableOn ha hg)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht =>
      bandPosSrc_nonneg ha g (mem_Ioi.mp ht).le)).symm

lemma bandMeasNegSrc_univ {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) {g : ℝ → ℝ}
    (hg : TestClass C.src a g) :
    bandMeasNegSrc C.src a g univ = ENNReal.ofReal (∫ t in Ioi 0, bandNegSrc C.src a g t) := by
  unfold bandMeasNegSrc
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (bandNegSrc_integrableOn ha hg)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht =>
      bandNegSrc_nonneg ha g (mem_Ioi.mp ht).le)).symm

lemma bandMeasPosSrc_isFinite {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) {g : ℝ → ℝ}
    (hg : TestClass C.src a g) : IsFiniteMeasure (bandMeasPosSrc C.src a g) :=
  ⟨by rw [bandMeasPosSrc_univ ha hg]; exact ENNReal.ofReal_lt_top⟩

lemma bandMeasNegSrc_isFinite {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) {g : ℝ → ℝ}
    (hg : TestClass C.src a g) : IsFiniteMeasure (bandMeasNegSrc C.src a g) :=
  ⟨by rw [bandMeasNegSrc_univ ha hg]; exact ENNReal.ofReal_lt_top⟩

lemma bandMeasPosSrc_Iic (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) :
    bandMeasPosSrc src a g (Iic 0) = 0 := by
  unfold bandMeasPosSrc
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]

lemma bandMeasNegSrc_Iic (src : ShiftSource) (a : ℝ) (g : ℝ → ℝ) :
    bandMeasNegSrc src a g (Iic 0) = 0 := by
  unfold bandMeasNegSrc
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]

lemma bandMeasSrc_tv {C : CommonSource} {a : ℝ} (ha : C.a₀ ≤ a) {g : ℝ → ℝ}
    (hg : TestClass C.src a g) (hM_pos : 0 < C.src.cardyNorm a g) :
    (bandMeasPosSrc C.src a g univ).toReal + (bandMeasNegSrc C.src a g univ).toReal = 1 := by
  rw [bandMeasPosSrc_univ ha hg, bandMeasNegSrc_univ ha hg,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun t ht =>
      bandPosSrc_nonneg ha g (mem_Ioi.mp ht).le),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun t ht =>
      bandNegSrc_nonneg ha g (mem_Ioi.mp ht).le),
    ← integral_add (bandPosSrc_integrableOn ha hg) (bandNegSrc_integrableOn ha hg)]
  have heq : EqOn (fun t => bandPosSrc C.src a g t + bandNegSrc C.src a g t)
      (fun t => |g t| * C.src.cardyV a t / C.src.cardyNorm a g) (Ioi 0) :=
    fun t _ => bandPosSrc_add_bandNegSrc C.src a g t
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_div]
  change C.src.cardyNorm a g / C.src.cardyNorm a g = 1
  exact div_self hM_pos.ne'

lemma bandMeasNegSrc_Ici_eq_zero (src : ShiftSource) (a : ℝ) {g : ℝ → ℝ} {T : ℝ}
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    bandMeasNegSrc src a g (Ici T) = 0 := by
  unfold bandMeasNegSrc
  rw [withDensity_apply _ measurableSet_Ici]
  refine setLIntegral_eq_zero measurableSet_Ici fun t ht => ?_
  have hgt := hg_nonneg t ht
  unfold bandNegSrc
  rw [max_eq_right (neg_nonpos.mpr hgt), zero_mul, zero_div, ENNReal.ofReal_zero]
  rfl

/-- If `M_src[g] > 0` for `c' ≥ max 1 (max (24 * S₀) (24 * a₀))`, then `M_{Q₀}[g] > 0`. -/
lemma cardyNorm_prob_pos_of_src_pos (C : CommonSource) {c' : ℝ}
    (hc' : max 1 (max (24 * C.F.prob.totalShift) (24 * C.a₀)) ≤ c')
    {g : ℝ → ℝ} (hg : TestClass C.src (c' / 12) g) (hM : 0 < C.src.cardyNorm (c' / 12) g) :
    0 < C.F.prob.cardyNorm (c' / 12) g := by
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c' :=
    max_le hc'1 ((le_max_left _ _).trans ((le_max_right _ _).trans hc'))
  have ha : C.a₀ ≤ c' / 12 := by
    have h1 : 24 * C.a₀ ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans hc')
    linarith
  have hS : C.F.prob.totalShift ≤ c' / 12 := by
    have h1 : 24 * C.F.prob.totalShift ≤ c' := (le_max_right _ _).trans hc'_prob
    linarith
  have hAt := C.at_ ha
  have hg0 := hAt.testClass_prob hg
  have hM0_nn : 0 ≤ C.F.prob.cardyNorm (c' / 12) g :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (C.F.prob.cardyV_nonneg hS (mem_Ioi.mp ht).le)
  by_contra hle
  push Not at hle
  have hM0_zero : C.F.prob.cardyNorm (c' / 12) g = 0 := le_antisymm hle hM0_nn
  have hae0 : (fun t => |g t| * C.F.prob.cardyV (c' / 12) t) =ᵐ[volume.restrict (Ioi 0)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (abs_nonneg _) (C.F.prob.cardyV_nonneg hS (mem_Ioi.mp ht).le))
      hg0.int_cardy).mp hM0_zero
  have hsupp_src : 0 < volume (Function.support (fun t => |g t| * C.src.cardyV (c' / 12) t) ∩ Ioi 0) :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (abs_nonneg _) (hAt.nonneg_V (mem_Ioi.mp ht).le))
      hg.int_cardy).mp hM
  have hne : (Function.support (fun t => |g t| * C.src.cardyV (c' / 12) t) ∩ Ioi 0).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty.mp hemp, measure_empty] at hsupp_src
    exact lt_irrefl 0 hsupp_src
  obtain ⟨t₀, ht₀_supp, ht₀_pos⟩ := hne
  have hgt₀_ne : g t₀ ≠ 0 := by
    intro hzero
    exact ht₀_supp (by simp [hzero])
  have hV0_pos : 0 < C.F.prob.cardyV (c' / 12) t₀ :=
    cardyV_pos_of_max hc'_prob (mem_Ioi.mp ht₀_pos)
  have hf0_pos : 0 < |g t₀| * C.F.prob.cardyV (c' / 12) t₀ :=
    mul_pos (abs_pos.mpr hgt₀_ne) hV0_pos
  have hf_cont : ContinuousOn (fun t => |g t| * C.F.prob.cardyV (c' / 12) t) (Ioi 0) :=
    (hg.cont.mono Ioi_subset_Ici_self).abs.mul
      (continuous_cardyV C.F.prob (c' / 12)).continuousOn
  have hopen : IsOpen {t ∈ Ioi (0 : ℝ) | 0 < |g t| * C.F.prob.cardyV (c' / 12) t} :=
    hf_cont.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
  have hpos_meas : 0 < volume {t ∈ Ioi (0 : ℝ) | 0 < |g t| * C.F.prob.cardyV (c' / 12) t} :=
    hopen.measure_pos volume ⟨t₀, ht₀_pos, hf0_pos⟩
  have hnull_restrict : (volume.restrict (Ioi (0 : ℝ)))
      {t ∈ Ioi (0 : ℝ) | 0 < |g t| * C.F.prob.cardyV (c' / 12) t} = 0 := by
    refine measure_mono_null (fun t ht => ?_) (ae_iff.mp hae0)
    simp only [mem_ofPred_eq] at ht
    simp only [mem_ofPred_eq, Pi.zero_apply]
    exact ne_of_gt ht.2
  rw [Measure.restrict_apply hopen.measurableSet,
    inter_eq_self_of_subset_left (fun _ ht => (mem_ofPred_eq.mp ht).1)] at hnull_restrict
  exact (hnull_restrict ▸ hpos_meas).false

/-! ### Section 2: Signed-source edge kernel and split identity -/

/-- Edge Mellin kernel `K_src(τ, t)` with `V = src.cardyV (c'/12)`. -/
noncomputable def edgeKernelKWSrc (src : ShiftSource) (c' τ t : ℝ) : ℂ :=
  if 0 < t then
    let z : ℂ := (src.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))
    Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
      (Complex.Gamma z * (src.cardyV (c' / 12) t : ℂ))
  else 0

lemma edgeKernelKWSrc_eq_mul (C : CommonSource) {c' : ℝ} (hc' : C.a₀ ≤ c' / 12)
    (hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c') (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    edgeKernelKWSrc C.src c' τ t =
      ((C.F.prob.cardyV (c' / 12) t / C.src.cardyV (c' / 12) t : ℝ) : ℂ) *
        edgeKernelKW C.F.prob c' τ t := by
  have hV0_ne : (C.F.prob.cardyV (c' / 12) t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (cardyV_pos_of_max hc'_prob ht).ne'
  have hVs_ne : (C.src.cardyV (c' / 12) t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((C.at_ hc').pos_V ht).ne'
  unfold edgeKernelKWSrc edgeKernelKW
  simp only [ht, ↓reduceIte, C.F.prob_w]
  push_cast
  field_simp [hV0_ne, hVs_ne]

lemma edgeKernelKWSrc_mul_src_eq (C : CommonSource) {c' : ℝ} (hc' : C.a₀ ≤ c' / 12)
    (hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c') (g : ℝ → ℝ) (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    edgeKernelKWSrc C.src c' τ t * ((g t * C.src.cardyV (c' / 12) t : ℝ) : ℂ) =
      edgeKernelKW C.F.prob c' τ t * ((g t * C.F.prob.cardyV (c' / 12) t : ℝ) : ℂ) := by
  rw [edgeKernelKWSrc_eq_mul C hc' hc'_prob τ ht]
  have hVs_ne : (C.src.cardyV (c' / 12) t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((C.at_ hc').pos_V ht).ne'
  push_cast
  field_simp [hVs_ne]

lemma measurable_edgeKernelKWSrc (C : CommonSource) {c' : ℝ}
    (hc' : C.a₀ ≤ c' / 12) (hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c') :
    Measurable (Function.uncurry (edgeKernelKWSrc C.src c')) := by
  have hc'0 : 0 ≤ c' := le_trans (by norm_num) ((le_max_left _ _).trans hc'_prob)
  have heq : Function.uncurry (edgeKernelKWSrc C.src c') =
      fun p : ℝ × ℝ =>
        ((C.F.prob.cardyV (c' / 12) p.2 / C.src.cardyV (c' / 12) p.2 : ℝ) : ℂ) *
          edgeKernelKW C.F.prob c' p.1 p.2 := by
    ext ⟨τ, t⟩
    by_cases ht : 0 < t
    · exact edgeKernelKWSrc_eq_mul C hc' hc'_prob τ ht
    · simp [Function.uncurry, edgeKernelKWSrc, edgeKernelKW, ht]
  rw [heq]
  have hrat : Measurable (fun p : ℝ × ℝ =>
      ((C.F.prob.cardyV (c' / 12) p.2 / C.src.cardyV (c' / 12) p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (((continuous_cardyV C.F.prob (c' / 12)).comp continuous_snd).measurable.div
        ((C.src.continuous_cardyV (c' / 12)).comp continuous_snd).measurable)
  exact hrat.mul (measurable_edgeKernelKW C.F.prob hc'0)

lemma integrableOn_edgeKernelKWSrc_mul (C : CommonSource) {c' : ℝ}
    (hc' : C.a₀ ≤ c' / 12) (hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c')
    {g : ℝ → ℝ} (hg : TestClass C.src (c' / 12) g) (τ : ℝ) :
    IntegrableOn (fun t => edgeKernelKWSrc C.src c' τ t *
      ((g t * C.src.cardyV (c' / 12) t : ℝ) : ℂ)) (Ioi 0) := by
  have hg0 := (C.at_ hc').testClass_prob hg
  refine (integrableOn_edgeKernelKW_mul C.F.prob hc'_prob hg0 τ).congr ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ fun t ht => (edgeKernelKWSrc_mul_src_eq C hc' hc'_prob g τ (mem_Ioi.mp ht)).symm

lemma edge_integral_split_src (C : CommonSource) {c' : ℝ}
    (hc' : C.a₀ ≤ c' / 12) (hc'_W : (ywWitness C.F.prob).c_W ≤ c')
    {g : ℝ → ℝ} (hg : TestClass C.src (c' / 12) g) (hM_pos : 0 < C.src.cardyNorm (c' / 12) g)
    (τ : ℝ) :
    (∫ ξ : ℝ, edgeKernelKWSrc C.src c' τ ξ ∂bandMeasPosSrc C.src (c' / 12) g) -
        (∫ ξ : ℝ, edgeKernelKWSrc C.src c' τ ξ ∂bandMeasNegSrc C.src (c' / 12) g) =
      ((C.src.cardyNorm (c' / 12) g)⁻¹ : ℝ) * tildeWW C.src.w c' g (Complex.I * (τ : ℂ)) := by
  have hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c' := (ywWitness C.F.prob).hc_W.trans hc'_W
  set M := C.src.cardyNorm (c' / 12) g with hM
  have hint_main := integrableOn_edgeKernelKWSrc_mul C hc' hc'_prob hg τ
  have hmeas_K : AEStronglyMeasurable (edgeKernelKWSrc C.src c' τ) (volume.restrict (Ioi 0)) :=
    ((measurable_edgeKernelKWSrc C hc' hc'_prob).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hint_K : ∀ (f : ℝ → ℝ), AEMeasurable f (volume.restrict (Ioi 0)) →
      (∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t) →
      (∀ t ∈ Ioi (0 : ℝ), f t ≤ |g t * C.src.cardyV (c' / 12) t| / M) →
      IntegrableOn (fun t => edgeKernelKWSrc C.src c' τ t * (f t : ℂ)) (Ioi 0) := by
    intro f hf_meas hf_nn hf_le
    refine (hint_main.div_const (M : ℂ)).mono
      ((hmeas_K.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hf_meas.aestronglyMeasurable))) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf_nn t ht), norm_div, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
    calc ‖edgeKernelKWSrc C.src c' τ t‖ * f t
        ≤ ‖edgeKernelKWSrc C.src c' τ t‖ * (|g t * C.src.cardyV (c' / 12) t| / M) :=
          mul_le_mul_of_nonneg_left (hf_le t ht) (norm_nonneg _)
      _ = ‖edgeKernelKWSrc C.src c' τ t‖ * |g t * C.src.cardyV (c' / 12) t| / M := by ring
      _ = _ := by rw [Real.norm_eq_abs]
  have hV_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ C.src.cardyV (c' / 12) t := fun t ht =>
    (C.at_ hc').nonneg_V (mem_Ioi.mp ht).le
  have hint_K_pos : IntegrableOn (fun t => edgeKernelKWSrc C.src c' τ t *
      (bandPosSrc C.src (c' / 12) g t : ℂ)) (Ioi 0) := by
    refine hint_K _ (bandPosSrc_aemeasurable hg)
      (fun t ht => bandPosSrc_nonneg hc' g (mem_Ioi.mp ht).le) fun t ht => ?_
    unfold bandPosSrc
    rw [abs_mul, abs_of_nonneg (hV_nn t ht)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (max_le (le_abs_self _) (abs_nonneg _)) (hV_nn t ht)) hM_pos.le
  have hint_K_neg : IntegrableOn (fun t => edgeKernelKWSrc C.src c' τ t *
      (bandNegSrc C.src (c' / 12) g t : ℂ)) (Ioi 0) := by
    refine hint_K _ (bandNegSrc_aemeasurable hg)
      (fun t ht => bandNegSrc_nonneg hc' g (mem_Ioi.mp ht).le) fun t ht => ?_
    unfold bandNegSrc
    rw [abs_mul, abs_of_nonneg (hV_nn t ht)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (max_le (neg_le_abs _) (abs_nonneg _)) (hV_nn t ht)) hM_pos.le
  have hI_pos : ∫ ξ : ℝ, edgeKernelKWSrc C.src c' τ ξ ∂bandMeasPosSrc C.src (c' / 12) g =
      ∫ t in Ioi (0 : ℝ), edgeKernelKWSrc C.src c' τ t * (bandPosSrc C.src (c' / 12) g t : ℂ) := by
    unfold bandMeasPosSrc
    rw [integral_withDensity_eq_integral_toReal_smul₀ (bandPosSrc_aemeasurable hg).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [ENNReal.toReal_ofReal (bandPosSrc_nonneg hc' g (mem_Ioi.mp ht).le), Complex.real_smul,
      mul_comm]
  have hI_neg : ∫ ξ : ℝ, edgeKernelKWSrc C.src c' τ ξ ∂bandMeasNegSrc C.src (c' / 12) g =
      ∫ t in Ioi (0 : ℝ), edgeKernelKWSrc C.src c' τ t * (bandNegSrc C.src (c' / 12) g t : ℂ) := by
    unfold bandMeasNegSrc
    rw [integral_withDensity_eq_integral_toReal_smul₀ (bandNegSrc_aemeasurable hg).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [ENNReal.toReal_ofReal (bandNegSrc_nonneg hc' g (mem_Ioi.mp ht).le), Complex.real_smul,
      mul_comm]
  rw [hI_pos, hI_neg, ← integral_sub hint_K_pos hint_K_neg]
  have hsub_eq : EqOn (fun t => edgeKernelKWSrc C.src c' τ t *
        (bandPosSrc C.src (c' / 12) g t : ℂ) -
        edgeKernelKWSrc C.src c' τ t * (bandNegSrc C.src (c' / 12) g t : ℂ))
      (fun t => ((M⁻¹ : ℝ) : ℂ) * (edgeKernelKW C.F.prob c' τ t *
        ((g t * C.F.prob.cardyV (c' / 12) t : ℝ) : ℂ))) (Ioi 0) := by
    intro t ht
    have hm := edgeKernelKWSrc_mul_src_eq C hc' hc'_prob g τ (mem_Ioi.mp ht)
    unfold bandPosSrc bandNegSrc
    have hsplit : max (g t) 0 - max (-g t) 0 = g t := by
      rcases le_total 0 (g t) with h | h <;> simp [h]
    calc edgeKernelKWSrc C.src c' τ t * ↑(max (g t) 0 * C.src.cardyV (c' / 12) t / M) -
          edgeKernelKWSrc C.src c' τ t * ↑(max (-g t) 0 * C.src.cardyV (c' / 12) t / M)
        = ((M⁻¹ : ℝ) : ℂ) * (edgeKernelKWSrc C.src c' τ t *
            (((max (g t) 0 - max (-g t) 0 : ℝ) : ℂ) * ↑(C.src.cardyV (c' / 12) t))) := by
          push_cast; ring
      _ = ((M⁻¹ : ℝ) : ℂ) * (edgeKernelKWSrc C.src c' τ t *
            ((g t * C.src.cardyV (c' / 12) t : ℝ) : ℂ)) := by
          rw [hsplit]; push_cast; ring
      _ = _ := by rw [hm]
  rw [setIntegral_congr_fun measurableSet_Ioi hsub_eq, integral_const_mul]
  have hJ := (ywWitness C.F.prob).hJ41_edge hc'_W ((C.at_ hc').testClass_prob hg) τ
  rw [C.F.prob_w] at hJ
  rw [← hJ]

/-! ### Section 3: `BandReductionInstance` and `proposition_YV_src` -/

/-- `BandReductionParams` for a `CommonSource`, scaling `C_W` and `C_a` by `max 1 C.F.d⁻¹`. -/
noncomputable def ywBandParamsSrc (C : CommonSource) (pg : LangerChartSpec) (A_thr : ℝ) :
    BandReductionParams :=
  let P := ywBandParams C.F.prob pg A_thr
  let fac : ℝ := max 1 C.F.d⁻¹
  have hfac : 1 ≤ fac := le_max_left _ _
  { M := P.M
    b := P.b
    κ_ζ := P.κ_ζ
    A_0 := P.A_0
    C_W := fac * P.C_W
    C_a := fac * P.C_a
    c_1 := P.c_1
    c_2 := P.c_2
    C_ν := P.C_ν
    κ_sub := P.κ_sub
    C_τ := P.C_τ
    hM := P.hM
    hb := P.hb
    hκ_ζ := P.hκ_ζ
    hA_0 := P.hA_0
    hC_W := mul_pos (lt_of_lt_of_le one_pos hfac) P.hC_W
    hC_a := mul_pos (lt_of_lt_of_le one_pos hfac) P.hC_a
    hc_1 := P.hc_1
    hc_2 := P.hc_2
    hC_ν := P.hC_ν
    hκ_sub := P.hκ_sub
    hC_τ := P.hC_τ }

/-- Threshold `c'` for `proposition_YV_src`. -/
noncomputable def ywThreshSrc (C : CommonSource) (pg : LangerChartSpec) (A_thr : ℝ) : ℝ :=
  max (ywThresh C.F.prob pg A_thr) (24 * C.a₀)

lemma ywThreshSrc_ge (C : CommonSource) (pg : LangerChartSpec) (A_thr : ℝ) :
    10000 ≤ ywThreshSrc C pg A_thr :=
  (ywThresh_ge C.F.prob pg A_thr).trans (le_max_left _ _)

/-- Concrete `BandReductionInstance (ywBandParamsSrc C pg A_thr)` constructed from
`ywBandInstance C.F.prob pg`. -/
noncomputable def ywBandInstanceSrc (C : CommonSource) (pg : LangerChartSpec)
    {A_thr c' R T : ℝ} (hA_thr : 0 ≤ A_thr) (hc' : ywThreshSrc C pg A_thr ≤ c')
    (hR_lb : (ywBandParamsSrc C pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (ywBandParamsSrc C pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T) (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass C.src (c' / 12) g) (hM_pos : 0 < C.src.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    BandReductionInstance (ywBandParamsSrc C pg A_thr) :=
  let hc'0 : ywThresh C.F.prob pg A_thr ≤ c' := (le_max_left _ _).trans hc'
  let hc'_yv : yvThresh pg A_thr ≤ c' := ywThresh_ge_yv hc'0
  let hc'_W : (ywWitness C.F.prob).c_W ≤ c' := ywThresh_ge_c_W hc'0
  let hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c' := (ywWitness C.F.prob).hc_W.trans hc'_W
  let hc'_a0 : 24 * C.a₀ ≤ c' := (le_max_right _ _).trans hc'
  let hc'_src : max 1 (max (24 * C.F.prob.totalShift) (24 * C.a₀)) ≤ c' :=
    max_le ((le_max_left _ _).trans hc'_prob) (max_le ((le_max_right _ _).trans hc'_prob) hc'_a0)
  let ha : C.a₀ ≤ c' / 12 := by
    have : 0 ≤ c' := le_trans (by norm_num) ((le_max_left _ _).trans hc'_prob)
    linarith
  let hAt := C.at_ ha
  let hg0 := hAt.testClass_prob hg
  let hM0_pos : 0 < C.F.prob.cardyNorm (c' / 12) g :=
    cardyNorm_prob_pos_of_src_pos C hc'_src hg hM_pos
  let I₀ := ywBandInstance C.F.prob pg hA_thr hc'0 hR_lb hR_ub hT_lo hT_hi hg0 hM0_pos hg_nonneg
  let fac : ℝ := max 1 C.F.d⁻¹
  have hfac : 1 ≤ fac := le_max_left _ _
  have hd_le_fac : C.F.d⁻¹ ≤ fac := le_max_right _ _
  have hrat_bd : ∀ {ξ : ℝ}, 0 < ξ →
      0 ≤ C.F.prob.cardyV (c' / 12) ξ / C.src.cardyV (c' / 12) ξ ∧
        C.F.prob.cardyV (c' / 12) ξ / C.src.cardyV (c' / 12) ξ ≤ fac := fun {ξ} hξ => by
    have hV0_nn : 0 ≤ C.F.prob.cardyV (c' / 12) ξ := (cardyV_pos_of_max hc'_prob hξ).le
    have hVs_pos : 0 < C.src.cardyV (c' / 12) ξ := hAt.pos_V hξ
    refine ⟨div_nonneg hV0_nn hVs_pos.le, ?_⟩
    have hlow := hAt.lower hξ
    have hdiv : C.F.prob.cardyV (c' / 12) ξ / C.src.cardyV (c' / 12) ξ ≤ C.F.d⁻¹ := by
      rw [div_le_iff₀ hVs_pos]
      calc C.F.prob.cardyV (c' / 12) ξ
          = C.F.d⁻¹ * (C.F.d * C.F.prob.cardyV (c' / 12) ξ) := by
              rw [← mul_assoc, inv_mul_cancel₀ C.F.hd.ne', one_mul]
        _ ≤ C.F.d⁻¹ * C.src.cardyV (c' / 12) ξ :=
            mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr C.F.hd.le)
    exact hdiv.trans hd_le_fac
  have hS4 := (ywWitness C.F.prob).hS4 hc'_W hg0
  have hM_ge : C.F.d * C.F.prob.cardyNorm (c' / 12) g ≤ C.src.cardyNorm (c' / 12) g :=
    hAt.cardyNorm_ge hg
  { c := c'
    ε := -1
    R := R
    hc := I₀.hc
    hε := I₀.hε
    hR_lb := hR_lb
    hR_ub := hR_ub
    hρR_ub := I₀.hρR_ub
    W_tilde := fun ζ => ((C.src.cardyNorm (c' / 12) g)⁻¹ : ℂ) * tildeWW C.src.w c' g ζ
    hW_cont := by
      rw [← C.F.prob_w]
      exact continuousOn_const.mul hS4.2.1
    hW_holo := by
      rw [← C.F.prob_w]
      exact hS4.1.const_mul _
    hW_symm := fun ζ h0 h1 => by
      have hsymm := hS4.2.2.1 ζ ⟨h0, h1⟩
      rw [← C.F.prob_w, hsymm]
      push_cast; ring
    hW_bound := fun ζ h0 h1 => by
      have hbd := hS4.2.2.2 ζ ⟨h0, h1⟩
      rw [← C.F.prob_w, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
      have hM_inv : (C.src.cardyNorm (c' / 12) g)⁻¹ * C.F.prob.cardyNorm (c' / 12) g ≤ fac := by
        rw [inv_mul_eq_div, div_le_iff₀ hM_pos]
        calc C.F.prob.cardyNorm (c' / 12) g
            = C.F.d⁻¹ * (C.F.d * C.F.prob.cardyNorm (c' / 12) g) := by
                rw [← mul_assoc, inv_mul_cancel₀ C.F.hd.ne', one_mul]
          _ ≤ C.F.d⁻¹ * C.src.cardyNorm (c' / 12) g :=
              mul_le_mul_of_nonneg_left hM_ge (inv_nonneg.mpr C.F.hd.le)
          _ ≤ fac * C.src.cardyNorm (c' / 12) g :=
              mul_le_mul_of_nonneg_right hd_le_fac hM_pos.le
      have hpow : (1 : ℝ) ≤ (1 + ‖ζ‖) ^ (ywBandParams C.F.prob pg A_thr).M :=
        Real.one_le_rpow (by linarith [norm_nonneg ζ]) (ywBandParams C.F.prob pg A_thr).hM
      have hCW_eq : (ywBandParams C.F.prob pg A_thr).C_W = (ywWitness C.F.prob).C_S4 := rfl
      calc (C.src.cardyNorm (c' / 12) g)⁻¹ * ‖tildeWW C.F.prob.w c' g ζ‖
          ≤ (C.src.cardyNorm (c' / 12) g)⁻¹ *
              ((ywWitness C.F.prob).C_S4 * C.F.prob.cardyNorm (c' / 12) g) :=
            mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hM_pos.le)
        _ = (ywWitness C.F.prob).C_S4 *
              ((C.src.cardyNorm (c' / 12) g)⁻¹ * C.F.prob.cardyNorm (c' / 12) g) := by ring
        _ ≤ (ywWitness C.F.prob).C_S4 * fac :=
            mul_le_mul_of_nonneg_left hM_inv (ywWitness C.F.prob).hC_S4.le
        _ = (ywBandParamsSrc C pg A_thr).C_W * 1 := by
            change (ywWitness C.F.prob).C_S4 * fac = fac * (ywBandParams C.F.prob pg A_thr).C_W * 1
            rw [hCW_eq]; ring
        _ ≤ (ywBandParamsSrc C pg A_thr).C_W * (1 + ‖ζ‖) ^ (ywBandParamsSrc C pg A_thr).M :=
            mul_le_mul_of_nonneg_left hpow (ywBandParamsSrc C pg A_thr).hC_W.le
    dmPos := bandMeasPosSrc C.src (c' / 12) g
    dmNeg := bandMeasNegSrc C.src (c' / 12) g
    hdmPos_fin := bandMeasPosSrc_isFinite ha hg
    hdmNeg_fin := bandMeasNegSrc_isFinite ha hg
    hdmPos_supp := bandMeasPosSrc_Iic C.src (c' / 12) g
    hdmNeg_supp := bandMeasNegSrc_Iic C.src (c' / 12) g
    hdm_tv := (bandMeasSrc_tv ha hg hM_pos).le
    T := T
    hdm_nonneg_tail := bandMeasNegSrc_Ici_eq_zero C.src (c' / 12) hg_nonneg
    E_sub := I₀.E_sub
    hE_sub_meas := I₀.hE_sub_meas
    hE_sub_sub := I₀.hE_sub_sub
    K_edge := edgeKernelKWSrc C.src c'
    hK_meas := measurable_edgeKernelKWSrc C ha hc'_prob
    hW_edge := fun τ => by
      have hsplit := edge_integral_split_src C ha hc'_W hg hM_pos τ
      rw [show (↑τ * Complex.I : ℂ) = Complex.I * ↑τ by ring]
      push_cast at hsplit ⊢
      exact hsplit.symm
    hK_sub := fun ξ hξ τ => by
      have hξ_pos : 0 < ξ := (I₀.hE_sub_sub hξ).1
      have hI0K := I₀.hK_sub ξ hξ τ
      have hK_eq : I₀.K_edge τ ξ = edgeKernelKW C.F.prob c' τ ξ := rfl
      have hκ : (ywBandParamsSrc C pg A_thr).κ_sub = (ywBandParams C.F.prob pg A_thr).κ_sub := rfl
      have hCa : (ywBandParamsSrc C pg A_thr).C_a = fac * (ywBandParams C.F.prob pg A_thr).C_a := rfl
      rw [edgeKernelKWSrc_eq_mul C ha hc'_prob τ hξ_pos, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hrat_bd hξ_pos).1, ← hK_eq]
      calc (C.F.prob.cardyV (c' / 12) ξ / C.src.cardyV (c' / 12) ξ) * ‖I₀.K_edge τ ξ‖
          ≤ fac * ((ywBandParams C.F.prob pg A_thr).C_a *
              Real.exp (-(ywBandParams C.F.prob pg A_thr).κ_sub * c')) :=
            mul_le_mul (hrat_bd hξ_pos).2 hI0K (norm_nonneg _) (lt_of_lt_of_le one_pos hfac).le
        _ = (ywBandParamsSrc C pg A_thr).C_a *
              Real.exp (-(ywBandParamsSrc C pg A_thr).κ_sub * c') := by
            rw [hκ, hCa]; ring
    a_0 := I₀.a_0
    a_0' := I₀.a_0'
    a_2 := fun ξ =>
      ((C.F.prob.cardyV (c' / 12) ξ / C.src.cardyV (c' / 12) ξ : ℝ) : ℂ) * I₀.a_2 ξ
    R_0 := I₀.R_0
    Phi := I₀.Phi
    hK_factor := fun ξ hξ τ => by
      have hξ_pos : 0 < ξ := mem_Ioi.mp hξ.1
      have hfac0 := I₀.hK_factor ξ hξ τ
      have hK_eq : I₀.K_edge τ ξ = edgeKernelKW C.F.prob c' τ ξ := rfl
      have hc_eq : (I₀.c : ℂ) = (c' : ℂ) := rfl
      rw [edgeKernelKWSrc_eq_mul C ha hc'_prob τ hξ_pos, ← hK_eq, hfac0, hc_eq]
      ring
    ha_2_bd := fun ξ hξ => by
      have hξ_pos : 0 < ξ := mem_Ioi.mp hξ.1
      have ha20 := I₀.ha_2_bd ξ hξ
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hrat_bd hξ_pos).1]
      exact (mul_le_mul (hrat_bd hξ_pos).2 ha20 (norm_nonneg _)
        (lt_of_lt_of_le one_pos hfac).le)
    ha_0_deriv := I₀.ha_0_deriv
    ha_0_bd := fun τ =>
      (I₀.ha_0_bd τ).trans (mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (ywBandParams C.F.prob pg A_thr).hC_a.le hfac)
        (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _))
    hR_0_nonpos := I₀.hR_0_nonpos
    hR_0_cont := I₀.hR_0_cont
    hR_0_even := I₀.hR_0_even
    hR_0_unimodal := I₀.hR_0_unimodal
    hPhi_odd := I₀.hPhi_odd
    ν := I₀.ν
    ν' := I₀.ν'
    invNu' := I₀.invNu'
    hν_deriv := I₀.hν_deriv
    hν'_cont := I₀.hν'_cont
    hν'_inv_pos := I₀.hν'_inv_pos
    hν'_inv_deriv := I₀.hν'_inv_deriv
    hinvNu'_cont := I₀.hinvNu'_cont
    hinvNu'_int := I₀.hinvNu'_int
    hinvNu'_integrable := I₀.hinvNu'_integrable
    μ := I₀.μ
    m := I₀.m
    m' := I₀.m'
    hPhi_deriv := I₀.hPhi_deriv
    hm_0 := I₀.hm_0
    hm_cont := I₀.hm_cont
    hm_strictMono := I₀.hm_strictMono
    hm_deriv := I₀.hm_deriv
    hm_step := I₀.hm_step
    hm_slope := I₀.hm_slope
    τ_0 := I₀.τ_0
    hτ_0_nn := I₀.hτ_0_nn
    hτ_0_eq_zero := I₀.hτ_0_eq_zero
    hτ_0_root := I₀.hτ_0_root
    u_tilde := I₀.u_tilde
    Delta := I₀.Delta
    hτ_0_below := I₀.hτ_0_below
    hτ_0_band := I₀.hτ_0_band
    hu_tilde_int := by
      have hfin : IsFiniteMeasure (bandMeasPosSrc C.src (c' / 12) g) := bandMeasPosSrc_isFinite ha hg
      have hProps := langerDelta_props hc'_yv hR_lb hR_ub
      have hR_pos := hProps.1
      have hR_ge := hProps.2.2.1
      have hmono_delta := hProps.2.2.2.2.1
      have hT_le_R : T ≤ langerDelta pg c' (-R) :=
        hT_hi.trans (hmono_delta.monotoneOn ⟨hA_thr, (le_max_left _ _).trans hR_ge⟩
          ⟨hR_pos.le, le_rfl⟩ ((le_max_left _ _).trans hR_ge))
      have hmono : MonotoneOn (fun ξ => -I₀.u_tilde ξ) (Icc T (I₀.Delta (-R))) := by
        have hu_eq : I₀.u_tilde = fun ξ => -langerNegV pg c' R ξ := rfl
        have hm := langerNegV_monotoneOn hc'_yv hR_lb hR_ub
        intro x hx y hy hxy
        simp only [hu_eq, neg_neg]
        exact hm ⟨hT_lo.trans hx.1, hx.2⟩ ⟨hT_lo.trans hy.1, hy.2⟩ hxy
      exact hmono.integrableOn_of_measure_ne_top (isLeast_Icc hT_le_R)
        (isGreatest_Icc hT_le_R) (measure_ne_top _ _) measurableSet_Icc }

/-! ### Section 4: Moments and `proposition_YV_src` -/

lemma ywBandInstanceSrc_moments (C : CommonSource) (pg : LangerChartSpec) {A_thr c' R T : ℝ}
    (hA_thr : 0 ≤ A_thr) (hc' : ywThreshSrc C pg A_thr ≤ c')
    (hR_lb : (ywBandParamsSrc C pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (ywBandParamsSrc C pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T) (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass C.src (c' / 12) g) (hM_pos : 0 < C.src.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    let I := ywBandInstanceSrc C pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
    let M := C.src.cardyNorm (c' / 12) g
    (∀ ζ : ℂ, I.W_tilde ζ = ↑M⁻¹ * tildeWW C.src.w c' g ζ) ∧
    (∀ u ∈ Icc (-R) 0, I.u_tilde (langerDelta pg c' u) = u) ∧
    bandB1 I = R⁻¹ * ∫ t in Icc T (langerDelta pg c' (-R)),
      (-I.u_tilde t) * (g t * C.src.cardyV (c' / 12) t / M) ∧
    bandB2 I = ∫ t in Ici (langerDelta pg c' (-R)),
      g t * C.src.cardyV (c' / 12) t / M := by
  intro I M
  have hc'0 : ywThresh C.F.prob pg A_thr ≤ c' := (le_max_left _ _).trans hc'
  have hc'_yv : yvThresh pg A_thr ≤ c' := ywThresh_ge_yv hc'0
  have hc'_W : (ywWitness C.F.prob).c_W ≤ c' := ywThresh_ge_c_W hc'0
  have hc'_prob : max 1 (24 * C.F.prob.totalShift) ≤ c' := (ywWitness C.F.prob).hc_W.trans hc'_W
  have hc'_a0 : 24 * C.a₀ ≤ c' := (le_max_right _ _).trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by norm_num) (ywThreshSrc_ge C pg A_thr |>.trans hc')
  have ha : C.a₀ ≤ c' / 12 := by linarith
  have hT_pos : 0 < T := by
    have hD0 : 0 < langerDelta pg c' 0 := by
      rw [langerDelta_zero]; have := xiStar_pos; positivity
    exact hD0.trans_le hT_lo
  refine ⟨fun ζ => by
    change ((C.src.cardyNorm (c' / 12) g)⁻¹ : ℂ) * _ = _
    push_cast; rfl, fun u hu => ?_, ?_, ?_⟩
  · change -langerNegV pg c' R (langerDelta pg c' u) = u
    exact langerNegV_inv_delta hc'_yv hR_lb hR_ub hu
  · unfold bandB1
    have hdm : I.dmPos = bandMeasPosSrc C.src (c' / 12) g := rfl
    have hu_eq : I.u_tilde = fun ξ => -langerNegV pg c' R ξ := rfl
    have hDelta_eq : I.Delta (-I.R) = langerDelta pg c' (-R) := rfl
    have hR_eq : I.R = R := rfl
    have hT_eq : I.T = T := rfl
    rw [hdm, hu_eq, hDelta_eq, hR_eq, hT_eq]
    congr 1
    simp only [neg_neg]
    unfold bandMeasPosSrc
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      (bandPosSrc_aemeasurable hg).ennreal_ofReal.restrict
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)
      (fun t => langerNegV pg c' R t) measurableSet_Icc]
    change (∫ t, (ENNReal.ofReal (bandPosSrc C.src (c' / 12) g t)).toReal •
        langerNegV pg c' R t ∂((volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R))))) = _
    rw [Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (fun t (ht : t ∈ Icc T (langerDelta pg c' (-R))) =>
        mem_Ioi.mpr (hT_pos.trans_le ht.1))]
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have ht_nn : 0 ≤ t := (hT_pos.trans_le ht.1).le
    rw [ENNReal.toReal_ofReal (bandPosSrc_nonneg ha g ht_nn), smul_eq_mul]
    have hgt : 0 ≤ g t := hg_nonneg t ht.1
    simp only [bandPosSrc, max_eq_left hgt]
    ring
  · unfold bandB2
    have hdm : I.dmPos = bandMeasPosSrc C.src (c' / 12) g := rfl
    have hDelta_eq : I.Delta (-I.R) = langerDelta pg c' (-R) := rfl
    rw [hdm, hDelta_eq]
    unfold bandMeasPosSrc
    have hD0 : 0 < langerDelta pg c' 0 := by
      rw [langerDelta_zero]; have := xiStar_pos; positivity
    have hDR : langerDelta pg c' 0 ≤ langerDelta pg c' (-R) := by
      have hProps := langerDelta_props hc'_yv hR_lb hR_ub
      have hR_pos := hProps.1
      simpa using hProps.2.2.2.2.1.monotoneOn ⟨le_rfl, hR_pos.le⟩ ⟨hR_pos.le, le_rfl⟩ hR_pos.le
    have hsub_oi : Ici (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) := fun t ht =>
      hD0.trans_le (hDR.trans ht)
    rw [withDensity_apply _ measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr hsub_oi]
    have hint_ici : IntegrableOn (bandPosSrc C.src (c' / 12) g) (Ici (langerDelta pg c' (-R))) :=
      (bandPosSrc_integrableOn ha hg).mono_set hsub_oi
    have hnn_ici : ∀ᵐ t ∂(volume.restrict (Ici (langerDelta pg c' (-R)))),
        0 ≤ bandPosSrc C.src (c' / 12) g t :=
      ae_restrict_of_forall_mem measurableSet_Ici fun t ht =>
        bandPosSrc_nonneg ha g (hsub_oi ht).le
    rw [← ofReal_integral_eq_lintegral_ofReal hint_ici hnn_ici,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ici fun t ht =>
        bandPosSrc_nonneg ha g (hsub_oi ht).le)]
    refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
    have hProps := langerDelta_props hc'_yv hR_lb hR_ub
    have hR_pos := hProps.1
    have hR_ge := hProps.2.2.1
    have hDT_le_R : T ≤ langerDelta pg c' (-R) :=
      hT_hi.trans (hProps.2.2.2.2.1.monotoneOn
        ⟨hA_thr, (le_max_left _ _).trans hR_ge⟩ ⟨hR_pos.le, le_rfl⟩ ((le_max_left _ _).trans hR_ge))
    have hgt : 0 ≤ g t := hg_nonneg t (hDT_le_R.trans ht)
    simp only [bandPosSrc, max_eq_left hgt]
    rfl

/-- **Proposition `Y_V` for signed common sources** (`pmix:o1`, `lower_o1_two_edge.tex`, §J4). -/
theorem proposition_YV_src (C : CommonSource) (pg : LangerChartSpec) {A_thr : ℝ}
    (hA_thr : 0 ≤ A_thr) :
    ∃ (c₀ C_Y b : ℝ), 10000 ≤ c₀ ∧ 0 < C_Y ∧ 0 < b ∧
      ∀ {c' R T : ℝ}, c₀ ≤ c' →
        b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R → R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 →
        langerDelta pg c' 0 ≤ T → T ≤ langerDelta pg c' (-A_thr) →
        ∀ {g : ℝ → ℝ}, TestClass C.src (c' / 12) g →
          0 < C.src.cardyNorm (c' / 12) g →
          (∀ t ∈ Ici T, 0 ≤ g t) →
          ∃ u_tilde : ℝ → ℝ,
            (∀ u ∈ Icc (-R) 0, u_tilde (langerDelta pg c' u) = u) ∧
            let M := C.src.cardyNorm (c' / 12) g
            let B₁ := R⁻¹ * ∫ t in Icc T (langerDelta pg c' (-R)),
              (-u_tilde t) * (g t * C.src.cardyV (c' / 12) t / M)
            let B₂ := ∫ t in Ici (langerDelta pg c' (-R)),
              g t * C.src.cardyV (c' / 12) t / M
            0 ≤ B₁ ∧ 0 ≤ B₂ ∧
            ∀ {ζ₀ : ℂ} {ψ : ℝ},
              kappaV * c' ^ (-(1 / 3 : ℝ)) * √R / 3 ≤ ‖ζ₀‖ →
              ‖ζ₀‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * √R) →
              ζ₀.re = ‖ζ₀‖ * Real.cos ψ →
              c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ →
              ‖tildeWW C.src.w c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
              ‖tildeWW C.src.w c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) := by
  let P := ywBandParamsSrc C pg A_thr
  refine ⟨ywThreshSrc C pg A_thr, tebBandConst P, P.b,
    ywThreshSrc_ge C pg A_thr, tebBandConst_pos P, P.hb,
    fun {c' R T} hc' hR_lb hR_ub hT_lo hT_hi {g} hg hM_pos hg_nonneg => ?_⟩
  let I := ywBandInstanceSrc C pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
  have hmom := ywBandInstanceSrc_moments C pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
  refine ⟨I.u_tilde, hmom.2.1, ?_⟩
  dsimp only
  rw [← hmom.2.2.1, ← hmom.2.2.2]
  refine ⟨bandB1_nonneg I, bandB2_nonneg I, fun {ζ₀} {ψ} hlo hhi hcos_eq hcos_lb => ?_⟩
  have hρ_eq : rhoR P c' R = kappaV * c' ^ (-(1 / 3 : ℝ)) * √R := rfl
  have hred := teb_band_reduction I (show rhoR P I.c I.R / 3 ≤ ‖ζ₀‖ from hρ_eq ▸ hlo)
    (show ‖ζ₀‖ ≤ 2 * rhoR P I.c I.R from hρ_eq ▸ hhi) hcos_eq
    (show I.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ from hcos_lb)
  have hW : I.W_tilde ζ₀ = ((C.src.cardyNorm (c' / 12) g)⁻¹ : ℝ) * tildeWW C.src.w c' g ζ₀ :=
    hmom.1 ζ₀
  have hred' : ‖tildeWW C.src.w c' g ζ₀‖ * (C.src.cardyNorm (c' / 12) g)⁻¹ ≤
      tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ ∧
      ‖tildeWW C.src.w c' g ζ₀‖ * (C.src.cardyNorm (c' / 12) g)⁻¹ ≤
        tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ))) := by
    rw [hW, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM_pos.le),
      mul_comm] at hred
    exact hred
  refine ⟨?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_right hred'.1 hM_pos.le
    rw [mul_assoc, inv_mul_cancel₀ hM_pos.ne', mul_one,
      mul_comm _ (C.src.cardyNorm (c' / 12) g)] at h1
    exact h1
  · have h2 := mul_le_mul_of_nonneg_right hred'.2 hM_pos.le
    rw [mul_assoc, inv_mul_cancel₀ hM_pos.ne', mul_one,
      mul_comm _ (C.src.cardyNorm (c' / 12) g)] at h2
    exact h2

end FormalResearch.ModularBootstrap.Mixtures
