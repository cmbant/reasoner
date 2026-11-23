module

public import FormalResearch.ModularBootstrap.FixedWeightBand.EdgeKernelW
public import FormalResearch.ModularBootstrap.StripBand.BandReduction

/-!
# The Band Density `dm = (g V / M[g]) dt` at Weight `w` (Proposition `Y_V`, `vlo:YV`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, proof of Proposition `Y_V`
(`vlo:YV`) and `CFT/common/two_edge_bootstrap.tex`, `(MS2)` (`teb:MS2`).

For `prob : FixedWeightProblem`, a level `a = c'/12 ≥ S` and a test function `g ∈ TestClass prob a`
with `M[g] = prob.cardyNorm a g > 0`, the signed measure `dm = g V / M[g] dt` on `(0, ∞)` is split as
`dm = dmPos - dmNeg` with densities `bandPos = (g)₊ V / M`, `bandNeg = (g)₋ V / M` (`bandMeasPos`,
`bandMeasNeg`).

* `bandMeasPos_univ_add`: `dmPos(ℝ) + dmNeg(ℝ) = 1` (the total variation condition of `(MS2)`);
* `bandMeasNeg_Ici_eq_zero`: `dmNeg [T, ∞) = 0` if `g ≥ 0` on `[T, ∞)`;
* `integrableOn_edgeKernelKW_mul`: `K(τ, ·) g V` is integrable on `(0, ∞)` (the kernel is `z`-power
  times the Mellin integrand `g(t) t^{z-1}` of `TestClass.integrableOn_mellin`);
* `edge_integral_split`: `∫ K dmPos - ∫ K dmNeg = M⁻¹ ∫ K g V`, the edge identity `(MS2)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Chart ChartGeometry

/-! ### Section 1: Densities and measures -/

/-- Density `(g)₊ V / M[g]` of the positive part of `dm`. -/
noncomputable def bandPos (prob : FixedWeightProblem) (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (g t) 0 * prob.cardyV a t / prob.cardyNorm a g

/-- Density `(g)₋ V / M[g]` of the negative part of `dm`. -/
noncomputable def bandNeg (prob : FixedWeightProblem) (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (-g t) 0 * prob.cardyV a t / prob.cardyNorm a g

/-- Positive part `dmPos` of `dm = g V / M[g] dt` on `(0, ∞)`. -/
noncomputable def bandMeasPos (prob : FixedWeightProblem) (a : ℝ) (g : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (bandPos prob a g t))

/-- Negative part `dmNeg` of `dm = g V / M[g] dt` on `(0, ∞)`. -/
noncomputable def bandMeasNeg (prob : FixedWeightProblem) (a : ℝ) (g : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (bandNeg prob a g t))

section Density

variable {prob : FixedWeightProblem} {a : ℝ} {g : ℝ → ℝ}

lemma bandPos_nonneg (ha : prob.totalShift ≤ a) (_hg : TestClass prob a g) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ bandPos prob a g t :=
  div_nonneg (mul_nonneg (le_max_right _ _) (prob.cardyV_nonneg ha ht))
    (prob.cardyNorm_nonneg ha g)

lemma bandNeg_nonneg (ha : prob.totalShift ≤ a) (_hg : TestClass prob a g) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ bandNeg prob a g t :=
  div_nonneg (mul_nonneg (le_max_right _ _) (prob.cardyV_nonneg ha ht))
    (prob.cardyNorm_nonneg ha g)

lemma bandPos_add_bandNeg (t : ℝ) :
    bandPos prob a g t + bandNeg prob a g t = |g t| * prob.cardyV a t / prob.cardyNorm a g := by
  unfold bandPos bandNeg
  have habs : max (g t) 0 + max (-g t) 0 = |g t| := by
    rcases le_total 0 (g t) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero, abs_of_nonneg h]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add, abs_of_nonpos h]
  rw [← add_div, ← add_mul, habs]

lemma bandPos_aemeasurable (hg : TestClass prob a g) :
    AEMeasurable (bandPos prob a g) (volume.restrict (Ioi 0)) := by
  have hV_cont := continuous_cardyV prob a
  have hcont : ContinuousOn (bandPos prob a g) (Ioi 0) := fun t ht =>
    (((hg.cont.mono Ioi_subset_Ici_self t ht).sup continuousWithinAt_const).mul
      hV_cont.continuousWithinAt).div_const _
  exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable

lemma bandNeg_aemeasurable (hg : TestClass prob a g) :
    AEMeasurable (bandNeg prob a g) (volume.restrict (Ioi 0)) := by
  have hV_cont := continuous_cardyV prob a
  have hcont : ContinuousOn (bandNeg prob a g) (Ioi 0) := fun t ht =>
    (((hg.cont.mono Ioi_subset_Ici_self t ht).neg.sup continuousWithinAt_const).mul
      hV_cont.continuousWithinAt).div_const _
  exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable

lemma bandPos_integrableOn (ha : prob.totalShift ≤ a) (hg : TestClass prob a g) :
    IntegrableOn (bandPos prob a g) (Ioi 0) := by
  refine (hg.int_cardy.div_const (prob.cardyNorm a g)).mono' (bandPos_aemeasurable hg).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_of_nonneg (bandPos_nonneg ha hg (mem_Ioi.mp ht).le), ← bandPos_add_bandNeg]
  linarith [bandNeg_nonneg ha hg (mem_Ioi.mp ht).le]

lemma bandNeg_integrableOn (ha : prob.totalShift ≤ a) (hg : TestClass prob a g) :
    IntegrableOn (bandNeg prob a g) (Ioi 0) := by
  refine (hg.int_cardy.div_const (prob.cardyNorm a g)).mono' (bandNeg_aemeasurable hg).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_of_nonneg (bandNeg_nonneg ha hg (mem_Ioi.mp ht).le), ← bandPos_add_bandNeg]
  linarith [bandPos_nonneg ha hg (mem_Ioi.mp ht).le]

lemma bandMeasPos_univ (ha : prob.totalShift ≤ a) (hg : TestClass prob a g) :
    bandMeasPos prob a g univ = ENNReal.ofReal (∫ t in Ioi 0, bandPos prob a g t) := by
  unfold bandMeasPos
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (bandPos_integrableOn ha hg)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht =>
      bandPos_nonneg ha hg (mem_Ioi.mp ht).le)).symm

lemma bandMeasNeg_univ (ha : prob.totalShift ≤ a) (hg : TestClass prob a g) :
    bandMeasNeg prob a g univ = ENNReal.ofReal (∫ t in Ioi 0, bandNeg prob a g t) := by
  unfold bandMeasNeg
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (bandNeg_integrableOn ha hg)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht =>
      bandNeg_nonneg ha hg (mem_Ioi.mp ht).le)).symm

lemma bandMeasPos_isFinite (ha : prob.totalShift ≤ a) (hg : TestClass prob a g) :
    IsFiniteMeasure (bandMeasPos prob a g) :=
  ⟨by rw [bandMeasPos_univ ha hg]; exact ENNReal.ofReal_lt_top⟩

lemma bandMeasNeg_isFinite (ha : prob.totalShift ≤ a) (hg : TestClass prob a g) :
    IsFiniteMeasure (bandMeasNeg prob a g) :=
  ⟨by rw [bandMeasNeg_univ ha hg]; exact ENNReal.ofReal_lt_top⟩

lemma bandMeasPos_Iic (g : ℝ → ℝ) : bandMeasPos prob a g (Iic 0) = 0 := by
  unfold bandMeasPos
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]

lemma bandMeasNeg_Iic (g : ℝ → ℝ) : bandMeasNeg prob a g (Iic 0) = 0 := by
  unfold bandMeasNeg
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]

/-- Total variation `dmPos(ℝ) + dmNeg(ℝ) = 1` for `M[g] > 0`. -/
lemma bandMeas_tv (ha : prob.totalShift ≤ a) (hg : TestClass prob a g)
    (hM_pos : 0 < prob.cardyNorm a g) :
    (bandMeasPos prob a g univ).toReal + (bandMeasNeg prob a g univ).toReal = 1 := by
  rw [bandMeasPos_univ ha hg, bandMeasNeg_univ ha hg,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun t ht =>
      bandPos_nonneg ha hg (mem_Ioi.mp ht).le),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun t ht =>
      bandNeg_nonneg ha hg (mem_Ioi.mp ht).le),
    ← integral_add (bandPos_integrableOn ha hg) (bandNeg_integrableOn ha hg)]
  have heq : EqOn (fun t => bandPos prob a g t + bandNeg prob a g t)
      (fun t => |g t| * prob.cardyV a t / prob.cardyNorm a g) (Ioi 0) :=
    fun t _ => bandPos_add_bandNeg t
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_div]
  change prob.cardyNorm a g / prob.cardyNorm a g = 1
  exact div_self hM_pos.ne'

lemma bandMeasNeg_Ici_eq_zero {T : ℝ} (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    bandMeasNeg prob a g (Ici T) = 0 := by
  unfold bandMeasNeg
  rw [withDensity_apply _ measurableSet_Ici]
  refine setLIntegral_eq_zero measurableSet_Ici fun t ht => ?_
  have hgt := hg_nonneg t ht
  simp only [bandNeg, max_eq_right (neg_nonpos.mpr hgt), zero_mul, zero_div,
    ENNReal.ofReal_zero, Pi.zero_apply]

/-! ### Section 2: The edge identity -/

lemma integrableOn_edgeKernelKW_mul (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (τ : ℝ) :
    IntegrableOn (fun t => edgeKernelKW prob c' τ t *
      ((g t * prob.cardyV (c' / 12) t : ℝ) : ℂ)) (Ioi 0) := by
  obtain ⟨hS, ha0, hc'_pos⟩ := shift_le_of_max_le prob hc'
  let ω := chartOmega (Complex.I * (τ : ℂ))
  let z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * ω
  have hω_re : 0 < ω.re := re_chartOmega_edge_pos τ
  have hz_re : 0 < z.re := by
    dsimp [z]
    have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast prob.hw
    simp only [Complex.div_ofNat_re, Complex.natCast_re, Complex.re_ofReal_mul]
    nlinarith [mul_pos hc'_pos hω_re]
  have hint_mg := TestClass.integrableOn_mellin hS ha0 hg hz_re
  let Cfac : ℂ := Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
    (2 * (Real.pi : ℂ)) ^ z / Complex.Gamma z
  refine (hint_mg.const_mul Cfac).congr ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun t ht => ?_))
  have ht0 : 0 < t := mem_Ioi.mp ht
  have hV_ne : (prob.cardyV (c' / 12) t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (cardyV_pos_of_max hc' ht0).ne'
  unfold edgeKernelKW
  simp only [ht0, ↓reduceIte]
  dsimp [Cfac, z, ω]
  push_cast; field_simp [hV_ne]

/-- The edge identity `(MS2)`: `∫ K dmPos - ∫ K dmNeg = M⁻¹ ∫ K g V`. -/
lemma edge_integral_split (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g) (τ : ℝ) :
    (∫ ξ : ℝ, edgeKernelKW prob c' τ ξ ∂bandMeasPos prob (c' / 12) g) -
        (∫ ξ : ℝ, edgeKernelKW prob c' τ ξ ∂bandMeasNeg prob (c' / 12) g) =
      ((prob.cardyNorm (c' / 12) g)⁻¹ : ℝ) *
        ∫ t in Ioi (0 : ℝ), edgeKernelKW prob c' τ t *
          ((g t * prob.cardyV (c' / 12) t : ℝ) : ℂ) := by
  obtain ⟨hS, ha0, hc'_pos⟩ := shift_le_of_max_le prob hc'
  set M := prob.cardyNorm (c' / 12) g with hM
  have hint_main := integrableOn_edgeKernelKW_mul prob hc' hg τ
  have hmeas_K : AEStronglyMeasurable (edgeKernelKW prob c' τ) (volume.restrict (Ioi 0)) :=
    (measurable_edgeKernelKW prob hc'_pos.le).comp (measurable_const.prodMk measurable_id)
      |>.aestronglyMeasurable
  have hint_K : ∀ (f : ℝ → ℝ), AEMeasurable f (volume.restrict (Ioi 0)) →
      (∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t) →
      (∀ t ∈ Ioi (0 : ℝ), f t ≤ |g t * prob.cardyV (c' / 12) t| / M) →
      IntegrableOn (fun t => edgeKernelKW prob c' τ t * (f t : ℂ)) (Ioi 0) := by
    intro f hf_meas hf_nn hf_le
    refine (hint_main.div_const (M : ℂ)).mono
      ((hmeas_K.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hf_meas.aestronglyMeasurable))) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf_nn t ht), norm_div, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
    calc ‖edgeKernelKW prob c' τ t‖ * f t
        ≤ ‖edgeKernelKW prob c' τ t‖ * (|g t * prob.cardyV (c' / 12) t| / M) :=
          mul_le_mul_of_nonneg_left (hf_le t ht) (norm_nonneg _)
      _ = ‖edgeKernelKW prob c' τ t‖ * |g t * prob.cardyV (c' / 12) t| / M := by ring
      _ = _ := by rw [Real.norm_eq_abs]
  have hV_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ prob.cardyV (c' / 12) t := fun t ht =>
    prob.cardyV_nonneg hS (mem_Ioi.mp ht).le
  have hint_K_pos : IntegrableOn (fun t => edgeKernelKW prob c' τ t * (bandPos prob (c' / 12) g t : ℂ))
      (Ioi 0) := by
    refine hint_K _ (bandPos_aemeasurable hg) (fun t ht => bandPos_nonneg hS hg (mem_Ioi.mp ht).le)
      fun t ht => ?_
    unfold bandPos
    rw [abs_mul, abs_of_nonneg (hV_nn t ht)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (max_le (le_abs_self _) (abs_nonneg _)) (hV_nn t ht)) hM_pos.le
  have hint_K_neg : IntegrableOn (fun t => edgeKernelKW prob c' τ t * (bandNeg prob (c' / 12) g t : ℂ))
      (Ioi 0) := by
    refine hint_K _ (bandNeg_aemeasurable hg) (fun t ht => bandNeg_nonneg hS hg (mem_Ioi.mp ht).le)
      fun t ht => ?_
    unfold bandNeg
    rw [abs_mul, abs_of_nonneg (hV_nn t ht)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (max_le (neg_le_abs _) (abs_nonneg _)) (hV_nn t ht)) hM_pos.le
  have hI_pos : ∫ ξ : ℝ, edgeKernelKW prob c' τ ξ ∂bandMeasPos prob (c' / 12) g =
      ∫ t in Ioi (0 : ℝ), edgeKernelKW prob c' τ t * (bandPos prob (c' / 12) g t : ℂ) := by
    unfold bandMeasPos
    rw [integral_withDensity_eq_integral_toReal_smul₀ (bandPos_aemeasurable hg).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [ENNReal.toReal_ofReal (bandPos_nonneg hS hg (mem_Ioi.mp ht).le), Complex.real_smul,
      mul_comm]
  have hI_neg : ∫ ξ : ℝ, edgeKernelKW prob c' τ ξ ∂bandMeasNeg prob (c' / 12) g =
      ∫ t in Ioi (0 : ℝ), edgeKernelKW prob c' τ t * (bandNeg prob (c' / 12) g t : ℂ) := by
    unfold bandMeasNeg
    rw [integral_withDensity_eq_integral_toReal_smul₀ (bandNeg_aemeasurable hg).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [ENNReal.toReal_ofReal (bandNeg_nonneg hS hg (mem_Ioi.mp ht).le), Complex.real_smul,
      mul_comm]
  rw [hI_pos, hI_neg, ← integral_sub hint_K_pos hint_K_neg]
  have hsub_eq : EqOn (fun t => edgeKernelKW prob c' τ t * (bandPos prob (c' / 12) g t : ℂ) -
        edgeKernelKW prob c' τ t * (bandNeg prob (c' / 12) g t : ℂ))
      (fun t => ((M⁻¹ : ℝ) : ℂ) * (edgeKernelKW prob c' τ t *
        ((g t * prob.cardyV (c' / 12) t : ℝ) : ℂ))) (Ioi 0) := by
    intro t _
    unfold bandPos bandNeg
    calc edgeKernelKW prob c' τ t * ↑(max (g t) 0 * prob.cardyV (c' / 12) t / M) -
          edgeKernelKW prob c' τ t * ↑(max (-g t) 0 * prob.cardyV (c' / 12) t / M)
        = ((M⁻¹ : ℝ) : ℂ) * (edgeKernelKW prob c' τ t *
            (((max (g t) 0 - max (-g t) 0 : ℝ) : ℂ) * ↑(prob.cardyV (c' / 12) t))) := by
          push_cast; ring
      _ = ((M⁻¹ : ℝ) : ℂ) * (edgeKernelKW prob c' τ t * ↑(g t * prob.cardyV (c' / 12) t)) := by
          rw [show max (g t) 0 - max (-g t) 0 = g t by
            rcases le_total 0 (g t) with h | h <;> simp [h]]
          push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsub_eq, integral_const_mul]

end Density

end FormalResearch.ModularBootstrap.FixedWeightBand
