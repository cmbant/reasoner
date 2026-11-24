module

public import FormalResearch.ModularBootstrap.Duality.Compactness
public import FormalResearch.ModularBootstrap.Duality.CrossingMeasure

/-!
# From limit measures on `[0, 1]` back to crossing measures on `[T, ∞)`

Given a finite measure `μ` on `[0, 1]` (the compactification of `[T₀, ∞]`), the measure
`ν = (τ₊ μ|_{s>0}) / w_*` on `ℝ` (pushforward by `τ(s) = T₀ + 1/s - 1`, divided by `w_*`) satisfies
`∫ g dν = ∫_{s>0} (g/w_*)(τ s) dμ`. The crossing equations for `Ξ_β / w_*` on `[0, 1]` become
the crossing equations (Z2) for `ν`, the bound `e^{-2πβt} ≤ C_β w_*` gives (Z1), `∫ w_* dν ≤ mass μ`,
and `∫ ζ_T dμ = 0` gives `ν (Iio T) = 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

lemma measurable_wStar (a β₀ : ℝ) : Measurable (wStar a β₀) := by
  unfold wStar
  have h1 : Measurable (Function.uncurry fun (t β : ℝ) =>
      Real.exp (-2 * π * β * t) * thetaW a β) := by
    have := measurable_thetaW a
    fun_prop
  exact (h1.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc 0 β₀))).measurable

lemma measurable_tauE (T₀ : ℝ) : Measurable (tauE T₀) := by
  unfold tauE; fun_prop

/-- `{s > 0}` in `[0, 1]`. -/
def posSet : Set Ecoord := {s | 0 < s.1}

lemma measurableSet_posSet : MeasurableSet posSet :=
  measurableSet_lt measurable_const measurable_subtype_coe

/-- The measure `ν = (τ₊ (μ|_{s>0})) / w_*` on `ℝ`. -/
noncomputable def pullMeasure (a β₀ T₀ : ℝ) (μ : Measure Ecoord) : Measure ℝ :=
  (Measure.map (tauE T₀) (μ.restrict posSet)).withDensity
    (fun t => ENNReal.ofReal (1 / wStar a β₀ t))

section

variable {a β₀ T₀ : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀) (hT₀ : 0 < T₀)
variable (μ : Measure Ecoord) [IsFiniteMeasure μ]

include ha hβ₀ hT₀ in
lemma wStar_tauE_pos {s : Ecoord} (hs : 0 < s.1) : 0 < wStar a β₀ (tauE T₀ s) :=
  wStar_pos ha.le hβ₀ (hT₀.le.trans (tauE_ge hs))

lemma measurable_dens (a β₀ : ℝ) : Measurable (fun t => ENNReal.ofReal (1 / wStar a β₀ t)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_wStar a β₀))

omit [IsFiniteMeasure μ] in
include ha hβ₀ hT₀ in
lemma integral_pullMeasure {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ t, g t ∂(pullMeasure a β₀ T₀ μ) =
      ∫ s in posSet, g (tauE T₀ s) / wStar a β₀ (tauE T₀ s) ∂μ := by
  unfold pullMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_dens a β₀).aemeasurable
    (Eventually.of_forall fun t => ENNReal.ofReal_lt_top) g]
  have hm : AEStronglyMeasurable (fun t => (ENNReal.ofReal (1 / wStar a β₀ t)).toReal • g t)
      (Measure.map (tauE T₀) (μ.restrict posSet)) :=
    (((measurable_dens a β₀).ennreal_toReal).smul hg).aestronglyMeasurable
  rw [integral_map (measurable_tauE T₀).aemeasurable hm]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_posSet] with s hs
  have hw := wStar_tauE_pos ha hβ₀ hT₀ hs
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

include ha hβ₀ hT₀ in
lemma integrable_pullMeasure_of_le {g : ℝ → ℝ} (hg : Measurable g) (M : ℝ)
    (hM : ∀ t, T₀ ≤ t → |g t| ≤ M * wStar a β₀ t) :
    Integrable g (pullMeasure a β₀ T₀ μ) := by
  unfold pullMeasure
  rw [integrable_withDensity_iff_integrable_smul' (measurable_dens a β₀)
    (Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  have hm : AEStronglyMeasurable (fun t => (ENNReal.ofReal (1 / wStar a β₀ t)).toReal • g t)
      (Measure.map (tauE T₀) (μ.restrict posSet)) :=
    (((measurable_dens a β₀).ennreal_toReal).smul hg).aestronglyMeasurable
  rw [integrable_map_measure hm (measurable_tauE T₀).aemeasurable]
  refine Integrable.of_bound (C := |M|) (hm.comp_measurable (measurable_tauE T₀)) ?_
  filter_upwards [ae_restrict_mem measurableSet_posSet] with s hs
  have hw := wStar_tauE_pos ha hβ₀ hT₀ hs
  simp only [Function.comp, smul_eq_mul, Real.norm_eq_abs, abs_mul]
  rw [ENNReal.toReal_ofReal (by positivity), abs_of_pos (by positivity)]
  have := hM _ (tauE_ge hs)
  calc 1 / wStar a β₀ (tauE T₀ s) * |g (tauE T₀ s)|
      ≤ 1 / wStar a β₀ (tauE T₀ s) * (M * wStar a β₀ (tauE T₀ s)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = M := by field_simp
    _ ≤ |M| := le_abs_self _

/-- Support of the pulled-back measure: if a cut-off `ζ ≥ 0` has `∫ ζ dμ = 0` and `ζ s = 0`, `s > 0`
forces `τ(s) ∈ X` for a measurable `X`, then `pullMeasure a β₀ T₀ μ` vanishes on `Xᶜ` (generalises
`pullMeasure_Iio_eq_zero`, the case `X = [T, ∞)`, `ζ = ζ_T`). -/
lemma pullMeasure_compl_eq_zero {X : Set ℝ} (hXm : MeasurableSet X) {ζ : Ecoord →ᵇ ℝ}
    (hζ0 : ∀ s, 0 ≤ ζ s) (hζX : ∀ s : Ecoord, 0 < s.1 → ζ s = 0 → tauE T₀ s ∈ X)
    (hζ : ∫ s, ζ s ∂μ = 0) :
    pullMeasure a β₀ T₀ μ Xᶜ = 0 := by
  have hae : ζ =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hζ0 (BoundedContinuousFunction.integrable μ _)).1 hζ
  have hnull : μ {s : Ecoord | tauE T₀ s ∉ X ∧ 0 < s.1} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (ae_iff.1 hae)
    simp only [mem_ofPred_eq, Pi.zero_apply]
    intro h0
    exact hs.1 (hζX s hs.2 h0)
  have h1 : (Measure.map (tauE T₀) (μ.restrict posSet)) Xᶜ = 0 := by
    rw [Measure.map_apply (measurable_tauE T₀) hXm.compl,
      Measure.restrict_apply (measurable_tauE T₀ hXm.compl)]
    refine measure_mono_null (fun s hs => ?_) hnull
    exact ⟨hs.1, hs.2⟩
  exact withDensity_absolutelyContinuous _ _ h1

/-- Support of the pulled-back measure below `T`; the case `X = [T, ∞)`, `ζ = ζ_T` of
`pullMeasure_compl_eq_zero`. -/
lemma pullMeasure_Iio_eq_zero {T : ℝ} (hT₀T : T₀ ≤ T) (hζ : ∫ s, zetaB T₀ T s ∂μ = 0) :
    pullMeasure a β₀ T₀ μ (Iio T) = 0 := by
  have h := pullMeasure_compl_eq_zero (a := a) (β₀ := β₀) (T₀ := T₀) μ (X := Ici T)
    measurableSet_Ici (zetaB_nonneg T₀ T) (fun s hs h0 => by
      by_contra hn
      exact ((zetaB_pos_iff hT₀T hs).2 (not_le.mp hn)).ne' h0) hζ
  rwa [compl_Ici] at h

omit [IsFiniteMeasure μ] in
lemma pullMeasure_Iio_T₀ : pullMeasure a β₀ T₀ μ (Iio T₀) = 0 := by
  have h1 : (Measure.map (tauE T₀) (μ.restrict posSet)) (Iio T₀) = 0 := by
    rw [Measure.map_apply (measurable_tauE T₀) measurableSet_Iio,
      Measure.restrict_apply (measurable_tauE T₀ measurableSet_Iio)]
    have : tauE T₀ ⁻¹' Iio T₀ ∩ posSet = ∅ := by
      ext s
      simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_and]
      intro h hs
      exact absurd h (not_lt.2 (tauE_ge hs))
    rw [this]; exact measure_empty
  exact withDensity_absolutelyContinuous _ _ h1

end

/-- **Theorem E(b), transport.** A finite measure `μ` on `[0, 1]` with mass `≤ C₀` and
`∫ Ξ_β/w_* dμ = ∫ Ξ_β ρ_C dt` for all `β > 0` gives a crossing measure `ν` (conditions (Z1),
(Z2)) with `∫ w_* dν ≤ C₀`, supported on `[T, ∞)` for every `T ≥ T₀` with `∫ ζ_T dμ = 0`. -/
theorem exists_crossingMeasure_of_limit {cTilde β₀ T₀ : ℝ} (S : DualSetup cTilde β₀ T₀)
    (μ : FiniteMeasure Ecoord) (hmass : (μ.mass : ℝ) ≤ dualC0 (cTilde / 12) β₀)
    (hcross : ∀ (β : ℝ) (hβ : 0 < β),
      ∫ x, FtildeB (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀) (by linarith [S.ha]) S.hβ₀ S.hT₀pos hβ x
        ∂(μ : Measure Ecoord) = crossingRHS (cTilde / 12) β) :
    ∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
      (∀ T, T₀ ≤ T → ∫ x, zetaB T₀ T x ∂(μ : Measure Ecoord) = 0 → meas.ν (Iio T) = 0) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 (cTilde / 12) β₀ := by
  have ha0 : 0 < cTilde / 12 := by linarith [S.ha]
  set a := cTilde / 12 with ha_def
  set ν := pullMeasure a β₀ T₀ (μ : Measure Ecoord) with hν
  have hIio0 : ν (Iio 0) = 0 :=
    measure_mono_null (Iio_subset_Iio S.hT₀pos.le) (pullMeasure_Iio_T₀ (μ : Measure Ecoord))
  have hrestr : ν.restrict (Ici 0) = ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, show {x : ℝ | x ∉ Ici 0} = Iio 0 by ext t; simp]
    exact hIio0
  have hint_le : ∀ {g : ℝ → ℝ}, Measurable g → ∀ M : ℝ, (∀ t, T₀ ≤ t → |g t| ≤ M * wStar a β₀ t) →
      Integrable g ν := fun hg M hM =>
    integrable_pullMeasure_of_le ha0 S.hβ₀ S.hT₀pos (μ : Measure Ecoord) hg M hM
  have hw_int : Integrable (wStar a β₀) ν := by
    refine hint_le (measurable_wStar a β₀) 1 fun t ht => ?_
    rw [abs_of_pos (wStar_pos ha0.le S.hβ₀ (S.hT₀pos.le.trans ht)), one_mul]
  refine ⟨{ ν := ν
            supp_nonneg := hIio0
            finite_laplace := fun {β} hβ => ?_
            crossing := fun {β} hβ => ?_ }, fun T hT hζ => ?_, hw_int, ?_⟩
  · obtain ⟨C, _, hC⟩ := exp_le_const_wStar (a := a) (β₀ := β₀) ha0.le S.hβ₀ hβ
    refine (hint_le (by fun_prop) C fun t ht => ?_).integrableOn
    rw [abs_of_pos (Real.exp_pos _)]
    exact hC t (S.hT₀pos.le.trans ht)
  · show ∫ t in Ici 0, thermalDiff 1 β t ∂ν = _
    rw [hrestr]
    have hmeas : Measurable (thermalDiff 1 β) := by unfold thermalDiff; fun_prop
    rw [hν, integral_pullMeasure ha0 S.hβ₀ S.hT₀pos (μ : Measure Ecoord) hmeas]
    have hF : ∫ s in posSet, thermalDiff 1 β (tauE T₀ s) / wStar a β₀ (tauE T₀ s) ∂(μ : Measure Ecoord)
        = ∫ s, Ftilde a β₀ T₀ β s ∂(μ : Measure Ecoord) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := posSet) (f := Ftilde a β₀ T₀ β)]
      · refine setIntegral_congr_fun measurableSet_posSet fun s hs => ?_
        have : s.1 ≠ 0 := hs.ne'
        simp [Ftilde, this]
      · intro s hs
        have : s.1 = 0 := by
          have h0 := s.2.1
          by_contra hne
          exact hs (lt_of_le_of_ne h0 (Ne.symm hne))
        simp [Ftilde, this]
    rw [hF]
    exact hcross β hβ
  · exact pullMeasure_Iio_eq_zero (a := a) (β₀ := β₀) (μ : Measure Ecoord) hT hζ
  · show ∫ t, wStar a β₀ t ∂ν ≤ dualC0 a β₀
    rw [hν, integral_pullMeasure ha0 S.hβ₀ S.hT₀pos (μ : Measure Ecoord) (measurable_wStar a β₀)]
    have : ∫ s in posSet, wStar a β₀ (tauE T₀ s) / wStar a β₀ (tauE T₀ s) ∂(μ : Measure Ecoord)
        = ∫ s in posSet, (1 : ℝ) ∂(μ : Measure Ecoord) := by
      refine setIntegral_congr_fun measurableSet_posSet fun s hs => ?_
      exact div_self (wStar_tauE_pos ha0 S.hβ₀ S.hT₀pos hs).ne'
    rw [this, setIntegral_const, smul_eq_mul, mul_one]
    refine le_trans ?_ hmass
    rw [finiteMeasure_mass_coe]
    exact measureReal_mono (subset_univ _)

/-- info: 'FormalResearch.ModularBootstrap.Duality.exists_crossingMeasure_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exists_crossingMeasure_of_limit

end FormalResearch.ModularBootstrap.Duality
