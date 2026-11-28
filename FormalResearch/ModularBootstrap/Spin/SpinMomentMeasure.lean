module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentDom
public import FormalResearch.ModularBootstrap.Spin.SpinMomentVacLimit
public import FormalResearch.ModularBootstrap.Spin.SpinDAssembly
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuum

/-!
# Spin-square spectral measure, scaled Volterra continuity, and Virasoro Cardy ratios

* `spinMomentSpectralMeasure`: Airy-rescaled spin-square spectral measure `η_j`.
* `spinMomentVolterraScaled`: scaled Volterra adjoint `(K^* g₅)(r) / c'`, continuous on `Ici 0`.
* `virasoro_cardy_jAiry_bounds`, `virasoro_cardy_jAiry_ratio_tendsto`,
  `virasoro_w5_cardy_ratio_tendsto`: uniform tip Cardy ratios on positive compacts.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Upper
open FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Ramped
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Bump

/-! ### 1. Spin-square Airy spectral measure -/

/-- The Airy-rescaled spin-square spectral measure `u_*(dM / (c' ρ_C J))` (with the `2π`
normalization of `spectralMeasure`, matching `spinMoment_vac_source_limsup_le`). -/
noncomputable def spinMomentSpectralMeasure (c' : ℝ) (ν : Measure (ℝ × ℝ)) : Measure ℝ :=
  spectralMeasure virasoroProblem c' (ENNReal.ofReal (1 / c') • spinMomentMeasure ν)

lemma spinMomentMeasure_Iio_null {a τ : ℝ} {X : Set (ℝ × ℝ)}
    (hX : X ⊆ {p | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X) :
    spinMomentMeasure meas.ν (Iio τ) = 0 := by
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  unfold spinMomentMeasure
  rw [Measure.map_apply hm measurableSet_Iio, withDensity_apply _ (hm measurableSet_Iio)]
  have hpre : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio τ ⊆ Xᶜ := by
    intro p hp hpX
    have := hX hpX
    simp only [mem_preimage, mem_Iio, mem_ofPred_eq] at hp this
    linarith
  exact le_antisymm
    ((lintegral_mono_set (f := fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 - p.2) ^ 2)) hpre).trans
      (by rw [setLIntegral_measure_zero _ _ meas.supp]))
    bot_le

lemma spinMomentMeasure_singleton_zero_null {a τ : ℝ} (hτ : 0 < τ) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ {p | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X) :
    spinMomentMeasure meas.ν {0} = 0 := by
  have _ := hτ
  exact measure_mono_null (fun _ hx => by simp only [mem_singleton_iff] at hx; subst hx; exact hτ)
    (spinMomentMeasure_Iio_null hX meas)

lemma spinMomentSpectralMeasure_supp {c' a τ : ℝ} (hc' : 0 < c') (_hτ : 0 < τ)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ {p | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X) :
    spinMomentSpectralMeasure c' meas.ν (Ioi (uAiry c' τ)) = 0 := by
  unfold spinMomentSpectralMeasure spectralMeasure
  have hu : Measurable (uAiry c') := (continuous_uAiry c').measurable
  rw [Measure.map_apply hu measurableSet_Ioi]
  have hsub : (uAiry c') ⁻¹' Ioi (uAiry c' τ) ∩ Ioi (0 : ℝ) ⊆ Iio τ := by
    intro t ⟨ht1, _⟩
    simp only [mem_preimage, mem_Ioi] at ht1
    by_contra hle
    exact absurd (uAiry_antitone hc' (not_lt.mp hle)) (not_le_of_gt ht1)
  have hnull : (ENNReal.ofReal (1 / c') • spinMomentMeasure meas.ν)
      ((uAiry c') ⁻¹' Ioi (uAiry c' τ) ∩ Ioi (0 : ℝ)) = 0 := by
    simp only [smul_apply, smul_eq_mul]
    rw [measure_mono_null hsub (spinMomentMeasure_Iio_null hX meas), mul_zero]
  rw [withDensity_apply _ (hu measurableSet_Ioi), Measure.restrict_restrict (hu measurableSet_Ioi)]
  exact setLIntegral_measure_zero _ _ hnull

lemma spinMomentSpectralMeasure_Ici_lt_top {c' a B τ : ℝ} (hc' : 24 ≤ c') (_ha : 2 ≤ a)
    (_hB : 0 ≤ B) (hτ : 0 < τ) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X) (A : ℝ) :
    spinMomentSpectralMeasure c' meas.ν (Ici A) < ⊤ := by
  have hc0 : 0 < c' := by linarith
  have hXτ : X ⊆ {p | τ ≤ p.1 + p.2} := hX.trans Set.inter_subset_right
  set T := tAiry c' A
  have haV : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hcont : ContinuousOn (spectralWeight virasoroProblem c') (Icc τ T) := by
    unfold spectralWeight
    refine continuousOn_const.div ?_ fun t ht => ?_
    · exact (((continuous_const.mul (continuous_cardyV virasoroProblem (c' / 12))).mul
        (continuous_jAiry c'))).continuousOn
    · have ht0 : 0 < t := hτ.trans_le ht.1
      have := virasoroProblem.cardyV_pos haV ht0
      have := jAiry_pos hc0 ht0
      positivity
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set νM : Measure ℝ := ENNReal.ofReal (1 / c') • spinMomentMeasure meas.ν
  have hνM_null : νM (Iio τ) = 0 := by
    simp only [νM, smul_apply, smul_eq_mul, spinMomentMeasure_Iio_null hXτ meas, mul_zero]
  unfold spinMomentSpectralMeasure spectralMeasure
  rw [Measure.map_apply (continuous_uAiry c').measurable measurableSet_Ici,
    withDensity_apply _ ((continuous_uAiry c').measurable measurableSet_Ici)]
  have hsub : (uAiry c' ⁻¹' Ici A) ≤ᵐ[νM.restrict (Ioi 0)] Icc τ T := by
    have hae : ∀ᵐ t ∂νM, τ ≤ t := by
      have := measure_eq_zero_iff_ae_notMem.1 hνM_null
      filter_upwards [this] with t ht
      exact not_lt.mp ht
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))]
      with t h1 h2 h3
    refine ⟨h1, ?_⟩
    have := tAiry_antitone hc0 (show A ≤ uAiry c' t from h3)
    rwa [tAiry_uAiry hc0 (mem_Ioi.1 h2).le] at this
  have hcc : spinMomentMeasure meas.ν (Icc 0 T) < ⊤ :=
    spinMomentMeasure_Icc_lt_top hX meas T
  calc ∫⁻ t in uAiry c' ⁻¹' Ici A, spectralDensity virasoroProblem c' t ∂(νM.restrict (Ioi 0))
      ≤ ∫⁻ t in Icc τ T, spectralDensity virasoroProblem c' t ∂(νM.restrict (Ioi 0)) :=
        lintegral_mono_set' hsub
    _ ≤ ∫⁻ t in Icc τ T, ENNReal.ofReal M ∂(νM.restrict (Ioi 0)) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        unfold spectralDensity
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM t ht))
    _ = ENNReal.ofReal M * (νM.restrict (Ioi 0)) (Icc τ T) := setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        calc (νM.restrict (Ioi 0)) (Icc τ T) ≤ νM (Icc τ T) := Measure.restrict_le_self _
          _ ≤ νM (Icc 0 T) := measure_mono (Icc_subset_Icc hτ.le le_rfl)
          _ = ENNReal.ofReal (1 / c') * spinMomentMeasure meas.ν (Icc 0 T) := by
              simp [νM, smul_apply, smul_eq_mul]
          _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcc

lemma spinMomentSpectralMeasure_isLocallyFinite {c' a B τ : ℝ} (hc' : 24 ≤ c') (ha : 2 ≤ a)
    (hB : 0 ≤ B) (hτ : 0 < τ) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X) :
    IsLocallyFiniteMeasure (spinMomentSpectralMeasure c' meas.ν) := by
  refine ⟨fun x => ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  exact lt_of_le_of_lt (measure_mono Icc_subset_Ici_self)
    (spinMomentSpectralMeasure_Ici_lt_top hc' ha hB hτ hX meas (x - 1))

lemma integral_spinMomentSpectralMeasure_psiAiry {c' a τ : ℝ} (hc' : 24 ≤ c') (hτ : 0 < τ)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ {p | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0)) :
    ∫ u, psiAiry virasoroProblem c' g u ∂(spinMomentSpectralMeasure c' meas.ν) =
      (∫ t in Ici 0, g t ∂(spinMomentMeasure meas.ν)) / (2 * π * c') := by
  have hc0 : 0 < c' := by linarith
  have haV : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hnull : (ENNReal.ofReal (1 / c') • spinMomentMeasure meas.ν) {0} = 0 := by
    simp [smul_eq_mul, spinMomentMeasure_singleton_zero_null hτ hX meas]
  unfold spinMomentSpectralMeasure
  rw [integral_spectralMeasure_psiAiry virasoroProblem hc0 haV hnull hg,
    Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

lemma integrable_spinMomentSpectralMeasure_psiAiry_iff {c' a τ : ℝ} (hc' : 24 ≤ c') (hτ : 0 < τ)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ {p | τ ≤ p.1 + p.2}) (meas : SpinCrossingMeasureOn a X)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0)) :
    Integrable (psiAiry virasoroProblem c' g) (spinMomentSpectralMeasure c' meas.ν) ↔
      IntegrableOn g (Ici 0) (spinMomentMeasure meas.ν) := by
  have hc0 : 0 < c' := by linarith
  have haV : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hnull : (ENNReal.ofReal (1 / c') • spinMomentMeasure meas.ν) {0} = 0 := by
    simp [smul_eq_mul, spinMomentMeasure_singleton_zero_null hτ hX meas]
  unfold spinMomentSpectralMeasure
  rw [integrable_spectralMeasure_psiAiry_iff virasoroProblem hc0 haV hnull hg]
  unfold IntegrableOn
  rw [Measure.restrict_smul]
  constructor
  · intro h
    have hsm : Integrable g (ENNReal.ofReal c' • (ENNReal.ofReal (1 / c') • (spinMomentMeasure meas.ν).restrict (Ici 0))) :=
      h.smul_measure ENNReal.ofReal_ne_top
    rwa [smul_smul, ← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel hc0.ne',
      ENNReal.ofReal_one, one_smul] at hsm
  · intro h
    exact h.smul_measure ENNReal.ofReal_ne_top

/-! ### 2. Scaled Volterra adjoint and continuity -/

/-- Scaled Volterra adjoint `r ↦ (K^* g₅)(r) / c'` for `SPIN-M`. -/
noncomputable def spinMomentVolterraScaled (d : BumpData) (N : ℕ) (η : ℝ) (σs : ℕ → ℝ)
    (c' r : ℝ) : ℝ :=
  spinVolterraAdjoint (bumpG spinMomentW5Prob d N η σs c') r / c'

private lemma integrableOn_mul_pow_exp_decay {C δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ici 0)) (hdec : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * Real.exp (-δ * √t))
    (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * g t) (Ici 0) volume := by
  set M := max C 0 * ((Nat.factorial (2 * k + 4) : ℝ) / δ ^ (2 * k + 4))
  have hm : AEStronglyMeasurable (fun t : ℝ => t ^ k * g t) (volume.restrict (Ici 0)) :=
    ((continuous_id.pow k).continuousOn.mul hg_cont).aestronglyMeasurable measurableSet_Ici
  refine (integrableOn_one_add_rpow_neg_two.const_mul (4 * M + 2 * max C 0)).mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have ht0 : 0 ≤ t := mem_Ici.mp ht
  have hexp := Real.pow_div_factorial_le_exp (δ * √t) (by positivity) (2 * k + 4)
  have hpow_eq : (δ * √t) ^ (2 * k + 4) = δ ^ (2 * k + 4) * t ^ (k + 2) := by
    rw [mul_pow, show (√t) ^ (2 * k + 4) = (√t ^ 2) ^ (k + 2) by ring, Real.sq_sqrt ht0]
  rw [hpow_eq] at hexp
  have hfac_pos : (0 : ℝ) < Nat.factorial (2 * k + 4) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h1 : δ ^ (2 * k + 4) * t ^ (k + 2) * Real.exp (-δ * √t) ≤ (Nat.factorial (2 * k + 4) : ℝ) := by
    have hpow' : δ ^ (2 * k + 4) * t ^ (k + 2) ≤ (Nat.factorial (2 * k + 4) : ℝ) * Real.exp (δ * √t) := by
      have := (div_le_iff₀ hfac_pos).mp hexp
      linarith
    calc δ ^ (2 * k + 4) * t ^ (k + 2) * Real.exp (-δ * √t)
        ≤ ((Nat.factorial (2 * k + 4) : ℝ) * Real.exp (δ * √t)) * Real.exp (-δ * √t) := by gcongr
      _ = (Nat.factorial (2 * k + 4) : ℝ) := by
          rw [mul_assoc, ← Real.exp_add, show δ * √t + -δ * √t = 0 by ring, Real.exp_zero, mul_one]
  have htk2 : t ^ (k + 2) * Real.exp (-δ * √t) ≤ (Nat.factorial (2 * k + 4) : ℝ) / δ ^ (2 * k + 4) := by
    have hδp : 0 < δ ^ (2 * k + 4) := pow_pos hδ _
    calc t ^ (k + 2) * Real.exp (-δ * √t)
        = (δ ^ (2 * k + 4) * t ^ (k + 2) * Real.exp (-δ * √t)) / δ ^ (2 * k + 4) := by field_simp
      _ ≤ (Nat.factorial (2 * k + 4) : ℝ) / δ ^ (2 * k + 4) := div_le_div_of_nonneg_right h1 hδp.le
  have hexp1 : Real.exp (-δ * √t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := mul_nonneg hδ.le (Real.sqrt_nonneg t); linarith)
  have hC : C ≤ max C 0 := le_max_left _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have h1t2 : (1 + t) ^ 2 * t ^ k ≤ 2 * (t ^ k + t ^ (k + 2)) := by
    have hpoly : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1)]
    calc (1 + t) ^ 2 * t ^ k ≤ 2 * (1 + t ^ 2) * t ^ k := by gcongr
      _ = 2 * (t ^ k + t ^ (k + 2)) := by ring
  have hbd_tk : t ^ k * Real.exp (-δ * √t) ≤ 1 + t ^ (k + 2) * Real.exp (-δ * √t) := by
    by_cases ht1 : t ≤ 1
    · have : t ^ k ≤ 1 := pow_le_one₀ ht0 ht1
      calc t ^ k * Real.exp (-δ * √t) ≤ 1 * 1 := mul_le_mul this hexp1 (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
        _ ≤ 1 + t ^ (k + 2) * Real.exp (-δ * √t) := le_add_of_nonneg_right (by positivity)
    · have ht_ge : 1 ≤ t := by linarith
      have : t ^ k ≤ t ^ (k + 2) := by
        calc t ^ k = t ^ k * 1 := (mul_one _).symm
          _ ≤ t ^ k * t ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg ht0 k)
          _ = t ^ (k + 2) := by ring
      calc t ^ k * Real.exp (-δ * √t) ≤ t ^ (k + 2) * Real.exp (-δ * √t) := by gcongr
        _ ≤ 1 + t ^ (k + 2) * Real.exp (-δ * √t) := by linarith
  have h1t_pos : 0 < (1 + t) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 k),
    show (1 + t) ^ (-2 : ℝ) = ((1 + t) ^ 2)⁻¹ by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith),
        Real.rpow_natCast], ← div_eq_mul_inv, le_div_iff₀ h1t_pos]
  calc t ^ k * |g t| * (1 + t) ^ 2
      ≤ t ^ k * (max C 0 * Real.exp (-δ * √t)) * (1 + t) ^ 2 := by
        gcongr; exact (hdec t ht0).trans (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)
    _ = max C 0 * ((1 + t) ^ 2 * t ^ k * Real.exp (-δ * √t)) := by ring
    _ ≤ max C 0 * (2 * (t ^ k + t ^ (k + 2)) * Real.exp (-δ * √t)) := by gcongr
    _ = max C 0 * (2 * (t ^ k * Real.exp (-δ * √t) + t ^ (k + 2) * Real.exp (-δ * √t))) := by ring
    _ ≤ max C 0 * (2 * ((1 + t ^ (k + 2) * Real.exp (-δ * √t)) +
          t ^ (k + 2) * Real.exp (-δ * √t))) := by gcongr
    _ = 2 * max C 0 + 4 * (max C 0 * (t ^ (k + 2) * Real.exp (-δ * √t))) := by ring
    _ ≤ 2 * max C 0 + 4 * M := by
        gcongr; dsimp [M]; exact mul_le_mul_of_nonneg_left htk2 hC0
    _ = 4 * M + 2 * max C 0 := by ring

lemma continuousOn_spinMomentVolterraScaled (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∀ᶠ c' in atTop, ContinuousOn (spinMomentVolterraScaled (rpParams 4).bumpData N η σs c') (Ici 0) := by
  set d5 := (rpParams 4).bumpData
  filter_upwards [bumpG_good spinMomentW5Prob d5 N hN hη0 hη1 σs] with c' ⟨hc', htest, C_b, hCb, hdec⟩
  set g := bumpG spinMomentW5Prob d5 N η σs c'
  set δ := π * √(3 / c')
  have hδ : 0 < δ := by have := Real.pi_pos; positivity
  have hg_dec : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C_b * Real.exp (-δ * √t) := fun t ht0 => by
    have hsq : π * √(3 * t / c') = δ * √t := by
      dsimp [δ]; rw [show 3 * t / c' = (3 / c') * t by ring, Real.sqrt_mul (by positivity), mul_assoc]
    have hexp : Real.exp (-4 * π * √(c' / 12 * t) - π * √(3 * t / c')) ≤ Real.exp (-δ * √t) := by
      apply Real.exp_le_exp.mpr
      rw [hsq]
      have : 0 ≤ 4 * π * √(c' / 12 * t) := by have := Real.pi_pos; positivity
      linarith
    exact (hdec t ht0).trans (mul_le_mul_of_nonneg_left hexp hCb)
  have hInt0 : IntegrableOn g (Ici 0) volume := by
    simpa using integrableOn_mul_pow_exp_decay hδ htest.cont hg_dec 0
  have hInt1 : IntegrableOn (fun t : ℝ => t * g t) (Ici 0) volume := by
    simpa using integrableOn_mul_pow_exp_decay hδ htest.cont hg_dec 1
  have hformula : ∀ r : ℝ, 0 ≤ r →
      spinMomentVolterraScaled d5 N η σs c' r =
        ((3 * r / 2) * ((∫ t in Ici 0, g t) - ∫ t in (0 : ℝ)..r, g t) -
          (1 / 2) * ((∫ t in Ici 0, t * g t) - ∫ t in (0 : ℝ)..r, t * g t)) / c' := by
    intro r hr
    have hIci_sub : ∀ {fn : ℝ → ℝ}, IntegrableOn fn (Ici 0) volume →
        ∫ t in Ici r, fn t = (∫ t in Ici 0, fn t) - ∫ t in (0 : ℝ)..r, fn t := fun {fn} hfi => by
      have hsub := Set.Ioc_union_Ioi_eq_Ioi hr
      have hdisj : Disjoint (Ioc 0 r) (Ioi r) := Set.Ioc_disjoint_Ioi_same
      have hfi_oi : IntegrableOn fn (Ioi 0) volume := hfi.mono_set Ioi_subset_Ici_self
      have hsplit : ∫ t in Ioi 0, fn t = (∫ t in Ioc 0 r, fn t) + ∫ t in Ioi r, fn t := by
        rw [← hsub]
        exact setIntegral_union hdisj measurableSet_Ioi
          (hfi_oi.mono_set Set.Ioc_subset_Ioi_self)
          (hfi_oi.mono_set (Set.Ioi_subset_Ioi hr))
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi,
        MeasureTheory.integral_Ici_eq_integral_Ioi]
      rw [intervalIntegral.integral_of_le hr, hsplit]
      ring
    have h0 := hIci_sub hInt0
    have h1 := hIci_sub hInt1
    have hi0r : IntegrableOn g (Ici r) volume := hInt0.mono_set (Ici_subset_Ici.mpr hr)
    have hi1r : IntegrableOn (fun t => t * g t) (Ici r) volume :=
      hInt1.mono_set (Ici_subset_Ici.mpr hr)
    have hrw : (∫ t in Ici r, (3 * r - t) / 2 * g t) =
        (3 * r / 2) * (∫ t in Ici r, g t) - (1 / 2) * (∫ t in Ici r, t * g t) := by
      rw [← integral_const_mul (3 * r / 2) g, ← integral_const_mul (1 / 2) (fun t => t * g t),
        ← integral_sub (hi0r.const_mul _) (hi1r.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun t => by ring)
    unfold spinMomentVolterraScaled spinVolterraAdjoint
    rw [hrw, h0, h1]
  have hcont_prim : ∀ {fn : ℝ → ℝ}, ContinuousOn fn (Ici 0) →
      ContinuousOn (fun r => ∫ t in (0 : ℝ)..r, fn t) (Ici 0) :=
    fun {fn} hf r hr => by
      have hr0 : 0 ≤ r := mem_Ici.mp hr
      have huIcc : Set.uIcc 0 (r + 1) = Icc 0 (r + 1) := Set.uIcc_of_le (by linarith)
      have hint_u : IntegrableOn fn (Set.uIcc 0 (r + 1)) volume := by
        rw [huIcc]; exact (hf.mono Icc_subset_Ici_self).integrableOn_Icc
      have hIcc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, fn t) (Icc 0 (r + 1)) := by
        simpa [huIcc] using intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := r + 1) hint_u
      have hmem : Icc 0 (r + 1) ∈ 𝓝[Ici 0] r := by
        rcases eq_or_lt_of_le hr0 with rfl | hr0'
        · exact Icc_mem_nhdsGE (by norm_num)
        · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hr0' (by linarith))
      exact (hIcc.continuousWithinAt ⟨hr0, by linarith⟩).mono_of_mem_nhdsWithin hmem
  have hcont_rhs : ContinuousOn (fun r : ℝ =>
      ((3 * r / 2) * ((∫ t in Ici 0, g t) - ∫ t in (0 : ℝ)..r, g t) -
        (1 / 2) * ((∫ t in Ici 0, t * g t) - ∫ t in (0 : ℝ)..r, t * g t)) / c') (Ici 0) := by
    refine ContinuousOn.div_const (ContinuousOn.sub ?_ ?_) c'
    · refine ContinuousOn.mul ((continuous_const.mul continuous_id).div_const 2).continuousOn ?_
      exact continuousOn_const.sub (hcont_prim htest.cont)
    · refine continuousOn_const.mul ?_
      exact continuousOn_const.sub (hcont_prim (continuousOn_id.mul htest.cont))
  exact hcont_rhs.congr fun r hr => hformula r (mem_Ici.mp hr)

lemma integral_Ici_shift_div {c' : ℝ} (hc' : 0 < c') (x : ℝ) (f : ℝ → ℝ) :
    ∫ y in Ici x, f y = (1 / c') * ∫ z in Ici (0 : ℝ), f (x + z / c') := by
  have h1 : ∫ y in Ici x, f y = ∫ t in Ici (0 : ℝ), f (x + t) := by
    have heq : (Ici x).indicator f = fun y => (Ici (0 : ℝ)).indicator (fun t => f (x + t)) (y - x) := by
      ext y
      simp only [Set.indicator, mem_Ici, sub_nonneg]
      split_ifs <;> simp
    rw [← MeasureTheory.integral_indicator measurableSet_Ici,
      ← MeasureTheory.integral_indicator measurableSet_Ici]
    conv_lhs => rw [heq]
    simpa using MeasureTheory.integral_sub_right_eq_self
      (fun t => (Ici (0 : ℝ)).indicator (fun s => f (x + s)) t) x
  have h2 : ∫ t in Ici (0 : ℝ), f (x + t) = (1 / c') * ∫ z in Ici (0 : ℝ), f (x + z / c') := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ici,
      ← MeasureTheory.integral_indicator measurableSet_Ici]
    have hcomp := Measure.integral_comp_mul_left
      (fun t => (Ici (0 : ℝ)).indicator (fun s => f (x + s)) t) (1 / c')
    have heq_ind : (fun z => (Ici (0 : ℝ)).indicator (fun s => f (x + s)) (1 / c' * z)) =
        fun z => (Ici (0 : ℝ)).indicator (fun w => f (x + w / c')) z := by
      ext z
      simp only [Set.indicator, mem_Ici, one_div_mul_eq_div]
      by_cases hz : 0 ≤ z
      · have hdiv : 0 ≤ z / c' := div_nonneg hz hc'.le
        simp [hz, hdiv]
      · have hdiv : ¬ 0 ≤ z / c' := fun h => hz (nonneg_of_mul_nonneg_left
          (by simpa [div_eq_mul_inv] using h) (by positivity))
        simp [hz, hdiv]
    rw [heq_ind] at hcomp
    have hinv : |(1 / c')⁻¹| = c' := by rw [one_div, inv_inv, abs_of_pos hc']
    rw [hinv, smul_eq_mul] at hcomp
    have := congr_arg (fun v => (1 / c') * v) hcomp
    simpa only [← mul_assoc, one_div_mul_cancel hc'.ne', one_mul] using this.symm
  exact h1.trans h2

/-! ### 3. Virasoro Cardy ratios and window regularity -/

lemma virasoro_nullPoly_eq (q : ℝ) : virasoroProblem.nullPoly q = (1 - q) ^ 2 := by
  unfold FixedWeightProblem.nullPoly virasoroProblem
  simp [Fin.prod_univ_two]
  ring

lemma virasoro_cardy_jAiry_bounds {x₀ X : ℝ} (hx₀ : 0 < x₀) (hX : x₀ ≤ X) :
    ∃ c_lo C_hi : ℝ, 0 < c_lo ∧ 0 < C_hi ∧ ∀ᶠ c' in atTop, ∀ x ∈ Icc x₀ X,
      c_lo / c' * Real.exp (c' * besselL x) ≤
          psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
            jAiry c' (c' * x ^ 2 / 3) ∧
        psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
            jAiry c' (c' * x ^ 2 / 3) ≤
          C_hi / c' * Real.exp (c' * besselL x) := by
  obtain ⟨A0, hA0, hFKc⟩ := FKc_one_mul_rpow_eq
  obtain ⟨Cv, hCv, hcardy⟩ := WeightAxioms.cardyV_asymptotic_real virasoroProblem hx₀
  set p0 : ℝ := (1 - Real.exp (-4 * π * x₀)) ^ 2
  have hp0 : 0 < p0 := by
    have : Real.exp (-4 * π * x₀) < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
    exact sq_pos_of_pos (sub_pos.mpr this)
  have hpi := Real.pi_pos
  have hCS := CStar_pos
  have hbt := betaTip_pos
  set C_hi := 2 * (2 * X / (3 * π * CStar * A0 * betaTip * √(x₀ / 3)))
  set c_lo' := p0 / 2 * (2 * x₀ / (3 * π * CStar * A0 * betaTip * √(X / 3)))
  have hclo : 0 < c_lo' := by have : 0 < X := hx₀.trans_le hX; positivity
  have hChi : 0 < C_hi := by have : 0 < X := hx₀.trans_le hX; positivity
  refine ⟨c_lo', C_hi, hclo, hChi, ?_⟩
  filter_upwards [eventually_ge_atTop (max 48 (2 * Cv / p0))] with c' hc' x hx
  have hc48 : (48 : ℝ) ≤ c' := (le_max_left _ _).trans hc'
  have hc0 : 0 < c' := by linarith
  have hc_sh : max 1 (24 * virasoroProblem.totalShift) ≤ c' := by
    rw [virasoroProblem_totalShift]; exact max_le (by linarith) (by linarith)
  have hCv' : Cv / c' ≤ p0 / 2 := by
    have h1 : 2 * Cv / p0 ≤ c' := (le_max_right _ _).trans hc'
    rw [div_le_div_iff₀ hc0 zero_lt_two]
    have : 2 * Cv ≤ c' * p0 := (div_le_iff₀ hp0).mp h1
    linarith
  have hasym := hcardy hc_sh hx.1
  rw [virasoro_nullPoly_eq, show (virasoroProblem.w - 1 : ℕ) = 0 from rfl, pow_zero, one_mul] at hasym
  have hx0' : 0 < x := hx₀.trans_le hx.1
  have hXpos : 0 < X := hx₀.trans_le hX
  have hbL : besselL x = 2 * π * x / 3 := rfl
  rw [← hbL] at hasym
  have hnull_lo : p0 ≤ (1 - Real.exp (-4 * π * x)) ^ 2 := by
    have he : Real.exp (-4 * π * x) ≤ Real.exp (-4 * π * x₀) :=
      Real.exp_le_exp.mpr (by nlinarith [hx.1])
    have he0 : 0 ≤ 1 - Real.exp (-4 * π * x₀) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
    exact pow_le_pow_left₀ he0 (by linarith) 2
  have hV_lo : p0 / 2 * besselAs (c' * besselL x) ≤ virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) := by
    have h1 : p0 / 2 ≤ virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) := by
      linarith [(abs_le.mp hasym).1]
    have hbpos := Bessel.besselAs_pos (show 0 < c' * besselL x by rw [hbL]; positivity)
    exact (le_div_iff₀ hbpos).mp h1
  have hV_hi : virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤ 2 * besselAs (c' * besselL x) := by
    have h1 : virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) ≤ 2 := by
      have hnull_hi : (1 - Real.exp (-4 * π * x)) ^ 2 ≤ 1 := by
        have := Real.exp_pos (-4 * π * x)
        have : Real.exp (-4 * π * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        nlinarith
      have hp0_1 : p0 ≤ 1 := by
        have := Real.exp_pos (-4 * π * x₀)
        have : Real.exp (-4 * π * x₀) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        dsimp [p0]; nlinarith
      linarith [(abs_le.mp hasym).2]
    have hbpos := Bessel.besselAs_pos (show 0 < c' * besselL x by rw [hbL]; positivity)
    exact (div_le_iff₀ hbpos).mp h1
  have hFK : FKc 1 1 c' = A0 * √c' * c' ^ (1 / 3 : ℝ) := by
    have := hFKc c' hc0
    calc FKc 1 1 c' = (FKc 1 1 c' * c' ^ (-(1 / 3 : ℝ))) * c' ^ (1 / 3 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hc0]; simp
      _ = A0 * √c' * c' ^ (1 / 3 : ℝ) := by rw [this]
  have hj : jAiry c' (c' * x ^ 2 / 3) = 2 * x * c' ^ (1 / 3 : ℝ) / (3 * betaTip) := by
    unfold jAiry
    rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp, Real.sqrt_sq hx0'.le]
  have hbs : besselAs (c' * besselL x) = Real.exp (c' * besselL x) / (2 * π * √(x / 3) * √c') := by
    unfold besselAs
    rw [hbL, show 2 * π * (c' * (2 * π * x / 3)) = (2 * π) ^ 2 * (x / 3) * c' by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hprod : psiScale virasoroProblem c' * besselAs (c' * besselL x) * jAiry c' (c' * x ^ 2 / 3) =
      (2 * x / (3 * π * CStar * A0 * betaTip * √(x / 3))) / c' * Real.exp (c' * besselL x) := by
    unfold psiScale
    rw [qProb_virasoro, hFK, hj, hbs]
    have hc_r : (c' ^ (1 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
    have hsq : √c' * √c' = c' := Real.mul_self_sqrt hc0.le
    have hx3 : √(x / 3) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
    rw [Real.sq_sqrt hc0.le]
  have hpsi_nn : 0 ≤ psiScale virasoroProblem c' := (psiScale_pos virasoroProblem hc0).le
  have hj_nn : 0 ≤ jAiry c' (c' * x ^ 2 / 3) := (jAiry_pos hc0 (by positivity)).le
  have hsqx_lo : √(x₀ / 3) ≤ √(x / 3) := Real.sqrt_le_sqrt (by linarith [hx.1])
  have hsqx_hi : √(x / 3) ≤ √(X / 3) := Real.sqrt_le_sqrt (by linarith [hx.2])
  have hfac_lo : 2 * x₀ / (3 * π * CStar * A0 * betaTip * √(X / 3)) ≤
      2 * x / (3 * π * CStar * A0 * betaTip * √(x / 3)) := by
    apply div_le_div₀ (by positivity) (by linarith [hx.1]) (by positivity)
    gcongr
  have hfac_hi : 2 * x / (3 * π * CStar * A0 * betaTip * √(x / 3)) ≤
      2 * X / (3 * π * CStar * A0 * betaTip * √(x₀ / 3)) := by
    apply div_le_div₀ (by positivity) (by linarith [hx.2]) (by positivity)
    gcongr
  constructor
  · calc c_lo' / c' * Real.exp (c' * besselL x)
        ≤ p0 / 2 * ((2 * x / (3 * π * CStar * A0 * betaTip * √(x / 3))) / c' * Real.exp (c' * besselL x)) := by
          dsimp [c_lo']
          rw [show (p0 / 2 * (2 * x₀ / (3 * π * CStar * A0 * betaTip * √(X / 3)))) / c' * Real.exp (c' * besselL x) =
            p0 / 2 * ((2 * x₀ / (3 * π * CStar * A0 * betaTip * √(X / 3))) / c' * Real.exp (c' * besselL x)) by ring]
          gcongr
      _ = psiScale virasoroProblem c' * (p0 / 2 * besselAs (c' * besselL x)) * jAiry c' (c' * x ^ 2 / 3) := by
          rw [← hprod]; ring
      _ ≤ psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
            jAiry c' (c' * x ^ 2 / 3) := by gcongr
  · calc psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
          jAiry c' (c' * x ^ 2 / 3)
        ≤ psiScale virasoroProblem c' * (2 * besselAs (c' * besselL x)) * jAiry c' (c' * x ^ 2 / 3) := by
          gcongr
      _ = 2 * ((2 * x / (3 * π * CStar * A0 * betaTip * √(x / 3))) / c' * Real.exp (c' * besselL x)) := by
          rw [← hprod]; ring
      _ ≤ C_hi / c' * Real.exp (c' * besselL x) := by
          dsimp [C_hi]
          rw [show 2 * (2 * X / (3 * π * CStar * A0 * betaTip * √(x₀ / 3))) / c' * Real.exp (c' * besselL x) =
            2 * ((2 * X / (3 * π * CStar * A0 * betaTip * √(x₀ / 3))) / c' * Real.exp (c' * besselL x)) by ring]
          gcongr

private lemma ratio_diff_bound {px py a b c₀ d₂ p₀ : ℝ} (hp₀ : 0 < p₀) (hpy : p₀ / 2 ≤ py)
    (hax : |px - a| ≤ c₀) (hay : |py - b| ≤ c₀) (hab : |a - b| ≤ d₂) :
    |px / py - 1| ≤ (2 * c₀ + d₂) / (p₀ / 2) := by
  have hpy_pos : 0 < py := lt_of_lt_of_le (half_pos hp₀) hpy
  have hdiff : |px - py| ≤ 2 * c₀ + d₂ := by
    have heq : px - py = (px - a) - (py - b) + (a - b) := by ring
    rw [heq]
    calc |(px - a) - (py - b) + (a - b)| ≤ |(px - a) - (py - b)| + |a - b| := abs_add_le _ _
      _ ≤ (|px - a| + |py - b|) + d₂ := add_le_add (abs_sub _ _) hab
      _ ≤ (c₀ + c₀) + d₂ := add_le_add (add_le_add hax hay) le_rfl
      _ = 2 * c₀ + d₂ := by ring
  rw [show px / py - 1 = (px - py) / py by field_simp, abs_div, abs_of_pos hpy_pos]
  exact div_le_div₀ (by have := abs_nonneg (px - py); linarith) hdiff (half_pos hp₀) hpy

lemma virasoro_cardy_jAiry_ratio_tendsto {x₀ X Z : ℝ} (hx₀ : 0 < x₀) (_hX : x₀ ≤ X)
    (hZ : 0 ≤ Z) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c' in atTop, ∀ x ∈ Icc x₀ X, ∀ z ∈ Icc 0 Z,
      |virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) * jAiry c' (c' * x ^ 2 / 3) /
          (virasoroProblem.cardyV (c' / 12) (c' * (x + z / c') ^ 2 / 3) *
            jAiry c' (c' * (x + z / c') ^ 2 / 3)) -
          Real.exp (-2 * π * z / 3)| ≤ ε := by
  intro ε hε
  obtain ⟨Cv, hCv, hcardy⟩ := WeightAxioms.cardyV_asymptotic_real virasoroProblem hx₀
  set p0 : ℝ := (1 - Real.exp (-4 * π * x₀)) ^ 2
  have hp0 : 0 < p0 := by
    have : Real.exp (-4 * π * x₀) < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
    exact sq_pos_of_pos (sub_pos.mpr this)
  have hpi := Real.pi_pos
  have hbt := betaTip_pos
  set L_n : ℝ := 16 * π / p0
  set K_n : ℝ := 2 * (Cv + 1) / p0
  set C_n : ℝ := 2 * ((2 * K_n + L_n * Z) + 1 / x₀ * Z)
  have hCn : 0 ≤ C_n := by positivity
  filter_upwards [eventually_ge_atTop (max (max 48 (4 * Cv / p0)) (C_n / ε + 1)),
    eventually_ge_atTop (max 1 Z)] with c' hc' _hcZ x hx z hz
  have hc48 : (48 : ℝ) ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc0 : 0 < c' := by linarith
  set y := x + z / c'
  have hy_lo : x₀ ≤ y := by have : 0 ≤ z / c' := div_nonneg hz.1 hc0.le; linarith [hx.1]
  have hx_pos : 0 < x := hx₀.trans_le hx.1
  have hy_pos : 0 < y := hx₀.trans_le hy_lo
  have hxy_le : y - x ≤ Z / c' := by
    dsimp [y]; rw [add_sub_cancel_left]; exact div_le_div_of_nonneg_right hz.2 hc0.le
  have hc_sh : max 1 (24 * virasoroProblem.totalShift) ≤ c' := by
    rw [virasoroProblem_totalShift]; exact max_le (by linarith) (by linarith)
  have hax := hcardy hc_sh hx.1
  have hay := hcardy hc_sh hy_lo
  rw [virasoro_nullPoly_eq, show (virasoroProblem.w - 1 : ℕ) = 0 from rfl, pow_zero, one_mul,
    show 2 * π * x / 3 = besselL x from rfl] at hax
  rw [virasoro_nullPoly_eq, show (virasoroProblem.w - 1 : ℕ) = 0 from rfl, pow_zero, one_mul,
    show 2 * π * y / 3 = besselL y from rfl] at hay
  set px := virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x)
  set py := virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) / besselAs (c' * besselL y)
  have hCv' : Cv / c' ≤ p0 / 4 := by
    have h1 : 4 * Cv / p0 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
    have : 4 * Cv ≤ c' * p0 := (div_le_iff₀ hp0).mp h1
    rw [div_le_div_iff₀ hc0 (by norm_num : (0 : ℝ) < 4)]; linarith
  have hpy_lo : p0 / 2 ≤ py := by
    have hnull_y : p0 ≤ (1 - Real.exp (-4 * π * y)) ^ 2 := by
      have he : Real.exp (-4 * π * y) ≤ Real.exp (-4 * π * x₀) := Real.exp_le_exp.mpr (by nlinarith)
      have he0 : 0 ≤ 1 - Real.exp (-4 * π * x₀) :=
        sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [hx₀, hpi]))
      exact pow_le_pow_left₀ he0 (by linarith) 2
    linarith [(abs_le.mp hay).1]
  have hjx : jAiry c' (c' * x ^ 2 / 3) = 2 * x * c' ^ (1 / 3 : ℝ) / (3 * betaTip) := by
    unfold jAiry; rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp, Real.sqrt_sq hx_pos.le]
  have hjy : jAiry c' (c' * y ^ 2 / 3) = 2 * y * c' ^ (1 / 3 : ℝ) / (3 * betaTip) := by
    unfold jAiry; rw [show 3 * (c' * y ^ 2 / 3) / c' = y ^ 2 by field_simp, Real.sqrt_sq hy_pos.le]
  have hbs_ratio : besselAs (c' * besselL x) / besselAs (c' * besselL y) =
      √(y / x) * Real.exp (-2 * π * z / 3) := by
    unfold besselAs
    have hLx : c' * besselL x = 2 * π * c' * x / 3 := by unfold besselL; ring
    have hLy : c' * besselL y = 2 * π * c' * y / 3 := by unfold besselL; ring
    rw [hLx, hLy]
    have hLdiff : 2 * π * c' * x / 3 - 2 * π * c' * y / 3 = -2 * π * z / 3 := by
      dsimp [y]; field_simp; ring
    have hexp_div : Real.exp (2 * π * c' * x / 3) / Real.exp (2 * π * c' * y / 3) =
        Real.exp (-2 * π * z / 3) := by rw [← Real.exp_sub, hLdiff]
    have hsq_x : √(2 * π * (2 * π * c' * x / 3)) = √(2 * π * (2 * π * c' / 3)) * √x := by
      rw [show 2 * π * (2 * π * c' * x / 3) = (2 * π * (2 * π * c' / 3)) * x by ring,
        Real.sqrt_mul (by positivity)]
    have hsq_y : √(2 * π * (2 * π * c' * y / 3)) = √(2 * π * (2 * π * c' / 3)) * √y := by
      rw [show 2 * π * (2 * π * c' * y / 3) = (2 * π * (2 * π * c' / 3)) * y by ring,
        Real.sqrt_mul (by positivity)]
    rw [div_div_div_eq, hsq_x, hsq_y, Real.sqrt_div hy_pos.le]
    have hc2 : 0 < √(2 * π * (2 * π * c' / 3)) := Real.sqrt_pos.mpr (by positivity)
    calc Real.exp (2 * π * c' * x / 3) * (√(2 * π * (2 * π * c' / 3)) * √y) /
          (√(2 * π * (2 * π * c' / 3)) * √x * Real.exp (2 * π * c' * y / 3))
        = (√y / √x) * (Real.exp (2 * π * c' * x / 3) / Real.exp (2 * π * c' * y / 3)) := by field_simp
      _ = √y / √x * Real.exp (-2 * π * z / 3) := by rw [hexp_div]
  have hfull_eq : virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) * jAiry c' (c' * x ^ 2 / 3) /
        (virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3)) =
      (px / py) * √(x / y) * Real.exp (-2 * π * z / 3) := by
    have hbx := Bessel.besselAs_pos (show 0 < c' * besselL x by unfold besselL; positivity)
    have hby := Bessel.besselAs_pos (show 0 < c' * besselL y by unfold besselL; positivity)
    have hpx_mul : virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) = px * besselAs (c' * besselL x) :=
      (div_mul_cancel₀ _ hbx.ne').symm
    have hpy_mul : virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) = py * besselAs (c' * besselL y) :=
      (div_mul_cancel₀ _ hby.ne').symm
    rw [hpx_mul, hpy_mul, hjx, hjy]
    have hc_r : (c' ^ (1 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
    have hratio : (px * besselAs (c' * besselL x) * (2 * x * c' ^ (1 / 3 : ℝ) / (3 * betaTip))) /
          (py * besselAs (c' * besselL y) * (2 * y * c' ^ (1 / 3 : ℝ) / (3 * betaTip))) =
        (px / py) * (besselAs (c' * besselL x) / besselAs (c' * besselL y)) * (x / y) := by
      field_simp
    rw [hratio, hbs_ratio]
    have hsqrt_xy : √(y / x) * (x / y) = √(x / y) := by
      rw [Real.sqrt_div hy_pos.le, Real.sqrt_div hx_pos.le]
      have hsx : 0 < √x := Real.sqrt_pos.mpr hx_pos
      have hsy : 0 < √y := Real.sqrt_pos.mpr hy_pos
      calc (√y / √x) * (x / y) = (√y / √x) * ((√x * √x) / (√y * √y)) := by
            rw [Real.mul_self_sqrt hx_pos.le, Real.mul_self_sqrt hy_pos.le]
        _ = √x / √y := by field_simp
    calc (px / py) * (√(y / x) * Real.exp (-2 * π * z / 3)) * (x / y)
        = (px / py) * (√(y / x) * (x / y)) * Real.exp (-2 * π * z / 3) := by ring
      _ = (px / py) * √(x / y) * Real.exp (-2 * π * z / 3) := by rw [hsqrt_xy]
  have hpx_py : |px / py - 1| ≤ (2 * K_n + L_n * Z) / c' := by
    have hxy0 : 0 ≤ y - x := by dsimp [y]; rw [add_sub_cancel_left]; exact div_nonneg hz.1 hc0.le
    have h4xy : 0 ≤ 4 * π * (y - x) := mul_nonneg (mul_nonneg (by norm_num) hpi.le) hxy0
    have hnull_diff : |(1 - Real.exp (-4 * π * x)) ^ 2 - (1 - Real.exp (-4 * π * y)) ^ 2| ≤
        8 * π * (y - x) := by
      have hu1 : Real.exp (-4 * π * x) ≤ 1 := Real.exp_le_one_iff.mpr
        (by rw [show -4 * π * x = -(4 * π * x) by ring, neg_nonpos]; positivity)
      have hv1 : Real.exp (-4 * π * y) ≤ 1 := Real.exp_le_one_iff.mpr
        (by rw [show -4 * π * y = -(4 * π * y) by ring, neg_nonpos]; positivity)
      have hu0 : 0 ≤ Real.exp (-4 * π * x) := (Real.exp_pos _).le
      have hv0 : 0 ≤ Real.exp (-4 * π * y) := (Real.exp_pos _).le
      have huv : Real.exp (-4 * π * x) - Real.exp (-4 * π * y) ≤ 4 * π * (y - x) := by
        have h1 := Real.add_one_le_exp (-4 * π * (y - x))
        have hexp_v : Real.exp (-4 * π * y) = Real.exp (-4 * π * x) * Real.exp (-4 * π * (y - x)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hneg4 : -4 * π * (y - x) ≤ 0 := by linarith
        have hexp_le1 : Real.exp (-4 * π * (y - x)) ≤ 1 := Real.exp_le_one_iff.mpr hneg4
        rw [hexp_v]
        calc Real.exp (-4 * π * x) - Real.exp (-4 * π * x) * Real.exp (-4 * π * (y - x))
            = Real.exp (-4 * π * x) * (1 - Real.exp (-4 * π * (y - x))) := by ring
          _ ≤ 1 * (4 * π * (y - x)) := mul_le_mul hu1 (by linarith) (by linarith) zero_le_one
          _ = 4 * π * (y - x) := one_mul _
      have hv_le_u : Real.exp (-4 * π * y) ≤ Real.exp (-4 * π * x) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [show (1 - Real.exp (-4 * π * x)) ^ 2 - (1 - Real.exp (-4 * π * y)) ^ 2 =
        -((2 - Real.exp (-4 * π * x) - Real.exp (-4 * π * y)) *
          (Real.exp (-4 * π * x) - Real.exp (-4 * π * y))) by ring, abs_neg, abs_mul]
      have h2uv : |2 - Real.exp (-4 * π * x) - Real.exp (-4 * π * y)| ≤ 2 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have huv0 : 0 ≤ Real.exp (-4 * π * x) - Real.exp (-4 * π * y) := sub_nonneg.mpr hv_le_u
      calc |2 - Real.exp (-4 * π * x) - Real.exp (-4 * π * y)| *
            |Real.exp (-4 * π * x) - Real.exp (-4 * π * y)|
          ≤ 2 * (4 * π * (y - x)) := by
            rw [abs_of_nonneg huv0]; exact mul_le_mul h2uv huv huv0 zero_le_two
        _ = 8 * π * (y - x) := by ring
    have hrb := ratio_diff_bound hp0 hpy_lo hax hay hnull_diff
    have hKn_bd : 4 * Cv / p0 ≤ 2 * K_n := by
      dsimp [K_n]
      rw [show 2 * (2 * (Cv + 1) / p0) = (4 * Cv + 4) / p0 by ring]
      exact div_le_div_of_nonneg_right (by linarith) hp0.le
    calc |px / py - 1| ≤ (2 * (Cv / c') + 8 * π * (y - x)) / (p0 / 2) := hrb
      _ ≤ (2 * (Cv / c') + 8 * π * (Z / c')) / (p0 / 2) := by gcongr
      _ = (4 * Cv / p0 + (16 * π / p0) * Z) / c' := by field_simp; ring
      _ ≤ (2 * K_n + L_n * Z) / c' := by dsimp [L_n]; gcongr
  have hsqrt_diff : |√(x / y) - 1| ≤ (Z / x₀) / c' := by
    have hxy_le1 : x ≤ y := by dsimp [y]; exact le_add_of_nonneg_right (div_nonneg hz.1 hc0.le)
    have h1 : √(x / y) ≤ 1 := Real.sqrt_le_one.mpr (div_le_one_of_le₀ hxy_le1 hy_pos.le)
    rw [abs_of_nonpos (sub_nonpos.mpr h1), neg_sub]
    have hsq : x / y ≤ √(x / y) := by
      calc x / y = √(x / y) * √(x / y) :=
            (Real.mul_self_sqrt (div_nonneg hx_pos.le hy_pos.le)).symm
        _ ≤ 1 * √(x / y) := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ = √(x / y) := one_mul _
    have hsq1 : 1 - √(x / y) ≤ 1 - x / y := by linarith
    rw [show 1 - x / y = (y - x) / y by field_simp] at hsq1
    calc 1 - √(x / y) ≤ (y - x) / y := hsq1
      _ ≤ (Z / c') / x₀ := div_le_div₀ (by positivity) hxy_le hx₀ hy_lo
      _ = (Z / x₀) / c' := by ring
  have hexp_z : Real.exp (-2 * π * z / 3) ≤ 1 := Real.exp_le_one_iff.mpr
    (by rw [show -2 * π * z / 3 = -(2 * π * z / 3) by ring, neg_nonpos]
        exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi.le) hz.1) (by norm_num))
  have hprod_close : |(px / py) * √(x / y) - 1| ≤ C_n / c' := by
    rw [show (px / py) * √(x / y) - 1 = (px / py - 1) * √(x / y) + (√(x / y) - 1) by ring]
    have hsq_le1 : |√(x / y)| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr (div_le_one_of_le₀ (by dsimp [y]; exact le_add_of_nonneg_right (div_nonneg hz.1 hc0.le)) hy_pos.le)
    calc |(px / py - 1) * √(x / y) + (√(x / y) - 1)|
        ≤ |(px / py - 1) * √(x / y)| + |√(x / y) - 1| := abs_add_le _ _
      _ = |px / py - 1| * |√(x / y)| + |√(x / y) - 1| := by rw [abs_mul]
      _ ≤ ((2 * K_n + L_n * Z) / c') * 1 + (Z / x₀) / c' := by gcongr
      _ = ((2 * K_n + L_n * Z) + 1 / x₀ * Z) / c' := by ring
      _ ≤ C_n / c' := by
          dsimp [C_n]; gcongr; linarith [show 0 ≤ (2 * K_n + L_n * Z) + 1 / x₀ * Z by positivity]
  rw [hfull_eq, show (px / py) * √(x / y) * Real.exp (-2 * π * z / 3) - Real.exp (-2 * π * z / 3) =
      ((px / py) * √(x / y) - 1) * Real.exp (-2 * π * z / 3) by ring, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc |(px / py) * √(x / y) - 1| * Real.exp (-2 * π * z / 3)
      ≤ (C_n / c') * 1 := mul_le_mul hprod_close hexp_z (Real.exp_pos _).le (by positivity)
    _ = C_n / c' := mul_one _
    _ ≤ ε := by
        have h1 : C_n / ε + 1 ≤ c' := (le_max_right _ _).trans hc'
        have h2 : C_n ≤ c' * ε := (div_le_iff₀ hε).mp (by linarith)
        exact (div_le_iff₀ hc0).mpr (by linarith)

lemma virasoro_w5_cardy_ratio_tendsto {x₀ X : ℝ} (_hx₀ : 0 < x₀) (_hX : x₀ ≤ X) :
    ∀ δ : ℝ, 0 < δ → ∃ ρ > 0, ∀ᶠ c' in atTop, ∀ y : ℝ, |y - xiStar| ≤ ρ →
      |qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) /
          kernelK 5 (c' / 12) (c' * y ^ 2 / 3) - 1| ≤ δ := by
  intro δ hδ
  set q5 := qProb spinMomentW5Prob
  have hq5_eq : q5 = (2 * xiStar) ^ 4 / (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
    dsimp [q5]; unfold qProb spinMomentW5Prob FixedWeightProblem.nullPoly; simp
  set f : ℝ → ℝ := fun y => q5 * ((1 - Real.exp (-4 * π * y)) ^ 2 / (2 * y) ^ 4)
  have hf_cont : ContinuousAt f xiStar := by
    have h2 : 2 * xiStar ≠ 0 := by have := xiStar_pos; positivity
    dsimp [f]; fun_prop (disch := positivity)
  have hf_val : f xiStar = 1 := by
    dsimp [f]; rw [hq5_eq]
    have h1 : 1 - Real.exp (-4 * π * xiStar) ≠ 0 := by
      have : Real.exp (-4 * π * xiStar) < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; have := xiStar_pos; nlinarith)
      linarith
    have h2 : (2 * xiStar) ^ 4 ≠ 0 := by have := xiStar_pos; positivity
    have hexp_eq : Real.exp (-(4 * π * xiStar)) = Real.exp (-4 * π * xiStar) := by congr 1; ring
    have h1' : 1 - Real.exp (-(4 * π * xiStar)) ≠ 0 := by rwa [hexp_eq]
    rw [← hexp_eq]
    calc (2 * xiStar) ^ 4 / (1 - Real.exp (-(4 * π * xiStar))) ^ 2 *
          ((1 - Real.exp (-(4 * π * xiStar))) ^ 2 / (2 * xiStar) ^ 4)
        = ((2 * xiStar) ^ 4 / (2 * xiStar) ^ 4) *
            ((1 - Real.exp (-(4 * π * xiStar))) ^ 2 / (1 - Real.exp (-(4 * π * xiStar))) ^ 2) := by
          ring
      _ = 1 * 1 := by rw [div_self h2, div_self (pow_ne_zero 2 h1')]
      _ = 1 := mul_one 1
  obtain ⟨ρ₀, hρ₀, hρ_cont⟩ := Metric.continuousAt_iff.mp hf_cont (δ / 2) (half_pos hδ)
  set ρ := min (ρ₀ / 2) (min (xiStar / 2) 1)
  have hρ : 0 < ρ := by have := xiStar_pos; positivity
  obtain ⟨C, hC0, hKdiv⟩ := kernelK5_div_virasoro_bound (half_pos xiStar_pos)
    (by linarith [xiStar_pos] : xiStar / 2 ≤ xiStar + 1)
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hKdiv, eventually_ge_atTop (max 1 (2 * C / δ + 1))] with c' hc' hcd y hy
  have hc0 : 0 < c' := by linarith [le_max_left (1 : ℝ) (2 * C / δ + 1)]
  have hy_mem : y ∈ Icc (xiStar / 2) (xiStar + 1) := by
    have h1 : |y - xiStar| ≤ xiStar / 2 := hy.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : |y - xiStar| ≤ 1 := hy.trans ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h2).2]⟩
  have h1 := hc' y hy_mem
  have h2 : dist (f y) (f xiStar) < δ / 2 :=
    hρ_cont (by rw [Real.dist_eq]; exact lt_of_le_of_lt (hy.trans (min_le_left _ _)) (half_lt_self hρ₀))
  rw [hf_val, Real.dist_eq] at h2
  have h3 : C / c' ≤ δ / 2 := by
    have hcd' : 2 * C / δ ≤ c' := by linarith [le_max_right (1 : ℝ) (2 * C / δ + 1)]
    exact (div_le_iff₀ hc0).mpr (by have := (div_le_iff₀ hδ).mp hcd'; linarith)
  calc |q5 * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) / kernelK 5 (c' / 12) (c' * y ^ 2 / 3) - 1|
      ≤ |q5 * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) / kernelK 5 (c' / 12) (c' * y ^ 2 / 3) - f y| +
          |f y - 1| := abs_sub_le _ _ _
    _ ≤ C / c' + δ / 2 := add_le_add h1 h2.le
    _ ≤ δ := by linarith

lemma continuousOn_sigWinW (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ContinuousOn (sigWinW N η σs) (Icc (-R) R) := by
  set d := (rpParams 0).bumpData
  have hunif : TendstoUniformlyOn
      (fun c' u => psiScale virasoroProblem c' *
        psiAiry virasoroProblem c' (bumpG virasoroProblem d N η σs c') u)
      (sigWinW N η σs) atTop (Icc (-R) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [bump_psi_uniform virasoroProblem d N hN hη0 hη1 σs hR (half_pos hε)] with c' hc' u hu
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hc' u hu) (half_lt_self hε)
  refine hunif.continuousOn (Filter.Eventually.frequently ?_)
  filter_upwards [bumpG_good virasoroProblem d N hN hη0.le hη1 σs] with c' ⟨hc', htest, _⟩
  exact (continuous_const.mul (continuous_psiAiry hc' htest.cont)).continuousOn

lemma bAiry_eq_of_Icc {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ c' in atTop, ∀ u ∈ Icc (-R) R,
      bAiry c' u = xiStar - u * slopeAiry c' ∧
        xiStar / 2 ≤ bAiry c' u ∧ bAiry c' u ≤ xiStar + 1 / 2 := by
  have hslope : Tendsto slopeAiry atTop (nhds 0) := by
    have heq : slopeAiry = fun c => c ^ (-(2 / 3 : ℝ)) / betaTip := by
      ext c; unfold slopeAiry epsAiry; rfl
    rw [heq]
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).div_const betaTip
  set M := min (xiStar / 2) (1 / 2) / (R + 1)
  have hM : 0 < M := by have := xiStar_pos; positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ), hslope.eventually_le_const hM] with c' hc' hsl u hu
  have hsl0 : 0 ≤ slopeAiry c' := (slopeAiry_pos hc').le
  have hR_sl : R * slopeAiry c' ≤ min (xiStar / 2) (1 / 2) := by
    calc R * slopeAiry c' ≤ R * M := mul_le_mul_of_nonneg_left hsl hR
      _ ≤ (R + 1) * (min (xiStar / 2) (1 / 2) / (R + 1)) := by gcongr; linarith
      _ = min (xiStar / 2) (1 / 2) := by field_simp
  have hu_abs : |u * slopeAiry c'| ≤ min (xiStar / 2) (1 / 2) := by
    rw [abs_mul, abs_of_nonneg hsl0]
    exact (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hu.1, hu.2⟩) hsl0).trans hR_sl
  have hpos_x : xiStar / 2 ≤ xiStar - u * slopeAiry c' := by
    linarith [(abs_le.mp hu_abs).2, min_le_left (xiStar / 2) (1 / 2)]
  have hhi_x : xiStar - u * slopeAiry c' ≤ xiStar + 1 / 2 := by
    linarith [(abs_le.mp hu_abs).1, min_le_right (xiStar / 2) (1 / 2)]
  have hu_lt : u < uEnd c' :=
    (lt_uEnd_iff hc' u).mpr (lt_of_lt_of_le (half_pos xiStar_pos) hpos_x)
  have hb := bAiry_eq_of_lt hc' hu_lt
  exact ⟨hb, by rw [hb]; exact hpos_x, by rw [hb]; exact hhi_x⟩

lemma uAiry_bAiry_eq {c' u : ℝ} (hc' : 0 < c') (hx : 0 < bAiry c' u)
    (hb : bAiry c' u = xiStar - u * slopeAiry c') :
    uAiry c' (c' * (bAiry c' u) ^ 2 / 3) = u := by
  rw [hb]
  have hpos : 0 ≤ xiStar - u * slopeAiry c' := by rw [← hb]; exact hx.le
  unfold uAiry
  rw [show 3 * (c' * (xiStar - u * slopeAiry c') ^ 2 / 3) / c' =
    (xiStar - u * slopeAiry c') ^ 2 by field_simp, Real.sqrt_sq hpos]
  unfold slopeAiry epsAiry
  have hcp : c' ^ (-(2 / 3 : ℝ)) * c' ^ ((2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hc']; norm_num
  have hbt0 : betaTip ≠ 0 := betaTip_pos.ne'
  calc -betaTip * (xiStar - u * (c' ^ (-(2 / 3 : ℝ)) / betaTip) - xiStar) * c' ^ ((2 : ℝ) / 3)
      = u * (c' ^ (-(2 / 3 : ℝ)) * c' ^ ((2 : ℝ) / 3)) := by field_simp; ring
    _ = u := by rw [hcp, mul_one]

end FormalResearch.ModularBootstrap.Spin
