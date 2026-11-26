module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import FormalResearch.Analysis.Scheffe

/-!
# Compact negative mass (`dsl:compact-mass`, `dual_spectrum_limit.tex`)

Let `λ` be a positive measure, finite on compact sets, on a topological space `Y`, and let
functions `f_j` (measurable, continuous on `K`) converge pointwise to `F`, uniformly on a compact set `K` outside which every `f_j`
is nonnegative, with `∫ |f_j| dλ = 1` and `∫ f_j dλ ≤ 0`.  Then `F ∈ L¹(λ)`, `∫ |F| ≤ 1`,
`∫ F ≤ 0` and `F ≠ 0`; and if also `∫ F ≥ 0` then `∫ F = 0`, `∫ |F| = 1` and `∫ |f_j - F| → 0`.

(The paper assumes local uniform convergence on a closed subset of Euclidean space; local uniform
convergence gives pointwise convergence and uniform convergence on the compact `K`, which is all that
is used.)
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Duality

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Compact negative mass** (`dsl:compact-mass`). -/
theorem compact_negative_mass {μ : Measure Y} {f : ℕ → Y → ℝ} {F : Y → ℝ} {K : Set Y}
    (hK : IsCompact K) [IsFiniteMeasureOnCompacts μ] (hfm : ∀ j, Measurable (f j))
    (hfc : ∀ j, ContinuousOn (f j) K)
    (hfi : ∀ j, Integrable (f j) μ) (hnorm : ∀ j, ∫ y, |f j y| ∂μ = 1)
    (hint : ∀ j, ∫ y, f j y ∂μ ≤ 0) (hneg : ∀ j, ∀ y, y ∉ K → 0 ≤ f j y)
    (hpt : ∀ y, Tendsto (fun j => f j y) atTop (𝓝 (F y)))
    (hunif : TendstoUniformlyOn f F atTop K) :
    Integrable F μ ∧ ∫ y, |F y| ∂μ ≤ 1 ∧ ∫ y, F y ∂μ ≤ 0 ∧ (∃ y, F y < 0) ∧
      (0 ≤ ∫ y, F y ∂μ → ∫ y, F y ∂μ = 0 ∧ ∫ y, |F y| ∂μ = 1 ∧
        Tendsto (fun j => ∫ y, |f j y - F y| ∂μ) atTop (𝓝 0)) := by
  classical
  -- positive and negative parts
  set p : ℕ → Y → ℝ := fun j y => max (f j y) 0 with hp
  set n : ℕ → Y → ℝ := fun j y => max (-f j y) 0 with hn
  set P : Y → ℝ := fun y => max (F y) 0 with hP
  set N : Y → ℝ := fun y => max (-F y) 0 with hN
  have hFm : Measurable F :=
    measurable_of_tendsto_metrizable hfm (tendsto_pi_nhds.2 hpt)
  have hpn : ∀ j y, f j y = p j y - n j y := fun j y => by
    simp only [hp, hn]; rcases le_total (f j y) 0 with h | h <;> simp [h]
  have hpn_abs : ∀ j y, |f j y| = p j y + n j y := fun j y => by
    simp only [hp, hn]; rcases le_total (f j y) 0 with h | h <;> simp [h, abs_of_nonpos, abs_of_nonneg]
  have hPN : ∀ y, F y = P y - N y := fun y => by
    simp only [hP, hN]; rcases le_total (F y) 0 with h | h <;> simp [h]
  have hPN_abs : ∀ y, |F y| = P y + N y := fun y => by
    simp only [hP, hN]; rcases le_total (F y) 0 with h | h <;> simp [h, abs_of_nonpos, abs_of_nonneg]
  have hp_nn : ∀ j y, 0 ≤ p j y := fun j y => le_max_right _ _
  have hn_nn : ∀ j y, 0 ≤ n j y := fun j y => le_max_right _ _
  have hP_nn : ∀ y, 0 ≤ P y := fun y => le_max_right _ _
  have hN_nn : ∀ y, 0 ≤ N y := fun y => le_max_right _ _
  have hp_int : ∀ j, Integrable (p j) μ := fun j => (hfi j).pos_part
  have hn_int : ∀ j, Integrable (n j) μ := fun j => (hfi j).neg_part
  have hsum : ∀ j, ∫ y, p j y ∂μ + ∫ y, n j y ∂μ = 1 := fun j => by
    rw [← integral_add (hp_int j) (hn_int j), ← hnorm j]
    exact integral_congr_ae (Eventually.of_forall fun y => (hpn_abs j y).symm)
  have hdiff : ∀ j, ∫ y, p j y ∂μ - ∫ y, n j y ∂μ ≤ 0 := fun j => by
    rw [← integral_sub (hp_int j) (hn_int j)]
    exact (integral_congr_ae (Eventually.of_forall fun y => (hpn j y).symm)).trans_le (hint j)
  have hn_half : ∀ j, 1 / 2 ≤ ∫ y, n j y ∂μ := fun j => by linarith [hsum j, hdiff j]
  have hF_out : ∀ y, y ∉ K → 0 ≤ F y := fun y hy =>
    ge_of_tendsto (hpt y) (Eventually.of_forall fun j => hneg j y hy)
  have hN_out : ∀ y, y ∉ K → N y = 0 := fun y hy => by
    simp only [hN]; exact max_eq_right (by linarith [hF_out y hy])
  have hn_out : ∀ j y, y ∉ K → n j y = 0 := fun j y hy => by
    simp only [hn]; exact max_eq_right (by linarith [hneg j y hy])
  -- pointwise limits
  have hpt_p : ∀ y, Tendsto (fun j => p j y) atTop (𝓝 (P y)) := fun y =>
    (continuous_id.max continuous_const).continuousAt.tendsto.comp (hpt y)
  have hpt_n : ∀ y, Tendsto (fun j => n j y) atTop (𝓝 (N y)) := fun y =>
    ((continuous_neg.max continuous_const).continuousAt.tendsto.comp (hpt y))
  -- bound for the negative parts on `K`
  have hFc : ContinuousOn F K :=
    hunif.continuousOn (Eventually.of_forall hfc).frequently
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hFc
  have hfin : μ K < ∞ := hK.measure_lt_top
  have hbound_int : Integrable (K.indicator fun _ => B + 1) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hfin.ne)
  have hunif' : ∀ᶠ j in atTop, ∀ y ∈ K, |f j y - F y| < 1 :=
    (Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos).mono fun j hj y hy => by
      rw [← Real.dist_eq, dist_comm]; exact hj y hy
  have hnN : Tendsto (fun j => ∫ y, n j y ∂μ) atTop (𝓝 (∫ y, N y ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ => B + 1)
      (Eventually.of_forall fun j => (hn_int j).aestronglyMeasurable) ?_ hbound_int
      (Eventually.of_forall fun y => hpt_n y)
    filter_upwards [hunif'] with j hj
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_of_nonneg (hn_nn j y)]
      have h1 := hj y hy
      have h2 := hB y hy
      rw [Real.norm_eq_abs] at h2
      have h3 : n j y ≤ |f j y| := by
        simp only [hn]; exact max_le (neg_le_abs _) (abs_nonneg _)
      have := abs_sub_abs_le_abs_sub (f j y) (F y)
      linarith [abs_nonneg (F y)]
    · rw [indicator_of_notMem hy, hn_out j y hy]; simp
  have hN_int : Integrable N μ := by
    refine hbound_int.mono' (hFm.neg.max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_of_nonneg (hN_nn y)]
      have h2 := hB y hy
      rw [Real.norm_eq_abs] at h2
      have h3 : N y ≤ |F y| := by
        simp only [hN]; exact max_le (neg_le_abs _) (abs_nonneg _)
      linarith
    · rw [indicator_of_notMem hy, hN_out y hy]; simp
  set ℓ := ∫ y, N y ∂μ with hℓ
  have hℓ_half : 1 / 2 ≤ ℓ := ge_of_tendsto hnN (Eventually.of_forall hn_half)
  have hℓ_le : ℓ ≤ 1 := le_of_tendsto hnN (Eventually.of_forall fun j => by
    linarith [hsum j, integral_nonneg (μ := μ) (f := p j) (hp_nn j)])
  -- limit of the positive masses
  have hpP : Tendsto (fun j => ∫ y, p j y ∂μ) atTop (𝓝 (1 - ℓ)) := by
    have : ∀ j, ∫ y, p j y ∂μ = 1 - ∫ y, n j y ∂μ := fun j => by linarith [hsum j]
    simp_rw [this]
    exact tendsto_const_nhds.sub hnN
  -- Fatou for the positive part
  have hP_meas : Measurable P := hFm.max measurable_const
  have hfatou : ∫⁻ y, ENNReal.ofReal (P y) ∂μ ≤ ENNReal.ofReal (1 - ℓ) := by
    have hlim_p : Tendsto (fun j => ∫⁻ y, ENNReal.ofReal (p j y) ∂μ) atTop
        (𝓝 (ENNReal.ofReal (1 - ℓ))) := by
      have : ∀ j, ∫⁻ y, ENNReal.ofReal (p j y) ∂μ = ENNReal.ofReal (∫ y, p j y ∂μ) := fun j =>
        (ofReal_integral_eq_lintegral_ofReal (hp_int j) (Eventually.of_forall (hp_nn j))).symm
      simp_rw [this]
      exact (ENNReal.tendsto_ofReal hpP)
    calc ∫⁻ y, ENNReal.ofReal (P y) ∂μ
        = ∫⁻ y, liminf (fun j => ENNReal.ofReal (p j y)) atTop ∂μ := by
          refine lintegral_congr fun y => ?_
          exact ((ENNReal.tendsto_ofReal (hpt_p y)).liminf_eq).symm
      _ ≤ liminf (fun j => ∫⁻ y, ENNReal.ofReal (p j y) ∂μ) atTop :=
          lintegral_liminf_le fun j =>
            ENNReal.measurable_ofReal.comp ((hfm j).max measurable_const)
      _ = ENNReal.ofReal (1 - ℓ) := hlim_p.liminf_eq
  have hP_int : Integrable P μ := by
    refine ⟨hP_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hP_nn)]
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hP_le : ∫ y, P y ∂μ ≤ 1 - ℓ := by
    have := (ofReal_integral_eq_lintegral_ofReal hP_int (Eventually.of_forall hP_nn)).trans_le hfatou
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 this
  have hFint : Integrable F μ := by
    refine (hP_int.sub hN_int).congr (Eventually.of_forall fun y => ?_)
    simp [hPN y]
  have habs : ∫ y, |F y| ∂μ = ∫ y, P y ∂μ + ℓ := by
    rw [← integral_add hP_int hN_int]
    exact integral_congr_ae (Eventually.of_forall hPN_abs)
  have hFval : ∫ y, F y ∂μ = ∫ y, P y ∂μ - ℓ := by
    rw [← integral_sub hP_int hN_int]
    exact integral_congr_ae (Eventually.of_forall hPN)
  refine ⟨hFint, by rw [habs]; linarith, by rw [hFval]; linarith, ?_, fun h0 => ?_⟩
  · by_contra hcon
    push Not at hcon
    have : ℓ = 0 := by
      have hz : N = fun _ => 0 := funext fun y => by
        simp only [hN]; exact max_eq_right (by linarith [hcon y])
      simp [hℓ, hz]
    linarith
  · rw [hFval] at h0
    have hPval : ∫ y, P y ∂μ = 1 / 2 := by linarith
    have hℓval : ℓ = 1 / 2 := by linarith
    refine ⟨by rw [hFval]; linarith, by rw [habs]; linarith, ?_⟩
    -- Scheffé for the positive and negative parts
    have hpS : Tendsto (fun j => ∫ y, ‖p j y - P y‖ ∂μ) atTop (𝓝 0) :=
      FormalResearch.Analysis.tendsto_integral_norm_sub_of_tendsto_ae
        (Eventually.of_forall hp_int) hP_int (Eventually.of_forall hpt_p) (by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hp_nn _ _), abs_of_nonneg (hP_nn _)]
          rw [hPval]
          have h12 : (1 : ℝ) - ℓ = 1 / 2 := by linarith
          rwa [h12] at hpP)
    have hnS : Tendsto (fun j => ∫ y, ‖n j y - N y‖ ∂μ) atTop (𝓝 0) :=
      FormalResearch.Analysis.tendsto_integral_norm_sub_of_tendsto_ae
        (Eventually.of_forall hn_int) hN_int (Eventually.of_forall hpt_n) (by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hn_nn _ _), abs_of_nonneg (hN_nn _)]
          exact hnN)
    refine squeeze_zero (fun j => integral_nonneg fun y => abs_nonneg _)
      (g := fun j => ∫ y, ‖p j y - P y‖ ∂μ + ∫ y, ‖n j y - N y‖ ∂μ) (fun j => ?_)
      (by simpa using hpS.add hnS)
    have hI1 : Integrable (fun y => ‖p j y - P y‖) μ := ((hp_int j).sub hP_int).norm
    have hI2 : Integrable (fun y => ‖n j y - N y‖) μ := ((hn_int j).sub hN_int).norm
    rw [← integral_add hI1 hI2]
    refine integral_mono ((hfi j).sub hFint).abs (hI1.add hI2) fun y => ?_
    simp only [Real.norm_eq_abs]
    have e : f j y - F y = (p j y - P y) - (n j y - N y) := by rw [hpn j y, hPN y]; ring
    rw [e]
    exact abs_sub _ _

/-- info: 'FormalResearch.ModularBootstrap.Duality.compact_negative_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.compact_negative_mass

end FormalResearch.ModularBootstrap.Duality
