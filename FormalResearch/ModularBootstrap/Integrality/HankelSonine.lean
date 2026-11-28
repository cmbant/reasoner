module

public import FormalResearch.ModularBootstrap.Integrality.HankelFourier
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# Hankel–Sonine Band Compression and Inverse Bound (`int:sonine`)

Proves the Hilbert-space contraction and Neumann-series inverse estimate for the compressed Hankel
transform `P_B U_w P_B` on `L²((0, B], t^{w-1} dt)` (`1 ≤ w : ℕ`, `B > 0`):
* `kerTransform_band_sq_le`: translates `fourier_concentration_radial` to the `L²(hankelBandMeasure w B)`
  contraction `‖P_B U_w φ‖₂² ≤ (1 - ε_B) ‖φ‖₂²`;
* `hankelBandOp`: extends `P_B U_w P_B` to `Lp ℝ 2 (hankelBandMeasure w B) →L[ℝ] Lp ℝ 2 (hankelBandMeasure w B)`
  with `‖hankelBandOp hw hB‖ ≤ √(1 - ε_B)`;
* `hankelSonine_inv`: constructs the inverse `(I + P_B U_w P_B)⁻¹` via `Units.oneSub` with
  operator norm `≤ max 4 (2048 * π ^ 2 * B ^ 2 * exp (16 * π * B))`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set BoundedContinuousFunction
open scoped FourierTransform ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap.Crossing

/-! ### Section 1: Band `L²` contraction on compactly supported continuous functions -/

/-- The Sonine spectral gap parameter `ε_B = min (1/2) (1 / (1024 π² B² exp(16π B)))`. -/
noncomputable def sonineGap (B : ℝ) : ℝ :=
  min (1 / 2 : ℝ) (1 / (1024 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B)))

lemma sonineGap_pos {B : ℝ} (hB : 0 < B) : 0 < sonineGap B := by
  unfold sonineGap
  exact lt_min (by norm_num) (by positivity)

lemma sonineGap_le_half (B : ℝ) : sonineGap B ≤ 1 / 2 := min_le_left _ _

lemma kerTransform_band_sq_le {w : ℕ} (hw : 1 ≤ w) {B : ℝ} (hB : 0 < B)
    {φ : ℝ → ℝ} (hφ_cont : Continuous φ) (hφ_supp : ∀ t, t ∉ Ioc 0 B → φ t = 0) :
    ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (kerTransform (hankelMeasure w) (hankelKernel w) φ t) ^ 2 ≤
      (1 - sonineGap B) * ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (φ t) ^ 2 := by
  let F : EuclideanSpace ℝ (Fin (2 * w)) → ℂ := radialLift w φ
  have hF_supp : ∀ x : EuclideanSpace ℝ (Fin (2 * w)), Real.sqrt (2 * B) < ‖x‖ → F x = 0 := by
    intro x hx
    have hgt : B < ‖x‖ ^ 2 / 2 := by
      have hsq : 2 * B < ‖x‖ ^ 2 := by
        calc 2 * B = (Real.sqrt (2 * B)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
          _ < ‖x‖ ^ 2 := by gcongr
      linarith
    simp [F, radialLift, hφ_supp _ fun hm => not_le.mpr hgt hm.2]
  have hF_cont : Continuous F := Complex.continuous_ofReal.comp (hφ_cont.comp (by fun_prop))
  have hF_cs : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact
      (ProperSpace.isCompact_closedBall 0 (Real.sqrt (2 * B))) fun x hx => ?_
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! hlt
    exact hx (hF_supp x hlt)
  have hF_mem : MemLp F 2 volume :=
    hF_cont.memLp_of_hasCompactSupport hF_cs
  have hconc := fourier_concentration_radial hw hB hF_cont.aestronglyMeasurable hF_mem hF_supp
  let Uφ : ℝ → ℝ := kerTransform (hankelMeasure w) (hankelKernel w) φ
  have h_noatom : volume ({(0 : EuclideanSpace ℝ (Fin (2 * w)))} : Set _) = 0 := by
    have : Nonempty (Fin (2 * w)) := ⟨⟨0, by omega⟩⟩
    exact measure_singleton 0
  have h_ae_zero : ∀ᵐ ξ : EuclideanSpace ℝ (Fin (2 * w)) ∂volume, ξ ≠ 0 :=
    ae_iff.mpr (by simpa [ne_eq, not_not] using h_noatom)
  have h_lhs : ∫ ξ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * w))) (Real.sqrt (2 * B)),
      ‖𝓕 F ξ‖ ^ 2 =
      ((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) * ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (Uφ t) ^ 2 := by
    have h_ae_ball : (fun ξ : EuclideanSpace ℝ (Fin (2 * w)) =>
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * w))) (Real.sqrt (2 * B))).indicator
          (fun ξ => ‖𝓕 F ξ‖ ^ 2) ξ) =ᵐ[volume]
        fun ξ => (Ioc (0 : ℝ) B).indicator (fun t => (Uφ t) ^ 2) (‖ξ‖ ^ 2 / 2) := by
      filter_upwards [h_ae_zero] with ξ hξ
      have hpos : 0 < ‖ξ‖ ^ 2 / 2 := div_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hξ)) two_pos
      have hiff : ξ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * w))) (Real.sqrt (2 * B)) ↔
          ‖ξ‖ ^ 2 / 2 ∈ Ioc (0 : ℝ) B := by
        rw [Metric.mem_closedBall, dist_zero_right, mem_Ioc]
        constructor
        · intro hn
          refine ⟨hpos, ?_⟩
          have hsq : ‖ξ‖ ^ 2 ≤ (Real.sqrt (2 * B)) ^ 2 := by gcongr
          rw [Real.sq_sqrt (by positivity)] at hsq
          linarith
        · intro ⟨_, hle⟩
          have hsq : ‖ξ‖ ^ 2 ≤ 2 * B := by linarith
          calc ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
            _ ≤ Real.sqrt (2 * B) := Real.sqrt_le_sqrt hsq
      by_cases hmem : ξ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * w))) (Real.sqrt (2 * B))
      · have hm2 : ‖ξ‖ ^ 2 / 2 ∈ Ioc (0 : ℝ) B := hiff.mp hmem
        simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hm2]
        rw [fourier_radialLift_eq_hankelTransform hw hB hφ_cont hφ_supp hξ,
          Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · have hm2 : ‖ξ‖ ^ 2 / 2 ∉ Ioc (0 : ℝ) B := fun hm => hmem (hiff.mpr hm)
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hm2]
    rw [← integral_indicator Metric.isClosed_closedBall.measurableSet, integral_congr_ae h_ae_ball,
      integral_radialLiftReal hw (fun t => (Ioc (0 : ℝ) B).indicator (fun t => (Uφ t) ^ 2) t)]
    congr 1
    rw [← integral_indicator (measurableSet_Ioi (a := (0 : ℝ))),
      ← integral_indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := B))]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases htm : t ∈ Ioc 0 B
    · simp [htm, htm.1]
    · simp [htm]
  have h_rhs : ∫ x : EuclideanSpace ℝ (Fin (2 * w)), ‖F x‖ ^ 2 =
      ((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) * ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (φ t) ^ 2 := by
    have heq_f : (fun x : EuclideanSpace ℝ (Fin (2 * w)) => ‖F x‖ ^ 2) =
        fun x => (φ (‖x‖ ^ 2 / 2)) ^ 2 := by
      ext x
      simp [F, radialLift, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [heq_f, integral_radialLiftReal hw (fun t => (φ t) ^ 2)]
    congr 1
    rw [← integral_indicator (measurableSet_Ioi (a := (0 : ℝ))),
      ← integral_indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := B))]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases htm : t ∈ Ioc 0 B
    · simp [htm, htm.1]
    · simp [htm, hφ_supp t htm]
  rw [h_lhs, h_rhs] at hconc
  have hcw : (0 : ℝ) < (2 * π) ^ w / (Nat.factorial (w - 1) : ℝ) := by positivity
  have hle : ((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
        ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (Uφ t) ^ 2 ≤
      ((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
        ((1 - sonineGap B) * ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (φ t) ^ 2) := by
    simpa [sonineGap] using hconc.trans_eq (by ring)
  exact le_of_mul_le_mul_left hle hcw

/-! ### Section 2: `hankelBandOp` on `L²((0, B], dm_w)` and its operator norm -/

/-- Raw integral operator `f ↦ ∫ s, hankelKernel w t s * f s ∂(hankelBandMeasure w B)`
before taking its equivalence class in `L²`. -/
noncomputable def rawHankelBand (w : ℕ) (B : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s, hankelKernel w t s * f s ∂(hankelBandMeasure w B)

lemma continuous_rawHankelBand {w : ℕ} {B : ℝ} {f : Lp ℝ 2 (hankelBandMeasure w B)} :
    Continuous (rawHankelBand w B f) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hf1 : Integrable (fun s => (f : ℝ → ℝ) s) (hankelBandMeasure w B) :=
    (Lp.memLp f).integrable one_le_two
  have hcompact : IsCompact ((Icc (t₀ - 1) (t₀ + 1)) ×ˢ (Icc (0 : ℝ) (max B 0))) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : ((Icc (t₀ - 1) (t₀ + 1)) ×ˢ (Icc (0 : ℝ) (max B 0))).Nonempty :=
    ⟨(t₀, 0), ⟨by linarith, by linarith⟩, ⟨le_rfl, le_max_right _ _⟩⟩
  obtain ⟨p₀, _, hp₀⟩ := hcompact.exists_isMaxOn hne
    (continuous_abs.comp (continuous_hankelKernel w)).continuousOn
  set M : ℝ := |hankelKernel w p₀.1 p₀.2|
  refine tendsto_integral_filter_of_dominated_convergence (fun s => M * ‖(f : ℝ → ℝ) s‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun t => ?_
    exact ((continuous_hankelKernel w).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · filter_upwards [Icc_mem_nhds (by linarith : t₀ - 1 < t₀) (by linarith : t₀ < t₀ + 1)] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hmem : (t, s) ∈ (Icc (t₀ - 1) (t₀ + 1)) ×ˢ (Icc (0 : ℝ) (max B 0)) :=
      ⟨ht, ⟨hs.1.le, hs.2.trans (le_max_left _ _)⟩⟩
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hp₀ hmem) (norm_nonneg _)
  · exact hf1.norm.const_mul M
  · refine Eventually.of_forall fun s => ?_
    exact ((continuous_hankelKernel w).comp
      (continuous_id.prodMk continuous_const)).continuousAt.mul continuousAt_const

lemma lp_norm_sq_hankelBandMeasure {w : ℕ} {B : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (hankelBandMeasure w B)) :
    ‖hf.toLp f‖ ^ 2 = ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (f t) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have heq : (fun t => inner ℝ ((hf.toLp f : ℝ → ℝ) t) ((hf.toLp f : ℝ → ℝ) t)) =ᵐ[hankelBandMeasure w B]
      fun t => (f t) ^ 2 := by
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [ht, RCLike.inner_apply, conj_trivial, sq]
  rw [integral_congr_ae heq, integral_hankelBandMeasure_eq]

lemma rawHankelBand_sq_le {w : ℕ} (_hw : 1 ≤ w) {B : ℝ} (hB : 0 < B)
    (f : Lp ℝ 2 (hankelBandMeasure w B)) {t : ℝ} (ht : 0 < t) :
    (rawHankelBand w B f t) ^ 2 ≤ (2 * π) ^ 2 * B * t ^ (-((w - 1 : ℕ) : ℝ)) * ‖f‖ ^ 2 := by
  have hk_bound : ∀ s ∈ Ioc (0 : ℝ) B,
      s ^ (w - 1) * (hankelKernel w t s) ^ 2 ≤ (2 * π) ^ 2 * t ^ (-((w - 1 : ℕ) : ℝ)) := by
    intro s hs
    have hk := hankelKernel_abs_le w ht hs.1
    have hsq : (hankelKernel w t s) ^ 2 ≤
        (2 * π) ^ 2 * (1 / Real.sqrt (t * s)) ^ (2 * (w - 1)) := by
      calc (hankelKernel w t s) ^ 2 = |hankelKernel w t s| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1)) ^ 2 := by gcongr
        _ = (2 * π) ^ 2 * (1 / Real.sqrt (t * s)) ^ (2 * (w - 1)) := by
            rw [mul_pow, ← pow_mul]; congr 2; ring
    have hpow_eq : s ^ (w - 1) * (1 / Real.sqrt (t * s)) ^ (2 * (w - 1)) =
        t ^ (-((w - 1 : ℕ) : ℝ)) := by
      have hts : (1 / Real.sqrt (t * s)) ^ (2 * (w - 1)) = (t * s) ^ (-((w - 1 : ℕ) : ℝ)) := by
        rw [one_div, inv_pow, Real.rpow_neg (mul_pos ht hs.1).le, pow_mul,
          Real.sq_sqrt (mul_pos ht hs.1).le, Real.rpow_natCast]
      rw [hts, Real.mul_rpow ht.le hs.1.le, Real.rpow_neg ht.le,
        Real.rpow_neg hs.1.le, Real.rpow_natCast, Real.rpow_natCast]
      have hs0 : s ^ (w - 1) ≠ 0 := (pow_pos hs.1 _).ne'
      field_simp [hs0]
    calc s ^ (w - 1) * (hankelKernel w t s) ^ 2
        ≤ s ^ (w - 1) * ((2 * π) ^ 2 * (1 / Real.sqrt (t * s)) ^ (2 * (w - 1))) :=
          mul_le_mul_of_nonneg_left hsq (pow_nonneg hs.1.le _)
      _ = (2 * π) ^ 2 * (s ^ (w - 1) * (1 / Real.sqrt (t * s)) ^ (2 * (w - 1))) := by ring
      _ = (2 * π) ^ 2 * t ^ (-((w - 1 : ℕ) : ℝ)) := by rw [hpow_eq]
  have hg_mem : MemLp (fun s => hankelKernel w t s) 2 (hankelBandMeasure w B) := by
    obtain ⟨s₀, _, hs₀⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr (le_max_right B 0)⟩
      ((continuous_abs.comp ((continuous_hankelKernel w).comp
        (continuous_const.prodMk continuous_id))).continuousOn : ContinuousOn _ (Icc 0 (max B 0)))
    refine MemLp.of_bound ((continuous_hankelKernel w).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable |hankelKernel w t s₀| ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hs₀ ⟨hs.1.le, hs.2.trans (le_max_left _ _)⟩
  let g : Lp ℝ 2 (hankelBandMeasure w B) := hg_mem.toLp _
  have hinner : rawHankelBand w B f t = inner ℝ g f := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg_mem.coeFn_toLp] with s hs
    rw [hs, real_inner_comm]
    rfl
  have hg_sq : ‖g‖ ^ 2 ≤ (2 * π) ^ 2 * B * t ^ (-((w - 1 : ℕ) : ℝ)) := by
    rw [lp_norm_sq_hankelBandMeasure hg_mem]
    have hconst_int : IntegrableOn (fun _ : ℝ => (2 * π) ^ 2 * t ^ (-((w - 1 : ℕ) : ℝ))) (Ioc 0 B) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have hker_int : IntegrableOn (fun s => s ^ (w - 1) * (hankelKernel w t s) ^ 2) (Ioc 0 B) := by
      refine hconst_int.mono' ((continuous_pow _).mul
        (((continuous_hankelKernel w).comp (continuous_const.prodMk continuous_id)).pow 2)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs.1.le _) (sq_nonneg _))]
      exact hk_bound s hs
    calc ∫ s in Ioc (0 : ℝ) B, s ^ (w - 1) * (hankelKernel w t s) ^ 2
        ≤ ∫ _s in Ioc (0 : ℝ) B, (2 * π) ^ 2 * t ^ (-((w - 1 : ℕ) : ℝ)) :=
          setIntegral_mono_on hker_int hconst_int measurableSet_Ioc hk_bound
      _ = volume.real (Ioc (0 : ℝ) B) • ((2 * π) ^ 2 * t ^ (-((w - 1 : ℕ) : ℝ))) :=
          setIntegral_const _
      _ = B * ((2 * π) ^ 2 * t ^ (-((w - 1 : ℕ) : ℝ))) := by
          rw [smul_eq_mul, Real.volume_real_Ioc_of_le hB.le, sub_zero]
      _ = (2 * π) ^ 2 * B * t ^ (-((w - 1 : ℕ) : ℝ)) := by ring
  have hcs := norm_inner_le_norm (𝕜 := ℝ) g f
  rw [hinner]
  calc (inner ℝ g f) ^ 2 = ‖inner ℝ g f‖ ^ 2 := (sq_abs _).symm
    _ ≤ (‖g‖ * ‖f‖) ^ 2 := by gcongr
    _ = ‖g‖ ^ 2 * ‖f‖ ^ 2 := by ring
    _ ≤ ((2 * π) ^ 2 * B * t ^ (-((w - 1 : ℕ) : ℝ))) * ‖f‖ ^ 2 := by gcongr

lemma rawHankelBand_memLp {w : ℕ} (hw : 1 ≤ w) {B : ℝ} (hB : 0 < B)
    (f : Lp ℝ 2 (hankelBandMeasure w B)) :
    MemLp (rawHankelBand w B f) 2 (hankelBandMeasure w B) := by
  refine (memLp_two_iff_integrable_sq continuous_rawHankelBand.aestronglyMeasurable).mpr ?_
  rw [integrable_hankelBandMeasure_iff]
  have hconst_int : IntegrableOn (fun _ : ℝ => (2 * π) ^ 2 * B * ‖f‖ ^ 2) (Ioc 0 B) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  refine hconst_int.mono' ((continuous_pow _).mul (continuous_rawHankelBand.pow 2)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (sq_nonneg _))]
  have hsq := rawHankelBand_sq_le hw hB f ht.1
  have hpow : t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ)) = 1 := by
    rw [Real.rpow_neg ht.1.le, Real.rpow_natCast, mul_inv_cancel₀ (pow_pos ht.1 _).ne']
  calc t ^ (w - 1) * (rawHankelBand w B f t) ^ 2
      ≤ t ^ (w - 1) * ((2 * π) ^ 2 * B * t ^ (-((w - 1 : ℕ) : ℝ)) * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (pow_nonneg ht.1.le _)
    _ = (2 * π) ^ 2 * B * ‖f‖ ^ 2 * (t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ))) := by ring
    _ = (2 * π) ^ 2 * B * ‖f‖ ^ 2 := by rw [hpow, mul_one]

/-- The bounded linear operator `P_B U_w P_B` on `L²(hankelBandMeasure w B)`. -/
noncomputable def hankelBandOp {w : ℕ} (hw : 1 ≤ w) {B : ℝ} (hB : 0 < B) :
    Lp ℝ 2 (hankelBandMeasure w B) →L[ℝ] Lp ℝ 2 (hankelBandMeasure w B) :=
  LinearMap.mkContinuous
    { toFun := fun f => (rawHankelBand_memLp hw hB f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add (rawHankelBand_memLp hw hB f) (rawHankelBand_memLp hw hB g)]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun t => ?_)
        unfold rawHankelBand
        have hf1 : Integrable (fun s => (f : ℝ → ℝ) s) (hankelBandMeasure w B) :=
          (Lp.memLp f).integrable one_le_two
        have hg1 : Integrable (fun s => (g : ℝ → ℝ) s) (hankelBandMeasure w B) :=
          (Lp.memLp g).integrable one_le_two
        have hk_bdd : ∀ t, ∃ M, ∀ᵐ s ∂(hankelBandMeasure w B), |hankelKernel w t s| ≤ M := fun t => by
          obtain ⟨s₀, _, hs₀⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr (le_max_right B 0)⟩
            ((continuous_abs.comp ((continuous_hankelKernel w).comp
              (continuous_const.prodMk continuous_id))).continuousOn : ContinuousOn _ (Icc 0 (max B 0)))
          refine ⟨|hankelKernel w t s₀|, ?_⟩
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hs₀ ⟨hs.1.le, hs.2.trans (le_max_left _ _)⟩
        obtain ⟨M, hM⟩ := hk_bdd t
        have hint_f : Integrable (fun s => hankelKernel w t s * (f : ℝ → ℝ) s) (hankelBandMeasure w B) := by
          refine (hf1.norm.const_mul M).mono'
            (((continuous_hankelKernel w).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
              (Lp.aestronglyMeasurable f)) ?_
          filter_upwards [hM] with s hs
          rw [norm_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
        have hint_g : Integrable (fun s => hankelKernel w t s * (g : ℝ → ℝ) s) (hankelBandMeasure w B) := by
          refine (hg1.norm.const_mul M).mono'
            (((continuous_hankelKernel w).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
              (Lp.aestronglyMeasurable g)) ?_
          filter_upwards [hM] with s hs
          rw [norm_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
        have heq_f : (fun s => hankelKernel w t s * ((f + g : Lp ℝ 2 (hankelBandMeasure w B)) : ℝ → ℝ) s) =ᵐ[hankelBandMeasure w B]
            fun s => hankelKernel w t s * (f : ℝ → ℝ) s + hankelKernel w t s * (g : ℝ → ℝ) s := by
          filter_upwards [Lp.coeFn_add f g] with s hs
          simp only [hs, Pi.add_apply, mul_add]
        rw [integral_congr_ae heq_f, integral_add hint_f hint_g]
        rfl
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (rawHankelBand_memLp hw hB f)]
        refine MemLp.toLp_congr _ _ (Eventually.of_forall fun t => ?_)
        unfold rawHankelBand
        have heq_c : (fun s => hankelKernel w t s * ((c • f : Lp ℝ 2 (hankelBandMeasure w B)) : ℝ → ℝ) s) =ᵐ[hankelBandMeasure w B]
            fun s => c * (hankelKernel w t s * (f : ℝ → ℝ) s) := by
          filter_upwards [Lp.coeFn_smul c f] with s hs
          simp only [hs, Pi.smul_apply, smul_eq_mul]
          ring
        rw [integral_congr_ae heq_c, integral_const_mul]
        rfl }
    (2 * π * B)
    fun f => by
      rw [← sq_le_sq₀ (norm_nonneg _) (by positivity)]
      change ‖(rawHankelBand_memLp hw hB f).toLp _‖ ^ 2 ≤ (2 * π * B * ‖f‖) ^ 2
      rw [lp_norm_sq_hankelBandMeasure (rawHankelBand_memLp hw hB f)]
      have hconst_int : IntegrableOn (fun _ : ℝ => (2 * π) ^ 2 * B * ‖f‖ ^ 2) (Ioc 0 B) :=
        integrableOn_const (hs := measure_Ioc_lt_top.ne)
      have hlhs_int : IntegrableOn (fun t => t ^ (w - 1) * (rawHankelBand w B f t) ^ 2) (Ioc 0 B) :=
        (integrable_hankelBandMeasure_iff _).mp
          ((rawHankelBand_memLp hw hB f).integrable_sq)
      calc ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (rawHankelBand w B f t) ^ 2
          ≤ ∫ _t in Ioc (0 : ℝ) B, (2 * π) ^ 2 * B * ‖f‖ ^ 2 := by
            refine setIntegral_mono_on hlhs_int hconst_int measurableSet_Ioc fun t ht => ?_
            have hsq := rawHankelBand_sq_le hw hB f ht.1
            have hpow : t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ)) = 1 := by
              rw [Real.rpow_neg ht.1.le, Real.rpow_natCast, mul_inv_cancel₀ (pow_pos ht.1 _).ne']
            calc t ^ (w - 1) * (rawHankelBand w B f t) ^ 2
                ≤ t ^ (w - 1) * ((2 * π) ^ 2 * B * t ^ (-((w - 1 : ℕ) : ℝ)) * ‖f‖ ^ 2) :=
                  mul_le_mul_of_nonneg_left hsq (pow_nonneg ht.1.le _)
              _ = (2 * π) ^ 2 * B * ‖f‖ ^ 2 * (t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ))) := by ring
              _ = (2 * π) ^ 2 * B * ‖f‖ ^ 2 := by rw [hpow, mul_one]
        _ = volume.real (Ioc (0 : ℝ) B) • ((2 * π) ^ 2 * B * ‖f‖ ^ 2) := setIntegral_const _
        _ = B * ((2 * π) ^ 2 * B * ‖f‖ ^ 2) := by
            rw [smul_eq_mul, Real.volume_real_Ioc_of_le hB.le, sub_zero]
        _ = (2 * π * B * ‖f‖) ^ 2 := by ring

lemma hankelBandOp_apply_ae {w : ℕ} (hw : 1 ≤ w) {B : ℝ} (hB : 0 < B)
    (f : Lp ℝ 2 (hankelBandMeasure w B)) :
    ∀ᵐ t ∂(hankelBandMeasure w B),
      (hankelBandOp hw hB f : ℝ → ℝ) t =
        ∫ s, hankelKernel w t s * (f : ℝ → ℝ) s ∂(hankelBandMeasure w B) :=
  (rawHankelBand_memLp hw hB f).coeFn_toLp

lemma hankelBandOp_norm_le {w : ℕ} (hw : 1 ≤ w) {B : ℝ} (hB : 0 < B) :
    ‖hankelBandOp hw hB‖ ≤ Real.sqrt (1 - sonineGap B) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun f => ?_
  have h_bcf : ∀ g : ℝ →ᵇ ℝ, ∀ (hg_mem : MemLp (g : ℝ → ℝ) 2 (hankelBandMeasure w B)),
      ‖hankelBandOp hw hB (hg_mem.toLp _)‖ ≤ Real.sqrt (1 - sonineGap B) * ‖hg_mem.toLp _‖ := by
    intro g hg_mem
    let N₀ : ℕ := Nat.ceil (4 / B) + 1
    let a : ℕ → ℝ := fun n => 1 / (2 * ((n + N₀ : ℕ) : ℝ))
    let b : ℕ → ℝ := fun n => 1 / ((n + N₀ : ℕ) : ℝ)
    let c : ℕ → ℝ := fun n => B - 1 / ((n + N₀ : ℕ) : ℝ)
    let d : ℕ → ℝ := fun n => B - 1 / (2 * ((n + N₀ : ℕ) : ℝ))
    let χ : ℕ → ℝ → ℝ := fun n s =>
      max 0 (min ((s - a n) / (b n - a n)) (min 1 ((d n - s) / (d n - c n))))
    have hχ_bounds : ∀ n s, 0 ≤ χ n s ∧ χ n s ≤ 1 := fun n s =>
      ⟨le_max_left _ _, max_le zero_le_one ((min_le_right _ _).trans (min_le_left _ _))⟩
    have hχ_cont : ∀ n, Continuous (χ n) := fun n => by
      unfold χ; fun_prop
    have h_ab : ∀ n, 0 < a n ∧ a n < b n ∧ b n < c n ∧ c n < d n ∧ d n < B := by
      intro n
      have hceil : 4 / B < (N₀ : ℝ) := by
        dsimp [N₀]
        have h1 : 4 / B ≤ (Nat.ceil (4 / B) : ℝ) := Nat.le_ceil _
        push_cast; linarith
      have hn : 4 / B < ((n + N₀ : ℕ) : ℝ) :=
        hceil.trans_le (by exact_mod_cast Nat.le_add_left N₀ n)
      have hpos : (0 : ℝ) < ((n + N₀ : ℕ) : ℝ) := lt_trans (by positivity) hn
      have h4B : 4 < B * ((n + N₀ : ℕ) : ℝ) := by
        have h1 : 4 / B * B < ((n + N₀ : ℕ) : ℝ) * B := mul_lt_mul_of_pos_right hn hB
        rw [div_mul_cancel₀ _ hB.ne'] at h1
        linarith
      have hinv4 : 4 * (1 / ((n + N₀ : ℕ) : ℝ)) < B := by
        rw [← mul_div_assoc, mul_one, div_lt_iff₀ hpos]
        linarith
      have hinv_half : 1 / (2 * ((n + N₀ : ℕ) : ℝ)) < 1 / ((n + N₀ : ℕ) : ℝ) :=
        div_lt_div_of_pos_left zero_lt_one hpos (by linarith)
      refine ⟨by positivity, hinv_half, ?_, ?_, ?_⟩
      · dsimp [b, c]; linarith
      · dsimp [c, d]; linarith
      · dsimp [d]; linarith [div_pos one_pos (by positivity : (0 : ℝ) < 2 * ((n + N₀ : ℕ) : ℝ))]
    have hχ_supp : ∀ n t, t ∉ Ioc 0 B → χ n t * g t = 0 := by
      intro n t ht
      obtain ⟨ha0, hab, _, hcd, hdB⟩ := h_ab n
      have hχ0 : χ n t = 0 := by
        simp only [mem_Ioc, not_and, not_le] at ht
        by_cases ht0 : t ≤ 0
        · have hle : (t - a n) / (b n - a n) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          exact max_eq_left ((min_le_left _ _).trans hle)
        · have hgt : B < t := ht (not_le.mp ht0)
          have hle : (d n - t) / (d n - c n) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans hle))
      rw [hχ0, zero_mul]
    have hφ_mem : ∀ n, MemLp (fun s => χ n s * g s) 2 (hankelBandMeasure w B) := fun n =>
      MemLp.of_bound (((hχ_cont n).mul g.continuous).aestronglyMeasurable) ‖g‖
        (Eventually.of_forall fun s => by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ_bounds n s).1]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hχ_bounds n s).2).trans (g.norm_coe_le_norm s))
    have hφ_norm : ∀ n, ‖hankelBandOp hw hB ((hφ_mem n).toLp _)‖ ≤
        Real.sqrt (1 - sonineGap B) * ‖(hφ_mem n).toLp _‖ := by
      intro n
      set φ := fun s => χ n s * g s
      have h_sq := kerTransform_band_sq_le hw hB ((hχ_cont n).mul g.continuous) (hχ_supp n)
      have hraw_eq : ∀ t, rawHankelBand w B ((hφ_mem n).toLp φ) t =
          kerTransform (hankelMeasure w) (hankelKernel w) φ t := by
        intro t
        unfold rawHankelBand kerTransform
        have h1 : (fun s => hankelKernel w t s * ((hφ_mem n).toLp φ : ℝ → ℝ) s) =ᵐ[hankelBandMeasure w B]
            fun s => hankelKernel w t s * φ s := by
          filter_upwards [(hφ_mem n).coeFn_toLp] with s hs
          rw [hs]
        rw [integral_congr_ae h1, integral_hankelBandMeasure_eq, integral_hankelMeasure_eq,
          ← integral_indicator (measurableSet_Ioi (a := (0 : ℝ))),
          ← integral_indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := B))]
        refine integral_congr_ae (Eventually.of_forall fun s => ?_)
        by_cases hm : s ∈ Ioc 0 B
        · simp [hm, hm.1]
        · by_cases hs0 : s ∈ Ioi 0 <;> simp [hm, hs0]
          exact Or.inr (Or.inr (hχ_supp n s hm))
      have hlhs : ‖hankelBandOp hw hB ((hφ_mem n).toLp φ)‖ ^ 2 =
          ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (kerTransform (hankelMeasure w) (hankelKernel w) φ t) ^ 2 := by
        rw [show hankelBandOp hw hB ((hφ_mem n).toLp φ) =
            (rawHankelBand_memLp hw hB ((hφ_mem n).toLp φ)).toLp _ from rfl,
          lp_norm_sq_hankelBandMeasure (rawHankelBand_memLp hw hB ((hφ_mem n).toLp φ))]
        refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
        rw [hraw_eq t]
      have hrhs : ‖(hφ_mem n).toLp φ‖ ^ 2 = ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (φ t) ^ 2 :=
        lp_norm_sq_hankelBandMeasure (hφ_mem n)
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
        mul_pow, Real.sq_sqrt (by linarith [sonineGap_le_half B]), hlhs, hrhs]
      exact h_sq
    have h_tend : Tendsto (fun n => (hφ_mem n).toLp (fun s => χ n s * g s)) atTop
        (𝓝 (hg_mem.toLp g)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      have h_sq_lim : Tendsto (fun n => ∫ s, (χ n s * g s - g s) ^ 2 ∂(hankelBandMeasure w B))
          atTop (𝓝 0) := by
        have h_ae_zero : ∀ᵐ s ∂(hankelBandMeasure w B), s ∈ Ioo (0 : ℝ) B := by
          have h_ioc : ∀ᵐ s ∂(hankelBandMeasure w B), s ∈ Ioc (0 : ℝ) B := ae_restrict_mem measurableSet_Ioc
          have hB_zero : (hankelBandMeasure w B) ({B} : Set ℝ) = 0 := by
            rw [hankelBandMeasure_eq, withDensity_apply _ (MeasurableSet.singleton B)]
            have hvol : (volume.restrict (Ioc (0 : ℝ) B)) ({B} : Set ℝ) = 0 := by
              rw [Measure.restrict_apply (MeasurableSet.singleton B)]
              exact measure_mono_null inter_subset_left (measure_singleton B)
            exact setLIntegral_measure_zero _ _ hvol
          have h_nB : ∀ᵐ s ∂(hankelBandMeasure w B), s ≠ B :=
            ae_iff.mpr (by simpa [ne_eq, not_not] using hB_zero)
          filter_upwards [h_ioc, h_nB] with s hs hns
          exact ⟨hs.1, lt_of_le_of_ne hs.2 hns⟩
        have h_int_0 : ∫ _s : ℝ, (0 : ℝ) ∂(hankelBandMeasure w B) = 0 := integral_zero _ _
        rw [← h_int_0]
        refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4 * ‖g‖ ^ 2) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall fun n =>
            (((hχ_cont n).mul g.continuous).sub g.continuous |>.pow 2).aestronglyMeasurable
        · refine Eventually.of_forall fun n => Eventually.of_forall fun s => ?_
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          have hsub : |χ n s * g s - g s| ≤ 2 * ‖g‖ := by
            have h1 : |χ n s * g s| ≤ ‖g‖ := by
              rw [abs_mul, abs_of_nonneg (hχ_bounds n s).1]
              exact (mul_le_of_le_one_left (abs_nonneg _) (hχ_bounds n s).2).trans (g.norm_coe_le_norm s)
            calc |χ n s * g s - g s| ≤ |χ n s * g s| + |g s| := abs_sub _ _
              _ ≤ ‖g‖ + ‖g‖ := add_le_add h1 (g.norm_coe_le_norm s)
              _ = 2 * ‖g‖ := by ring
          calc (χ n s * g s - g s) ^ 2 = |χ n s * g s - g s| ^ 2 := (sq_abs _).symm
            _ ≤ (2 * ‖g‖) ^ 2 := by gcongr
            _ = 4 * ‖g‖ ^ 2 := by ring
        · exact integrable_const _
        · filter_upwards [h_ae_zero] with s hs
          have h_ev : ∀ᶠ n in atTop, χ n s * g s - g s = 0 := by
            obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt hs.1
            obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (sub_pos.mpr hs.2)
            rw [eventually_atTop]
            refine ⟨max N₁ N₂, fun n hn => ?_⟩
            have hbn : b n ≤ s := by
              have h1 : (1 : ℝ) / ((n + N₀ : ℕ) : ℝ) ≤ 1 / ((N₁ : ℝ) + 1) := by
                refine one_div_le_one_div_of_le (by positivity) ?_
                have : N₁ + 1 ≤ n + N₀ := by
                  have : 1 ≤ N₀ := Nat.le_add_left 1 _
                  omega
                exact_mod_cast this
              exact h1.trans hN₁.le
            have hcn : s ≤ c n := by
              have h1 : (1 : ℝ) / ((n + N₀ : ℕ) : ℝ) ≤ 1 / ((N₂ : ℝ) + 1) := by
                refine one_div_le_one_div_of_le (by positivity) ?_
                have : N₂ + 1 ≤ n + N₀ := by
                  have : 1 ≤ N₀ := Nat.le_add_left 1 _
                  omega
                exact_mod_cast this
              dsimp [c]; linarith
            obtain ⟨_, hab, _, hcd, _⟩ := h_ab n
            have hleft : 1 ≤ (s - a n) / (b n - a n) := by
              rw [le_div_iff₀ (by linarith)]; linarith
            have hright : 1 ≤ (d n - s) / (d n - c n) := by
              rw [le_div_iff₀ (by linarith)]; linarith
            have hχ1 : χ n s = 1 := by
              dsimp [χ]
              rw [min_eq_left hright, min_eq_right hleft, max_eq_right zero_le_one]
            simp [hχ1]
          exact Tendsto.congr' (h_ev.mono fun n hn => by dsimp only; rw [hn, zero_pow two_ne_zero])
            tendsto_const_nhds
      rw [Metric.tendsto_atTop] at h_sq_lim
      obtain ⟨N, hN⟩ := h_sq_lim (δ ^ 2) (sq_pos_of_pos hδ)
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm, ← MemLp.toLp_sub (hφ_mem n) hg_mem]
      have hsq_eq : ‖((hφ_mem n).sub hg_mem).toLp ((fun s => χ n s * g s) - ⇑g)‖ ^ 2 =
          ∫ s, (χ n s * g s - g s) ^ 2 ∂(hankelBandMeasure w B) := by
        rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [((hφ_mem n).sub hg_mem).coeFn_toLp] with s hs
        rw [hs, Pi.sub_apply, RCLike.inner_apply, conj_trivial, sq]
      have hlt := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hlt
      rw [← hsq_eq] at hlt
      exact (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp hlt
    have h_op_tend : Tendsto (fun n => ‖hankelBandOp hw hB ((hφ_mem n).toLp (fun s => χ n s * g s))‖)
        atTop (𝓝 ‖hankelBandOp hw hB (hg_mem.toLp g)‖) :=
      (((hankelBandOp hw hB).continuous.tendsto _).comp h_tend).norm
    have h_rhs_tend : Tendsto (fun n => Real.sqrt (1 - sonineGap B) * ‖(hφ_mem n).toLp (fun s => χ n s * g s)‖)
        atTop (𝓝 (Real.sqrt (1 - sonineGap B) * ‖hg_mem.toLp g‖)) :=
      tendsto_const_nhds.mul h_tend.norm
    exact le_of_tendsto_of_tendsto h_op_tend h_rhs_tend (Eventually.of_forall hφ_norm)
  have h_eps : ∀ {ε : ℝ}, 0 < ε →
      ‖hankelBandOp hw hB f‖ ≤ Real.sqrt (1 - sonineGap B) * ‖f‖ +
        (Real.sqrt (1 - sonineGap B) + ‖hankelBandOp hw hB‖) * ε := by
    intro ε hε
    have hf_mem : MemLp (f : ℝ → ℝ) (ENNReal.ofReal 2) (hankelBandMeasure w B) := by
      simpa using Lp.memLp f
    obtain ⟨g, hg_int, g_mem⟩ := hf_mem.exists_boundedContinuous_integral_rpow_sub_le zero_lt_two
      (sq_pos_of_pos hε)
    have g_mem2 : MemLp (g : ℝ → ℝ) 2 (hankelBandMeasure w B) := by simpa using g_mem
    have hdist : ‖f - g_mem2.toLp g‖ ≤ ε := by
      have hf2 : f = (Lp.memLp f).toLp f := (Lp.toLp_coeFn f (Lp.memLp f)).symm
      have hsub_eq : f - g_mem2.toLp g = ((Lp.memLp f).sub g_mem2).toLp ((f : ℝ → ℝ) - ⇑g) := by
        nth_rw 1 [hf2]
        rw [MemLp.toLp_sub]
      rw [hsub_eq, ← sq_le_sq₀ (norm_nonneg _) hε.le, ← real_inner_self_eq_norm_sq,
        MeasureTheory.L2.inner_def]
      have heq_in : (fun s => inner ℝ ((((Lp.memLp f).sub g_mem2).toLp ((f : ℝ → ℝ) - ⇑g) : ℝ → ℝ) s)
          ((((Lp.memLp f).sub g_mem2).toLp ((f : ℝ → ℝ) - ⇑g) : ℝ → ℝ) s)) =ᵐ[hankelBandMeasure w B]
          fun s => ‖(f : ℝ → ℝ) s - g s‖ ^ (2 : ℝ) := by
        filter_upwards [((Lp.memLp f).sub g_mem2).coeFn_toLp] with s hs
        rw [hs, Pi.sub_apply, RCLike.inner_apply, conj_trivial, Real.rpow_two, Real.norm_eq_abs,
          sq_abs, sq]
      rw [integral_congr_ae heq_in]
      exact hg_int
    have hdiff_op : ‖hankelBandOp hw hB f - hankelBandOp hw hB (g_mem2.toLp g)‖ ≤
        ‖hankelBandOp hw hB‖ * ε := by
      rw [← map_sub]
      exact ((hankelBandOp hw hB).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
    have hg_norm : ‖g_mem2.toLp g‖ ≤ ‖f‖ + ε := by
      calc ‖g_mem2.toLp g‖ = ‖f - (f - g_mem2.toLp g)‖ := by congr 1; abel
        _ ≤ ‖f‖ + ‖f - g_mem2.toLp g‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ε := by linarith
    calc ‖hankelBandOp hw hB f‖
        ≤ ‖hankelBandOp hw hB (g_mem2.toLp g)‖ +
            ‖hankelBandOp hw hB f - hankelBandOp hw hB (g_mem2.toLp g)‖ := by
          simpa only [add_comm] using
            (norm_add_le (hankelBandOp hw hB (g_mem2.toLp g))
              (hankelBandOp hw hB f - hankelBandOp hw hB (g_mem2.toLp g))) |>.trans_eq' (by
              congr 1; abel)
      _ ≤ Real.sqrt (1 - sonineGap B) * ‖g_mem2.toLp g‖ + ‖hankelBandOp hw hB‖ * ε :=
          add_le_add (h_bcf g g_mem2) hdiff_op
      _ ≤ Real.sqrt (1 - sonineGap B) * (‖f‖ + ε) + ‖hankelBandOp hw hB‖ * ε := by gcongr
      _ = Real.sqrt (1 - sonineGap B) * ‖f‖ +
            (Real.sqrt (1 - sonineGap B) + ‖hankelBandOp hw hB‖) * ε := by ring
  by_contra! hlt
  set δ : ℝ := ‖hankelBandOp hw hB f‖ - Real.sqrt (1 - sonineGap B) * ‖f‖
  have hδ : 0 < δ := sub_pos.mpr hlt
  set K : ℝ := Real.sqrt (1 - sonineGap B) + ‖hankelBandOp hw hB‖
  have hK : 0 ≤ K := add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h_ctr := h_eps (ε := δ / (2 * (K + 1))) (by positivity)
  have h_small : K * (δ / (2 * (K + 1))) < δ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Hankel–Sonine inverse bound (`int:sonine`)**: `1 + hankelBandOp hw hB` is invertible on
`L²(hankelBandMeasure w B)` with operator norm
`‖(1 + hankelBandOp hw hB)⁻¹‖ ≤ max 4 (2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B))`. -/
theorem hankelSonine_inv {w : ℕ} (hw : 1 ≤ w) {B : ℝ} (hB : 0 < B) :
    ∃ A_inv : Lp ℝ 2 (hankelBandMeasure w B) →L[ℝ] Lp ℝ 2 (hankelBandMeasure w B),
      (1 + hankelBandOp hw hB) * A_inv = 1 ∧
      A_inv * (1 + hankelBandOp hw hB) = 1 ∧
      ‖A_inv‖ ≤ max 4 (2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B)) := by
  set ε := sonineGap B
  have hε_pos : 0 < ε := sonineGap_pos hB
  have hε_le : ε ≤ 1 / 2 := sonineGap_le_half B
  have hnorm : ‖-hankelBandOp hw hB‖ ≤ Real.sqrt (1 - ε) := by
    rw [norm_neg]; exact hankelBandOp_norm_le hw hB
  have hlt1 : ‖-hankelBandOp hw hB‖ < 1 := by
    refine hnorm.trans_lt ?_
    rw [Real.sqrt_lt' (by positivity)]
    linarith
  let u := Units.oneSub (-hankelBandOp hw hB) hlt1
  refine ⟨(u⁻¹ : _ˣ), ?_, ?_, ?_⟩
  · have hu : (u : _ →L[ℝ] _) = 1 + hankelBandOp hw hB := by
      simp [u, Units.val_oneSub, sub_neg_eq_add]
    rw [← hu]
    exact Units.mul_inv u
  · have hu : (u : _ →L[ℝ] _) = 1 + hankelBandOp hw hB := by
      simp [u, Units.val_oneSub, sub_neg_eq_add]
    rw [← hu]
    exact Units.inv_mul u
  · have h_geo := tsum_geometric_le_of_norm_lt_one (-hankelBandOp hw hB) hlt1
    have h_u_eq : (↑(u⁻¹ : _ˣ) : Lp ℝ 2 (hankelBandMeasure w B) →L[ℝ] Lp ℝ 2 (hankelBandMeasure w B)) =
        ∑' n : ℕ, (-hankelBandOp hw hB) ^ n := rfl
    rw [h_u_eq]
    have h1_le : ‖(1 : Lp ℝ 2 (hankelBandMeasure w B) →L[ℝ] Lp ℝ 2 (hankelBandMeasure w B))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have h_geo' : ‖∑' n : ℕ, (-hankelBandOp hw hB) ^ n‖ ≤ (1 - ‖-hankelBandOp hw hB‖)⁻¹ := by
      linarith
    have hs_lt : Real.sqrt (1 - ε) < 1 := by
      rw [Real.sqrt_lt' (by positivity)]; linarith
    have h_inv_le : (1 - ‖-hankelBandOp hw hB‖)⁻¹ ≤ (1 - Real.sqrt (1 - ε))⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    have h_gap_lb : ε / 2 ≤ 1 - Real.sqrt (1 - ε) := by
      have hsq : (1 - Real.sqrt (1 - ε)) * (1 + Real.sqrt (1 - ε)) = ε := by
        calc (1 - Real.sqrt (1 - ε)) * (1 + Real.sqrt (1 - ε))
            = 1 - (Real.sqrt (1 - ε)) ^ 2 := by ring
          _ = 1 - (1 - ε) := by rw [Real.sq_sqrt (by linarith)]
          _ = ε := by ring
      have hle2 : 1 + Real.sqrt (1 - ε) ≤ 2 := by
        linarith [Real.sqrt_le_one.mpr (by linarith : 1 - ε ≤ 1)]
      nth_rw 1 [← hsq]
      calc (1 - Real.sqrt (1 - ε)) * (1 + Real.sqrt (1 - ε)) / 2
          ≤ (1 - Real.sqrt (1 - ε)) * 2 / 2 := by gcongr
        _ = 1 - Real.sqrt (1 - ε) := by ring
    have h_two_div : (1 - Real.sqrt (1 - ε))⁻¹ ≤ 2 / ε := by
      rw [div_eq_mul_inv]
      calc (1 - Real.sqrt (1 - ε))⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ (by positivity) h_gap_lb
        _ = 2 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have h_max_eq : 2 / ε = max 4 (2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B)) := by
      simp only [ε, sonineGap]
      set C : ℝ := 1024 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B)
      have hC : 0 < C := by positivity
      by_cases hle : (1 / 2 : ℝ) ≤ 1 / C
      · have hC2 : C ≤ 2 := by
          rwa [one_div, one_div, inv_le_inv₀ (by norm_num) hC] at hle
        rw [min_eq_left hle, max_eq_left]
        · norm_num
        · calc 2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B) = 2 * C := by simp only [C]; ring
            _ ≤ 4 := by linarith
      · have hgt : 1 / C < 1 / 2 := not_le.mp hle
        have hC2 : 2 < C := by
          rwa [one_div, one_div, inv_lt_inv₀ hC (by norm_num)] at hgt
        rw [min_eq_right hgt.le, max_eq_right]
        · simp only [C, one_div, div_inv_eq_mul]; ring
        · calc (4 : ℝ) ≤ 2 * C := by linarith
            _ = 2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B) := by simp only [C]; ring
    exact h_geo'.trans (h_inv_le.trans (h_two_div.trans_eq h_max_eq))

/-- info: 'FormalResearch.ModularBootstrap.Integrality.hankelSonine_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelSonine_inv

end FormalResearch.ModularBootstrap.Integrality
