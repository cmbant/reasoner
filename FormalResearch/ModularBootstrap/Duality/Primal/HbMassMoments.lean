module

public import FormalResearch.ModularBootstrap.Duality.Primal.HbMassProfile

/-!
# Chart bounds and near-optimal extremal tail bound (`dsl:hb-mass`)

Helper module for `HbMass.lean`:
* Chart MVT bounds (`virasoroDeltaChart_mvt_bounds`) and Jacobian ratio (`jacRatio`) bounds;
* `spectralMeasure_near_bump_bounded` and `near_opt_extremal_le` (`∫_{[B_n, ∞)} (g_{*,n} / 2π) dν_n ≤ C · η_n / c_n^{1/3}`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.Hadamard
  FormalResearch.ArgPrinciple

private instance (H : HermiteBiehlerData) : Finite (HbNodes H) :=
  Finite.of_injective (fun i : HbNodes H => (⟨i.1, i.2.1⟩ : H.S))
    (fun _ _ h => Subtype.ext (Subtype.mk.inj h))

/-! ### 1. Chart MVT bounds and Jacobian ratio bounds -/

lemma virasoroDeltaChart_mvt_bounds :
    ∃ C_d : ℝ, cStar / 2 ≤ C_d ∧
      ∀ {c u1 u2 : ℝ}, 0 < c → |u1| ≤ virasoroAC c ^ 2 → |u2| ≤ virasoroAC c ^ 2 → u1 ≤ u2 →
        (cStar / 2) * c ^ ((1 : ℝ) / 3) * (u2 - u1) ≤
          virasoroDeltaChart c u1 - virasoroDeltaChart c u2 ∧
        virasoroDeltaChart c u1 - virasoroDeltaChart c u2 ≤
          C_d * c ^ ((1 : ℝ) / 3) * (u2 - u1) := by
  obtain ⟨C_d, hCd, hder⟩ := virasoroDeltaChart_deriv_abs_bounds
  refine ⟨C_d, hCd, fun {c u1 u2} hc hu1 hu2 hle => ?_⟩
  rcases eq_or_lt_of_le hle with rfl | hlt
  · simp
  have hsub : ∀ u ∈ Icc u1 u2, |u| ≤ virasoroAC c ^ 2 := fun u hu => by
    have h1 := abs_le.mp hu1; have h2 := abs_le.mp hu2
    exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hcont : ContinuousOn (virasoroDeltaChart c) (Icc u1 u2) := fun u hu =>
    (virasoroDeltaChart_hasDerivAt hc (hsub u hu)).continuousAt.continuousWithinAt
  have hdiff : ∀ u ∈ Ioo u1 u2, HasDerivAt (virasoroDeltaChart c) (deriv (virasoroDeltaChart c) u) u := fun u hu => by
    have hd := virasoroDeltaChart_hasDerivAt hc (hsub u (Ioo_subset_Icc_self hu))
    rwa [hd.deriv]
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (virasoroDeltaChart c) (fun u => deriv (virasoroDeltaChart c) u)
    hlt hcont hdiff
  have hbd := hder hc (hsub ξ (Ioo_subset_Icc_self hξ))
  have hne : u2 - u1 ≠ 0 := sub_ne_zero.mpr hlt.ne'
  have hpos : 0 < u2 - u1 := sub_pos.mpr hlt
  have heq : virasoroDeltaChart c u1 - virasoroDeltaChart c u2 =
      (-deriv (virasoroDeltaChart c) ξ) * (u2 - u1) := by
    rw [eq_div_iff hne] at hslope; linarith
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_right hbd.1 hpos.le, mul_le_mul_of_nonneg_right hbd.2 hpos.le⟩

/-- Ratio `jAiry c t / (- deriv (virasoroDeltaChart c) (chartUT c t))` converting
`spectralWeight prob c t * (psiTilde prob c gs (chartUT c t)).re` to `gs t / (2 * π)`. -/
noncomputable def jacRatio (c t : ℝ) : ℝ :=
  jAiry c t / (-deriv (virasoroDeltaChart c) (chartUT c t))

lemma gs_div_two_pi_eq_jacRatio (prob : FixedWeightProblem) {c t : ℝ} (hc : 0 < c)
    (hsh : prob.totalShift ≤ c / 12) (ht : 0 < t) {gs : ℝ → ℝ} (htc : TestClass prob (c / 12) gs)
    (hM : prob.cardyNorm (c / 12) gs = 1) (hu_vac : |chartUT c t| ≤ virasoroAC c ^ 2)
    (hΔ : virasoroDeltaChart c (chartUT c t) = t) :
    gs t / (2 * Real.pi) =
      jacRatio c t * spectralWeight prob c t * (psiTilde prob c gs (chartUT c t : ℂ)).re := by
  obtain ⟨_, _, hder⟩ := virasoroDeltaChart_deriv_abs_bounds
  have hder_pos : 0 < -deriv (virasoroDeltaChart c) (chartUT c t) :=
    lt_of_lt_of_le (mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc _)) (hder hc hu_vac).1
  have hV_pos : 0 < prob.cardyV (c / 12) t := prob.cardyV_pos hsh ht
  have hJ_pos : 0 < jAiry c t := jAiry_pos hc ht
  have hre := psiTilde_re_ofReal prob hc htc hu_vac
  rw [hre, hM, hΔ, inv_one, one_mul]
  unfold jacRatio spectralWeight
  field_simp [neg_ne_zero.mp hder_pos.ne', hV_pos.ne', hJ_pos.ne', Real.pi_ne_zero]

lemma jacRatio_bounds {M : ℝ} (hM : 0 ≤ M) :
    ∃ c0 jac_lo jac_hi : ℝ, max 1 M ≤ c0 ∧ 0 < jac_lo ∧ jac_lo ≤ jac_hi ∧
      ∀ {c t : ℝ}, c0 ≤ c → 0 < t → |uAiry c t| ≤ M →
        |chartUT c t| ≤ virasoroAC c ^ 2 →
        jac_lo ≤ jacRatio c t ∧ jacRatio c t ≤ jac_hi := by
  obtain ⟨C_d, hCd, hder⟩ := virasoroDeltaChart_deriv_abs_bounds
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err hM
  let c_x : ℝ := ((2 * M / (betaTip * xiStar)) ^ (3 / 2 : ℝ)) + 1
  let c0 : ℝ := max (max 1 M) (max c_ut c_x)
  let jac_lo : ℝ := xiStar / (3 * betaTip * C_d)
  let jac_hi : ℝ := 2 * xiStar / (betaTip * cStar)
  have hCd_pos : 0 < C_d := lt_of_lt_of_le (half_pos cStar_pos) hCd
  have hjac_lo_pos : 0 < jac_lo := div_pos xiStar_pos (mul_pos (mul_pos (by norm_num) betaTip_pos) hCd_pos)
  have hjac_le : jac_lo ≤ jac_hi := by
    dsimp [jac_lo, jac_hi]
    have hc2 : cStar ≤ 2 * C_d := by linarith
    have h1 : 1 / (3 * C_d) ≤ 2 / cStar := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hCd_pos) cStar_pos]; linarith
    calc xiStar / (3 * betaTip * C_d) = (xiStar / betaTip) * (1 / (3 * C_d)) := by ring
      _ ≤ (xiStar / betaTip) * (2 / cStar) := mul_le_mul_of_nonneg_left h1 (div_pos xiStar_pos betaTip_pos).le
      _ = 2 * xiStar / (betaTip * cStar) := by ring
  refine ⟨c0, jac_lo, jac_hi, le_max_left _ _, hjac_lo_pos, hjac_le, fun {c t} hc htp hu hu_vac => ?_⟩
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one ((le_max_left 1 M).trans ((le_max_left _ _).trans hc))
  have hc_x : c_x ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc23_ge : 2 * M / (betaTip * xiStar) ≤ c ^ ((2 : ℝ) / 3) := by
    have h0 : 0 ≤ 2 * M / (betaTip * xiStar) := div_nonneg (mul_nonneg (by norm_num) hM) (mul_pos betaTip_pos xiStar_pos).le
    have hc_ge' : (2 * M / (betaTip * xiStar)) ^ (3 / 2 : ℝ) ≤ c := by
      have : c_x = (2 * M / (betaTip * xiStar)) ^ (3 / 2 : ℝ) + 1 := rfl
      linarith
    have hr := Real.rpow_le_rpow (by positivity) hc_ge' (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    rw [← Real.rpow_mul h0] at hr
    simpa [show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num] using hr
  have hu_div : M / (betaTip * c ^ ((2 : ℝ) / 3)) ≤ xiStar / 2 := by
    have hc23_pos : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
    rw [div_le_div_iff₀ (mul_pos betaTip_pos hc23_pos) two_pos]
    have h1 := mul_le_mul_of_nonneg_right hc23_ge (mul_pos betaTip_pos xiStar_pos).le
    rw [div_mul_cancel₀ _ (mul_pos betaTip_pos xiStar_pos).ne'] at h1
    linarith
  have hx_eq : Real.sqrt (3 * t / c) = xiStar - uAiry c t / (betaTip * c ^ ((2 : ℝ) / 3)) := by
    unfold uAiry
    have hp : c ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc_pos _).ne'
    field_simp [betaTip_pos.ne', hp]; ring
  have hdiff_le : |uAiry c t / (betaTip * c ^ ((2 : ℝ) / 3))| ≤ xiStar / 2 := by
    have hc23_pos : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
    rw [abs_div, abs_of_pos (mul_pos betaTip_pos hc23_pos)]
    exact (div_le_div_of_nonneg_right hu (mul_pos betaTip_pos hc23_pos).le).trans hu_div
  have hx_bds : xiStar / 2 ≤ Real.sqrt (3 * t / c) ∧ Real.sqrt (3 * t / c) ≤ 3 * xiStar / 2 := by
    have := abs_le.mp hdiff_le
    rw [hx_eq]; constructor <;> linarith
  have hc13_pos : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
  have hJ_bds : (xiStar / (3 * betaTip)) * c ^ ((1 : ℝ) / 3) ≤ jAiry c t ∧
      jAiry c t ≤ (xiStar / betaTip) * c ^ ((1 : ℝ) / 3) := by
    have hj : jAiry c t = 2 * Real.sqrt (3 * t / c) * c ^ ((1 : ℝ) / 3) / (3 * betaTip) := rfl
    rw [hj]
    have h3b : (0 : ℝ) ≤ 3 * betaTip := by have := betaTip_pos; positivity
    constructor
    · calc (xiStar / (3 * betaTip)) * c ^ ((1 : ℝ) / 3)
          = 2 * (xiStar / 2) * c ^ ((1 : ℝ) / 3) / (3 * betaTip) := by ring
        _ ≤ 2 * Real.sqrt (3 * t / c) * c ^ ((1 : ℝ) / 3) / (3 * betaTip) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx_bds.1 (by norm_num)) hc13_pos.le) h3b
    · calc 2 * Real.sqrt (3 * t / c) * c ^ ((1 : ℝ) / 3) / (3 * betaTip)
          ≤ 2 * (3 * xiStar / 2) * c ^ ((1 : ℝ) / 3) / (3 * betaTip) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx_bds.2 (by norm_num)) hc13_pos.le) h3b
        _ = (xiStar / betaTip) * c ^ ((1 : ℝ) / 3) := by ring
  have hD_bds := hder hc_pos hu_vac
  have hD_lo_pos : 0 < (cStar / 2) * c ^ ((1 : ℝ) / 3) := mul_pos (half_pos cStar_pos) hc13_pos
  have hD_pos : 0 < -deriv (virasoroDeltaChart c) (chartUT c t) := lt_of_lt_of_le hD_lo_pos hD_bds.1
  have hJ_pos : 0 ≤ jAiry c t := (jAiry_pos hc_pos htp).le
  have hxi1b : 0 ≤ (xiStar / betaTip) * c ^ ((1 : ℝ) / 3) :=
    mul_nonneg (div_nonneg xiStar_pos.le betaTip_pos.le) hc13_pos.le
  unfold jacRatio
  constructor
  · calc jac_lo = ((xiStar / (3 * betaTip)) * c ^ ((1 : ℝ) / 3)) / (C_d * c ^ ((1 : ℝ) / 3)) := by
          dsimp [jac_lo]; field_simp [hc13_pos.ne', hCd_pos.ne', betaTip_pos.ne']
      _ ≤ jAiry c t / (-deriv (virasoroDeltaChart c) (chartUT c t)) :=
          div_le_div₀ hJ_pos hJ_bds.1 hD_pos hD_bds.2
  · calc jAiry c t / (-deriv (virasoroDeltaChart c) (chartUT c t))
        ≤ ((xiStar / betaTip) * c ^ ((1 : ℝ) / 3)) / ((cStar / 2) * c ^ ((1 : ℝ) / 3)) :=
          div_le_div₀ hxi1b hJ_bds.2 hD_lo_pos hD_bds.1
      _ = jac_hi := by
          dsimp [jac_hi]; field_simp [hc13_pos.ne', cStar_pos.ne', betaTip_pos.ne']

lemma uAiry_window_t_bounds {M : ℝ} (hM : 0 ≤ M) :
    ∃ c0 : ℝ, max 1 M ≤ c0 ∧ ∀ {c t : ℝ}, c0 ≤ c → 0 < t → |uAiry c t| ≤ M →
      c * (xiStar / 2) ^ 2 / 3 ≤ t ∧ t ≤ c * (3 * xiStar / 2) ^ 2 / 3 := by
  let c0 : ℝ := max (max 1 M) (((2 * M / (betaTip * xiStar)) ^ (3 / 2 : ℝ)) + 1)
  refine ⟨c0, le_max_left _ _, fun {c t} hc htp hu => ?_⟩
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one ((le_max_left 1 M).trans ((le_max_left _ _).trans hc))
  have hc_x : ((2 * M / (betaTip * xiStar)) ^ (3 / 2 : ℝ)) + 1 ≤ c := (le_max_right _ _).trans hc
  have hc23_ge : 2 * M / (betaTip * xiStar) ≤ c ^ ((2 : ℝ) / 3) := by
    have h0 : 0 ≤ 2 * M / (betaTip * xiStar) := div_nonneg (mul_nonneg (by norm_num) hM) (mul_pos betaTip_pos xiStar_pos).le
    have hr := Real.rpow_le_rpow (by positivity) (by linarith : (2 * M / (betaTip * xiStar)) ^ (3 / 2 : ℝ) ≤ c)
      (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    rw [← Real.rpow_mul h0] at hr
    simpa [show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num] using hr
  have hc23_pos : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
  have hu_div : M / (betaTip * c ^ ((2 : ℝ) / 3)) ≤ xiStar / 2 := by
    rw [div_le_div_iff₀ (mul_pos betaTip_pos hc23_pos) two_pos]
    have h1 := mul_le_mul_of_nonneg_right hc23_ge (mul_pos betaTip_pos xiStar_pos).le
    rw [div_mul_cancel₀ _ (mul_pos betaTip_pos xiStar_pos).ne'] at h1
    linarith
  have hx_eq : Real.sqrt (3 * t / c) = xiStar - uAiry c t / (betaTip * c ^ ((2 : ℝ) / 3)) := by
    unfold uAiry
    field_simp [betaTip_pos.ne', hc23_pos.ne']; ring
  have hdiff_le : |uAiry c t / (betaTip * c ^ ((2 : ℝ) / 3))| ≤ xiStar / 2 := by
    rw [abs_div, abs_of_pos (mul_pos betaTip_pos hc23_pos)]
    exact (div_le_div_of_nonneg_right hu (mul_pos betaTip_pos hc23_pos).le).trans hu_div
  have hx_bds : xiStar / 2 ≤ Real.sqrt (3 * t / c) ∧ Real.sqrt (3 * t / c) ≤ 3 * xiStar / 2 := by
    have := abs_le.mp hdiff_le; rw [hx_eq]; constructor <;> linarith
  have hsq : Real.sqrt (3 * t / c) ^ 2 = 3 * t / c := Real.sq_sqrt (div_nonneg (by linarith) hc_pos.le)
  have hsq_lo : (xiStar / 2) ^ 2 ≤ 3 * t / c := by rw [← hsq]; exact sq_le_sq' (by linarith [xiStar_pos]) hx_bds.1
  have hsq_hi : 3 * t / c ≤ (3 * xiStar / 2) ^ 2 := by rw [← hsq]; exact sq_le_sq' (by linarith [xiStar_pos]) hx_bds.2
  constructor
  · rw [le_div_iff₀ hc_pos] at hsq_lo; linarith
  · rw [div_le_iff₀ hc_pos] at hsq_hi; linarith

lemma integrableOn_spectralWeight_mul_of_continuousOn (prob : FixedWeightProblem)
    {c t_lo t_hi : ℝ} (hc : 0 < c) (hsh : prob.totalShift ≤ c / 12) (ht_lo : 0 < t_lo)
    (_hle : t_lo ≤ t_hi) (meas : AdmissibleCrossingMeasure prob (c / 12))
    {W : Set ℝ} (_hW_meas : MeasurableSet W) (hW_sub : W ⊆ Icc t_lo t_hi)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc t_lo t_hi)) :
    IntegrableOn (fun t => f t * spectralWeight prob c t) W meas.ν := by
  have hsw_cont : ContinuousOn (spectralWeight prob c) (Icc t_lo t_hi) := by
    unfold spectralWeight
    refine continuousOn_const.div ?_ fun t ht => ?_
    · exact (((continuous_const.mul (continuous_cardyV prob (c / 12))).mul
        (continuous_jAiry c))).continuousOn
    · have ht0 : 0 < t := ht_lo.trans_le ht.1
      exact (mul_pos (mul_pos (by positivity) (prob.cardyV_pos hsh ht0)) (jAiry_pos hc ht0)).ne'
  obtain ⟨C_b, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.mul hsw_cont)
  have hfin : meas.ν (Icc t_lo t_hi) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (Icc_subset_Icc ht_lo.le le_rfl)) (measure_Icc_lt_top meas t_hi)).ne
  have hconst : IntegrableOn (fun _ : ℝ => max C_b 0) (Icc t_lo t_hi) meas.ν :=
    integrableOn_const hfin
  refine IntegrableOn.mono_set (hconst.mono' ?_ ?_) hW_sub
  · exact (hf.mul hsw_cont).aestronglyMeasurable measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hCb t ht).trans (le_max_left C_b 0)

lemma spectralMeasure_near_bump_bounded (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    {η : ℕ → ℝ} (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hvag_near : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))))
    (χ : ℝ → ℝ) (hχ_cont : Continuous χ) (hχ_cs : HasCompactSupport χ) (hχ_sub : tsupport χ ⊆ Ioo CD.a CD.b) :
    ∃ C_χ : ℝ, 0 < C_χ ∧ ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0 →
        ∫ u, χ u ∂(spectralMeasure prob (c n) meas.ν) ≤ C_χ := by
  classical
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  let L := ∑ k : Fin CD.K, CD.ω k * χ (CD.z k)
  let C_χ : ℝ := max L 0 + 1
  refine ⟨C_χ, by positivity, ?_⟩
  obtain ⟨_, ν0, _, hν0⟩ := hb_canonical_primal prob H hc hs_pos
  by_contra hnot
  rw [not_eventually] at hnot
  let Bad := fun (n : ℕ) (m : AdmissibleCrossingMeasure prob (c n / 12)) =>
    m.ν (F n ∪ Ici (B n - η n))ᶜ = 0 ∧ C_χ < ∫ u, χ u ∂(spectralMeasure prob (c n) m.ν)
  have hfreq : ∃ᶠ n in atTop, ∃ m, Bad n m := hnot.mono fun _ hn => by push Not at hn; exact hn
  let ν_bad : ℕ → Measure ℝ := fun n => if h : ∃ m, Bad n m then h.choose.ν else ν0 n
  have hν_bad_mem : ∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
      ν_bad n = meas.ν ∧ meas.ν (F n ∪ Ici (B n - η n))ᶜ = 0 := by
    filter_upwards [hν0, hη_nn] with n ⟨meas0, hν0_eq, hν0_supp⟩ hnn
    dsimp [ν_bad]; split_ifs with h
    · exact ⟨h.choose, rfl, h.choose_spec.1⟩
    · have hsub : (F n ∪ Ici (B n - η n))ᶜ ⊆ (F n ∪ Ici (B n))ᶜ :=
        compl_subset_compl.mpr (union_subset_union_right _ (Ici_subset_Ici.mpr (by linarith)))
      exact ⟨meas0, hν0_eq, measure_mono_null hsub hν0_supp⟩
  have hlim := hvag_near ν_bad hν_bad_mem χ hχ_cont hχ_cs hχ_sub
  have hle_Cχ : ∀ᶠ n in atTop, ∫ u, χ u ∂(spectralMeasure prob (c n) (ν_bad n)) ≤ C_χ := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by dsimp [C_χ]; linarith [le_max_left L 0] : L < C_χ))]
      with n hn; exact hn.le
  have hcontra : ∀ᶠ n in atTop, ¬ ∃ m, Bad n m := by
    filter_upwards [hle_Cχ] with n hle ⟨m, hm1, hm2⟩
    have hex : ∃ m', Bad n m' := ⟨m, hm1, hm2⟩
    have hsp := Classical.choose_spec hex
    have hν_eq : ν_bad n = hex.choose.ν := dite_eq_left hex
    rw [hν_eq] at hle
    exact absurd hle (not_le_of_gt hsp.2)
  exact hfreq hcontra

/-! ### 2. Fundamental one-sided extremal integral bound `∫_{[B_n, ∞)} g_{*,n}/(2π) dν_n ≤ C η_n / c_n^{1/3}` -/

lemma near_opt_extremal_le (prob : FixedWeightProblem) (H : HermiteBiehlerData)
    (CD : HbClusterData H) {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {s : HbNodes H → ℕ → ℝ} (hs_pos : ∀ i : HbNodes H, ∀ᶠ n in atTop, 0 < s i n)
    (hs_tend : ∀ i : HbNodes H, Tendsto (fun n => uAiry (c n) (s i n)) atTop (𝓝 i.1))
    (hB_tend : Tendsto (fun n => uAiry (c n) (constrainedThreshold prob (c n) (hbPrescribedSet s n)))
      atTop (𝓝 H.tm))
    {η : ℕ → ℝ} (hη_nn : ∀ᶠ n in atTop, 0 ≤ η n)
    (hη_o : Tendsto (fun n => η n / (c n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0))
    (hvag_near : ∀ (ν_seq : ℕ → Measure ℝ),
      (∀ᶠ n in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c n / 12),
        ν_seq n = meas.ν ∧
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0) →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo CD.a CD.b →
        Tendsto (fun n => ∫ u, g u ∂(spectralMeasure prob (c n) (ν_seq n))) atTop
          (𝓝 (∑ k : Fin CD.K, CD.ω k * g (CD.z k))))
    {gs0 : ℕ → ℝ → ℝ} (hgs0 : ∀ᶠ n in atTop, IsWeakExtremal prob (c n) (hbPrescribedSet s n)
      (constrainedThreshold prob (c n) (hbPrescribedSet s n)) (gs0 n))
    (hgs0_B : ∀ᶠ n in atTop, gs0 n (constrainedThreshold prob (c n) (hbPrescribedSet s n)) = 0) :
    ∃ C_pos : ℝ, 0 < C_pos ∧ ∀ᶠ n in atTop,
      ∀ meas : AdmissibleCrossingMeasure prob (c n / 12),
        meas.ν (hbPrescribedSet s n ∪ Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n) - η n))ᶜ = 0 →
        IntegrableOn (gs0 n) (Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n))) meas.ν ∧
        0 ≤ ∫ t in Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)), gs0 n t / (2 * Real.pi) ∂meas.ν ∧
        ∫ t in Ici (constrainedThreshold prob (c n) (hbPrescribedSet s n)), gs0 n t / (2 * Real.pi) ∂meas.ν ≤
          C_pos * η n / (c n) ^ ((1 : ℝ) / 3) := by
  let B : ℕ → ℝ := fun n => constrainedThreshold prob (c n) (hbPrescribedSet s n)
  let F : ℕ → Set ℝ := hbPrescribedSet s
  obtain ⟨r0, hr0_pos, hr0_win, _, _⟩ := exists_window_radius CD
  obtain ⟨m0, hm0⟩ := CD.hS_sub H.tm H.tm_mem
  choose bump hbump_cont hbump_cs hbump_01 hbump_one _ hbump_tsupp using
    fun _ : Unit => exists_bump_near (x₀ := H.tm) (r := r0 / 2) (by positivity)
  let χ := bump ()
  have hχ_sub : tsupport χ ⊆ Ioo CD.a CD.b := fun u hu => by
    have h1 := hbump_tsupp () hu
    have hw := hr0_win m0
    rw [← hm0] at hw
    exact ⟨by linarith [h1.1, hw.1], by linarith [h1.2, hw.2]⟩
  obtain ⟨C_χ, hCχ_pos, hχ_bd⟩ := spectralMeasure_near_bump_bounded prob H CD hc hs_pos hη_nn hvag_near
    χ (hbump_cont ()) (hbump_cs ()) hχ_sub
  let M_tm : ℝ := |H.tm| + r0 + 1
  obtain ⟨jac_c0, jac_lo, jac_hi, _, hjac_lo_pos, hjac_le, hjac_bds⟩ := jacRatio_bounds (show 0 ≤ M_tm by positivity)
  obtain ⟨C_ut, c_ut, _, _, hC_ut⟩ := chartUT_sub_uAiry_err (show 0 ≤ M_tm by positivity)
  have hjac_hi_pos : 0 < jac_hi := lt_of_lt_of_le hjac_lo_pos hjac_le
  -- Derivative bound on `psiTilde prob (c n) (gs0 n)` on `closedBall 0 (|H.tm| + r0 + 2)`:
  let m_r : ℕ := Nat.ceil (|H.tm| + r0 + 2)
  let R_m : ℝ := (m_r : ℝ) + 2
  have hm_ge : |H.tm| + r0 + 2 ≤ (m_r : ℝ) + 1 := by
    have := Nat.le_ceil (|H.tm| + r0 + 2); linarith
  obtain ⟨hB_chart, hbl⟩ := weakExtremal_blnorm prob H hc hs_pos hs_tend hB_tend hgs0
  obtain ⟨c_an, hc_an, han⟩ := psiTilde_analyticOnNhd prob
  obtain ⟨D_p⟩ := UniformPropositionPData.of_problem prob
  have hDiff_ev : ∀ᶠ n in atTop, DifferentiableOn ℂ (psiTilde prob (c n) (gs0 n)) (ball (0 : ℂ) R_m) := by
    filter_upwards [hc.eventually_ge_atTop c_an, chartAC_sq_eventually_ge D_p.hr1_pos hc R_m, hgs0]
      with n hcn hAc hwe
    have hcpos : 0 < c n := hc_an.trans_le hcn
    have hsub : ball (0 : ℂ) R_m ⊆ psiDom (c n) :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hAc)).trans
        (closedBall_chartAC_subset_psiDom D_p.hr1_pos hcpos)
    exact ((han hcn hwe.1).mono hsub).differentiableOn
  obtain ⟨n_d, hn_d⟩ := eventually_atTop.mp hDiff_ev
  let Fn : ℕ → ℂ → ℂ := fun n => psiTilde prob (c (n + n_d)) (gs0 (n + n_d))
  have hFn_diff : ∀ n, DifferentiableOn ℂ (Fn n) (ball (0 : ℂ) R_m) := fun n => hn_d (n + n_d) (Nat.le_add_left n_d n)
  have hFn_loc : TendstoLocallyUniformlyOn Fn (normProfile H.G) atTop (ball (0 : ℂ) R_m) := by
    have hbl_shift : TendstoUniformlyOn Fn (normProfile H.G) atTop (closedBall (0 : ℂ) ((m_r + 1 : ℕ) + 1)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have h0 := (Metric.tendstoUniformlyOn_iff.mp (hbl (m_r + 1))) ε hε
      rw [eventually_atTop] at h0 ⊢
      obtain ⟨N, hN⟩ := h0
      exact ⟨N, fun n hn => hN (n + n_d) (by omega)⟩
    exact hbl_shift.tendstoLocallyUniformlyOn.mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by dsimp [R_m]; norm_cast)))
  have hFn_der := tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball 1 Fn (normProfile H.G) hFn_diff hFn_loc
  have hFn_der_unif : TendstoUniformlyOn (fun n => deriv (Fn n)) (deriv (normProfile H.G)) atTop
      (closedBall (0 : ℂ) (|H.tm| + r0 + 1)) := by
    have hcb : IsCompact (closedBall (0 : ℂ) (|H.tm| + r0 + 1)) := isCompact_closedBall _ _
    have hsub : closedBall (0 : ℂ) (|H.tm| + r0 + 1) ⊆ ball (0 : ℂ) R_m := fun z hz => by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_ball_zero_iff]
      dsimp [R_m]; linarith [hm_ge]
    have h1 := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hFn_der
      (closedBall (0 : ℂ) (|H.tm| + r0 + 1)) hsub hcb
    simpa only [iteratedDeriv_one] using h1
  have hG_der_cont : ContinuousOn (deriv (normProfile H.G)) (closedBall (0 : ℂ) (|H.tm| + r0 + 1)) :=
    (normProfile_deriv_differentiable H).continuous.continuousOn
  obtain ⟨M_d, hMd⟩ := (isCompact_closedBall (0 : ℂ) (|H.tm| + r0 + 1)).exists_bound_of_continuousOn hG_der_cont
  have hder_bd_shift : ∀ᶠ n in atTop, ∀ v ∈ closedBall (0 : ℂ) (|H.tm| + r0 + 1), ‖deriv (Fn n) v‖ ≤ max M_d 0 + 1 := by
    rw [Metric.tendstoUniformlyOn_iff] at hFn_der_unif
    filter_upwards [hFn_der_unif 1 zero_lt_one] with n hn v hv
    have hdist : ‖deriv (Fn n) v‖ ≤ ‖deriv (normProfile H.G) v‖ + ‖deriv (normProfile H.G) v - deriv (Fn n) v‖ := by
      calc ‖deriv (Fn n) v‖ ≤ ‖deriv (normProfile H.G) v‖ + ‖-(deriv (normProfile H.G) v - deriv (Fn n) v)‖ := by
            simpa [sub_eq_add_neg] using norm_add_le (deriv (normProfile H.G) v) (-(deriv (normProfile H.G) v - deriv (Fn n) v))
        _ = ‖deriv (normProfile H.G) v‖ + ‖deriv (normProfile H.G) v - deriv (Fn n) v‖ := by rw [norm_neg]
    have h1 := hMd v hv
    have h2 : dist (deriv (normProfile H.G) v) (deriv (Fn n) v) < 1 := hn v hv
    rw [dist_eq_norm] at h2
    linarith [le_max_left M_d 0]
  have hder_bd : ∀ᶠ n in atTop, ∀ v ∈ closedBall (0 : ℂ) (|H.tm| + r0 + 1),
      ‖deriv (psiTilde prob (c n) (gs0 n)) v‖ ≤ max M_d 0 + 1 := by
    rw [eventually_atTop] at hder_bd_shift ⊢
    obtain ⟨N, hN⟩ := hder_bd_shift
    refine ⟨N + n_d, fun n hn => ?_⟩
    have hn' := hN (n - n_d) (by omega)
    dsimp [Fn] at hn'
    rwa [show n - n_d + n_d = n by omega] at hn'
  let C_F : ℝ := max M_d 0 + 1
  have hCF_pos : 0 < C_F := by positivity
  let C_pos : ℝ := jac_hi * C_F * (2 / cStar) * C_χ + 1
  refine ⟨C_pos, by have := cStar_pos; positivity, ?_⟩
  obtain ⟨hu_shift, hBη_pos⟩ := uAiry_sub_shift_tendsto hc hB_tend hη_nn hη_o
  have hC_ut_err : ∀ᶠ n in atTop, C_ut * (c n) ^ (-(2 / 3 : ℝ)) < r0 / 8 := by
    have h0 : Tendsto (fun n => C_ut * (c n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc).const_mul C_ut
    exact h0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hgs0, hgs0_B, hχ_bd, hder_bd, hDiff_ev, hBη_pos, hη_nn,
    eventually_pos_of_uAiry_tendsto hc hB_tend,
    hB_tend.eventually (Metric.ball_mem_nhds H.tm (show 0 < r0 / 8 by positivity)),
    hu_shift.eventually (Metric.ball_mem_nhds H.tm (show 0 < r0 / 8 by positivity)),
    hB_chart.eventually (Metric.ball_mem_nhds H.tm (show 0 < r0 / 8 by positivity)),
    hC_ut_err, hc.eventually_ge_atTop (max jac_c0 (max c_ut (max 1 (12 * prob.totalShift)))),
    virasoroAC_sq_eventually_ge hc (|H.tm| + r0 + 2), eventually_all.2 hs_pos]
    with n hwe hgsB hχ hDF hDiff hBη hnn hB_pos hBu hBηu hBc hCut hc_ge hVac hs_n meas hν
  have hc_pos : 0 < c n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge)))
  have hsh12 : prob.totalShift ≤ c n / 12 := by
    have := (le_max_right 1 _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_ge)); linarith
  have hjac_c : jac_c0 ≤ c n := (le_max_left _ _).trans hc_ge
  have hcut : c_ut ≤ c n := (le_max_left _ _).trans ((le_max_right _ _).trans hc_ge)
  have ha0 : 0 < c n / 12 := by positivity
  obtain ⟨hint_Ici0, hfw_le⟩ := lemma_fwX_one_sided_unconditional prob hsh12 ha0 meas hwe.1
    (T := B n) (fun t ht => hwe.2.2.2 t (Or.inr ht))
  have hvac0 : prob.gVac (c n / 12) (gs0 n) = 0 := hwe.2.2.1
  rw [hvac0, zero_add] at hfw_le
  have hint_IciB : IntegrableOn (gs0 n) (Ici (B n)) meas.ν :=
    hint_Ici0.mono_set (Ici_subset_Ici.mpr hB_pos.le)
  have hint_Ico0B : IntegrableOn (gs0 n) (Ico 0 (B n)) meas.ν :=
    hint_Ici0.mono_set Ico_subset_Ici_self
  have hsplit : ∫ t in Ici (0 : ℝ), gs0 n t ∂meas.ν =
      (∫ t in Ico (0 : ℝ) (B n), gs0 n t ∂meas.ν) + ∫ t in Ici (B n), gs0 n t ∂meas.ν := by
    rw [← Ico_union_Ici_eq_Ici hB_pos.le,
      setIntegral_union (Set.disjoint_iff.mpr fun _ ⟨h1, h2⟩ => not_le_of_gt h1.2 h2)
        measurableSet_Ici hint_Ico0B hint_IciB]
  have hIci_nn : 0 ≤ ∫ t in Ici (B n), gs0 n t ∂meas.ν :=
    setIntegral_nonneg measurableSet_Ici fun t ht => hwe.2.2.2 t (Or.inr ht)
  have hint_Ico0Bη : IntegrableOn (gs0 n) (Ico 0 (B n - η n)) meas.ν :=
    hint_Ici0.mono_set (Ico_subset_Ici_self)
  have hint_IcoBη : IntegrableOn (gs0 n) (Ico (B n - η n) (B n)) meas.ν :=
    hint_Ici0.mono_set (Ico_subset_Ici_self.trans (Ici_subset_Ici.mpr hBη.le))
  have hIco_split : ∫ t in Ico (0 : ℝ) (B n), gs0 n t ∂meas.ν =
      (∫ t in Ico (0 : ℝ) (B n - η n), gs0 n t ∂meas.ν) +
        ∫ t in Ico (B n - η n) (B n), gs0 n t ∂meas.ν := by
    rw [← Ico_union_Ico_eq_Ico hBη.le (by linarith : B n - η n ≤ B n),
      setIntegral_union (Set.disjoint_iff.mpr fun _ ⟨h1, h2⟩ => not_le_of_gt h1.2 h2.1)
        measurableSet_Ico hint_Ico0Bη hint_IcoBη]
  have hIco0_nn : 0 ≤ ∫ t in Ico (0 : ℝ) (B n - η n), gs0 n t ∂meas.ν := by
    refine setIntegral_nonneg_ae measurableSet_Ico ?_
    have hsupp : ∀ᵐ t ∂meas.ν, t ∈ F n ∪ Ici (B n - η n) := by
      have := measure_eq_zero_iff_ae_notMem.1 hν
      filter_upwards [this] with t ht using notMem_compl_iff.1 ht
    filter_upwards [hsupp] with t hmem htIco
    have htF : t ∈ F n := by
      rcases hmem with hF | hIci
      · exact hF
      · exact absurd hIci (not_le_of_gt htIco.2)
    exact hwe.2.2.2 t (Or.inl htF)
  have h_upper_gs : ∫ t in Ici (B n), gs0 n t ∂meas.ν ≤
      ∫ t in Ico (B n - η n) (B n), |gs0 n t| ∂meas.ν := by
    have h1 : ∫ t in Ici (B n), gs0 n t ∂meas.ν ≤ -∫ t in Ico (B n - η n) (B n), gs0 n t ∂meas.ν := by
      linarith [hfw_le, hsplit, hIco_split, hIco0_nn]
    have h2 : -∫ t in Ico (B n - η n) (B n), gs0 n t ∂meas.ν ≤
        ∫ t in Ico (B n - η n) (B n), |gs0 n t| ∂meas.ν := by
      rw [← integral_neg]
      exact setIntegral_mono_on hint_IcoBη.neg hint_IcoBη.norm measurableSet_Ico
        fun t _ => neg_le_abs (gs0 n t)
    exact h1.trans h2
  -- Now bound `|gs0 n t| / (2 * π)` on `Ico (B n - η n) (B n)`
  obtain ⟨C_d, hCd, hmv_bds⟩ := virasoroDeltaChart_mvt_bounds
  have hBu_win : |uAiry (c n) (B n)| ≤ M_tm := by
    have := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBu : |uAiry (c n) (B n) - H.tm| < r0 / 8)
    dsimp [M_tm]; exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩
  obtain ⟨_, hΔB, herrB⟩ := hC_ut hcut hB_pos hBu_win
  let uB := chartUT (c n) (B n)
  have huB_ball : |uB - H.tm| < r0 / 8 := by simpa [uB, Metric.mem_ball, Real.dist_eq] using hBc
  have huB_vac : |uB| ≤ virasoroAC (c n) ^ 2 := by
    have := abs_lt.mp huB_ball
    exact (abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩).trans
      ((show |H.tm| + r0 / 8 ≤ |H.tm| + r0 + 2 by linarith).trans hVac)
  have hψB : (psiTilde prob (c n) (gs0 n) (uB : ℂ)).re = 0 := by
    have h1 := (psiTilde_eq_zero_iff prob hc_pos hsh12 hwe.1
      (by rw [hwe.2.1]; exact zero_lt_one) huB_vac).mpr (by rw [hΔB]; exact hgsB)
    rw [h1, Complex.zero_re]
  have h_pt_bd : ∀ t ∈ Ico (B n - η n) (B n),
      |gs0 n t| / (2 * Real.pi) ≤
        (jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3)) *
          (spectralWeight prob (c n) t * χ (uAiry (c n) t)) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hBη ht.1
    have hu_ant := uAiry_antitoneOn hc_pos
    have hu_le : uAiry (c n) (B n) ≤ uAiry (c n) t := hu_ant ht_pos.le hB_pos.le ht.2.le
    have hu_ge : uAiry (c n) t ≤ uAiry (c n) (B n - η n) := hu_ant hBη.le ht_pos.le ht.1
    have hu_tm : |uAiry (c n) t - H.tm| < r0 / 8 := by
      have h1 := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBu : |uAiry (c n) (B n) - H.tm| < r0 / 8)
      have h2 := abs_lt.mp (by simpa [Metric.mem_ball, Real.dist_eq] using hBηu : |uAiry (c n) (B n - η n) - H.tm| < r0 / 8)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hu_win : |uAiry (c n) t| ≤ M_tm := by
      have := abs_lt.mp hu_tm
      dsimp [M_tm]; exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm], by linarith [le_abs_self H.tm]⟩
    obtain ⟨_, hΔt, herrt⟩ := hC_ut hcut ht_pos hu_win
    let u := chartUT (c n) t
    have hu_close : |u - H.tm| < r0 / 4 := by
      have h1 := abs_lt.mp hu_tm; have h2 := abs_lt.mp (herrt.trans_lt hCut)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hu_vac : |u| ≤ virasoroAC (c n) ^ 2 := by
      have hu_c := abs_lt.mp hu_close
      exact (abs_le.mpr ⟨by linarith [neg_abs_le H.tm, hu_c.1],
        by linarith [le_abs_self H.tm, hu_c.2]⟩).trans
        ((show |H.tm| + r0 / 4 ≤ |H.tm| + r0 + 2 by linarith).trans hVac)
    have huB_le_u : uB ≤ u := by
      by_contra hlt; push Not at hlt
      have := (virasoroDeltaChart_strictAnti hc_pos) (abs_le.mp hu_vac) (abs_le.mp huB_vac) hlt
      rw [hΔt, hΔB] at this; linarith [ht.2]
    have hmvt := (hmv_bds hc_pos huB_vac hu_vac huB_le_u).1
    rw [hΔB, hΔt] at hmvt
    have hc13_pos : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
    have hu_diff : u - uB ≤ (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3) := by
      have hle : (cStar / 2) * (c n) ^ ((1 : ℝ) / 3) * (u - uB) ≤ η n := hmvt.trans (by linarith [ht.1])
      rw [le_div_iff₀ hc13_pos]
      have hcs0 : 0 < cStar := cStar_pos
      calc (u - uB) * (c n) ^ ((1 : ℝ) / 3)
          = (cStar / 2 * (c n) ^ ((1 : ℝ) / 3) * (u - uB)) * (2 / cStar) := by
            field_simp [cStar_pos.ne']
        _ ≤ η n * (2 / cStar) := mul_le_mul_of_nonneg_right hle (div_nonneg zero_le_two cStar_pos.le)
        _ = (2 / cStar) * η n := by ring
    -- MVT for `x ↦ (psiTilde prob (c n) (gs0 n) (x : ℂ)).re` on `[uB, u]`
    have hψ_diff : |(psiTilde prob (c n) (gs0 n) (u : ℂ)).re| ≤ C_F * (u - uB) := by
      rcases eq_or_lt_of_le huB_le_u with h_eq | h_lt
      · rw [← h_eq, hψB, abs_zero, sub_self, mul_zero]
      · have hseg : ∀ x ∈ Icc uB u, (x : ℂ) ∈ closedBall (0 : ℂ) (|H.tm| + r0 + 1) := fun x hx => by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          have h1 := abs_lt.mp huB_ball; have h2 := abs_lt.mp hu_close
          exact abs_le.mpr ⟨by linarith [neg_abs_le H.tm, hx.1], by linarith [le_abs_self H.tm, hx.2]⟩
        have hcont : ContinuousOn (fun x : ℝ => (psiTilde prob (c n) (gs0 n) (x : ℂ)).re) (Icc uB u) :=
          fun x hx => by
            have hball : (x : ℂ) ∈ ball (0 : ℂ) R_m := by
              have hcb := hseg x hx
              rw [mem_closedBall_zero_iff] at hcb; rw [mem_ball_zero_iff]; dsimp [R_m]; linarith [hm_ge]
            have hda := hDiff.differentiableAt (isOpen_ball.mem_nhds hball)
            exact (hasDerivAt_re_of_complex hda.hasDerivAt).continuousAt.continuousWithinAt
        have hder_mvt : ∀ x ∈ Ioo uB u, HasDerivAt (fun y : ℝ => (psiTilde prob (c n) (gs0 n) (y : ℂ)).re)
            (deriv (psiTilde prob (c n) (gs0 n)) (x : ℂ)).re x := fun x hx => by
          have hball : (x : ℂ) ∈ ball (0 : ℂ) R_m := by
            have hcb := hseg x (Ioo_subset_Icc_self hx)
            rw [mem_closedBall_zero_iff] at hcb; rw [mem_ball_zero_iff]; dsimp [R_m]; linarith [hm_ge]
          exact hasDerivAt_re_of_complex (hDiff.differentiableAt (isOpen_ball.mem_nhds hball)).hasDerivAt
        obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope _ _ h_lt hcont hder_mvt
        have hbd_ξ : |(deriv (psiTilde prob (c n) (gs0 n)) (ξ : ℂ)).re| ≤ C_F :=
          (Complex.abs_re_le_norm _).trans (hDF _ (hseg ξ (Ioo_subset_Icc_self hξ)))
        have heq_sub : (psiTilde prob (c n) (gs0 n) (u : ℂ)).re =
            (deriv (psiTilde prob (c n) (gs0 n)) (ξ : ℂ)).re * (u - uB) := by
          rw [eq_div_iff (sub_ne_zero.mpr h_lt.ne')] at hslope
          linarith [hψB]
        rw [heq_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr huB_le_u)]
        exact mul_le_mul_of_nonneg_right hbd_ξ (sub_nonneg.mpr huB_le_u)
    have hgs_eq := gs_div_two_pi_eq_jacRatio prob hc_pos hsh12 ht_pos hwe.1 hwe.2.1 hu_vac hΔt
    have hjac := hjac_bds hjac_c ht_pos hu_win hu_vac
    have hsw_pos : 0 < spectralWeight prob (c n) t := spectralWeight_pos hc_pos hsh12 ht_pos
    have hχ1 : χ (uAiry (c n) t) = 1 := by
      have := abs_lt.mp hu_tm
      exact hbump_one () _ ⟨by linarith, by linarith⟩
    calc |gs0 n t| / (2 * Real.pi)
        = |gs0 n t / (2 * Real.pi)| := by rw [abs_div, abs_of_pos Real.two_pi_pos]
      _ = jacRatio (c n) t * spectralWeight prob (c n) t * |(psiTilde prob (c n) (gs0 n) (u : ℂ)).re| := by
          rw [hgs_eq, abs_mul, abs_mul, abs_of_pos (lt_of_lt_of_le hjac_lo_pos hjac.1), abs_of_pos hsw_pos]
      _ ≤ jac_hi * spectralWeight prob (c n) t * (C_F * ((2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3))) := by
          gcongr
          · exact hjac.2
          · exact hψ_diff.trans (mul_le_mul_of_nonneg_left hu_diff hCF_pos.le)
      _ = (jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3)) *
            (spectralWeight prob (c n) t * χ (uAiry (c n) t)) := by
          rw [hχ1, mul_one]; ring
  have hint_χ : IntegrableOn (fun t => spectralWeight prob (c n) t * χ (uAiry (c n) t)) (Ioi 0) meas.ν := by
    let S_pts : Set ℝ := F n ∪ {B n - η n}
    have hS_fin : S_pts.Finite := (Set.finite_range _).union (Set.finite_singleton _)
    have hS_ne : hS_fin.toFinset.Nonempty := ⟨B n - η n, hS_fin.mem_toFinset.mpr (Or.inr rfl)⟩
    obtain ⟨τ_min, hτ_mem, hτ_le⟩ := hS_fin.toFinset.exists_min_image id hS_ne
    have hτ_pos : 0 < τ_min := by
      rcases hS_fin.mem_toFinset.mp hτ_mem with ⟨i, rfl⟩ | h_eq
      · exact hs_n i
      · rw [mem_singleton_iff.mp h_eq]; exact hBη
    have hgap : Duality.IsAtGap meas τ_min := by
      refine measure_mono_null (fun t ht => ?_) hν
      rintro (⟨i, rfl⟩ | ht_ge)
      · exact (not_le_of_gt (mem_Iio.mp ht)) (hτ_le (s i n) (hS_fin.mem_toFinset.mpr (Or.inl ⟨i, rfl⟩)))
      · have h1 : τ_min ≤ B n - η n := hτ_le (B n - η n) (hS_fin.mem_toFinset.mpr (Or.inr rfl))
        exact (not_le_of_gt (mem_Iio.mp ht)) (h1.trans ht_ge)
    have hlf := isLocallyFiniteMeasure_spectralMeasure prob hc_pos hsh12 meas hτ_pos hgap
    exact (integrable_spectralMeasure_iff prob hc_pos hsh12 meas.ν (hbump_cont ())).mp
      ((hbump_cont ()).integrable_of_hasCompactSupport (hbump_cs ()))
  have hc13_pos : 0 < (c n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc_pos _
  have hcoef_nn : 0 ≤ jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3) := by
    have := cStar_pos; positivity
  refine ⟨hint_IciB, ?_, ?_⟩
  · simp only [div_eq_mul_inv, integral_mul_const]
    exact mul_nonneg hIci_nn (by positivity)
  · have hIco_sub : Ico (B n - η n) (B n) ⊆ Ioi (0 : ℝ) := fun _ ht => lt_of_lt_of_le hBη ht.1
    calc ∫ t in Ici (B n), gs0 n t / (2 * Real.pi) ∂meas.ν
        = (∫ t in Ici (B n), gs0 n t ∂meas.ν) / (2 * Real.pi) := by
            simp only [div_eq_mul_inv, integral_mul_const]
      _ ≤ (∫ t in Ico (B n - η n) (B n), |gs0 n t| ∂meas.ν) / (2 * Real.pi) :=
            div_le_div_of_nonneg_right h_upper_gs Real.two_pi_pos.le
      _ = ∫ t in Ico (B n - η n) (B n), |gs0 n t| / (2 * Real.pi) ∂meas.ν := by
            simp only [div_eq_mul_inv, integral_mul_const]
      _ ≤ ∫ t in Ico (B n - η n) (B n), (jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3)) *
            (spectralWeight prob (c n) t * χ (uAiry (c n) t)) ∂meas.ν := by
            refine setIntegral_mono_on (hint_IcoBη.norm.div_const _)
              ((hint_χ.mono_set hIco_sub).const_mul _) measurableSet_Ico h_pt_bd
      _ ≤ (jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3)) *
            ∫ t in Ioi (0 : ℝ), spectralWeight prob (c n) t * χ (uAiry (c n) t) ∂meas.ν := by
            rw [integral_const_mul]
            refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hint_χ ?_
              (Eventually.of_forall hIco_sub)) hcoef_nn
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg (spectralWeight_pos hc_pos hsh12 ht).le (hbump_01 () _).1
      _ ≤ C_pos * η n / (c n) ^ ((1 : ℝ) / 3) := by
            rw [← integral_spectralMeasure prob hc_pos hsh12 meas.ν (hbump_cont ())]
            have h1 : (jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3)) *
                ∫ u, χ u ∂(spectralMeasure prob (c n) meas.ν) ≤
                (jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3)) * C_χ :=
              mul_le_mul_of_nonneg_left (hχ meas hν) hcoef_nn
            dsimp [χ] at h1
            have hηc_nn : 0 ≤ η n / (c n) ^ ((1 : ℝ) / 3) := div_nonneg hnn hc13_pos.le
            have hmul_eq : (jac_hi * C_F * (2 / cStar) * η n / (c n) ^ ((1 : ℝ) / 3)) * C_χ =
                (jac_hi * C_F * (2 / cStar) * C_χ) * (η n / (c n) ^ ((1 : ℝ) / 3)) := by ring
            have hCpos_eq : C_pos * η n / (c n) ^ ((1 : ℝ) / 3) =
                (jac_hi * C_F * (2 / cStar) * C_χ + 1) * (η n / (c n) ^ ((1 : ℝ) / 3)) := by
              dsimp [C_pos]; ring
            have hle_cpos : jac_hi * C_F * (2 / cStar) * C_χ ≤ jac_hi * C_F * (2 / cStar) * C_χ + 1 :=
              by linarith
            exact h1.trans (by rw [hmul_eq, hCpos_eq]; linarith [mul_le_mul_of_nonneg_right hle_cpos hηc_nn])

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.near_opt_extremal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.near_opt_extremal_le

end FormalResearch.ModularBootstrap.FixedWeight