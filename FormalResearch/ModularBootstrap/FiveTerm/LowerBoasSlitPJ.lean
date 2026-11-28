module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasCoordGeom
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen

/-!
# Poisson–Jensen `log |B(σ)|` bound and quadratic `confB` root bounds on `lowerBoasRightDom`

* `setIntegral_log_slitBoundaryMap_le_of_confB`:
  `∫_{slitPreimage} log |B(σ)| P_{z₀}(σ) dσ ≤ log (|(confB z₀).re| + 3/2) + log 2`.
* `z0_norm_re_im_bounds_of_confB`, `z0_im_ratio_of_confB`, `z0_sigmaStar_sep_of_confB`:
  geometric estimates on the preimage `z₀` of `b = confB z₀` with `Re b > ξ_*`, `0 < |Im b| ≤ 1/4`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.TipFront

noncomputable section

lemma sqrt2_gt_slit : (1.414 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma sqrt2_lt_slit : √2 < (1.415 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma posLog_mono_nn {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    max 0 (Real.log a) ≤ max 0 (Real.log b) := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · simp [Real.log_zero]
  · exact max_le_max_left 0 (Real.log_le_log ha_pos hab)

lemma posLog_div_le_posLog_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max 0 (Real.log (a / b)) ≤ max 0 (Real.log a) + max 0 (Real.log (1 / b)) := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · simp only [zero_div, Real.log_zero, max_self, zero_add]; positivity
  · rcases hb.eq_or_lt with rfl | hb_pos
    · simp only [div_zero, Real.log_zero, max_self]; positivity
    · rw [Real.log_div ha_pos.ne' hb_pos.ne', one_div, Real.log_inv]
      rcases le_or_gt (Real.log a - Real.log b) 0 with h | h
      · rw [max_eq_left h]; positivity
      · rw [max_eq_right h.le]
        have h1 : Real.log a ≤ max 0 (Real.log a) := le_max_right _ _
        have h2 : -Real.log b ≤ max 0 (-Real.log b) := le_max_right _ _
        linarith

lemma intervalIntegrable_posLog_inv_abs (c a b : ℝ) :
    IntervalIntegrable (fun σ => max 0 (Real.log (1 / |σ - c|))) volume a b := by
  have hlog : IntervalIntegrable (fun σ => |Real.log (σ - c)|) volume a b := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := a - c) (b := b - c)).comp_sub_right c
      eNorm_ne_top
    rw [sub_add_cancel, sub_add_cancel] at h
    exact h.abs
  have hm : Measurable (fun σ : ℝ => max 0 (Real.log (1 / |σ - c|))) :=
    Measurable.max measurable_const (Real.measurable_log.comp
      (measurable_const.div (continuous_abs.measurable.comp (measurable_id.sub measurable_const))))
  refine hlog.mono_fun hm.aestronglyMeasurable (Eventually.of_forall fun σ => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (le_max_left _ _), Real.norm_of_nonneg (abs_nonneg _)]
  by_cases hσ : σ = c
  · subst hσ; simp
  · rw [one_div, Real.log_inv, Real.log_abs]
    rcases le_or_gt (-Real.log (σ - c)) 0 with h | h
    · rw [max_eq_left h]; exact abs_nonneg _
    · rw [max_eq_right h.le, ← abs_neg]; exact le_abs_self _

lemma integrable_poisson_mul_posLog_div (x y ρ : ℝ) (hy : 0 < y) (hρ : 0 < ρ) :
    Integrable (fun σ => poissonKernel x y σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) := by
  have hi := (intervalIntegrable_posLog_inv_abs sigmaStar (sigmaStar - ρ) (sigmaStar + ρ)).1
  have hdom : Integrable ((Ioc (sigmaStar - ρ) (sigmaStar + ρ)).indicator
      (fun σ => (π * y)⁻¹ * (max 0 (Real.log ρ) + max 0 (Real.log (1 / |σ - sigmaStar|))))) :=
    IntegrableOn.integrable_indicator
      (((intervalIntegrable_const (c := max 0 (Real.log ρ))).1.add hi).const_mul (π * y)⁻¹)
      measurableSet_Ioc
  have hm : Measurable (fun σ : ℝ =>
      poissonKernel x y σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) :=
    (continuous_poissonKernel x hy).measurable.mul (Measurable.max measurable_const
      (Real.measurable_log.comp (measurable_const.div
        (continuous_abs.measurable.comp (measurable_id.sub measurable_const)))))
  refine hdom.mono hm.aestronglyMeasurable (Eventually.of_forall fun σ => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hy.le σ) (le_max_left 0 _))]
  by_cases hmem : σ ∈ Ioc (sigmaStar - ρ) (sigmaStar + ρ)
  · rw [indicator_of_mem hmem]
    have hP : poissonKernel x y σ ≤ (π * y)⁻¹ := by
      simpa [one_div] using poissonKernel_le_inv_pi_mul_y hy σ
    have hL : max 0 (Real.log (ρ / |σ - sigmaStar|)) ≤
        max 0 (Real.log ρ) + max 0 (Real.log (1 / |σ - sigmaStar|)) :=
      posLog_div_le_posLog_add hρ.le (abs_nonneg _)
    have hnorm : ‖(π * y)⁻¹ * (max 0 (Real.log ρ) + max 0 (Real.log (1 / |σ - sigmaStar|)))‖ =
        (π * y)⁻¹ * (max 0 (Real.log ρ) + max 0 (Real.log (1 / |σ - sigmaStar|))) :=
      Real.norm_of_nonneg (by positivity)
    rw [hnorm]
    exact mul_le_mul hP hL (le_max_left 0 _) (by positivity)
  · rw [indicator_of_notMem hmem, norm_zero]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hmem
    have hge : ρ ≤ |σ - sigmaStar| := by
      rcases hmem with h1 | h2
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have h0 : max 0 (Real.log (ρ / |σ - sigmaStar|)) = 0 :=
      max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge (abs_nonneg _)))
    rw [h0, mul_zero]

/-! ### 1. `log |B(σ)|` Poisson integral bound -/

private lemma confB_real_im_abs_le_half {σ : ℝ} (hnot : σ ∉ ({-1, 0, 1} : Set ℝ)) :
    |(confB (σ : ℂ)).im| ≤ 1 / 2 := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
  rcases lt_trichotomy σ (-1) with hm | rfl | hm1
  · rw [confB_real_im_of_lt_neg_one hm]; norm_num
  · exact absurd rfl hnot.1
  · rcases lt_trichotomy σ 0 with h0 | rfl | h0
    · rw [confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1, h0⟩]; norm_num
    · exact absurd rfl hnot.2.1
    · rcases lt_trichotomy σ 1 with h1 | rfl | h1
      · rw [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]; norm_num
      · exact absurd rfl hnot.2.2
      · rw [confB_real_im_of_one_lt h1]; norm_num

private lemma confB_sub_I_norm_ge_half_of_mem {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    1 / 2 ≤ ‖b - Complex.I‖ := by
  have him : (b - Complex.I).im ≤ -(1 / 2 : ℝ) := by
    have := (abs_le.mp hb).2
    simp only [Complex.sub_im, Complex.I_im]
    linarith
  have h1 : 1 / 2 ≤ |(b - Complex.I).im| := by rw [abs_of_neg (by linarith)]; linarith
  exact h1.trans (Complex.abs_im_le_norm _)

private lemma slit_edge_partition_ae :
    (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
  have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 :=
    ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
  refine Filter.eventuallyEqSet_iff'.2 ?_
  change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
  rw [ae_iff]
  refine measure_mono_null (fun σ hσ => ?_) hnull
  by_contra hnot
  apply hσ; apply propext
  simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
  rcases lt_or_gt_of_ne hnot.1 with hm | hm
  · exact Or.inr (Or.inl hm)
  · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
    · exact Or.inl (Or.inl ⟨hm, h0⟩)
    · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
      · exact Or.inr (Or.inr ⟨h0, h1⟩)
      · exact Or.inl (Or.inr h1)

private lemma disjoint_slitPreimage_edgePreimage : Disjoint slitPreimage edgePreimage := by
  rw [Set.disjoint_left]
  intro σ h1 h2
  rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2
  · linarith [h1.1]
  · linarith [h1.2, h2.1]
  · linarith
  · linarith [h2.2]

private lemma abs_slitBoundaryMap_ge_xiStar {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    xiStar ≤ |slitBoundaryMap σ| := by
  rcases hσ with hIoo | hIoi
  · exact (xiStar_le_slitBoundaryMap hIoo).trans (le_abs_self _)
  · have := slitBoundaryMap_le_neg_xiStar hIoi
    linarith [neg_abs_le (slitBoundaryMap σ)]

private lemma confB_eq_slitBoundaryMap_of_mem {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := by
  rcases hσ with hIoo | hIoi
  · exact Complex.ext (confB_real_re hIoo.2.ne (by linarith [hIoo.2]) hIoo.1.ne')
      (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
  · have hgt : 1 < σ := hIoi
    exact Complex.ext (confB_real_re (by linarith) hgt.ne' (by linarith))
      (confB_real_im_of_one_lt hgt)

/-- Upper bound on the slit Poisson integral of `log |B(σ)|` by applying `halfPlane_poissonJensen`
to `w ↦ (confB w - I)⁻¹`. -/
theorem setIntegral_log_slitBoundaryMap_le_of_confB {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    IntegrableOn (fun σ => Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ) slitPreimage ∧
    ∫ σ in slitPreimage, Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ ≤
      Real.log (|(confB z₀).re| + 3 / 2) + Real.log 2 := by
  let b := confB z₀
  have hb_strip : b ∈ slitStrip := confB_mem_slitStrip hz₀
  let Ψ : ℂ → ℂ := fun w => (confB w - Complex.I)⁻¹
  let Ψ_bdy : ℝ → ℂ := fun σ => (confB (σ : ℂ) - Complex.I)⁻¹
  have hΨ_diff : DifferentiableOn ℂ Ψ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hcb : confB w ∈ slitStrip := confB_mem_slitStrip hw
    have hne : confB w - Complex.I ≠ 0 := by
      intro h0
      have := confB_sub_I_norm_ge_half_of_mem hcb.1.le
      rw [h0, norm_zero] at this
      linarith
    exact (((hasDerivAt_confB hw).sub_const Complex.I).inv hne).differentiableAt.differentiableWithinAt
  have hΨ_bd : ∀ w : ℂ, 0 < w.im → ‖Ψ w‖ ≤ 2 := by
    intro w hw
    have hge := confB_sub_I_norm_ge_half_of_mem (confB_mem_slitStrip hw).1.le
    dsimp [Ψ]; rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hΨ_bdy : ∀ᵐ σ : ℝ ∂volume,
      Tendsto Ψ (𝓝[{w : ℂ | 0 < w.im}] (σ : ℂ)) (𝓝 (Ψ_bdy σ)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 :=
      ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot
    have hnot' : σ ∉ ({-1, 0, 1} : Set ℝ) := hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot'
    have hne : confB (σ : ℂ) - Complex.I ≠ 0 := by
      intro h0
      have := confB_sub_I_norm_ge_half_of_mem (confB_real_im_abs_le_half hnot)
      rw [h0, norm_zero] at this; linarith
    have htend_B : Tendsto (fun w : ℂ => confB w - Complex.I)
        (𝓝[{w : ℂ | 0 < w.im}] (σ : ℂ)) (𝓝 (confB (σ : ℂ) - Complex.I)) :=
      ((confB_continuousWithinAt_real hnot'.2.1 hnot'.2.2 hnot'.1).sub
        continuousWithinAt_const).tendsto.mono_left
        (nhdsWithin_mono _ fun w (hw : 0 < w.im) => hw.le)
    exact htend_B.inv₀ hne
  have hΨ_z₀ : Ψ z₀ ≠ 0 := by
    dsimp [Ψ]
    refine inv_ne_zero (fun h0 => ?_)
    have := confB_sub_I_norm_ge_half_of_mem hb_strip.1.le
    rw [h0, norm_zero] at this; linarith
  obtain ⟨hPJ_int, hPJ_le⟩ :=
    halfPlane_poissonJensen (by norm_num : (0 : ℝ) < 2) hΨ_diff hΨ_bd hΨ_bdy hz₀ hΨ_z₀
  have hsplit : ∫ σ : ℝ, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ =
      (∫ σ in slitPreimage, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ) +
        (∫ σ in edgePreimage, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set slit_edge_partition_ae,
      setIntegral_union disjoint_slitPreimage_edgePreimage (measurableSet_Iio.union measurableSet_Ioo)
        hPJ_int.integrableOn hPJ_int.integrableOn]
  have hedge_le : ∫ σ in edgePreimage, Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ ≤
      Real.log 2 := by
    have hpk_int : IntegrableOn (poissonKernel z₀.re z₀.im) edgePreimage :=
      (integrable_poissonKernel z₀.re hz₀).integrableOn
    have hmono := setIntegral_mono_on hPJ_int.integrableOn (hpk_int.const_mul (Real.log 2))
      (measurableSet_Iio.union measurableSet_Ioo) (fun σ hσ => ?_)
    · rw [integral_const_mul] at hmono
      have hedge_mass : ∫ σ in edgePreimage, poissonKernel z₀.re z₀.im σ ≤ 1 := by
        calc ∫ σ in edgePreimage, poissonKernel z₀.re z₀.im σ
            ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
              setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
                (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
          _ = 1 := integral_poissonKernel z₀.re hz₀
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hmass_nn : 0 ≤ ∫ σ in edgePreimage, poissonKernel z₀.re z₀.im σ :=
        setIntegral_nonneg (measurableSet_Iio.union measurableSet_Ioo)
          fun σ _ => poissonKernel_nonneg hz₀.le σ
      nlinarith
    · have hnot : σ ∉ ({-1, 0, 1} : Set ℝ) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        rcases hσ with (h : σ < -1) | h
        · exact ⟨h.ne, by linarith, by linarith⟩
        · exact ⟨by linarith [h.1], h.1.ne', h.2.ne⟩
      have hge := confB_sub_I_norm_ge_half_of_mem (confB_real_im_abs_le_half hnot)
      have hle2 : ‖Ψ_bdy σ‖ ≤ 2 := by
        dsimp [Ψ_bdy]; rw [norm_inv]; exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
      have hpos : 0 < ‖Ψ_bdy σ‖ := by
        dsimp [Ψ_bdy]; exact norm_pos_iff.mpr (inv_ne_zero (fun h0 => by
          rw [h0, norm_zero] at hge; linarith))
      exact mul_le_mul_of_nonneg_right (Real.log_le_log hpos hle2) (poissonKernel_nonneg hz₀.le σ)
  have hslit_pt : ∀ σ ∈ slitPreimage,
      Real.log |slitBoundaryMap σ| ≤ -Real.log ‖Ψ_bdy σ‖ := by
    intro σ hσ
    have hxi : xiStar ≤ |slitBoundaryMap σ| := abs_slitBoundaryMap_ge_xiStar hσ
    have hpos : 0 < |slitBoundaryMap σ| := xiStar_pos.trans_le hxi
    have hb_eq : confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := confB_eq_slitBoundaryMap_of_mem hσ
    have hsub_ge : |slitBoundaryMap σ| ≤ ‖confB (σ : ℂ) - Complex.I‖ := by
      rw [hb_eq]
      have hre : ((slitBoundaryMap σ : ℂ) - Complex.I).re = slitBoundaryMap σ := by simp
      calc |slitBoundaryMap σ| = |((slitBoundaryMap σ : ℂ) - Complex.I).re| := by rw [hre]
        _ ≤ ‖(slitBoundaryMap σ : ℂ) - Complex.I‖ := Complex.abs_re_le_norm _
    have hΨ_eq : -Real.log ‖Ψ_bdy σ‖ = Real.log ‖confB (σ : ℂ) - Complex.I‖ := by
      dsimp [Ψ_bdy]; rw [norm_inv, Real.log_inv, neg_neg]
    rw [hΨ_eq]
    exact Real.log_le_log hpos hsub_ge
  have hlog_int : IntegrableOn (fun σ => Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ)
      slitPreimage := by
    have hpk_int : IntegrableOn (poissonKernel z₀.re z₀.im) slitPreimage :=
      (integrable_poissonKernel z₀.re hz₀).integrableOn
    let dom : ℝ → ℝ := fun σ =>
      |Real.log xiStar| * poissonKernel z₀.re z₀.im σ +
        ‖Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ‖
    have hdom_int : IntegrableOn dom slitPreimage :=
      (hpk_int.const_mul _).add hPJ_int.norm.integrableOn
    have hmeas : AEStronglyMeasurable
        (fun σ => Real.log |slitBoundaryMap σ| * poissonKernel z₀.re z₀.im σ)
        (volume.restrict slitPreimage) := by
      have hm_b : Measurable slitBoundaryMap := by
        unfold slitBoundaryMap; fun_prop (disch := measurability)
      exact ((Real.measurable_log.comp hm_b.abs).mul
        (continuous_poissonKernel z₀.re hz₀).measurable).aestronglyMeasurable
    refine hdom_int.mono' hmeas ((ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)).mpr
      (Eventually.of_forall fun σ hσ => ?_))
    have hP0 := poissonKernel_nonneg (x := z₀.re) hz₀.le σ
    have hlo : Real.log xiStar ≤ Real.log |slitBoundaryMap σ| :=
      Real.log_le_log xiStar_pos (abs_slitBoundaryMap_ge_xiStar hσ)
    have hhi := hslit_pt σ hσ
    have habs_le : |Real.log (|slitBoundaryMap σ|)| ≤ |Real.log xiStar| + |Real.log ‖Ψ_bdy σ‖| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log xiStar), abs_nonneg (Real.log ‖Ψ_bdy σ‖)]
      · linarith [abs_nonneg (Real.log xiStar), neg_abs_le (Real.log ‖Ψ_bdy σ‖)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    calc |Real.log (|slitBoundaryMap σ|)| * poissonKernel z₀.re z₀.im σ
        ≤ (|Real.log xiStar| + |Real.log ‖Ψ_bdy σ‖|) * poissonKernel z₀.re z₀.im σ := by gcongr
      _ = |Real.log xiStar| * poissonKernel z₀.re z₀.im σ +
            ‖Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]; ring
  have hPJ_neg_int : IntegrableOn
      (fun σ => -(Real.log ‖Ψ_bdy σ‖ * poissonKernel z₀.re z₀.im σ)) slitPreimage :=
    hPJ_int.neg.integrableOn
  have hmono_slit := setIntegral_mono_on hlog_int hPJ_neg_int
    (measurableSet_Ioo.union measurableSet_Ioi) (fun σ hσ => by
      have hm := mul_le_mul_of_nonneg_right (hslit_pt σ hσ) (poissonKernel_nonneg (x := z₀.re) hz₀.le σ)
      linarith only [hm])
  rw [integral_neg] at hmono_slit
  have hlhs_eq : Real.log ‖Ψ z₀‖ = -Real.log ‖b - Complex.I‖ := by
    dsimp [Ψ, b]; rw [norm_inv, Real.log_inv]
  have hbI_le : ‖b - Complex.I‖ ≤ |b.re| + 3 / 2 := by
    have hre : (b - Complex.I).re = b.re := by simp
    have him : |(b - Complex.I).im| ≤ 3 / 2 := by
      have hbim : |b.im| < 1 / 2 := hb_strip.1
      rw [Complex.sub_im, Complex.I_im]
      rw [abs_lt] at hbim; rw [abs_le]; constructor <;> linarith
    calc ‖b - Complex.I‖ ≤ |(b - Complex.I).re| + |(b - Complex.I).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ |b.re| + 3 / 2 := by rw [hre]; linarith
  have hlogb_le : Real.log ‖b - Complex.I‖ ≤ Real.log (|b.re| + 3 / 2) := by
    refine Real.log_le_log ?_ hbI_le
    have := confB_sub_I_norm_ge_half_of_mem hb_strip.1.le
    linarith
  refine ⟨hlog_int, ?_⟩
  linarith [hPJ_le, hsplit, hedge_le, hmono_slit, hlhs_eq, hlogb_le]

/-! ### 2. Quadratic `confB` root bounds -/

private lemma z0_im_ne_zero_triplet {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    z₀ ≠ 0 ∧ z₀ - 1 ≠ 0 ∧ z₀ + 1 ≠ 0 :=
  ⟨fun h => by rw [h, Complex.zero_im] at hz₀; exact lt_irrefl 0 hz₀,
   fun h => by have : z₀ = 1 := sub_eq_zero.mp h; rw [this, Complex.one_im] at hz₀; exact lt_irrefl 0 hz₀,
   fun h => by have : z₀ = -1 := eq_neg_of_add_eq_zero_left h; rw [this, Complex.neg_im, Complex.one_im, neg_zero] at hz₀; exact lt_irrefl 0 hz₀⟩

lemma z0_norm_re_im_bounds_of_confB {z₀ b : ℂ} (hz₀ : 0 < z₀.im) (hb : confB z₀ = b)
    (hre : xiStar < b.re) :
    ‖z₀‖ ≤ 2 ∧ (1 / 4 : ℝ) ≤ ‖z₀ - 1‖ ∧ z₀.re ≤ 1 / 2 ∧
      z₀.im ≤ 0.85 ∧ |z₀.re - sigmaStar| ≤ 0.95 := by
  obtain ⟨hz0, hz1, hz2⟩ := z0_im_ne_zero_triplet hz₀
  set E : ℂ := Complex.exp (2 * (π : ℂ) * b)
  have hE_eq : confE z₀ = E := by
    have h := exp_two_pi_mul_confB hz₀
    rw [hb] at h; exact h.symm
  have hE_norm : ‖E‖ = Real.exp (2 * π * b.re) := by
    dsimp [E]; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hE_gt5 : 5 < ‖E‖ := by
    rw [hE_norm]
    have hpi := Real.pi_pos
    have hlt : Real.exp (2 * π * xiStar) < Real.exp (2 * π * b.re) :=
      Real.exp_lt_exp.mpr (by nlinarith only [hpi, hre])
    rw [exp_two_pi_xiStar] at hlt
    linarith only [hlt, sqrt2_gt_slit]
  have hE_formula : ‖E‖ = ‖z₀ - 1‖ / (‖z₀‖ * ‖z₀ + 1‖) := by
    rw [← hE_eq]; unfold confE; rw [norm_div, norm_mul]
  have hnorm_le2 : ‖z₀‖ ≤ 2 := by
    by_contra hgt
    have hz_gt2 : 2 < ‖z₀‖ := not_le.mp hgt
    have hnum : ‖z₀ - 1‖ ≤ ‖z₀‖ + 1 := (norm_sub_le z₀ 1).trans (by simp)
    have hden1 : 1 < ‖z₀‖ - 1 := by linarith only [hz_gt2]
    have hden2 : ‖z₀‖ - 1 ≤ ‖z₀ + 1‖ := by
      have := norm_sub_le (z₀ + 1) (1 : ℂ); simpa using this
    have hE_le : ‖E‖ ≤ 3 / 2 := by
      rw [hE_formula]
      calc ‖z₀ - 1‖ / (‖z₀‖ * ‖z₀ + 1‖)
          ≤ (‖z₀‖ + 1) / (‖z₀‖ * (‖z₀‖ - 1)) := by gcongr
        _ ≤ 3 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith only [hz_gt2]
    linarith only [hE_gt5, hE_le]
  have h1_ge : (1 / 4 : ℝ) ≤ ‖z₀ - 1‖ := by
    by_contra hlt
    have hz1_lt : ‖z₀ - 1‖ < 1 / 4 := not_le.mp hlt
    have hz_gt : 3 / 4 < ‖z₀‖ := by
      have h2 := norm_add_le z₀ (1 - z₀)
      have h1 : z₀ + (1 - z₀) = (1 : ℂ) := by ring
      rw [h1, norm_one, norm_sub_rev (1 : ℂ) z₀] at h2
      linarith only [h2, hz1_lt]
    have hz2_gt : 7 / 4 < ‖z₀ + 1‖ := by
      have h2 := norm_add_le (z₀ + 1) (1 - z₀)
      have h1 : (z₀ + 1) + (1 - z₀) = (2 : ℂ) := by ring
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h1, h2n, norm_sub_rev (1 : ℂ) z₀] at h2
      linarith only [h2, hz1_lt]
    have hE_lt : ‖E‖ < 1 := by
      rw [hE_formula, div_lt_one (mul_pos (by linarith only [hz_gt]) (by linarith only [hz2_gt]))]
      nlinarith only [hz1_lt, hz_gt, hz2_gt]
    linarith only [hE_gt5, hE_lt]
  have hre_le : z₀.re ≤ 1 / 2 := by
    by_contra hgt
    have hrx : 1 / 2 < z₀.re := not_le.mp hgt
    have hns : Complex.normSq (z₀ - 1) < Complex.normSq z₀ := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        sub_zero]
      linarith only [hrx]
    have hnum_lt : ‖z₀ - 1‖ < ‖z₀‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (z₀ - 1)), ← Real.sqrt_sq (norm_nonneg z₀)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by simpa [Complex.normSq_eq_norm_sq] using hns)
    have hz2_gt : 3 / 2 < ‖z₀ + 1‖ := by
      have := Complex.re_le_norm (z₀ + 1)
      simp only [Complex.add_re, Complex.one_re] at this
      linarith only [hrx, this]
    have hE_lt : ‖E‖ < 1 := by
      rw [hE_formula, div_lt_one (mul_pos (norm_pos_iff.mpr hz0) (by linarith only [hz2_gt]))]
      nlinarith only [hnum_lt, hz2_gt, norm_nonneg (z₀ - 1)]
    linarith only [hE_gt5, hE_lt]
  have hE_ne : E ≠ 0 := Complex.exp_ne_zero _
  have hquad : (z₀ + 1 / 2 - 1 / (2 * E)) ^ 2 = 1 / 4 - 3 / (2 * E) + 1 / (4 * E ^ 2) := by
    have hce : (z₀ - 1) / (z₀ * (z₀ + 1)) = E := hE_eq
    have heq1 : E * z₀ * (z₀ + 1) - (z₀ - 1) = 0 := by
      rw [div_eq_iff (mul_ne_zero hz0 hz2)] at hce; linear_combination -hce
    have heq2 : z₀ ^ 2 + (1 - 1 / E) * z₀ + 1 / E = 0 := by
      calc z₀ ^ 2 + (1 - 1 / E) * z₀ + 1 / E
          = (E * z₀ * (z₀ + 1) - (z₀ - 1)) / E := by field_simp [hE_ne]; ring
        _ = 0 := by rw [heq1, zero_div]
    linear_combination heq2
  have hinvE_lt : ‖1 / E‖ < 0.172 := by
    rw [one_div, norm_inv]
    have hlb : 3 + 2 * √2 < ‖E‖ := by
      rw [hE_norm, ← exp_two_pi_xiStar]
      exact Real.exp_lt_exp.mpr (by nlinarith only [Real.pi_pos, hre])
    have h582 : (5.82 : ℝ) < ‖E‖ := by linarith only [hlb, sqrt2_gt_slit]
    calc ‖E‖⁻¹ < 5.82⁻¹ := inv_strictAnti₀ (by norm_num) h582
      _ < 0.172 := by norm_num
  have hhalf_norm : ‖z₀ + 1 / 2‖ ≤ 0.85 := by
    have hsq_le : ‖z₀ + 1 / 2 - 1 / (2 * E)‖ ^ 2 < 0.75 ^ 2 := by
      rw [← norm_pow, hquad]
      calc ‖(1 / 4 : ℂ) - 3 / (2 * E) + 1 / (4 * E ^ 2)‖
          ≤ ‖(1 / 4 : ℂ) - 3 / (2 * E)‖ + ‖1 / (4 * E ^ 2)‖ := norm_add_le _ _
        _ ≤ (‖(1 / 4 : ℂ)‖ + ‖3 / (2 * E)‖) + ‖1 / (4 * E ^ 2)‖ := by gcongr; exact norm_sub_le _ _
        _ = 1 / 4 + (3 / 2) * ‖1 / E‖ + (1 / 4) * ‖1 / E‖ ^ 2 := by
            simp only [norm_div, norm_one, norm_pow, norm_mul]; norm_num; ring
        _ < 1 / 4 + (3 / 2) * 0.172 + (1 / 4) * 0.172 ^ 2 := by
            nlinarith only [hinvE_lt, norm_nonneg (1 / E)]
        _ < 0.75 ^ 2 := by norm_num
    have h1 : ‖z₀ + 1 / 2 - 1 / (2 * E)‖ < 0.75 := by
      nlinarith only [hsq_le, norm_nonneg (z₀ + 1 / 2 - 1 / (2 * E))]
    have h2 : ‖1 / (2 * E)‖ < 0.086 := by
      rw [show 1 / (2 * E) = (1 / 2 : ℂ) * (1 / E) by ring, norm_mul,
        show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      linarith only [hinvE_lt]
    have h3 := norm_add_le (z₀ + 1 / 2 - 1 / (2 * E)) (1 / (2 * E))
    rw [show (z₀ + 1 / 2 - 1 / (2 * E)) + 1 / (2 * E) = z₀ + 1 / 2 by ring] at h3
    linarith only [h1, h2, h3]
  have hy₀_le : z₀.im ≤ 0.85 := by
    have : z₀.im = (z₀ + 1 / 2).im := by simp
    rw [this]
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hhalf_norm)
  have hre_star_le : |z₀.re - sigmaStar| ≤ 0.95 := by
    have h1 : |(sigmaStar : ℝ) + 1 / 2| < 0.09 := by
      unfold sigmaStar; rw [abs_lt]; constructor <;> linarith only [sqrt2_gt_slit, sqrt2_lt_slit]
    have h2 : |z₀.re + 1 / 2| ≤ 0.85 := by
      have : z₀.re + 1 / 2 = (z₀ + 1 / 2).re := by simp
      rw [this]; exact (Complex.abs_re_le_norm _).trans hhalf_norm
    calc |z₀.re - sigmaStar| = |(z₀.re + 1 / 2) - (sigmaStar + 1 / 2)| := by ring_nf
      _ ≤ |z₀.re + 1 / 2| + |sigmaStar + 1 / 2| := abs_sub _ _
      _ ≤ 0.95 := by linarith only [h1, h2]
  exact ⟨hnorm_le2, h1_ge, hre_le, hy₀_le, hre_star_le⟩

private lemma confE_inv_im_id {z₀ b : ℂ} (hz₀ : 0 < z₀.im) (hb : confB z₀ = b) :
    z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 =
      Real.exp (-2 * π * b.re) * |Real.sin (2 * π * b.im)| ∧
    ‖z₀ * (z₀ + 1)‖ / ‖z₀ - 1‖ = Real.exp (-2 * π * b.re) := by
  have hz1 : z₀ - 1 ≠ 0 := (z0_im_ne_zero_triplet hz₀).2.1
  set E : ℂ := Complex.exp (2 * (π : ℂ) * b)
  have hE_eq : confE z₀ = E := by
    have h := exp_two_pi_mul_confB hz₀
    rw [hb] at h; exact h.symm
  have hE_norm : ‖E‖ = Real.exp (2 * π * b.re) := by
    dsimp [E]; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hE_formula : ‖E‖ = ‖z₀ - 1‖ / (‖z₀‖ * ‖z₀ + 1‖) := by
    rw [← hE_eq]; unfold confE; rw [norm_div, norm_mul]
  let w : ℂ := z₀ * (z₀ + 1) / (z₀ - 1)
  have hce : (z₀ - 1) / (z₀ * (z₀ + 1)) = Complex.exp (2 * (π : ℂ) * b) := hE_eq
  have hw_eq : w = Complex.exp (-(2 * (π : ℂ) * b)) := by
    dsimp [w]; rw [Complex.exp_neg, ← hce, inv_div]
  have hw_im1 : w.im = z₀.im * (z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2) / ‖z₀ - 1‖ ^ 2 := by
    dsimp [w]
    rw [Complex.div_im, ← Complex.normSq_eq_norm_sq (z₀ - 1)]
    have hns : Complex.normSq (z₀ - 1) = (z₀.re - 1) ^ 2 + z₀.im ^ 2 := by
      simp [Complex.normSq_apply]; ring
    have hnum : (z₀ * (z₀ + 1)).im * (z₀ - 1).re - (z₀ * (z₀ + 1)).re * (z₀ - 1).im =
        z₀.im * (z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    have hns_ne : Complex.normSq (z₀ - 1) ≠ 0 := (Complex.normSq_pos.mpr hz1).ne'
    field_simp [hns_ne]
    linear_combination hnum
  have hw_im2 : w.im = -(Real.exp (-2 * π * b.re) * Real.sin (2 * π * b.im)) := by
    rw [hw_eq]
    have hneg : -(2 * (π : ℂ) * b) =
        ((-2 * π * b.re : ℝ) : ℂ) + ((-2 * π * b.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hneg, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    rw [show -2 * π * b.im = -(2 * π * b.im) by ring, Real.sin_neg]
    ring
  have hw_im_id : z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 =
      Real.exp (-2 * π * b.re) * |Real.sin (2 * π * b.im)| := by
    have hw_abs : |w.im| = z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 := by
      rw [hw_im1, abs_div, abs_mul, abs_of_pos hz₀, abs_of_nonneg (sq_nonneg ‖z₀ - 1‖)]
    rw [hw_im2, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)] at hw_abs
    exact hw_abs.symm
  have hnorm_w_id : ‖z₀ * (z₀ + 1)‖ / ‖z₀ - 1‖ = Real.exp (-2 * π * b.re) := by
    have h1 : ‖z₀ * (z₀ + 1)‖ / ‖z₀ - 1‖ = ‖E‖⁻¹ := by
      rw [hE_formula, inv_div, norm_mul, mul_comm ‖z₀‖ ‖z₀ + 1‖]
    rw [h1, hE_norm, ← Real.exp_neg]; congr 1; ring
  exact ⟨hw_im_id, hnorm_w_id⟩

lemma z0_im_ratio_of_confB {z₀ b : ℂ} (hz₀ : 0 < z₀.im) (hb : confB z₀ = b)
    (hre : xiStar < b.re) (him_le : |b.im| ≤ 1 / 4) (him_ne : b.im ≠ 0) :
    ‖z₀ * (z₀ + 1)‖ / z₀.im ≤ 13 / |b.im| := by
  obtain ⟨hnorm_le2, h1_ge, _, _, _⟩ := z0_norm_re_im_bounds_of_confB hz₀ hb hre
  obtain ⟨hw_im_id, hnorm_w_id⟩ := confE_inv_im_id hz₀ hb
  have hsin_lb : 4 * |b.im| ≤ |Real.sin (2 * π * b.im)| := by
    have him_pos : 0 ≤ 2 * |b.im| := by positivity
    have him_half : 2 * |b.im| ≤ 1 / 2 := by linarith only [him_le]
    have hsin_abs : |Real.sin (2 * π * b.im)| = Real.sin (π * (2 * |b.im|)) := by
      have hpi := Real.pi_pos
      rcases le_or_gt 0 b.im with h | h
      · have hle_pi : 2 * π * b.im ≤ π := by nlinarith only [abs_le.mp him_le, hpi]
        rw [abs_of_nonneg h, show π * (2 * b.im) = 2 * π * b.im by ring,
          abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith only [h, hpi]) hle_pi)]
      · have hle_pi : π * (2 * |b.im|) ≤ π := by nlinarith only [him_half, hpi]
        have hpos_sin : 0 ≤ Real.sin (π * (2 * |b.im|)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hle_pi
        have hsn : Real.sin (2 * π * b.im) = -Real.sin (π * (2 * |b.im|)) := by
          rw [abs_of_neg h, show 2 * π * b.im = -(π * (2 * -b.im)) by ring, Real.sin_neg]
        rw [hsn, abs_neg, abs_of_nonneg hpos_sin]
    rw [hsin_abs]
    linarith only [sin_pi_t_ge_two_mul him_pos him_half]
  have hpoly_le13 : |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| ≤ 13 := by
    have hxr : |z₀.re| ≤ 2 := (Complex.abs_re_le_norm z₀).trans hnorm_le2
    have hxi : |z₀.im| ≤ 2 := (Complex.abs_im_le_norm z₀).trans hnorm_le2
    rw [abs_le]; constructor <;> nlinarith only [abs_le.mp hxr, abs_le.mp hxi, sq_nonneg z₀.re, sq_nonneg z₀.im]
  have hb_pos : 0 < |b.im| := abs_pos.mpr him_ne
  have hz1_pos : 0 < ‖z₀ - 1‖ := by linarith only [h1_ge]
  have heq_mul : ‖z₀ * (z₀ + 1)‖ * |Real.sin (2 * π * b.im)| =
      z₀.im * (|z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖) := by
    have h2 := congrArg (fun x => x * ‖z₀ - 1‖) hw_im_id
    have h3 : z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 * ‖z₀ - 1‖ =
        z₀.im * (|z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖) := by
      field_simp [hz1_pos.ne']
    rw [h3, ← hnorm_w_id] at h2
    have h4 : ‖z₀ * (z₀ + 1)‖ / ‖z₀ - 1‖ * |Real.sin (2 * π * b.im)| * ‖z₀ - 1‖ =
        ‖z₀ * (z₀ + 1)‖ * |Real.sin (2 * π * b.im)| := by
      field_simp [hz1_pos.ne']
    linarith only [h2, h4]
  have hnum_le : ‖z₀ * (z₀ + 1)‖ * (4 * |b.im|) ≤ z₀.im * 52 := by
    have h1 : ‖z₀ * (z₀ + 1)‖ * (4 * |b.im|) ≤ ‖z₀ * (z₀ + 1)‖ * |Real.sin (2 * π * b.im)| :=
      mul_le_mul_of_nonneg_left hsin_lb (norm_nonneg _)
    have h2 : |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ≤ 52 := by
      rw [div_le_iff₀ hz1_pos]; linarith only [hpoly_le13, h1_ge]
    have h3 : z₀.im * (|z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖) ≤ z₀.im * 52 :=
      mul_le_mul_of_nonneg_left h2 hz₀.le
    linarith only [h1, heq_mul, h3]
  rw [div_le_div_iff₀ hz₀ hb_pos]
  linarith only [hnum_le]

lemma z0_sigmaStar_sep_of_confB {z₀ b : ℂ} (hz₀ : 0 < z₀.im) (hb : confB z₀ = b)
    (hre : xiStar < b.re) (him_le : |b.im| ≤ 1 / 4) :
    (xiStar + 0.1 ≤ b.re → (0.01 : ℝ) ≤ ‖z₀ - (sigmaStar : ℂ)‖) ∧
    (b.re ≤ xiStar + 0.1 → |b.im| / 1000 ≤ z₀.im) := by
  obtain ⟨hnorm_le2, h1_ge, _, _, _⟩ := z0_norm_re_im_bounds_of_confB hz₀ hb hre
  obtain ⟨hw_im_id, _⟩ := confE_inv_im_id hz₀ hb
  have hE_eq : confE z₀ = Complex.exp (2 * (π : ℂ) * b) := by
    have h := exp_two_pi_mul_confB hz₀
    rw [hb] at h; exact h.symm
  have hE_norm : ‖Complex.exp (2 * (π : ℂ) * b)‖ = Real.exp (2 * π * b.re) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hE_formula : ‖Complex.exp (2 * (π : ℂ) * b)‖ = ‖z₀ - 1‖ / (‖z₀‖ * ‖z₀ + 1‖) := by
    rw [← hE_eq]; unfold confE; rw [norm_div, norm_mul]
  refine ⟨?_, ?_⟩
  · intro hfar
    by_contra hlt
    have hclose : ‖z₀ - (sigmaStar : ℂ)‖ < 0.01 := not_le.mp hlt
    have hsig_1 : 0.40 ≤ ‖(sigmaStar : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg sigmaStar_neg]
      unfold sigmaStar; linarith only [sqrt2_gt_slit]
    have hsig_p1 : 0.58 ≤ ‖(sigmaStar : ℂ) + 1‖ := by
      rw [show (sigmaStar : ℂ) + 1 = ((sigmaStar + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by unfold sigmaStar; linarith only [sqrt2_lt_slit])]
      unfold sigmaStar; linarith only [sqrt2_lt_slit]
    have hsig_m1 : ‖(sigmaStar : ℂ) - 1‖ ≤ 1.42 := by
      rw [show (sigmaStar : ℂ) - 1 = ((sigmaStar - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by unfold sigmaStar; linarith only [sqrt2_gt_slit])]
      unfold sigmaStar; linarith only [sqrt2_lt_slit]
    have hz_lo : 0.39 ≤ ‖z₀‖ := by
      have h2 := norm_add_le z₀ ((sigmaStar : ℂ) - z₀)
      have h1 : z₀ + ((sigmaStar : ℂ) - z₀) = (sigmaStar : ℂ) := by ring
      rw [h1, norm_sub_rev (sigmaStar : ℂ) z₀] at h2
      linarith only [hsig_1, h2, hclose]
    have hz_p1_lo : 0.57 ≤ ‖z₀ + 1‖ := by
      have h2 := norm_add_le (z₀ + 1) ((sigmaStar : ℂ) - z₀)
      have h1 : z₀ + 1 + ((sigmaStar : ℂ) - z₀) = (sigmaStar : ℂ) + 1 := by ring
      rw [h1, norm_sub_rev (sigmaStar : ℂ) z₀] at h2
      linarith only [hsig_p1, h2, hclose]
    have hz_m1_hi : ‖z₀ - 1‖ ≤ 1.43 := by
      have hadd := norm_add_le (z₀ - (sigmaStar : ℂ)) ((sigmaStar : ℂ) - 1)
      have h1 : (z₀ - (sigmaStar : ℂ)) + ((sigmaStar : ℂ) - 1) = z₀ - 1 := by ring
      rw [h1] at hadd
      linarith only [hadd, hclose, hsig_m1]
    have hE_ub : ‖Complex.exp (2 * (π : ℂ) * b)‖ ≤ 1.43 / (0.39 * 0.57) := by
      rw [hE_formula]
      exact div_le_div₀ (by norm_num) hz_m1_hi (by positivity)
        (mul_le_mul hz_lo hz_p1_lo (by norm_num) (by linarith only [hz_lo]))
    have hE_lb : 10 < ‖Complex.exp (2 * (π : ℂ) * b)‖ := by
      rw [hE_norm]
      have hpi := Real.pi_pos
      have hexp1 : Real.exp (2 * π * xiStar + 0.2 * π) ≤ Real.exp (2 * π * b.re) :=
        Real.exp_le_exp.mpr (by nlinarith only [hfar, hpi])
      rw [Real.exp_add, exp_two_pi_xiStar] at hexp1
      have h02 : (1.77 : ℝ) ≤ Real.exp (0.2 * π) := by
        have hp : 0.62 ≤ 0.2 * π := by nlinarith only [Real.pi_gt_d2]
        have he1 : (1.155 : ℝ) ≤ Real.exp 0.155 := by linarith only [Real.add_one_le_exp (0.155 : ℝ)]
        have hpow : (1.77 : ℝ) ≤ (1.155 : ℝ) ^ 4 := by norm_num
        have hpow2 : (1.155 : ℝ) ^ 4 ≤ Real.exp 0.155 ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
        have he4 : Real.exp 0.62 = Real.exp 0.155 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        have he3 : Real.exp 0.62 ≤ Real.exp (0.2 * π) := Real.exp_le_exp.mpr hp
        linarith only [hpow, hpow2, he4, he3]
      have h3 : (5.82 : ℝ) ≤ 3 + 2 * √2 := by linarith only [sqrt2_gt_slit]
      nlinarith only [hexp1, h02, h3]
    norm_num at hE_ub
    linarith only [hE_ub, hE_lb]
  · intro hnear
    have hpoly_le13 : |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| ≤ 13 := by
      have hxr : |z₀.re| ≤ 2 := (Complex.abs_re_le_norm z₀).trans hnorm_le2
      have hxi : |z₀.im| ≤ 2 := (Complex.abs_im_le_norm z₀).trans hnorm_le2
      rw [abs_le]; constructor <;> nlinarith only [abs_le.mp hxr, abs_le.mp hxi, sq_nonneg z₀.re, sq_nonneg z₀.im]
    have hsin_lb : 4 * |b.im| ≤ |Real.sin (2 * π * b.im)| := by
      have him_pos : 0 ≤ 2 * |b.im| := by positivity
      have him_half : 2 * |b.im| ≤ 1 / 2 := by linarith only [him_le]
      have hsin_abs : |Real.sin (2 * π * b.im)| = Real.sin (π * (2 * |b.im|)) := by
        have hpi := Real.pi_pos
        rcases le_or_gt 0 b.im with h | h
        · have hle_pi : 2 * π * b.im ≤ π := by nlinarith only [abs_le.mp him_le, hpi]
          rw [abs_of_nonneg h, show π * (2 * b.im) = 2 * π * b.im by ring,
            abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith only [h, hpi]) hle_pi)]
        · have hle_pi : π * (2 * |b.im|) ≤ π := by nlinarith only [him_half, hpi]
          have hpos_sin : 0 ≤ Real.sin (π * (2 * |b.im|)) :=
            Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hle_pi
          have hsn : Real.sin (2 * π * b.im) = -Real.sin (π * (2 * |b.im|)) := by
            rw [abs_of_neg h, show 2 * π * b.im = -(π * (2 * -b.im)) by ring, Real.sin_neg]
          rw [hsn, abs_neg, abs_of_nonneg hpos_sin]
      rw [hsin_abs]
      linarith only [sin_pi_t_ge_two_mul him_pos him_half]
    have hEinv_lb : (1 / 12 : ℝ) ≤ Real.exp (-2 * π * b.re) := by
      rw [show -2 * π * b.re = -(2 * π * b.re) by ring, Real.exp_neg, one_div]
      refine inv_anti₀ (Real.exp_pos _) ?_
      have hexp_ub : Real.exp (2 * π * b.re) ≤ Real.exp (2 * π * xiStar + 0.2 * π) :=
        Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hnear])
      rw [Real.exp_add, exp_two_pi_xiStar] at hexp_ub
      have h02 : Real.exp (0.2 * π) ≤ 2 := by
        have hpi4 : 0.2 * π ≤ 2 / 3 := by linarith only [Real.pi_lt_d4]
        have h4 := Real.exp_le_exp.mpr hpi4
        have he1 : Real.exp 1 ≤ 2.72 := by linarith only [Real.exp_one_lt_d9]
        have hcube : Real.exp (2 / 3 : ℝ) ^ 3 ≤ 2 ^ 3 := by
          have hpow1 : Real.exp (2 / 3 : ℝ) ^ 3 = Real.exp 1 ^ 2 := by
            rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
          rw [hpow1]
          have hpow2 : Real.exp 1 ^ 2 ≤ (2.72 : ℝ) ^ 2 :=
            pow_le_pow_left₀ (Real.exp_pos _).le he1 2
          have h2le : (2.72 : ℝ) ^ 2 ≤ 2 ^ 3 := by norm_num
          linarith only [hpow2, h2le]
        have hle2 : Real.exp (2 / 3 : ℝ) ≤ 2 := by
          by_contra hgt
          have h2lt : (2 : ℝ) < Real.exp (2 / 3 : ℝ) := not_le.mp hgt
          have h2cube : (2 : ℝ) ^ 3 < Real.exp (2 / 3 : ℝ) ^ 3 :=
            pow_lt_pow_left₀ h2lt (by norm_num) (by norm_num)
          linarith only [hcube, h2cube]
        linarith only [h4, hle2]
      have h583 : 3 + 2 * √2 ≤ 5.83 := by linarith only [sqrt2_lt_slit]
      have h3pos : (0 : ℝ) ≤ 3 + 2 * √2 := by positivity
      have hepos : 0 ≤ Real.exp (0.2 * π) := (Real.exp_pos _).le
      nlinarith only [hexp_ub, h02, h583, h3pos, hepos]
    have hlhs_le : z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| / ‖z₀ - 1‖ ^ 2 ≤
        208 * z₀.im := by
      have hz1_sq : (1 / 16 : ℝ) ≤ ‖z₀ - 1‖ ^ 2 := by nlinarith only [h1_ge]
      rw [div_le_iff₀ (by positivity)]
      calc z₀.im * |z₀.re ^ 2 - 2 * z₀.re - 1 + z₀.im ^ 2| ≤ z₀.im * 13 := by gcongr
        _ ≤ 208 * z₀.im * (1 / 16 : ℝ) := by linarith only
        _ ≤ 208 * z₀.im * ‖z₀ - 1‖ ^ 2 := by gcongr
    have hrhs_ge : |b.im| / 3 ≤ Real.exp (-2 * π * b.re) * |Real.sin (2 * π * b.im)| := by
      calc |b.im| / 3 = (1 / 12) * (4 * |b.im|) := by ring
        _ ≤ Real.exp (-2 * π * b.re) * |Real.sin (2 * π * b.im)| := by gcongr
    rw [hw_im_id] at hlhs_le
    linarith only [hlhs_le, hrhs_ge, hz₀, abs_nonneg b.im]

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.setIntegral_log_slitBoundaryMap_le_of_confB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.setIntegral_log_slitBoundaryMap_le_of_confB
