module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasGrowthBase

/-!
# Pointwise Poisson–Jensen strip bound for `boasH` on `1 ≤ |Im ζ| ≤ 2 log c'` (`cts:boas` Step 2)
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Upper.Comb

noncomputable section

private lemma log_integral_jensen_slit_local {x₀ y₀ B : ℝ} (hz₀_im : 0 < y₀) (_hB_pos : 0 < B)
    {f : ℝ → ℝ} (hf_pos_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ)
    (hf_pull_int : IntegrableOn (fun σ => f σ * poissonKernel x₀ y₀ σ) slitPreimage)
    (hlogf_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x₀ y₀ σ) slitPreimage)
    (hI_le : ∫ σ in slitPreimage, f σ * poissonKernel x₀ y₀ σ ≤ B) :
    ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ ≤
      slitMass x₀ y₀ * Real.log B + (1 - slitMass x₀ y₀) := by
  have hpk_int : Integrable (poissonKernel x₀ y₀) := integrable_poissonKernel x₀ hz₀_im
  set m : ℝ := slitMass x₀ y₀
  have hm_pos : 0 < m := by
    have hi : 0 < ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x₀ y₀ σ := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun σ => poissonKernel_nonneg (x := x₀) hz₀_im.le σ)
        hpk_int.integrableOn).mpr ?_
      have hsupp : Function.support (poissonKernel x₀ y₀) ∩ Ioo (-1 : ℝ) 0 = Ioo (-1) 0 := by
        ext σ; simp [poissonKernel_pos (x := x₀) hz₀_im σ |>.ne']
      rw [hsupp, Real.volume_Ioo]; norm_num
    exact hi.trans_le (setIntegral_mono_set hpk_int.integrableOn
      (Eventually.of_forall fun σ => poissonKernel_nonneg (x := x₀) hz₀_im.le σ)
      (ae_of_all _ fun _ hσ => Set.subset_union_left hσ))
  set I_f : ℝ := ∫ σ in slitPreimage, f σ * poissonKernel x₀ y₀ σ
  have hIf_pos : 0 < I_f := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hf_pull_int).mpr ?_
    · filter_upwards [hf_pos_ae] with σ hσ
      exact mul_nonneg hσ.le (poissonKernel_nonneg (x := x₀) hz₀_im.le σ)
    · have hIoo_sub : Ioo (-1 : ℝ) 0 ⊆ slitPreimage := Set.subset_union_left
      have hIoo_pos : 0 < volume (Ioo (-1 : ℝ) 0) := by rw [Real.volume_Ioo]; norm_num
      have hae_pos : ∀ᵐ σ ∂volume, σ ∈ Ioo (-1 : ℝ) 0 → 0 < f σ * poissonKernel x₀ y₀ σ := by
        have h1 : ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), 0 < f σ :=
          hf_pos_ae.filter_mono (ae_mono (Measure.restrict_mono hIoo_sub le_rfl))
        rw [ae_restrict_iff' measurableSet_Ioo] at h1
        filter_upwards [h1] with σ hσ hm
        exact mul_pos (hσ hm) (poissonKernel_pos (x := x₀) hz₀_im σ)
      by_contra h0
      have hzero : volume ((Function.support fun σ => f σ * poissonKernel x₀ y₀ σ) ∩ slitPreimage) = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp h0)
      have hnull1 : ∀ᵐ σ ∂volume, ¬(σ ∈ Ioo (-1 : ℝ) 0 ∧ f σ * poissonKernel x₀ y₀ σ ≠ 0) := by
        rw [← compl_mem_ae_iff] at hzero
        filter_upwards [hzero] with σ hσ ⟨h1, h2⟩
        exact hσ ⟨h2, hIoo_sub h1⟩
      have hsub_empty : ∀ᵐ σ ∂volume, σ ∉ Ioo (-1 : ℝ) 0 := by
        filter_upwards [hae_pos, hnull1] with σ hp hn hm
        exact hn ⟨hm, (hp hm).ne'⟩
      have hv0 : volume (Ioo (-1 : ℝ) 0) = 0 := by
        rw [ae_iff] at hsub_empty
        convert hsub_empty using 2
        ext σ; simp
      exact hIoo_pos.ne' hv0
  set c_avg : ℝ := I_f / m
  have hc_pos : 0 < c_avg := div_pos hIf_pos hm_pos
  have hlog_bd : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x₀ y₀ σ ≤
        (Real.log c_avg - 1) * poissonKernel x₀ y₀ σ + c_avg⁻¹ * (f σ * poissonKernel x₀ y₀ σ) := by
    filter_upwards [hf_pos_ae] with σ hσ
    have h1 : Real.log (f σ / c_avg) ≤ f σ / c_avg - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hσ hc_pos)
    rw [Real.log_div hσ.ne' hc_pos.ne'] at h1
    have h2 : Real.log (f σ) ≤ (Real.log c_avg - 1) + c_avg⁻¹ * f σ := by
      linarith [show f σ / c_avg = c_avg⁻¹ * f σ by ring]
    have hP0 := poissonKernel_nonneg (x := x₀) hz₀_im.le σ
    calc Real.log (f σ) * poissonKernel x₀ y₀ σ
        ≤ ((Real.log c_avg - 1) + c_avg⁻¹ * f σ) * poissonKernel x₀ y₀ σ := by gcongr
      _ = (Real.log c_avg - 1) * poissonKernel x₀ y₀ σ + c_avg⁻¹ * (f σ * poissonKernel x₀ y₀ σ) := by ring
  have hrhs_int : IntegrableOn
      (fun σ => (Real.log c_avg - 1) * poissonKernel x₀ y₀ σ + c_avg⁻¹ * (f σ * poissonKernel x₀ y₀ σ))
      slitPreimage :=
    (hpk_int.integrableOn.const_mul _).add (hf_pull_int.const_mul _)
  have hint_mono := setIntegral_mono_ae_restrict hlogf_int hrhs_int hlog_bd
  have heval : ∫ σ in slitPreimage,
        ((Real.log c_avg - 1) * poissonKernel x₀ y₀ σ + c_avg⁻¹ * (f σ * poissonKernel x₀ y₀ σ)) =
      m * Real.log (I_f / m) := by
    rw [integral_add (hpk_int.integrableOn.const_mul _) (hf_pull_int.const_mul _),
      integral_const_mul, integral_const_mul]
    change (Real.log c_avg - 1) * m + c_avg⁻¹ * I_f = m * Real.log (I_f / m)
    have hc_eq : c_avg⁻¹ * I_f = m := by dsimp [c_avg]; field_simp [hm_pos.ne', hIf_pos.ne']
    rw [hc_eq]; dsimp [c_avg]; ring
  have hdiv_le : m * Real.log (I_f / m) ≤ m * Real.log B + (1 - m) := by
    rw [div_eq_mul_inv, Real.log_mul hIf_pos.ne' (inv_ne_zero hm_pos.ne')]
    have hlogI : Real.log I_f ≤ Real.log B := Real.log_le_log hIf_pos hI_le
    have hlogm : Real.log m⁻¹ ≤ m⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hm_pos)
    have hm1 : m * Real.log m⁻¹ ≤ 1 - m := by
      calc m * Real.log m⁻¹ ≤ m * (m⁻¹ - 1) := mul_le_mul_of_nonneg_left hlogm hm_pos.le
        _ = 1 - m := by field_simp [hm_pos.ne']
    calc m * (Real.log I_f + Real.log m⁻¹) = m * Real.log I_f + m * Real.log m⁻¹ := by ring
      _ ≤ m * Real.log B + (1 - m) := add_le_add (mul_le_mul_of_nonneg_left hlogI hm_pos.le) hm1
  exact hint_mono.trans (heval.le.trans hdiv_le)

private lemma boasH_strip_pj_pos {c' C_e : ℝ} (hc10000 : 10000 ≤ c') (hCe : 0 < C_e)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (hedge_all : ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
      ‖hankelContinuation c' g b‖ ≤ C_e * virasoroProblem.cardyNorm (c' / 12) g)
    {w : ℂ} (hw : w ∈ zetaStrip c') (hre_w : 0 < w.re) (him1_w : 1 ≤ w.im)
    (hbim_le : |(bOfZeta c' w).im| ≤ 1 / 4) (hwG : hankelContinuation c' g (bOfZeta c' w) ≠ 0) :
    let C_slit : ℝ := 9 * Real.sqrt (2 * π) / xiStar
    let C_log : ℝ := max 0 (Real.log (2 * C_slit)) + 1 + max 0 (Real.log C_e) + 4 +
      (1 / 2 : ℝ) * Real.log (2 * π / 3) + (1 / 2 : ℝ) * Real.log 2 + 35
    let C₁ : ℝ := Real.exp C_log * (16 * 16)
    ‖boasH c' g w‖ ≤ C₁ * c' ^ 2 * ‖1 + w / (c' : ℂ)‖ ^ 3 * Real.exp (2 * π * w.im) := by
  intro C_slit C_log C₁
  have hc0 : 0 < c' := by linarith
  have hc1000 : 1000 ≤ c' := by linarith
  have hc8 : 8 ≤ c' := by linarith
  set b := bOfZeta c' w
  have hb_mem : b ∈ lowerBoasRightDom := bOfZeta_mem hc0 hw
  have hbw_im_pos : 0 < b.im := by
    rcases lt_trichotomy b.im 0 with hn | hz | hp
    · have hneg : (zetaRight c' b).im < 0 := by
        have hb_conj : starRingEnd ℂ b ∈ lowerBoasRightDom :=
          ⟨by simpa using hb_mem.1, by simpa using hb_mem.2⟩
        have hpos_conj := zetaRight_im_pos_of_im_pos hc0 hb_conj (by simpa using hn)
        have hc := congrArg Complex.im (zetaRight_conj hb_mem (c' := c'))
        simp only [Complex.conj_im] at hc; linarith only [hpos_conj, hc]
      rw [zetaRight_bOfZeta hc0 hw] at hneg; linarith
    · have heq : b = (b.re : ℂ) := Complex.ext rfl hz
      have hzr : (zetaRight c' b).im = 0 := by rw [heq, zetaRight_ofReal hb_mem.1]; simp
      rw [zetaRight_bOfZeta hc0 hw] at hzr; linarith
    · exact hp
  have hb_strip : b ∈ slitStrip := ⟨hb_mem.2, fun ⟨him, _⟩ => hbw_im_pos.ne' him⟩
  obtain ⟨z₀, hz₀_uhp, hz₀_eq⟩ := confB_surjOn hb_strip
  have hz₀_im : 0 < z₀.im := hz₀_uhp
  set x₀ := z₀.re; set y₀ := z₀.im
  set M := virasoroProblem.cardyNorm (c' / 12) g
  let F : ℂ → ℂ := fun z => (M⁻¹ : ℂ) * hankelContinuation c' g (confB z)
  let F_bdy : ℝ → ℂ := fun σ => (M⁻¹ : ℂ) * hankelContinuation c' g (confB (σ : ℂ))
  have hF_diff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} := fun z hz =>
    ((differentiableOn_hankelContinuation hc1000 hg).comp
      (fun u hu => (hasDerivAt_confB hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (confB_mem_slitStrip hu).1) z hz).const_mul _
  have hF_bd : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ C_e := fun z hz => by
    have hbd := hedge_all (confB_mem_slitStrip hz).1.le
    dsimp [F]; rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos]
    calc M⁻¹ * ‖hankelContinuation c' g (confB z)‖ ≤ M⁻¹ * (C_e * M) := by gcongr
      _ = C_e := by field_simp [hM_pos.ne']
  have hF_bdy : ∀ᵐ σ : ℝ ∂volume, Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (F_bdy σ)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hnot
    have hcontB := confB_continuousWithinAt_real hnot.2.1 hnot.2.2 hnot.1
    have htB : Tendsto confB (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝[{b : ℂ | |b.im| ≤ 1 / 2}] (confB (σ : ℂ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hcontB.tendsto.mono_left (nhdsWithin_mono _ fun z (hz : 0 < z.im) => hz.le), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (confB_mem_slitStrip hz).1.le
    have hcb_mem : confB (σ : ℂ) ∈ {b : ℂ | |b.im| ≤ 1 / 2} := by
      rcases lt_trichotomy σ (-1) with hm | rfl | hm1
      · simp [confB_real_im_of_lt_neg_one hm]
      · exact absurd rfl hnot.1
      · rcases lt_trichotomy σ 0 with h0 | rfl | h0
        · simp [confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1, h0⟩]
        · exact absurd rfl hnot.2.1
        · rcases lt_trichotomy σ 1 with h1 | rfl | h1
          · simp [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]
          · exact absurd rfl hnot.2.2
          · simp [confB_real_im_of_one_lt h1]
    exact tendsto_const_nhds.mul
      (((continuousOn_hankelContinuation hc1000 hg).continuousWithinAt hcb_mem).tendsto.comp htB)
  have hFz₀_ne : F z₀ ≠ 0 := by
    dsimp [F]; rw [hz₀_eq]; exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hwG
  obtain ⟨hPJ_int, hPJ_le⟩ := halfPlane_poissonJensen hCe hF_diff hF_bd hF_bdy hz₀_im hFz₀_ne
  change Integrable (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) at hPJ_int
  change Real.log ‖F z₀‖ ≤ ∫ σ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ at hPJ_le
  have hslit_confB : ∀ σ ∈ slitPreimage, confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := by
    intro σ hσ
    rcases hσ with (hIoo : σ ∈ Ioo (-1) 0) | (hIoi : 1 < σ)
    · exact Complex.ext (confB_real_re hIoo.2.ne (by linarith [hIoo.2]) hIoo.1.ne')
        (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
    · exact Complex.ext (confB_real_re (by linarith) hIoi.ne' (by linarith))
        (confB_real_im_of_one_lt hIoi)
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]; intro σ h1 h2
    rcases h1 with h1 | (h1 : 1 < σ)
    · rcases h2 with (h2 : σ < -1) | h2
      · linarith [h1.1]
      · linarith [h1.2, h2.1]
    · rcases h2 with (h2 : σ < -1) | h2
      · linarith
      · linarith [h2.2]
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    refine Filter.eventuallyEqSet_iff'.2 ?_
    change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
    rw [ae_iff]; refine measure_mono_null (fun σ hσ => ?_) hnull
    by_contra hnot; apply hσ; apply propext
    simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_or_gt_of_ne hnot.1 with hm | hm
    · exact Or.inr (Or.inl hm)
    · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
      · exact Or.inl (Or.inl ⟨hm, h0⟩)
      · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
        · exact Or.inr (Or.inr ⟨h0, h1⟩)
        · exact Or.inl (Or.inr h1)
  have hpk_int : Integrable (poissonKernel x₀ y₀) := integrable_poissonKernel x₀ hz₀_im
  set m : ℝ := slitMass x₀ y₀
  have hm_pos : 0 < m := by
    have hi : 0 < ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x₀ y₀ σ := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun σ => poissonKernel_nonneg (x := x₀) hz₀_im.le σ)
        hpk_int.integrableOn).mpr ?_
      have hsupp : Function.support (poissonKernel x₀ y₀) ∩ Ioo (-1 : ℝ) 0 = Ioo (-1) 0 := by
        ext σ; simp [poissonKernel_pos (x := x₀) hz₀_im σ |>.ne']
      rw [hsupp, Real.volume_Ioo]; norm_num
    exact hi.trans_le (setIntegral_mono_set hpk_int.integrableOn
      (Eventually.of_forall fun σ => poissonKernel_nonneg (x := x₀) hz₀_im.le σ)
      (ae_of_all _ fun _ hσ => Set.subset_union_left hσ))
  have hm_le : m ≤ 1 := by
    calc slitMass x₀ y₀ ≤ ∫ σ, poissonKernel x₀ y₀ σ :=
          setIntegral_le_integral hpk_int (Eventually.of_forall fun σ => poissonKernel_nonneg (x := x₀) hz₀_im.le σ)
      _ = 1 := integral_poissonKernel x₀ hz₀_im
  have htot : m + ∫ σ in edgePreimage, poissonKernel x₀ y₀ σ = 1 := by
    unfold m slitMass
    rw [← setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
      hpk_int.integrableOn hpk_int.integrableOn, setIntegral_congr_set hunion_ae, setIntegral_univ,
      integral_poissonKernel x₀ hz₀_im]
  have hsplit_eq : ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) +
        (∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set hunion_ae]
    exact setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
      hPJ_int.integrableOn hPJ_int.integrableOn
  have hedge_le : ∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤
      (1 - m) * max 0 (Real.log C_e) := by
    have hpt : ∀ σ ∈ edgePreimage,
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤ max 0 (Real.log C_e) * poissonKernel x₀ y₀ σ := by
      intro σ hσ
      have hbim_σ : |(confB (σ : ℂ)).im| ≤ 1 / 2 := by
        rcases hσ with (h : σ < -1) | ⟨h0, h1⟩
        · rw [confB_real_im_of_lt_neg_one h]; norm_num
        · rw [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]; norm_num
      have hbd_σ : ‖F_bdy σ‖ ≤ C_e := by
        dsimp [F_bdy]; rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos]
        calc M⁻¹ * ‖hankelContinuation c' g (confB (σ : ℂ))‖
            ≤ M⁻¹ * (C_e * M) := by gcongr; exact hedge_all hbim_σ
          _ = C_e := by field_simp [hM_pos.ne']
      have hP0 := poissonKernel_nonneg (x := x₀) hz₀_im.le σ
      rcases eq_or_lt_of_le (norm_nonneg (F_bdy σ)) with he0 | hpos
      · simp [← he0]; positivity
      · exact mul_le_mul_of_nonneg_right ((Real.log_le_log hpos hbd_σ).trans (le_max_right _ _)) hP0
    have hm1 := setIntegral_mono_on hPJ_int.integrableOn (hpk_int.integrableOn.const_mul _)
      (measurableSet_Iio.union measurableSet_Ioo) hpt
    rw [integral_const_mul] at hm1
    change ∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤
      max 0 (Real.log C_e) * ∫ σ in edgePreimage, poissonKernel x₀ y₀ σ at hm1
    have hce_nn : 0 ≤ max 0 (Real.log C_e) := le_max_left _ _
    nlinarith only [hm1, htot, hce_nn]
  let φ : ℝ → ℝ := fun t => (|g (c' * t ^ 2 / 3)| / M) * Bessel.besselI0 (c' * Bessel.besselL t)
  have hφ_cont : Continuous φ :=
    ((hg.cont.comp_continuous (by fun_prop) (fun t => by change 0 ≤ c' * t ^ 2 / 3; positivity)).abs.div_const M).mul
      (PoissonJensen.continuous_besselI0.comp (continuous_const.mul (by unfold Bessel.besselL; fun_prop)))
  have hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t := fun _ _ =>
    mul_nonneg (div_nonneg (abs_nonneg _) hM_pos.le) (zero_le_one.trans (Bessel.one_le_besselI0 _))
  obtain ⟨heS_int, heS_le⟩ := eSlitMass hc10000 hg
  have hφ_eq_on : EqOn φ (fun t => (|g (c' * t ^ 2 / 3)| * Bessel.besselK (c' / 12) (c' * t ^ 2 / 3)) / M) (Ioi xiStar) :=
    fun t ht => by
      have hK := Bessel.besselK_shift (c' := c') (x := t) (j := 0) hc0 (xiStar_pos.trans ht).le
      simp only [mul_zero, zero_div, sub_zero, Real.sqrt_one, mul_one] at hK
      dsimp [φ]; rw [← hK]; ring
  have hφ_int : IntegrableOn φ (Ioi xiStar) :=
    IntegrableOn.congr_fun (heS_int.div_const M) hφ_eq_on.symm measurableSet_Ioi
  have hIφ_le : 2 * ∫ t in Ioi xiStar, φ t ≤ 2 * C_slit * c'⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi hφ_eq_on, integral_div]
    calc 2 * ((∫ t in Ioi xiStar, |g (c' * t ^ 2 / 3)| * Bessel.besselK (c' / 12) (c' * t ^ 2 / 3)) / M)
        ≤ 2 * ((C_slit * c'⁻¹ * M) / M) := by gcongr
      _ = 2 * C_slit * c'⁻¹ := by field_simp [hM_pos.ne']
  obtain ⟨hf_pull_int, hf_pull_eq⟩ :=
    setIntegral_slitPreimage_div_slitDensity (x := x₀) hz₀_im hφ_cont.measurable hφ_nn hφ_int
  let K_val : ℝ → ℝ := fun σ => Bessel.besselI0 (c' * Bessel.besselL |slitBoundaryMap σ|)
  let f : ℝ → ℝ := fun σ => φ |slitBoundaryMap σ| / slitDensity x₀ y₀ σ
  have hK_pos : ∀ σ : ℝ, 0 < K_val σ := fun _ => lt_of_lt_of_le zero_lt_one (Bessel.one_le_besselI0 _)
  have hf_eq_Fbdy : ∀ σ ∈ slitPreimage, f σ = ‖F_bdy σ‖ * K_val σ / slitDensity x₀ y₀ σ := fun σ hσ => by
    dsimp [f, φ, K_val, F_bdy]
    rw [hslit_confB σ hσ, hankelContinuation_ofReal hc0 hg (slitBoundaryMap σ), norm_mul, norm_inv,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hM_pos,
      sq_abs]; ring
  have hG_ne_ae := hankelContinuation_bdy_ne_zero_ae_right hc1000 hg hb_mem.2 hwG
  have hf_pos_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ := by
    filter_upwards [hG_ne_ae, slitDensity_pos_ae (x := x₀) hz₀_im,
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hG hω hσ
    rw [hf_eq_Fbdy σ hσ]
    have hF_pos : 0 < ‖F_bdy σ‖ := by
      dsimp [F_bdy]; rw [hslit_confB σ hσ]
      exact norm_pos_iff.mpr (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hG)
    exact div_pos (mul_pos hF_pos (hK_pos σ)) hω
  obtain ⟨hlogB_int, hlogB_le⟩ := setIntegral_log_slitBoundaryMap_le_of_confB hz₀_im
  have hident := identification_integrand_integrable x₀ hz₀_im
  have hlogK_int : IntegrableOn (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    have hmeas_K : AEStronglyMeasurable (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ)
        (volume.restrict slitPreimage) :=
      ((Real.measurable_log.comp (PoissonJensen.continuous_besselI0.measurable.comp (measurable_const.mul
        ((by unfold Bessel.besselL; fun_prop : Continuous Bessel.besselL).measurable.comp
          measurable_slitBoundaryMap.abs)))).mul
        (continuous_poissonKernel x₀ hz₀_im).measurable).aestronglyMeasurable
    refine ((hident.const_mul (c' + 1 / 2)).add
      (hpk_int.integrableOn.const_mul (4 + (1 / 2 : ℝ) * (|Real.log c'| + |Real.log (2 * π * xiStar / 3)|)))).mono'
      hmeas_K ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hσ
    have hge : xiStar ≤ |slitBoundaryMap σ| := by
      rcases hσ with hIoo | hIoi
      · exact (xiStar_le_slitBoundaryMap hIoo).trans (le_abs_self _)
      · linarith [slitBoundaryMap_le_neg_xiStar hIoi, neg_abs_le (slitBoundaryMap σ)]
    have hasy := Bessel.log_besselK_asymptotic hc8 hge
    rw [show Bessel.besselK (c' / 12) (c' * |slitBoundaryMap σ| ^ 2 / 3) = K_val σ by
      simpa [K_val] using Bessel.besselK_shift (c' := c') (x := |slitBoundaryMap σ|) (j := 0) hc0
        (xiStar_pos.trans_le hge).le] at hasy
    have hbL : Bessel.besselL |slitBoundaryMap σ| = slitL (slitBoundaryMap σ) := rfl
    rw [hbL] at hasy
    have hL_ge : 2 * π * xiStar / 3 ≤ slitL (slitBoundaryMap σ) := by unfold slitL; gcongr
    have hL_pos : 0 < slitL (slitBoundaryMap σ) := lt_of_lt_of_le (by positivity [xiStar_pos]) hL_ge
    have hlogL : |Real.log (slitL (slitBoundaryMap σ))| ≤
        |Real.log (2 * π * xiStar / 3)| + slitL (slitBoundaryMap σ) := by
      have h1 := Real.log_le_log (by positivity [xiStar_pos]) hL_ge
      have h2 := Real.log_le_sub_one_of_pos hL_pos
      rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log (2 * π * xiStar / 3)), abs_nonneg (Real.log (2 * π * xiStar / 3))]
    have hlogcL : |Real.log (c' * slitL (slitBoundaryMap σ))| ≤
        |Real.log c'| + |Real.log (2 * π * xiStar / 3)| + slitL (slitBoundaryMap σ) := by
      rw [Real.log_mul hc0.ne' hL_pos.ne']
      linarith only [abs_add_le (Real.log c') (Real.log (slitL (slitBoundaryMap σ))), hlogL]
    have hlogK_bd : |Real.log (K_val σ)| ≤ (c' + 1 / 2) * slitL (slitBoundaryMap σ) +
        (4 + (1 / 2 : ℝ) * (|Real.log c'| + |Real.log (2 * π * xiStar / 3)|)) := by
      have h1 : |Real.log (K_val σ)| ≤ |c' * slitL (slitBoundaryMap σ) - 1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ))| + 4 :=
        by linarith [abs_sub_abs_le_abs_sub (Real.log (K_val σ)) (c' * slitL (slitBoundaryMap σ) - 1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ)))]
      have h2 : |c' * slitL (slitBoundaryMap σ) - 1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ))| ≤
          c' * slitL (slitBoundaryMap σ) + 1 / 2 * |Real.log (c' * slitL (slitBoundaryMap σ))| := by
        calc _ ≤ |c' * slitL (slitBoundaryMap σ)| + |1 / 2 * Real.log (c' * slitL (slitBoundaryMap σ))| := abs_sub _ _
          _ = c' * slitL (slitBoundaryMap σ) + 1 / 2 * |Real.log (c' * slitL (slitBoundaryMap σ))| := by
              rw [abs_of_pos (mul_pos hc0 hL_pos), abs_mul, abs_of_pos (by norm_num)]
      linarith
    have hP0 := poissonKernel_nonneg (x := x₀) hz₀_im.le σ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    exact (mul_le_mul_of_nonneg_right hlogK_bd hP0).trans_eq (by simp only [Pi.add_apply]; ring)
  have hlogω_int : IntegrableOn (fun σ => Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    (integrableOn_poisson_mul_log_slitDensity x₀ hz₀_im).congr_fun
      (fun _ _ => by dsimp only; ring) (measurableSet_Ioo.union measurableSet_Ioi)
  have hlogf_eq_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x₀ y₀ σ = Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
        Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ +
        Real.log (K_val σ) * poissonKernel x₀ y₀ σ := by
    filter_upwards [hG_ne_ae, slitDensity_pos_ae (x := x₀) hz₀_im,
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hG hω hσ
    rw [hf_eq_Fbdy σ hσ]
    have hF_pos : 0 < ‖F_bdy σ‖ := by
      dsimp [F_bdy]; rw [hslit_confB σ hσ]
      exact norm_pos_iff.mpr (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hG)
    rw [Real.log_div (mul_pos hF_pos (hK_pos σ)).ne' hω.ne', Real.log_mul hF_pos.ne' (hK_pos σ).ne']; ring
  have hlogf_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    ((hPJ_int.integrableOn.sub hlogω_int).add hlogK_int).congr (by filter_upwards [hlogf_eq_ae] with σ h; exact h.symm)
  have hjensen := log_integral_jensen_slit_local hz₀_im (by dsimp [C_slit]; positivity [xiStar_pos])
    hf_pos_ae hf_pull_int hlogf_int (hf_pull_eq.le.trans hIφ_le)
  have hB_eq : Real.log (2 * C_slit * c'⁻¹) = Real.log (2 * C_slit) - Real.log c' := by
    rw [Real.log_mul (by dsimp [C_slit]; positivity [xiStar_pos]) (inv_ne_zero hc0.ne'), Real.log_inv]; ring
  have hm_cs : m * Real.log (2 * C_slit) ≤ max 0 (Real.log (2 * C_slit)) := by
    calc m * Real.log (2 * C_slit) ≤ m * max 0 (Real.log (2 * C_slit)) :=
          mul_le_mul_of_nonneg_left (le_max_right 0 _) hm_pos.le
      _ ≤ 1 * max 0 (Real.log (2 * C_slit)) := mul_le_mul_of_nonneg_right hm_le (le_max_left _ _)
      _ = max 0 (Real.log (2 * C_slit)) := one_mul _
  rw [hB_eq, mul_sub] at hjensen
  have hjensen2 : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ ≤
      max 0 (Real.log (2 * C_slit)) - m * Real.log c' + (1 - m) := by linarith only [hjensen, hm_cs]
  have hdecomp : ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ) +
        (∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) -
        (∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) := by
    have hadd := integral_add (hlogf_int.add hlogω_int) hlogK_int.neg
    have hadd2 := integral_add hlogf_int hlogω_int
    have heq_f : ∀ᵐ σ ∂(volume.restrict slitPreimage),
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
          Real.log (f σ) * poissonKernel x₀ y₀ σ +
            Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ -
            Real.log (K_val σ) * poissonKernel x₀ y₀ σ := by
      filter_upwards [hlogf_eq_ae] with σ h; linarith
    calc ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ
        = ∫ σ in slitPreimage,
            (Real.log (f σ) * poissonKernel x₀ y₀ σ +
              Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) +
              -(Real.log (K_val σ) * poissonKernel x₀ y₀ σ) :=
            integral_congr_ae (by filter_upwards [heq_f] with σ h; linarith)
      _ = (∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ +
              Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) +
            ∫ σ in slitPreimage, -(Real.log (K_val σ) * poissonKernel x₀ y₀ σ) := hadd
      _ = (∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ) +
            (∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) -
            (∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) := by
          rw [hadd2, integral_neg, sub_eq_add_neg]
  have hentropy : ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ ≤
      slitEntropy x₀ y₀ := by
    calc ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ
        = ∫ σ in slitPreimage, poissonKernel x₀ y₀ σ * Real.log (slitDensity x₀ y₀ σ) :=
          integral_congr_ae (Eventually.of_forall fun σ => by ring)
      _ ≤ slitEntropy x₀ y₀ := setIntegral_poisson_mul_log_slitDensity_le_entropy x₀ hz₀_im
  have hlogK_lb : -(∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) ≤
      c' * majorant2D b + ((1 / 2 : ℝ) * Real.log c' + 4 + (1 / 2 : ℝ) * Real.log (2 * π / 3)) * m +
        (1 / 2 : ℝ) * (Real.log (|b.re| + 3 / 2) + Real.log 2) := by
    let rhs1 : ℝ → ℝ := fun σ => c' * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ)
    let rhs2 : ℝ → ℝ := fun σ =>
      (1 / 2 * Real.log c' + 4 + 1 / 2 * Real.log (2 * π / 3)) * poissonKernel x₀ y₀ σ
    let rhs3 : ℝ → ℝ := fun σ => (1 / 2 : ℝ) * (Real.log |slitBoundaryMap σ| * poissonKernel x₀ y₀ σ)
    let rhs : ℝ → ℝ := fun σ => rhs1 σ - rhs2 σ - rhs3 σ
    have hr12 : IntegrableOn (fun σ => rhs1 σ - rhs2 σ) slitPreimage :=
      (hident.const_mul c').sub (hpk_int.integrableOn.const_mul _)
    have hrhs_int : IntegrableOn rhs slitPreimage := hr12.sub (hlogB_int.const_mul _)
    have hpt : ∀ σ ∈ slitPreimage, rhs σ ≤ Real.log (K_val σ) * poissonKernel x₀ y₀ σ := by
      intro σ hσ
      have hge : xiStar ≤ |slitBoundaryMap σ| := by
        rcases hσ with hIoo | hIoi
        · exact (xiStar_le_slitBoundaryMap hIoo).trans (le_abs_self _)
        · linarith [slitBoundaryMap_le_neg_xiStar hIoi, neg_abs_le (slitBoundaryMap σ)]
      have hasy := (abs_le.mp (Bessel.log_besselK_asymptotic hc8 hge)).1
      rw [show Bessel.besselK (c' / 12) (c' * |slitBoundaryMap σ| ^ 2 / 3) = K_val σ by
        simpa [K_val] using Bessel.besselK_shift (c' := c') (x := |slitBoundaryMap σ|) (j := 0) hc0
          (xiStar_pos.trans_le hge).le] at hasy
      have hL_eq : Bessel.besselL |slitBoundaryMap σ| = (2 * π / 3) * |slitBoundaryMap σ| := by
        unfold Bessel.besselL; ring
      have hL_slit : slitL (slitBoundaryMap σ) = (2 * π / 3) * |slitBoundaryMap σ| := by
        unfold slitL; ring
      have hlogcL : Real.log (c' * Bessel.besselL |slitBoundaryMap σ|) =
          Real.log c' + Real.log (2 * π / 3) + Real.log |slitBoundaryMap σ| := by
        have habs_pos : 0 < |slitBoundaryMap σ| := xiStar_pos.trans_le hge
        rw [hL_eq, Real.log_mul hc0.ne' (by positivity), Real.log_mul (by positivity) habs_pos.ne']; ring
      rw [hlogcL, hL_eq, ← hL_slit] at hasy
      have hP0 := poissonKernel_nonneg (x := x₀) hz₀_im.le σ
      have hK_low : c' * slitL (slitBoundaryMap σ) -
          (1 / 2 * Real.log c' + 4 + 1 / 2 * Real.log (2 * π / 3)) -
          (1 / 2) * Real.log |slitBoundaryMap σ| ≤ Real.log (K_val σ) := by linarith only [hasy]
      calc rhs σ
          = (c' * slitL (slitBoundaryMap σ) -
              (1 / 2 * Real.log c' + 4 + 1 / 2 * Real.log (2 * π / 3)) -
              (1 / 2) * Real.log |slitBoundaryMap σ|) * poissonKernel x₀ y₀ σ := by
            dsimp [rhs, rhs1, rhs2, rhs3]; ring
        _ ≤ Real.log (K_val σ) * poissonKernel x₀ y₀ σ := mul_le_mul_of_nonneg_right hK_low hP0
    have hmono := setIntegral_mono_on hrhs_int hlogK_int (measurableSet_Ioo.union measurableSet_Ioi) hpt
    have hrhs_eval : ∫ σ in slitPreimage, rhs σ =
        c' * (∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) -
          (1 / 2 * Real.log c' + 4 + 1 / 2 * Real.log (2 * π / 3)) * m -
          (1 / 2 : ℝ) * (∫ σ in slitPreimage, Real.log |slitBoundaryMap σ| * poissonKernel x₀ y₀ σ) := by
      change ∫ σ in slitPreimage, (rhs1 σ - rhs2 σ) - rhs3 σ = _
      rw [integral_sub hr12 (hlogB_int.const_mul _),
        integral_sub (hident.const_mul c') (hpk_int.integrableOn.const_mul _)]
      rw [integral_const_mul, integral_const_mul, integral_const_mul]
      rfl
    rw [hrhs_eval] at hmono
    have hharm : -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ = majorant2D b := by
      rw [← hz₀_eq]; exact (harmonicMajorantIdentification_complex hz₀_im).symm
    have hharm_eq : ∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ = -majorant2D b := by
      linarith only [hharm]
    rw [hharm_eq] at hmono
    rw [hz₀_eq] at hlogB_le
    linarith only [hmono, hlogB_le]
  have hslit_ent : slitEntropy x₀ y₀ ≤ 35 + 2 * Real.log (1 / |b.im|) :=
    slitEntropy_le_of_confB hz₀_im hz₀_eq hb_mem.1 hbim_le hbw_im_pos.ne'
  have hF_log : Real.log ‖F z₀‖ = Real.log ‖hankelContinuation c' g b‖ - Real.log M := by
    dsimp [F]; rw [hz₀_eq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos,
      Real.log_mul (inv_ne_zero hM_pos.ne') (norm_ne_zero_iff.mpr hwG), Real.log_inv]; ring
  rw [hF_log, hsplit_eq] at hPJ_le
  have hlogG_le : Real.log (M⁻¹ * ‖hankelContinuation c' g b‖) ≤
      c' * majorant2D b + (1 / 2 * Real.log c' * m - m * Real.log c') +
        (1 / 2 : ℝ) * Real.log (|b.re| + 3 / 2) + 2 * Real.log (1 / |b.im|) +
        (max 0 (Real.log (2 * C_slit)) + 1 + max 0 (Real.log C_e) + 4 +
          1 / 2 * Real.log (2 * π / 3) + 1 / 2 * Real.log 2 + 35) := by
    rw [Real.log_mul (inv_ne_zero hM_pos.ne') (norm_ne_zero_iff.mpr hwG), Real.log_inv]
    have h1_m : (1 - m) * max 0 (Real.log C_e) ≤ max 0 (Real.log C_e) := by
      have hce0 : 0 ≤ max 0 (Real.log C_e) := le_max_left _ _
      nlinarith only [hm_pos, hm_le, hce0]
    have h4m : (4 + 1 / 2 * Real.log (2 * π / 3)) * m ≤ 4 + 1 / 2 * Real.log (2 * π / 3) := by
      have hpi3 : 1 ≤ 2 * π / 3 := by linarith only [Real.pi_gt_three]
      have hnn : 0 ≤ 4 + 1 / 2 * Real.log (2 * π / 3) := by
        have := Real.log_nonneg hpi3; positivity
      nlinarith only [hm_pos, hm_le, hnn]
    have hdistrib : (1 / 2 * Real.log c' + 4 + 1 / 2 * Real.log (2 * π / 3)) * m =
        1 / 2 * Real.log c' * m + (4 + 1 / 2 * Real.log (2 * π / 3)) * m := by ring
    linarith only [hPJ_le, hedge_le, hdecomp, hjensen2, hentropy, hlogK_lb, hslit_ent, h1_m, h4m, hdistrib, hm_pos]
  have hmaj_eq : c' * majorant2D b + (2 * π / 3) * c' * b.re = 2 * π * w.im := by
    have hm_eq := majorantUExt_bOfZeta hc0 hw
    have huext : majorantUExt b = majorant2D b := by
      unfold majorantUExt
      have h1 : |b.im| ≠ 1 / 2 := hb_mem.2.ne
      have h2 : ¬ (b.im = 0 ∧ xiStar ≤ |b.re|) := fun h => hbw_im_pos.ne' h.1
      rw [ite_eq_right h1, ite_eq_right h2]
    rw [huext] at hm_eq
    rw [abs_of_pos (by linarith : 0 < w.im)] at hm_eq
    linarith only [hm_eq]
  obtain ⟨_, habs_b, hb1_le, _⟩ := bOfZeta_re_bounds hc0 hw hre_w.le
  have hbim_inv : 1 / |b.im| ≤ (8 / 3 : ℝ) * c' * ‖1 + w / (c' : ℂ)‖ := by
    have hle_im := zetaRight_im_abs_le hc0 hb_mem
    rw [zetaRight_bOfZeta hc0 hw, abs_of_pos (by linarith : 0 < w.im)] at hle_im
    have h1 : 1 ≤ (2 * c' / 3) * |b.im| * (b.re + 1) := him1_w.trans hle_im
    have hb_pos_im : 0 < |b.im| := abs_pos.mpr hbw_im_pos.ne'
    rw [div_le_iff₀ hb_pos_im]
    calc 1 ≤ (2 * c' / 3) * |b.im| * (b.re + 1) := h1
      _ ≤ (2 * c' / 3) * |b.im| * (4 * ‖1 + w / (c' : ℂ)‖) := by gcongr
      _ = (8 / 3 : ℝ) * c' * ‖1 + w / (c' : ℂ)‖ * |b.im| := by ring
  have hnorm1 : 1 ≤ ‖1 + w / (c' : ℂ)‖ := by
    have h1 : (1 + w / (c' : ℂ)).re = 1 + w.re / c' := by simp [Complex.div_ofReal_re]
    have h2 := Complex.re_le_norm (1 + w / (c' : ℂ))
    linarith only [h1, h2, div_nonneg hre_w.le hc0.le]
  have hlog_bim : 2 * Real.log (1 / |b.im|) ≤
      2 * Real.log (8 / 3) + 2 * Real.log c' + 2 * Real.log ‖1 + w / (c' : ℂ)‖ := by
    have h1 : Real.log (1 / |b.im|) ≤ Real.log ((8 / 3 : ℝ) * c' * ‖1 + w / (c' : ℂ)‖) :=
      Real.log_le_log (one_div_pos.mpr (abs_pos.mpr hbw_im_pos.ne')) hbim_inv
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hc0.ne'] at h1
    linarith only [h1]
  have hlog_bre : (1 / 2 : ℝ) * Real.log (|b.re| + 3 / 2) ≤
      (1 / 2 : ℝ) * Real.log 4 + Real.log ‖1 + w / (c' : ℂ)‖ := by
    have h1 : Real.log (|b.re| + 3 / 2) ≤ Real.log (4 * ‖1 + w / (c' : ℂ)‖) :=
      Real.log_le_log (by linarith only [abs_nonneg b.re]) habs_b
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    have hnn : 0 ≤ Real.log ‖1 + w / (c' : ℂ)‖ := Real.log_nonneg hnorm1
    linarith only [h1, hnn]
  have hm_c_nn : 1 / 2 * Real.log c' * m - m * Real.log c' ≤ 0 := by
    have hc1 : 0 ≤ Real.log c' := Real.log_nonneg (by linarith)
    nlinarith only [hm_pos, hc1]
  have hC1_eq : Real.exp (C_log + 2 * Real.log (8 / 3) + 1 / 2 * Real.log 4) ≤ C₁ := by
    have h1 : Real.exp (2 * Real.log (8 / 3)) = (8 / 3 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) * Real.log (8 / 3) = ((2 : ℕ) : ℝ) * Real.log (8 / 3) by norm_num,
        ← Real.log_pow, Real.exp_log (by positivity)]
    have h2 : Real.exp (1 / 2 * Real.log 4) = 2 := by
      rw [show (1 / 2 : ℝ) * Real.log 4 = Real.log (2 : ℝ) by
        rw [show (4 : ℝ) = ((2 : ℝ) ^ (2 : ℕ)) by norm_num, Real.log_pow]; norm_num; ring,
        Real.exp_log (by norm_num)]
    rw [Real.exp_add, Real.exp_add, h1, h2]
    dsimp [C₁]
    nlinarith only [Real.exp_pos C_log]
  have hlog_H : Real.log ‖boasH c' g w‖ ≤
      Real.log C₁ + 2 * Real.log c' + 3 * Real.log ‖1 + w / (c' : ℂ)‖ + 2 * π * w.im := by
    have hH_norm : ‖boasH c' g w‖ =
        M⁻¹ * ‖hankelContinuation c' g b‖ * Real.exp ((2 * π / 3) * c' * b.re) := by
      unfold boasH
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos,
        Complex.norm_exp, show (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * b).re = (2 * π / 3) * c' * b.re by
          simp [Complex.mul_re]]
    have hH_log : Real.log ‖boasH c' g w‖ =
        Real.log (M⁻¹ * ‖hankelContinuation c' g b‖) + (2 * π / 3) * c' * b.re := by
      rw [hH_norm, Real.log_mul (mul_pos (inv_pos.mpr hM_pos) (norm_pos_iff.mpr hwG)).ne'
        (Real.exp_pos _).ne', Real.log_exp]
    have hC_log : C_log + 2 * Real.log (8 / 3) + 1 / 2 * Real.log 4 ≤ Real.log C₁ := by
      calc C_log + 2 * Real.log (8 / 3) + 1 / 2 * Real.log 4
          = Real.log (Real.exp (C_log + 2 * Real.log (8 / 3) + 1 / 2 * Real.log 4)) := (Real.log_exp _).symm
        _ ≤ Real.log C₁ := Real.log_le_log (Real.exp_pos _) hC1_eq
    dsimp [C_log] at hC_log
    linarith only [hH_log, hlogG_le, hmaj_eq, hlog_bim, hlog_bre, hm_c_nn, hC_log]
  have hH_pos : 0 < ‖boasH c' g w‖ := by
    unfold boasH
    exact norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hwG)
      (Complex.exp_ne_zero _))
  rw [← Real.exp_log hH_pos]
  calc Real.exp (Real.log ‖boasH c' g w‖)
      ≤ Real.exp (Real.log C₁ + 2 * Real.log c' + 3 * Real.log ‖1 + w / (c' : ℂ)‖ + 2 * π * w.im) :=
        Real.exp_le_exp.mpr hlog_H
    _ = C₁ * c' ^ 2 * ‖1 + w / (c' : ℂ)‖ ^ 3 * Real.exp (2 * π * w.im) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by dsimp [C₁]; positivity),
          show (2 : ℝ) * Real.log c' = ((2 : ℕ) : ℝ) * Real.log c' by norm_num,
          show (3 : ℝ) * Real.log ‖1 + w / (c' : ℂ)‖ = ((3 : ℕ) : ℝ) * Real.log ‖1 + w / (c' : ℂ)‖ by norm_num,
          ← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity)]

theorem boasH_strip_pj :
    ∃ c₀ C₁ : ℝ, 10000 ≤ c₀ ∧ 0 < C₁ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g → (∃ t ≥ 0, g t ≠ 0) →
      ∀ {ζ : ℂ}, 0 < ζ.re → 1 ≤ |ζ.im| → |ζ.im| ≤ 2 * Real.log c' →
        ζ ∈ zetaStrip c' ∧
          ‖boasH c' g ζ‖ ≤ C₁ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 * Real.exp (2 * π * |ζ.im|) := by
  obtain ⟨c_e, C_e, _, hc_e, hC_e, _, h_edge⟩ := edge_hankel_one_virasoro
  have hev_bim : ∀ᶠ c' : ℝ in atTop, 2 * Real.log c' < c' / 48000 := by
    have ht := (Real.isLittleO_log_id_atTop).bound (c := 1 / 96001) (by positivity)
    filter_upwards [eventually_gt_atTop (1 : ℝ), ht] with c' hc1 hlog
    dsimp at hlog
    rw [abs_of_nonneg (Real.log_pos hc1).le, abs_of_nonneg (by linarith)] at hlog
    linarith
  obtain ⟨c_lim, hc_lim⟩ := eventually_atTop.mp hev_bim
  let C_slit : ℝ := 9 * Real.sqrt (2 * π) / xiStar
  let C_log : ℝ := max 0 (Real.log (2 * C_slit)) + 1 + max 0 (Real.log C_e) + 4 +
    (1 / 2 : ℝ) * Real.log (2 * π / 3) + (1 / 2 : ℝ) * Real.log 2 + 35
  let C₁ : ℝ := Real.exp C_log * (16 * 16)
  refine ⟨max 10000 (max c_e c_lim), C₁, le_max_left _ _, by positivity,
    fun {c'} hc' {g} hg hnz {ζ} hre him1 him2 => ?_⟩
  have hc10000 : 10000 ≤ c' := (le_max_left _ _).trans hc'
  have hc_e_le : c_e ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc_lim_le : c_lim ≤ c' := ((le_max_right _ _).trans (le_max_right _ _)).trans hc'
  have hc0 : 0 < c' := by linarith
  have hc1000 : 1000 ≤ c' := by linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero (by rw [virasoroProblem_totalShift]; linarith) hg hnz
  have hζ_mem : ζ ∈ zetaStrip c' := mem_zetaStrip_of_log_im hc10000 hre him2
  refine ⟨hζ_mem, ?_⟩
  have hbim_of : ∀ {w : ℂ}, w ∈ zetaStrip c' → |w.im| ≤ 2 * Real.log c' → |(bOfZeta c' w).im| ≤ 1 / 4 := by
    intro w hw him_w
    set b := bOfZeta c' w
    have hb_mem := bOfZeta_mem hc0 hw
    by_contra hgt
    have h14 : 1 / 4 < |b.im| := not_le.mp hgt
    have hnorm_ge : 1 / 4 ≤ ‖b - (xiStar : ℂ)‖ := by
      have him_abs := Complex.abs_im_le_norm (b - (xiStar : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him_abs
      exact h14.le.trans him_abs
    have hsq_ge : 1 / 2 ≤ Real.sqrt (‖b - (xiStar : ℂ)‖ * (1 + b.re)) := by
      have hre1 : 1 ≤ 1 + b.re := by linarith [hb_mem.1, xiStar_pos]
      have : 1 / 4 ≤ ‖b - (xiStar : ℂ)‖ * (1 + b.re) := by nlinarith
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2), show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
      exact Real.sqrt_le_sqrt this
    have hge_im := zetaRight_im_abs_ge hc0 hb_mem
    rw [zetaRight_bOfZeta hc0 hw] at hge_im
    have hbad : c' / 48000 ≤ |w.im| := by
      have : (c' / 6000) * (1 / 4) * (1 / 2) ≤ (c' / 6000) * |b.im| *
          Real.sqrt (‖b - (xiStar : ℂ)‖ * (1 + b.re)) := by gcongr
      linarith
    linarith [hc_lim c' hc_lim_le]
  by_cases hG0 : hankelContinuation c' g (bOfZeta c' ζ) = 0
  · have hb0 : boasH c' g ζ = 0 := by unfold boasH; rw [hG0, mul_zero, zero_mul]
    rw [hb0, norm_zero]; positivity
  · rcases le_or_gt 0 ζ.im with him_nn | him_neg
    · have him1_pos : 1 ≤ ζ.im := by rwa [abs_of_nonneg him_nn] at him1
      rw [abs_of_nonneg him_nn]
      exact boasH_strip_pj_pos hc10000 hC_e hg hM_pos (fun hb => (h_edge hc_e_le hg).2.2 hb)
        hζ_mem hre him1_pos (hbim_of hζ_mem him2) hG0
    · set ζ' := starRingEnd ℂ ζ
      have hζ'_mem : ζ' ∈ zetaStrip c' := conj_mem_zetaStrip hζ_mem
      have hre' : 0 < ζ'.re := by simpa [ζ'] using hre
      have him1' : 1 ≤ ζ'.im := by
        have : ζ'.im = -ζ.im := by simp [ζ']
        rw [this]; rw [abs_of_neg him_neg] at him1; exact him1
      have him2' : |ζ'.im| ≤ 2 * Real.log c' := by
        simpa [ζ', abs_neg] using him2
      have hG0' : hankelContinuation c' g (bOfZeta c' ζ') ≠ 0 := by
        intro h0
        have hconj := hankelContinuation_conj hc1000 hg (bOfZeta_mem hc0 hζ_mem).2.le
        rw [← bOfZeta_conj hc0 hζ_mem] at hconj
        rw [h0] at hconj
        exact hG0 (by simpa using congrArg (starRingEnd ℂ) hconj.symm)
      have hbd' := boasH_strip_pj_pos hc10000 hC_e hg hM_pos (fun hb => (h_edge hc_e_le hg).2.2 hb)
        hζ'_mem hre' him1' (hbim_of hζ'_mem him2') hG0'
      have hconj_H : ‖boasH c' g ζ‖ = ‖boasH c' g ζ'‖ := by
        dsimp [ζ']; rw [boasH_conj hc1000 hg hζ_mem, Complex.norm_conj]
      have hconj_fac : ‖1 + ζ' / (c' : ℂ)‖ = ‖1 + ζ / (c' : ℂ)‖ := by
        have : 1 + ζ' / (c' : ℂ) = starRingEnd ℂ (1 + ζ / (c' : ℂ)) := by
          simp [ζ', map_add, map_div₀, Complex.conj_ofReal]
        rw [this, Complex.norm_conj]
      have him_eq : ζ'.im = |ζ.im| := by simp [ζ', abs_of_neg him_neg]
      rw [hconj_H, ← him_eq, ← hconj_fac]
      exact hbd'

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boasH_strip_pj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boasH_strip_pj
