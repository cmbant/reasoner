/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_1_Strip
public import FormalResearch.ModularBootstrap.Blowup.Majorant
public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen

/-!
# Section 5.1 Complex Poisson–Jensen Bound (`s4:5.1`)

Proves `spinPtilde_pj_bound`, the complex type-(II) Langer majorant for `spinPtilde c Φ u` off
the negative cut `{u : ℂ | u.im = 0 ∧ u.re ≤ 0}` inside `closedBall 0 (virasoroAC (c - 1)^2)`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.Special

noncomputable def spinPtildeC2 : ℝ :=
  3 * ((2 / (0.3 * π)) * (3 / (2 * Real.sqrt slitQ)) * chartParams.c_tip_hi)

lemma spinPtildeC2_pos : 0 < spinPtildeC2 := by
  unfold spinPtildeC2
  have := slitQ_pos
  have := chartParams.hc_tip_hi_pos
  positivity

noncomputable def spinPtildeCκ (C_strip C_slit κ : ℝ) : ℝ :=
  ((2 / xiStar) * chartParams.C_dxi) *
    max 1 (C_strip / κ) * max 1 (2 * C_slit / κ) * Real.exp 1 *
    ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) * Real.exp slitEntropyComplexConst)

lemma spinPtildeCκ_pos {C_strip C_slit κ : ℝ} (_hκ : 0 < κ) :
    0 < spinPtildeCκ C_strip C_slit κ := by
  unfold spinPtildeCκ
  have := xiStar_pos
  have := chartParams.hCdxi_pos
  have := slitQ_pos
  have := chartParams.hc_tip_lo_pos
  positivity

private lemma cpow_half_re_pos_spin {u : ℂ} (hu : u ≠ 0) (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    0 < (u ^ (1 / 2 : ℂ)).re := by
  rw [Complex.cpow_def_of_ne_zero hu, Complex.exp_re]
  have him : (Complex.log u * (1 / 2 : ℂ)).im = u.arg / 2 := by
    simp [Complex.log_im]; ring
  rw [him]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have hpi_ne : u.arg ≠ π := by
    intro hpi
    obtain ⟨hre, him0⟩ := Complex.arg_eq_pi_iff.mp hpi
    exact hcut ⟨him0, hre.le⟩
  exact ⟨by linarith [Complex.neg_pi_lt_arg u], by linarith [lt_of_le_of_ne (Complex.arg_le_pi u) hpi_ne]⟩

lemma spinPtilde_pj_bound {C_strip C_slit κ : ℝ}
    (_hCstrip : 0 < C_strip)
    (hStrip_bd : ∀ {c : ℝ}, 40 ≤ c → ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
      ∀ b : ℂ, |b.im| ≤ 1 / 2 → ‖spinGcalCl ((c - 1) / 12) Φ b‖ ≤ C_strip * (c - 1) ^ 2 * spinM2 ((c - 1) / 12) Φ)
    (hCslit : 0 < C_slit)
    (hSlit_bd : ∀ {c : ℝ}, 40 ≤ c → ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
      Integrable (fun x : ℝ => ‖spinGcal ((c - 1) / 12) Φ (x : ℂ)‖ * ((c - 1) / 12) * Real.exp ((c - 1) * spinL x)) ∧
      (∫ x : ℝ, ‖spinGcal ((c - 1) / 12) Φ (x : ℂ)‖ * ((c - 1) / 12) * Real.exp ((c - 1) * spinL x)) ≤
        C_slit * spinM2 ((c - 1) / 12) Φ)
    (hκ : 0 < κ) {c : ℝ} (hc : 49 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    (hB_lo : κ * spinM2 ((c - 1) / 12) Φ ≤ spinCalNorm c Φ)
    {u : ℂ} (hu_ac : u ∈ closedBall (0 : ℂ) (virasoroAC (c - 1) ^ 2))
    (hu_ne : u ≠ 0) (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    let n := c - 1
    ‖spinPtilde c Φ u‖ ≤ spinPtildeCκ C_strip C_slit κ * spinAiryEnv u *
      Real.exp (spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
        (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re) := by
  intro n
  let a : ℝ := n / 12
  let B_n : ℝ := spinCalNorm c Φ
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_pos : 0 < a := by dsimp [a, n]; linarith
  have hc40 : 40 ≤ c := by linarith
  have hε_pos : 0 < tipEps n := tipEps_pos hn_pos
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := cpow_half_re_pos_spin hu_ne hcut
  by_cases hB0 : B_n = 0
  · have hP0 : spinPtilde c Φ u = 0 := by
      unfold spinPtilde
      change _ / (B_n : ℂ) = 0
      rw [hB0]; simp
    rw [hP0, norm_zero]
    have hsp := spinPtildeCκ_pos hκ (C_strip := C_strip) (C_slit := C_slit)
    have hae : 0 ≤ spinAiryEnv u := by unfold spinAiryEnv; exact (Real.exp_pos _).le
    positivity
  have hM2_nn : 0 ≤ spinM2 a Φ := integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg (by dsimp [a, n]; linarith) p.1))
      (spinV1_nonneg (by dsimp [a, n]; linarith) p.2)
  have hB_pos : 0 < B_n := lt_of_le_of_ne ((mul_nonneg hκ.le hM2_nn).trans hB_lo) (Ne.symm hB0)
  let M_base : ℝ := max 1 (C_strip / κ)
  let B_slit : ℝ := max 1 (2 * C_slit / κ)
  have hMbase_ge1 : 1 ≤ M_base := le_max_left _ _
  have hMbase_pos : 0 < M_base := lt_of_lt_of_le zero_lt_one hMbase_ge1
  have hBslit_ge1 : 1 ≤ B_slit := le_max_left _ _
  have hBslit_pos : 0 < B_slit := lt_of_lt_of_le zero_lt_one hBslit_ge1
  set b := virasoroBChart n u
  by_cases hG0 : spinGcal a Φ b = 0
  · have hP0 : spinPtilde c Φ u = 0 := by
      unfold spinPtilde
      change ((a : ℂ) * _ * _ * spinGcal a Φ b) / _ = 0
      rw [hG0]; simp
    rw [hP0, norm_zero]
    have hsp := spinPtildeCκ_pos hκ (C_strip := C_strip) (C_slit := C_slit)
    have hae : 0 ≤ spinAiryEnv u := by unfold spinAiryEnv; exact (Real.exp_pos _).le
    positivity
  -- Apply `virasoro_lemma_T1` & `virasoro_tip_comparability`
  set ζ : ℂ := ((tipEps n)⁻¹ : ℝ) * (b - (xiStar : ℂ))
  have hb_eq : bScale n ζ = b := by
    unfold bScale ζ
    have h1 : ((tipEps n : ℝ) : ℂ) * (((tipEps n)⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hε_pos.ne')
    calc (xiStar : ℂ) + ((tipEps n : ℝ) : ℂ) * ((((tipEps n)⁻¹ : ℝ) : ℂ) * (b - (xiStar : ℂ)))
        = (xiStar : ℂ) + (((tipEps n : ℝ) : ℂ) * (((tipEps n)⁻¹ : ℝ) : ℂ)) * (b - (xiStar : ℂ)) := by ring
      _ = b := by rw [h1, one_mul]; ring
  have hεζ_eq : tipEps n * ‖ζ‖ = ‖b - (xiStar : ℂ)‖ := by
    dsimp [ζ]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hε_pos.le)]
    field_simp [hε_pos.ne']
  have htip_cap := virasoro_deltaChart_tip_cap hn_pos hu_ac
  have hεζ_1 : tipEps n * ‖ζ‖ ≤ chartParams.ρ₁_tip := by
    rw [hεζ_eq]; exact htip_cap.trans (min_le_left _ _)
  have hεζ_T1 : tipEps n * ‖ζ‖ ≤ 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) := by
    rw [hεζ_eq]; exact htip_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcomp := virasoro_tip_comparability hn_pos hu_ac hcut
  have hζ_cut : ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) := by
    intro h0
    have hre_z : ((-ζ) ^ (1 / 2 : ℂ)).re = 0 := by
      have hneg_im : (-ζ).im = 0 := by simp [h0.1]
      have hneg_re : (-ζ).re ≤ 0 := by simp [h0.2]
      by_cases hzero : -ζ = 0
      · rw [hzero, Complex.zero_cpow (by norm_num)]; simp
      · have harg : (-ζ).arg = π := Complex.arg_eq_pi_iff.mpr ⟨by
          have : (-ζ).re ≠ 0 := fun h => hzero (Complex.ext h hneg_im)
          exact lt_of_le_of_ne hneg_re this, hneg_im⟩
        rw [Complex.cpow_def_of_ne_zero hzero, Complex.exp_re]
        have him : (Complex.log (-ζ) * (1 / 2 : ℂ)).im = π / 2 := by
          simp [Complex.log_im, harg]; ring
        rw [him, Real.cos_pi_div_two, mul_zero]
    have hpos_rhs : 0 < chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re :=
      mul_pos chartParams.hc_tip_lo_pos hu_re_pos
    linarith [hcomp.1]
  obtain ⟨_, hz_im, hz_tip, hz_map, _, hz_im_bd, _, hz_prod_bd⟩ :=
    virasoro_lemma_T1 hn_pos hζ_cut hεζ_1
  set v : ℂ := I * ((Real.sqrt (tipEps n) : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
  set z_b : ℂ := (sigmaStar : ℂ) + chartParams.ψ_tip v
  have hconfB_zb : confB z_b = b := by
    rw [← slitBoundaryMapC_eq_confB hz_im, hz_map, hb_eq]
  have hcb_zb := confB_mem_slitStrip hz_im
  rw [hconfB_zb] at hcb_zb
  -- Poisson-Jensen setup on upper half-plane for `F z := (B_n : ℂ)⁻¹ * spinGcal a Φ (confB z)`
  let F : ℂ → ℂ := fun z => (B_n : ℂ)⁻¹ * spinGcal a Φ (confB z)
  let F_bdy : ℝ → ℂ := fun σ => (B_n : ℂ)⁻¹ * spinGcalCl a Φ (confB (σ : ℂ))
  let M_strip : ℝ := M_base * n ^ 2
  have hMstrip_pos : 0 < M_strip := by dsimp [M_strip]; positivity
  have hF_diff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} := by
    intro z hz
    have hc_diff : DifferentiableAt ℂ confB z := (hasDerivAt_confB hz).differentiableAt
    have hg_diff : DifferentiableAt ℂ (spinGcal a Φ) (confB z) :=
      (spinGcal_differentiableOn_strip hc40 hΦ).differentiableAt
        ((isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds (confB_mem_slitStrip hz).1)
    exact ((hg_diff.comp z hc_diff).const_mul (B_n : ℂ)⁻¹).differentiableWithinAt
  have hconfB_strip_bd : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖(B_n : ℂ)⁻¹ * spinGcalCl a Φ w‖ ≤ M_strip := fun w hw => by
    have h1 := hStrip_bd hc40 hΦ w hw
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB_pos.le]
    have hdiv : C_strip * spinM2 a Φ / B_n ≤ M_base := by
      rcases eq_or_lt_of_le hM2_nn with h0 | _hpos
      · rw [← h0, mul_zero, zero_div]; exact hMbase_pos.le
      · rw [div_le_iff₀ hB_pos]
        calc C_strip * spinM2 a Φ = (C_strip / κ) * (κ * spinM2 a Φ) := by field_simp [hκ.ne']
          _ ≤ M_base * B_n := mul_le_mul (le_max_right _ _) hB_lo (mul_nonneg hκ.le hM2_nn) hMbase_pos.le
    calc B_n⁻¹ * ‖spinGcalCl a Φ w‖
        ≤ B_n⁻¹ * (C_strip * n ^ 2 * spinM2 a Φ) := by gcongr
      _ = (C_strip * spinM2 a Φ / B_n) * n ^ 2 := by ring
      _ ≤ M_base * n ^ 2 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
  have hF_bd : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ M_strip := fun z hz => by
    have hcb := confB_mem_slitStrip hz
    obtain ⟨_, hagree⟩ := spinGcalCl_props hc40 hΦ
    dsimp [F]
    rw [← hagree _ hcb.1]
    exact hconfB_strip_bd _ hcb.1.le
  have hconfB_im_real : ∀ σ : ℝ, σ ∉ ({-1, 0, 1} : Set ℝ) → |(confB (σ : ℂ)).im| ≤ 1 / 2 := by
    intro σ hnot
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
  have hF_bdy : ∀ᵐ σ : ℝ ∂volume,
      Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (F_bdy σ)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot
    have hnot' : σ ∉ ({-1, 0, 1} : Set ℝ) := hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot'
    have htend_B : Tendsto confB (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ))
        (𝓝[{w : ℂ | |w.im| ≤ 1 / 2}] (confB (σ : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (confB_continuousWithinAt_real hnot'.2.1 hnot'.2.2 hnot'.1).tendsto.mono_left
          (nhdsWithin_mono _ fun z (hz : 0 < z.im) => hz.le)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact (confB_mem_slitStrip hz).1.le
    obtain ⟨hcont_cl, hagree_cl⟩ := spinGcalCl_props hc40 hΦ
    have htend_G : Tendsto (fun z : ℂ => spinGcal a Φ (confB z))
        (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (spinGcalCl a Φ (confB (σ : ℂ)))) := by
      have ht := ((hcont_cl (confB (σ : ℂ)) (hconfB_im_real σ hnot)).tendsto).comp htend_B
      refine ht.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hagree_cl _ (confB_mem_slitStrip hz).1
    exact tendsto_const_nhds.mul htend_G
  have hF_zb_ne : F z_b ≠ 0 := by
    dsimp [F]; rw [hconfB_zb]
    exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hB_pos.ne')) hG0
  obtain ⟨hPJ_int, hPJ_le⟩ := halfPlane_poissonJensen hMstrip_pos hF_diff hF_bd hF_bdy hz_im hF_zb_ne
  let x₀ : ℝ := z_b.re
  let y₀ : ℝ := z_b.im
  have hm_pos : 0 < slitMass x₀ y₀ := slitMass_pos_s4 hz_im
  have hm_le : slitMass x₀ y₀ ≤ 1 := slitMass_le_one_s4 hz_im
  set m : ℝ := slitMass x₀ y₀
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]
    intro σ h1 h2
    rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2
    · linarith [h1.1]
    · linarith [h1.2, h2.1]
    · linarith
    · linarith [h2.2]
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
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
  have hsplit_eq : ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) +
        (∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set hunion_ae]
    exact setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
      hPJ_int.integrableOn hPJ_int.integrableOn
  have hedge_mass : ∫ σ in edgePreimage, poissonKernel x₀ y₀ σ = 1 - m := by
    have hint := integrable_poissonKernel x₀ hz_im
    have htot : (∫ σ in slitPreimage, poissonKernel x₀ y₀ σ) +
        ∫ σ in edgePreimage, poissonKernel x₀ y₀ σ = 1 := by
      rw [← setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
        hint.integrableOn hint.integrableOn, setIntegral_congr_set hunion_ae,
        setIntegral_univ, integral_poissonKernel x₀ hz_im]
    change m + _ = 1 at htot; linarith
  -- Edge integral bound
  have hedge_le : ∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤
      (1 - m) * Real.log M_base + 2 * (1 - m) * Real.log n := by
    have hint_edge := hPJ_int.integrableOn (s := edgePreimage)
    have hpk_edge : IntegrableOn (fun σ => Real.log M_strip * poissonKernel x₀ y₀ σ) edgePreimage :=
      (integrable_poissonKernel x₀ hz_im).integrableOn.const_mul _
    have hMstrip_ge1 : 1 ≤ M_strip := by
      dsimp [M_strip]
      have hn1 : 1 ≤ n ^ 2 := by nlinarith
      nlinarith
    have hpt_edge : ∀ σ ∈ edgePreimage,
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤ Real.log M_strip * poissonKernel x₀ y₀ σ := by
      intro σ hσ
      have hnot : σ ∉ ({-1, 0, 1} : Set ℝ) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        rcases hσ with (hlt : σ < -1) | ⟨h0, h1⟩
        · exact ⟨by linarith, by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith, by linarith⟩
      have hbd_σ : ‖F_bdy σ‖ ≤ M_strip := hconfB_strip_bd _ (hconfB_im_real σ hnot)
      have hlog_le : Real.log ‖F_bdy σ‖ ≤ Real.log M_strip := by
        by_cases h0 : ‖F_bdy σ‖ = 0
        · rw [h0, Real.log_zero]; exact Real.log_nonneg hMstrip_ge1
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hbd_σ
      exact mul_le_mul_of_nonneg_right hlog_le (poissonKernel_nonneg hz_im.le σ)
    have hmono := setIntegral_mono_on hint_edge hpk_edge (measurableSet_Iio.union measurableSet_Ioo) hpt_edge
    rw [integral_const_mul, hedge_mass] at hmono
    have hMstrip_log : Real.log M_strip = Real.log M_base + 2 * Real.log n := by
      dsimp [M_strip]
      rw [Real.log_mul hMbase_pos.ne' (pow_ne_zero 2 hn_pos.ne'), Real.log_pow, Nat.cast_ofNat]
    rw [hMstrip_log] at hmono
    linarith [hmono]
  -- Slit integral bound via `setIntegral_slitPreimage_div_slitDensity`
  have hslit_confB : ∀ σ ∈ slitPreimage, confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := by
    intro σ hσ
    rcases hσ with hIoo | hIoi
    · exact Complex.ext (confB_real_re hIoo.2.ne (by linarith [hIoo.2]) hIoo.1.ne')
        (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
    · have hgt : 1 < σ := hIoi
      exact Complex.ext (confB_real_re (by linarith) hgt.ne' (by linarith))
        (confB_real_im_of_one_lt hgt)
  let φ : ℝ → ℝ := fun t => a * Real.exp (n * slitL t) * (‖spinGcal a Φ (t : ℂ)‖ / B_n)
  have hφ_meas : Measurable φ := by
    have hcont_g : Continuous (fun t : ℝ => spinGcal a Φ (t : ℂ)) :=
      (spinGcal_differentiableOn_strip hc40 hΦ).continuousOn.comp_continuous Complex.continuous_ofReal
        fun x => by change |(x : ℂ).im| < 1 / 2; simp [Complex.ofReal_im]
    have hL : Continuous slitL := by unfold slitL; fun_prop
    exact ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hL))).mul
      (hcont_g.norm.div_const B_n)).measurable
  have hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t := fun t _ =>
    mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) (div_nonneg (norm_nonneg _) hB_pos.le)
  obtain ⟨hG_int_all, hG_bd_all⟩ := hSlit_bd hc40 hΦ
  have hφ_eq_all : φ = fun t : ℝ => B_n⁻¹ * (‖spinGcal a Φ (t : ℂ)‖ * a * Real.exp (n * spinL t)) := by
    ext t; dsimp [φ]
    have hL : slitL t = spinL t := rfl
    rw [hL]; ring
  have hφ_int : IntegrableOn φ (Ioi xiStar) := by
    rw [hφ_eq_all]; exact (hG_int_all.const_mul B_n⁻¹).integrableOn
  have hIφ_le : 2 * ∫ t in Ioi xiStar, φ t ≤ B_slit := by
    have hφ_int_all : Integrable φ volume := by
      rw [hφ_eq_all]; exact hG_int_all.const_mul B_n⁻¹
    have hset_le : ∫ t in Ioi xiStar, φ t ≤ ∫ t : ℝ, φ t :=
      setIntegral_le_integral hφ_int_all (Eventually.of_forall fun t =>
        mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) (div_nonneg (norm_nonneg _) hB_pos.le))
    have hint_le_all : ∫ t : ℝ, φ t ≤ C_slit / κ := by
      rw [hφ_eq_all, integral_const_mul]
      rcases eq_or_lt_of_le hM2_nn with h0 | hpos
      · have hzero : ∫ x : ℝ, ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) ≤ 0 := by
          calc ∫ x : ℝ, ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)
              ≤ C_slit * spinM2 a Φ := hG_bd_all
            _ = 0 := by rw [← h0, mul_zero]
        have hnn : 0 ≤ B_n⁻¹ * ∫ x : ℝ, ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) :=
          mul_nonneg (inv_pos.mpr hB_pos).le (integral_nonneg fun _ =>
            mul_nonneg (mul_nonneg (norm_nonneg _) ha_pos.le) (Real.exp_pos _).le)
        have h0_eq : B_n⁻¹ * ∫ x : ℝ, ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) = 0 :=
          le_antisymm (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hB_pos).le hzero) hnn
        rw [h0_eq]; exact div_nonneg hCslit.le hκ.le
      · calc B_n⁻¹ * ∫ x : ℝ, ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)
            ≤ B_n⁻¹ * (C_slit * spinM2 a Φ) := mul_le_mul_of_nonneg_left hG_bd_all (inv_pos.mpr hB_pos).le
          _ ≤ (κ * spinM2 a Φ)⁻¹ * (C_slit * spinM2 a Φ) := by gcongr
          _ = C_slit / κ := by
              field_simp [hκ.ne', hpos.ne']
    calc 2 * ∫ t in Ioi xiStar, φ t ≤ 2 * ∫ t : ℝ, φ t := mul_le_mul_of_nonneg_left hset_le two_pos.le
      _ ≤ 2 * (C_slit / κ) := mul_le_mul_of_nonneg_left hint_le_all two_pos.le
      _ = 2 * C_slit / κ := by ring
      _ ≤ B_slit := le_max_right _ _
  obtain ⟨hf_pull_int, hf_pull_eq⟩ :=
    setIntegral_slitPreimage_div_slitDensity (x := x₀) hz_im hφ_meas hφ_nn hφ_int
  let K_val : ℝ → ℝ := fun σ => Real.exp (n * slitL (slitBoundaryMap σ))
  let f : ℝ → ℝ := fun σ => ‖F_bdy σ‖ * (a * K_val σ) / slitDensity x₀ y₀ σ
  have hK_pos : ∀ σ : ℝ, 0 < K_val σ := fun σ => Real.exp_pos _
  have hFbdy_eq_slit : ∀ σ ∈ slitPreimage,
      ‖F_bdy σ‖ = ‖spinGcal a Φ (slitBoundaryMap σ : ℂ)‖ / B_n := fun σ hσ => by
    obtain ⟨_, hagree⟩ := spinGcalCl_props hc40 hΦ
    dsimp [F_bdy]
    rw [hslit_confB σ hσ, hagree _ (by change |(slitBoundaryMap σ : ℂ).im| < 1 / 2; simp),
      norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB_pos.le, inv_mul_eq_div]
  have hf_eq_pull : ∀ σ ∈ slitPreimage, f σ = φ |slitBoundaryMap σ| / slitDensity x₀ y₀ σ := fun σ hσ => by
    dsimp [f, φ, K_val]
    rw [hFbdy_eq_slit σ hσ, show slitL |slitBoundaryMap σ| = slitL (slitBoundaryMap σ) by unfold slitL; rw [abs_abs]]
    have heven : spinGcal a Φ ((|slitBoundaryMap σ| : ℝ) : ℂ) = spinGcal a Φ (slitBoundaryMap σ : ℂ) := by
      rcases le_or_gt 0 (slitBoundaryMap σ) with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, Complex.ofReal_neg, spinGcal_neg hc40 hΦ]
    rw [heven]; ring
  have hG_ne_ae := spinGcal_bdy_ne_zero_ae hc40 hΦ hcb_zb.1 hG0
  have hf_pos_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ := by
    filter_upwards [hG_ne_ae, slitDensity_pos_ae (x := x₀) hz_im,
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hG hω hσ
    dsimp [f]
    rw [hFbdy_eq_slit σ hσ]
    exact div_pos (mul_pos (div_pos (norm_pos_iff.mpr hG) hB_pos) (mul_pos ha_pos (hK_pos σ))) hω
  have hf_int : IntegrableOn (fun σ => f σ * poissonKernel x₀ y₀ σ) slitPreimage := by
    refine hf_pull_int.congr_fun (fun σ hσ => ?_) (measurableSet_Ioo.union measurableSet_Ioi)
    rw [hf_eq_pull σ hσ]
  have hf_int_eq : ∫ σ in slitPreimage, f σ * poissonKernel x₀ y₀ σ =
      2 * ∫ t in Ioi xiStar, φ t := by
    rw [← hf_pull_eq]
    exact setIntegral_congr_fun (measurableSet_Ioo.union measurableSet_Ioi) fun σ hσ => by
      rw [hf_eq_pull σ hσ]
  have hident : IntegrableOn (fun σ => slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    identification_integrand_integrable x₀ hz_im
  have hlogK_eq : (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) =
      fun σ => n * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) := by
    ext σ; dsimp [K_val]; rw [Real.log_exp]; ring
  have hlogK_int : IntegrableOn (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    rw [hlogK_eq]; exact hident.const_mul n
  have hlogK_eval : ∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ =
      -n * majorant2D b := by
    rw [hlogK_eq, integral_const_mul, ← hconfB_zb, harmonicMajorantIdentification_complex hz_im]
    ring
  have hlogω_int : IntegrableOn
      (fun σ => Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    (integrableOn_poisson_mul_log_slitDensity x₀ hz_im).congr_fun
      (fun _ _ => by dsimp only; ring) (measurableSet_Ioo.union measurableSet_Ioi)
  have hlogF_slit_int : IntegrableOn
      (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) slitPreimage :=
    hPJ_int.integrableOn
  have hpk_slit : IntegrableOn (poissonKernel x₀ y₀) slitPreimage :=
    (integrable_poissonKernel x₀ hz_im).integrableOn
  have hlogf_eq_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x₀ y₀ σ =
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
          Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ +
          Real.log (K_val σ) * poissonKernel x₀ y₀ σ +
          Real.log a * poissonKernel x₀ y₀ σ := by
    filter_upwards [hG_ne_ae, slitDensity_pos_ae (x := x₀) hz_im,
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hG hω hσ
    have hF_pos : 0 < ‖F_bdy σ‖ := by
      rw [hFbdy_eq_slit σ hσ]; exact div_pos (norm_pos_iff.mpr hG) hB_pos
    dsimp [f]
    rw [Real.log_div (mul_pos hF_pos (mul_pos ha_pos (hK_pos σ))).ne' hω.ne',
      Real.log_mul hF_pos.ne' (mul_pos ha_pos (hK_pos σ)).ne',
      Real.log_mul ha_pos.ne' (hK_pos σ).ne']
    ring
  have hsub_int : IntegrableOn (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
      Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    hlogF_slit_int.sub hlogω_int
  have h1_int : IntegrableOn (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
      Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ +
      Real.log (K_val σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    hsub_int.add hlogK_int
  have hlogf_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    (h1_int.add (hpk_slit.const_mul (Real.log a))).congr (hlogf_eq_ae.mono fun σ h => h.symm)
  have hjensen := log_integral_jensen_slitPreimage_s4 hz_im hf_pos_ae hf_int hlogf_int
    hBslit_pos (hf_int_eq.le.trans hIφ_le)
  have hdecomp : ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ) +
        (∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) -
        (∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) -
        m * Real.log a := by
    have hadd_f : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ =
        ∫ σ in slitPreimage,
          (Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ - Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ +
            Real.log (K_val σ) * poissonKernel x₀ y₀ σ) + Real.log a * poissonKernel x₀ y₀ σ :=
      integral_congr_ae hlogf_eq_ae
    rw [hadd_f, integral_add h1_int (hpk_slit.const_mul (Real.log a)), integral_add hsub_int hlogK_int,
      integral_sub hlogF_slit_int hlogω_int, integral_const_mul]
    have hm_eq : m = ∫ σ in slitPreimage, poissonKernel x₀ y₀ σ := rfl
    rw [hm_eq]; ring
  have hent_le : ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ ≤
      slitEntropy x₀ y₀ := by
    calc ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ
        = ∫ σ in slitPreimage, poissonKernel x₀ y₀ σ * Real.log (slitDensity x₀ y₀ σ) :=
          integral_congr_ae (Eventually.of_forall fun σ => by ring)
      _ ≤ slitEntropy x₀ y₀ := setIntegral_poisson_mul_log_slitDensity_le_entropy x₀ hz_im
  -- Tip geometry bounds from T1, T4, and potential identity
  have hCT1_sqrt : chartParams.C_T1_tip * Real.sqrt (tipEps n * ‖ζ‖) ≤ 1 / 2 := by
    have hsqrt_le : Real.sqrt (tipEps n * ‖ζ‖) ≤ 1 / (2 * (chartParams.C_T1_tip + 1)) := by
      have h1 : 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) =
          (1 / (2 * (chartParams.C_T1_tip + 1))) ^ 2 := by
        have hp : chartParams.C_T1_tip + 1 ≠ 0 := by linarith [chartParams.hCT1_tip_nn]
        field_simp [hp]; ring
      calc Real.sqrt (tipEps n * ‖ζ‖) ≤ Real.sqrt ((1 / (2 * (chartParams.C_T1_tip + 1))) ^ 2) :=
            Real.sqrt_le_sqrt (h1 ▸ hεζ_T1)
        _ = 1 / (2 * (chartParams.C_T1_tip + 1)) :=
            Real.sqrt_sq (div_nonneg zero_le_one (by linarith [chartParams.hCT1_tip_nn]))
    calc chartParams.C_T1_tip * Real.sqrt (tipEps n * ‖ζ‖)
        ≤ chartParams.C_T1_tip * (1 / (2 * (chartParams.C_T1_tip + 1))) :=
          mul_le_mul_of_nonneg_left hsqrt_le chartParams.hCT1_tip_nn
      _ = (chartParams.C_T1_tip / (chartParams.C_T1_tip + 1)) * (1 / 2) := by
          have hp : chartParams.C_T1_tip + 1 ≠ 0 := by linarith [chartParams.hCT1_tip_nn]
          field_simp [hp]
      _ ≤ 1 * (1 / 2) := by
          gcongr; exact (div_le_one (by linarith [chartParams.hCT1_tip_nn])).mpr (by linarith)
      _ = 1 / 2 := one_mul _
  have hd_pos : 0 < tipDist ζ := tipDist_pos_of_not_nonneg hζ_cut
  have hprod_lb : (1 / 2 : ℝ) * ((tipEps n / slitQ) * tipDist ζ) ≤
      y₀ * ‖z_b - (sigmaStar : ℂ)‖ := by
    have hbase_nn : 0 ≤ (tipEps n / slitQ) * tipDist ζ :=
      mul_nonneg (div_nonneg hε_pos.le slitQ_pos.le) hd_pos.le
    have h1 := (abs_le.mp hz_prod_bd).1
    have h2 := mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    dsimp [y₀]; linarith
  have hy_ub : y₀ ≤ (3 / (2 * Real.sqrt slitQ)) * chartParams.c_tip_hi * n ^ (-(1 / 3 : ℝ)) *
      (u ^ (1 / 2 : ℂ)).re := by
    have hzeta_re_nn : 0 ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg (-ζ)
    have hbase_nn : 0 ≤ Real.sqrt (tipEps n / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re :=
      mul_nonneg (Real.sqrt_nonneg _) hzeta_re_nn
    have h1 := (abs_le.mp hz_im_bd).2
    have h2 := mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    have hsqrt_eps : Real.sqrt (tipEps n / slitQ) = n ^ (-(1 / 3 : ℝ)) / Real.sqrt slitQ := by
      have hε_nn : 0 ≤ tipEps n := hε_pos.le
      rw [Real.sqrt_div hε_nn]
      have h1 : Real.sqrt (tipEps n) = n ^ (-(1 / 3 : ℝ)) := by
        unfold tipEps
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn_pos.le]
        norm_num
      rw [h1]
    have hsq_re : Real.sqrt (tipEps n / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re ≤
        (n ^ (-(1 / 3 : ℝ)) / Real.sqrt slitQ) * (chartParams.c_tip_hi * (u ^ (1 / 2 : ℂ)).re) := by
      rw [← hsqrt_eps]
      exact mul_le_mul_of_nonneg_left hcomp.2.1 (Real.sqrt_nonneg _)
    calc y₀ = z_b.im := rfl
      _ ≤ (3 / 2 : ℝ) * (Real.sqrt (tipEps n / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by linarith
      _ ≤ (3 / 2 : ℝ) * ((n ^ (-(1 / 3 : ℝ)) / Real.sqrt slitQ) *
            (chartParams.c_tip_hi * (u ^ (1 / 2 : ℂ)).re)) :=
          mul_le_mul_of_nonneg_left hsq_re (by norm_num)
      _ = (3 / (2 * Real.sqrt slitQ)) * chartParams.c_tip_hi * n ^ (-(1 / 3 : ℝ)) *
            (u ^ (1 / 2 : ℂ)).re := by ring
  have hz_eta : (x₀ : ℂ) + (y₀ : ℂ) * I = z_b := Complex.re_add_im z_b
  have hT4 := lemma_T4 hz_im (by rw [hz_eta]; exact hz_tip)
  have hz_norm_pos : 0 < ‖z_b - (sigmaStar : ℂ)‖ := by
    by_contra hle
    have h0 : ‖z_b - (sigmaStar : ℂ)‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    have heq : z_b = (sigmaStar : ℂ) := sub_eq_zero.mp (norm_eq_zero.mp h0)
    have : z_b.im = 0 := by rw [heq, Complex.ofReal_im]
    linarith [hz_im]
  have hprod_pos : 0 < (1 / 2 : ℝ) * ((tipEps n / slitQ) * tipDist ζ) := by
    have := slitQ_pos; positivity
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hS_term : slitEntropy x₀ y₀ ≤
      Real.log (n ^ (2 / 3 : ℝ) * (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
        (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) + slitEntropyComplexConst := by
    have hm_inv_eq : Real.log (1 / y₀) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) =
        Real.log (1 / (y₀ * ‖z_b - (sigmaStar : ℂ)‖)) := by
      rw [← Real.log_mul (one_div_pos.mpr hz_im).ne' (one_div_pos.mpr hz_norm_pos).ne']
      congr 1; ring
    have hinv_le : 1 / (y₀ * ‖z_b - (sigmaStar : ℂ)‖) ≤
        n ^ (2 / 3 : ℝ) * (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ := by
      have hlo_dist := hcomp.2.2.2.2
      have hlhs_pos : 0 < chartParams.c_tip_lo ^ (3 / 2 : ℝ) * Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
        have := chartParams.hc_tip_lo_pos; positivity
      calc 1 / (y₀ * ‖z_b - (sigmaStar : ℂ)‖)
          ≤ 1 / ((1 / 2 : ℝ) * ((tipEps n / slitQ) * tipDist ζ)) :=
            one_div_le_one_div_of_le hprod_pos hprod_lb
        _ = n ^ (2 / 3 : ℝ) * (2 * slitQ) / tipDist ζ := by
            unfold tipEps
            rw [Real.rpow_neg hn_pos.le]
            field_simp [hn_pos.ne', slitQ_pos.ne', hd_pos.ne']
        _ ≤ n ^ (2 / 3 : ℝ) * (2 * slitQ) /
              (chartParams.c_tip_lo ^ (3 / 2 : ℝ) * Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re) := by
            gcongr; exact mul_nonneg (Real.rpow_nonneg hn_pos.le _) (by linarith [slitQ_pos])
        _ = n ^ (2 / 3 : ℝ) * (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
              (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ := by
            rw [Real.rpow_neg chartParams.hc_tip_lo_pos.le]
            ring
    have hlog_inv : Real.log (1 / (y₀ * ‖z_b - (sigmaStar : ℂ)‖)) ≤
        Real.log (n ^ (2 / 3 : ℝ) * (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) :=
      Real.log_le_log (one_div_pos.mpr (mul_pos hz_im hz_norm_pos)) hinv_le
    have hS' : slitEntropy x₀ y₀ ≤
        Real.log (1 / y₀) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) + slitEntropyComplexConst := by
      have h2 := hT4.2
      change slitEntropy x₀ y₀ ≤
        Real.log (1 / y₀) + Real.log (1 / ‖(x₀ : ℂ) + (y₀ : ℂ) * I - (sigmaStar : ℂ)‖) +
          slitEntropyComplexConst at h2
      rwa [hz_eta] at h2
    linarith only [hm_inv_eq, hlog_inv, hS']
  have h1m_bd : 1 - m ≤ (2 / (0.3 * π)) * (3 / (2 * Real.sqrt slitQ)) * chartParams.c_tip_hi *
      n ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re := by
    calc 1 - m ≤ (2 / (0.3 * π)) * y₀ := hT4.1
      _ ≤ (2 / (0.3 * π)) * ((3 / (2 * Real.sqrt slitQ)) * chartParams.c_tip_hi *
            n ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re) :=
          mul_le_mul_of_nonneg_left hy_ub (by positivity)
      _ = _ := by ring
  have hpot := virasoro_chart_potential_eq hn_pos hu_ac hcut
  have hPJ_comb : Real.log ‖F z_b‖ ≤
      (1 - m) * Real.log M_base + 2 * (1 - m) * Real.log n +
        (m * Real.log B_slit + (1 - m)) + slitEntropy x₀ y₀ + n * majorant2D b - m * Real.log a := by
    have hj : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ ≤
        m * Real.log B_slit + (1 - m) := hjensen
    linarith only [hPJ_le, hsplit_eq, hedge_le, hdecomp, hj, hent_le, hlogK_eval]
  have ha_eq : a = n / 12 := rfl
  have h1m_nn : 0 ≤ 1 - m := by linarith only [hm_le]
  have hlogM_bd : (1 - m) * Real.log M_base ≤ Real.log M_base :=
    mul_le_of_le_one_left (Real.log_nonneg hMbase_ge1) (by linarith only [hm_pos])
  have hlogB_bd : m * Real.log B_slit ≤ Real.log B_slit :=
    mul_le_of_le_one_left (Real.log_nonneg hBslit_ge1) hm_le
  have h1m_le1 : 1 - m ≤ 1 := by linarith only [hm_pos]
  have hn_ge1 : 1 ≤ n := by dsimp [n]; linarith only [hc]
  have hlog_n_combine : Real.log a - (2 / 3 : ℝ) * Real.log n +
      2 * (1 - m) * Real.log n - m * Real.log a ≤
      spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re -
        (2 / 3 : ℝ) * Real.log n := by
    have hlog12_nn : 0 ≤ Real.log 12 := Real.log_nonneg (by norm_num)
    have hloga : Real.log a = Real.log n - Real.log 12 := by
      rw [ha_eq, Real.log_div hn_pos.ne' (by norm_num)]
    have h1 : Real.log a - (2 / 3 : ℝ) * Real.log n + 2 * (1 - m) * Real.log n - m * Real.log a =
        (1 - m) * (3 * Real.log n - Real.log 12) - (2 / 3 : ℝ) * Real.log n := by
      rw [hloga]; ring
    have h2 : (1 - m) * (3 * Real.log n - Real.log 12) ≤ 3 * (1 - m) * Real.log n := by
      calc (1 - m) * (3 * Real.log n - Real.log 12)
          ≤ (1 - m) * (3 * Real.log n) := mul_le_mul_of_nonneg_left (by linarith only [hlog12_nn]) h1m_nn
        _ = 3 * (1 - m) * Real.log n := by ring
    have h3 : 3 * (1 - m) * Real.log n ≤
        spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re := by
      have hln_nn : 0 ≤ Real.log n := Real.log_nonneg hn_ge1
      calc 3 * (1 - m) * Real.log n
          ≤ 3 * ((2 / (0.3 * π)) * (3 / (2 * Real.sqrt slitQ)) * chartParams.c_tip_hi *
              n ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re) * Real.log n := by gcongr
        _ = spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re := by
            unfold spinPtildeC2; ring
    linarith only [h1, h2, h3]
  -- Factor `spinPtilde c Φ u` and conclude
  have hP_fac : spinPtilde c Φ u =
      ((a * tipEps n : ℝ) : ℂ) * (deriv (virasoroBChart n) u / ((tipEps n : ℝ) : ℂ)) *
        (-Complex.exp ((n : ℂ) * tipL b)) * F z_b := by
    have he_ne : ((tipEps n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε_pos.ne'
    have hmul : ((a * tipEps n : ℝ) : ℂ) * (deriv (virasoroBChart n) u / ((tipEps n : ℝ) : ℂ)) =
        (a : ℂ) * deriv (virasoroBChart n) u := by
      rw [Complex.ofReal_mul]; field_simp [he_ne]
    have hexp_eq : Complex.exp ((n : ℂ) * tipL b) =
        Complex.exp ((((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ)) * b) := by
      unfold tipL; ring_nf
    unfold spinPtilde
    dsimp only [F]
    rw [hconfB_zb]
    change (((a : ℂ) * Complex.exp ((((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ)) * b) *
        (-deriv (virasoroBChart n) u) * spinGcal a Φ b) / (B_n : ℂ)) = _
    rw [hmul, hexp_eq, div_eq_mul_inv]
    ring
  have hnorm_P : ‖spinPtilde c Φ u‖ ≤
      ((2 / xiStar) * chartParams.C_dxi) *
        (a * tipEps n * Real.exp (n * (tipL b).re) * ‖F z_b‖) := by
    rw [hP_fac, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg ha_pos.le hε_pos.le), norm_neg, Complex.norm_exp,
      Complex.re_ofReal_mul]
    have hd_bd := virasoroBChart_deriv_norm_le_spin hn_pos hu_ac
    have hnn : 0 ≤ a * tipEps n * Real.exp (n * (tipL b).re) * ‖F z_b‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg ha_pos.le hε_pos.le) (Real.exp_pos _).le) (norm_nonneg _)
    calc (a * tipEps n) * ‖deriv (virasoroBChart n) u / ((tipEps n : ℝ) : ℂ)‖ *
          Real.exp (n * (tipL b).re) * ‖F z_b‖
        = ‖deriv (virasoroBChart n) u / ((tipEps n : ℝ) : ℂ)‖ *
            (a * tipEps n * Real.exp (n * (tipL b).re) * ‖F z_b‖) := by ring
      _ ≤ ((2 / xiStar) * chartParams.C_dxi) *
            (a * tipEps n * Real.exp (n * (tipL b).re) * ‖F z_b‖) :=
          mul_le_mul_of_nonneg_right hd_bd hnn
  let Q : ℝ := a * tipEps n * Real.exp (n * (tipL b).re) * ‖F z_b‖
  have hQ_pos : 0 < Q :=
    mul_pos (mul_pos (mul_pos ha_pos hε_pos) (Real.exp_pos _)) (norm_pos_iff.mpr hF_zb_ne)
  have hlog_Q : Real.log Q = Real.log a - (2 / 3 : ℝ) * Real.log n +
      n * (tipL b).re + Real.log ‖F z_b‖ := by
    have hε_eq : tipEps n = n ^ (-(2 / 3 : ℝ)) := rfl
    dsimp [Q]
    rw [Real.log_mul (mul_pos (mul_pos ha_pos hε_pos) (Real.exp_pos _)).ne'
        (norm_pos_iff.mpr hF_zb_ne).ne',
      Real.log_mul (mul_pos ha_pos hε_pos).ne' (Real.exp_pos _).ne',
      Real.log_mul ha_pos.ne' hε_pos.ne', hε_eq, Real.log_rpow hn_pos, Real.log_exp]
    ring
  have hpot_eq : n * (tipL b).re + n * majorant2D b = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
    rw [← mul_add, add_comm, ← hpot]
  have hlog_Q_le : Real.log Q ≤
      Real.log (M_base * B_slit * Real.exp 1 *
        ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) * Real.exp slitEntropyComplexConst *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹)) +
        (-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) +
        spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re := by
    have hlog_dist_split :
        Real.log (n ^ (2 / 3 : ℝ) * (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) =
        (2 / 3 : ℝ) * Real.log n +
          Real.log ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
            (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) := by
      have h1 : 0 < (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ := by
        have := slitQ_pos; have := chartParams.hc_tip_lo_pos; positivity
      rw [show n ^ (2 / 3 : ℝ) * (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ =
          n ^ (2 / 3 : ℝ) * ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
            (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) by ring,
        Real.log_mul (Real.rpow_pos_of_pos hn_pos _).ne' h1.ne', Real.log_rpow hn_pos]
    have hlog_rhs_eq :
        Real.log (M_base * B_slit * Real.exp 1 *
          ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) * Real.exp slitEntropyComplexConst *
            (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹)) =
        Real.log M_base + Real.log B_slit + 1 +
          Real.log ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
            (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) + slitEntropyComplexConst := by
      have h1 : 0 < (2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ := by
        have := slitQ_pos; have := chartParams.hc_tip_lo_pos; positivity
      rw [show M_base * B_slit * Real.exp 1 *
          ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) * Real.exp slitEntropyComplexConst *
            (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) =
          (M_base * B_slit * Real.exp 1) * (Real.exp slitEntropyComplexConst *
            ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) *
              (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹)) by ring,
        Real.log_mul (mul_pos (mul_pos hMbase_pos hBslit_pos) (Real.exp_pos 1)).ne'
          (mul_pos (Real.exp_pos _) h1).ne',
        Real.log_mul (mul_pos hMbase_pos hBslit_pos).ne' (Real.exp_pos 1).ne',
        Real.log_mul hMbase_pos.ne' hBslit_pos.ne', Real.log_exp,
        Real.log_mul (Real.exp_pos _).ne' h1.ne', Real.log_exp]
      ring
    linarith only [hlog_Q, hPJ_comb, hlogM_bd, hlogB_bd, h1m_le1, hS_term, hlog_dist_split,
      hlog_n_combine, hpot_eq, hlog_rhs_eq]
  have hQ_le : Q ≤
      (M_base * B_slit * Real.exp 1 *
        ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) * Real.exp slitEntropyComplexConst)) *
        spinAiryEnv u *
        Real.exp (spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re) := by
    have hexp := Real.exp_le_exp.mpr hlog_Q_le
    rw [Real.exp_log hQ_pos] at hexp
    have hpos_A : 0 < M_base * B_slit * Real.exp 1 *
        ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) * Real.exp slitEntropyComplexConst *
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹) := by
      have := slitQ_pos; have := chartParams.hc_tip_lo_pos; positivity
    rw [Real.exp_add, Real.exp_add, Real.exp_log hpos_A] at hexp
    refine hexp.trans_eq ?_
    unfold spinAiryEnv; ring
  calc ‖spinPtilde c Φ u‖
      ≤ ((2 / xiStar) * chartParams.C_dxi) * Q := hnorm_P
    _ ≤ ((2 / xiStar) * chartParams.C_dxi) *
          ((M_base * B_slit * Real.exp 1 *
            ((2 * slitQ) * chartParams.c_tip_lo ^ (-(3 / 2 : ℝ)) * Real.exp slitEntropyComplexConst)) *
            spinAiryEnv u *
            Real.exp (spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
              (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)) :=
        mul_le_mul_of_nonneg_left hQ_le (by have := xiStar_pos; have := chartParams.hCdxi_pos; positivity)
    _ = spinPtildeCκ C_strip C_slit κ * spinAiryEnv u *
          Real.exp (spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
            (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re) := by
        unfold spinPtildeCκ
        dsimp [M_base, B_slit]
        ring

end FormalResearch.ModularBootstrap.Spin
