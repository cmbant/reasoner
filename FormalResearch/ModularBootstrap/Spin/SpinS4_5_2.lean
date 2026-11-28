/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_4
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_3

/-!
# Section 5.2 Proposition (`s4:5.2`): Exact Langer Jacobian and Truncated Real-Integral Bound

Proves `spinS4_5_2 : SpinS4_5_2` (`spinning_s4.tex`, Proposition 5.2):
1. Exact Jacobian substitution `∫_{J_n} Re P_tilde = B_n⁻¹ ∫_I a e^{n k b} Re G_cal(b) db`.
2. Uniform upper bound `∫_{J_n} Re P_tilde ≤ C_κ n^{-2/3} log n` on near-critical slack-feasible tests,
   using `spinS4_2_3`, `spinS4_2_4`, and `spinGcal_re_nonneg_of_ge`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal Interval
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap

private lemma virasoroDeltaChart_div_scale_eq {n : ℝ} (hn : 0 < n) (x : ℝ) :
    virasoroDeltaChart n (x * n ^ (2 / 3 : ℝ)) / n = virasoroDeltaChart 1 x := by
  unfold virasoroDeltaChart virasoroXiChartC
  have hr : ((x * n ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ((n ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
      (x : ℂ) * (((1 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.one_rpow, mul_one, mul_assoc,
      ← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [hr, mul_div_cancel_left₀ _ hn.ne', one_mul]

private lemma spinS4_5_2_r0_exists :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < xiStar / 2 ∧
      virasoroDeltaChart 1 (virasoroAC 1 ^ 2) < (xiStar - r₀) ^ 2 / 3 ∧
      (xiStar + r₀) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) := by
  have h1_pos : (0 : ℝ) < 1 := zero_lt_one
  have hac_nn : 0 ≤ virasoroAC 1 ^ 2 := sq_nonneg _
  have hac_pos : 0 < virasoroAC 1 ^ 2 := by
    rw [virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]
    have := virasoroBV_pos; positivity
  have hanti := virasoroDeltaChart_strictAnti h1_pos
  have hmem_hi : virasoroAC 1 ^ 2 ∈ Icc (-(virasoroAC 1 ^ 2)) (virasoroAC 1 ^ 2) :=
    ⟨by linarith, le_rfl⟩
  have hmem_0 : (0 : ℝ) ∈ Icc (-(virasoroAC 1 ^ 2)) (virasoroAC 1 ^ 2) :=
    ⟨by linarith, hac_nn⟩
  have hmem_lo : -(virasoroAC 1 ^ 2) ∈ Icc (-(virasoroAC 1 ^ 2)) (virasoroAC 1 ^ 2) :=
    ⟨le_rfl, by linarith⟩
  have h0 : xiBar = virasoroDeltaChart 1 0 := by
    rw [virasoroDeltaChart_zero, mul_one]
  have hlt1 : virasoroDeltaChart 1 (virasoroAC 1 ^ 2) < xiBar := by
    rw [h0]; exact hanti hmem_0 hmem_hi hac_pos
  have hlt2 : xiBar < virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) := by
    rw [h0]; exact hanti hmem_lo hmem_0 (by linarith)
  let δ := min (xiBar - virasoroDeltaChart 1 (virasoroAC 1 ^ 2))
    (virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) - xiBar)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  let r₀ := min (xiStar / 4) (δ / (2 * xiStar))
  have hr₀_pos : 0 < r₀ := lt_min (by positivity [xiStar_pos]) (by positivity [xiStar_pos, hδ])
  have hr₀_half : r₀ < xiStar / 2 := (min_le_left _ _).trans_lt (by linarith [xiStar_pos])
  have hr₀_xi : r₀ * xiStar ≤ δ / 2 := by
    have h1 : r₀ ≤ δ / (2 * xiStar) := min_le_right _ _
    calc r₀ * xiStar ≤ (δ / (2 * xiStar)) * xiStar := mul_le_mul_of_nonneg_right h1 xiStar_pos.le
      _ = δ / 2 := by field_simp [xiStar_pos.ne']
  have hsq_lo : xiBar - (xiStar - r₀) ^ 2 / 3 < δ := by
    have hEq : xiBar - (xiStar - r₀) ^ 2 / 3 = (2 * xiStar * r₀ - r₀ ^ 2) / 3 := by
      unfold xiBar; ring
    rw [hEq]
    have h1 : 2 * xiStar * r₀ - r₀ ^ 2 ≤ 2 * xiStar * r₀ := by nlinarith [sq_nonneg r₀]
    nlinarith [hr₀_xi, hδ]
  have hsq_hi : (xiStar + r₀) ^ 2 / 3 - xiBar < δ := by
    have hEq : (xiStar + r₀) ^ 2 / 3 - xiBar = (2 * xiStar * r₀ + r₀ ^ 2) / 3 := by
      unfold xiBar; ring
    rw [hEq]
    have h1 : r₀ ^ 2 ≤ xiStar * r₀ := by nlinarith [hr₀_pos, hr₀_half]
    nlinarith [hr₀_xi, hδ]
  refine ⟨r₀, hr₀_pos, hr₀_half, ?_, ?_⟩
  · linarith [min_le_left (xiBar - virasoroDeltaChart 1 (virasoroAC 1 ^ 2))
      (virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) - xiBar), hsq_lo]
  · linarith [min_le_right (xiBar - virasoroDeltaChart 1 (virasoroAC 1 ^ 2))
      (virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) - xiBar), hsq_hi]

private lemma spinS4_5_2_jacobian {c r₀ : ℝ} (hc : 40 ≤ c)
    (hr₀_pos : 0 < r₀) (hr₀_half : r₀ < xiStar / 2)
    (hlo : virasoroDeltaChart 1 (virasoroAC 1 ^ 2) < (xiStar - r₀) ^ 2 / 3)
    (hhi : (xiStar + r₀) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)))
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    let n := c - 1
    let a := n / 12
    let I_b := Icc (xiStar - r₀) (xiStar + r₀)
    let u_hi := virasoroUChart n ((xiStar - r₀) ^ 2 / 3)
    let u_lo := virasoroUChart n ((xiStar + r₀) ^ 2 / 3)
    (∫ u in Icc u_lo u_hi, (spinPtilde c Φ (u : ℂ)).re) =
      (spinCalNorm c Φ)⁻¹ *
        ∫ b in I_b, a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re := by
  intro n a I_b u_hi u_lo
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have hξ_scale_lo : virasoroDeltaChart n (virasoroAC n ^ 2) / n =
      virasoroDeltaChart 1 (virasoroAC 1 ^ 2) := by
    have hac : virasoroAC n ^ 2 = virasoroAC 1 ^ 2 * n ^ (2 / 3 : ℝ) := by
      rw [virasoroAC_sq n hn_pos.le, virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]
    rw [hac]; exact virasoroDeltaChart_div_scale_eq hn_pos _
  have hξ_scale_hi : virasoroDeltaChart n (-(virasoroAC n ^ 2)) / n =
      virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) := by
    have hac : -(virasoroAC n ^ 2) = (-(virasoroAC 1 ^ 2)) * n ^ (2 / 3 : ℝ) := by
      rw [virasoroAC_sq n hn_pos.le, virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]; ring
    rw [hac]; exact virasoroDeltaChart_div_scale_eq hn_pos _
  have hmem_div_lo := virasoroDeltaChart_div_mem hn_pos (abs_of_nonneg (sq_nonneg _) |>.le)
  have hmem_div_hi := virasoroDeltaChart_div_mem hn_pos (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])
  have hξ_m_mem : (xiStar - r₀) ^ 2 / 3 ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨hmem_div_lo.1.trans (hξ_scale_lo ▸ hlo.le),
      ((by
        have : (xiStar - r₀) ^ 2 / 3 < (xiStar + r₀) ^ 2 / 3 := by
          have : 0 < xiStar - r₀ := by linarith [xiStar_pos]
          nlinarith [hr₀_pos]
        linarith [hhi, hξ_scale_hi] : (xiStar - r₀) ^ 2 / 3 ≤ virasoroDeltaChart n (-(virasoroAC n ^ 2)) / n)).trans hmem_div_hi.2⟩
  have hξ_p_mem : (xiStar + r₀) ^ 2 / 3 ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨hmem_div_lo.1.trans ((by
      have : 0 < xiStar - r₀ := by linarith [xiStar_pos]
      have : (xiStar - r₀) ^ 2 / 3 < (xiStar + r₀) ^ 2 / 3 := by nlinarith [hr₀_pos]
      linarith [hlo, hξ_scale_lo] : virasoroDeltaChart n (virasoroAC n ^ 2) / n ≤ (xiStar + r₀) ^ 2 / 3)),
      (hξ_scale_hi ▸ hhi.le).trans hmem_div_hi.2⟩
  have hu_anti := virasoroUChart_strictAnti hn_pos
  have hu_lo_gt : -(virasoroAC n ^ 2) < u_lo := by
    have h1 := hu_anti hξ_p_mem hmem_div_hi (hξ_scale_hi ▸ hhi)
    rwa [virasoroUChart_deltaChart hn_pos (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])] at h1
  have hu_hi_lt : u_hi < virasoroAC n ^ 2 := by
    have h1 := hu_anti hmem_div_lo hξ_m_mem (hξ_scale_lo ▸ hlo)
    rwa [virasoroUChart_deltaChart hn_pos (abs_of_nonneg (sq_nonneg _)).le] at h1
  have hu_lo_lt_hi : u_lo < u_hi := by
    have hlt : (xiStar - r₀) ^ 2 / 3 < (xiStar + r₀) ^ 2 / 3 := by
      have : 0 < xiStar - r₀ := by linarith [xiStar_pos]
      nlinarith [hr₀_pos]
    exact hu_anti hξ_m_mem hξ_p_mem hlt
  have hsub_ac : ∀ u ∈ Icc u_lo u_hi, |u| < virasoroAC n ^ 2 := fun u hu =>
    abs_lt.mpr ⟨hu_lo_gt.trans_le hu.1, hu.2.trans_lt hu_hi_lt⟩
  let b_real : ℝ → ℝ := fun u => (virasoroBChart n (u : ℂ)).re
  have hb_real_eq : ∀ u ∈ Icc u_lo u_hi,
      virasoroBChart n (u : ℂ) = (b_real u : ℂ) := fun u hu => by
    exact Complex.ext rfl (virasoroBChart_ofReal hn_pos (hsub_ac u hu).le).1
  have hb_deriv_im : ∀ u ∈ Icc u_lo u_hi, (deriv (virasoroBChart n) (u : ℂ)).im = 0 := by
    intro u hu
    have hu_dom : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (hsub_ac u hu).trans (virasoroAC_sq_lt_domain hn_pos)
    have hd_C : HasDerivAt (fun t : ℝ => virasoroBChart n (t : ℂ))
        (deriv (virasoroBChart n) (u : ℂ)) u :=
      ((virasoroBChart_analyticOnNhd hn_pos (u : ℂ) hu_dom).differentiableAt.hasDerivAt).comp_ofReal
    have hd_im : HasDerivAt (fun t : ℝ => (virasoroBChart n (t : ℂ)).im)
        (deriv (virasoroBChart n) (u : ℂ)).im u :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    have hev : (fun t : ℝ => (virasoroBChart n (t : ℂ)).im) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      have ho : IsOpen (Ioo (-(virasoroAC n ^ 2)) (virasoroAC n ^ 2)) := isOpen_Ioo
      have hu_ioo : u ∈ Ioo (-(virasoroAC n ^ 2)) (virasoroAC n ^ 2) := abs_lt.mp (hsub_ac u hu)
      filter_upwards [ho.mem_nhds hu_ioo] with t ht
      exact (virasoroBChart_ofReal hn_pos (abs_lt.mpr ht).le).1
    exact hd_im.unique ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev)
  have hb_hasDeriv : ∀ u ∈ Set.uIcc u_lo u_hi, HasDerivAt b_real (deriv b_real u) u := by
    intro u hu
    rw [Set.uIcc_of_le hu_lo_lt_hi.le] at hu
    have hu_dom : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (hsub_ac u hu).trans (virasoroAC_sq_lt_domain hn_pos)
    have hd_C : HasDerivAt (fun t : ℝ => virasoroBChart n (t : ℂ))
        (deriv (virasoroBChart n) (u : ℂ)) u :=
      ((virasoroBChart_analyticOnNhd hn_pos (u : ℂ) hu_dom).differentiableAt.hasDerivAt).comp_ofReal
    have hd_re : HasDerivAt b_real (deriv (virasoroBChart n) (u : ℂ)).re u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    exact hd_re.deriv ▸ hd_re
  have hb_deriv_eq : ∀ u ∈ Icc u_lo u_hi,
      deriv (virasoroBChart n) (u : ℂ) = ((deriv b_real u : ℝ) : ℂ) := by
    intro u hu
    have hu_dom : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (hsub_ac u hu).trans (virasoroAC_sq_lt_domain hn_pos)
    have hd_C : HasDerivAt (fun t : ℝ => virasoroBChart n (t : ℂ))
        (deriv (virasoroBChart n) (u : ℂ)) u :=
      ((virasoroBChart_analyticOnNhd hn_pos (u : ℂ) hu_dom).differentiableAt.hasDerivAt).comp_ofReal
    have hd_re : HasDerivAt b_real (deriv (virasoroBChart n) (u : ℂ)).re u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    rw [hd_re.deriv]
    exact Complex.ext rfl (hb_deriv_im u hu)
  have hb_deriv_cont : ContinuousOn (deriv b_real) (Set.uIcc u_lo u_hi) := by
    rw [Set.uIcc_of_le hu_lo_lt_hi.le]
    have hcont_c : ContinuousOn (fun u : ℝ => (deriv (virasoroBChart n) (u : ℂ)).re) (Icc u_lo u_hi) := by
      refine Complex.continuous_re.comp_continuousOn
        ((virasoroBChart_analyticOnNhd hn_pos).deriv.continuousOn.comp continuous_ofReal.continuousOn
          fun u hu => ?_)
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (hsub_ac u hu).trans (virasoroAC_sq_lt_domain hn_pos)
    refine hcont_c.congr fun u hu => ?_
    have hd := congrArg Complex.re (hb_deriv_eq u hu)
    simpa [Complex.ofReal_re] using hd.symm
  have hb_u_lo : b_real u_lo = xiStar + r₀ := by
    have hof := virasoroBChart_ofReal hn_pos (hsub_ac u_lo ⟨le_rfl, hu_lo_lt_hi.le⟩).le
    have hdu := virasoroDeltaChart_uChart hn_pos
      (hξ_scale_lo ▸ (by
        have : 0 < xiStar - r₀ := by linarith [xiStar_pos]
        have : (xiStar - r₀) ^ 2 / 3 < (xiStar + r₀) ^ 2 / 3 := by nlinarith [hr₀_pos]
        linarith [hlo]))
      (hξ_scale_hi ▸ hhi.le)
    have hb_eq_sqrt : b_real u_lo = Real.sqrt (3 * virasoroDeltaChart n u_lo / n) := by
      have hre := congrArg Complex.re hof.2.2.1
      simpa [b_real, Complex.ofReal_re] using hre
    rw [hb_eq_sqrt, hdu]
    have h3 : 3 * (n * ((xiStar + r₀) ^ 2 / 3)) / n = (xiStar + r₀) ^ 2 := by
      field_simp [hn_pos.ne']
    rw [h3, Real.sqrt_sq (by linarith [xiStar_pos])]
  have hb_u_hi : b_real u_hi = xiStar - r₀ := by
    have hof := virasoroBChart_ofReal hn_pos (hsub_ac u_hi ⟨hu_lo_lt_hi.le, le_rfl⟩).le
    have hdu := virasoroDeltaChart_uChart hn_pos
      (hξ_scale_lo ▸ hlo.le)
      (hξ_scale_hi ▸ (by
        have : 0 < xiStar - r₀ := by linarith [xiStar_pos]
        have : (xiStar - r₀) ^ 2 / 3 < (xiStar + r₀) ^ 2 / 3 := by nlinarith [hr₀_pos]
        linarith [hhi]))
    have hb_eq_sqrt : b_real u_hi = Real.sqrt (3 * virasoroDeltaChart n u_hi / n) := by
      have hre := congrArg Complex.re hof.2.2.1
      simpa [b_real, Complex.ofReal_re] using hre
    rw [hb_eq_sqrt, hdu]
    have h3 : 3 * (n * ((xiStar - r₀) ^ 2 / 3)) / n = (xiStar - r₀) ^ 2 := by
      field_simp [hn_pos.ne']
    rw [h3, Real.sqrt_sq (by linarith [xiStar_pos])]
  have hb_pos_on : ∀ u ∈ Icc u_lo u_hi, 0 < b_real u := fun u hu =>
    (virasoroBChart_ofReal hn_pos (hsub_ac u hu).le).2.1
  let f_b : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
  have hf_cont : ContinuousOn f_b (b_real '' Set.uIcc u_lo u_hi) := by
    have hg_cont : Continuous (fun b : ℝ => (spinGcal a Φ (b : ℂ)).re) :=
      Complex.continuous_re.comp ((spinGcal_differentiableOn_strip hc hΦ).continuousOn.comp_continuous
        Complex.continuous_ofReal fun x => by change |(x : ℂ).im| < 1 / 2; simp [Complex.ofReal_im])
    have hL_cont : Continuous spinL := by unfold spinL; fun_prop
    exact ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hL_cont))).mul
      hg_cont).continuousOn
  have hcov := intervalIntegral.integral_comp_mul_deriv' hb_hasDeriv hb_deriv_cont hf_cont
  have hpt : ∀ u ∈ Icc u_lo u_hi,
      (spinPtilde c Φ (u : ℂ)).re = -((spinCalNorm c Φ)⁻¹ * (f_b (b_real u) * deriv b_real u)) := by
    intro u hu
    have hbof := hb_real_eq u hu
    have hdbof := hb_deriv_eq u hu
    have hbpos := hb_pos_on u hu
    have hL_eq : spinL (b_real u) = 2 * π / 3 * b_real u := by
      unfold spinL; rw [abs_of_pos hbpos]; ring
    have hg_im : (spinGcal a Φ (b_real u : ℂ)).im = 0 := spinGcal_im_ofReal ha_pos.le hΦ _
    have hg_eq : spinGcal a Φ (b_real u : ℂ) = ((spinGcal a Φ (b_real u : ℂ)).re : ℂ) :=
      Complex.ext rfl hg_im
    have hexp : Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * (b_real u : ℂ)) =
        ((Real.exp (n * spinL (b_real u)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp, hL_eq, mul_assoc]
    have hnum_eq : ((a : ℂ) *
        Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * (b_real u : ℂ)) *
        (-((deriv b_real u : ℝ) : ℂ)) * spinGcal a Φ (b_real u : ℂ)) =
        ((-(a * Real.exp (n * spinL (b_real u)) * (spinGcal a Φ (b_real u : ℂ)).re *
          deriv b_real u) : ℝ) : ℂ) := by
      rw [hexp]
      conv_lhs =>
        arg 2
        rw [hg_eq]
      rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        Complex.ofReal_inj]
      ring
    unfold spinPtilde
    change (((a : ℂ) *
        Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ)) *
        (-deriv (virasoroBChart n) (u : ℂ)) * spinGcal a Φ (virasoroBChart n (u : ℂ))) /
      (spinCalNorm c Φ : ℂ)).re = _
    rw [hbof, hdbof, hnum_eq, ← Complex.ofReal_div, Complex.ofReal_re, div_eq_mul_inv]
    dsimp [f_b]; ring
  have hL_eq : ∫ u in Icc u_lo u_hi, (spinPtilde c Φ (u : ℂ)).re =
      ∫ u in u_lo..u_hi, (spinPtilde c Φ (u : ℂ)).re := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu_lo_lt_hi.le]
  have hR_eq : ∫ b in I_b, f_b b = ∫ b in (xiStar - r₀)..(xiStar + r₀), f_b b := by
    have hle : xiStar - r₀ ≤ xiStar + r₀ := by linarith
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hint_congr : ∫ u in u_lo..u_hi, (spinPtilde c Φ (u : ℂ)).re =
      -((spinCalNorm c Φ)⁻¹ * ∫ u in u_lo..u_hi, f_b (b_real u) * deriv b_real u) := by
    have h1 : ∫ u in u_lo..u_hi, (spinPtilde c Φ (u : ℂ)).re =
        ∫ u in u_lo..u_hi, -((spinCalNorm c Φ)⁻¹ * (f_b (b_real u) * deriv b_real u)) :=
      intervalIntegral.integral_congr fun u hu => hpt u (Set.uIcc_of_le hu_lo_lt_hi.le ▸ hu)
    rw [h1, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  have hcov' : ∫ u in u_lo..u_hi, f_b (b_real u) * deriv b_real u =
      ∫ b in (b_real u_lo)..(b_real u_hi), f_b b := hcov
  rw [hL_eq, hR_eq, hint_congr, hcov', hb_u_lo, hb_u_hi,
    intervalIntegral.integral_symm (xiStar + r₀) (xiStar - r₀)]
  ring

private lemma spinGcal_re_even {a : ℝ} (ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    (b : ℝ) : (spinGcal a Φ ((-b : ℝ) : ℂ)).re = (spinGcal a Φ (b : ℂ)).re := by
  rw [spinGcal_re_ofReal ha hΦ (-b), spinGcal_re_ofReal ha hΦ b]
  congr 1
  have hsum : ∀ d : ℝ, spinHbCalReal (-b) (-d) * spinG a Φ (-b + -d) (-b - -d) =
      spinHbCalReal b d * spinG a Φ (b + d) (b - d) := fun d => by
    rw [spinHbCalReal_neg, show -b + -d = -(b + d) by ring, show -b - -d = -(b - d) by ring,
      spinG_d4_neg_left hΦ, spinG_d4_neg_right hΦ]
  rw [← integral_neg_eq_self (fun d => spinHbCalReal (-b) d * spinG a Φ (-b + d) (-b - d))]
  exact integral_congr_ae (Eventually.of_forall hsum)

/-- **`s4:5.2` (`spinning_s4.tex`, Proposition 5.2): exact Langer Jacobian identity and truncated
real-integral bound on `[u_lo, u_hi]`.** -/
theorem spinS4_5_2 : SpinS4_5_2 := by
  intro C₀ κ hC₀ hκ
  obtain ⟨r₀, hr₀_pos, hr₀_half, hlo, hhi⟩ := spinS4_5_2_r0_exists
  have hr₀_lt : r₀ < xiStar := hr₀_half.trans (by linarith [xiStar_pos])
  obtain ⟨_cσ, C₂₃, c₀_23, _, hC23_pos, hc0_23, h23⟩ := spinS4_2_3 (C_x := C₀)
  obtain ⟨C₂₄, C_p, c₀_24, hC24_pos, hCp_pos, hc0_24, h24⟩ :=
    spinS4_2_4 (C_x := C₀) (p := 3) (r₀ := r₀) (by norm_num) hr₀_pos hr₀_lt
  let c₀ : ℝ := max (max 40 c₀_23) (max c₀_24 (1 + (C₀ / r₀) ^ (3 / 2 : ℝ)))
  have hc0_40 : 40 ≤ c₀ := (le_max_left _ _).trans (le_max_left _ _)
  let C_κ : ℝ := (((C₂₃ + 1) / 2) + C₂₄ + C_p) / κ
  have hCκ_pos : 0 < C_κ := by positivity [hC23_pos, hC24_pos, hCp_pos, hκ]
  refine ⟨r₀, C_κ, c₀, hr₀_pos, hr₀_lt, hCκ_pos, hc0_40, ?_⟩
  intro c x₁ hc n a ε hx₁ Φ hS hB_lo
  have hc40 : 40 ≤ c := hc0_40.trans hc
  have hc23 : c₀_23 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc24 : c₀_24 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hceps : 1 + (C₀ / r₀) ^ (3 / 2 : ℝ) ≤ c :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hn_ge39 : 39 ≤ n := by dsimp [n]; linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have hε_pos : 0 < ε := by dsimp [ε]; exact Real.rpow_pos_of_pos hn_pos _
  have hid := spinS4_5_2_jacobian hc40 hr₀_pos hr₀_half hlo hhi hS.2.1
  refine ⟨hid, ?_⟩
  rw [hid]
  let I_b := Icc (xiStar - r₀) (xiStar + r₀)
  let Q : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
  have hQ_int : Integrable Q volume := integrable_spinCalInt_integrand hc40 hS.2.1
  have hQ_even : ∀ b : ℝ, Q (-b) = Q b := fun b => by
    dsimp [Q]
    have hL : spinL (-b) = spinL b := by unfold spinL; rw [abs_neg]
    rw [hL, spinGcal_re_even ha_pos.le hS.2.1 b]
  have hcal_23 := (h23 hc23 hS.1 (by linarith [(abs_le.mp hx₁).2] : x₁ ≤ xiStar + C₀ * n ^ (-(2 / 3 : ℝ)))
    hS.2.1 hS.2.2.1 hS.2.2.2.2).2.2 hS.2.2.2.1
  have hhalf_int : 2 * ∫ b in Ioi (0 : ℝ), Q b = spinCalInt c Φ := by
    have hneg_eq : ∫ b in Iio (0 : ℝ), Q b = ∫ b in Ioi (0 : ℝ), Q b := by
      rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
      rw [← integral_neg_eq_self (fun b => (Ioi (0 : ℝ)).indicator Q b)]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      by_cases hb : b < 0
      · have hnb : -b ∈ Ioi (0 : ℝ) := by simpa using hb
        have hbm : b ∈ Iio (0 : ℝ) := hb
        simp [Set.indicator_of_mem hbm, Set.indicator_of_mem hnb, hQ_even b]
      · have hnot1 : b ∉ Iio (0 : ℝ) := hb
        have hnot2 : -b ∉ Ioi (0 : ℝ) := fun h => hb (by simpa using h)
        simp [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
    have hunion : (∫ b in Iic (0 : ℝ), Q b) + ∫ b in Ioi (0 : ℝ), Q b = ∫ b : ℝ, Q b := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hQ_int.integrableOn
        hQ_int.integrableOn, Iic_union_Ioi, setIntegral_univ]
    rw [MeasureTheory.integral_Iic_eq_integral_Iio, hneg_eq] at hunion
    change _ = spinCalInt c Φ at hunion
    linarith
  have hIoi0_le : ∫ b in Ioi (0 : ℝ), Q b ≤ ((C₂₃ + 1) / 2) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
    linarith
  have hC0eps_r0 : C₀ * ε ≤ r₀ := by
    have h1 : (C₀ / r₀) ^ (3 / 2 : ℝ) ≤ n := by dsimp [n]; linarith
    have h2 : C₀ / r₀ ≤ n ^ (2 / 3 : ℝ) := by
      have hpow := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num,
        Real.rpow_one] at hpow
      exact hpow
    calc C₀ * ε = r₀ * ((C₀ / r₀) * n ^ (-(2 / 3 : ℝ))) := by dsimp [ε]; field_simp [hr₀_pos.ne']
      _ ≤ r₀ * (n ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ))) := by gcongr
      _ = r₀ * 1 := by rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
      _ = r₀ := mul_one r₀
  have hx1_le_hi : x₁ ≤ xiStar + r₀ := by
    have := (abs_le.mp hx₁).2
    linarith
  have hQ_ext_nn : 0 ≤ ∫ b in Ioi (xiStar + r₀), Q b := by
    refine setIntegral_nonneg measurableSet_Ioi fun b hb => ?_
    have hgb := spinGcal_re_nonneg_of_ge ha_pos.le hS.2.1 hS.1 hS.2.2.2.2 (b := b)
      (by linarith [mem_Ioi.mp hb, hx1_le_hi])
    exact mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) hgb
  -- Split `(0, ∞)` into `(0, ξ_* - r₀] ∪ [ξ_* - r₀, ξ_* + r₀] ∪ (ξ_* + r₀, ∞)`
  have hxs_m_pos : 0 < xiStar - r₀ := by linarith [xiStar_pos]
  have hxs_m_le_p : xiStar - r₀ ≤ xiStar + r₀ := by linarith
  have hsplit_top : ∫ b in Ioi (0 : ℝ), Q b =
      (∫ b in Ioc (0 : ℝ) (xiStar + r₀), Q b) + ∫ b in Ioi (xiStar + r₀), Q b := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hQ_int.integrableOn hQ_int.integrableOn, Ioc_union_Ioi_eq_Ioi (by linarith [xiStar_pos])]
  have hsplit_mid : ∫ b in Ioc (0 : ℝ) (xiStar + r₀), Q b =
      (∫ b in Ioc (0 : ℝ) (xiStar - r₀), Q b) + ∫ b in I_b, Q b := by
    dsimp [I_b]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    have h1 : Ioc (0 : ℝ) (xiStar - r₀) ∪ Ioc (xiStar - r₀) (xiStar + r₀) = Ioc (0 : ℝ) (xiStar + r₀) :=
      Ioc_union_Ioc_eq_Ioc hxs_m_pos.le hxs_m_le_p
    have h2 := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl _)) measurableSet_Ioc
      (hQ_int.integrableOn (s := Ioc 0 (xiStar - r₀)))
      (hQ_int.integrableOn (s := Ioc (xiStar - r₀) (xiStar + r₀)))
    rw [h1] at h2
    exact h2
  -- Bound negative mass on `(0, ξ_* - r₀]` via `spinS4_2_4`
  have h24_bd := (h24 hc24 (by linarith [(abs_le.mp hx₁).2] : x₁ ≤ xiStar + C₀ * n ^ (-(2 / 3 : ℝ))) hS).2.2.2
  let Gplus : ℝ × ℝ → ℝ := fun q => max (spinG a Φ q.1 q.2) 0
  let Gminus : ℝ × ℝ → ℝ := fun q => max (-spinG a Φ q.1 q.2) 0
  have hQmax_int : Integrable (fun b : ℝ => max (-Q b) 0) volume := by
    refine hQ_int.norm.mono' (hQ_int.aestronglyMeasurable.neg.sup aestronglyMeasurable_const)
      (Eventually.of_forall fun b => ?_)
    rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hGm_int : ∫ b in Ioc (0 : ℝ) (xiStar - r₀), max (-Q b) 0 ≤
      (spinRhoProjMeasure c Gminus (Icc 0 (xiStar - r₀))).toReal := by
    let f_m : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * spinCalProjFn Gminus b
    have hfm_nn : ∀ b : ℝ, 0 ≤ f_m b := fun b => by
      refine mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) ?_
      unfold spinCalProjFn
      refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
      rw [spinHbCal_ofReal, Complex.ofReal_re]
      exact mul_nonneg (spinHbCalReal_nonneg b d) (le_max_right _ _)
    have hG_meas : Measurable (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
      unfold spinG
      exact (hS.2.1.cont.comp ((continuous_const.mul continuous_fst).prodMk
        (continuous_const.mul continuous_snd))).measurable
    have hGp_meas : Measurable Gplus := hG_meas.max measurable_const
    have hGm_meas : Measurable Gminus := hG_meas.neg.max measurable_const
    have hGp_bd : ∀ p : ℝ × ℝ, |Gplus p| ≤ |spinG a Φ p.1 p.2| := fun p => by
      rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)
    have hGm_bd : ∀ p : ℝ × ℝ, |Gminus p| ≤ |spinG a Φ p.1 p.2| := fun p => by
      rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (neg_le_abs _) (abs_nonneg _)
    have hGp_sym : (∀ x y, Gplus (-x, y) = Gplus (x, y)) ∧ (∀ x y, Gplus (x, -y) = Gplus (x, y)) :=
      ⟨fun x y => by dsimp [Gplus]; rw [spinG_d4_neg_left hS.2.1],
       fun x y => by dsimp [Gplus]; rw [spinG_d4_neg_right hS.2.1]⟩
    have hGm_sym : (∀ x y, Gminus (-x, y) = Gminus (x, y)) ∧ (∀ x y, Gminus (x, -y) = Gminus (x, y)) :=
      ⟨fun x y => by dsimp [Gminus]; rw [spinG_d4_neg_left hS.2.1],
       fun x y => by dsimp [Gminus]; rw [spinG_d4_neg_right hS.2.1]⟩
    let φ : ℝ → ℝ := (Icc 0 (xiStar - r₀)).indicator (fun _ => 1)
    have hφ_meas : Measurable φ := measurable_const.indicator measurableSet_Icc
    have hφ_bd : ∀ x : ℝ, |φ x| ≤ 1 := fun x => by
      dsimp [φ]; by_cases hx : x ∈ Icc 0 (xiStar - r₀) <;> simp [hx]
    have hadj_p := spinCal_adjoint_identity hc40 hS.2.1 hGp_meas hGp_bd hGp_sym.1 hGp_sym.2
      (φ := fun _ : ℝ => (1 : ℝ)) measurable_const zero_le_one (fun _ => by norm_num)
    have hadj_m1 := spinCal_adjoint_identity hc40 hS.2.1 hGm_meas hGm_bd hGm_sym.1 hGm_sym.2
      (φ := fun _ : ℝ => (1 : ℝ)) measurable_const zero_le_one (fun _ => by norm_num)
    have hadj := spinCal_adjoint_identity hc40 hS.2.1 hGm_meas hGm_bd hGm_sym.1 hGm_sym.2
      hφ_meas zero_le_one hφ_bd
    have hfm_int : Integrable (fun b : ℝ => (Icc 0 (xiStar - r₀)).indicator 1 |b| * f_m b) := by
      have hprod : Integrable (fun p : ℝ × ℝ =>
          a * Real.exp (n * spinL p.1) * (Icc 0 (xiStar - r₀)).indicator 1 |p.1| *
            (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * Gminus (p.1 + p.2, p.1 - p.2)))
          (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hadj.1
      have hleft := hprod.integral_prod_left
      have hfun : (fun b : ℝ => ∫ d : ℝ, a * Real.exp (n * spinL b) *
          (Icc 0 (xiStar - r₀)).indicator 1 |b| *
            (4 * spinCalF xiStar ^ 2 * spinHbCalReal b d * Gminus (b + d, b - d))) =
          fun b : ℝ => (Icc 0 (xiStar - r₀)).indicator 1 |b| * f_m b := by
        ext b
        have heq_in : (∫ d : ℝ, a * Real.exp (n * spinL b) *
            (Icc 0 (xiStar - r₀)).indicator 1 |b| *
              (4 * spinCalF xiStar ^ 2 * spinHbCalReal b d * Gminus (b + d, b - d))) =
            a * Real.exp (n * spinL b) * (Icc 0 (xiStar - r₀)).indicator 1 |b| *
              (4 * spinCalF xiStar ^ 2) * ∫ d : ℝ, spinHbCalReal b d * Gminus (b + d, b - d) := by
          rw [← integral_const_mul]
          congr 1; ext d; ring
        rw [heq_in]
        dsimp [f_m]; unfold spinCalProjFn
        have heq2 : (∫ d : ℝ, (spinHbCal (b : ℂ) d).re * Gminus (b + d, b - d)) =
            ∫ d : ℝ, spinHbCalReal b d * Gminus (b + d, b - d) :=
          integral_congr_ae (Eventually.of_forall fun d => by
            dsimp only; rw [spinHbCal_ofReal, Complex.ofReal_re])
        rw [heq2]; ring
      rwa [hfun] at hleft
    have hrho_eq : (spinRhoProjMeasure c Gminus (Icc 0 (xiStar - r₀))).toReal =
        ∫ b : ℝ, (Icc 0 (xiStar - r₀)).indicator 1 |b| * f_m b := by
      have hmabs : MeasurableSet (abs ⁻¹' Icc 0 (xiStar - r₀)) := continuous_abs.measurable measurableSet_Icc
      have hmax : (fun b : ℝ => ENNReal.ofReal (a * Real.exp (n * spinL b) * max (spinCalProjFn Gminus b) 0)) =
          fun b : ℝ => ENNReal.ofReal (f_m b) := by
        ext b
        have hcp : 0 ≤ spinCalProjFn Gminus b := by
          unfold spinCalProjFn
          refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
          rw [spinHbCal_ofReal, Complex.ofReal_re]
          exact mul_nonneg (spinHbCalReal_nonneg b d) (le_max_right _ _)
        dsimp [f_m]; rw [max_eq_left hcp]
      have hmeq : spinRhoProjMeasure c Gminus (Icc 0 (xiStar - r₀)) =
          ∫⁻ b : ℝ, ENNReal.ofReal ((Icc 0 (xiStar - r₀)).indicator 1 |b| * f_m b) := by
        unfold spinRhoProjMeasure
        rw [Measure.map_apply continuous_abs.measurable measurableSet_Icc,
          withDensity_apply _ hmabs, hmax, ← lintegral_indicator hmabs]
        refine lintegral_congr fun b => ?_
        by_cases hb : |b| ∈ Icc 0 (xiStar - r₀) <;> simp [hb]
      rw [hmeq, ← ofReal_integral_eq_lintegral_ofReal hfm_int
        (Eventually.of_forall fun b => by
          by_cases hb : |b| ∈ Icc 0 (xiStar - r₀)
          · simp [hb, hfm_nn b]
          · simp [hb]),
        ENNReal.toReal_ofReal (integral_nonneg fun b => by
          by_cases hb : |b| ∈ Icc 0 (xiStar - r₀)
          · simp [hb, hfm_nn b]
          · simp [hb])]
    have hae_split : ∀ᵐ b : ℝ ∂volume,
        (spinGcal a Φ (b : ℂ)).re = spinCalProjFn Gplus b - spinCalProjFn Gminus b := by
      have hHp_prod : Integrable (fun p : ℝ × ℝ =>
          a * Real.exp (n * spinL p.1) * 1 *
            (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * Gplus (p.1 + p.2, p.1 - p.2)))
          (volume.prod volume) := by rw [← Measure.volume_eq_prod]; exact hadj_p.1
      have hHm_prod : Integrable (fun p : ℝ × ℝ =>
          a * Real.exp (n * spinL p.1) * 1 *
            (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * Gminus (p.1 + p.2, p.1 - p.2)))
          (volume.prod volume) := by rw [← Measure.volume_eq_prod]; exact hadj_m1.1
      filter_upwards [hHp_prod.prod_right_ae, hHm_prod.prod_right_ae] with b hbp hbm
      have hC_pos : 0 < a * Real.exp (n * spinL b) * 1 * (4 * spinCalF xiStar ^ 2) :=
        mul_pos (mul_pos (mul_pos ha_pos (Real.exp_pos _)) one_pos)
          (mul_pos (by norm_num) (pow_pos (spinCalF_pos' xiStar_pos) 2))
      have hFne := (spinCalF_pos' xiStar_pos).ne'
      have hbp' : Integrable (fun d : ℝ => spinHbCalReal b d * Gplus (b + d, b - d)) volume := by
        have h := hbp.const_mul (a * Real.exp (n * spinL b) * 1 * (4 * spinCalF xiStar ^ 2))⁻¹
        refine h.congr (Eventually.of_forall fun d => ?_)
        have hCne := hC_pos.ne'; dsimp only; field_simp [hCne, hFne]
      have hbm' : Integrable (fun d : ℝ => spinHbCalReal b d * Gminus (b + d, b - d)) volume := by
        have h := hbm.const_mul (a * Real.exp (n * spinL b) * 1 * (4 * spinCalF xiStar ^ 2))⁻¹
        refine h.congr (Eventually.of_forall fun d => ?_)
        have hCne := hC_pos.ne'; dsimp only; field_simp [hCne, hFne]
      rw [spinGcal_re_ofReal ha_pos.le hS.2.1 b]
      have hsplit : (fun d : ℝ => spinHbCalReal b d * spinG a Φ (b + d) (b - d)) =
          fun d : ℝ => spinHbCalReal b d * Gplus (b + d, b - d) -
            spinHbCalReal b d * Gminus (b + d, b - d) := by
        ext d
        have hg : spinG a Φ (b + d) (b - d) = Gplus (b + d, b - d) - Gminus (b + d, b - d) := by
          dsimp [Gplus, Gminus]; linarith [max_zero_sub_max_neg_zero_eq_self (spinG a Φ (b + d) (b - d))]
        rw [hg, mul_sub]
      rw [hsplit, integral_sub hbp' hbm', mul_sub]
      unfold spinCalProjFn
      have hre_p : (fun d : ℝ => (spinHbCal (b : ℂ) d).re * Gplus (b + d, b - d)) =
          fun d => spinHbCalReal b d * Gplus (b + d, b - d) := by
        ext d; rw [spinHbCal_ofReal, Complex.ofReal_re]
      have hre_m : (fun d : ℝ => (spinHbCal (b : ℂ) d).re * Gminus (b + d, b - d)) =
          fun d => spinHbCalReal b d * Gminus (b + d, b - d) := by
        ext d; rw [spinHbCal_ofReal, Complex.ofReal_re]
      rw [hre_p, hre_m]
    have hae_bd : ∀ᵐ b ∂(volume.restrict (Ioc (0 : ℝ) (xiStar - r₀))),
        max (-Q b) 0 ≤ (Icc 0 (xiStar - r₀)).indicator 1 |b| * f_m b := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hae_split] with b hb hsp
      have hmem : |b| ∈ Icc 0 (xiStar - r₀) := by rw [abs_of_pos hb.1]; exact ⟨hb.1.le, hb.2⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      have hGp_nn : 0 ≤ spinCalProjFn Gplus b := by
        unfold spinCalProjFn
        refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
        rw [spinHbCal_ofReal, Complex.ofReal_re]
        exact mul_nonneg (spinHbCalReal_nonneg b d) (le_max_right _ _)
      have hneg_le : -(spinGcal a Φ (b : ℂ)).re ≤ spinCalProjFn Gminus b := by linarith [hsp, hGp_nn]
      have hQ_neg : -Q b ≤ f_m b := by
        dsimp [Q, f_m]; rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left hneg_le (mul_nonneg ha_pos.le (Real.exp_pos _).le)
      exact max_le hQ_neg (hfm_nn b)
    rw [hrho_eq]
    have hmono := setIntegral_mono_ae_restrict hQmax_int.integrableOn hfm_int.integrableOn hae_bd
    exact hmono.trans (setIntegral_le_integral hfm_int (Eventually.of_forall fun b => by
      by_cases hb : |b| ∈ Icc 0 (xiStar - r₀)
      · simp [hb, hfm_nn b]
      · simp [hb]))
  have hn3_le_dn : n ^ (-(3 : ℝ)) ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n := by
    have h1 : n ^ (-(3 : ℝ)) ≤ n⁻¹ := by
      rw [← Real.rpow_neg_one n]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact h1.trans (deltaN_ge_inv hn_ge39)
  have hneg_Ioc_le : -∫ b in Ioc (0 : ℝ) (xiStar - r₀), Q b ≤
      (C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
    have hle1 : -∫ b in Ioc (0 : ℝ) (xiStar - r₀), Q b ≤
        ∫ b in Ioc (0 : ℝ) (xiStar - r₀), max (-Q b) 0 := by
      rw [← integral_neg]
      exact setIntegral_mono_on hQ_int.neg.integrableOn
        hQmax_int.integrableOn measurableSet_Ioc fun b _ => le_max_left _ _
    have hle2 : (spinRhoProjMeasure c Gminus (Icc 0 (xiStar - r₀))).toReal ≤
        (C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      have h1 := h24_bd
      nlinarith [hCp_pos, hn3_le_dn]
    exact (hle1.trans hGm_int).trans hle2
  have hI_b_le : ∫ b in I_b, Q b ≤
      (((C₂₃ + 1) / 2) + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
    linarith [hIoi0_le, hQ_ext_nn, hsplit_top, hsplit_mid, hneg_Ioc_le]
  have hB_pos : 0 < spinCalNorm c Φ := hκ.trans_le hB_lo
  calc (spinCalNorm c Φ)⁻¹ * ∫ b in I_b, a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
      ≤ κ⁻¹ * ((((C₂₃ + 1) / 2) + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n)) := by
        have h1 : (spinCalNorm c Φ)⁻¹ ≤ κ⁻¹ := (inv_le_inv₀ hB_pos hκ).mpr hB_lo
        have hI_nn_or : 0 ≤ (((C₂₃ + 1) / 2) + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
          have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ n)
          positivity [hC23_pos, hC24_pos, hCp_pos]
        by_cases hInt_nn : 0 ≤ ∫ b in I_b, Q b
        · exact mul_le_mul h1 hI_b_le hInt_nn (inv_pos.mpr hκ).le
        · have hneg : (spinCalNorm c Φ)⁻¹ * ∫ b in I_b, Q b ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hB_pos).le (le_of_not_ge hInt_nn)
          exact hneg.trans (mul_nonneg (inv_pos.mpr hκ).le hI_nn_or)
    _ = C_κ * n ^ (-(2 / 3 : ℝ)) * Real.log n := by dsimp [C_κ]; ring

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_5_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_5_2

end FormalResearch.ModularBootstrap.Spin
