/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_2
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1Airy
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds

/-!
# Section 6.1 Disc & `QuantC1B2Holds` Helpers (`s4:6.1`)

Proves:
- `spinPtilde_re_nonneg_of_le` and `spinPtilde_jacobian_on`: exact Langer Jacobian on arbitrary
  subintervals inside the chart disc, positivity beyond the gap threshold `x₁`, and `L¹ ≤ 1/2`.
- `spinPtilde_tail_le_of_env`: exponential real-axis Airy decay from `spinS4_5_1`.
- `spinPtilde_quant_c1`: `QuantC1B2Holds (fun u => 2 * spinPtilde c Φ u) u_T` uniformly at large `c`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal Interval
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.Special

lemma deriv_airyAiC_ofReal' (x : ℝ) : deriv airyAiC (x : ℂ) = (airyAi' x : ℂ) := by
  have hd_c : HasDerivAt (fun t : ℝ => airyAiC (t : ℂ)) (deriv airyAiC (x : ℂ)) x :=
    (differentiable_airyAiC (x : ℂ)).hasDerivAt.comp_ofReal
  have heq : (fun t : ℝ => airyAiC (t : ℂ)) = (fun t : ℝ => (airyAi t : ℂ)) :=
    funext airyAiC_ofReal
  rw [heq] at hd_c
  exact hd_c.unique (hasDerivAt_airyAi x).ofReal_comp

lemma circleMap_mem_slitPlane' {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo (-π) π) :
    circleMap 0 R θ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hθ0 : θ = 0
  · left; subst hθ0; simpa [circleMap] using hR
  · right
    have him_eq : (circleMap 0 R θ).im = R * Real.sin θ := by
      rw [circleMap, zero_add, Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re]
    rw [him_eq]
    have hsin_ne : Real.sin θ ≠ 0 := by
      rcases lt_or_gt_of_ne hθ0 with hlt | hlt
      · rw [← neg_ne_zero, ← Real.sin_neg]
        exact (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hlt) (by linarith [hθ.1])).ne'
      · exact (Real.sin_pos_of_pos_of_lt_pi hlt hθ.2).ne'
    exact mul_ne_zero hR.ne' hsin_ne

lemma virasoroDeltaChart_div_scale_eq' {n : ℝ} (hn : 0 < n) (x : ℝ) :
    virasoroDeltaChart n (x * n ^ (2 / 3 : ℝ)) / n = virasoroDeltaChart 1 x := by
  unfold virasoroDeltaChart virasoroXiChartC
  have hr : ((x * n ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ((n ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
      (x : ℂ) * (((1 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.one_rpow, mul_one, mul_assoc,
      ← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [hr, mul_div_cancel_left₀ _ hn.ne', one_mul]

lemma virasoroUChart_scale_eq' {n : ℝ} (_hn : 0 < n) (ξ : ℝ) :
    virasoroUChart n ξ = n ^ (2 / 3 : ℝ) * virasoroUChart 1 ξ := by
  unfold virasoroUChart
  rw [Real.one_rpow, one_mul]

lemma virasoroBChart_ofReal_eq_sqrt {n u : ℝ} (hn : 0 < n) (hu : |u| ≤ virasoroAC n ^ 2) :
    virasoroBChart n (u : ℂ) = (Real.sqrt (3 * virasoroDeltaChart n u / n) : ℂ) ∧
    (virasoroBChart n (u : ℂ)).re = Real.sqrt (3 * virasoroDeltaChart n u / n) ∧
    0 < (virasoroBChart n (u : ℂ)).re := by
  have hof := virasoroBChart_ofReal hn hu
  have hre : (virasoroBChart n (u : ℂ)).re = Real.sqrt (3 * virasoroDeltaChart n u / n) := by
    have h := congrArg Complex.re hof.2.2.1
    simpa [Complex.ofReal_re] using h
  exact ⟨hof.2.2.1, hre, hre ▸ hof.2.1⟩

lemma bReal_antitoneOn {n : ℝ} (hn : 0 < n) :
    AntitoneOn (fun u : ℝ => (virasoroBChart n (u : ℂ)).re)
      (Icc (-(virasoroAC n ^ 2)) (virasoroAC n ^ 2)) := by
  intro u hu v hv huv
  dsimp only
  rw [(virasoroBChart_ofReal_eq_sqrt hn (abs_le.mpr hu)).2.1,
      (virasoroBChart_ofReal_eq_sqrt hn (abs_le.mpr hv)).2.1]
  refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hn.le)
  exact (virasoroDeltaChart_strictAnti hn).antitoneOn hu hv huv

lemma spinPtilde_re_eq_and_deriv_nonpos {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {u : ℝ} (hu_lt : |u| < virasoroAC (c - 1) ^ 2) :
    let n := c - 1
    let a := n / 12
    let b_real : ℝ → ℝ := fun t => (virasoroBChart n (t : ℂ)).re
    deriv b_real u ≤ 0 ∧
    (spinPtilde c Φ (u : ℂ)).re =
      (spinCalNorm c Φ)⁻¹ *
        (a * Real.exp (n * spinL (b_real u)) * (spinGcal a Φ (b_real u : ℂ)).re *
          (-deriv b_real u)) := by
  intro n a b_real
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have hu_le_ac : |u| ≤ virasoroAC n ^ 2 := hu_lt.le
  obtain ⟨hbof, _, hb_pos⟩ := virasoroBChart_ofReal_eq_sqrt hn_pos hu_le_ac
  have hu_dom : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hu_lt.trans (virasoroAC_sq_lt_domain hn_pos)
  have hd_C : HasDerivAt (fun t : ℝ => virasoroBChart n (t : ℂ))
      (deriv (virasoroBChart n) (u : ℂ)) u :=
    ((virasoroBChart_analyticOnNhd hn_pos (u : ℂ) hu_dom).differentiableAt.hasDerivAt).comp_ofReal
  have hd_im : (deriv (virasoroBChart n) (u : ℂ)).im = 0 := by
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    have hev : (fun t : ℝ => (virasoroBChart n (t : ℂ)).im) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hu_lt)] with t ht
      exact (virasoroBChart_ofReal hn_pos (abs_lt.mpr ht).le).1
    exact h1.unique ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev)
  have hd_re : HasDerivAt b_real (deriv b_real u) u := by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    exact h1.deriv ▸ h1
  have hdbof : deriv (virasoroBChart n) (u : ℂ) = ((deriv b_real u : ℝ) : ℂ) := by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    have h2 : deriv b_real u = (deriv (virasoroBChart n) (u : ℂ)).re := h1.deriv
    rw [h2]; exact Complex.ext rfl hd_im
  have hd_nonpos : deriv b_real u ≤ 0 := by
    have hanti := bReal_antitoneOn hn_pos
    have ht_nhd : ∀ᶠ t in 𝓝[>] u, t ∈ Icc (-(virasoroAC n ^ 2)) (virasoroAC n ^ 2) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds (abs_lt.mp hu_lt))] with t ht
      exact Ioo_subset_Icc_self ht
    have hq_nonpos : ∀ᶠ t in 𝓝[>] u, slope b_real u t ≤ 0 := by
      filter_upwards [ht_nhd, self_mem_nhdsWithin] with t ht hut
      have hsub : b_real t ≤ b_real u := hanti (abs_le.mp hu_le_ac) ht (le_of_lt hut)
      rw [slope_def_field]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsub) (sub_pos.mpr (mem_Ioi.mp hut)).le
    have hmono_nhds : 𝓝[>] u ≤ 𝓝[≠] u := nhdsWithin_mono u fun _ ht => ne_of_gt (mem_Ioi.mp ht)
    exact le_of_tendsto (hd_re.tendsto_slope.mono_left hmono_nhds) hq_nonpos
  refine ⟨hd_nonpos, ?_⟩
  have hL_eq : spinL (b_real u) = 2 * π / 3 * b_real u := by
    unfold spinL; rw [abs_of_pos hb_pos]; ring
  have hg_im : (spinGcal a Φ (b_real u : ℂ)).im = 0 := spinGcal_im_ofReal ha_pos.le hΦ _
  have hg_eq : spinGcal a Φ (b_real u : ℂ) = ((spinGcal a Φ (b_real u : ℂ)).re : ℂ) :=
    Complex.ext rfl hg_im
  have hexp : Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * (b_real u : ℂ)) =
      ((Real.exp (n * spinL (b_real u)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp, hL_eq, mul_assoc]
  have hbof' : virasoroBChart n (u : ℂ) = (b_real u : ℂ) := Complex.ext rfl (virasoroBChart_ofReal hn_pos hu_le_ac).1
  have hnum_eq : ((a : ℂ) *
      Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * (b_real u : ℂ)) *
      (-((deriv b_real u : ℝ) : ℂ)) * spinGcal a Φ (b_real u : ℂ)) =
      ((a * Real.exp (n * spinL (b_real u)) * (spinGcal a Φ (b_real u : ℂ)).re *
        (-deriv b_real u) : ℝ) : ℂ) := by
    rw [hexp]
    conv_lhs => arg 2; rw [hg_eq]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_inj]
    ring
  unfold spinPtilde
  change (((a : ℂ) *
      Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ)) *
      (-deriv (virasoroBChart n) (u : ℂ)) * spinGcal a Φ (virasoroBChart n (u : ℂ))) /
    (spinCalNorm c Φ : ℂ)).re = _
  rw [hbof', hdbof, hnum_eq, ← Complex.ofReal_div, Complex.ofReal_re, div_eq_mul_inv]
  ring

lemma spinPtilde_re_nonneg_of_le {c x₁ u_T u : ℝ} (hc : 40 ≤ c)
    (hx₁ : 0 ≤ x₁) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    (hgap : ∀ ξ d : ℝ, x₁ ^ 2 ≤ ξ ^ 2 + d ^ 2 → 0 ≤ spinG ((c - 1) / 12) Φ (ξ + d) (ξ - d))
    (hB_nn : 0 ≤ spinCalNorm c Φ)
    (huT : |u_T| ≤ virasoroAC (c - 1) ^ 2) (hx1_eq : (virasoroBChart (c - 1) (u_T : ℂ)).re = x₁)
    (hu_lt : |u| < virasoroAC (c - 1) ^ 2) (hu_le : u ≤ u_T) :
    0 ≤ (spinPtilde c Φ (u : ℂ)).re := by
  set n := c - 1
  set a := n / 12
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  obtain ⟨hd_nonpos, hre⟩ := spinPtilde_re_eq_and_deriv_nonpos hc hΦ hu_lt
  rw [hre]
  have hb_ge : x₁ ≤ (virasoroBChart n (u : ℂ)).re := by
    rw [← hx1_eq]
    exact bReal_antitoneOn hn_pos (abs_le.mp hu_lt.le) (abs_le.mp huT) hu_le
  have hG_nn : 0 ≤ (spinGcal a Φ ((virasoroBChart n (u : ℂ)).re : ℂ)).re :=
    spinGcal_re_nonneg_of_ge ha_pos.le hΦ hx₁ hgap hb_ge
  exact mul_nonneg (inv_nonneg.mpr hB_nn)
    (mul_nonneg (mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) hG_nn) (neg_nonneg.mpr hd_nonpos))

lemma spinPtilde_jacobian_on {c u₁ u₂ : ℝ} (hc : 40 ≤ c)
    (h1_gt : -(virasoroAC (c - 1) ^ 2) < u₁) (h12 : u₁ ≤ u₂) (h2_lt : u₂ < virasoroAC (c - 1) ^ 2)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    (hB_pos : 0 < spinCalNorm c Φ) :
    let n := c - 1
    let a := n / 12
    let b₁ := (virasoroBChart n (u₂ : ℂ)).re
    let b₂ := (virasoroBChart n (u₁ : ℂ)).re
    let Q : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
    b₁ ≤ b₂ ∧ 0 < b₁ ∧
    (∫ u in u₁..u₂, (spinPtilde c Φ (u : ℂ)).re) = (spinCalNorm c Φ)⁻¹ * ∫ b in b₁..b₂, Q b ∧
    (∫ u in u₁..u₂, |(spinPtilde c Φ (u : ℂ)).re|) = (spinCalNorm c Φ)⁻¹ * ∫ b in b₁..b₂, |Q b| ∧
    (∫ u in u₁..u₂, max 0 (-(spinPtilde c Φ (u : ℂ)).re)) =
      (spinCalNorm c Φ)⁻¹ * ∫ b in b₁..b₂, max (-Q b) 0 ∧
    (∫ u in u₁..u₂, |(spinPtilde c Φ (u : ℂ)).re|) ≤ 1 / 2 := by
  intro n a b₁ b₂ Q
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have hsub_ac : ∀ u ∈ Icc u₁ u₂, |u| < virasoroAC n ^ 2 := fun u hu =>
    abs_lt.mpr ⟨h1_gt.trans_le hu.1, hu.2.trans_lt h2_lt⟩
  have hb₁₂ : b₁ ≤ b₂ :=
    bReal_antitoneOn hn_pos ⟨h1_gt.le, (h12.trans_lt h2_lt).le⟩
      ⟨(h1_gt.trans_le h12).le, h2_lt.le⟩ h12
  have hb₁_pos : 0 < b₁ := (virasoroBChart_ofReal_eq_sqrt hn_pos
    (abs_lt.mpr ⟨h1_gt.trans_le h12, h2_lt⟩).le).2.2
  let b_real : ℝ → ℝ := fun u => (virasoroBChart n (u : ℂ)).re
  have hb_hasDeriv : ∀ u ∈ Set.uIcc u₁ u₂, HasDerivAt b_real (deriv b_real u) u := by
    intro u hu
    rw [Set.uIcc_of_le h12] at hu
    have hu_dom : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (hsub_ac u hu).trans (virasoroAC_sq_lt_domain hn_pos)
    have hd_C : HasDerivAt (fun t : ℝ => virasoroBChart n (t : ℂ))
        (deriv (virasoroBChart n) (u : ℂ)) u :=
      ((virasoroBChart_analyticOnNhd hn_pos (u : ℂ) hu_dom).differentiableAt.hasDerivAt).comp_ofReal
    have hd_re : HasDerivAt b_real (deriv (virasoroBChart n) (u : ℂ)).re u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    exact hd_re.deriv ▸ hd_re
  have hb_deriv_cont : ContinuousOn (deriv b_real) (Set.uIcc u₁ u₂) := by
    rw [Set.uIcc_of_le h12]
    have hcont_c : ContinuousOn (fun u : ℝ => (deriv (virasoroBChart n) (u : ℂ)).re) (Icc u₁ u₂) := by
      refine Complex.continuous_re.comp_continuousOn
        ((virasoroBChart_analyticOnNhd hn_pos).deriv.continuousOn.comp continuous_ofReal.continuousOn
          fun u hu => ?_)
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (hsub_ac u hu).trans (virasoroAC_sq_lt_domain hn_pos)
    refine hcont_c.congr fun u hu => ?_
    have hu_dom : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (hsub_ac u hu).trans (virasoroAC_sq_lt_domain hn_pos)
    have hd_C : HasDerivAt (fun t : ℝ => virasoroBChart n (t : ℂ))
        (deriv (virasoroBChart n) (u : ℂ)) u :=
      ((virasoroBChart_analyticOnNhd hn_pos (u : ℂ) hu_dom).differentiableAt.hasDerivAt).comp_ofReal
    have hd_re : HasDerivAt b_real (deriv (virasoroBChart n) (u : ℂ)).re u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    exact hd_re.deriv
  have hQ_cont : Continuous Q := by
    have hg_cont : Continuous (fun b : ℝ => (spinGcal a Φ (b : ℂ)).re) :=
      Complex.continuous_re.comp ((spinGcal_differentiableOn_strip hc hΦ).continuousOn.comp_continuous
        Complex.continuous_ofReal fun x => by change |(x : ℂ).im| < 1 / 2; simp [Complex.ofReal_im])
    have hL_cont : Continuous spinL := by unfold spinL; fun_prop
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hL_cont))).mul hg_cont
  have hcov_id : ∫ u in u₁..u₂, (spinPtilde c Φ (u : ℂ)).re =
      (spinCalNorm c Φ)⁻¹ * ∫ b in b₁..b₂, Q b := by
    have hcov : ∫ u in u₁..u₂, Q (b_real u) * deriv b_real u = ∫ b in b_real u₁..b_real u₂, Q b :=
      intervalIntegral.integral_comp_mul_deriv' hb_hasDeriv hb_deriv_cont hQ_cont.continuousOn
    have hcong : ∫ u in u₁..u₂, (spinPtilde c Φ (u : ℂ)).re =
        -(spinCalNorm c Φ)⁻¹ * ∫ u in u₁..u₂, Q (b_real u) * deriv b_real u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le h12] at hu
      have hre := (spinPtilde_re_eq_and_deriv_nonpos hc hΦ (hsub_ac u hu)).2
      dsimp only [Q, b_real, a, n] at hre ⊢; linarith only [hre]
    rw [hcong, hcov, intervalIntegral.integral_symm b₁ b₂]
    ring
  have hcov_abs : ∫ u in u₁..u₂, |(spinPtilde c Φ (u : ℂ)).re| =
      (spinCalNorm c Φ)⁻¹ * ∫ b in b₁..b₂, |Q b| := by
    have hcov : ∫ u in u₁..u₂, |Q (b_real u)| * deriv b_real u = ∫ b in b_real u₁..b_real u₂, |Q b| :=
      intervalIntegral.integral_comp_mul_deriv' hb_hasDeriv hb_deriv_cont hQ_cont.abs.continuousOn
    have hcong : ∫ u in u₁..u₂, |(spinPtilde c Φ (u : ℂ)).re| =
        -(spinCalNorm c Φ)⁻¹ * ∫ u in u₁..u₂, |Q (b_real u)| * deriv b_real u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le h12] at hu
      obtain ⟨hd_nonpos, hre⟩ := spinPtilde_re_eq_and_deriv_nonpos hc hΦ (hsub_ac u hu)
      dsimp only [Q, b_real, a, n] at hd_nonpos hre ⊢
      rw [hre, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hB_pos), abs_of_nonneg (neg_nonneg.mpr hd_nonpos)]
      ring
    rw [hcong, hcov, intervalIntegral.integral_symm b₁ b₂]
    ring
  have hcov_neg : ∫ u in u₁..u₂, max 0 (-(spinPtilde c Φ (u : ℂ)).re) =
      (spinCalNorm c Φ)⁻¹ * ∫ b in b₁..b₂, max (-Q b) 0 := by
    have hcov : ∫ u in u₁..u₂, max (-Q (b_real u)) 0 * deriv b_real u =
        ∫ b in b_real u₁..b_real u₂, max (-Q b) 0 :=
      intervalIntegral.integral_comp_mul_deriv' hb_hasDeriv hb_deriv_cont
        (hQ_cont.neg.sup continuous_const).continuousOn
    have hcong : ∫ u in u₁..u₂, max 0 (-(spinPtilde c Φ (u : ℂ)).re) =
        -(spinCalNorm c Φ)⁻¹ * ∫ u in u₁..u₂, max (-Q (b_real u)) 0 * deriv b_real u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le h12] at hu
      obtain ⟨hd_nonpos, hre⟩ := spinPtilde_re_eq_and_deriv_nonpos hc hΦ (hsub_ac u hu)
      dsimp only [Q, b_real, a, n] at hd_nonpos hre ⊢
      have hfac : -(spinPtilde c Φ (u : ℂ)).re =
          ((spinCalNorm c Φ)⁻¹ * (-deriv b_real u)) * (-Q (b_real u)) := by
        rw [hre]; ring
      have hfac_nn : 0 ≤ (spinCalNorm c Φ)⁻¹ * (-deriv b_real u) :=
        mul_nonneg (inv_nonneg.mpr hB_pos.le) (neg_nonneg.mpr hd_nonpos)
      have hmx : max 0 (-(spinPtilde c Φ (u : ℂ)).re) =
          ((spinCalNorm c Φ)⁻¹ * (-deriv b_real u)) * max (-Q (b_real u)) 0 := by
        rw [hfac]
        by_cases hq : 0 ≤ -Q (b_real u)
        · rw [max_eq_left hq, max_eq_right (mul_nonneg hfac_nn hq)]
        · have hq' : -Q (b_real u) ≤ 0 := le_of_not_ge hq
          rw [max_eq_right hq', max_eq_left (mul_nonpos_of_nonneg_of_nonpos hfac_nn hq'), mul_zero]
      rw [hmx]; ring
    rw [hcong, hcov, intervalIntegral.integral_symm b₁ b₂]
    ring
  have hhalf_le : ∫ u in u₁..u₂, |(spinPtilde c Φ (u : ℂ)).re| ≤ 1 / 2 := by
    rw [hcov_abs]
    have hQ_int : Integrable Q volume := integrable_spinCalInt_integrand hc hΦ
    have hL_neg : ∀ b : ℝ, spinL (-b) = spinL b := fun b => by unfold spinL; rw [abs_neg]
    have hG_even : ∀ b : ℝ, (spinGcal a Φ ((-b : ℝ) : ℂ)).re = (spinGcal a Φ (b : ℂ)).re := fun b => by
      rw [spinGcal_re_ofReal ha_pos.le hΦ (-b), spinGcal_re_ofReal ha_pos.le hΦ b]
      congr 1
      have hsum : ∀ d : ℝ, spinHbCalReal (-b) (-d) * spinG a Φ (-b + -d) (-b - -d) =
          spinHbCalReal b d * spinG a Φ (b + d) (b - d) := fun d => by
        rw [spinHbCalReal_neg, show -b + -d = -(b + d) by ring, show -b - -d = -(b - d) by ring,
          spinG_d4_neg_left hΦ, spinG_d4_neg_right hΦ]
      rw [← integral_neg_eq_self (fun d => spinHbCalReal (-b) d * spinG a Φ (-b + d) (-b - d))]
      exact integral_congr_ae (Eventually.of_forall hsum)
    have hQ_even : ∀ b : ℝ, Q (-b) = Q b := fun b => by
      dsimp [Q]; rw [hL_neg, hG_even b]
    have hhalf_norm : 2 * ∫ b in Ioi (0 : ℝ), |Q b| = spinCalNorm c Φ := by
      have hneg_eq : ∫ b in Iio (0 : ℝ), |Q b| = ∫ b in Ioi (0 : ℝ), |Q b| := by
        rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
          ← integral_neg_eq_self (fun b => (Ioi (0 : ℝ)).indicator (fun y => |Q y|) b)]
        refine integral_congr_ae (Eventually.of_forall fun b => ?_)
        by_cases hb : b < 0
        · have hnb : -b ∈ Ioi (0 : ℝ) := by simpa using hb
          have hbm : b ∈ Iio (0 : ℝ) := hb
          simp [Set.indicator_of_mem hbm, Set.indicator_of_mem hnb, hQ_even b]
        · have hnot1 : b ∉ Iio (0 : ℝ) := hb
          have hnot2 : -b ∉ Ioi (0 : ℝ) := fun h => hb (by simpa using h)
          simp [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
      have hunion : (∫ b in Iic (0 : ℝ), |Q b|) + ∫ b in Ioi (0 : ℝ), |Q b| = ∫ b : ℝ, |Q b| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          hQ_int.abs.integrableOn hQ_int.abs.integrableOn, Iic_union_Ioi, setIntegral_univ]
      rw [MeasureTheory.integral_Iic_eq_integral_Iio, hneg_eq] at hunion
      have hnorm_eq : ∫ b : ℝ, |Q b| = spinCalNorm c Φ := by
        unfold spinCalNorm; dsimp only [Q, a, n]
        refine integral_congr_ae (Eventually.of_forall fun b => ?_)
        dsimp only
        rw [abs_mul, abs_mul, abs_of_pos ha_pos, abs_of_pos (Real.exp_pos _)]
      linarith only [hunion, hnorm_eq]
    have hsub_le : ∫ b in b₁..b₂, |Q b| ≤ ∫ b in Ioi (0 : ℝ), |Q b| := by
      rw [intervalIntegral.integral_of_le hb₁₂]
      exact setIntegral_mono_set hQ_int.abs.integrableOn
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hb₁_pos.le)))
    have h1 : (spinCalNorm c Φ)⁻¹ * ∫ b in b₁..b₂, |Q b| ≤ (spinCalNorm c Φ)⁻¹ * (spinCalNorm c Φ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hhalf_norm, hsub_le]) (inv_nonneg.mpr hB_pos.le)
    have h2 : (spinCalNorm c Φ)⁻¹ * (spinCalNorm c Φ / 2) = 1 / 2 := by
      field_simp [hB_pos.ne']
    exact h1.trans_eq h2
  exact ⟨hb₁₂, hb₁_pos, hcov_id, hcov_abs, hcov_neg, hhalf_le⟩

lemma spinPtilde_tail_le_of_env {c C_κ C₂ r_d cA A B : ℝ}
    (hc : 40 ≤ c) (hCκ : 0 < C_κ) (_hr_d : 0 < r_d) (_hcA : 0 < cA)
    (hA1 : 1 ≤ A) (hAB : A ≤ B)
    (hB_an : B < r_d * (c - 1) ^ (2 / 3 : ℝ))
    (hB_cA : B ≤ (cA * (c - 1) ^ (1 / 3 : ℝ)) ^ 2)
    (hς : C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) ≤ 1 / 2)
    {Φ : ℝ × ℝ → ℝ}
    (hAn : AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) (r_d * (c - 1) ^ (2 / 3 : ℝ))))
    (hEnv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ (cA * (c - 1) ^ (1 / 3 : ℝ)) ^ 2 →
      0 < (u ^ (1 / 2 : ℂ)).re →
      ‖spinPtilde c Φ u‖ ≤ C_κ * spinAiryEnv u *
        Real.exp (C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * (u ^ (1 / 2 : ℂ)).re) /
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)) :
    ∫ x in A..B, ‖spinPtilde c Φ (x : ℂ)‖ ≤
      (6 / 5 : ℝ) * C_κ * Real.exp (-(5 / 6 : ℝ) * A) := by
  set n := c - 1
  have hn_ge39 : 39 ≤ n := by dsimp [n]; linarith
  have hΨ_cont : ContinuousOn (fun x : ℝ => spinPtilde c Φ (x : ℂ)) (Icc A B) := by
    refine hAn.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.1])]
    exact hx.2.trans_lt hB_an
  have hi_l : IntervalIntegrable (fun x : ℝ => ‖spinPtilde c Φ (x : ℂ)‖) volume A B :=
    (continuous_norm.comp_continuousOn hΨ_cont).intervalIntegrable_of_Icc hAB
  have hi_r : IntervalIntegrable (fun x : ℝ => C_κ * Real.exp (-(5 / 6 : ℝ) * x)) volume A B :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable A B
  have hpt : ∀ x ∈ Icc A B, ‖spinPtilde c Φ (x : ℂ)‖ ≤ C_κ * Real.exp (-(5 / 6 : ℝ) * x) := by
    intro x hx
    have hx1 : 1 ≤ x := hA1.trans hx.1
    have hx_pos : 0 < x := by linarith
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    have hx_norm : ‖(x : ℂ)‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]; exact hx.2.trans hB_cA
    have h_re_sqrt : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re, Real.sqrt_eq_rpow]
    have hre_pos : 0 < ((x : ℂ) ^ (1 / 2 : ℂ)).re := by rw [h_re_sqrt]; exact Real.sqrt_pos.mpr hx_pos
    have hbd := hEnv (x : ℂ) hx_ne hx_norm hre_pos
    have h_env_val : spinAiryEnv (x : ℂ) = Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) := by
      unfold spinAiryEnv
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re]
    have h_denom : Real.sqrt ‖(x : ℂ)‖ * ((x : ℂ) ^ (1 / 2 : ℂ)).re = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos, h_re_sqrt, Real.mul_self_sqrt hx_pos.le]
    have hx32 : x ≤ x ^ (3 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hsqrt_le : √x ≤ x := by
      rw [Real.sqrt_eq_rpow]
      conv_rhs => rw [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h_exp : -(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) +
        C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * √x ≤ -(5 / 6 : ℝ) * x := by
      have h1 : C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * √x ≤ (1 / 2 : ℝ) * x :=
        (mul_le_mul_of_nonneg_right hς (Real.sqrt_nonneg _)).trans (by linarith)
      linarith
    have hle_exp : Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
        Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * √x) ≤ Real.exp (-(5 / 6 : ℝ) * x) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr h_exp
    have h_denom' : Real.sqrt ‖(x : ℂ)‖ * √x = x := by rw [← h_re_sqrt]; exact h_denom
    calc ‖spinPtilde c Φ (x : ℂ)‖
        ≤ C_κ * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * √x) / x := by
          rw [h_env_val, h_re_sqrt, h_denom'] at hbd; exact hbd
      _ ≤ C_κ * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * √x) :=
          div_le_self (by positivity) hx1
      _ = C_κ * (Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * √x)) := by ring
      _ ≤ C_κ * Real.exp (-(5 / 6 : ℝ) * x) := mul_le_mul_of_nonneg_left hle_exp hCκ.le
  have hint_mono := intervalIntegral.integral_mono_on hAB hi_l hi_r hpt
  have hint_exp : ∫ x in A..B, C_κ * Real.exp (-(5 / 6 : ℝ) * x) =
      (6 / 5 : ℝ) * C_κ * (Real.exp (-(5 / 6 : ℝ) * A) - Real.exp (-(5 / 6 : ℝ) * B)) := by
    rw [intervalIntegral.integral_const_mul]
    have hderiv : ∀ x ∈ Set.uIcc A B,
        HasDerivAt (fun y : ℝ => -(6 / 5 : ℝ) * Real.exp (-(5 / 6 : ℝ) * y))
          (Real.exp (-(5 / 6 : ℝ) * x)) x := fun x _ => by
      have h1 := ((hasDerivAt_id x).const_mul (-(5 / 6 : ℝ))).exp.const_mul (-(6 / 5 : ℝ))
      exact h1.congr_deriv (by simp only [id_eq]; ring)
    have hint_c : Continuous (fun x : ℝ => Real.exp (-(5 / 6 : ℝ) * x)) := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint_c.intervalIntegrable A B)]
    ring
  have hpos_B : 0 ≤ (6 / 5 : ℝ) * C_κ * Real.exp (-(5 / 6 : ℝ) * B) := by positivity
  linarith only [hint_mono, hint_exp, hpos_B]

private lemma disc_r0_exists :
    ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ < xiStar / 2 ∧
      virasoroDeltaChart 1 (virasoroBV ^ 2) < (xiStar - r₁) ^ 2 / 3 ∧
      (xiStar + r₁) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroBV ^ 2)) := by
  have hbv_pos : 0 < virasoroBV ^ 2 := sq_pos_of_pos virasoroBV_pos
  have hac_eq : virasoroAC 1 ^ 2 = 2 * virasoroBV ^ 2 := by
    rw [virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]
  have hbv_le_ac : virasoroBV ^ 2 ≤ virasoroAC 1 ^ 2 := by linarith only [hbv_pos, hac_eq]
  have hanti := virasoroDeltaChart_strictAnti one_pos
  have h0 : xiBar = virasoroDeltaChart 1 0 := by rw [virasoroDeltaChart_zero, mul_one]
  have hlt1 : virasoroDeltaChart 1 (virasoroBV ^ 2) < xiBar := by
    rw [h0]; exact hanti ⟨by linarith only [hbv_pos, hbv_le_ac], by linarith only [hbv_pos, hbv_le_ac]⟩
      ⟨by linarith only [hbv_pos, hbv_le_ac], hbv_le_ac⟩ hbv_pos
  have hlt2 : xiBar < virasoroDeltaChart 1 (-(virasoroBV ^ 2)) := by
    rw [h0]; exact hanti ⟨by linarith only [hbv_pos, hbv_le_ac], by linarith only [hbv_pos, hbv_le_ac]⟩
      ⟨by linarith only [hbv_pos, hbv_le_ac], by linarith only [hbv_pos, hbv_le_ac]⟩ (by linarith only [hbv_pos])
  let δ := min (xiBar - virasoroDeltaChart 1 (virasoroBV ^ 2))
    (virasoroDeltaChart 1 (-(virasoroBV ^ 2)) - xiBar)
  have hδ : 0 < δ := lt_min (by linarith only [hlt1]) (by linarith only [hlt2])
  let r₁ := min (xiStar / 4) (δ / (2 * xiStar))
  have hr₁_pos : 0 < r₁ := lt_min (by positivity [xiStar_pos]) (by positivity [xiStar_pos, hδ])
  have hr₁_half : r₁ < xiStar / 2 := (min_le_left _ _).trans_lt (by linarith only [xiStar_pos])
  have hr₁_xi : r₁ * xiStar ≤ δ / 2 := by
    calc r₁ * xiStar ≤ (δ / (2 * xiStar)) * xiStar := mul_le_mul_of_nonneg_right (min_le_right _ _) xiStar_pos.le
      _ = δ / 2 := by field_simp [xiStar_pos.ne']
  have hsq_lo : xiBar - (xiStar - r₁) ^ 2 / 3 < δ := by
    have hEq : xiBar - (xiStar - r₁) ^ 2 / 3 = (2 * xiStar * r₁ - r₁ ^ 2) / 3 := by unfold xiBar; ring
    rw [hEq]; nlinarith only [sq_nonneg r₁, hr₁_xi, hδ]
  have hsq_hi : (xiStar + r₁) ^ 2 / 3 - xiBar < δ := by
    have hEq : (xiStar + r₁) ^ 2 / 3 - xiBar = (2 * xiStar * r₁ + r₁ ^ 2) / 3 := by unfold xiBar; ring
    rw [hEq]; nlinarith only [hr₁_pos, hr₁_half, hr₁_xi, hδ]
  refine ⟨r₁, hr₁_pos, hr₁_half, ?_, ?_⟩
  · have hml := min_le_left (xiBar - virasoroDeltaChart 1 (virasoroBV ^ 2))
      (virasoroDeltaChart 1 (-(virasoroBV ^ 2)) - xiBar)
    linarith only [hsq_lo, hml]
  · have hmr := min_le_right (xiBar - virasoroDeltaChart 1 (virasoroBV ^ 2))
      (virasoroDeltaChart 1 (-(virasoroBV ^ 2)) - xiBar)
    linarith only [hsq_hi, hmr]

lemma spin_rhoMinus_Icc_le_of_slack {C₀ r₁ C₂₄ C_p c x₁ : ℝ}
    (hc : 40 ≤ c) (_hr₁_pos : 0 < r₁) (_hr₁_lt : r₁ < xiStar)
    (_hx₁ : x₁ ≤ xiStar + C₀ * (c - 1) ^ (-(2 / 3 : ℝ)))
    {Φ : ℝ × ℝ → ℝ} (hS : SpinSlackHyp c x₁ Φ)
    (h24_bd : (spinRhoProjMeasure c (fun q => max (-spinG ((c - 1) / 12) Φ q.1 q.2) 0)
      (Icc 0 (xiStar - r₁))).toReal ≤ C₂₄ * ((c - 1) ^ (-(2 / 3 : ℝ)) * Real.log (c - 1)) + C_p * (c - 1) ^ (-3 : ℝ)) :
    let n := c - 1
    let a := n / 12
    let Q : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
    ∫ b in Ioc (0 : ℝ) (xiStar - r₁), max (-Q b) 0 ≤
      C₂₄ * (n ^ (-(2 / 3 : ℝ)) * Real.log n) + C_p * n ^ (-3 : ℝ) := by
  intro n a Q
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  let Gplus : ℝ × ℝ → ℝ := fun q => max (spinG a Φ q.1 q.2) 0
  let Gminus : ℝ × ℝ → ℝ := fun q => max (-spinG a Φ q.1 q.2) 0
  have hQ_int : Integrable Q volume := integrable_spinCalInt_integrand hc hS.2.1
  have hQmax_int : Integrable (fun b : ℝ => max (-Q b) 0) volume := by
    refine hQ_int.norm.mono' (hQ_int.aestronglyMeasurable.neg.sup aestronglyMeasurable_const)
      (Eventually.of_forall fun b => ?_)
    rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  let f_m : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * spinCalProjFn Gminus b
  have hG_meas : Measurable (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
    unfold spinG
    exact (hS.2.1.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).measurable
  have hGp_meas : Measurable Gplus := hG_meas.max measurable_const
  have hGm_meas : Measurable Gminus := hG_meas.neg.max measurable_const
  have hGp_bd : ∀ p : ℝ × ℝ, |Gplus p| ≤ |spinG a Φ p.1 p.2| := fun p => by
    dsimp [Gplus]; rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hGm_bd : ∀ p : ℝ × ℝ, |Gminus p| ≤ |spinG a Φ p.1 p.2| := fun p => by
    dsimp [Gminus]; rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hGp_sym : (∀ x y : ℝ, Gplus (-x, y) = Gplus (x, y)) ∧
      (∀ x y : ℝ, Gplus (x, -y) = Gplus (x, y)) :=
    ⟨fun x y => by dsimp [Gplus]; rw [spinG_d4_neg_left hS.2.1],
     fun x y => by dsimp [Gplus]; rw [spinG_d4_neg_right hS.2.1]⟩
  have hGm_sym : (∀ x y : ℝ, Gminus (-x, y) = Gminus (x, y)) ∧
      (∀ x y : ℝ, Gminus (x, -y) = Gminus (x, y)) :=
    ⟨fun x y => by dsimp [Gminus]; rw [spinG_d4_neg_left hS.2.1],
     fun x y => by dsimp [Gminus]; rw [spinG_d4_neg_right hS.2.1]⟩
  let φ : ℝ → ℝ := (Icc 0 (xiStar - r₁)).indicator fun _ => 1
  have hφ_meas : Measurable φ := measurable_const.indicator measurableSet_Icc
  have hφ_bd : ∀ x : ℝ, |φ x| ≤ 1 := fun x => by
    dsimp [φ]; by_cases h : x ∈ Icc 0 (xiStar - r₁) <;> simp [h]
  have hadj_p := spinCal_adjoint_identity hc hS.2.1 hGp_meas hGp_bd hGp_sym.1 hGp_sym.2
    (φ := fun _ : ℝ => (1 : ℝ)) measurable_const zero_le_one (fun _ => by norm_num)
  have hadj_m1 := spinCal_adjoint_identity hc hS.2.1 hGm_meas hGm_bd hGm_sym.1 hGm_sym.2
    (φ := fun _ : ℝ => (1 : ℝ)) measurable_const zero_le_one (fun _ => by norm_num)
  have hadj := spinCal_adjoint_identity hc hS.2.1 hGm_meas hGm_bd hGm_sym.1 hGm_sym.2
    hφ_meas zero_le_one hφ_bd
  have hfm_nn : ∀ b : ℝ, 0 ≤ f_m b := fun b => by
    refine mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) ?_
    unfold spinCalProjFn
    refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
    rw [spinHbCal_ofReal, Complex.ofReal_re]
    exact mul_nonneg (spinHbCalReal_nonneg b d) (le_max_right _ _)
  have hfm_int : Integrable (fun b : ℝ => (Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b) volume := by
    have hprod : Integrable (fun p : ℝ × ℝ =>
        a * Real.exp (n * spinL p.1) * (Icc 0 (xiStar - r₁)).indicator 1 |p.1| *
          (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * Gminus (p.1 + p.2, p.1 - p.2)))
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hadj.1
    have hleft := hprod.integral_prod_left
    have hfun : (fun b : ℝ => ∫ d : ℝ, a * Real.exp (n * spinL b) *
        (Icc 0 (xiStar - r₁)).indicator 1 |b| *
          (4 * spinCalF xiStar ^ 2 * spinHbCalReal b d * Gminus (b + d, b - d))) =
        fun b : ℝ => (Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b := by
      ext b
      have heq_in : (∫ d : ℝ, a * Real.exp (n * spinL b) *
          (Icc 0 (xiStar - r₁)).indicator 1 |b| *
            (4 * spinCalF xiStar ^ 2 * spinHbCalReal b d * Gminus (b + d, b - d))) =
          a * Real.exp (n * spinL b) * (Icc 0 (xiStar - r₁)).indicator 1 |b| *
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
  have hrho_eq : (spinRhoProjMeasure c Gminus (Icc 0 (xiStar - r₁))).toReal =
      ∫ b : ℝ, (Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b := by
    have hmabs : MeasurableSet (abs ⁻¹' Icc 0 (xiStar - r₁)) := continuous_abs.measurable measurableSet_Icc
    have hmax : (fun b : ℝ => ENNReal.ofReal (a * Real.exp (n * spinL b) * max (spinCalProjFn Gminus b) 0)) =
        fun b : ℝ => ENNReal.ofReal (f_m b) := by
      ext b
      have hcp : 0 ≤ spinCalProjFn Gminus b := by
        unfold spinCalProjFn
        refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
        rw [spinHbCal_ofReal, Complex.ofReal_re]
        exact mul_nonneg (spinHbCalReal_nonneg b d) (le_max_right _ _)
      dsimp [f_m]; rw [max_eq_left hcp]
    have hmeq : spinRhoProjMeasure c Gminus (Icc 0 (xiStar - r₁)) =
        ∫⁻ b : ℝ, ENNReal.ofReal ((Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b) := by
      unfold spinRhoProjMeasure
      rw [Measure.map_apply continuous_abs.measurable measurableSet_Icc,
        withDensity_apply _ hmabs, hmax, ← lintegral_indicator hmabs]
      refine lintegral_congr fun b => ?_
      by_cases hb : |b| ∈ Icc 0 (xiStar - r₁) <;> simp [hb]
    rw [hmeq, ← ofReal_integral_eq_lintegral_ofReal hfm_int
      (Eventually.of_forall fun b => by by_cases hb : |b| ∈ Icc 0 (xiStar - r₁) <;> simp [hb, hfm_nn b]),
      ENNReal.toReal_ofReal (integral_nonneg fun b => by
        by_cases hb : |b| ∈ Icc 0 (xiStar - r₁) <;> simp [hb, hfm_nn b])]
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
    unfold spinCalProjFn
    have heq_p : (∫ d : ℝ, (spinHbCal (b : ℂ) d).re * Gplus (b + d, b - d)) =
        ∫ d : ℝ, spinHbCalReal b d * Gplus (b + d, b - d) :=
      integral_congr_ae (Eventually.of_forall fun d => by dsimp only; rw [spinHbCal_ofReal, Complex.ofReal_re])
    have heq_m : (∫ d : ℝ, (spinHbCal (b : ℂ) d).re * Gminus (b + d, b - d)) =
        ∫ d : ℝ, spinHbCalReal b d * Gminus (b + d, b - d) :=
      integral_congr_ae (Eventually.of_forall fun d => by dsimp only; rw [spinHbCal_ofReal, Complex.ofReal_re])
    rw [heq_p, heq_m, ← mul_sub, ← integral_sub hbp' hbm']
    congr 1; refine integral_congr_ae (Eventually.of_forall fun d => ?_)
    have hG_split : spinG a Φ (b + d) (b - d) = Gplus (b + d, b - d) - Gminus (b + d, b - d) := by
      dsimp [Gplus, Gminus]; rcases le_total 0 (spinG a Φ (b + d) (b - d)) with h | h <;> simp [h]
    dsimp only; rw [hG_split]; ring
  have hQmax_le : ∀ᵐ b : ℝ ∂volume, b ∈ Ioc 0 (xiStar - r₁) →
      max (-Q b) 0 ≤ (Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b := by
    filter_upwards [hae_split] with b hgb hb_ioc
    have hb_icc : |b| ∈ Icc 0 (xiStar - r₁) := by
      rw [abs_of_pos hb_ioc.1]; exact ⟨hb_ioc.1.le, hb_ioc.2⟩
    have hcp_nn : 0 ≤ spinCalProjFn Gplus b := by
      unfold spinCalProjFn
      refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
      rw [spinHbCal_ofReal, Complex.ofReal_re]
      exact mul_nonneg (spinHbCalReal_nonneg b d) (le_max_right _ _)
    have hcm_nn : 0 ≤ spinCalProjFn Gminus b := by
      unfold spinCalProjFn
      refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
      rw [spinHbCal_ofReal, Complex.ofReal_re]
      exact mul_nonneg (spinHbCalReal_nonneg b d) (le_max_right _ _)
    have hQ_lb : -Q b ≤ f_m b := by
      dsimp [Q, f_m]; rw [hgb]; nlinarith [mul_nonneg ha_pos.le (Real.exp_pos (n * spinL b)).le]
    have hle_fm : max (-Q b) 0 ≤ f_m b := max_le hQ_lb (hfm_nn b)
    simpa [hb_icc] using hle_fm
  have hmono_int : ∫ b in Ioc (0 : ℝ) (xiStar - r₁), max (-Q b) 0 ≤
      ∫ b in Ioc (0 : ℝ) (xiStar - r₁), (Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b := by
    refine setIntegral_mono_ae_restrict hQmax_int.integrableOn hfm_int.integrableOn ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr hQmax_le
  have hsub_tot : ∫ b in Ioc (0 : ℝ) (xiStar - r₁), (Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b ≤
      ∫ b : ℝ, (Icc 0 (xiStar - r₁)).indicator 1 |b| * f_m b :=
    setIntegral_le_integral hfm_int (Eventually.of_forall fun b => by
      by_cases hb : |b| ∈ Icc 0 (xiStar - r₁) <;> simp [hb, hfm_nn b])
  linarith [hmono_int, hsub_tot, hrho_eq, h24_bd]

private lemma rpow_neg_third_log_le_half {C₂ n : ℝ} (hC₂ : 0 ≤ C₂)
    (hn1 : 1 ≤ n) (hn_bd : (12 * C₂) ^ 6 ≤ n) :
    C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n ≤ 1 / 2 := by
  have hn_pos : 0 < n := by linarith
  have hn16_pos : 0 < n ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hlog : Real.log n ≤ 6 * n ^ (1 / 6 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos hn16_pos
    rw [Real.log_rpow hn_pos] at h1
    linarith
  have h16_ge : 12 * C₂ ≤ n ^ (1 / 6 : ℝ) := by
    have h1 := Real.rpow_le_rpow (by positivity) hn_bd (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul (by positivity)] at h1
    norm_num at h1; exact h1
  have hcomb : n ^ (-(1 / 3 : ℝ)) * n ^ (1 / 6 : ℝ) = (n ^ (1 / 6 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hn_pos, ← Real.rpow_neg hn_pos.le]; congr 1; norm_num
  have h_le : C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n ≤ (6 * C₂) / n ^ (1 / 6 : ℝ) := by
    calc C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n
        ≤ C₂ * n ^ (-(1 / 3 : ℝ)) * (6 * n ^ (1 / 6 : ℝ)) := by gcongr
      _ = 6 * C₂ * (n ^ (-(1 / 3 : ℝ)) * n ^ (1 / 6 : ℝ)) := by ring
      _ = (6 * C₂) / n ^ (1 / 6 : ℝ) := by rw [hcomb, ← div_eq_mul_inv]
  have h_div : (6 * C₂) / n ^ (1 / 6 : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hn16_pos]; linarith
  exact h_le.trans h_div

private lemma exp_neg_sixth_le_rpow {n : ℝ} (hn1 : 1 ≤ n) :
    Real.exp (-(5 / 6 : ℝ) * n ^ (1 / 6 : ℝ)) ≤ 720 / (5 / 6 : ℝ) ^ 6 * n⁻¹ := by
  have hn_pos : 0 < n := by linarith
  set t : ℝ := (5 / 6 : ℝ) * n ^ (1 / 6 : ℝ)
  have ht_nn : 0 ≤ t := by positivity
  have hpow6 : t ^ 6 / 720 ≤ Real.exp t := by
    have h1 := (Finset.single_le_sum (fun i _ => by positivity)
      (Finset.mem_range.mpr (by norm_num : 6 < 7))).trans (Real.sum_le_exp_of_nonneg ht_nn 7)
    have hfac : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
    rwa [hfac] at h1
  have ht6_eq : t ^ 6 = (5 / 6 : ℝ) ^ 6 * n := by
    dsimp [t]; rw [mul_pow, ← Real.rpow_natCast (n ^ (1 / 6 : ℝ)) 6, ← Real.rpow_mul hn_pos.le]
    norm_num
  rw [ht6_eq] at hpow6
  have hinv := inv_anti₀ (by positivity) hpow6
  have heq : -(5 / 6 : ℝ) * n ^ (1 / 6 : ℝ) = -t := by dsimp [t]; ring
  rw [heq, Real.exp_neg]
  refine hinv.trans_eq ?_
  rw [inv_div]; field_simp

private lemma inv_le_deltaN {n : ℝ} (hn : 39 ≤ n) :
    n⁻¹ ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n := by
  have hn_pos : 0 < n := by linarith
  have h1log : 1 ≤ Real.log n := by
    have he : Real.exp 1 ≤ n := (Real.exp_one_lt_d9.le).trans (by linarith)
    exact (Real.log_exp 1 ▸ Real.log_le_log (Real.exp_pos 1) he)
  have h_inv_eq : n⁻¹ = n ^ (-(2 / 3 : ℝ)) * n ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_add hn_pos, show -(2 / 3 : ℝ) + -(1 / 3 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h13_le1 : n ^ (-(1 / 3 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hn_pos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
  calc n⁻¹ = n ^ (-(2 / 3 : ℝ)) * n ^ (-(1 / 3 : ℝ)) := h_inv_eq
    _ ≤ n ^ (-(2 / 3 : ℝ)) * 1 := mul_le_mul_of_nonneg_left h13_le1 (Real.rpow_nonneg hn_pos.le _)
    _ ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n := mul_le_mul_of_nonneg_left h1log (Real.rpow_nonneg hn_pos.le _)

private lemma rpow_neg3_le_deltaN {n : ℝ} (hn : 39 ≤ n) :
    n ^ (-3 : ℝ) ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n := by
  have hn_pos : 0 < n := by linarith
  have h_le : n ^ (-3 : ℝ) ≤ n ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_neg_one] at h_le
  exact h_le.trans (inv_le_deltaN hn)

private lemma spinPtilde_analytic_on_ball' {c : ℝ} (hc40 : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) (2 * virasoroBV ^ 2 * (c - 1) ^ (2 / 3 : ℝ))) := by
  set n : ℝ := c - 1
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hac_eq : 2 * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) = virasoroAC n ^ 2 := by
    rw [virasoroAC_sq n hn_pos.le]
  have hdom : ball (0 : ℂ) (2 * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ)) ⊆
      ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
    rw [hac_eq]; exact ball_subset_ball (virasoroAC_sq_lt_domain hn_pos).le
  have hb_an : AnalyticOnNhd ℂ (virasoroBChart n) (ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ))) :=
    virasoroBChart_analyticOnNhd hn_pos
  have hg_an : AnalyticOnNhd ℂ (spinGcal (n / 12) Φ) {w : ℂ | |w.im| < 1 / 2} :=
    (spinGcal_differentiableOn_strip hc40 hΦ).analyticOnNhd
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  intro u hu
  have hu_ac : u ∈ closedBall (0 : ℂ) (virasoroAC n ^ 2) := by
    rw [mem_closedBall_zero_iff]; exact (hac_eq ▸ mem_ball_zero_iff.mp hu).le
  have hu_dom : u ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := hdom hu
  have hb_im : |(virasoroBChart n u).im| < 1 / 2 := by
    have hmin := virasoro_deltaChart_b_min hn_pos hu_ac
    have him : |(virasoroBChart n u).im| ≤ ‖virasoroBChart n u - (xiStar : ℂ)‖ := by
      have heq : (virasoroBChart n u).im = (virasoroBChart n u - (xiStar : ℂ)).im := by simp
      rw [heq]; exact Complex.abs_im_le_norm _
    have h05 : ‖virasoroBChart n u - (xiStar : ℂ)‖ ≤ 0.05 :=
      hmin.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have h1 : AnalyticAt ℂ (fun z => ((n / 12 : ℝ) : ℂ) *
      Complex.exp (((n * (2 * π / 3) : ℝ) : ℂ) * virasoroBChart n z)) u :=
    analyticAt_const.mul ((analyticAt_const.mul (hb_an u hu_dom)).cexp)
  have h2 : AnalyticAt ℂ (fun z => -deriv (virasoroBChart n) z) u := (hb_an.deriv u hu_dom).neg
  have h3 : AnalyticAt ℂ (fun z => spinGcal (n / 12) Φ (virasoroBChart n z)) u :=
    (hg_an _ hb_im).comp_of_eq (hb_an u hu_dom) rfl
  exact ((h1.mul h2).mul h3).mul analyticAt_const |>.congr (Eventually.of_forall fun z => by
    unfold spinPtilde
    change _ * (spinCalNorm c Φ : ℂ)⁻¹ = _ / (spinCalNorm c Φ : ℂ)
    rw [← div_eq_mul_inv]; congr 1; simp [n])

private lemma spinPtilde_ofReal_im' {c : ℝ} (hc40 : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {u : ℝ} (hu : u ∈ Metric.ball (0 : ℝ) (2 * virasoroBV ^ 2 * (c - 1) ^ (2 / 3 : ℝ))) :
    (spinPtilde c Φ (u : ℂ)).im = 0 := by
  set n : ℝ := c - 1
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hac_eq : 2 * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) = virasoroAC n ^ 2 := by
    rw [virasoroAC_sq n hn_pos.le]
  have hu_abs : |u| ≤ virasoroAC n ^ 2 := by
    rw [← hac_eq]; simpa [Real.norm_eq_abs] using (mem_ball_zero_iff.mp hu).le
  obtain ⟨hb_im, _, _, _⟩ := virasoroBChart_ofReal hn_pos hu_abs
  let b₀ : ℝ := (virasoroBChart n (u : ℂ)).re
  have hb_eq : virasoroBChart n (u : ℂ) = (b₀ : ℂ) := Complex.ext rfl hb_im
  have hg_im : (spinGcal (n / 12) Φ (virasoroBChart n (u : ℂ))).im = 0 := by
    rw [hb_eq]; exact spinGcal_im_ofReal (by dsimp [n]; linarith) hΦ b₀
  have hdb_im : (deriv (virasoroBChart n) (u : ℂ)).im = 0 := by
    have hu_dom : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact hu_abs.trans_lt (virasoroAC_sq_lt_domain hn_pos)
    have hd_C : HasDerivAt (fun t : ℝ => virasoroBChart n (t : ℂ))
        (deriv (virasoroBChart n) (u : ℂ)) u :=
      ((virasoroBChart_analyticOnNhd hn_pos (u : ℂ) hu_dom).differentiableAt.hasDerivAt).comp_ofReal
    have hd_im := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    have hev : (fun t : ℝ => (virasoroBChart n (t : ℂ)).im) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hu] with t ht
      have ht_abs : |t| ≤ virasoroAC n ^ 2 := by
        rw [← hac_eq]; simpa [Real.norm_eq_abs] using (mem_ball_zero_iff.mp ht).le
      exact (virasoroBChart_ofReal hn_pos ht_abs).1
    exact hd_im.unique ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev)
  have hexp_im : (Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ))).im = 0 := by
    rw [hb_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_im]
  have hneg_im : (-deriv (virasoroBChart n) (u : ℂ)).im = 0 := by simp [hdb_im]
  have hnum_im : (((n / 12 : ℝ) : ℂ) *
      Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ)) *
      (-deriv (virasoroBChart n) (u : ℂ)) * spinGcal (n / 12) Φ (virasoroBChart n (u : ℂ))).im = 0 := by
    simp only [Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero, hexp_im, mul_zero,
      hneg_im, hg_im]
  unfold spinPtilde; dsimp only
  change ((((n / 12 : ℝ) : ℂ) *
      Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ)) *
      (-deriv (virasoroBChart n) (u : ℂ)) * spinGcal (n / 12) Φ (virasoroBChart n (u : ℂ))) /
      (spinCalNorm c Φ : ℂ)).im = 0
  rw [Complex.div_ofReal_im, hnum_im, zero_div]

private lemma spinPtilde_quantC1B2_apply
    {c n R_dom_n u_T u_hi C_κ51 C₂ cA δ_lobe_n : ℝ}
    {Φ : ℝ × ℝ → ℝ}
    (hteb_n : ∀ Ψ : ℂ → ℂ, ∀ u₀ : ℝ,
      AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) (n ^ (1 / 6 : ℝ))) →
      (∀ x ∈ Icc (-(n ^ (1 / 6 : ℝ))) (n ^ (1 / 6 : ℝ)), (Ψ (x : ℂ)).im = 0) →
      (∀ u ∈ closedBall (0 : ℂ) (n ^ (1 / 6 : ℝ)), ¬ (u.im = 0 ∧ u.re ≤ 0) →
        ‖Ψ u‖ ≤ (2 * C_κ51) * airyEnv u *
          Real.exp ((C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n) * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) →
      airyZero 1 < u₀ → u₀ ≤ n ^ (1 / 6 : ℝ) →
      (∀ x ∈ Icc (-(n ^ (1 / 6 : ℝ))) u₀, 0 ≤ (Ψ (x : ℂ)).re) →
      ∫ x in (-(n ^ (1 / 6 : ℝ)))..(n ^ (1 / 6 : ℝ)), ‖Ψ (x : ℂ)‖ ≤ 1 →
      (1 / 2 : ℝ) - δ_lobe_n ≤ ∫ x in u₀..(n ^ (1 / 6 : ℝ)), max 0 (-(Ψ (x : ℂ)).re) →
      (∀ R' ∈ Icc (0 : ℝ) (n ^ (1 / 6 : ℝ)), -R' ≤ u₀ →
        ∫ x in (-R')..(n ^ (1 / 6 : ℝ)), (Ψ (x : ℂ)).re ≤ δ_lobe_n) →
      QuantC1B2Holds Ψ u₀)
    (hR_eq : n ^ (1 / 6 : ℝ) = R_dom_n)
    (han_dom : AnalyticOnNhd ℂ (spinPtilde c Φ) (closedBall (0 : ℂ) R_dom_n))
    (him_dom : ∀ x ∈ Icc (-R_dom_n) R_dom_n, (spinPtilde c Φ (x : ℂ)).im = 0)
    (hR_lt_uhi : R_dom_n < u_hi) (hu_hi_cA : u_hi ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2)
    (henv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 → 0 < (u ^ (1 / 2 : ℂ)).re →
      ‖spinPtilde c Φ u‖ ≤ C_κ51 * spinAiryEnv u *
        Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re))
    (huT_gt : airyZero 1 < u_T) (huT_le_dom : u_T ≤ R_dom_n)
    (hpos_band : ∀ x ∈ Icc (-R_dom_n) u_T, 0 ≤ (spinPtilde c Φ (x : ℂ)).re)
    (hL1_le : ∫ x in (-R_dom_n)..R_dom_n, ‖((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)‖ ≤ 1)
    (hlobe_lb : (1 / 2 : ℝ) - δ_lobe_n ≤
      ∫ x in u_T..R_dom_n, max 0 (-(((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re))
    (hwin_ub : ∀ R' ∈ Icc (0 : ℝ) R_dom_n, -R' ≤ u_T →
      ∫ x in (-R')..R_dom_n, (((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re ≤ δ_lobe_n) :
    QuantC1B2Holds (fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u) u_T := by
  subst hR_eq
  refine hteb_n (fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u) u_T
    (analyticOnNhd_const.mul han_dom) ?_ ?_ huT_gt huT_le_dom ?_ hL1_le hlobe_lb hwin_ub
  · intro x hx
    have him := him_dom x hx
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro u hu hcut
    have hnorm_u : ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 :=
      (mem_closedBall_zero_iff.mp hu).trans (hR_lt_uhi.le.trans hu_hi_cA)
    have hu_ne : u ≠ 0 := fun h0 => hcut ⟨by simp [h0], by simp [h0]⟩
    have hu_slit : u ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; by_contra hns; push Not at hns; exact hcut ⟨hns.2, hns.1⟩
    have hre_pos : 0 < (u ^ (1 / 2 : ℂ)).re := re_cpow_half_pos_of_slit hu_slit
    have hbd := henv u hu_ne hnorm_u hre_pos
    have h_inv : (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ =
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
      rw [Real.sqrt_eq_rpow, mul_inv, Real.rpow_neg (norm_nonneg _)]
    have h_env_eq : spinAiryEnv u = airyEnv u := rfl
    have hbd' : ‖spinPtilde c Φ u‖ ≤ C_κ51 * airyEnv u *
        Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) *
        (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
      rw [← h_env_eq, ← h_inv, ← div_eq_mul_inv]
      exact hbd
    have h2_norm : ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ = 2 * ‖spinPtilde c Φ u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg two_pos.le]
    have hmul2 := mul_le_mul_of_nonneg_left hbd' two_pos.le
    rw [h2_norm]
    exact hmul2.trans_eq (by ring)
  · intro x hx
    have hre := hpos_band x hx
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith only [hre]

theorem spinPtilde_quant_c1 {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ (r₁ c₀ C_κ51 C₂ r_d cA C_dl κ_obs : ℝ),
      0 < r₁ ∧ r₁ < xiStar / 2 ∧
      virasoroDeltaChart 1 (virasoroBV ^ 2) < (xiStar - r₁) ^ 2 / 3 ∧
      (xiStar + r₁) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroBV ^ 2)) ∧
      40 ≤ c₀ ∧ 0 < C_κ51 ∧ 0 < C₂ ∧ 0 < r_d ∧ 0 < cA ∧ 0 < C_dl ∧ 0 < κ_obs ∧
      r_d = 2 * virasoroBV ^ 2 ∧ cA = virasoroBV ∧
      ∀ {c x₁ u_T : ℝ}, c₀ ≤ c →
        let n := c - 1
        let R_dom := n ^ (1 / 6 : ℝ)
        |x₁ - xiStar| ≤ C₀ * n ^ (-(2 / 3 : ℝ)) →
        airyZero 1 < u_T → u_T ≤ |airyZero 1| + 1 →
        (virasoroBChart n (u_T : ℂ)).re = x₁ →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinSlackHyp c x₁ Φ →
          κ_obs ≤ spinCalNorm c Φ ∧
          AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) (r_d * n ^ (2 / 3 : ℝ))) ∧
          (∀ u : ℝ, u ∈ ball (0 : ℝ) (r_d * n ^ (2 / 3 : ℝ)) → (spinPtilde c Φ (u : ℂ)).im = 0) ∧
          (∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 → 0 < (u ^ (1 / 2 : ℂ)).re →
            ‖spinPtilde c Φ u‖ ≤ C_κ51 * spinAiryEnv u *
              Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
                (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)) ∧
          (∀ x ∈ Icc (-R_dom) R_dom, (spinPtilde c Φ (x : ℂ)).im = 0) ∧
          (∀ x ∈ Icc (-R_dom) u_T, 0 ≤ (spinPtilde c Φ (x : ℂ)).re) ∧
          (∫ x in (-R_dom)..R_dom, ‖((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)‖ ≤ 1) ∧
          QuantC1B2Holds (fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u) u_T := by
  obtain ⟨r₁, hr₁_pos, hr₁_half, hlo, hhi⟩ := disc_r0_exists
  have hr₁_lt : r₁ < xiStar := hr₁_half.trans (half_lt_self xiStar_pos)
  obtain ⟨_κJ, κ_obs, c₀_43, _hκJ_pos, hκ_pos, hc0_43, h43⟩ :=
    spinS4_4_3 (aJ := C₀ + 1) (bJ := C₀ + 2) hC₀ (by linarith) (by linarith)
  obtain ⟨C_strip, hCstrip, hStrip_bd⟩ := spinGcalCl_closed_strip_bound
  obtain ⟨C_slit, hCslit, hSlit_bd⟩ := spinGcal_slit_L1_bound
  let C_κ51 : ℝ := spinPtildeCκ C_strip C_slit κ_obs
  have hCκ51_pos : 0 < C_κ51 := spinPtildeCκ_pos hκ_pos
  let C₂ : ℝ := spinPtildeC2
  have hC2_pos : 0 < C₂ := spinPtildeC2_pos
  let r_d : ℝ := 2 * virasoroBV ^ 2
  let cA : ℝ := virasoroBV
  have hrd_pos : 0 < r_d := by have := virasoroBV_pos; positivity
  have hcA_pos : 0 < cA := virasoroBV_pos
  obtain ⟨_cσ, C₂₃, c₀_23, _, hC23_pos, hc0_23, h23⟩ := spinS4_2_3 (C_x := C₀)
  obtain ⟨C₂₄, C_p, c₀_24, hC24_pos, hCp_pos, hc0_24, h24⟩ :=
    spinS4_2_4 (C_x := C₀) (p := 3) (r₀ := r₁) (by norm_num) hr₁_pos hr₁_lt
  let C_tail : ℝ := (6 / 5 : ℝ) * C_κ51 * (720 / (5 / 6 : ℝ) ^ 6)
  have hCtail_pos : 0 < C_tail := by dsimp [C_tail]; positivity
  let C_dl : ℝ := ((C₂₃ + 1) + 2 * C₂₄ + 2 * C_p) / κ_obs + 2 * C_tail
  have hCdl_pos : 0 < C_dl := by positivity
  let R_dom : ℝ → ℝ := fun n => n ^ (1 / 6 : ℝ)
  let ς : ℝ → ℝ := fun n => C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n
  let δ_lobe : ℝ → ℝ := fun n => C_dl * n ^ (-(2 / 3 : ℝ)) * Real.log n
  have hR_lim : Tendsto R_dom atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hς_nn : ∀ᶠ n in atTop, 0 ≤ ς n := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
    dsimp [ς]; have := Real.log_nonneg hn; positivity
  have hς_lim : Tendsto ς atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul (6 * C₂) |>.trans_eq
        (by rw [mul_zero])) hς_nn ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
    have hn_pos : 0 < n := by linarith
    have hlog : Real.log n ≤ 6 * n ^ (1 / 6 : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos (1 / 6 : ℝ))
      rw [Real.log_rpow hn_pos] at h1; linarith
    have hcomb : n ^ (-(1 / 3 : ℝ)) * n ^ (1 / 6 : ℝ) = n ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    dsimp [ς]
    calc C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n
        ≤ C₂ * n ^ (-(1 / 3 : ℝ)) * (6 * n ^ (1 / 6 : ℝ)) := by gcongr
      _ = 6 * C₂ * (n ^ (-(1 / 3 : ℝ)) * n ^ (1 / 6 : ℝ)) := by ring
      _ = 6 * C₂ * n ^ (-(1 / 6 : ℝ)) := by rw [hcomb]
  have hδ_nn : ∀ᶠ n in atTop, 0 ≤ δ_lobe n := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
    dsimp [δ_lobe]; have := Real.log_nonneg hn; positivity
  have hδ_lim : Tendsto δ_lobe atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (3 * C_dl) |>.trans_eq
        (by rw [mul_zero])) hδ_nn ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
    have hn_pos : 0 < n := by linarith
    have hlog : Real.log n ≤ 3 * n ^ (1 / 3 : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos (1 / 3 : ℝ))
      rw [Real.log_rpow hn_pos] at h1; linarith
    have hcomb : n ^ (-(2 / 3 : ℝ)) * n ^ (1 / 3 : ℝ) = n ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    dsimp [δ_lobe]
    calc C_dl * n ^ (-(2 / 3 : ℝ)) * Real.log n
        ≤ C_dl * n ^ (-(2 / 3 : ℝ)) * (3 * n ^ (1 / 3 : ℝ)) := by gcongr
      _ = 3 * C_dl * (n ^ (-(2 / 3 : ℝ)) * n ^ (1 / 3 : ℝ)) := by ring
      _ = 3 * C_dl * n ^ (-(1 / 3 : ℝ)) := by rw [hcomb]
  obtain ⟨c₁_teb, hc1_2, hteb⟩ :=
    teb_quant_c1_typeII (mul_pos two_pos hCκ51_pos) R_dom ς δ_lobe hR_lim hς_nn hς_lim hδ_nn hδ_lim
  have hbv_pos : 0 < virasoroBV ^ 2 := sq_pos_of_pos virasoroBV_pos
  have hac_eq : virasoroAC 1 ^ 2 = 2 * virasoroBV ^ 2 := by
    rw [virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]
  have hbv_lt_ac1 : virasoroBV ^ 2 < virasoroAC 1 ^ 2 := by linarith only [hbv_pos, hac_eq]
  have hlo_ac1 : virasoroDeltaChart 1 (virasoroAC 1 ^ 2) < (xiStar - r₁) ^ 2 / 3 := by
    have hlt := virasoroDeltaChart_strictAnti one_pos
      ⟨by linarith only [hbv_pos, hac_eq], hbv_lt_ac1.le⟩
      ⟨by linarith only [hbv_pos, hac_eq], le_rfl⟩ hbv_lt_ac1
    linarith only [hlt, hlo]
  have hhi_ac1 : (xiStar + r₁) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) := by
    have hlt := virasoroDeltaChart_strictAnti one_pos
      ⟨le_rfl, by linarith only [sq_nonneg (virasoroAC 1)]⟩
      ⟨neg_le_neg hbv_lt_ac1.le, (neg_nonpos.mpr hbv_pos.le).trans (sq_nonneg _)⟩
      (neg_lt_neg hbv_lt_ac1)
    linarith only [hlt, hhi]
  have hmem_div_lo := virasoroDeltaChart_div_mem one_pos (abs_of_nonneg (sq_nonneg _) |>.le)
  have hmem_div_hi := virasoroDeltaChart_div_mem one_pos (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])
  have hlo_ac1' : virasoroDeltaChart 1 (virasoroAC 1 ^ 2) / 1 < (xiStar - r₁) ^ 2 / 3 := by
    simpa only [div_one] using hlo_ac1
  have hhi_ac1' : (xiStar + r₁) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) / 1 := by
    simpa only [div_one] using hhi_ac1
  have hlt_sq : (xiStar - r₁) ^ 2 / 3 < (xiStar + r₁) ^ 2 / 3 := by
    have hxm : 0 < xiStar - r₁ := by linarith only [xiStar_pos, hr₁_half]
    nlinarith only [hr₁_pos, hxm]
  have hξ_m_mem : (xiStar - r₁) ^ 2 / 3 ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨hmem_div_lo.1.trans hlo_ac1'.le, (hlt_sq.le.trans hhi_ac1'.le).trans hmem_div_hi.2⟩
  have hξ_p_mem : (xiStar + r₁) ^ 2 / 3 ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨hmem_div_lo.1.trans (hlo_ac1'.le.trans hlt_sq.le), hhi_ac1'.le.trans hmem_div_hi.2⟩
  let u_hi1 : ℝ := virasoroUChart 1 ((xiStar - r₁) ^ 2 / 3)
  let u_lo1 : ℝ := virasoroUChart 1 ((xiStar + r₁) ^ 2 / 3)
  have h_xiBar_mem : xiBar ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨by linarith only [virasoroChartR0_pos], by linarith only [virasoroChartR0_pos]⟩
  have h0_xiBar : (0 : ℝ) = virasoroUChart 1 xiBar := virasoroUChart_xiBar.symm
  have hu_hi1_pos : 0 < u_hi1 := by
    have h1 : (xiStar - r₁) ^ 2 / 3 < xiBar := by
      unfold xiBar
      have hxm : 0 < xiStar - r₁ := by linarith only [xiStar_pos, hr₁_half]
      nlinarith only [hr₁_pos, hxm]
    rw [h0_xiBar]
    exact virasoroUChart_strictAnti one_pos hξ_m_mem h_xiBar_mem h1
  have hu_lo1_neg : u_lo1 < 0 := by
    have h1 : xiBar < (xiStar + r₁) ^ 2 / 3 := by
      unfold xiBar; nlinarith only [xiStar_pos, hr₁_pos]
    rw [h0_xiBar]
    exact virasoroUChart_strictAnti one_pos h_xiBar_mem hξ_p_mem h1
  let c_R : ℝ := max (4096) (max (1 / u_hi1 ^ 2 + 1) (1 / u_lo1 ^ 2 + 1))
  let c₀ : ℝ := max (max 49 (max c₀_43 (max c₀_23 c₀_24)))
    (max (c₁_teb + 1) (max (c_R + 1) (max ((12 * C₂) ^ 6 + 1) (max (1 + (C₀ / r₁) ^ (3 / 2 : ℝ)) 50))))
  have hc0_40 : 40 ≤ c₀ := (by norm_num : (40 : ℝ) ≤ 49).trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨r₁, c₀, C_κ51, C₂, r_d, cA, C_dl, κ_obs,
    hr₁_pos, hr₁_half, hlo, hhi, hc0_40, hCκ51_pos, hC2_pos, hrd_pos, hcA_pos, hCdl_pos, hκ_pos, rfl, rfl, ?_⟩
  intro c x₁ u_T hc n R_dom_n hx₁ huT_gt huT_le hx1_eq Φ hS
  have hc49 : 49 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc40 : 40 ≤ c := by linarith
  have hc43 : c₀_43 ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hc23 : c₀_23 ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))).trans hc
  have hc24 : c₀_24 ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))).trans hc
  have hc_teb : c₁_teb ≤ n := by
    have h1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
    dsimp [n]; linarith
  have hn_4096 : 4096 ≤ n := by
    have h1 : c_R ≤ n := by
      have := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
      dsimp [n]; linarith
    exact (le_max_left _ _).trans h1
  have hn_cR : c_R ≤ n := by
    have := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
    dsimp [n]; linarith
  have hn_12C2 : (12 * C₂) ^ 6 ≤ n := by
    have := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
    dsimp [n]; linarith
  have hc_eps : 1 + (C₀ / r₁) ^ (3 / 2 : ℝ) ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hc
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hn_ge1 : 1 ≤ n := by linarith
  have hn_ge48 : 48 ≤ n := by linarith
  have ha_pos : 0 < n / 12 := by linarith
  have hB_lo : κ_obs ≤ spinCalNorm c Φ := by
    have h4 := (h43 hc43 hx₁ hS).2
    rwa [hS.2.2.1, mul_one] at h4
  have hB_pos : 0 < spinCalNorm c Φ := lt_of_lt_of_le hκ_pos hB_lo
  have han : AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) (r_d * n ^ (2 / 3 : ℝ))) :=
    spinPtilde_analytic_on_ball' hc40 hS.2.1
  have him_ball : ∀ u : ℝ, u ∈ ball (0 : ℝ) (r_d * n ^ (2 / 3 : ℝ)) →
      (spinPtilde c Φ (u : ℂ)).im = 0 := fun u hu =>
    spinPtilde_ofReal_im' hc40 hS.2.1 hu
  have henv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 → 0 < (u ^ (1 / 2 : ℂ)).re →
      ‖spinPtilde c Φ u‖ ≤ C_κ51 * spinAiryEnv u *
        Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re) := by
    intro u hu_ne hu_le hu_re
    have hac_le : (cA * n ^ (1 / 3 : ℝ)) ^ 2 ≤ virasoroAC n ^ 2 := by
      have h_eq : (cA * n ^ (1 / 3 : ℝ)) ^ 2 = virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by
        dsimp [cA]; rw [mul_pow, ← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 2,
          ← Real.rpow_mul hn_pos.le]; norm_num
      rw [h_eq, virasoroAC_sq n hn_pos.le]
      have hnn : 0 ≤ virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by positivity
      linarith only [hnn]
    have hu_ac : u ∈ closedBall (0 : ℂ) (virasoroAC n ^ 2) :=
      mem_closedBall_zero_iff.mpr (hu_le.trans hac_le)
    have hcut : ¬ (u.im = 0 ∧ u.re ≤ 0) := fun ⟨him0, hre0⟩ => by
      have hre : (u ^ (1 / 2 : ℂ)).re = 0 := by
        rw [Complex.cpow_def_of_ne_zero hu_ne]
        have harg : u.arg = π := Complex.arg_eq_pi_iff.mpr ⟨lt_of_le_of_ne hre0 (fun h0 =>
          hu_ne (Complex.ext h0 him0)), him0⟩
        rw [Complex.exp_re]
        have him' : (Complex.log u * (1 / 2 : ℂ)).im = π / 2 := by
          simp [Complex.log_im, harg]; ring
        rw [him', Real.cos_pi_div_two, mul_zero]
      linarith
    have hB_lo' : κ_obs * spinM2 (n / 12) Φ ≤ spinCalNorm c Φ := by rwa [hS.2.2.1, mul_one]
    exact spinPtilde_pj_bound hCstrip hStrip_bd hCslit hSlit_bd hκ_pos hc49 hS.2.1 hB_lo' hu_ac hu_ne hcut
  have hR_dom_ge4 : 4 ≤ R_dom_n := by
    dsimp [R_dom_n]
    have h1 := Real.rpow_le_rpow (by norm_num) hn_4096 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have h46 : ((4096 : ℝ) ^ (1 / 6 : ℝ)) = 4 := by
      rw [show (4096 : ℝ) = (4 : ℝ) ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast (4 : ℝ) 6,
        ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hR_dom_eq : R_dom_n = R_dom n := rfl
  let u_hi := virasoroUChart n ((xiStar - r₁) ^ 2 / 3)
  let u_lo := virasoroUChart n ((xiStar + r₁) ^ 2 / 3)
  have hu_hi_eq : u_hi = u_hi1 * n ^ (2 / 3 : ℝ) := by
    dsimp [u_hi, u_hi1]; rw [virasoroUChart_scale_eq' hn_pos]; ring
  have hu_lo_eq : u_lo = u_lo1 * n ^ (2 / 3 : ℝ) := by
    dsimp [u_lo, u_lo1]; rw [virasoroUChart_scale_eq' hn_pos]; ring
  have hR_lt_uhi : R_dom_n < u_hi := by
    have hinv : 1 / u_hi1 ^ 2 < n := lt_of_lt_of_le (by linarith only [])
      ((le_max_left _ _).trans ((le_max_right _ _).trans hn_cR))
    have hsqrt' : 1 < u_hi1 * n ^ (1 / 2 : ℝ) := by
      have h_sq : 1 ^ 2 < (u_hi1 * n ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast (n ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hn_pos.le]
        norm_num
        calc (1 : ℝ) = u_hi1 ^ 2 * (1 / u_hi1 ^ 2) := by field_simp [hu_hi1_pos.ne']
          _ < u_hi1 ^ 2 * n := mul_lt_mul_of_pos_left hinv (sq_pos_of_pos hu_hi1_pos)
      have hprod_pos : 0 < u_hi1 * n ^ (1 / 2 : ℝ) :=
        mul_pos hu_hi1_pos (Real.rpow_pos_of_pos hn_pos (1 / 2 : ℝ))
      nlinarith only [h_sq, hprod_pos]
    have hn_split : n ^ (2 / 3 : ℝ) = n ^ (1 / 2 : ℝ) * n ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    rw [hu_hi_eq, hn_split, ← mul_assoc]
    calc R_dom_n = 1 * n ^ (1 / 6 : ℝ) := by dsimp [R_dom_n]; ring
      _ < (u_hi1 * n ^ (1 / 2 : ℝ)) * n ^ (1 / 6 : ℝ) :=
        mul_lt_mul_of_pos_right hsqrt' (Real.rpow_pos_of_pos hn_pos _)
  have hulo_lt_negR : u_lo < -R_dom_n := by
    have hinv : 1 / u_lo1 ^ 2 < n := lt_of_lt_of_le (by linarith only [])
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn_cR))
    have hneg_lo : 0 < -u_lo1 := neg_pos.mpr hu_lo1_neg
    have hsqrt' : 1 < (-u_lo1) * n ^ (1 / 2 : ℝ) := by
      have h_sq : 1 ^ 2 < ((-u_lo1) * n ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [mul_pow, neg_sq, ← Real.rpow_natCast (n ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hn_pos.le]
        norm_num
        calc (1 : ℝ) = u_lo1 ^ 2 * (1 / u_lo1 ^ 2) := by field_simp [hu_lo1_neg.ne]
          _ < u_lo1 ^ 2 * n := mul_lt_mul_of_pos_left hinv (sq_pos_of_ne_zero hu_lo1_neg.ne)
      have hprod_pos : 0 < (-u_lo1) * n ^ (1 / 2 : ℝ) :=
        mul_pos hneg_lo (Real.rpow_pos_of_pos hn_pos (1 / 2 : ℝ))
      nlinarith only [h_sq, hprod_pos]
    have hn_split : n ^ (2 / 3 : ℝ) = n ^ (1 / 2 : ℝ) * n ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    have h1 : R_dom_n < (-u_lo1) * n ^ (1 / 2 : ℝ) * n ^ (1 / 6 : ℝ) := by
      calc R_dom_n = 1 * n ^ (1 / 6 : ℝ) := by dsimp [R_dom_n]; ring
        _ < ((-u_lo1) * n ^ (1 / 2 : ℝ)) * n ^ (1 / 6 : ℝ) :=
          mul_lt_mul_of_pos_right hsqrt' (Real.rpow_pos_of_pos hn_pos _)
    rw [hu_lo_eq, hn_split]; linarith only [h1]
  have hξ_scale_lo : virasoroDeltaChart n (virasoroAC n ^ 2) / n =
      virasoroDeltaChart 1 (virasoroAC 1 ^ 2) := by
    rw [virasoroAC_sq n hn_pos.le, virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]
    exact virasoroDeltaChart_div_scale_eq' hn_pos _
  have hξ_scale_hi : virasoroDeltaChart n (-(virasoroAC n ^ 2)) / n =
      virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) := by
    have hac : -(virasoroAC n ^ 2) = (-(virasoroAC 1 ^ 2)) * n ^ (2 / 3 : ℝ) := by
      rw [virasoroAC_sq n hn_pos.le, virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]; ring
    rw [hac]; exact virasoroDeltaChart_div_scale_eq' hn_pos _
  have hmem_div_lo := virasoroDeltaChart_div_mem hn_pos (abs_of_nonneg (sq_nonneg _) |>.le)
  have hmem_div_hi := virasoroDeltaChart_div_mem hn_pos (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])
  have hulo_gt_ac : -(virasoroAC n ^ 2) < u_lo := by
    have h1 := virasoroUChart_strictAnti hn_pos hξ_p_mem hmem_div_hi (hξ_scale_hi ▸ hhi_ac1)
    rwa [virasoroUChart_deltaChart hn_pos (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])] at h1
  have huhi_lt_ac : u_hi < virasoroAC n ^ 2 := by
    have h1 := virasoroUChart_strictAnti hn_pos hmem_div_lo hξ_m_mem (hξ_scale_lo ▸ hlo_ac1)
    rwa [virasoroUChart_deltaChart hn_pos (abs_of_nonneg (sq_nonneg _)).le] at h1
  have h_ac_sq : virasoroAC n ^ 2 = r_d * n ^ (2 / 3 : ℝ) := by
    rw [virasoroAC_sq n hn_pos.le]
  have hu_hi_cA : u_hi ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 := by
    have hbv_abs1 : |virasoroBV ^ 2| ≤ virasoroAC 1 ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact hbv_lt_ac1.le
    have hbv_mem := virasoroDeltaChart_div_mem one_pos hbv_abs1
    have h1_lt : u_hi1 < virasoroBV ^ 2 := by
      have h1 := virasoroUChart_strictAnti one_pos hbv_mem hξ_m_mem (by simpa only [div_one] using hlo)
      rwa [virasoroUChart_deltaChart one_pos hbv_abs1] at h1
    have hcA_eq : (cA * n ^ (1 / 3 : ℝ)) ^ 2 = virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by
      dsimp [cA]; rw [mul_pow, ← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 2,
        ← Real.rpow_mul hn_pos.le]; norm_num
    rw [hu_hi_eq, hcA_eq]
    exact mul_le_mul_of_nonneg_right h1_lt.le (Real.rpow_nonneg hn_pos.le _)
  have huT_lt_uhi : u_T < u_hi := by
    have h1 : u_T ≤ |airyZero 1| + 1 := huT_le
    have h2 : |airyZero 1| + 1 < 4 := by
      obtain ⟨ha1, _⟩ := airyZero_one
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hulo_lt_uT : u_lo < u_T := by
    have h1 : -4 < airyZero 1 := by obtain ⟨ha1, _⟩ := airyZero_one; linarith
    linarith
  have hAThr_lt : |airyZero 1| + 1 < 4 := by
    obtain ⟨ha1, _⟩ := airyZero_one; rw [abs_of_neg (by linarith)]; linarith
  have hR_dom_lt_ac : R_dom_n < virasoroAC n ^ 2 := hR_lt_uhi.trans huhi_lt_ac
  have hnegR_dom_gt_ac : -(virasoroAC n ^ 2) < -R_dom_n := by
    linarith [hulo_gt_ac, hulo_lt_negR]
  have him_dom : ∀ x ∈ Icc (-R_dom_n) R_dom_n, (spinPtilde c Φ (x : ℂ)).im = 0 := fun x hx =>
    him_ball x (by
    rw [mem_ball_zero_iff, Real.norm_eq_abs, ← h_ac_sq]
    exact abs_lt.mpr ⟨by linarith only [hx.1, hnegR_dom_gt_ac], by linarith only [hx.2, hR_dom_lt_ac]⟩)
  have huT_abs : |u_T| ≤ virasoroAC n ^ 2 :=
    abs_le.mpr ⟨(hulo_gt_ac.trans hulo_lt_uT).le, (huT_lt_uhi.trans huhi_lt_ac).le⟩
  have hpos_band : ∀ x ∈ Icc (-R_dom_n) u_T, 0 ≤ (spinPtilde c Φ (x : ℂ)).re := fun x hx =>
    spinPtilde_re_nonneg_of_le hc40 hS.1 hS.2.1 hS.2.2.2.2 hB_pos.le huT_abs hx1_eq
      (abs_lt.mpr ⟨hnegR_dom_gt_ac.trans_le hx.1, (hx.2.trans_lt huT_lt_uhi).trans huhi_lt_ac⟩)
      hx.2
  have hjac_dom := spinPtilde_jacobian_on hc40 hnegR_dom_gt_ac (by linarith [hR_dom_ge4])
    hR_dom_lt_ac hS.2.1 hB_pos
  have hL1_le : ∫ x in (-R_dom_n)..R_dom_n, ‖((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)‖ ≤ 1 := by
    have hnorm_eq : ∫ x in (-R_dom_n)..R_dom_n, ‖((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)‖ =
        2 * ∫ x in (-R_dom_n)..R_dom_n, |(spinPtilde c Φ (x : ℂ)).re| := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by linarith [hR_dom_ge4])] at hx
      have him := him_dom x hx
      have hp_eq : spinPtilde c Φ (x : ℂ) = ((spinPtilde c Φ (x : ℂ)).re : ℂ) :=
        Complex.ext rfl him
      conv_lhs => arg 1; arg 2; rw [hp_eq]
      rw [show ((2 : ℝ) : ℂ) * ((spinPtilde c Φ (x : ℂ)).re : ℂ) =
          ((2 * (spinPtilde c Φ (x : ℂ)).re : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos two_pos]
    rw [hnorm_eq]; linarith only [hjac_dom.2.2.2.2.2]
  -- Tail bound on `[R_dom_n, u_hi]`
  have hς_half : C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n ≤ 1 / 2 :=
    rpow_neg_third_log_le_half hC2_pos.le hn_ge1 hn_12C2
  have hn_ge39 : 39 ≤ n := by linarith
  have htail_le : ∫ x in R_dom_n..u_hi, ‖spinPtilde c Φ (x : ℂ)‖ ≤
      C_tail * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
    have h1 := spinPtilde_tail_le_of_env hc40 hCκ51_pos hrd_pos hcA_pos
      (by linarith : 1 ≤ R_dom_n) hR_lt_uhi.le (h_ac_sq ▸ huhi_lt_ac) hu_hi_cA hς_half han henv
    have h2 := (exp_neg_sixth_le_rpow hn_ge1).trans
      (mul_le_mul_of_nonneg_left (inv_le_deltaN hn_ge39) (by positivity))
    calc ∫ x in R_dom_n..u_hi, ‖spinPtilde c Φ (x : ℂ)‖
        ≤ (6 / 5 : ℝ) * C_κ51 * Real.exp (-(5 / 6 : ℝ) * R_dom_n) := h1
      _ ≤ (6 / 5 : ℝ) * C_κ51 * (720 / (5 / 6 : ℝ) ^ 6 * (n ^ (-(2 / 3 : ℝ)) * Real.log n)) := by
          dsimp [R_dom_n]; gcongr
      _ = C_tail * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by dsimp [C_tail]; ring
  -- Calibrated `Q`-decomposition on `Ioi 0`
  let a := n / 12
  let Q : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
  have hQ_int : Integrable Q volume := integrable_spinCalInt_integrand hc40 hS.2.1
  have hQmax_int : Integrable (fun b : ℝ => max (-Q b) 0) volume := by
    refine hQ_int.norm.mono' (hQ_int.aestronglyMeasurable.neg.sup aestronglyMeasurable_const)
      (Eventually.of_forall fun b => ?_)
    rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hL_neg : ∀ b : ℝ, spinL (-b) = spinL b := fun b => by unfold spinL; rw [abs_neg]
  have hG_even : ∀ b : ℝ, (spinGcal a Φ ((-b : ℝ) : ℂ)).re = (spinGcal a Φ (b : ℂ)).re := fun b => by
    rw [spinGcal_re_ofReal ha_pos.le hS.2.1 (-b), spinGcal_re_ofReal ha_pos.le hS.2.1 b]
    congr 1
    have hsum : ∀ d : ℝ, spinHbCalReal (-b) (-d) * spinG a Φ (-b + -d) (-b - -d) =
        spinHbCalReal b d * spinG a Φ (b + d) (b - d) := fun d => by
      rw [spinHbCalReal_neg, show -b + -d = -(b + d) by ring, show -b - -d = -(b - d) by ring,
        spinG_d4_neg_left hS.2.1, spinG_d4_neg_right hS.2.1]
    rw [← integral_neg_eq_self (fun d => spinHbCalReal (-b) d * spinG a Φ (-b + d) (-b - d))]
    exact integral_congr_ae (Eventually.of_forall hsum)
  have hQ_even : ∀ b : ℝ, Q (-b) = Q b := fun b => by
    dsimp [Q]; rw [hL_neg, hG_even b]
  have hhalf_int : 2 * ∫ b in Ioi (0 : ℝ), Q b = spinCalInt c Φ := by
    have hneg_eq : ∫ b in Iio (0 : ℝ), Q b = ∫ b in Ioi (0 : ℝ), Q b := by
      rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
        ← integral_neg_eq_self (fun b => (Ioi (0 : ℝ)).indicator Q b)]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      by_cases hb : b < 0
      · have hnb : -b ∈ Ioi (0 : ℝ) := by simpa using hb
        have hbm : b ∈ Iio (0 : ℝ) := hb
        simp [Set.indicator_of_mem hbm, Set.indicator_of_mem hnb, hQ_even b]
      · have hnot1 : b ∉ Iio (0 : ℝ) := hb
        have hnot2 : -b ∉ Ioi (0 : ℝ) := fun h => hb (by simpa using h)
        simp [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
    have hunion : (∫ b in Iic (0 : ℝ), Q b) + ∫ b in Ioi (0 : ℝ), Q b = ∫ b : ℝ, Q b := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hQ_int.integrableOn hQ_int.integrableOn, Iic_union_Ioi, setIntegral_univ]
    rw [MeasureTheory.integral_Iic_eq_integral_Iio, hneg_eq] at hunion
    have hcal_eq : spinCalInt c Φ = ∫ b : ℝ, Q b := rfl
    linarith only [hunion, hcal_eq]
  have hhalf_abs : 2 * ∫ b in Ioi (0 : ℝ), |Q b| = spinCalNorm c Φ := by
    have hneg_eq : ∫ b in Iio (0 : ℝ), |Q b| = ∫ b in Ioi (0 : ℝ), |Q b| := by
      rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
        ← integral_neg_eq_self (fun b => (Ioi (0 : ℝ)).indicator (fun y => |Q y|) b)]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      by_cases hb : b < 0
      · have hnb : -b ∈ Ioi (0 : ℝ) := by simpa using hb
        have hbm : b ∈ Iio (0 : ℝ) := hb
        simp [Set.indicator_of_mem hbm, Set.indicator_of_mem hnb, hQ_even b]
      · have hnot1 : b ∉ Iio (0 : ℝ) := hb
        have hnot2 : -b ∉ Ioi (0 : ℝ) := fun h => hb (by simpa using h)
        simp [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
    have hunion : (∫ b in Iic (0 : ℝ), |Q b|) + ∫ b in Ioi (0 : ℝ), |Q b| = ∫ b : ℝ, |Q b| := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hQ_int.abs.integrableOn hQ_int.abs.integrableOn, Iic_union_Ioi, setIntegral_univ]
    rw [MeasureTheory.integral_Iic_eq_integral_Iio, hneg_eq] at hunion
    have hnorm_eq : ∫ b : ℝ, |Q b| = spinCalNorm c Φ := by
      unfold spinCalNorm; dsimp only [Q, a, n]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      dsimp only
      rw [abs_mul, abs_mul, abs_of_pos ha_pos, abs_of_pos (Real.exp_pos _)]
    linarith only [hunion, hnorm_eq]
  have hx1_ub_hi : x₁ ≤ xiStar + C₀ * n ^ (-(2 / 3 : ℝ)) := by linarith only [(abs_le.mp hx₁).2]
  have hcal_23 : spinCalInt c Φ ≤ (C₂₃ + 1) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) :=
    ((h23 hc23 hS.1 hx1_ub_hi hS.2.1 hS.2.2.1 hS.2.2.2.2).2.2 hS.2.2.2.1)
  have h24_bd := (h24 hc24 hx1_ub_hi hS).2.2.2
  have hIoc_rm : ∫ b in Ioc (0 : ℝ) (xiStar - r₁), max (-Q b) 0 ≤
      C₂₄ * (n ^ (-(2 / 3 : ℝ)) * Real.log n) + C_p * n ^ (-3 : ℝ) :=
    spin_rhoMinus_Icc_le_of_slack hc40 hr₁_pos hr₁_lt hx1_ub_hi hS h24_bd
  have hIoc_rm_δ : ∫ b in Ioc (0 : ℝ) (xiStar - r₁), max (-Q b) 0 ≤
      (C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
    have h1 := mul_le_mul_of_nonneg_left (rpow_neg3_le_deltaN hn_ge39) hCp_pos.le
    linarith only [hIoc_rm, h1]
  have hIoc_Q_ge : -(C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) ≤
      ∫ b in Ioc (0 : ℝ) (xiStar - r₁), Q b := by
    have h1 : ∫ b in Ioc (0 : ℝ) (xiStar - r₁), -Q b ≤
        ∫ b in Ioc (0 : ℝ) (xiStar - r₁), max (-Q b) 0 :=
      setIntegral_mono_on hQ_int.neg.integrableOn hQmax_int.integrableOn measurableSet_Ioc
        fun b _ => le_max_left _ _
    rw [integral_neg] at h1; linarith only [h1, hIoc_rm_δ]
  -- Exact boundary values `b(u_hi) = ξ_* - r₁` and `b(u_lo) = ξ_* + r₁`
  let b_hi := (virasoroBChart n (R_dom_n : ℂ)).re
  have hb_uhi : (virasoroBChart n (u_hi : ℂ)).re = xiStar - r₁ := by
    have hdu := virasoroDeltaChart_uChart hn_pos
      (hξ_scale_lo ▸ hlo_ac1.le)
      (hξ_scale_hi ▸ hlt_sq.le.trans hhi_ac1.le)
    rw [(virasoroBChart_ofReal_eq_sqrt hn_pos
      (abs_lt.mpr ⟨by linarith only [hulo_gt_ac, hulo_lt_uT, huT_lt_uhi], huhi_lt_ac⟩).le).2.1]
    change Real.sqrt (3 * virasoroDeltaChart n (virasoroUChart n ((xiStar - r₁) ^ 2 / 3)) / n) = _
    rw [hdu, show 3 * (n * ((xiStar - r₁) ^ 2 / 3)) / n = (xiStar - r₁) ^ 2 by field_simp [hn_pos.ne'],
      Real.sqrt_sq (by linarith only [xiStar_pos, hr₁_half])]
  have hb_ulo : (virasoroBChart n (u_lo : ℂ)).re = xiStar + r₁ := by
    have hdu := virasoroDeltaChart_uChart hn_pos
      (hξ_scale_lo ▸ hlo_ac1.le.trans hlt_sq.le)
      (hξ_scale_hi ▸ hhi_ac1.le)
    rw [(virasoroBChart_ofReal_eq_sqrt hn_pos
      (abs_lt.mpr ⟨hulo_gt_ac, by linarith only [hulo_lt_uT, huT_lt_uhi, huhi_lt_ac]⟩).le).2.1]
    change Real.sqrt (3 * virasoroDeltaChart n (virasoroUChart n ((xiStar + r₁) ^ 2 / 3)) / n) = _
    rw [hdu, show 3 * (n * ((xiStar + r₁) ^ 2 / 3)) / n = (xiStar + r₁) ^ 2 by field_simp [hn_pos.ne'],
      Real.sqrt_sq (by linarith only [xiStar_pos, hr₁_pos])]
  have hanti_b := bReal_antitoneOn hn_pos
  have hrm_le_bhi : xiStar - r₁ ≤ b_hi := by
    rw [← hb_uhi]
    exact hanti_b ⟨by linarith only [hnegR_dom_gt_ac, hR_dom_ge4], hR_dom_lt_ac.le⟩
      ⟨by linarith only [hulo_gt_ac, hulo_lt_uT, huT_lt_uhi], huhi_lt_ac.le⟩
      hR_lt_uhi.le
  have hbhi_le_x1 : b_hi ≤ x₁ := by
    rw [← hx1_eq]
    exact hanti_b (abs_le.mp huT_abs)
      ⟨by linarith only [hnegR_dom_gt_ac, hR_dom_ge4], hR_dom_lt_ac.le⟩
      (huT_le.trans (by linarith only [hAThr_lt, hR_dom_ge4]))
  have hxs_m_pos : 0 < xiStar - r₁ := by linarith only [xiStar_pos, hr₁_half]
  -- Hypothesis 7 of `teb_quant_c1_typeII`: negative lobe lower bound
  have hlobe_lb : (1 / 2 : ℝ) - δ_lobe n ≤
      ∫ x in u_T..R_dom_n, max 0 (-(((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re) := by
    have hsplit1 : ∫ b in Ioi (0 : ℝ), max (-Q b) 0 =
        (∫ b in Ioc 0 (xiStar - r₁), max (-Q b) 0) + ∫ b in Ioi (xiStar - r₁), max (-Q b) 0 := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        hQmax_int.integrableOn hQmax_int.integrableOn, Ioc_union_Ioi_eq_Ioi hxs_m_pos.le]
    have hsplit2 : ∫ b in Ioi (xiStar - r₁), max (-Q b) 0 =
        (∫ b in Ioc (xiStar - r₁) b_hi, max (-Q b) 0) + ∫ b in Ioi b_hi, max (-Q b) 0 := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        hQmax_int.integrableOn hQmax_int.integrableOn, Ioc_union_Ioi_eq_Ioi hrm_le_bhi]
    have hsplit3 : ∫ b in Ioi b_hi, max (-Q b) 0 =
        (∫ b in Ioc b_hi x₁, max (-Q b) 0) + ∫ b in Ioi x₁, max (-Q b) 0 := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        hQmax_int.integrableOn hQmax_int.integrableOn, Ioc_union_Ioi_eq_Ioi hbhi_le_x1]
    have hext0 : ∫ b in Ioi x₁, max (-Q b) 0 = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun b hb => ?_
      have hgb := spinGcal_re_nonneg_of_ge ha_pos.le hS.2.1 hS.1 hS.2.2.2.2 (mem_Ioi.mp hb).le
      have hQb : 0 ≤ Q b := mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) hgb
      exact max_eq_right (neg_nonpos.mpr hQb)
    have htot_eq : 2 * ∫ b in Ioi (0 : ℝ), max (-Q b) 0 =
        (∫ b in Ioi (0 : ℝ), |Q b|) - ∫ b in Ioi (0 : ℝ), Q b := by
      rw [← integral_const_mul, ← integral_sub hQ_int.abs.integrableOn hQ_int.integrableOn]
      refine setIntegral_congr_fun measurableSet_Ioi fun b _ => ?_
      rcases le_total 0 (Q b) with h | h
      · rw [abs_of_nonneg h, max_eq_right (by linarith only [h])]; ring
      · rw [abs_of_nonpos h, max_eq_left (by linarith only [h])]; ring
    have h_lobe_Q : (1 / 2 : ℝ) - (C₂₃ + 1) / (2 * κ_obs) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) ≤
        2 * (spinCalNorm c Φ)⁻¹ * ∫ b in Ioi (0 : ℝ), max (-Q b) 0 := by
      have h1 : (1 / 2 : ℝ) * spinCalNorm c Φ - (C₂₃ + 1) / 2 * (n ^ (-(2 / 3 : ℝ)) * Real.log n) ≤
          2 * ∫ b in Ioi (0 : ℝ), max (-Q b) 0 := by
        linarith only [htot_eq, hhalf_abs, hhalf_int, hcal_23]
      have hmul := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hB_pos.le)
      have hB_inv_div : (spinCalNorm c Φ)⁻¹ * ((C₂₃ + 1) / 2 * (n ^ (-(2 / 3 : ℝ)) * Real.log n)) ≤
          (C₂₃ + 1) / (2 * κ_obs) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
        have h1' : (spinCalNorm c Φ)⁻¹ ≤ κ_obs⁻¹ := inv_anti₀ hκ_pos hB_lo
        have h2' : 0 ≤ (C₂₃ + 1) / 2 * (n ^ (-(2 / 3 : ℝ)) * Real.log n) :=
          mul_nonneg (div_nonneg (by linarith only [hC23_pos]) zero_le_two)
            (mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.log_nonneg hn_ge1))
        calc (spinCalNorm c Φ)⁻¹ * ((C₂₃ + 1) / 2 * (n ^ (-(2 / 3 : ℝ)) * Real.log n))
            ≤ κ_obs⁻¹ * ((C₂₃ + 1) / 2 * (n ^ (-(2 / 3 : ℝ)) * Real.log n)) :=
              mul_le_mul_of_nonneg_right h1' h2'
          _ = (C₂₃ + 1) / (2 * κ_obs) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by ring
      have hB_half : (spinCalNorm c Φ)⁻¹ * ((1 / 2 : ℝ) * spinCalNorm c Φ) = 1 / 2 := by
        field_simp [hB_pos.ne']
      linarith only [hmul, hB_inv_div, hB_half]
    have hjac_tail := spinPtilde_jacobian_on hc40 (by linarith only [hnegR_dom_gt_ac, hR_dom_ge4])
      hR_lt_uhi.le huhi_lt_ac hS.2.1 hB_pos
    have h_mid_le : (spinCalNorm c Φ)⁻¹ * ∫ b in Ioc (xiStar - r₁) b_hi, max (-Q b) 0 ≤
        C_tail * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      have hmono1 : ∫ b in Ioc (xiStar - r₁) b_hi, max (-Q b) 0 ≤
          ∫ b in (xiStar - r₁)..b_hi, |Q b| := by
        rw [intervalIntegral.integral_of_le hrm_le_bhi]
        exact setIntegral_mono_on hQmax_int.integrableOn hQ_int.abs.integrableOn measurableSet_Ioc
          fun b _ => max_le (neg_le_abs _) (abs_nonneg _)
      have h1_rhs : (spinCalNorm c Φ)⁻¹ * ∫ b in (xiStar - r₁)..b_hi, |Q b| =
          ∫ u in R_dom_n..u_hi, |(spinPtilde c Φ (u : ℂ)).re| := by
        rw [← hb_uhi, ← hjac_tail.2.2.2.1]
      have h1 : (spinCalNorm c Φ)⁻¹ * ∫ b in Ioc (xiStar - r₁) b_hi, max (-Q b) 0 ≤
          ∫ u in R_dom_n..u_hi, |(spinPtilde c Φ (u : ℂ)).re| :=
        (mul_le_mul_of_nonneg_left hmono1 (inv_nonneg.mpr hB_pos.le)).trans_eq h1_rhs
      have hcont_P : ContinuousOn (fun x : ℝ => spinPtilde c Φ (x : ℂ)) (Icc R_dom_n u_hi) :=
        han.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, ← h_ac_sq]
          exact abs_lt.mpr ⟨by linarith only [hx.1, hnegR_dom_gt_ac, hR_dom_ge4], by linarith only [hx.2, huhi_lt_ac]⟩
      have h2 : ∫ x in R_dom_n..u_hi, |(spinPtilde c Φ (x : ℂ)).re| ≤
          ∫ x in R_dom_n..u_hi, ‖spinPtilde c Φ (x : ℂ)‖ := by
        refine intervalIntegral.integral_mono_on hR_lt_uhi.le
          ((Complex.continuous_re.comp_continuousOn hcont_P).abs.intervalIntegrable_of_Icc hR_lt_uhi.le)
          ((continuous_norm.comp_continuousOn hcont_P).intervalIntegrable_of_Icc hR_lt_uhi.le)
          fun x _ => Complex.abs_re_le_norm _
      exact h1.trans (h2.trans htail_le)
    have hjac_lobe := spinPtilde_jacobian_on hc40 (hulo_gt_ac.trans hulo_lt_uT)
      (huT_le.trans (by linarith only [hAThr_lt, hR_dom_ge4])) hR_dom_lt_ac hS.2.1 hB_pos
    have h_lobe_eq : 2 * (spinCalNorm c Φ)⁻¹ * ∫ b in Ioc b_hi x₁, max (-Q b) 0 =
        ∫ x in u_T..R_dom_n, max 0 (-(((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re) := by
      have h_b : ∫ b in Ioc b_hi x₁, max (-Q b) 0 = ∫ b in b_hi..x₁, max (-Q b) 0 :=
        (intervalIntegral.integral_of_le hbhi_le_x1).symm
      rw [h_b, ← hx1_eq]
      have h_u := hjac_lobe.2.2.2.2.1
      dsimp only [b_hi, Q, a, n] at h_u ⊢
      have h_twice : ∫ x in u_T..R_dom_n, max 0 (-(((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re) =
          2 * ∫ x in u_T..R_dom_n, max 0 (-(spinPtilde c Φ (x : ℂ)).re) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun x _ => ?_
        have hre : (-(((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re) = 2 * (-(spinPtilde c Φ (x : ℂ)).re) := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; ring
        rw [hre]
        by_cases hp : 0 ≤ -(spinPtilde c Φ (x : ℂ)).re
        · rw [max_eq_right (mul_nonneg zero_le_two hp), max_eq_right hp]
        · have hp' : -(spinPtilde c Φ (x : ℂ)).re ≤ 0 := le_of_not_ge hp
          rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos zero_le_two hp'), max_eq_left hp', mul_zero]
      rw [h_twice, h_u]; ring
    have hIoc_rm_2 : 2 * (spinCalNorm c Φ)⁻¹ * ∫ b in Ioc (0 : ℝ) (xiStar - r₁), max (-Q b) 0 ≤
        2 * (C₂₄ + C_p) / κ_obs * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      have h1 : 2 * (spinCalNorm c Φ)⁻¹ ≤ 2 / κ_obs := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hκ_pos hB_lo) zero_le_two
      have h2 := mul_le_mul h1 hIoc_rm_δ (setIntegral_nonneg measurableSet_Ioc fun _ _ => le_max_right _ _)
        (div_nonneg zero_le_two hκ_pos.le)
      exact h2.trans_eq (by ring)
    have hsplit_tot : 2 * (spinCalNorm c Φ)⁻¹ * ∫ b in Ioi (0 : ℝ), max (-Q b) 0 =
        2 * (spinCalNorm c Φ)⁻¹ * (∫ b in Ioc 0 (xiStar - r₁), max (-Q b) 0) +
        2 * ((spinCalNorm c Φ)⁻¹ * (∫ b in Ioc (xiStar - r₁) b_hi, max (-Q b) 0)) +
        2 * (spinCalNorm c Φ)⁻¹ * (∫ b in Ioc b_hi x₁, max (-Q b) 0) := by
      have hsum : ∫ b in Ioi (0 : ℝ), max (-Q b) 0 =
          (∫ b in Ioc 0 (xiStar - r₁), max (-Q b) 0) +
          (∫ b in Ioc (xiStar - r₁) b_hi, max (-Q b) 0) +
          (∫ b in Ioc b_hi x₁, max (-Q b) 0) := by
        linarith only [hsplit1, hsplit2, hsplit3, hext0]
      rw [hsum]; ring
    have hδ_lobe_eq : δ_lobe n = C_dl * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by dsimp [δ_lobe]; ring
    have hCdl_split : (C₂₃ + 1) / (2 * κ_obs) + 2 * (C₂₄ + C_p) / κ_obs + 2 * C_tail ≤ C_dl := by
      dsimp [C_dl]
      have hnn : 0 ≤ (C₂₃ + 1) / κ_obs := div_nonneg (by linarith only [hC23_pos]) hκ_pos.le
      have h1 : (C₂₃ + 1) / (2 * κ_obs) ≤ (C₂₃ + 1) / κ_obs := by
        rw [show (C₂₃ + 1) / (2 * κ_obs) = (1 / 2) * ((C₂₃ + 1) / κ_obs) by ring]
        linarith only [hnn]
      linarith only [h1, show 2 * (C₂₄ + C_p) / κ_obs + (C₂₃ + 1) / κ_obs =
        ((C₂₃ + 1) + 2 * C₂₄ + 2 * C_p) / κ_obs by ring]
    have hlog_nn : 0 ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n :=
      mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.log_nonneg hn_ge1)
    have hmul_dl := mul_le_mul_of_nonneg_right hCdl_split hlog_nn
    have h_comb : (C₂₃ + 1) / (2 * κ_obs) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) +
        2 * (C₂₄ + C_p) / κ_obs * (n ^ (-(2 / 3 : ℝ)) * Real.log n) +
        2 * C_tail * (n ^ (-(2 / 3 : ℝ)) * Real.log n) ≤
        C_dl * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      rw [← add_mul, ← add_mul]; exact hmul_dl
    linarith only [h_lobe_Q, hsplit_tot, hIoc_rm_2, h_mid_le, h_lobe_eq, hδ_lobe_eq, h_comb]
  -- Hypothesis 8 of `teb_quant_c1_typeII`: truncated integral upper bound on `[-R', R_dom_n]`
  have hwin_ub : ∀ R' ∈ Icc (0 : ℝ) R_dom_n, -R' ≤ u_T →
      ∫ x in (-R')..R_dom_n, (((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re ≤ δ_lobe n := by
    intro R' hR' hnegR'_le_uT
    have hjac_full := spinPtilde_jacobian_on hc40 hulo_gt_ac
      (by linarith only [hulo_lt_negR, hR_dom_ge4, hR_lt_uhi])
      huhi_lt_ac hS.2.1 hB_pos
    have hC0_r1 : C₀ * n ^ (-(2 / 3 : ℝ)) ≤ r₁ := by
      have hp : C₀ / r₁ ≤ n ^ (2 / 3 : ℝ) := by
        have hc32 : (C₀ / r₁) ^ (3 / 2 : ℝ) ≤ n := by linarith only [hc_eps, show n = c - 1 by rfl]
        have h1 := Real.rpow_le_rpow (by positivity) hc32 (by norm_num : (0 : ℝ) ≤ 2 / 3)
        rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num,
          Real.rpow_one] at h1
        exact h1
      rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hn_pos _)]
      exact (div_le_iff₀ hr₁_pos).mp hp |>.trans_eq (by ring)
    have hx1_hi : x₁ ≤ xiStar + r₁ := by linarith only [hx1_ub_hi, hC0_r1]
    have h_hi_ext : 0 ≤ ∫ b in Ioi (xiStar + r₁), Q b := by
      refine setIntegral_nonneg measurableSet_Ioi fun b hb => ?_
      have hb_ge : x₁ ≤ b := by linarith only [mem_Ioi.mp hb, hx1_hi]
      have hgb := spinGcal_re_nonneg_of_ge ha_pos.le hS.2.1 hS.1 hS.2.2.2.2 hb_ge
      exact mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) hgb
    have hxs_m_le_p : xiStar - r₁ ≤ xiStar + r₁ := by linarith only [hr₁_pos]
    have hsplit_top : ∫ b in Ioi (0 : ℝ), Q b =
        (∫ b in Ioc (0 : ℝ) (xiStar + r₁), Q b) + ∫ b in Ioi (xiStar + r₁), Q b := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        hQ_int.integrableOn hQ_int.integrableOn, Ioc_union_Ioi_eq_Ioi (by linarith only [xiStar_pos, hr₁_pos])]
    have hsplit_mid : ∫ b in Ioc (0 : ℝ) (xiStar + r₁), Q b =
        (∫ b in Ioc (0 : ℝ) (xiStar - r₁), Q b) + ∫ b in (xiStar - r₁)..(xiStar + r₁), Q b := by
      rw [intervalIntegral.integral_of_le hxs_m_le_p]
      have h1 : Ioc (0 : ℝ) (xiStar - r₁) ∪ Ioc (xiStar - r₁) (xiStar + r₁) = Ioc (0 : ℝ) (xiStar + r₁) :=
        Ioc_union_Ioc_eq_Ioc hxs_m_pos.le hxs_m_le_p
      have h2 := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl _)) measurableSet_Ioc
        (hQ_int.integrableOn (s := Ioc 0 (xiStar - r₁)))
        (hQ_int.integrableOn (s := Ioc (xiStar - r₁) (xiStar + r₁)))
      rwa [h1] at h2
    have hQ_win_le : ∫ b in (xiStar - r₁)..(xiStar + r₁), Q b ≤
        ((C₂₃ + 1) / 2 + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      linarith only [hhalf_int, hcal_23, hsplit_top, hsplit_mid, h_hi_ext, hIoc_Q_ge]
    have hfull_re_le : ∫ u in u_lo..u_hi, (spinPtilde c Φ (u : ℂ)).re ≤
        ((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      have h1 := hjac_full.2.2.1
      dsimp only at h1
      rw [hb_uhi, hb_ulo] at h1
      have hlog_nn : 0 ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n :=
        mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.log_nonneg hn_ge1)
      have hdiv_le : (spinCalNorm c Φ)⁻¹ ≤ κ_obs⁻¹ := inv_anti₀ hκ_pos hB_lo
      have hC_nn : 0 ≤ (C₂₃ + 1) / 2 + C₂₄ + C_p := by linarith only [hC23_pos, hC24_pos, hCp_pos]
      rcases le_or_gt 0 (∫ b in (xiStar - r₁)..(xiStar + r₁), Q b) with hQnn | hQneg
      · calc ∫ u in u_lo..u_hi, (spinPtilde c Φ (u : ℂ)).re
            = (spinCalNorm c Φ)⁻¹ * ∫ b in (xiStar - r₁)..(xiStar + r₁), Q b := h1
          _ ≤ κ_obs⁻¹ * (((C₂₃ + 1) / 2 + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n)) :=
              mul_le_mul hdiv_le hQ_win_le hQnn (inv_nonneg.mpr hκ_pos.le)
          _ = ((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by ring
      · have hneg' : (spinCalNorm c Φ)⁻¹ * ∫ b in (xiStar - r₁)..(xiStar + r₁), Q b ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hB_pos.le) hQneg.le
        have hpos_r : 0 ≤ ((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs * (n ^ (-(2 / 3 : ℝ)) * Real.log n) :=
          mul_nonneg (div_nonneg hC_nn hκ_pos.le) hlog_nn
        linarith only [h1, hneg', hpos_r]
    have hcont_re : ContinuousOn (fun u : ℝ => (spinPtilde c Φ (u : ℂ)).re) (Icc u_lo u_hi) :=
      Complex.continuous_re.comp_continuousOn (han.continuousOn.comp continuous_ofReal.continuousOn
        fun u hu => by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, ← h_ac_sq]
          exact abs_lt.mpr ⟨hulo_gt_ac.trans_le hu.1, hu.2.trans_lt huhi_lt_ac⟩)
    have hsplit_u1 : ∫ x in u_lo..u_hi, (spinPtilde c Φ (x : ℂ)).re =
        (∫ x in u_lo..(-R'), (spinPtilde c Φ (x : ℂ)).re) +
        (∫ x in (-R')..R_dom_n, (spinPtilde c Φ (x : ℂ)).re) +
        ∫ x in R_dom_n..u_hi, (spinPtilde c Φ (x : ℂ)).re := by
      have hnegR'_ge : u_lo ≤ -R' := by linarith only [hulo_lt_negR, hR'.2]
      have hnegR'_le_Rdom : -R' ≤ R_dom_n := by linarith only [hR'.1, hR_dom_ge4]
      have h12 := (intervalIntegral.integral_add_adjacent_intervals
        ((hcont_re.mono (Icc_subset_Icc le_rfl (hnegR'_le_Rdom.trans hR_lt_uhi.le))).intervalIntegrable_of_Icc (μ := volume) hnegR'_ge)
        ((hcont_re.mono (Icc_subset_Icc hnegR'_ge hR_lt_uhi.le)).intervalIntegrable_of_Icc (μ := volume) hnegR'_le_Rdom)).symm
      have h23 := (intervalIntegral.integral_add_adjacent_intervals
        ((hcont_re.mono (Icc_subset_Icc le_rfl hR_lt_uhi.le)).intervalIntegrable_of_Icc (μ := volume) (hnegR'_ge.trans hnegR'_le_Rdom))
        ((hcont_re.mono (Icc_subset_Icc (hnegR'_ge.trans hnegR'_le_Rdom) le_rfl)).intervalIntegrable_of_Icc (μ := volume) hR_lt_uhi.le)).symm
      linarith only [h12, h23]
    have h_band_nn : 0 ≤ ∫ x in u_lo..(-R'), (spinPtilde c Φ (x : ℂ)).re := by
      refine intervalIntegral.integral_nonneg (by linarith only [hulo_lt_negR, hR'.2]) fun x hx => ?_
      exact spinPtilde_re_nonneg_of_le hc40 hS.1 hS.2.1 hS.2.2.2.2 hB_pos.le huT_abs hx1_eq
        (abs_lt.mpr ⟨hulo_gt_ac.trans_le hx.1, (hx.2.trans hnegR'_le_uT).trans_lt (huT_lt_uhi.trans huhi_lt_ac)⟩)
        (hx.2.trans hnegR'_le_uT)
    have h_tail_neg : -(∫ x in R_dom_n..u_hi, (spinPtilde c Φ (x : ℂ)).re) ≤
        C_tail * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      have hi1 := (hcont_re.mono (Icc_subset_Icc (hulo_lt_negR.le.trans (by linarith only [hR_dom_ge4])) le_rfl)).intervalIntegrable_of_Icc (μ := volume) hR_lt_uhi.le
      have hnorm1 := intervalIntegral.norm_integral_le_integral_norm
        (f := fun x : ℝ => (spinPtilde c Φ (x : ℂ)).re) (μ := volume) hR_lt_uhi.le
      rw [Real.norm_eq_abs] at hnorm1
      have h2 : ∫ x in R_dom_n..u_hi, ‖(spinPtilde c Φ (x : ℂ)).re‖ ≤
          ∫ x in R_dom_n..u_hi, ‖spinPtilde c Φ (x : ℂ)‖ :=
        intervalIntegral.integral_mono_on hR_lt_uhi.le hi1.norm
          ((continuous_norm.comp_continuousOn (han.continuousOn.comp continuous_ofReal.continuousOn
            fun x hx => by
              rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, ← h_ac_sq]
              exact abs_lt.mpr ⟨by linarith only [hnegR_dom_gt_ac, hR_dom_ge4, hx.1], hx.2.trans_lt huhi_lt_ac⟩)).intervalIntegrable_of_Icc hR_lt_uhi.le)
          fun x _ => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      linarith only [(abs_le.mp (hnorm1.trans (h2.trans htail_le))).1]
    have h_two_eq : ∫ x in (-R')..R_dom_n, (((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re =
        2 * ∫ x in (-R')..R_dom_n, (spinPtilde c Φ (x : ℂ)).re := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hδ_lobe_eq : δ_lobe n = C_dl * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by dsimp [δ_lobe]; ring
    have hCdl_win : 2 * (((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs + C_tail) ≤ C_dl := by
      dsimp [C_dl]
      have h1 : 2 * (((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs + C_tail) =
          ((C₂₃ + 1) + 2 * C₂₄ + 2 * C_p) / κ_obs + 2 * C_tail := by ring
      linarith only [h1]
    have hlog_nn : 0 ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n :=
      mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.log_nonneg hn_ge1)
    have h_ub_single : ∫ x in (-R')..R_dom_n, (spinPtilde c Φ (x : ℂ)).re ≤
        (((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs + C_tail) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      linarith only [hfull_re_le, hsplit_u1, h_band_nn, h_tail_neg]
    calc ∫ x in (-R')..R_dom_n, (((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re
        = 2 * ∫ x in (-R')..R_dom_n, (spinPtilde c Φ (x : ℂ)).re := h_two_eq
      _ ≤ 2 * ((((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs + C_tail) * (n ^ (-(2 / 3 : ℝ)) * Real.log n)) := by
          linarith only [h_ub_single]
      _ = (2 * (((C₂₃ + 1) / 2 + C₂₄ + C_p) / κ_obs + C_tail)) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by ring
      _ ≤ C_dl * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := mul_le_mul_of_nonneg_right hCdl_win hlog_nn
      _ = δ_lobe n := hδ_lobe_eq.symm
  -- Apply `teb_quant_c1_typeII` to `Ψ₂ u := 2 * spinPtilde c Φ u` via helper
  have han_dom : AnalyticOnNhd ℂ (spinPtilde c Φ) (closedBall (0 : ℂ) R_dom_n) :=
    han.mono (closedBall_subset_ball (by rw [← h_ac_sq]; exact hR_dom_lt_ac))
  have hB2 : QuantC1B2Holds (fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u) u_T :=
    spinPtilde_quantC1B2_apply (hteb n hc_teb) rfl han_dom him_dom hR_lt_uhi hu_hi_cA henv
      huT_gt (huT_le.trans (by linarith only [hAThr_lt, hR_dom_ge4])) hpos_band hL1_le hlobe_lb hwin_ub
  exact ⟨hB_lo, han, him_ball, henv, him_dom, hpos_band, hL1_le, hB2⟩

end FormalResearch.ModularBootstrap.Spin

