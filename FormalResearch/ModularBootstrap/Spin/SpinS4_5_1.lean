/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_1_Helpers
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.AiryDiscBounds

/-!
# Section 5.1 Main Theorem (`s4:5.1`)

Proves `spinS4_5_1 : SpinS4_5_1`:
1. Analyticity of `spinPtilde c Φ` on `ball 0 (r_d * n^(2/3))` (`r_d := 2 * virasoroBV^2`).
2. Real-valuedness on the real interval inside that ball.
3. Complex type-(II) Langer majorant on `‖u‖ ≤ (cA * n^(1/3))^2` (`cA := virasoroBV`).
4. Cut-inclusive uniform bound on `closedBall 0 R ∩ closedBall 0 ((cA * n^(1/3))^2)`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.Special

private lemma rpow_neg_third_mul_log_le {n : ℝ} (hn : 1 ≤ n) :
    n ^ (-(1 / 3 : ℝ)) * Real.log n ≤ 3 := by
  have hn_pos : 0 < n := by linarith
  have ht_pos : 0 < n ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hlog_eq : Real.log n = 3 * Real.log (n ^ (1 / 3 : ℝ)) := by
    rw [Real.log_rpow hn_pos]; ring
  have hlog_le : Real.log (n ^ (1 / 3 : ℝ)) ≤ n ^ (1 / 3 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos ht_pos]
  calc n ^ (-(1 / 3 : ℝ)) * Real.log n
      = 3 * (n ^ (-(1 / 3 : ℝ)) * Real.log (n ^ (1 / 3 : ℝ))) := by rw [hlog_eq]; ring
    _ ≤ 3 * (n ^ (-(1 / 3 : ℝ)) * n ^ (1 / 3 : ℝ)) := by gcongr
    _ = 3 * 1 := by
        rw [← Real.rpow_add hn_pos, neg_add_cancel, Real.rpow_zero]
    _ = 3 := by ring

private lemma spinAiryEnv_le_exp_ball {u : ℂ} {R : ℝ} (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    spinAiryEnv u ≤ Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) := by
  unfold spinAiryEnv
  apply Real.exp_le_exp.mpr
  have hre_le : -((u ^ (3 / 2 : ℂ)).re) ≤ ‖u ^ (3 / 2 : ℂ)‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hnorm_cpow : ‖u ^ (3 / 2 : ℂ)‖ ≤ R ^ (3 / 2 : ℝ) := by
    by_cases hu0 : u = 0
    · rw [hu0, Complex.zero_cpow (by norm_num), norm_zero]
      exact Real.rpow_nonneg hR _
    · rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
      exact Real.rpow_le_rpow (norm_nonneg u) hu (by norm_num)
  linarith

private lemma spinPtilde_analytic_on_ball {c : ℝ} (hc40 : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) (2 * virasoroBV ^ 2 * (c - 1) ^ (2 / 3 : ℝ))) := by
  set n : ℝ := c - 1
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hac_eq : 2 * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) = virasoroAC n ^ 2 := by
    rw [virasoroAC_sq n hn_pos.le]
  have hdom : ball (0 : ℂ) (2 * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ)) ⊆
      ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ)) := by
    rw [hac_eq]
    exact ball_subset_ball (virasoroAC_sq_lt_domain hn_pos).le
  have hb_an : AnalyticOnNhd ℂ (virasoroBChart n) (ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ))) :=
    virasoroBChart_analyticOnNhd hn_pos
  have hdb_an : AnalyticOnNhd ℂ (deriv (virasoroBChart n))
      (ball (0 : ℂ) (virasoroRUInf * n ^ (2 / 3 : ℝ))) :=
    hb_an.deriv
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
  have h2 : AnalyticAt ℂ (fun z => -deriv (virasoroBChart n) z) u := (hdb_an u hu_dom).neg
  have h3 : AnalyticAt ℂ (fun z => spinGcal (n / 12) Φ (virasoroBChart n z)) u :=
    (hg_an _ hb_im).comp_of_eq (hb_an u hu_dom) rfl
  have hnum : AnalyticAt ℂ (fun z => ((n / 12 : ℝ) : ℂ) *
      Complex.exp (((n * (2 * π / 3) : ℝ) : ℂ) * virasoroBChart n z) *
      (-deriv (virasoroBChart n) z) * spinGcal (n / 12) Φ (virasoroBChart n z)) u :=
    (h1.mul h2).mul h3
  exact (hnum.mul analyticAt_const).congr (Eventually.of_forall fun z => by
    unfold spinPtilde
    change _ * (spinCalNorm c Φ : ℂ)⁻¹ = _ / (spinCalNorm c Φ : ℂ)
    rw [← div_eq_mul_inv]
    congr 1; simp [n])

private lemma spinPtilde_ofReal_im {c : ℝ} (hc40 : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {u : ℝ} (hu : u ∈ Metric.ball (0 : ℝ) (2 * virasoroBV ^ 2 * (c - 1) ^ (2 / 3 : ℝ))) :
    (spinPtilde c Φ (u : ℂ)).im = 0 := by
  set n : ℝ := c - 1
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hac_eq : 2 * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) = virasoroAC n ^ 2 := by
    rw [virasoroAC_sq n hn_pos.le]
  have hu_abs : |u| ≤ virasoroAC n ^ 2 := by
    rw [← hac_eq]
    have h1 := mem_ball_zero_iff.mp hu
    rw [Real.norm_eq_abs] at h1
    exact h1.le
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
    have hd_im : HasDerivAt (fun t : ℝ => (virasoroBChart n (t : ℂ)).im)
        (deriv (virasoroBChart n) (u : ℂ)).im u :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hd_C
    have hev : (fun t : ℝ => (virasoroBChart n (t : ℂ)).im) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      have ho : IsOpen (Metric.ball (0 : ℝ) (2 * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ))) := isOpen_ball
      filter_upwards [ho.mem_nhds hu] with t ht
      have ht_abs : |t| ≤ virasoroAC n ^ 2 := by
        rw [← hac_eq]
        have h1 := mem_ball_zero_iff.mp ht
        rw [Real.norm_eq_abs] at h1
        exact h1.le
      exact (virasoroBChart_ofReal hn_pos ht_abs).1
    have hd0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 u := hasDerivAt_const u (0 : ℝ)
    exact hd_im.unique (hd0.congr_of_eventuallyEq hev)
  have hexp_im : (Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ))).im = 0 := by
    have heq : ((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ) =
        ((n * (2 * π / 3) * b₀ : ℝ) : ℂ) := by
      rw [hb_eq]; push_cast; ring
    rw [heq, ← Complex.ofReal_exp, Complex.ofReal_im]
  have hneg_im : (-deriv (virasoroBChart n) (u : ℂ)).im = 0 := by simp [hdb_im]
  have hnum_im : (((n / 12 : ℝ) : ℂ) *
      Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ)) *
      (-deriv (virasoroBChart n) (u : ℂ)) * spinGcal (n / 12) Φ (virasoroBChart n (u : ℂ))).im = 0 := by
    simp only [Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero, hexp_im, mul_zero,
      hneg_im, hg_im]
  unfold spinPtilde
  dsimp only
  change ((((n / 12 : ℝ) : ℂ) *
      Complex.exp (((n : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart n (u : ℂ)) *
      (-deriv (virasoroBChart n) (u : ℂ)) * spinGcal (n / 12) Φ (virasoroBChart n (u : ℂ))) /
      (spinCalNorm c Φ : ℂ)).im = 0
  rw [Complex.div_ofReal_im, hnum_im, zero_div]

/-- **`s4:5.1` (`spinning_s4.tex`, Theorem 5.1): source-independent scalar complex Langer
majorant and compact-disc bound for `spinPtilde c Φ`.** -/
theorem spinS4_5_1 : SpinS4_5_1 := by
  intro κ hκ
  obtain ⟨C_strip, hCstrip, hStrip_bd⟩ := spinGcalCl_closed_strip_bound
  obtain ⟨C_slit, hCslit, hSlit_bd⟩ := spinGcal_slit_L1_bound
  let C_κ : ℝ := max (spinPtildeCκ C_strip C_slit κ) 1
  have hCκ_pos : 0 < C_κ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCpj_le : spinPtildeCκ C_strip C_slit κ ≤ C_κ := le_max_left _ _
  let C₂ : ℝ := spinPtildeC2
  let r_d : ℝ := 2 * virasoroBV ^ 2
  let cA : ℝ := virasoroBV
  have hC2_pos : 0 < C₂ := spinPtildeC2_pos
  have hrd_pos : 0 < r_d := by have := virasoroBV_pos; positivity
  have hcA_pos : 0 < cA := virasoroBV_pos
  refine ⟨49, C_κ, C₂, r_d, cA, by norm_num, hCκ_pos, hC2_pos, hrd_pos, hcA_pos, ?_⟩
  intro R hR
  -- Case A bound via `typeII_disc_avg_bound`, Case B bound via direct strip estimate on bounded `n`
  let C_A : ℝ :=
    8 * Real.exp (5 / 2) * spinPtildeCκ C_strip C_slit κ *
      Real.exp (C₂ * 3 * Real.sqrt (R + 2)) *
      Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) * (1 + R) ^ (1 / 2 : ℝ)
  let N_max : ℝ := max 48 (((R + 2) / ((3 / 2 : ℝ) * virasoroBV ^ 2)) ^ (3 / 2 : ℝ))
  let C_B : ℝ :=
    (N_max / 12) * ((2 / xiStar) * chartParams.C_dxi) *
      Real.exp (N_max * (2 * π / 3) * (xiStar + 0.05)) * (C_strip * N_max ^ 2 / κ)
  have hCA_pos : 0 < C_A := by
    have := spinPtildeCκ_pos hκ (C_strip := C_strip) (C_slit := C_slit)
    dsimp [C_A]; positivity
  have hCB_pos : 0 < C_B := by
    have := xiStar_pos; have := chartParams.hCdxi_pos; have := Real.pi_pos
    have hN_pos : 0 < N_max := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    dsimp [C_B]; positivity
  refine ⟨max C_A C_B, lt_max_of_lt_left hCA_pos, ?_⟩
  intro c x₁ hc n a Φ hΦ _hpos_ext hB_lo _hB_hi
  have hc40 : 40 ≤ c := by linarith
  have hn_ge48 : 48 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have hac_le : (cA * n ^ (1 / 3 : ℝ)) ^ 2 ≤ virasoroAC n ^ 2 := by
    rw [virasoroAC_sq n hn_pos.le, mul_pow, ← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 2,
      ← Real.rpow_mul hn_pos.le, show (1 / 3 : ℝ) * (2 : ℕ) = 2 / 3 by norm_num]
    dsimp [cA]
    have : 0 ≤ virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by positivity
    linarith
  have han : AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) (r_d * n ^ (2 / 3 : ℝ))) :=
    spinPtilde_analytic_on_ball hc40 hΦ
  have him : ∀ u : ℝ, u ∈ Metric.ball (0 : ℝ) (r_d * n ^ (2 / 3 : ℝ)) →
      (spinPtilde c Φ (u : ℂ)).im = 0 := fun u hu =>
    spinPtilde_ofReal_im hc40 hΦ hu
  have henv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 →
      0 < (u ^ (1 / 2 : ℂ)).re →
      ‖spinPtilde c Φ u‖ ≤ C_κ * spinAiryEnv u *
        Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re) := by
    intro u hu_ne hu_le hu_re
    have hu_ac : u ∈ closedBall (0 : ℂ) (virasoroAC n ^ 2) :=
      (mem_closedBall_zero_iff.mpr (hu_le.trans hac_le))
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
    have hbd := spinPtilde_pj_bound hCstrip hStrip_bd hCslit hSlit_bd hκ hc hΦ hB_lo hu_ac hu_ne hcut
    refine hbd.trans ?_
    have h1 : 0 ≤ spinAiryEnv u * Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
        (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re) := by
      unfold spinAiryEnv; positivity
    calc spinPtildeCκ C_strip C_slit κ * spinAiryEnv u *
          Real.exp (spinPtildeC2 * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
            (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)
        = spinPtildeCκ C_strip C_slit κ * (spinAiryEnv u *
            Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
              (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)) := by ring
      _ ≤ C_κ * (spinAiryEnv u *
            Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
              (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)) :=
          mul_le_mul_of_nonneg_right hCpj_le h1
      _ = _ := by ring
  refine ⟨han, him, henv, fun u huR huA => ?_⟩
  rcases le_or_gt (R + 2) ((3 / 2 : ℝ) * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ)) with hcaseA | hcaseB
  · -- Case A: disc average bound
    let R₁ : ℝ := min R ((cA * n ^ (1 / 3 : ℝ)) ^ 2)
    let R_dom : ℝ := R₁ + 2
    have hR₁_nn : 0 ≤ R₁ := le_min hR.le (sq_nonneg _)
    have hRdom_lt : R_dom < r_d * n ^ (2 / 3 : ℝ) := by
      have hR₁_leR : R₁ ≤ R := min_le_left _ _
      have hpos_v : 0 < (1 / 2 : ℝ) * virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by positivity
      dsimp [R_dom, r_d]; linarith
    have hRdom_le_ac : R_dom ≤ virasoroAC n ^ 2 := by
      rw [virasoroAC_sq n hn_pos.le]; exact hRdom_lt.le
    let ς : ℝ := C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n
    have hς_nn : 0 ≤ ς := by
      have := Real.log_nonneg (by linarith : 1 ≤ n)
      dsimp [ς]; positivity
    have hς_le : ς ≤ C₂ * 3 := by
      have h3 := rpow_neg_third_mul_log_le (by linarith : 1 ≤ n)
      calc C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n
          = C₂ * (n ^ (-(1 / 3 : ℝ)) * Real.log n) := by ring
        _ ≤ C₂ * 3 := mul_le_mul_of_nonneg_left h3 hC2_pos.le
    have hΨ_an : AnalyticOnNhd ℂ (spinPtilde c Φ) (closedBall (0 : ℂ) R_dom) :=
      han.mono (closedBall_subset_ball hRdom_lt)
    have hΨ_env : ∀ w ∈ closedBall (0 : ℂ) R_dom, ¬ (w.im = 0 ∧ w.re ≤ 0) →
        ‖spinPtilde c Φ w‖ ≤ spinPtildeCκ C_strip C_slit κ * airyEnv w *
          Real.exp (ς * (w ^ (1 / 2 : ℂ)).re) * ‖w‖ ^ (-(1 / 2 : ℝ)) * ((w ^ (1 / 2 : ℂ)).re)⁻¹ := by
      intro w hw hcut
      have hw_ne : w ≠ 0 := fun h0 => hcut ⟨by simp [h0], by simp [h0]⟩
      have hw_ac : w ∈ closedBall (0 : ℂ) (virasoroAC n ^ 2) :=
        closedBall_subset_closedBall hRdom_le_ac hw
      have hbd := spinPtilde_pj_bound hCstrip hStrip_bd hCslit hSlit_bd hκ hc hΦ hB_lo hw_ac hw_ne hcut
      refine hbd.trans_eq ?_
      have henv_eq : spinAiryEnv w = airyEnv w := rfl
      have hsq : Real.sqrt ‖w‖ = ‖w‖ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow ‖w‖
      have hrp : (‖w‖ ^ (1 / 2 : ℝ))⁻¹ = ‖w‖ ^ (-(1 / 2 : ℝ)) :=
        (Real.rpow_neg (norm_nonneg w) (1 / 2 : ℝ)).symm
      rw [henv_eq, div_eq_mul_inv, mul_inv, hsq, hrp]
      dsimp [ς, C₂]; ring
    have hu₀ : u ∈ closedBall (0 : ℂ) R₁ := mem_closedBall_zero_iff.mpr (le_min huR huA)
    have hdisc := (typeII_disc_avg_bound hR₁_nn le_rfl (spinPtildeCκ_pos hκ) hς_nn hΨ_an hΨ_env hu₀).1
    have hR₁2_le : Real.sqrt (R₁ + 2) ≤ Real.sqrt (R + 2) :=
      Real.sqrt_le_sqrt (by linarith [min_le_left R ((cA * n ^ (1 / 3 : ℝ)) ^ 2)])
    have hexp_ς : Real.exp (ς * Real.sqrt (R₁ + 2)) ≤ Real.exp (C₂ * 3 * Real.sqrt (R + 2)) := by
      apply Real.exp_le_exp.mpr
      calc ς * Real.sqrt (R₁ + 2) ≤ (C₂ * 3) * Real.sqrt (R₁ + 2) :=
              mul_le_mul_of_nonneg_right hς_le (Real.sqrt_nonneg _)
        _ ≤ (C₂ * 3) * Real.sqrt (R + 2) :=
              mul_le_mul_of_nonneg_left hR₁2_le (by positivity)
    have hair_le : airyEnv u ≤ Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) :=
      spinAiryEnv_le_exp_ball hR.le huR
    have h1u_le : (1 + ‖u‖) ^ (1 / 2 : ℝ) ≤ (1 + R) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith [norm_nonneg u]) (by linarith) (by norm_num)
    have hsp_pos := spinPtildeCκ_pos hκ (C_strip := C_strip) (C_slit := C_slit)
    have hcomb : 8 * Real.exp (5 / 2) * spinPtildeCκ C_strip C_slit κ *
        Real.exp (ς * Real.sqrt (R₁ + 2)) * airyEnv u * (1 + ‖u‖) ^ (1 / 2 : ℝ) ≤ C_A := by
      dsimp [C_A]
      have h_ae_nn : 0 ≤ airyEnv u := by unfold airyEnv; exact (Real.exp_pos _).le
      gcongr
    exact (hdisc.trans hcomb).trans (le_max_left _ _)
  · -- Case B: bounded `n`, direct strip estimate
    have hn23_lt : n ^ (2 / 3 : ℝ) < (R + 2) / ((3 / 2 : ℝ) * virasoroBV ^ 2) := by
      have hpos : 0 < (3 / 2 : ℝ) * virasoroBV ^ 2 := by have := virasoroBV_pos; positivity
      rw [lt_div_iff₀ hpos]; linarith
    have hn_le_N : n ≤ N_max := by
      have h1 : n = (n ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul hn_pos.le, show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
      have h2 : (n ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤
          ((R + 2) / ((3 / 2 : ℝ) * virasoroBV ^ 2)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hn_pos.le _) hn23_lt.le (by norm_num)
      rw [h1]
      exact h2.trans (le_max_right _ _)
    have hu_ac : u ∈ closedBall (0 : ℂ) (virasoroAC n ^ 2) :=
      mem_closedBall_zero_iff.mpr (huA.trans hac_le)
    have hd_bd : ‖deriv (virasoroBChart n) u‖ ≤ ((2 / xiStar) * chartParams.C_dxi) * tipEps n := by
      have hder := virasoroBChart_deriv_norm_le_spin hn_pos hu_ac
      have hε : 0 < tipEps n := tipEps_pos hn_pos
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le, div_le_iff₀ hε] at hder
      exact hder
    have hb_re_le : (virasoroBChart n u).re ≤ xiStar + 0.05 := by
      have hmin := virasoro_deltaChart_b_min hn_pos hu_ac
      have h05 : ‖virasoroBChart n u - (xiStar : ℂ)‖ ≤ 0.05 :=
        hmin.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hre : |(virasoroBChart n u).re - xiStar| ≤ 0.05 := by
        have h1 := (Complex.abs_re_le_norm (virasoroBChart n u - (xiStar : ℂ))).trans h05
        simpa [Complex.sub_re, Complex.ofReal_re] using h1
      linarith [(abs_le.mp hre).2]
    have hb_im_le : |(virasoroBChart n u).im| ≤ 1 / 2 := by
      have hmin := virasoro_deltaChart_b_min hn_pos hu_ac
      have h05 : ‖virasoroBChart n u - (xiStar : ℂ)‖ ≤ 0.05 :=
        hmin.trans ((min_le_right _ _).trans (min_le_left _ _))
      have him' : |(virasoroBChart n u).im| ≤ 0.05 := by
        simpa using (Complex.abs_im_le_norm (virasoroBChart n u - (xiStar : ℂ))).trans h05
      linarith
    have hG_bd : ‖spinGcal a Φ (virasoroBChart n u)‖ ≤ C_strip * n ^ 2 * spinM2 a Φ := by
      have h1 := hStrip_bd hc40 hΦ (virasoroBChart n u) hb_im_le
      obtain ⟨_, hagree⟩ := spinGcalCl_props hc40 hΦ
      have him_lt : |(virasoroBChart n u).im| < 1 / 2 := by
        have hmin := virasoro_deltaChart_b_min hn_pos hu_ac
        have h05 : ‖virasoroBChart n u - (xiStar : ℂ)‖ ≤ 0.05 :=
          hmin.trans ((min_le_right _ _).trans (min_le_left _ _))
        have him' : |(virasoroBChart n u).im| ≤ 0.05 := by
          simpa using (Complex.abs_im_le_norm (virasoroBChart n u - (xiStar : ℂ))).trans h05
        linarith
      rwa [hagree _ him_lt] at h1
    by_cases hM0 : spinM2 a Φ = 0
    · have hG0 : spinGcal a Φ (virasoroBChart n u) = 0 := by
        rw [← norm_eq_zero]
        have hle := hG_bd; rw [hM0, mul_zero] at hle
        exact le_antisymm hle (norm_nonneg _)
      have hP0 : spinPtilde c Φ u = 0 := by
        unfold spinPtilde
        change ((n / 12 : ℝ) : ℂ) * _ * _ * spinGcal a Φ (virasoroBChart n u) / _ = 0
        rw [hG0]; simp
      rw [hP0, norm_zero]; exact (lt_max_of_lt_left hCA_pos).le
    have hM2_nn : 0 ≤ spinM2 a Φ := integral_nonneg fun p =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg (by dsimp [a, n]; linarith) p.1))
        (spinV1_nonneg (by dsimp [a, n]; linarith) p.2)
    have hM_pos : 0 < spinM2 a Φ := lt_of_le_of_ne hM2_nn (Ne.symm hM0)
    have hB_pos : 0 < spinCalNorm c Φ := lt_of_lt_of_le (mul_pos hκ hM_pos) hB_lo
    have hnorm_eq : ‖spinPtilde c Φ u‖ =
        a * Real.exp (n * (2 * π / 3) * (virasoroBChart n u).re) *
          ‖deriv (virasoroBChart n) u‖ * (‖spinGcal a Φ (virasoroBChart n u)‖ / spinCalNorm c Φ) := by
      unfold spinPtilde
      dsimp only [a, n]
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_pos.le,
        Complex.norm_exp, norm_neg, Complex.norm_real, Real.norm_of_nonneg hB_pos.le]
      have hre_exp : (((c - 1 : ℝ) : ℂ) * ((2 * π / 3 : ℝ) : ℂ) * virasoroBChart (c - 1) u).re =
          (c - 1) * (2 * π / 3) * (virasoroBChart (c - 1) u).re := by
        rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
      rw [hre_exp]; ring
    have hε_le1 : tipEps n ≤ 1 := by
      unfold tipEps
      rw [Real.rpow_neg hn_pos.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
    have hG_div_le : ‖spinGcal a Φ (virasoroBChart n u)‖ / spinCalNorm c Φ ≤ C_strip * n ^ 2 / κ := by
      calc ‖spinGcal a Φ (virasoroBChart n u)‖ / spinCalNorm c Φ
          ≤ (C_strip * n ^ 2 * spinM2 a Φ) / (κ * spinM2 a Φ) :=
            div_le_div₀ (by positivity [hCstrip]) hG_bd (mul_pos hκ hM_pos) hB_lo
        _ = C_strip * n ^ 2 / κ := by field_simp [hM0, hκ.ne']
    have hexp_le : Real.exp (n * (2 * π / 3) * (virasoroBChart n u).re) ≤
        Real.exp (N_max * (2 * π / 3) * (xiStar + 0.05)) := by
      apply Real.exp_le_exp.mpr
      have hxi_nn : 0 ≤ xiStar + 0.05 := by have := xiStar_pos; linarith
      have hpi_nn : 0 ≤ 2 * π / 3 := by have := Real.pi_pos; positivity
      by_cases hbre : 0 ≤ (virasoroBChart n u).re
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hn_le_N hpi_nn) hb_re_le hbre
          (mul_nonneg (by linarith) hpi_nn)
      · have h1 : n * (2 * π / 3) * (virasoroBChart n u).re ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hn_pos.le hpi_nn) (le_of_not_ge hbre)
        exact h1.trans (mul_nonneg (mul_nonneg (by linarith) hpi_nn) hxi_nn)
    have hbd_step : ‖spinPtilde c Φ u‖ ≤ C_B := by
      rw [hnorm_eq]
      have hd_bd1 : ‖deriv (virasoroBChart n) u‖ ≤ (2 / xiStar) * chartParams.C_dxi :=
        hd_bd.trans (mul_le_of_le_one_right (by have := xiStar_pos; have := chartParams.hCdxi_pos; positivity) hε_le1)
      have ha_le : a ≤ N_max / 12 := by dsimp [a]; linarith
      have hstrip_le : C_strip * n ^ 2 / κ ≤ C_strip * N_max ^ 2 / κ := by
        gcongr
      have hn_le_CB : 0 ≤ N_max / 12 := by linarith
      have h_cdxi_nn : 0 ≤ (2 / xiStar) * chartParams.C_dxi := by
        have := xiStar_pos; have := chartParams.hCdxi_pos; positivity
      have h1 : a * Real.exp (n * (2 * π / 3) * (virasoroBChart n u).re) ≤
          (N_max / 12) * Real.exp (N_max * (2 * π / 3) * (xiStar + 0.05)) :=
        mul_le_mul ha_le hexp_le (Real.exp_pos _).le hn_le_CB
      have h2 : a * Real.exp (n * (2 * π / 3) * (virasoroBChart n u).re) * ‖deriv (virasoroBChart n) u‖ ≤
          (N_max / 12) * Real.exp (N_max * (2 * π / 3) * (xiStar + 0.05)) * ((2 / xiStar) * chartParams.C_dxi) :=
        mul_le_mul h1 hd_bd1 (norm_nonneg _) (mul_nonneg hn_le_CB (Real.exp_pos _).le)
      have h3 := mul_le_mul h2 (hG_div_le.trans hstrip_le) (div_nonneg (norm_nonneg _) hB_pos.le)
        (mul_nonneg (mul_nonneg hn_le_CB (Real.exp_pos _).le) h_cdxi_nn)
      exact h3.trans_eq (by dsimp [C_B]; ring)
    exact hbd_step.trans (le_max_right _ _)

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_5_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_5_1

end FormalResearch.ModularBootstrap.Spin
