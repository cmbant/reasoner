/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_1_Boundary
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_StripCont
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LangerChart

/-!
# Section 5.1 Strip & Chart Helpers (`s4:5.1`)

Supporting lemmas for `SpinS4_5_1` (`Spin/SpinS4_5_1_Helpers.lean` and `Spin/SpinS4_5_1.lean`):
1. `spinGcalCl_closed_strip_bound`: uniform `C n² M₂` bound on the closed strip `{|Im b| ≤ 1/2}`.
2. `spinGcal_slit_L1_bound` and `spinCalNorm_le_const_mul_spinM2`: weighted `L¹` slit bound.
3. `spinGcal_bdy_ne_zero_ae`: a.e. non-vanishing on `slitPreimage` when `spinGcal a Φ b₀ ≠ 0`.
4. `virasoroBChart_deriv_norm_le_spin`: `‖deriv (virasoroBChart n) u / tipEps n‖ ≤ (2 / ξ_*) C_dxi`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.Special

lemma spinGcalCl_closed_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {c : ℝ}, 40 ≤ c →
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
        ∀ b : ℂ, |b.im| ≤ 1 / 2 →
          ‖spinGcalCl ((c - 1) / 12) Φ b‖ ≤ C * (c - 1) ^ 2 * spinM2 ((c - 1) / 12) Φ := by
  obtain ⟨C, hC, hbd⟩ := spinGcal_strip_bound_exists
  refine ⟨C, hC, fun {c} hc {Φ} hΦ b hb => ?_⟩
  obtain ⟨hcont, hagree⟩ := spinGcalCl_props hc hΦ
  let seq : ℕ → ℂ := fun k => (b.re : ℂ) + (((1 - 1 / ((k : ℝ) + 2)) * b.im : ℝ) : ℂ) * I
  have hmem_open : ∀ k : ℕ, seq k ∈ spinStrip (1 / 2) := fun k => by
    have h1 : (0 : ℝ) ≤ 1 - 1 / ((k : ℝ) + 2) := by
      have : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have h2 : 1 - 1 / ((k : ℝ) + 2) < 1 := by
      linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 2) by positivity]
    change |(seq k).im| < 1 / 2
    simp only [seq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_add]
    rw [abs_mul, abs_of_nonneg h1]
    rcases eq_or_lt_of_le (abs_nonneg b.im) with him0 | him_pos
    · rw [← him0, mul_zero]; norm_num
    · exact (mul_lt_mul_of_pos_right h2 him_pos).trans_le (by linarith)
  have hmem_cl : ∀ k : ℕ, seq k ∈ {z : ℂ | |z.im| ≤ 1 / 2} := fun k =>
    (show |(seq k).im| < 1 / 2 from hmem_open k).le
  have htend : Tendsto seq atTop (𝓝 b) := by
    have hre : Tendsto (fun _ : ℕ => b.re) atTop (𝓝 b.re) := tendsto_const_nhds
    have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have him : Tendsto (fun k : ℕ => (1 - 1 / ((k : ℝ) + 2)) * b.im) atTop (𝓝 b.im) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).mul_const b.im
    have hc1 := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
    have hc2 := (Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul_const I
    have heq : (b.re : ℂ) + (b.im : ℂ) * I = b := Complex.re_add_im b
    simpa [seq, heq] using hc1.add hc2
  have hwithin : Tendsto seq atTop (𝓝[{z : ℂ | |z.im| ≤ 1 / 2}] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend, Eventually.of_forall hmem_cl⟩
  have hnorm_tend : Tendsto (fun k => ‖spinGcalCl ((c - 1) / 12) Φ (seq k)‖) atTop
      (𝓝 ‖spinGcalCl ((c - 1) / 12) Φ b‖) :=
    (continuous_norm.continuousAt.tendsto.comp ((hcont b hb).tendsto.comp hwithin))
  refine le_of_tendsto hnorm_tend (Eventually.of_forall fun k => ?_)
  rw [hagree _ (hmem_open k)]
  exact hbd hc hΦ _ (hmem_open k)

lemma spinGcal_slit_L1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {c : ℝ}, 40 ≤ c →
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
        Integrable (fun x : ℝ =>
          ‖spinGcal ((c - 1) / 12) Φ (x : ℂ)‖ * ((c - 1) / 12) * Real.exp ((c - 1) * spinL x)) ∧
        (∫ x : ℝ,
          ‖spinGcal ((c - 1) / 12) Φ (x : ℂ)‖ * ((c - 1) / 12) * Real.exp ((c - 1) * spinL x)) ≤
          C * spinM2 ((c - 1) / 12) Φ := by
  obtain ⟨C0, hC0, hS23⟩ := spinS23
  let K : ℝ := 4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0 * spinCalFacStripConst
  have hF : 0 < spinCalF xiStar := by
    unfold spinCalF
    have hlt := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_gt_three, xiStar_pos] : -4 * π * xiStar < 0)
    linarith
  have hs0 : 0 < spinSigma0 := by unfold spinSigma0; positivity
  have hK_pos : 0 < K := by have := spinCalFacStripConst_pos; positivity
  refine ⟨K * C0, mul_pos hK_pos hC0, fun {c} hc {Φ} hΦ => ?_⟩
  let n : ℝ := c - 1
  let a : ℝ := n / 12
  have ha0 : 0 ≤ a := by dsimp [a, n]; linarith
  obtain ⟨_, _, _, hint_eff, hbd_eff, _⟩ := hS23 hc hΦ
  have hcont_g : Continuous (fun x : ℝ => spinGcal a Φ (x : ℂ)) :=
    (spinGcal_differentiableOn_strip hc hΦ).continuousOn.comp_continuous Complex.continuous_ofReal
      fun x => by change |(x : ℂ).im| < 1 / 2; simp [Complex.ofReal_im]
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) volume := by
    have hL : Continuous spinL := by unfold spinL; fun_prop
    exact (((hcont_g.norm.mul continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul hL))).aestronglyMeasurable)
  have hpt : ∀ x : ℝ,
      ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) ≤
        K * (‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) := fun x => by
    rw [spinGcal_eq_mul_spinGeff, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have hcf := norm_spinCalFacC_le (b := (x : ℂ)) (by simp [Complex.ofReal_im])
    have hg0 : 0 ≤ ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) ha0) (Real.exp_pos _).le
    calc ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0) * ‖spinCalFacC (x : ℂ)‖ *
            ‖spinGeff a Φ (x : ℂ)‖) * a * Real.exp (n * spinL x)
        = ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0) * ‖spinCalFacC (x : ℂ)‖) *
            (‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) := by ring
      _ ≤ ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0) * spinCalFacStripConst) *
            (‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) := by gcongr
      _ = _ := by dsimp [K]
  have hint_g : Integrable (fun x : ℝ =>
      ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) volume := by
    refine (hint_eff.const_mul K).mono' hmeas (Eventually.of_forall fun x => ?_)
    have hnn : 0 ≤ ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) ha0) (Real.exp_pos _).le
    simpa only [Real.norm_of_nonneg hnn] using hpt x
  refine ⟨hint_g, ?_⟩
  have hmono := integral_mono hint_g (hint_eff.const_mul K) hpt
  rw [integral_const_mul] at hmono
  calc ∫ x : ℝ, ‖spinGcal a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)
      ≤ K * ∫ x : ℝ, ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) := hmono
    _ ≤ K * (C0 * spinM2 a Φ) := mul_le_mul_of_nonneg_left hbd_eff hK_pos.le
    _ = (K * C0) * spinM2 a Φ := by ring

lemma spinCalNorm_le_const_mul_spinM2 :
    ∃ C : ℝ, 0 < C ∧ ∀ {c : ℝ}, 40 ≤ c →
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
        spinCalNorm c Φ ≤ C * spinM2 ((c - 1) / 12) Φ := by
  obtain ⟨C, hC, hbd⟩ := spinGcal_slit_L1_bound
  refine ⟨C, hC, fun {c} hc {Φ} hΦ => ?_⟩
  obtain ⟨hint, hle⟩ := hbd hc hΦ
  unfold spinCalNorm
  refine (integral_mono ?_ hint fun b => ?_).trans hle
  · refine hint.mono' ?_ (Eventually.of_forall fun b => ?_)
    · have hcont_g : Continuous (fun x : ℝ => spinGcal ((c - 1) / 12) Φ (x : ℂ)) :=
        (spinGcal_differentiableOn_strip hc hΦ).continuousOn.comp_continuous Complex.continuous_ofReal
          fun x => by change |(x : ℂ).im| < 1 / 2; simp [Complex.ofReal_im]
      have hL : Continuous spinL := by unfold spinL; fun_prop
      exact ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hL))).mul
        (Complex.continuous_re.comp hcont_g).abs).aestronglyMeasurable
    · have ha0 : 0 ≤ (c - 1) / 12 := by linarith
      have hnn : 0 ≤ ((c - 1) / 12) * Real.exp ((c - 1) * spinL b) *
          |(spinGcal ((c - 1) / 12) Φ (b : ℂ)).re| :=
        mul_nonneg (mul_nonneg ha0 (Real.exp_pos _).le) (abs_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      calc ((c - 1) / 12) * Real.exp ((c - 1) * spinL b) *
            |(spinGcal ((c - 1) / 12) Φ (b : ℂ)).re|
          ≤ ((c - 1) / 12) * Real.exp ((c - 1) * spinL b) *
              ‖spinGcal ((c - 1) / 12) Φ (b : ℂ)‖ :=
            mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (mul_nonneg ha0 (Real.exp_pos _).le)
        _ = ‖spinGcal ((c - 1) / 12) Φ (b : ℂ)‖ * ((c - 1) / 12) * Real.exp ((c - 1) * spinL b) := by
            ring
  · have ha0 : 0 ≤ (c - 1) / 12 := by linarith
    calc ((c - 1) / 12) * Real.exp ((c - 1) * spinL b) *
          |(spinGcal ((c - 1) / 12) Φ (b : ℂ)).re|
        ≤ ((c - 1) / 12) * Real.exp ((c - 1) * spinL b) *
            ‖spinGcal ((c - 1) / 12) Φ (b : ℂ)‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (mul_nonneg ha0 (Real.exp_pos _).le)
      _ = ‖spinGcal ((c - 1) / 12) Φ (b : ℂ)‖ * ((c - 1) / 12) * Real.exp ((c - 1) * spinL b) := by
          ring

lemma spinGcal_bdy_ne_zero_ae {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) {b₀ : ℂ} (hb₀ : |b₀.im| < 1 / 2)
    (hb₀_ne : spinGcal ((c - 1) / 12) Φ b₀ ≠ 0) :
    ∀ᵐ σ ∂(volume.restrict slitPreimage),
      spinGcal ((c - 1) / 12) Φ (slitBoundaryMap σ : ℂ) ≠ 0 := by
  let a : ℝ := (c - 1) / 12
  let U : Set ℂ := {w : ℂ | |w.im| < 1 / 2}
  have han : AnalyticOnNhd ℂ (spinGcal a Φ) U :=
    (spinGcal_differentiableOn_strip hc hΦ).analyticOnNhd
      (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hpre : IsPreconnected U := by
    have hconv : Convex ℝ U := by
      intro x hx y hy u v hu hv huv
      change |(u • x + v • y).im| < 1 / 2
      have him : (u • x + v • y).im = u * x.im + v * y.im := by
        simp [Complex.add_im, Complex.real_smul]
      rw [him]
      have hx' : |x.im| < 1 / 2 := hx
      have hy' : |y.im| < 1 / 2 := hy
      have hbd : u * |x.im| + v * |y.im| < 1 / 2 := by
        rcases eq_or_lt_of_le hu with rfl | hu_pos
        · have hv1 : v = 1 := by linarith
          subst hv1; simpa using hy'
        · have h1 : u * |x.im| < u * (1 / 2) := mul_lt_mul_of_pos_left hx' hu_pos
          have h2 : v * |y.im| ≤ v * (1 / 2) := mul_le_mul_of_nonneg_left hy'.le hv
          nlinarith [show u + v = 1 from huv]
      calc |u * x.im + v * y.im| ≤ |u * x.im| + |v * y.im| := abs_add_le _ _
        _ = u * |x.im| + v * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
        _ < 1 / 2 := hbd
    exact hconv.isPreconnected
  have hz_re_cnt : {r : ℝ | spinGcal a Φ (r : ℂ) = 0}.Countable := by
    have heq : {r : ℝ | spinGcal a Φ (r : ℂ) = 0} =
        ⋃ k : ℕ, {r : ℝ | r ∈ Icc (-(k : ℝ)) k ∧ spinGcal a Φ (r : ℂ) = 0} := by
      ext r; simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Icc]
      refine ⟨fun hr => ?_, fun ⟨_, _, hr⟩ => hr⟩
      obtain ⟨k, hk⟩ := exists_nat_ge |r|
      exact ⟨k, ⟨by linarith [abs_le.mp hk], by linarith [abs_le.mp hk]⟩, hr⟩
    rw [heq]
    have hfin : ∀ k : ℕ, {r : ℝ | r ∈ Icc (-(k : ℝ)) k ∧ spinGcal a Φ (r : ℂ) = 0}.Finite := by
      intro k; by_contra hinf; rw [Set.not_finite] at hinf
      obtain ⟨r₀, _, hacc⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun _ hr => hr.1)
      have hr₀_mem : (r₀ : ℂ) ∈ U := by simp [U]
      have hfreq : ∃ᶠ z in 𝓝[≠] (r₀ : ℂ), spinGcal a Φ z = 0 := by
        rw [Filter.frequently_iff]
        intro V' hV'
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hV'
        obtain ⟨W', hW', hWV⟩ := hV'
        obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp hW'
        rw [accPt_iff_frequently] at hacc
        obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ :=
          (hacc.and_eventually (Metric.ball_mem_nhds r₀ hδ_pos)).exists
        have hrC_ne : (r : ℂ) ≠ (r₀ : ℂ) := fun he => hr_ne (Complex.ofReal_injective he)
        have hrC_ball : (r : ℂ) ∈ Metric.ball (r₀ : ℂ) δ := by
          rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          simpa [Metric.mem_ball, Real.dist_eq] using hr_ball
        exact ⟨(r : ℂ), hWV ⟨hball hrC_ball, hrC_ne⟩, hr_mem.2⟩
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hr₀_mem hfreq
      exact hb₀_ne (hzero hb₀)
    exact Set.countable_iUnion fun k => (hfin k).countable
  have hσ_cnt : {σ : ℝ | σ ∈ slitPreimage ∧ spinGcal a Φ (slitBoundaryMap σ : ℂ) = 0}.Countable := by
    have hsub : {σ : ℝ | σ ∈ slitPreimage ∧ spinGcal a Φ (slitBoundaryMap σ : ℂ) = 0} ⊆
        ⋃ r ∈ {r : ℝ | spinGcal a Φ (r : ℂ) = 0},
          {σ : ℝ | σ ∈ slitPreimage ∧ slitBoundaryMap σ = r} := fun σ ⟨hσ, h0⟩ =>
      mem_iUnion₂.mpr ⟨slitBoundaryMap σ, h0, hσ, rfl⟩
    exact (hz_re_cnt.biUnion fun r _ => (slitBoundaryMap_preimage_finite r).countable).mono hsub
  have hnull : volume {σ : ℝ | σ ∈ slitPreimage ∧ spinGcal a Φ (slitBoundaryMap σ : ℂ) = 0} = 0 :=
    hσ_cnt.measure_zero volume
  change ∀ᵐ σ ∂volume.restrict (Ioo (-1 : ℝ) 0 ∪ Ioi 1),
      spinGcal a Φ (slitBoundaryMap σ : ℂ) ≠ 0
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hσ hmem h0
  exact hσ ⟨hmem, h0⟩

private lemma spin_sq_cpow_half (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  by_cases hz : z = 0
  · rw [hz, Complex.zero_cpow (by norm_num)]; simp
  · rw [Complex.cpow_def_of_ne_zero hz, ← Complex.exp_nat_mul]
    have hmul : ((2 : ℕ) : ℂ) * (Complex.log z * (1 / 2 : ℂ)) = Complex.log z := by
      push_cast; ring
    rw [hmul, Complex.exp_log hz]

lemma virasoroBChart_deriv_norm_le_spin {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    ‖deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)‖ ≤
      (2 / xiStar) * chartParams.C_dxi := by
  have hu_open : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_closedBall_zero_iff] at hu
    rw [mem_ball_zero_iff]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc')
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc' u hu_open
  have hxi_an : AnalyticAt ℂ (virasoroXiChartC c') u := virasoroXiChartC_analyticOnNhd hc' u hu_open
  have hsq : (fun z => virasoroBChart c' z ^ 2) = fun z => (3 : ℂ) * virasoroXiChartC c' z := by
    ext z; unfold virasoroBChart virasoroBOfXi; exact spin_sq_cpow_half _
  have hd_lhs : HasDerivAt (fun z => virasoroBChart c' z ^ 2)
      (2 * virasoroBChart c' u * deriv (virasoroBChart c') u) u := by
    convert hb_an.differentiableAt.hasDerivAt.pow 2 using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hd_rhs : HasDerivAt (fun z => (3 : ℂ) * virasoroXiChartC c' z)
      (3 * deriv (virasoroXiChartC c') u) u :=
    hxi_an.differentiableAt.hasDerivAt.const_mul 3
  rw [hsq] at hd_lhs
  have hd_eq : 2 * virasoroBChart c' u * deriv (virasoroBChart c') u =
      3 * deriv (virasoroXiChartC c') u := hd_lhs.unique hd_rhs
  let s : ℝ := c' ^ (-(2 / 3 : ℝ))
  let w : ℂ := u * (s : ℂ)
  have hw_mem : w ∈ ball (0 : ℂ) virasoroRUInf := virasoro_u_mem_open_ball hc' hu
  have hw_cl : w ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) := virasoro_u_mem_ball hc' hu
  have hd_xi : HasDerivAt virasoroXiInf (deriv virasoroXiInf w) w :=
    (virasoroXiInf_an w hw_mem).differentiableAt.hasDerivAt
  have hd_lin : HasDerivAt (fun z : ℂ => z * (s : ℂ)) (s : ℂ) u := by
    simpa using (hasDerivAt_id u).mul_const (s : ℂ)
  have hd_xiChart : deriv (virasoroXiChartC c') u = deriv virasoroXiInf w * (s : ℂ) :=
    ((hd_xi.comp u hd_lin).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).deriv
  have hs_eq : (s : ℂ) = ((tipEps c' : ℝ) : ℂ) := rfl
  rw [hd_xiChart, hs_eq] at hd_eq
  have hb_min := virasoro_deltaChart_b_min hc' hu
  have hb_sub : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤ xiStar / 4 :=
    hb_min.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb_lb : 3 * xiStar / 4 ≤ ‖virasoroBChart c' u‖ := by
    have htri := norm_sub_norm_le (xiStar : ℂ) (virasoroBChart c' u)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le] at htri
    linarith
  have hb_ne : virasoroBChart c' u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hb_lb; linarith [xiStar_pos]
  have hε_ne : ((tipEps c' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (tipEps_pos hc').ne'
  have hdiv_eq : deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ) =
      (3 / (2 * virasoroBChart c' u)) * deriv virasoroXiInf w := by
    have h2b : (2 : ℂ) * virasoroBChart c' u ≠ 0 := mul_ne_zero (by norm_num) hb_ne
    apply mul_left_cancel₀ h2b
    calc (2 * virasoroBChart c' u) * (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ))
        = (2 * virasoroBChart c' u * deriv (virasoroBChart c') u) / ((tipEps c' : ℝ) : ℂ) := by ring
      _ = (3 * (deriv virasoroXiInf w * ((tipEps c' : ℝ) : ℂ))) / ((tipEps c' : ℝ) : ℂ) := by
          rw [hd_eq]
      _ = (2 * virasoroBChart c' u) * ((3 / (2 * virasoroBChart c' u)) * deriv virasoroXiInf w) := by
          field_simp [hb_ne, hε_ne]
  rw [hdiv_eq, norm_mul, norm_div, Complex.norm_ofNat, norm_mul, Complex.norm_ofNat]
  have h32_bd : (3 : ℝ) / (2 * ‖virasoroBChart c' u‖) ≤ 2 / xiStar := by
    have hden_pos : 0 < 2 * (3 * xiStar / 4) := by linarith [xiStar_pos]
    calc (3 : ℝ) / (2 * ‖virasoroBChart c' u‖)
        ≤ 3 / (2 * (3 * xiStar / 4)) := by gcongr
      _ = 2 / xiStar := by field_simp [xiStar_pos.ne']; ring
  have hdxi_bd : ‖deriv virasoroXiInf w‖ ≤ chartParams.C_dxi := chartParams.hdxi_bd w hw_cl
  exact mul_le_mul h32_bd hdxi_bd (norm_nonneg _) (by positivity [xiStar_pos])

end FormalResearch.ModularBootstrap.Spin
