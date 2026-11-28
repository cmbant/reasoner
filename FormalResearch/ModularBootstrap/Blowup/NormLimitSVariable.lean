module

public import FormalResearch.ModularBootstrap.Blowup.NormLimitConcrete
public import FormalResearch.ModularBootstrap.Upper.Rigidity.SpectrumCorollary

/-!
# `bl:norm` (`s`-variable form) for fixed-weight problems

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma BL-N (`bl:norm`).

Bridges `NormLimitConcrete` (`airy_blnorm`, `clark_blnorm`, `hb_blnorm` in the Langer `u`-variable)
to the paper's `s`-variable formulation:

* `normProfileS G s := (β : ℂ) * normProfile G (-β s)` (`Φ_N(s) = (β / ‖G_N‖₁) G_N(-β s)`),
  with `‖normProfileS G‖₁ = 1`;
* `psiTildeS prob c' g s := (β : ℂ) * psiTilde prob c' g (-β s)` (the Langer density in `s`);
* threshold translation `(T_j - ξ̄ c'_j) / c'_j^{1/3}` via `virasoro_deltaChart_err` and
  `uAiry`;
* `hb_blnorm_s`, `airy_blnorm_s`, `clark_blnorm_s`:
  upper-bounded `(T_j - ξ̄ c'_j) / c'_j^{1/3} ≤ S_hi` gives
  (a) `liminf (T_j - ξ̄ c'_j) / c'_j^{1/3} ≥ -c_* z_m`, and
  (b) if `(T_j - ξ̄ c'_j) / c'_j^{1/3} ≤ -c_* z_m + o(1)` (forcing convergence to `-c_* z_m` and
  `uAiry (c'_j) (T_j) → z_m`), then `psiTildeS` and its derivatives converge locally uniformly to
  `normProfileS`, converge in `L¹(ℝ)` with no escaping mass, and `M[g_j]⁻¹ ∫₀^∞ g_j V → 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.ModularBootstrap Crossing PoissonJensen WeightAxioms TipFront ConcreteBootstrap
  FixedWeightTip Upper.Rigidity FormalResearch.Special FormalResearch.SignUncertainty

/-- Normalised `s`-variable extremal profile `Φ_N(s) = (β / ‖G‖₁) G(-β s)`. -/
noncomputable def normProfileS (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((betaTip : ℝ) : ℂ) * normProfile G (-((betaTip : ℝ) : ℂ) * s)

/-- Rescaled Langer density in the `s`-variable: `Φ_j^L(s) = β Ψ̃_j(-β s)`. -/
noncomputable def psiTildeS (prob : FixedWeightProblem) (c' : ℝ) (g : ℝ → ℝ) (s : ℂ) : ℂ :=
  ((betaTip : ℝ) : ℂ) * psiTilde prob c' g (-((betaTip : ℝ) : ℂ) * s)

lemma normProfileS_integral_norm {G : ℂ → ℂ} (hG : ExtremalProfile G) :
    ∫ s : ℝ, ‖normProfileS G (s : ℂ)‖ = 1 := by
  have hb := betaTip_pos
  have heq : (fun s : ℝ => ‖normProfileS G (s : ℂ)‖) =
      fun s => betaTip * ‖normProfile G (((-betaTip * s : ℝ) : ℂ))‖ := by
    ext s; unfold normProfileS
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
    congr 2; push_cast; ring
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left
    (fun u : ℝ => ‖normProfile G (u : ℂ)‖) (-betaTip), abs_inv, abs_neg, abs_of_pos hb,
    normProfile_integral_norm hG, smul_eq_mul]
  field_simp [hb.ne']

lemma sThresh_le_delta_of_eventually {c' T : ℕ → ℝ} (hc' : Tendsto c' atTop atTop)
    {S_hi : ℝ} (hS : ∀ᶠ n in atTop, (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ S_hi) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-K) := by
  let K : ℝ := max 0 ((|S_hi| + 1) / cStar)
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKs : S_hi + 1 / 2 ≤ cStar * K := by
    have hm := mul_le_mul_of_nonneg_left (le_max_right 0 ((|S_hi| + 1) / cStar)) cStar_pos.le
    have : cStar * ((|S_hi| + 1) / cStar) = |S_hi| + 1 := by field_simp [cStar_pos.ne']
    linarith [le_abs_self S_hi]
  refine ⟨K, hK0, ?_⟩
  have hc_pos := hc'.eventually (eventually_gt_atTop (0 : ℝ))
  have h_rpow : Tendsto (fun n => (c' n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
  have hc_rpow : ∀ᶠ n in atTop, (c' n) ^ (-(2 / 3 : ℝ)) ≤ 1 / (2 * (chartParams.C_xi * K ^ 2 + 1)) :=
    h_rpow.eventually (eventually_le_nhds (by have := chartParams.hCxi_nn; positivity))
  have hc_vir : ∀ᶠ n in atTop, K ≤ virasoroAC (c' n) ^ 2 := by
    have ht : Tendsto (fun n => virasoroAC (c' n) ^ 2) atTop atTop :=
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc').const_mul_atTop
        (mul_pos two_pos (sq_pos_of_pos virasoroBV_pos))).congr'
        (by
          filter_upwards [hc_pos] with n hn
          simp only [Function.comp_apply]
          rw [virasoroAC_sq _ hn.le])
    exact ht.eventually (eventually_ge_atTop K)
  filter_upwards [hS, hc_pos, hc_vir, hc_rpow] with n hn hc0 hKac herr
  have h_absK : |-K| ≤ virasoroAC (c' n) ^ 2 := by rwa [abs_neg, abs_of_nonneg hK0]
  have hΔ_inv := (abs_le.mp (virasoro_deltaChart_err hc0 h_absK)).1
  have hcp : 0 < (c' n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
  have hT_le : T n ≤ xiBar * c' n + S_hi * (c' n) ^ ((1 : ℝ) / 3) := by
    rw [div_le_iff₀ hcp] at hn; linarith
  have hc_err_bd : chartParams.C_xi * (c' n) ^ (-(1 / 3 : ℝ)) * (-K) ^ 2 ≤
      (1 / 2 : ℝ) * (c' n) ^ ((1 : ℝ) / 3) := by
    have hrp : (c' n) ^ (-(1 / 3 : ℝ)) = (c' n) ^ (-(2 / 3 : ℝ)) * (c' n) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hden_pos : 0 < chartParams.C_xi * K ^ 2 + 1 := by
      have := chartParams.hCxi_nn; positivity
    have hnn : 0 ≤ (c' n) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    have h1 : chartParams.C_xi * K ^ 2 * (c' n) ^ (-(2 / 3 : ℝ)) ≤
        (chartParams.C_xi * K ^ 2 + 1) * (c' n) ^ (-(2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hnn
    have h2 : (chartParams.C_xi * K ^ 2 + 1) * (c' n) ^ (-(2 / 3 : ℝ)) ≤
        (chartParams.C_xi * K ^ 2 + 1) * (1 / (2 * (chartParams.C_xi * K ^ 2 + 1))) :=
      mul_le_mul_of_nonneg_left herr hden_pos.le
    have h3 : (chartParams.C_xi * K ^ 2 + 1) * (1 / (2 * (chartParams.C_xi * K ^ 2 + 1))) = 1 / 2 := by
      field_simp [hden_pos.ne']
    have hm : chartParams.C_xi * (c' n) ^ (-(2 / 3 : ℝ)) * K ^ 2 ≤ 1 / 2 := by
      linarith only [h1, h2, h3]
    calc chartParams.C_xi * (c' n) ^ (-(1 / 3 : ℝ)) * (-K) ^ 2
        = (chartParams.C_xi * (c' n) ^ (-(2 / 3 : ℝ)) * K ^ 2) * (c' n) ^ ((1 : ℝ) / 3) := by
            rw [hrp, neg_sq]; ring
      _ ≤ (1 / 2 : ℝ) * (c' n) ^ ((1 : ℝ) / 3) := mul_le_mul_of_nonneg_right hm hcp.le
  have h1 : xiBar * c' n + S_hi * (c' n) ^ ((1 : ℝ) / 3) ≤
      xiBar * c' n - cStar * (c' n) ^ ((1 : ℝ) / 3) * (-K) -
        chartParams.C_xi * (c' n) ^ (-(1 / 3 : ℝ)) * (-K) ^ 2 := by
    nlinarith only [hc_err_bd, hKs, hcp]
  linarith only [hT_le, h1, hΔ_inv]

/-- Chart conversion between `(T_n - ξ̄ c'_n) / c'_n^{1/3}` and `-c_* chartUT c'_n T_n`. -/
lemma tendsto_sThresh_add_cStar_chartUT {r₁ : ℝ} (hr1 : 0 < r₁) {c' T : ℕ → ℝ}
    (hc' : Tendsto c' atTop atTop)
    (hlo : ∀ᶠ n in atTop, virasoroDeltaChart (c' n) (chartAC r₁ (c' n) ^ 2) ≤ T n)
    (hhi : ∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-(chartAC r₁ (c' n) ^ 2)))
    (hbd : ∃ M : ℝ, ∀ᶠ n in atTop, |chartUT (c' n) (T n)| ≤ M) :
    Tendsto (fun n => (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) + cStar * chartUT (c' n) (T n))
      atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hbd
  have hc_pos := hc'.eventually (eventually_gt_atTop (0 : ℝ))
  have h_err : ∀ᶠ n in atTop,
      |(T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) + cStar * chartUT (c' n) (T n)| ≤
        chartParams.C_xi * M ^ 2 * (c' n) ^ (-(2 / 3 : ℝ)) := by
    filter_upwards [hc_pos, hlo, hhi, hM] with n hc0 h1 h2 h3
    obtain ⟨hmem, hΔu⟩ := chartUT_mem_Icc_of_between' hr1 hc0 h1 h2
    have hA2 := chartAC_sq_le_virasoroAC_sq hr1 hc0.le
    have hu_vir : |chartUT (c' n) (T n)| ≤ virasoroAC (c' n) ^ 2 :=
      (abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩).trans hA2
    have herr := virasoro_deltaChart_err hc0 hu_vir
    rw [hΔu] at herr
    have hcp : 0 < (c' n) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hm := div_le_div_of_nonneg_right herr hcp.le
    rw [← abs_of_pos hcp, ← abs_div, abs_of_pos hcp] at hm
    have heq : (T n - (xiBar * c' n - cStar * (c' n) ^ ((1 : ℝ) / 3) * chartUT (c' n) (T n))) /
        (c' n) ^ ((1 : ℝ) / 3) =
        (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) + cStar * chartUT (c' n) (T n) := by
      field_simp [hcp.ne']; ring
    have hrhs : chartParams.C_xi * (c' n) ^ (-(1 / 3 : ℝ)) * (chartUT (c' n) (T n)) ^ 2 /
        (c' n) ^ ((1 : ℝ) / 3) =
        chartParams.C_xi * (chartUT (c' n) (T n)) ^ 2 * (c' n) ^ (-(2 / 3 : ℝ)) := by
      have hrp : (c' n) ^ (-(1 / 3 : ℝ)) / (c' n) ^ ((1 : ℝ) / 3) = (c' n) ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_sub hc0]; norm_num
      calc chartParams.C_xi * (c' n) ^ (-(1 / 3 : ℝ)) * (chartUT (c' n) (T n)) ^ 2 /
          (c' n) ^ ((1 : ℝ) / 3)
          = chartParams.C_xi * (chartUT (c' n) (T n)) ^ 2 *
              ((c' n) ^ (-(1 / 3 : ℝ)) / (c' n) ^ ((1 : ℝ) / 3)) := by ring
        _ = chartParams.C_xi * (chartUT (c' n) (T n)) ^ 2 * (c' n) ^ (-(2 / 3 : ℝ)) := by rw [hrp]
    rw [heq, hrhs] at hm
    have hu2 : (chartUT (c' n) (T n)) ^ 2 ≤ M ^ 2 := by
      calc (chartUT (c' n) (T n)) ^ 2 = |chartUT (c' n) (T n)| ^ 2 := (sq_abs _).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    have h1' : chartParams.C_xi * (chartUT (c' n) (T n)) ^ 2 * (c' n) ^ (-(2 / 3 : ℝ)) ≤
        chartParams.C_xi * M ^ 2 * (c' n) ^ (-(2 / 3 : ℝ)) := by
      have := chartParams.hCxi_nn
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 this)
        (Real.rpow_nonneg hc0.le _)
    exact hm.trans h1'
  have hlim0 : Tendsto (fun n => chartParams.C_xi * M ^ 2 * (c' n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc').const_mul
        (chartParams.C_xi * M ^ 2)
  exact squeeze_zero_norm' h_err hlim0

private lemma vac_integral_tendsto_zero_of_blnorm {prob : FixedWeightProblem}
    (D : UniformPropositionPData prob) {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-K))
    (hre : Tendsto (fun n => ∫ x in (-(chartAC D.r_1 (c' n) ^ 2))..(chartAC D.r_1 (c' n) ^ 2),
      (psiTilde prob (c' n) (g n) (x : ℂ)).re) atTop (𝓝 0)) :
    Tendsto (fun n => (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
      ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hKev⟩ := hK
  obtain ⟨c_S, C₀, C_gap, κ_gap, hcS, _hC₀, hC_gap, hκ_gap, key⟩ := densityHyp_of_slack D
  have hη4 : ∀ᶠ n in atTop, η n ≤ 1 / 4 := hη.eventually (eventually_le_nhds (by norm_num))
  have hc_ge := hc'.eventually (eventually_ge_atTop c_S)
  have hcA := ((tendsto_chartAC_sq D.hr1_pos).comp hc').eventually (eventually_gt_atTop K)
  have hdl0 : Tendsto (fun n => C_gap * Real.exp (-κ_gap * c' n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => -κ_gap * c' n) atTop atBot :=
      hc'.const_mul_atTop_of_neg (by linarith)
    simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp h1).const_mul C_gap
  have h_lo_ev : ∀ᶠ n in atTop,
      (∫ x in (-(chartAC D.r_1 (c' n) ^ 2))..(chartAC D.r_1 (c' n) ^ 2),
        (psiTilde prob (c' n) (g n) (x : ℂ)).re) - C_gap * Real.exp (-κ_gap * c' n) ≤
      (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t := by
    filter_upwards [hc_ge, hη0, hη4, hsf, hKev, hcA] with n hcS_n hη0_n hη4_n hsf_n hK_n hKA_n
    have hc'_pos : 0 < c' n := D.hc₀_pos.trans_le (hcS.trans hcS_n)
    have hc'_c₀ : D.c₀ ≤ c' n := hcS.trans hcS_n
    have hint := interior_of_le_neg D.hr1_pos hc'_pos hK0 hKA_n hK_n
    obtain ⟨hdl, _, hT_lo, _⟩ := key hcS_n hη0_n hη4_n hsf_n hint
    have hA2_nn : 0 ≤ chartAC D.r_1 (c' n) ^ 2 := sq_nonneg _
    have hA2_vir := chartAC_sq_le_virasoroAC_sq D.hr1_pos hc'_pos.le
    have hre_eq := psiTilde_re_integral_eq prob hc'_pos hsf_n.1 (a := -(chartAC D.r_1 (c' n) ^ 2))
      (b := chartAC D.r_1 (c' n) ^ 2) (by linarith) hA2_vir (by linarith)
    set t_lo := virasoroDeltaChart (c' n) (chartAC D.r_1 (c' n) ^ 2)
    set t_hi := virasoroDeltaChart (c' n) (-(chartAC D.r_1 (c' n) ^ 2))
    have ht_lo_pos : 0 < t_lo := virasoroDeltaChart_pos hc'_pos
      (chart_real_abs_le_virasoro D.hr1_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]))
    have ht_lo_hi : t_lo ≤ t_hi := (hT_lo.trans hint).le
    have ht_hi_nn : 0 ≤ t_hi := ht_lo_pos.le.trans ht_lo_hi
    have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c' n / 12) t := fun {t} ht =>
      (D.cardyV_nonneg hc'_c₀ ht)
    have hgv_int : IntegrableOn (fun t => g n t * prob.cardyV (c' n / 12) t) (Ioi 0) :=
      hsf_n.1.int_cardy.norm.mono'
        (((hsf_n.1.cont.mul (continuous_cardyV prob (c' n / 12)).continuousOn).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
    have hsplit1 : ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t =
        (∫ t in (0 : ℝ)..t_hi, g n t * prob.cardyV (c' n / 12) t) +
        ∫ t in Ioi t_hi, g n t * prob.cardyV (c' n / 12) t := by
      rw [intervalIntegral.integral_of_le ht_hi_nn, ← setIntegral_union Ioc_disjoint_Ioi_same
        measurableSet_Ioi (hgv_int.mono_set Ioc_subset_Ioi_self)
        (hgv_int.mono_set (Ioi_subset_Ioi ht_hi_nn)), Ioc_union_Ioi_eq_Ioi ht_hi_nn]
    have hsplit2 : ∫ t in (0 : ℝ)..t_hi, g n t * prob.cardyV (c' n / 12) t =
        (∫ t in (0 : ℝ)..t_lo, g n t * prob.cardyV (c' n / 12) t) +
        ∫ t in t_lo..t_hi, g n t * prob.cardyV (c' n / 12) t := by
      have hcont : ContinuousOn (fun t => g n t * prob.cardyV (c' n / 12) t) (Ici 0) :=
        hsf_n.1.cont.mul (continuous_cardyV prob (c' n / 12)).continuousOn
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((hcont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos.le)
        ((hcont.mono (fun t (ht : t ∈ Set.Icc (_ : ℝ) _) => ht_lo_pos.le.trans ht.1)).intervalIntegrable_of_Icc
          ht_lo_hi)).symm
    have htail_nn : 0 ≤ ∫ t in Ioi t_hi, g n t * prob.cardyV (c' n / 12) t :=
      setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (hsf_n.2.2.2 t (hint.le.trans (mem_Ioi.mp ht).le)) (hV_nn (ht_hi_nn.trans (mem_Ioi.mp ht).le))
    have h_lobe_bd : -(prob.cardyNorm (c' n / 12) (g n) * deltaLobe prob D.r_1 (c' n) (g n)) ≤
        ∫ t in (0 : ℝ)..t_lo, g n t * prob.cardyV (c' n / 12) t := by
      have hlobe_eq : ∫ t in (0 : ℝ)..t_lo, |g n t| * prob.cardyV (c' n / 12) t =
          prob.cardyNorm (c' n / 12) (g n) * deltaLobe prob D.r_1 (c' n) (g n) := by
        rw [deltaLobe, ← mul_assoc, mul_inv_cancel₀ hsf_n.2.1.ne', one_mul]
      have hcont1 : ContinuousOn (fun t => -(g n t * prob.cardyV (c' n / 12) t)) (Icc 0 t_lo) :=
        ((hsf_n.1.cont.mul (continuous_cardyV prob (c' n / 12)).continuousOn).mono Icc_subset_Ici_self).neg
      have hcont2 : ContinuousOn (fun t => |g n t| * prob.cardyV (c' n / 12) t) (Icc 0 t_lo) :=
        (hsf_n.1.cont.abs.mul (continuous_cardyV prob (c' n / 12)).continuousOn).mono Icc_subset_Ici_self
      have hi1 : IntervalIntegrable (fun t => -(g n t * prob.cardyV (c' n / 12) t)) volume 0 t_lo :=
        hcont1.intervalIntegrable_of_Icc ht_lo_pos.le
      have hi2 : IntervalIntegrable (fun t => |g n t| * prob.cardyV (c' n / 12) t) volume 0 t_lo :=
        hcont2.intervalIntegrable_of_Icc ht_lo_pos.le
      have hm := intervalIntegral.integral_mono_on ht_lo_pos.le hi1 hi2 fun t ht => by
        calc -(g n t * prob.cardyV (c' n / 12) t) = (-g n t) * prob.cardyV (c' n / 12) t := by ring
          _ ≤ |g n t| * prob.cardyV (c' n / 12) t :=
              mul_le_mul_of_nonneg_right (neg_le_abs _) (hV_nn ht.1)
      rw [intervalIntegral.integral_neg, hlobe_eq] at hm
      linarith
    have htot_lo : (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
        (∫ t in t_lo..t_hi, g n t * prob.cardyV (c' n / 12) t) - deltaLobe prob D.r_1 (c' n) (g n) ≤
        (prob.cardyNorm (c' n / 12) (g n))⁻¹ * ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t := by
      have h_int_ineq : (∫ t in t_lo..t_hi, g n t * prob.cardyV (c' n / 12) t) -
          prob.cardyNorm (c' n / 12) (g n) * deltaLobe prob D.r_1 (c' n) (g n) ≤
          ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t := by
        linarith
      have hmul := mul_le_mul_of_nonneg_left h_int_ineq (inv_nonneg.mpr hsf_n.2.1.le)
      have h_id : (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
          ((∫ t in t_lo..t_hi, g n t * prob.cardyV (c' n / 12) t) -
            prob.cardyNorm (c' n / 12) (g n) * deltaLobe prob D.r_1 (c' n) (g n)) =
          (prob.cardyNorm (c' n / 12) (g n))⁻¹ * (∫ t in t_lo..t_hi, g n t * prob.cardyV (c' n / 12) t) -
            deltaLobe prob D.r_1 (c' n) (g n) := by
        field_simp [hsf_n.2.1.ne']
      linarith
    rw [← hre_eq] at htot_lo
    linarith
  have h_hi_ev : ∀ᶠ n in atTop,
      (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t ≤ η n := by
    filter_upwards [hsf] with n hsf_n
    have hmul := mul_le_mul_of_nonneg_left hsf_n.2.2.1 (inv_nonneg.mpr hsf_n.2.1.le)
    have hid : (prob.cardyNorm (c' n / 12) (g n))⁻¹ * (η n * prob.cardyNorm (c' n / 12) (g n)) = η n := by
      field_simp [hsf_n.2.1.ne']
    rwa [hid] at hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hre.sub hdl0) hη h_lo_ev h_hi_ev

private theorem blnorm_s_of_u {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    (z_m : ℝ) (G_lim : ℂ → ℂ) (hExt : ExtremalProfile G_lim)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hS : ∃ S_hi : ℝ, ∀ᶠ n in atTop, (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ S_hi)
    (h_u_main : ∀ (K : ℝ), 0 ≤ K → (∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-K)) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, chartUT (c' n) (T n) ≤ z_m + ε) ∧
      ((∀ x < z_m, ∀ᶠ n in atTop, x ≤ chartUT (c' n) (T n)) →
        Tendsto (fun n => chartUT (c' n) (T n)) atTop (𝓝 z_m) ∧
        (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTilde prob (c' n) (g n)) (normProfile G_lim) atTop
          (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
        Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2)).indicator
          (fun x : ℝ => psiTilde prob (c' n) (g n) (x : ℂ)) x - normProfile G_lim (x : ℂ)‖) atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ x in (-(chartAC D.r_1 (c' n) ^ 2))..(chartAC D.r_1 (c' n) ^ 2),
          (psiTilde prob (c' n) (g n) (x : ℂ)).re) atTop (𝓝 0))) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      -cStar * z_m - ε ≤ (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) ∧
    ((∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ -cStar * z_m + ε) →
      Tendsto (fun n => (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) atTop (𝓝 (-cStar * z_m)) ∧
      Tendsto (fun n => uAiry (c' n) (T n)) atTop (𝓝 z_m) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTildeS prob (c' n) (g n)) (normProfileS G_lim) atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => deriv (psiTildeS prob (c' n) (g n)))
        (deriv (normProfileS G_lim)) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Tendsto (fun n => ∫ s : ℝ,
        ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
          (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s - normProfileS G_lim (s : ℂ)‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t) atTop (𝓝 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        ∫ s in {s : ℝ | R < |s|},
          ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
            (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s‖ < ε)) := by
  obtain ⟨S_hi, hS_ev⟩ := hS
  obtain ⟨K, hK0, hKev⟩ := sThresh_le_delta_of_eventually hc' hS_ev
  obtain ⟨h_u_le, h_b⟩ := h_u_main K hK0 hKev
  obtain ⟨c_S, _C₀, _C_gap, _κ_gap, hcS, _hC₀, _hCg, _hκ, key⟩ := densityHyp_of_slack D
  have hη4 : ∀ᶠ n in atTop, η n ≤ 1 / 4 := hη.eventually (eventually_le_nhds (by norm_num))
  have hc_ge := hc'.eventually (eventually_ge_atTop c_S)
  have hcA := ((tendsto_chartAC_sq D.hr1_pos).comp hc').eventually (eventually_gt_atTop K)
  have h_bounds : (∀ᶠ n in atTop, virasoroDeltaChart (c' n) (chartAC D.r_1 (c' n) ^ 2) ≤ T n) ∧
      (∀ᶠ n in atTop, T n ≤ virasoroDeltaChart (c' n) (-(chartAC D.r_1 (c' n) ^ 2))) ∧
      (∀ᶠ n in atTop, -K ≤ chartUT (c' n) (T n)) := by
    have hall : ∀ᶠ n in atTop, virasoroDeltaChart (c' n) (chartAC D.r_1 (c' n) ^ 2) ≤ T n ∧
        T n ≤ virasoroDeltaChart (c' n) (-(chartAC D.r_1 (c' n) ^ 2)) ∧
        -K ≤ chartUT (c' n) (T n) := by
      filter_upwards [hc_ge, hη0, hη4, hsf, hKev, hcA] with n hcS_n hη0_n hη4_n hsf_n hK_n hKA_n
      have hc'_pos : 0 < c' n := D.hc₀_pos.trans_le (hcS.trans hcS_n)
      have hint := interior_of_le_neg D.hr1_pos hc'_pos hK0 hKA_n hK_n
      obtain ⟨_, _, hT_lo, _⟩ := key hcS_n hη0_n hη4_n hsf_n hint
      exact ⟨hT_lo.le, hint.le, neg_le_chartUT D.hr1_pos hc'_pos hK0 hKA_n hT_lo.le hK_n⟩
    exact ⟨hall.mono fun _ h => h.1, hall.mono fun _ h => h.2.1, hall.mono fun _ h => h.2.2⟩
  have h_bd : ∃ M : ℝ, ∀ᶠ n in atTop, |chartUT (c' n) (T n)| ≤ M := by
    refine ⟨max K (|z_m| + 1), ?_⟩
    filter_upwards [h_bounds.2.2, h_u_le 1 zero_lt_one] with n hlo hhi
    exact abs_le.mpr ⟨by linarith [le_max_left K (|z_m| + 1)],
      hhi.trans (by linarith [le_abs_self z_m, le_max_right K (|z_m| + 1)])⟩
  have h_conv := tendsto_sThresh_add_cStar_chartUT D.hr1_pos hc' h_bounds.1 h_bounds.2.1 h_bd
  refine ⟨fun ε hε => ?_, fun h_s_ub => ?_⟩
  · have h1 := h_u_le (ε / (2 * cStar)) (by have := cStar_pos; positivity)
    have h2' := h_conv.eventually (lt_mem_nhds (by linarith : -(ε / 2) < 0))
    filter_upwards [h1, h2'] with n h1n h2n
    have hc1 : cStar * chartUT (c' n) (T n) ≤ cStar * z_m + ε / 2 := by
      have hm := mul_le_mul_of_nonneg_left h1n cStar_pos.le
      have : cStar * (ε / (2 * cStar)) = ε / 2 := by field_simp [cStar_pos.ne']
      linarith
    linarith
  · have hu_ge : ∀ x < z_m, ∀ᶠ n in atTop, x ≤ chartUT (c' n) (T n) := by
      intro x hx
      let δ : ℝ := cStar * (z_m - x) / 2
      have hδ_pos : 0 < δ := by have := cStar_pos; dsimp [δ]; positivity
      filter_upwards [h_s_ub δ hδ_pos, h_conv.eventually (lt_mem_nhds (by linarith : -δ < 0))] with
        n hs1 hc1
      have hm : cStar * chartUT (c' n) (T n) ≥ cStar * z_m - 2 * δ := by linarith
      have hsub : cStar * (z_m - x) = 2 * δ := by dsimp [δ]; ring
      have : cStar * x ≤ cStar * chartUT (c' n) (T n) := by linarith
      exact le_of_mul_le_mul_left this cStar_pos
    obtain ⟨huT_lim, hUnif, hL1, hRe⟩ := h_b hu_ge
    have hs_lim : Tendsto (fun n => (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) atTop
        (𝓝 (-cStar * z_m)) := by
      have h_mul : Tendsto (fun n => -cStar * chartUT (c' n) (T n)) atTop (𝓝 (-cStar * z_m)) :=
        huT_lim.const_mul (-cStar)
      simpa using h_conv.add h_mul
    have huAiry_lim : Tendsto (fun n => uAiry (c' n) (T n)) atTop (𝓝 z_m) := by
      have hTc : Tendsto (fun n => T n / c' n) atTop (𝓝 xiBar) := by
        have h1 : Tendsto (fun n => ((T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) *
            (c' n) ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
          simpa [mul_zero] using hs_lim.mul ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc')
        have h2 : Tendsto (fun n => ((T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) *
            (c' n) ^ (-(2 / 3 : ℝ)) + xiBar) atTop (𝓝 xiBar) := by
          simpa using h1.add_const xiBar
        refine h2.congr' ?_
        filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with n hc0
        have hrp : (c' n) ^ ((1 : ℝ) / 3) * (c' n) ^ ((2 : ℝ) / 3) = c' n := by
          rw [← Real.rpow_add hc0]; norm_num
        rw [Real.rpow_neg hc0.le]
        field_simp [hc0.ne', (Real.rpow_pos_of_pos hc0 _).ne']
        rw [mul_assoc xiBar, hrp, mul_assoc (T n), hrp]; ring
      have hsqrt : Tendsto (fun n => Real.sqrt (3 * T n / c' n)) atTop (𝓝 xiStar) := by
        have h3 := (hTc.const_mul 3).sqrt
        have heq : Real.sqrt (3 * xiBar) = xiStar := by
          have : 3 * xiBar = xiStar ^ 2 := by unfold xiBar; ring
          rw [this, Real.sqrt_sq xiStar_pos.le]
        have hfun : (fun n => Real.sqrt (3 * (T n / c' n))) = fun n => Real.sqrt (3 * T n / c' n) :=
          funext fun n => by rw [mul_div_assoc]
        rw [heq, hfun] at h3
        exact h3
      have h_id_ev : ∀ᶠ n in atTop,
          uAiry (c' n) (T n) =
            -((T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) *
              (3 * betaTip / (Real.sqrt (3 * T n / c' n) + xiStar)) := by
        filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ)), h_bounds.1] with n hc0 hT_lo
        have hT_nn : 0 ≤ T n :=
          (virasoroDeltaChart_pos hc0
            (chart_real_abs_le_virasoro D.hr1_pos hc0 (by rw [abs_of_nonneg (sq_nonneg _)]))).le.trans hT_lo
        have hsq_eq : Real.sqrt (3 * T n / c' n) ^ 2 = 3 * T n / c' n :=
          Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hT_nn) hc0.le)
        have hsum_pos : 0 < Real.sqrt (3 * T n / c' n) + xiStar := by
          have := Real.sqrt_nonneg (3 * T n / c' n)
          linarith [xiStar_pos]
        have hrp : (c' n) ^ ((1 : ℝ) / 3) * (c' n) ^ ((2 : ℝ) / 3) = c' n := by
          rw [← Real.rpow_add hc0]; norm_num
        unfold uAiry xiBar
        have h_diff_sq : (Real.sqrt (3 * T n / c' n) - xiStar) * (Real.sqrt (3 * T n / c' n) + xiStar) =
            3 * (T n - xiStar ^ 2 / 3 * c' n) / c' n := by
          rw [mul_comm (Real.sqrt (3 * T n / c' n) - xiStar), ← sq_sub_sq, hsq_eq]
          field_simp [hc0.ne']
        have h_eq1 : Real.sqrt (3 * T n / c' n) - xiStar =
            3 * (T n - xiStar ^ 2 / 3 * c' n) / (c' n * (Real.sqrt (3 * T n / c' n) + xiStar)) := by
          calc Real.sqrt (3 * T n / c' n) - xiStar
              = (Real.sqrt (3 * T n / c' n) - xiStar) * (Real.sqrt (3 * T n / c' n) + xiStar) /
                  (Real.sqrt (3 * T n / c' n) + xiStar) := by
                  rw [mul_div_cancel_right₀ _ hsum_pos.ne']
            _ = (3 * (T n - xiStar ^ 2 / 3 * c' n) / c' n) / (Real.sqrt (3 * T n / c' n) + xiStar) := by
                  rw [h_diff_sq]
            _ = 3 * (T n - xiStar ^ 2 / 3 * c' n) / (c' n * (Real.sqrt (3 * T n / c' n) + xiStar)) := by
                  rw [div_div]
        rw [h_eq1]
        have hcp1 : (c' n) ^ ((1 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
        have hc2 : (c' n) ^ ((2 : ℝ) / 3) = c' n / (c' n) ^ ((1 : ℝ) / 3) :=
          eq_div_of_mul_eq hcp1 (by rw [mul_comm]; exact hrp)
        rw [hc2]
        field_simp [hc0.ne', hsum_pos.ne', hcp1]
      have h_fac_lim : Tendsto (fun n => 3 * betaTip / (Real.sqrt (3 * T n / c' n) + xiStar))
          atTop (𝓝 (3 * betaTip / (xiStar + xiStar))) :=
        Tendsto.div tendsto_const_nhds (hsqrt.add tendsto_const_nhds) (by linarith [xiStar_pos])
      have h_tgt : -(-cStar * z_m) * (3 * betaTip / (xiStar + xiStar)) = z_m := by
        unfold cStar
        have hb := betaTip_pos.ne'
        have hx := xiStar_pos.ne'
        field_simp [hb, hx]
        ring
      have h_prod := (hs_lim.neg.mul h_fac_lim)
      rw [h_tgt] at h_prod
      exact h_prod.congr' (h_id_ev.mono fun _ h => h.symm)
    have hS_unif : ∀ m : ℕ,
        TendstoUniformlyOn (fun n => psiTildeS prob (c' n) (g n)) (normProfileS G_lim) atTop
          (closedBall (0 : ℂ) ((m : ℝ) + 1)) := by
      intro m
      obtain ⟨M, hM⟩ := exists_nat_ge (betaTip * ((m : ℝ) + 1))
      have hM' : betaTip * ((m : ℝ) + 1) ≤ (M : ℝ) + 1 := hM.trans (by linarith)
      rw [tendstoUniformlyOn_iff]
      intro ε hε
      have hb_pos := betaTip_pos
      have hU := (tendstoUniformlyOn_iff.mp (hUnif M)) (ε / betaTip) (div_pos hε hb_pos)
      filter_upwards [hU] with n hn s hs
      have hsM : -((betaTip : ℝ) : ℂ) * s ∈ closedBall (0 : ℂ) ((M : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff] at hs ⊢
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hb_pos.le]
        exact (mul_le_mul_of_nonneg_left hs hb_pos.le).trans hM'
      have hd := hn (-((betaTip : ℝ) : ℂ) * s) hsM
      rw [dist_eq_norm] at hd ⊢
      dsimp only [normProfileS, psiTildeS]
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb_pos.le]
      calc betaTip * ‖normProfile G_lim (-((betaTip : ℝ) : ℂ) * s) -
            psiTilde prob (c' n) (g n) (-((betaTip : ℝ) : ℂ) * s)‖
          < betaTip * (ε / betaTip) := mul_lt_mul_of_pos_left hd hb_pos
        _ = ε := mul_div_cancel₀ _ hb_pos.ne'
    obtain ⟨c₀_pt, _hc₀_pos, han_pt⟩ := psiTilde_analyticOnNhd prob
    have hS_deriv : ∀ m : ℕ,
        TendstoUniformlyOn (fun n => deriv (psiTildeS prob (c' n) (g n)))
          (deriv (normProfileS G_lim)) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1)) := by
      intro m
      have hloc : TendstoLocallyUniformlyOn (fun n => psiTildeS prob (c' n) (g n))
          (normProfileS G_lim) atTop (ball (0 : ℂ) ((m : ℝ) + 2)) :=
        (hS_unif (m + 1)).tendstoLocallyUniformlyOn.mono (by
          intro z hz; rw [mem_ball_zero_iff] at hz; rw [mem_closedBall_zero_iff]
          push_cast; linarith)
      have hdiff_ev : ∀ᶠ n in atTop,
          DifferentiableOn ℂ (psiTildeS prob (c' n) (g n)) (ball (0 : ℂ) ((m : ℝ) + 2)) := by
        obtain ⟨M, hM⟩ := exists_nat_ge (betaTip * ((m : ℝ) + 2))
        filter_upwards [hc'.eventually (eventually_ge_atTop c₀_pt), hc_ge, hsf,
          ((tendsto_chartAC_sq D.hr1_pos).comp hc').eventually (eventually_ge_atTop (M : ℝ))] with
          n hc0_n hcS_n hsf_n hAM_n
        have hc'_pos : 0 < c' n := D.hc₀_pos.trans_le (hcS.trans hcS_n)
        have han : AnalyticOnNhd ℂ (psiTilde prob (c' n) (g n)) (psiDom (c' n)) :=
          han_pt hc0_n hsf_n.1
        intro z hz
        have hzM : -((betaTip : ℝ) : ℂ) * z ∈ closedBall (0 : ℂ) (chartAC D.r_1 (c' n) ^ 2) := by
          rw [mem_closedBall_zero_iff, norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg betaTip_pos.le]
          rw [mem_ball_zero_iff] at hz
          have h1 : betaTip * ‖z‖ ≤ betaTip * ((m : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hz.le betaTip_pos.le
          exact h1.trans (hM.trans hAM_n)
        have h_at := (han _ (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos hzM)).differentiableAt
        have h_comp : DifferentiableAt ℂ (psiTildeS prob (c' n) (g n)) z := by
          unfold psiTildeS
          exact (h_at.comp z (differentiableAt_const _ |>.mul differentiableAt_id)).const_mul _
        exact h_comp.differentiableWithinAt
      have hderiv_loc := hloc.deriv hdiff_ev isOpen_ball
      exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hderiv_loc
        (closedBall (0 : ℂ) ((m : ℝ) + 1))
        (closedBall_subset_ball (by linarith)) (isCompact_closedBall (0 : ℂ) ((m : ℝ) + 1))
    have hS_l1 : Tendsto (fun n => ∫ s : ℝ,
        ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
          (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s - normProfileS G_lim (s : ℂ)‖)
        atTop (𝓝 0) := by
      refine hL1.congr' ?_
      filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with n _hc0
      have hb := betaTip_pos
      have heq_f : ∀ s : ℝ,
          ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
            (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s - normProfileS G_lim (s : ℂ)‖ =
          betaTip * ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2)).indicator
            (fun x : ℝ => psiTilde prob (c' n) (g n) (x : ℂ)) (-betaTip * s) -
            normProfile G_lim (((-betaTip * s : ℝ) : ℂ))‖ := by
        intro s
        have hmem : s ∈ Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip) ↔
            -betaTip * s ∈ Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2) := by
          simp only [mem_Icc]
          constructor <;> rintro ⟨h1, h2⟩
          · constructor
            · have hm := mul_le_mul_of_nonneg_left h2 hb.le
              have : betaTip * (chartAC D.r_1 (c' n) ^ 2 / betaTip) = chartAC D.r_1 (c' n) ^ 2 := by
                field_simp [hb.ne']
              linarith
            · have hm := mul_le_mul_of_nonneg_left h1 hb.le
              have : betaTip * -(chartAC D.r_1 (c' n) ^ 2 / betaTip) = -(chartAC D.r_1 (c' n) ^ 2) := by
                field_simp [hb.ne']
              linarith
          · constructor
            · rw [neg_le, le_div_iff₀ hb]; linarith
            · rw [le_div_iff₀ hb]; linarith
        by_cases hs : s ∈ Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)
        · have hs' : -betaTip * s ∈ Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2) := hmem.mp hs
          rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
          unfold psiTildeS normProfileS
          have hcz : -((betaTip : ℝ) : ℂ) * (s : ℂ) = (((-betaTip * s : ℝ) : ℂ)) := by push_cast; ring
          rw [hcz, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
        · have hs' : -betaTip * s ∉ Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2) :=
            mt hmem.mpr hs
          rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs', zero_sub, zero_sub, norm_neg, norm_neg]
          unfold normProfileS
          have hcz : -((betaTip : ℝ) : ℂ) * (s : ℂ) = (((-betaTip * s : ℝ) : ℂ)) := by push_cast; ring
          rw [hcz, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
      simp_rw [heq_f]
      rw [integral_const_mul, Measure.integral_comp_mul_left
        (fun x : ℝ => ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2)) (chartAC D.r_1 (c' n) ^ 2)).indicator
          (fun x : ℝ => psiTilde prob (c' n) (g n) (x : ℂ)) x - normProfile G_lim (x : ℂ)‖) (-betaTip),
        abs_inv, abs_neg, abs_of_pos hb, smul_eq_mul]
      field_simp [hb.ne']
    have hS_no_esc : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        ∫ s in {s : ℝ | R < |s|},
          ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
            (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s‖ < ε := by
      intro ε hε
      have hInt_Phi : Integrable (fun s : ℝ => normProfileS G_lim (s : ℂ)) := by
        refine ((normProfile_integrable hExt).comp_mul_left'
          (neg_ne_zero.mpr betaTip_pos.ne')).const_mul ((betaTip : ℝ) : ℂ) |>.congr
          (Eventually.of_forall fun s => ?_)
        unfold normProfileS
        push_cast; ring
      have hInt_norm : Integrable (fun s : ℝ => ‖normProfileS G_lim (s : ℂ)‖) := hInt_Phi.norm
      have h_symm : Tendsto (fun R : ℝ => ∫ s in (Icc (-R) R), ‖normProfileS G_lim (s : ℂ)‖)
          atTop (𝓝 (∫ s : ℝ, ‖normProfileS G_lim (s : ℂ)‖)) := by
        have hdom : ∀ R : ℝ, ∀ᵐ s, ‖(Icc (-R) R).indicator (fun s : ℝ => ‖normProfileS G_lim (s : ℂ)‖) s‖ ≤
            ‖normProfileS G_lim (s : ℂ)‖ := fun R => Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]
          by_cases hs : s ∈ Icc (-R) R
          · rw [Set.indicator_of_mem hs, abs_of_nonneg (norm_nonneg _)]
          · rw [Set.indicator_of_notMem hs, abs_zero]; exact norm_nonneg _
        have hlim_pt : ∀ᵐ s, Tendsto (fun R : ℝ =>
            (Icc (-R) R).indicator (fun s : ℝ => ‖normProfileS G_lim (s : ℂ)‖) s) atTop
            (𝓝 ‖normProfileS G_lim (s : ℂ)‖) := Eventually.of_forall fun s => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop |s|] with R hR
          rw [Set.indicator_of_mem (mem_Icc.mpr ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩)]
        have hmeas : ∀ᶠ R in atTop,
            AEStronglyMeasurable (fun s => (Icc (-R) R).indicator (fun s : ℝ => ‖normProfileS G_lim (s : ℂ)‖) s)
              volume := Eventually.of_forall fun R =>
          (hInt_norm.aestronglyMeasurable.indicator measurableSet_Icc)
        have h1 := tendsto_integral_filter_of_dominated_convergence (fun s : ℝ => ‖normProfileS G_lim (s : ℂ)‖)
          hmeas (Eventually.of_forall hdom) hInt_norm hlim_pt
        exact h1.congr (fun R => integral_indicator measurableSet_Icc)
      obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (h_symm.eventually (lt_mem_nhds
        (show (∫ s : ℝ, ‖normProfileS G_lim (s : ℂ)‖) - ε / 2 < ∫ s : ℝ, ‖normProfileS G_lim (s : ℂ)‖ by linarith)))
      let R : ℝ := max R₀ 1
      have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hR_tail : ∫ s in {s : ℝ | R < |s|}, ‖normProfileS G_lim (s : ℂ)‖ < ε / 2 := by
        have hcompl : {s : ℝ | R < |s|} = (Icc (-R) R)ᶜ := by
          ext s; simp only [mem_ofPred_eq, mem_compl_iff, mem_Icc, not_and_or, not_le, lt_abs, lt_neg]
          exact or_comm
        rw [hcompl]
        have hadd := integral_add_compl (measurableSet_Icc : MeasurableSet (Icc (-R) R)) hInt_norm
        have hle := hR₀ R (le_max_left _ _)
        linarith
      refine ⟨R, hR_pos, ?_⟩
      filter_upwards [hS_l1.eventually (gt_mem_nhds (half_pos hε)),
        hc'.eventually (eventually_ge_atTop c₀_pt), hc_ge, hsf] with n hn hc0_n hcS_n hsf_n
      let J_n : Set ℝ := Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)
      let ind : ℝ → ℂ := fun s => J_n.indicator (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s
      have hc'_pos : 0 < c' n := D.hc₀_pos.trans_le (hcS.trans hcS_n)
      have han : AnalyticOnNhd ℂ (psiTilde prob (c' n) (g n)) (psiDom (c' n)) :=
        han_pt hc0_n hsf_n.1
      have hcont : ContinuousOn (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) J_n := by
        intro s hs
        dsimp only [psiTildeS]
        have hs' : -((betaTip : ℝ) : ℂ) * (s : ℂ) ∈ closedBall (0 : ℂ) (chartAC D.r_1 (c' n) ^ 2) := by
          rw [mem_closedBall_zero_iff, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg betaTip_pos.le,
            Complex.norm_real, Real.norm_eq_abs]
          obtain ⟨h1, h2⟩ := hs
          have h_abs : |s| ≤ chartAC D.r_1 (c' n) ^ 2 / betaTip := abs_le.mpr ⟨h1, h2⟩
          have hm := mul_le_mul_of_nonneg_left h_abs betaTip_pos.le
          have hid : betaTip * (chartAC D.r_1 (c' n) ^ 2 / betaTip) = chartAC D.r_1 (c' n) ^ 2 := by
            field_simp [betaTip_pos.ne']
          rwa [hid] at hm
        have h_at := (han _ (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos hs')).continuousAt
        have h_c : ContinuousAt (fun z : ℂ => psiTilde prob (c' n) (g n) (-((betaTip : ℝ) : ℂ) * z)) (s : ℂ) :=
          h_at.comp (continuousAt_const.mul continuousAt_id)
        exact (continuousAt_const.mul (h_c.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
      have h_int_raw : Integrable ind :=
        (integrable_indicator_iff measurableSet_Icc).mpr hcont.integrableOn_Icc
      have h_int_ind : Integrable (fun s => ‖ind s‖) := h_int_raw.norm
      have h_int_diff : Integrable (fun s => ‖ind s - normProfileS G_lim (s : ℂ)‖) :=
        (h_int_raw.sub hInt_Phi).norm
      have hmono : ∫ s in {s : ℝ | R < |s|}, ‖ind s‖ ≤
          ∫ s in {s : ℝ | R < |s|}, (‖ind s - normProfileS G_lim (s : ℂ)‖ + ‖normProfileS G_lim (s : ℂ)‖) := by
        refine setIntegral_mono_on h_int_ind.integrableOn
          (h_int_diff.integrableOn.add hInt_norm.integrableOn)
          (isOpen_lt continuous_const continuous_abs).measurableSet fun s _ => ?_
        calc ‖ind s‖ = ‖(ind s - normProfileS G_lim (s : ℂ)) + normProfileS G_lim (s : ℂ)‖ := by
              congr 1; abel
          _ ≤ ‖ind s - normProfileS G_lim (s : ℂ)‖ + ‖normProfileS G_lim (s : ℂ)‖ := norm_add_le _ _
      have hadd_tail : ∫ s in {s : ℝ | R < |s|},
          (‖ind s - normProfileS G_lim (s : ℂ)‖ + ‖normProfileS G_lim (s : ℂ)‖) =
          (∫ s in {s : ℝ | R < |s|}, ‖ind s - normProfileS G_lim (s : ℂ)‖) +
            ∫ s in {s : ℝ | R < |s|}, ‖normProfileS G_lim (s : ℂ)‖ :=
        integral_add h_int_diff.integrableOn hInt_norm.integrableOn
      have hdiff_le : ∫ s in {s : ℝ | R < |s|}, ‖ind s - normProfileS G_lim (s : ℂ)‖ ≤
          ∫ s : ℝ, ‖ind s - normProfileS G_lim (s : ℂ)‖ :=
        setIntegral_le_integral h_int_diff (Eventually.of_forall fun _ => norm_nonneg _)
      have hn' : ∫ s : ℝ, ‖ind s - normProfileS G_lim (s : ℂ)‖ < ε / 2 := hn
      change ∫ s in {s : ℝ | R < |s|}, ‖ind s‖ < ε
      linarith
    exact ⟨hs_lim, huAiry_lim, hS_unif, hS_deriv, hS_l1,
      vac_integral_tendsto_zero_of_blnorm D hc' hη hη0 hsf ⟨K, hK0, hKev⟩ hRe, hS_no_esc⟩

/-- **`bl:norm`, general `m₀`, `s`-variable form for fixed-weight problems.** -/
theorem hb_blnorm_s {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    (H : HermiteBiehlerData)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hS : ∃ S_hi : ℝ, ∀ᶠ n in atTop, (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ S_hi)
    (hnode : ∀ i : HbNodes H, ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 i.1) ∧
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (ũ n))) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      -cStar * H.tm - ε ≤ (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) ∧
    ((∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ -cStar * H.tm + ε) →
      Tendsto (fun n => (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) atTop (𝓝 (-cStar * H.tm)) ∧
      Tendsto (fun n => uAiry (c' n) (T n)) atTop (𝓝 H.tm) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTildeS prob (c' n) (g n)) (normProfileS H.G) atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => deriv (psiTildeS prob (c' n) (g n)))
        (deriv (normProfileS H.G)) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Tendsto (fun n => ∫ s : ℝ,
        ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
          (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s - normProfileS H.G (s : ℂ)‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t) atTop (𝓝 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        ∫ s in {s : ℝ | R < |s|},
          ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
            (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s‖ < ε)) :=
  blnorm_s_of_u D H.tm H.G (hbExtremalProfile H) hc' hη hη0 hsf hS fun K hK0 hKev =>
    hb_blnorm D H hc' hη hη0 hsf ⟨K, hK0, hKev⟩ hnode

/-- **`bl:norm`, `m₀ = 1` (Airy), `s`-variable form for fixed-weight problems.** -/
theorem airy_blnorm_s {prob : FixedWeightProblem} (D : UniformPropositionPData prob)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hS : ∃ S_hi : ℝ, ∀ᶠ n in atTop, (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ S_hi) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      -cStar * airyZero 1 - ε ≤ (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) ∧
    ((∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ -cStar * airyZero 1 + ε) →
      Tendsto (fun n => (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) atTop (𝓝 Aopt) ∧
      Tendsto (fun n => uAiry (c' n) (T n)) atTop (𝓝 (airyZero 1)) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTildeS prob (c' n) (g n))
        (normProfileS airyExtremal) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => deriv (psiTildeS prob (c' n) (g n)))
        (deriv (normProfileS airyExtremal)) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Tendsto (fun n => ∫ s : ℝ,
        ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
          (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s - normProfileS airyExtremal (s : ℂ)‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t) atTop (𝓝 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        ∫ s in {s : ℝ | R < |s|},
          ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
            (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s‖ < ε)) := by
  have h := blnorm_s_of_u D (airyZero 1) airyExtremal airyExtremalProfile hc' hη hη0 hsf hS
    fun K hK0 hKev => airy_blnorm D hc' hη hη0 hsf ⟨K, hK0, hKev⟩
  have hAopt : -cStar * airyZero 1 = Aopt := by
    unfold Aopt; rw [abs_of_neg (airyZero_neg 1)]; ring
  simpa [hAopt] using h

/-- **`bl:norm`, `m₀ = 2` (Clark), `s`-variable form for fixed-weight problems.** -/
theorem clark_blnorm_s {prob : FixedWeightProblem} (D : UniformPropositionPData prob) {α : ℝ}
    (hα : Real.sin α ≠ 0)
    {c' T η : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hc' : Tendsto c' atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hη0 : ∀ᶠ n in atTop, 0 ≤ η n)
    (hsf : ∀ᶠ n in atTop, IsSlackFeasible prob (c' n / 12) (T n) (η n) (g n))
    (hS : ∃ S_hi : ℝ, ∀ᶠ n in atTop, (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ S_hi)
    (hnode : ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 (clarkNode α 1)) ∧
      ∀ᶠ n in atTop, 0 ≤ g n (virasoroDeltaChart (c' n) (ũ n))) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      -cStar * clarkNode α 2 - ε ≤ (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) ∧
    ((∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3) ≤ -cStar * clarkNode α 2 + ε) →
      Tendsto (fun n => (T n - xiBar * c' n) / (c' n) ^ ((1 : ℝ) / 3)) atTop
        (𝓝 (-cStar * clarkNode α 2)) ∧
      Tendsto (fun n => uAiry (c' n) (T n)) atTop (𝓝 (clarkNode α 2)) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => psiTildeS prob (c' n) (g n))
        (normProfileS (clarkExtremal α)) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun n => deriv (psiTildeS prob (c' n) (g n)))
        (deriv (normProfileS (clarkExtremal α))) atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Tendsto (fun n => ∫ s : ℝ,
        ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
          (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s - normProfileS (clarkExtremal α) (s : ℂ)‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (prob.cardyNorm (c' n / 12) (g n))⁻¹ *
        ∫ t in Ioi (0 : ℝ), g n t * prob.cardyV (c' n / 12) t) atTop (𝓝 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        ∫ s in {s : ℝ | R < |s|},
          ‖(Icc (-(chartAC D.r_1 (c' n) ^ 2 / betaTip)) (chartAC D.r_1 (c' n) ^ 2 / betaTip)).indicator
            (fun s : ℝ => psiTildeS prob (c' n) (g n) (s : ℂ)) s‖ < ε)) :=
  blnorm_s_of_u D (clarkNode α 2) (clarkExtremal α) (clarkExtremalProfile hα) hc' hη hη0 hsf hS
    fun K hK0 hKev => clark_blnorm D hα hc' hη hη0 hsf ⟨K, hK0, hKev⟩ hnode

/-- info: 'FormalResearch.ModularBootstrap.Blowup.hb_blnorm_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hb_blnorm_s

/-- info: 'FormalResearch.ModularBootstrap.Blowup.airy_blnorm_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_blnorm_s

/-- info: 'FormalResearch.ModularBootstrap.Blowup.clark_blnorm_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_blnorm_s

end FormalResearch.ModularBootstrap.Blowup
