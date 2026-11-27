module

public import Mathlib
public import FormalResearch.SignUncertainty.CtSdMain
public import FormalResearch.SignUncertainty.CtDualLim
public import FormalResearch.SignUncertainty.CtLangerBeta
public import FormalResearch.SignUncertainty.CtChartPsiAnalytic
public import FormalResearch.SignUncertainty.CtWindowOrth
public import FormalResearch.SignUncertainty.CtRoscBudget
public import FormalResearch.Special.AiryAsymBiPos
public import FormalResearch.Special.AiryBound

/-!
# `ct:dyadic` (4), `window` Step W3 (`ct:cfu` (1) in the Hankel chart `[-R', φ_c(R)]`)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:dyadic` Part (4) `(ct:combined)` and Lemma `ct:cfu` (1).

Proves:
* `ctCfu_Xi_eq_hankelXiUnit`: `CtCfu.Xi a = hankelXiUnit a` on a two-sided neighborhood `(-δ, δ)` of `0` via `AnalyticAt`
  and the identity theorem against `CtLangerBeta.ct_NF_tau0_sq`, `ct_AF_tau0_sq`; hence
  `CtCfu.NF (CtCfu.zA (ctMu c * x)) = Real.log (π ^ 2 * hankelXi c x)` on both signs of `x`.
* `airyAiBiDeriv_abs_le`: uniform `O(1)` bound on `Ai'(U) Bi(U) + Ai(U) Bi'(U)` across all `U : ℝ`.
* `ctPhiR_uhatAn_inv`: `ctPhiR ε c u + ctLam c * CtCfu.psiOf th (ctMu c * ctPhiR ε c u) = u` on ALL `u ∈ [-R, R]`
  by holomorphic continuation on `ball 0 (R + 1)`.
* `dualK_cfu_hankel_band`: transfers `CtSd.cfu_K_airy_beta` to `x ∈ [-ctRprime ε c R, ctPhiR ε c R]` as a
  bound on `|dualK ε c (hankelXi c x) - (α₁ (-π (Ai Bi)'(U(x))) + c^{-2/3} α₂ (Ai Bi)(U(x)))|`.
-/

@[expose] public section

open Complex Metric Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Part 1: Two-sided analytic identification `CtCfu.Xi = hankelXiUnit` -/

/-- The `c`-independent unit Langer coordinate `ξ_unit(a) = (1 + Re y⁻¹(a / (2^{2/3} κ))) / π²`. -/
noncomputable def hankelXiUnit (a : ℝ) : ℝ :=
  (1 + (chartYinv etaC (((a / ((2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa) : ℝ)) : ℂ)).re) / π ^ 2

lemma hankelXi_eq_hankelXiUnit {c : ℝ} (hc : 0 < c) (x : ℝ) :
    hankelXi c x = hankelXiUnit (ctMu c * x) := by
  unfold hankelXi hankelXiUnit ctMu langerScale
  congr 3
  have h1 : c ^ (-(2 / 3) : ℝ) = (c ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg hc.le _
  have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have h3 : c ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have h4 : langerKappa ≠ 0 := langerKappa_pos.ne'
  rw [h1]
  congr 1
  field_simp

lemma chartY_etaC_zero : chartY etaC 0 = 0 := by
  have h := norm_chartY_add_le langerEta_etaC (w := (0 : ℂ)) (by norm_num)
  simpa using h

lemma analyticOnNhd_ball_of_analyticAt {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ r > (0 : ℝ), AnalyticOnNhd ℝ f (ball 0 r) := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨s0, hs0pos, hs0R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hs0 : (0 : ℝ) < s0 := by exact_mod_cast hs0pos
  refine ⟨s0, hs0, fun x hx => ?_⟩
  have hxb : x ∈ Metric.eball (0 : ℝ) R := by
    rw [Metric.mem_eball, edist_zero_right]
    have hx' : |x| < (s0 : ℝ) := by simpa [Real.dist_eq] using hx
    have hnn : (‖x‖₊ : ENNReal) < s0 := by
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm, Real.norm_eq_abs]; exact hx'
    exact hnn.trans hs0R
  exact hp.analyticOnNhd x hxb

lemma analyticAt_hankelXiUnit : AnalyticAt ℝ hankelXiUnit 0 := by
  have hcy0 : AnalyticAt ℂ (chartYinv etaC) 0 := by
    have h := (analyticAt_chartYinv langerEta_etaC (w0 := (0 : ℂ)) (by norm_num)).1
    rwa [chartY_etaC_zero] at h
  have hcyR : AnalyticAt ℝ (fun y : ℝ => (chartYinv etaC (y : ℂ)).re) 0 :=
    (Complex.reCLM.analyticAt _).comp ((hcy0.restrictScalars).comp_of_eq (Complex.ofRealCLM.analyticAt 0) (by simp))
  have hlin : AnalyticAt ℝ (fun a : ℝ => a / ((2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa)) 0 :=
    analyticAt_id.div analyticAt_const (by have := langerKappa_pos; positivity)
  have hcomp : AnalyticAt ℝ (fun a : ℝ => (chartYinv etaC (((a / ((2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa) : ℝ)) : ℂ)).re) 0 :=
    hcyR.comp_of_eq hlin (by simp)
  exact (analyticAt_const.add hcomp).div analyticAt_const (by positivity)

lemma analyticAt_CtCfu_Xi : AnalyticAt ℝ CtCfu.Xi 0 := by
  have hNF : AnalyticAt ℝ CtCfu.NF 0 := analyticAt_id.mul CtCfu.analyticAt_nfun
  have hcomp : AnalyticAt ℝ (fun a => CtCfu.NF (CtCfu.zA a)) 0 :=
    hNF.comp_of_eq CtCfu.analyticAt_zA CtCfu.zA_zero
  exact hcomp.rexp.div analyticAt_const (by positivity)

/-- Near `0`, `CtCfu.Xi` and `hankelXiUnit` agree on both signs of `a`. -/
theorem ctCfu_Xi_eq_hankelXiUnit :
    ∃ δ > (0 : ℝ), ∀ a : ℝ, |a| < δ →
      CtCfu.Xi a = hankelXiUnit a ∧
      CtCfu.NF (CtCfu.zA a) = Real.log (π ^ 2 * hankelXiUnit a) ∧
      CtCfu.AF (CtCfu.zA a) = a := by
  -- Local inverse `zA (AF z) = z` via `StrictAntiOn AF` near `0` and `AF (zA a) = a`
  have hAFp_neg : ∀ᶠ z in 𝓝 (0 : ℝ), CtCfu.AFp z < 0 := by
    have hcont : ContinuousAt CtCfu.AFp 0 := CtCfu.hasDerivAt_AFp_zero.continuousAt
    exact hcont.eventually (Iio_mem_nhds (by rw [CtCfu.AFp_zero]; have := CtCfu.d0_pos; linarith only [sq_pos_of_pos this]))
  obtain ⟨r1, hr1_pos, hr1⟩ := Metric.eventually_nhds_iff.mp hAFp_neg
  have hf_ev : ∀ᶠ z in 𝓝 (0 : ℝ), 0 < CtCfu.fF z :=
    (CtCfu.contDiffAt_fF.continuousAt).eventually (Ioi_mem_nhds (by rw [CtCfu.fF_zero]; positivity))
  obtain ⟨r2, hr2_pos, hr2⟩ := Metric.eventually_nhds_iff.mp hf_ev
  set rI : ℝ := min (min r1 r2) CtCfu.rr
  have hrI_pos : 0 < rI := lt_min (lt_min hr1_pos hr2_pos) CtCfu.rr_pos
  have hAnti : StrictAntiOn CtCfu.AF (Ioo (-rI) rI) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo (-rI) rI) ?_ ?_
    · intro z hz
      have hz1 : z ∈ Ioo (-CtCfu.rr) CtCfu.rr :=
        ⟨by linarith only [hz.1, show rI ≤ CtCfu.rr from min_le_right _ _],
         by linarith only [hz.2, show rI ≤ CtCfu.rr from min_le_right _ _]⟩
      have hfpos : 0 < CtCfu.fF z := hr2 (by
        rw [Real.dist_eq, sub_zero]
        exact (abs_lt.2 hz).trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      exact (CtCfu.hasDerivAt_AF hz1 hfpos).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ioo] at hz
      have hz1 : z ∈ Ioo (-CtCfu.rr) CtCfu.rr :=
        ⟨by linarith only [hz.1, show rI ≤ CtCfu.rr from min_le_right _ _],
         by linarith only [hz.2, show rI ≤ CtCfu.rr from min_le_right _ _]⟩
      have hfpos : 0 < CtCfu.fF z := hr2 (by
        rw [Real.dist_eq, sub_zero]
        exact (abs_lt.2 hz).trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      rw [(CtCfu.hasDerivAt_AF hz1 hfpos).deriv]
      exact hr1 (by
        rw [Real.dist_eq, sub_zero]
        exact (abs_lt.2 hz).trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hAF_zA := CtCfu.AF_zA_eventually
  obtain ⟨rA, hrA_pos, hrA⟩ := Metric.eventually_nhds_iff.mp hAF_zA
  have hzA_AF : ∀ᶠ z in 𝓝 (0 : ℝ), CtCfu.zA (CtCfu.AF z) = z := by
    have hcontA : ContinuousAt CtCfu.AF 0 := CtCfu.hasDerivAt_AF_zero.continuousAt
    have hev1 : ∀ᶠ z in 𝓝 (0 : ℝ), CtCfu.AF z ∈ ball (0 : ℝ) rA :=
      hcontA.eventually (by rw [CtCfu.AF_zero]; exact ball_mem_nhds 0 hrA_pos)
    have hev2 : ∀ᶠ z in 𝓝 (0 : ℝ), CtCfu.zA (CtCfu.AF z) ∈ Ioo (-rI) rI :=
      (CtCfu.tendsto_zA.comp (by simpa [CtCfu.AF_zero] using hcontA.tendsto : Tendsto CtCfu.AF (𝓝 0) (𝓝 0))).eventually
        (Ioo_mem_nhds (by linarith only [hrI_pos]) hrI_pos)
    have hev3 : ∀ᶠ z in 𝓝 (0 : ℝ), z ∈ Ioo (-rI) rI := Ioo_mem_nhds (by linarith only [hrI_pos]) hrI_pos
    filter_upwards [hev1, hev2, hev3] with z hz1 hz2 hz3
    exact hAnti.injOn hz2 hz3 (hrA hz1)
  obtain ⟨rZ, hrZ_pos, hrZ⟩ := Metric.eventually_nhds_iff.mp hzA_AF
  -- `tau0 L < τ₁` for small `L > 0` via `critical_value_strictMonoOn`
  have hfF_ev : ∀ᶠ z in 𝓝 (0 : ℝ), π ^ 2 / 36 ≤ CtCfu.fF z := by
    have hcont : ContinuousAt CtCfu.fF 0 := (CtCfu.contDiffAt_fF).continuousAt
    have hlt : π ^ 2 / 36 < CtCfu.fF 0 := by
      rw [CtCfu.fF_zero]; have := Real.pi_pos; nlinarith
    exact hcont.eventually (Ici_mem_nhds hlt)
  obtain ⟨rF, hrF_pos, hrF⟩ := Metric.eventually_nhds_iff.mp hfF_ev
  set rB : ℝ := min (min rZ rF) (min CtCfu.rr 1e-3) with hrB_def
  have hrB_pos : 0 < rB := lt_min (lt_min hrZ_pos hrF_pos) (lt_min CtCfu.rr_pos (by norm_num))
  set τ₁ : ℝ := Real.sqrt (rB / 2) with hτ₁_def
  have hτ₁_pos : 0 < τ₁ := Real.sqrt_pos.mpr (half_pos hrB_pos)
  have hτ₁_sq : τ₁ ^ 2 = rB / 2 := Real.sq_sqrt (half_pos hrB_pos).le
  have hτ₁_rr : τ₁ ^ 2 < CtCfu.rr := by
    rw [hτ₁_sq]; exact (half_lt_self hrB_pos).trans_le (min_le_right _ _ |>.trans (min_le_left _ _))
  have hτ₁_fF : π ^ 2 / 36 ≤ CtCfu.fF (τ₁ ^ 2) := hrF (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _), hτ₁_sq]
    exact (half_lt_self hrB_pos).trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hφ₁_pos : 0 < CohnElkies.edgePhi (hankelEdgeM τ₁) τ₁ := by
    rw [CtCfu.edgePhi_crit hτ₁_pos.le hτ₁_rr]
    have : 0 < CtCfu.fF (τ₁ ^ 2) := lt_of_lt_of_le (by positivity) hτ₁_fF
    positivity
  -- Agreement along the sequence `L_n = 1 / (n + N)` → 0⁺
  set φ₁ : ℝ := CohnElkies.edgePhi (hankelEdgeM τ₁) τ₁
  have hexp_ten : Tendsto (fun L : ℝ => Real.exp L - 1) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_exp.tendsto 0).sub_const 1
  have hphi_ten : Tendsto (fun L : ℝ => (4 / 3 : ℝ) * (langerKappa * (1.0025 * L)) ^ ((3 : ℝ) / 2)) (𝓝[>] 0) (𝓝 0) := by
    have hc0 : Continuous (fun L : ℝ => (4 / 3 : ℝ) * (langerKappa * (1.0025 * L)) ^ ((3 : ℝ) / 2)) :=
      continuous_const.mul ((continuous_const.mul (continuous_const.mul continuous_id)).rpow_const fun _ => Or.inr (by norm_num))
    simpa using (hc0.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨δ1, hδ1, hd1⟩ := Metric.eventually_nhds_iff.mp (hexp_ten.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 5e-4)))
  obtain ⟨δ2, hδ2, hd2⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp (hphi_ten.eventually (Iio_mem_nhds hφ₁_pos)))
  set L₀ : ℝ := min (δ1 / 2) (δ2 / 2)
  have hL₀_pos : 0 < L₀ := lt_min (half_pos hδ1) (half_pos hδ2)
  set aOfL : ℝ → ℝ := fun L => -((2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa * ctChartG L)
  have hagree_L : ∀ L ∈ Ioo 0 L₀,
      CtCfu.Xi (aOfL L) = hankelXiUnit (aOfL L) ∧ aOfL L < 0 := by
    intro L hL
    have hLe5 : Real.exp L - 1 ≤ 5e-4 := hd1 (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hL.1]
      exact hL.2.trans_le ((min_le_left _ _).trans (half_lt_self hδ1).le))
    obtain ⟨hτpos, hτ3, -⟩ := tau0_band hL.1 hLe5
    set τ := CohnElkies.tau0 L
    have hgb := ctChartG_bounds hL.1.le hLe5
    have hg_pos : 0 < ctChartG L := ctChartG_pos hL.1 hLe5
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
    have hκpos := langerKappa_pos
    have ha_neg : aOfL L < 0 := by
      simp only [aOfL, Left.neg_neg_iff]; positivity
    -- Show `τ < τ₁` hence `τ^2 < rZ`
    have hedge := ct_langer_edge hL.1 hLe5
    have hedge_lt : CohnElkies.edgePhi (hankelEdgeM τ) τ < φ₁ := by
      have hm_eq : hankelEdgeM τ = L := hτ3 |> fun _ => by exact (tau0_band hL.1 hLe5).2.2
      rw [hm_eq]
      change CohnElkies.edgePhi L (CohnElkies.tau0 L) < φ₁
      rw [hedge]
      have h1 : langerKappa * ctChartG L ≤ langerKappa * (1.0025 * L) :=
        mul_le_mul_of_nonneg_left hgb.2.1 hκpos.le
      have h2 : (langerKappa * ctChartG L) ^ ((3 : ℝ) / 2) ≤ (langerKappa * (1.0025 * L)) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      have h3 : (4 / 3 : ℝ) * (langerKappa * ctChartG L) ^ ((3 : ℝ) / 2) ≤
          (4 / 3 : ℝ) * (langerKappa * (1.0025 * L)) ^ ((3 : ℝ) / 2) := by linarith only [h2]
      refine h3.trans_lt (hd2 ?_ hL.1)
      rw [Real.dist_eq, sub_zero, abs_of_pos hL.1]
      exact hL.2.trans_le ((min_le_right _ _).trans (half_lt_self hδ2).le)
    have hτ_lt : τ < τ₁ := by
      by_contra hge
      push Not at hge
      have hle := CtCfu.critical_value_strictMonoOn.le_iff_le (show τ₁ ∈ Ici 0 from hτ₁_pos.le)
        (show τ ∈ Ici 0 from hτpos.le) |>.2 hge
      exact absurd hedge_lt (not_lt.2 hle)
    have hτ2_lt : τ ^ 2 < rZ := by
      have hsq : τ ^ 2 < τ₁ ^ 2 := pow_lt_pow_left₀ hτ_lt hτpos.le (by norm_num)
      rw [hτ₁_sq] at hsq
      exact hsq.trans_le ((half_le_self hrB_pos.le).trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hzA_eq : CtCfu.zA (aOfL L) = τ ^ 2 := by
      have hAF := ct_AF_tau0_sq hL.1 hLe5
      change CtCfu.AF (CohnElkies.tau0 L ^ 2) = aOfL L at hAF
      rw [← hAF]
      exact hrZ (by rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]; exact hτ2_lt)
    have hNF_eq : CtCfu.NF (CtCfu.zA (aOfL L)) = L := by
      rw [hzA_eq]
      exact ct_NF_tau0_sq hL.1 hLe5
    have hXi_val : CtCfu.Xi (aOfL L) = Real.exp L / π ^ 2 := by
      unfold CtCfu.Xi; rw [hNF_eq]
    -- Compute `hankelXiUnit (aOfL L) = Real.exp L / π ^ 2`
    set w : ℝ := Real.exp L - 1
    have hw0 : 0 ≤ w := by linarith only [Real.one_le_exp hL.1.le]
    have hwn : ‖(w : ℂ)‖ ≤ 5e-4 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]; exact hLe5
    have hw_ball : (w : ℂ) ∈ closedBall (0 : ℂ) 1e-3 := by
      rw [mem_closedBall_zero_iff]; linarith only [hwn]
    have hcY_conj := chartY_conj langerEta_etaC (hw_ball |> mem_closedBall_zero_iff.1)
    rw [Complex.conj_ofReal] at hcY_conj
    have hcY_im : (chartY etaC (w : ℂ)).im = 0 := by
      have h1 := congrArg Complex.im hcY_conj
      simp at h1; linarith only [h1]
    have hcY_re : (chartY etaC (w : ℂ)).re = -ctChartG L := by
      unfold ctChartG ctYR; ring
    set y : ℂ := ((aOfL L / ((2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa) : ℝ) : ℂ)
    have hy_eq : chartY etaC (w : ℂ) = y := by
      refine Complex.ext ?_ (by rw [hcY_im]; simp only [y, Complex.ofReal_im])
      simp only [y, Complex.ofReal_re, hcY_re, aOfL]
      field_simp
    have hy_mem : ∃ w' ∈ ball (0 : ℂ) 1e-3, chartY etaC w' = y :=
      ⟨(w : ℂ), mem_ball_zero_iff.2 (by linarith only [hwn]), hy_eq⟩
    obtain ⟨hw'_ball, hw'_eq⟩ := chartYinv_spec etaC hy_mem
    have hw_inv : chartYinv etaC y = (w : ℂ) :=
      (injOn_chartY langerEta_etaC) (ball_subset_closedBall hw'_ball) hw_ball (hw'_eq.trans hy_eq.symm)
    have hUnit_val : hankelXiUnit (aOfL L) = Real.exp L / π ^ 2 := by
      unfold hankelXiUnit
      rw [show (((aOfL L / ((2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa) : ℝ)) : ℂ) = y from rfl, hw_inv,
        Complex.ofReal_re]
      simp only [w]; ring
    exact ⟨hXi_val.trans hUnit_val.symm, ha_neg⟩
  -- Analyticity on an open ball `Ioo (-r₀) r₀` and identity theorem
  obtain ⟨rX, hrX_pos, hrX⟩ := analyticOnNhd_ball_of_analyticAt analyticAt_CtCfu_Xi
  obtain ⟨rU, hrU_pos, hrU⟩ := analyticOnNhd_ball_of_analyticAt analyticAt_hankelXiUnit
  set r₀ : ℝ := min (min rX rU) rA with hr₀_def
  have hr₀_pos : 0 < r₀ := lt_min (lt_min hrX_pos hrU_pos) hrA_pos
  have hAnX : AnalyticOnNhd ℝ CtCfu.Xi (ball 0 r₀) :=
    hrX.mono (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)))
  have hAnU : AnalyticOnNhd ℝ hankelXiUnit (ball 0 r₀) :=
    hrU.mono (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)))
  have hfreq : ∃ᶠ a in 𝓝[≠] (0 : ℝ), CtCfu.Xi a = hankelXiUnit a := by
    rw [frequently_nhdsWithin_iff, Filter.frequently_iff]
    intro U hU
    obtain ⟨ε', hε', hU_sub⟩ := Metric.mem_nhds_iff.mp hU
    have hten : Tendsto aOfL (𝓝[>] 0) (𝓝 0) := by
      have ha_eq : ∀ᶠ L in 𝓝[>] 0, |aOfL L| ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa * (1.0025 * L) := by
        filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT (show (0 : ℝ) < min (δ1 / 2) L₀ by positivity)] with L hL0 hL1
        have hLe5 : Real.exp L - 1 ≤ 5e-4 := hd1 (by
          rw [Real.dist_eq, sub_zero, abs_of_pos hL0]
          exact hL1.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ1)))
        have hgb := ctChartG_bounds hL0.le hLe5
        have hg_pos : 0 ≤ ctChartG L := (ctChartG_pos hL0 hLe5).le
        have h2κ : 0 ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa := by have := langerKappa_pos; positivity
        rw [abs_neg, abs_of_nonneg (mul_nonneg h2κ hg_pos)]
        exact mul_le_mul_of_nonneg_left hgb.2.1 h2κ
      have hten0 : Tendsto (fun L : ℝ => (2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa * (1.0025 * L)) (𝓝[>] 0) (𝓝 0) := by
        have hc0 : Continuous (fun L : ℝ => (2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa * (1.0025 * L)) := by fun_prop
        simpa using (hc0.tendsto 0).mono_left nhdsWithin_le_nhds
      exact (tendsto_zero_iff_abs_tendsto_zero _).2
        (squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ha_eq hten0)
    obtain ⟨δ3, hδ3, hd3⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp (hten.eventually (ball_mem_nhds 0 hε')))
    set L := min (L₀ / 2) (δ3 / 2)
    have hL_pos : 0 < L := lt_min (half_pos hL₀_pos) (half_pos hδ3)
    have hL_mem : L ∈ Ioo 0 L₀ := ⟨hL_pos, (min_le_left _ _).trans_lt (half_lt_self hL₀_pos)⟩
    obtain ⟨heq, hneg⟩ := hagree_L L hL_mem
    exact ⟨aOfL L, hU_sub (hd3 (by rw [Real.dist_eq, sub_zero, abs_of_pos hL_pos]; exact (min_le_right _ _).trans_lt (half_lt_self hδ3)) hL_pos), heq, hneg.ne⟩
  have heqOn : EqOn CtCfu.Xi hankelXiUnit (ball 0 r₀) :=
    hAnX.eqOn_of_preconnected_of_frequently_eq hAnU (convex_ball _ _).isPreconnected (mem_ball_self hr₀_pos) hfreq
  refine ⟨r₀, hr₀_pos, fun a ha => ?_⟩
  have hmem : a ∈ ball (0 : ℝ) r₀ := by simpa [Real.dist_eq] using ha
  have hXi : CtCfu.Xi a = hankelXiUnit a := heqOn hmem
  have hAF : CtCfu.AF (CtCfu.zA a) = a := hrA (by simpa [Real.dist_eq] using ha.trans_le (min_le_right _ _))
  have hNF : CtCfu.NF (CtCfu.zA a) = Real.log (π ^ 2 * hankelXiUnit a) := by
    have h1 : Real.exp (CtCfu.NF (CtCfu.zA a)) = π ^ 2 * CtCfu.Xi a := by
      unfold CtCfu.Xi
      have hpi : (π ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
      field_simp
    rw [hXi] at h1
    rw [← h1, Real.log_exp]
  exact ⟨hXi, hNF, hAF⟩

/-! ### Part 2: Uniform `O(1)` bound on `Ai'(U) Bi(U) + Ai(U) Bi'(U)` on `ℝ` -/

/-- `|Ai'(U) Bi(U) + Ai(U) Bi'(U)|` is uniformly bounded over all `U : ℝ`. -/
lemma airyAiBiDeriv_abs_le :
    ∃ M : ℝ, 0 < M ∧ ∀ U : ℝ, |airyAi' U * airyBi U + airyAi U * airyBiDeriv U| ≤ M := by
  let G : ℝ → ℝ := fun U => |airyAi' U * airyBi U + airyAi U * airyBiDeriv U|
  have hcont : Continuous G := by
    refine continuous_abs.comp ?_
    have hBi : Continuous airyBi := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBi x).continuousAt
    have hBi' : Continuous airyBiDeriv := continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBiDeriv x).continuousAt
    exact ((continuous_airyAi'.mul hBi).add (continuous_airyAi.mul hBi'))
  obtain ⟨U₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Nonempty (Icc (-1 : ℝ) 1)) hcont.continuousOn
  set M₀ := max (G U₀) 10 with hM₀
  refine ⟨M₀, by positivity, fun U => ?_⟩
  rcases le_or_gt U (-1) with hU_neg | hU_gt1
  · -- Case `U ≤ -1`: use `CtAiryHplus.calD_bound`
    have hne : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hnorm : 1 ≤ ‖(U : ℂ)‖ := by simpa [Real.norm_eq_abs] using (show 1 ≤ |U| by rw [abs_of_neg (by linarith)]; linarith)
    have hcb := CtAiryHplus.calD_bound (u := (U : ℂ)) (by simp) hne hnorm
    have hexp : Real.exp (4 / 3 * ((U : ℂ) ^ (3 / 2 : ℂ)).re) = 1 := by
      have h1 : airyUpE (U : ℂ) = Complex.exp ((4 / 3 : ℂ) * (U : ℂ) ^ (3 / 2 : ℂ)) := by
        unfold airyUpE
        rw [airyUp_pow_eq (by simp) hne]
      have h2 : airyUpE (U : ℂ) = Complex.exp (((-(4 / 3 * (-U) ^ (3 / 2 : ℝ)) : ℝ) : ℂ) * I) := by
        rw [show U = -(-U) by ring, airyUpE_ofReal_neg (by linarith only [hU_neg])]
        congr 1; push_cast; ring
      have hn : ‖Complex.exp ((4 / 3 : ℂ) * (U : ℂ) ^ (3 / 2 : ℂ))‖ = 1 := by
        rw [← h1, h2, Complex.norm_exp_ofReal_mul_I]
      rw [Complex.norm_exp] at hn
      simpa using hn
    have hD11 : ‖CtAiryHplus.calD (U : ℂ)‖ ≤ 11 := by
      rw [hexp, mul_one] at hcb
      have hrp : ‖(U : ℂ)‖ ^ (-(3 / 2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hnorm (by norm_num)
      nlinarith
    have him := CtAiryHplus.calD_im_real U
    simp only [show U < 0 by linarith, ↓reduceIte] at him
    have him_abs : |(CtAiryHplus.calD (U : ℂ)).im| ≤ 11 := (Complex.abs_im_le_norm _).trans hD11
    have hpi_prod : |(-π) * (airyAi' U * airyBi U + airyAi U * airyBiDeriv U)| ≤ 12 := by
      have hsin := Real.abs_sin_le_one (4 / 3 * (-U) ^ (3 / 2 : ℝ))
      have hdiff : (-π) * (airyAi' U * airyBi U + airyAi U * airyBiDeriv U) =
          (CtAiryHplus.calD (U : ℂ)).im - Real.sin (4 / 3 * (-U) ^ (3 / 2 : ℝ)) := by linarith [him]
      rw [hdiff]
      exact (abs_sub _ _).trans (by linarith [him_abs, hsin])
    rw [abs_mul, abs_neg, abs_of_pos Real.pi_pos] at hpi_prod
    have hG_le : |airyAi' U * airyBi U + airyAi U * airyBiDeriv U| ≤ 12 / π :=
      (le_div_iff₀ Real.pi_pos).2 (by linarith)
    have h12 : 12 / π ≤ 10 := by
      rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
    exact hG_le.trans (h12.trans (le_max_right _ _))
  · rcases le_or_gt U 1 with hU_mid | hU_pos
    · exact (hmax ⟨hU_gt1.le, hU_mid⟩).trans (le_max_left _ _)
    · -- Case `1 < U`: combine `airyAi_abs_le`/`airyAi'_abs_le` with `airyBi_pos_asymptotic`/`airyBiDeriv_pos_asymptotic`
      have hU0 : 0 < U := by linarith
      set E : ℝ := Real.exp (2 / 3 * U ^ (3 / 2 : ℝ))
      have hE_pos : 0 < E := Real.exp_pos _
      have hEm_eq : Real.exp (-(2 / 3) * U ^ (3 / 2 : ℝ)) = E⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      have hAi := airyAi_abs_le hU0
      have hAi' := airyAi'_abs_le hU0
      have hBi := airyBi_pos_asymptotic hU0
      have hBi' := airyBiDeriv_pos_asymptotic hU0
      rw [hEm_eq] at hAi hAi'
      have hU14_inv : U ^ (-(1 / 4) : ℝ) = (U ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hU0.le _
      have hU12_le : U ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hU_pos.le (by norm_num)
      have hU14_le : U ^ (-(1 / 4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hU_pos.le (by norm_num)
      have hU74_le : U ^ (-(7 / 4) : ℝ) ≤ U ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hU_pos.le (by norm_num)
      have hU54_le : U ^ (-(5 / 4) : ℝ) ≤ U ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hU_pos.le (by norm_num)
      have hpi : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
      have hU14_pos : 0 < U ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hU0 _
      have hUm14_pos : 0 < U ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hU0 _
      -- `|Bi U| ≤ (1/√π + 4/5) U^{-1/4} E`
      have hBi_bd : |airyBi U| ≤ (1 / √π + 4 / 5) * U ^ (-(1 / 4) : ℝ) * E := by
        have h1 := abs_sub_abs_le_abs_sub (airyBi U) (1 / √π * U ^ (-(1 / 4) : ℝ) * E)
        have h2 : |1 / √π * U ^ (-(1 / 4) : ℝ) * E| = 1 / √π * U ^ (-(1 / 4) : ℝ) * E :=
          abs_of_pos (by positivity)
        have h3 : |airyBi U| ≤ 1 / √π * U ^ (-(1 / 4) : ℝ) * E + 4 / 5 * U ^ (-(7 / 4) : ℝ) * E := by
          linarith [hBi]
        have h4 : 4 / 5 * U ^ (-(7 / 4) : ℝ) * E ≤ 4 / 5 * U ^ (-(1 / 4) : ℝ) * E := by
          gcongr
        linarith
      -- `|Bi' U| ≤ (1/√π + 7/4) U^{1/4} E`
      have hBi'_bd : |airyBiDeriv U| ≤ (1 / √π + 7 / 4) * U ^ (1 / 4 : ℝ) * E := by
        have h1 := abs_sub_abs_le_abs_sub (airyBiDeriv U) (1 / √π * U ^ (1 / 4 : ℝ) * E)
        have h2 : |1 / √π * U ^ (1 / 4 : ℝ) * E| = 1 / √π * U ^ (1 / 4 : ℝ) * E :=
          abs_of_pos (by positivity)
        have h3 : |airyBiDeriv U| ≤ 1 / √π * U ^ (1 / 4 : ℝ) * E + 7 / 4 * U ^ (-(5 / 4) : ℝ) * E := by
          linarith [hBi']
        have h4 : 7 / 4 * U ^ (-(5 / 4) : ℝ) * E ≤ 7 / 4 * U ^ (1 / 4 : ℝ) * E := by
          gcongr
        linarith
      -- `|Ai' U| ≤ (1/(2π)) (√π + 1) U^{1/4} E⁻¹`
      have hU12_le_U14 : U ^ (-(1 / 2) : ℝ) ≤ U ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hU_pos.le (by norm_num)
      have hAi'_bd : |airyAi' U| ≤ (1 / (2 * π)) * (√π + 1) * U ^ (1 / 4 : ℝ) * E⁻¹ := by
        have : √π * U ^ (1 / 4 : ℝ) + U ^ (-(1 / 2) : ℝ) ≤ (√π + 1) * U ^ (1 / 4 : ℝ) := by linarith
        calc |airyAi' U| ≤ 1 / (2 * π) * (√π * U ^ (1 / 4 : ℝ) + U ^ (-(1 / 2) : ℝ)) * E⁻¹ := hAi'
          _ ≤ 1 / (2 * π) * ((√π + 1) * U ^ (1 / 4 : ℝ)) * E⁻¹ := by gcongr
          _ = _ := by ring
      have hprod1 : |airyAi' U * airyBi U| ≤ (1 / (2 * π)) * (√π + 1) * (1 / √π + 4 / 5) := by
        rw [abs_mul]
        calc |airyAi' U| * |airyBi U|
            ≤ ((1 / (2 * π)) * (√π + 1) * U ^ (1 / 4 : ℝ) * E⁻¹) *
              ((1 / √π + 4 / 5) * U ^ (-(1 / 4) : ℝ) * E) :=
              mul_le_mul hAi'_bd hBi_bd (abs_nonneg _) (by positivity)
          _ = (1 / (2 * π)) * (√π + 1) * (1 / √π + 4 / 5) * ((U ^ (1 / 4 : ℝ) * U ^ (-(1 / 4) : ℝ)) * (E⁻¹ * E)) := by ring
          _ = (1 / (2 * π)) * (√π + 1) * (1 / √π + 4 / 5) := by
              rw [hU14_inv, mul_inv_cancel₀ hU14_pos.ne', inv_mul_cancel₀ hE_pos.ne', mul_one, mul_one]
      have hprod2 : |airyAi U * airyBiDeriv U| ≤ 1 / (2 * √π) * (1 / √π + 7 / 4) := by
        rw [abs_mul]
        calc |airyAi U| * |airyBiDeriv U|
            ≤ (1 / (2 * √π) * U ^ (-(1 / 4) : ℝ) * E⁻¹) *
              ((1 / √π + 7 / 4) * U ^ (1 / 4 : ℝ) * E) :=
              mul_le_mul hAi hBi'_bd (abs_nonneg _) (by positivity)
          _ = 1 / (2 * √π) * (1 / √π + 7 / 4) * ((U ^ (1 / 4 : ℝ) * U ^ (-(1 / 4) : ℝ)) * (E⁻¹ * E)) := by ring
          _ = 1 / (2 * √π) * (1 / √π + 7 / 4) := by
              rw [hU14_inv, mul_inv_cancel₀ hU14_pos.ne', inv_mul_cancel₀ hE_pos.ne', mul_one, mul_one]
      have hpi_gt : (1 : ℝ) < √π := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by linarith [Real.pi_gt_three])
      have hb1 : (1 / (2 * π)) * (√π + 1) * (1 / √π + 4 / 5) ≤ 2 := by
        have hsqpi : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
        have : 1 / √π ≤ 1 := div_le_one_of_le₀ hpi_gt.le (by positivity)
        have hsub : √π + 1 ≤ 2 * √π := by linarith
        have hdiv : √π / π = 1 / √π := by
          rw [div_eq_div_iff Real.pi_ne_zero (by positivity), one_mul, hsqpi]
        calc (1 / (2 * π)) * (√π + 1) * (1 / √π + 4 / 5)
            ≤ (1 / (2 * π)) * (2 * √π) * (1 + 4 / 5) := by gcongr
          _ = (√π / π) * (9 / 5) := by ring
          _ = (1 / √π) * (9 / 5) := by rw [hdiv]
          _ ≤ 1 * (9 / 5) := by gcongr
          _ ≤ 2 := by norm_num
      have hb2 : 1 / (2 * √π) * (1 / √π + 7 / 4) ≤ 2 := by
        have : 1 / √π ≤ 1 := div_le_one_of_le₀ hpi_gt.le (by positivity)
        calc 1 / (2 * √π) * (1 / √π + 7 / 4) ≤ (1 / 2) * (1 + 7 / 4) := by gcongr; linarith
          _ ≤ 2 := by norm_num
      have htot : |airyAi' U * airyBi U + airyAi U * airyBiDeriv U| ≤ 4 :=
        (abs_add_le _ _).trans (by linarith)
      exact htot.trans (by linarith [le_max_right (G U₀) 10])

/-! ### Part 3: Inverse relation `ctPhiR ε c u + ctLam c * psiOf th (ctMu c * ctPhiR ε c u) = u` on `[-R, R]` -/

lemma psi_eq_psiOf_of_theta {ε : ℝ} {th : ℝ → ℝ}
    (hrel : ∀ᶠ τ in 𝓝 (0 : ℝ), CtOuter.outerTheta ε τ = τ * th (τ ^ 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ Ioo (-ρ) 0, ctPsi ε a = CtCfu.psiOf th a := by
  have htau : Tendsto CtCfu.tau0 (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto CtCfu.tau0 (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp CtCfu.tendsto_zA
    rwa [Real.sqrt_zero] at h
  have hev : ∀ᶠ a in 𝓝 (0 : ℝ), (CtCfu.zA a ∈ Ioo (-CtCfu.rr) CtCfu.rr ∧ 0 < CtCfu.fF (CtCfu.zA a) ∧
      CtCfu.AFp (CtCfu.zA a) ≠ 0) ∧ CtCfu.AF (CtCfu.zA a) = a :=
    CtCfu.zA_good.and CtCfu.AF_zA_eventually
  have hev2 : ∀ᶠ a in 𝓝 (0 : ℝ), CtOuter.outerTheta ε (CtCfu.tau0 a) = CtCfu.tau0 a * th (CtCfu.tau0 a ^ 2) :=
    htau.eventually hrel
  obtain ⟨ρ, hρ, h3⟩ := Metric.eventually_nhds_iff.mp (hev.and hev2)
  refine ⟨ρ, hρ, fun a ha => ?_⟩
  have ha3 : dist a 0 < ρ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg ha.2]; linarith [ha.1]
  obtain ⟨⟨hgood, hAF⟩, hth_eq⟩ := h3 ha3
  have hz_pos := CtCfu.zA_pos ha.2 hAF
  have hτ_sq : CtCfu.tau0 a ^ 2 = CtCfu.zA a := Real.sq_sqrt hz_pos.le
  obtain ⟨hτ_pos, -, hphi_eq, hsqrt_eq⟩ := CtCfu.tau0_props ha.2 hAF hgood
  have hspec : 0 < ctTau0 a ∧
      CohnElkies.edgePhi (hankelEdgeM (ctTau0 a)) (ctTau0 a) = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) :=
    Classical.epsilon_spec (p := fun τ : ℝ => 0 < τ ∧
      CohnElkies.edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2)) ⟨CtCfu.tau0 a, hτ_pos, hphi_eq⟩
  have hctTau : ctTau0 a = CtCfu.tau0 a :=
    CtCfu.critical_value_strictMonoOn.injOn hspec.1.le hτ_pos.le (hspec.2.trans hphi_eq.symm)
  unfold ctPsi CtCfu.psiOf
  rw [hctTau, hth_eq, hsqrt_eq, hτ_sq]
  have hne : CtCfu.tau0 a ≠ 0 := hτ_pos.ne'
  field_simp

/-- Analytic inverse identity on ALL of `[-R, R]`: for `U_fn x := x + ctLam c * psiOf th (ctMu c * x)`,
`U_fn (ctPhiR ε c u) = u` whenever `u ∈ Icc (-R) R`, via holomorphic continuation on `ball 0 (R + 1)`. -/
lemma ctPhiR_uhatAn_inv {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {th : ℝ → ℝ} (hth : AnalyticAt ℝ th 0)
    (hrel : ∀ᶠ τ in 𝓝 (0 : ℝ), CtOuter.outerTheta ε τ = τ * th (τ ^ 2)) :
    ∃ γ_u > (0 : ℝ), ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ_u → ∃ c_u : ℝ, 3e6 ≤ c_u ∧
      ∀ c : ℝ, c_u ≤ c → ∀ R : ℝ, c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
        ∀ u ∈ Icc (-R) R, ctPhiR ε c u + ctLam c * CtCfu.psiOf th (ctMu c * ctPhiR ε c u) = u := by
  obtain ⟨rΨ, Ψ, hrΨ_pos, hΨ_diff, _, hΨ_real⟩ := exists_complex_extension (CtCfu.analyticAt_psiOf hth)
  obtain ⟨ρ_p, hρ_p_pos, hpsi_eq⟩ := psi_eq_psiOf_of_theta hrel
  obtain ⟨ρW, MW, hρW_pos, hMW_nn, hWin⟩ := ctPsi_window hε
  obtain ⟨C, c_ch, hC_nn, hCh⟩ := ctChartComplex_ctChartC1
  set rA : ℝ := min rΨ (min ρ_p ρW) with hrA_def
  have hrA_pos : 0 < rA := lt_min hrΨ_pos (lt_min hρ_p_pos hρW_pos)
  -- Need `8 γ_u^2 ≤ rA / 2` and `γ_u ≤ ctChartC1 / 2`
  set γ_u : ℝ := min (ctChartC1 / 2) (Real.sqrt (rA / 16)) with hγ_u_def
  have hγ_u_pos : 0 < γ_u := lt_min (half_pos ctChartC1_pos) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨γ_u, hγ_u_pos, fun c₁ hc₁_pos hc₁_le => ?_⟩
  have hc₁_lt_C1 : c₁ < ctChartC1 := hc₁_le.trans_lt ((min_le_left _ _).trans_lt (half_lt_self ctChartC1_pos))
  have h8c₁ : 8 * c₁ ^ 2 ≤ rA / 2 := by
    have hs : c₁ ≤ Real.sqrt (rA / 16) := hc₁_le.trans (min_le_right _ _)
    have hsq : c₁ ^ 2 ≤ Real.sqrt (rA / 16) ^ 2 := sq_le_sq' (by linarith) hs
    rw [Real.sq_sqrt (by positivity)] at hsq
    linarith
  -- Choose `c_u` large enough (clean integer powers avoid `rpow` headaches)
  set S_ch : ℝ := max (C + 1) (2 * MW + 1) with hS_ch_def
  set c_u : ℝ := max (max 3e6 c_ch)
    (max (max ((2 * MW + 1) ^ 3) ((2 * C + 2) ^ 3))
      (max (max ((4 / c₁ ^ 2 + 2) ^ 2) ((4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA + 2) ^ 2))
           ((2 * (C + 1) + 2) ^ 3))) with hc_u_def
  have hc_u_ge : 3e6 ≤ c_u := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨c_u, hc_u_ge, fun c hc R hR_lb hR_ub u hu => ?_⟩
  have hc0 : 0 < c := by linarith
  have hc_ch' : c_ch ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hPhiDom : ∀ x : ℝ, -ctRmax ctChartC1 c ≤ x → x ≤ 0 → x ∈ ctPhiDom ε c :=
    (hCh ε hε c hc_ch').2.1
  have hPhiIm : ∀ x : ℝ, |x| ≤ ctRmax ctChartC1 c → (ctPhiC ctChartC1 ε c (x : ℂ)).im = 0 :=
    (hCh ε hε c hc_ch').2.2.1
  have hPhiBd := (hCh ε hε c hc_ch').2.2.2
  -- Verify `R + 1 ≤ ctRmax ctChartC1 c` and `1 < R`
  have hC13 : C * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 := by
    have h1 : (2 * C + 2) ^ 3 ≤ c :=
      (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
    have h2 : 2 * C + 2 ≤ c ^ ((1 : ℝ) / 3) := by
      have hpos : 0 ≤ 2 * C + 2 := by linarith only [hC_nn]
      have hpow3 : (2 * C + 2) ^ (3 : ℕ) = (2 * C + 2) ^ (3 : ℝ) := by norm_cast
      calc 2 * C + 2 = ((2 * C + 2) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_mul hpos]; norm_num
        _ ≤ c ^ ((1 : ℝ) / 3) := by rw [← hpow3]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [Real.rpow_neg hc0.le, mul_inv_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
    nlinarith only [h2, hC_nn, Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3)]
  have Hchart : CtRealChartHyp ε c C :=
    ⟨hCh ε hε c hc_ch', hC_nn, by linarith only [hc_u_ge, hc], hC13⟩
  obtain ⟨⟨ρ0, hρ0, hFdiff⟩, hFext⟩ := ctPhiC_spec Hchart.body.1
  -- `c^(2/3) ≥ c^(1/2)` and `4 / c₁^2 ≤ c^(2/3)`
  have hc12_le_c23 : c ^ ((1 : ℝ) / 2) ≤ c ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc_u_ge, hc]) (by norm_num)
  have h4c₁ : 4 / c₁ ^ 2 + 2 ≤ c ^ ((2 : ℝ) / 3) := by
    have h1 : (4 / c₁ ^ 2 + 2) ^ 2 ≤ c :=
      (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
    have h2 : 4 / c₁ ^ 2 + 2 ≤ c ^ ((1 : ℝ) / 2) := by
      calc 4 / c₁ ^ 2 + 2 = √((4 / c₁ ^ 2 + 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = ((4 / c₁ ^ 2 + 2) ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
        _ ≤ c ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    exact h2.trans hc12_le_c23
  have hR_gt_2 : 2 < R := by
    have h4a : 4 ≤ c₁ ^ 2 * c ^ ((2 : ℝ) / 3) := by
      have h4b : 4 / c₁ ^ 2 ≤ c ^ ((2 : ℝ) / 3) := by linarith only [h4c₁]
      rwa [div_le_iff₀ (sq_pos_of_pos hc₁_pos), mul_comm] at h4b
    linarith only [hR_lb, h4a]
  have hR_add_lt_Rm : R + 1 ≤ ctRmax ctChartC1 c := by
    have hdiff : 1 ≤ (ctChartC1 ^ 2 - c₁ ^ 2) * 4 * c ^ ((2 : ℝ) / 3) := by
      have hc1_sq : c₁ ^ 2 ≤ ctChartC1 ^ 2 / 4 := by
        have h1 : c₁ ≤ ctChartC1 / 2 := hc₁_le.trans (min_le_left _ _)
        nlinarith only [hc₁_pos, h1, ctChartC1_pos]
      have hpos_C1 : 0 < ctChartC1 ^ 2 := sq_pos_of_pos ctChartC1_pos
      have hc4 : 4 / c₁ ^ 2 ≤ c ^ ((2 : ℝ) / 3) := by linarith only [h4c₁]
      have hc_big : 1 ≤ 3 * c₁ ^ 2 * c ^ ((2 : ℝ) / 3) := by
        have h4a : 4 ≤ c₁ ^ 2 * c ^ ((2 : ℝ) / 3) := by
          rwa [div_le_iff₀ (sq_pos_of_pos hc₁_pos), mul_comm] at hc4
        linarith only [h4a]
      nlinarith only [hc1_sq, hc_big, sq_nonneg c₁, Real.rpow_pos_of_pos hc0 ((2 : ℝ) / 3)]
    unfold ctRmax
    nlinarith only [hR_ub, hdiff]
  -- Bound `ctMu c * ‖ctPhiC ctChartC1 ε c z‖ < rA` on `ball 0 (R + 1)`
  have hc23_ge : 4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA + 2 ≤ c ^ ((2 : ℝ) / 3) := by
    have h1 : (4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA + 2) ^ 2 ≤ c :=
      (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
    have h2 : 4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA + 2 ≤ c ^ ((1 : ℝ) / 2) := by
      calc 4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA + 2
          = √((4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA + 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = ((4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA + 2) ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
        _ ≤ c ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    exact h2.trans hc12_le_c23
  have hmap : ∀ z ∈ ball (0 : ℂ) (R + 1), ‖(ctMu c : ℂ) * ctPhiC ctChartC1 ε c z‖ < rA := by
    intro z hz
    have hzn : ‖z‖ ≤ R + 1 := (mem_ball_zero_iff.1 hz).le
    have hzm : ‖z‖ ≤ ctRmax ctChartC1 c := hzn.trans hR_add_lt_Rm
    have hbd := (hPhiBd z hzm).1
    have hcφ : ‖ctPhiC ctChartC1 ε c z‖ ≤ R + 2 := by
      calc ‖ctPhiC ctChartC1 ε c z‖ = ‖z + (ctPhiC ctChartC1 ε c z - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖ctPhiC ctChartC1 ε c z - z‖ := norm_add_le _ _
        _ ≤ (R + 1) + C * c ^ (-(1 / 3 : ℝ)) := add_le_add hzn hbd
        _ ≤ R + 2 := by linarith only [hC13]
    have hμ0 := ctMu_pos hc0
    have hμ_bound : ctMu c * (R + 2) < rA := by
      have hμR : ctMu c * R ≤ 8 * c₁ ^ 2 := by
        calc ctMu c * R ≤ ctMu c * (4 * c₁ ^ 2 * c ^ ((2 : ℝ) / 3)) :=
              mul_le_mul_of_nonneg_left hR_ub hμ0.le
          _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 * (c ^ (-(2 / 3) : ℝ) * c ^ ((2 : ℝ) / 3)) := by
              unfold ctMu; ring
          _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 := by
              rw [← Real.rpow_add hc0]; simp
          _ ≤ 8 * c₁ ^ 2 := by
              have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
                calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                  _ = 2 := Real.rpow_one 2
              nlinarith only [h2, sq_nonneg c₁]
      have hμ2 : ctMu c * 2 < rA / 2 := by
        unfold ctMu
        rw [Real.rpow_neg hc0.le]
        have hlt : 2 * (2 : ℝ) ^ ((2 : ℝ) / 3) / (rA / 2) < c ^ ((2 : ℝ) / 3) := by
          have h1 : 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) / rA ≤ 4 * (C + 1) * 2 ^ ((2 : ℝ) / 3) / rA := by
            gcongr; linarith only [hC_nn]
          have h2 : 2 * (2 : ℝ) ^ ((2 : ℝ) / 3) / (rA / 2) = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) / rA := by ring
          linarith only [h1, h2, hc23_ge]
        rw [div_lt_iff₀ (half_pos hrA_pos)] at hlt
        calc (2 : ℝ) ^ ((2 : ℝ) / 3) * (c ^ ((2 : ℝ) / 3))⁻¹ * 2
            = (2 * (2 : ℝ) ^ ((2 : ℝ) / 3)) / c ^ ((2 : ℝ) / 3) := by ring
          _ < rA / 2 := (div_lt_iff₀ (Real.rpow_pos_of_pos hc0 _)).2 (by linarith only [hlt])
      linarith only [hμR, h8c₁, hμ2]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
    exact (mul_le_mul_of_nonneg_left hcφ hμ0.le).trans_lt hμ_bound
  -- Define `G z := ctPhiC ctChartC1 ε c z + (ctLam c : ℂ) * Ψ ((ctMu c : ℂ) * ctPhiC ctChartC1 ε c z)`
  let G : ℂ → ℂ := fun z =>
    ctPhiC ctChartC1 ε c z + (ctLam c : ℂ) * Ψ ((ctMu c : ℂ) * ctPhiC ctChartC1 ε c z)
  have hG_an : AnalyticOnNhd ℂ G (ball 0 (R + 1)) := by
    have hball_sub : ball (0 : ℂ) (R + 1) ⊆ ball 0 ρ0 :=
      ball_subset_ball (hR_add_lt_Rm.trans hρ0.le)
    have hΦ_diff : DifferentiableOn ℂ (ctPhiC ctChartC1 ε c) (ball 0 (R + 1)) :=
      hFdiff.mono hball_sub
    have hΨ_sub : ∀ z ∈ ball (0 : ℂ) (R + 1), (ctMu c : ℂ) * ctPhiC ctChartC1 ε c z ∈ ball (0 : ℂ) rΨ :=
      fun z hz => mem_ball_zero_iff.2 ((hmap z hz).trans_le (min_le_left _ _))
    have hG_diff : DifferentiableOn ℂ G (ball 0 (R + 1)) := fun z hz => by
      have h2 : DifferentiableAt ℂ (ctPhiC ctChartC1 ε c) z :=
        (hΦ_diff z hz).differentiableAt (isOpen_ball.mem_nhds hz)
      have h3 : DifferentiableAt ℂ Ψ ((ctMu c : ℂ) * ctPhiC ctChartC1 ε c z) :=
        (hΨ_diff _ (hΨ_sub z hz)).differentiableAt (isOpen_ball.mem_nhds (hΨ_sub z hz))
      exact (h2.add ((h3.comp z (h2.const_mul _)).const_mul _)).differentiableWithinAt
    exact hG_diff.analyticOnNhd isOpen_ball
  have hlamMW : ctLam c * MW ≤ 1 / 2 := by
    unfold ctLam
    have h2 : (2 : ℝ) ^ (-(2 / 3) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have h1 : (2 * MW + 1) ^ 3 ≤ c :=
      (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
    have hpow : 2 * MW + 1 ≤ c ^ ((1 : ℝ) / 3) := by
      have hpos : 0 ≤ 2 * MW + 1 := by linarith only [hMW_nn]
      have hpow3 : (2 * MW + 1) ^ (3 : ℕ) = (2 * MW + 1) ^ (3 : ℝ) := by norm_cast
      calc 2 * MW + 1 = ((2 * MW + 1) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_mul hpos]; norm_num
        _ ≤ c ^ ((1 : ℝ) / 3) := by rw [← hpow3]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [Real.rpow_neg hc0.le, mul_assoc, inv_mul_eq_div]
    have hle : MW / c ^ ((1 : ℝ) / 3) ≤ 1 / 2 := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]; linarith only [hpow]
    nlinarith only [h2, hle, show 0 ≤ MW / c ^ ((1 : ℝ) / 3) by positivity]
  have hx₀_dom : ∀ x ∈ Ioo (-3 * R / 4) (-R / 4),
      x ∈ ctPhiDom ε c ∧ x < 0 ∧ |x| ≤ ctRmax ctChartC1 c ∧
        ctMu c * |x| < rA ∧ |(ctUhat ε c x)| ≤ 3 * R / 4 + 1 / 2 := by
    intro x hx
    have hx_neg : x < 0 := by linarith only [hx.2, hR_gt_2]
    have hx_abs : |x| ≤ 3 * R / 4 := by rw [abs_of_neg hx_neg]; linarith only [hx.1, hx.2, hR_gt_2]
    have hx_R : |x| ≤ R := hx_abs.trans (by linarith only [hR_gt_2])
    have hx_Rm : |x| ≤ ctRmax ctChartC1 c := hx_R.trans (by linarith only [hR_add_lt_Rm])
    have hx_dom : x ∈ ctPhiDom ε c := hPhiDom x (by linarith only [abs_le.1 hx_Rm]) hx_neg.le
    have hμ0 := ctMu_pos hc0
    have hμR : ctMu c * R ≤ 8 * c₁ ^ 2 := by
      calc ctMu c * R ≤ ctMu c * (4 * c₁ ^ 2 * c ^ ((2 : ℝ) / 3)) := mul_le_mul_of_nonneg_left hR_ub hμ0.le
        _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 * (c ^ (-(2 / 3) : ℝ) * c ^ ((2 : ℝ) / 3)) := by unfold ctMu; ring
        _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 := by rw [← Real.rpow_add hc0]; simp
        _ ≤ 8 * c₁ ^ 2 := by
            have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
              calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
            nlinarith only [h2, sq_nonneg c₁]
    have hμx_lt : ctMu c * |x| < rA := by
      have h1 : ctMu c * |x| ≤ ctMu c * R := mul_le_mul_of_nonneg_left hx_R hμ0.le
      linarith only [h1, hμR, h8c₁, hrA_pos]
    have hμx_W : ctMu c * x ∈ Ioo (-ρW) 0 := by
      have hW := hμx_lt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      rw [abs_of_neg hx_neg] at hW
      exact ⟨by linarith only [hW], mul_neg_of_pos_of_neg hμ0 hx_neg⟩
    have hpsi_bd : |ctPsi ε (ctMu c * x)| ≤ MW := (hWin _ hμx_W).2.1
    have hu_bd : |ctUhat ε c x| ≤ 3 * R / 4 + 1 / 2 := by
      unfold ctUhat
      have hlam0 := (ctLam_pos hc0).le
      calc |x + ctLam c * ctPsi ε (ctMu c * x)|
          ≤ |x| + |ctLam c * ctPsi ε (ctMu c * x)| := abs_add_le _ _
        _ = |x| + ctLam c * |ctPsi ε (ctMu c * x)| := by rw [abs_mul, abs_of_nonneg hlam0]
        _ ≤ 3 * R / 4 + ctLam c * MW := add_le_add hx_abs (mul_le_mul_of_nonneg_left hpsi_bd hlam0)
        _ ≤ 3 * R / 4 + 1 / 2 := add_le_add_right hlamMW _
    exact ⟨hx_dom, hx_neg, hx_Rm, hμx_lt, hu_bd⟩
  -- Center identity theorem at `z₀ := ((ctUhat ε c (-R / 2) : ℝ) : ℂ)`
  set x₀ : ℝ := -R / 2 with hx₀_def
  have hx₀_I : x₀ ∈ Ioo (-3 * R / 4) (-R / 4) := ⟨by linarith only [hR_gt_2, hx₀_def], by linarith only [hR_gt_2, hx₀_def]⟩
  obtain ⟨hx₀_dom', hx₀_neg, hx₀_Rm, _, hx₀_ubd⟩ := hx₀_dom x₀ hx₀_I
  set z₀ : ℂ := ((ctUhat ε c x₀ : ℝ) : ℂ)
  have hz₀_ball : z₀ ∈ ball (0 : ℂ) (R + 1) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    linarith only [hx₀_ubd, hR_gt_2]
  have hid_an : AnalyticOnNhd ℂ (fun z : ℂ => z) (ball 0 (R + 1)) := fun _ _ => analyticAt_id
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, G z = z := by
    have hcont_u : ContinuousAt (ctUhat ε c) x₀ := by
      have hμ_ltW := (hx₀_dom x₀ hx₀_I).2.2.2.1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      rw [abs_of_neg hx₀_neg] at hμ_ltW
      exact (ctUhat_hasDerivAt ⟨hρW_pos, hMW_nn, hWin⟩ hc0 hx₀_neg (by linarith only [hμ_ltW])).continuousAt
    have hev_x : ∀ᶠ x in 𝓝[≠] x₀, x ∈ Ioo (-3 * R / 4) (-R / 4) :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx₀_I.1 hx₀_I.2)
    have htend : Tendsto (fun x : ℝ => ((ctUhat ε c x : ℝ) : ℂ)) (𝓝[≠] x₀) (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.continuousAt.comp hcont_u).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [hev_x, self_mem_nhdsWithin] with x hx hne h_eq
      have hdom_x := (hx₀_dom x hx).1
      exact hne (ctUhat_injOn_dom ε hc0 hdom_x hx₀_dom' (Complex.ofReal_injective h_eq))
    have hagr : ∀ᶠ x in 𝓝[≠] x₀, G ((ctUhat ε c x : ℝ) : ℂ) = ((ctUhat ε c x : ℝ) : ℂ) := by
      filter_upwards [hev_x] with x hx
      obtain ⟨hdom_x, hx_neg, hx_Rm, hμx_lt, _⟩ := hx₀_dom x hx
      have hF_val := hFext x hdom_x hx_neg hx_Rm
      have hμx_Ψ : |ctMu c * x| < rΨ := by
        rw [abs_mul, abs_of_pos (ctMu_pos hc0)]
        exact hμx_lt.trans_le (min_le_left _ _)
      have hμx_p : ctMu c * x ∈ Ioo (-ρ_p) 0 := by
        have hp := hμx_lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        rw [abs_of_neg hx_neg] at hp
        exact ⟨by linarith only [hp], mul_neg_of_pos_of_neg (ctMu_pos hc0) hx_neg⟩
      have hpsi_eq' := hpsi_eq (ctMu c * x) hμx_p
      simp only [G]
      rw [hF_val]
      simp only [ctUhat]
      rw [show (ctMu c : ℂ) * (x : ℂ) = ((ctMu c * x : ℝ) : ℂ) by push_cast; ring, hΨ_real _ hμx_Ψ, ← hpsi_eq']
      push_cast; ring
    by_contra hcon
    obtain ⟨x, hx1, hx2⟩ := (hagr.and (htend.eventually (Filter.not_frequently.mp hcon))).exists
    exact hx2 hx1
  have heqOn := hG_an.eqOn_of_preconnected_of_frequently_eq hid_an (convex_ball _ _).isPreconnected hz₀_ball hfreq
  have hu_ball : (u : ℂ) ∈ ball (0 : ℂ) (R + 1) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have hab := abs_le.2 hu
    linarith only [hab]
  have heq_u := congrArg Complex.re (heqOn hu_ball)
  have hu_Rm : |u| ≤ ctRmax ctChartC1 c := (abs_le.2 hu).trans (by linarith only [hR_add_lt_Rm])
  have hPhi_u := Hchart.ctPhiC_ofReal hu_Rm
  have hΨ_u : |ctMu c * ctPhiR ε c u| < rΨ := by
    have := hmap (u : ℂ) hu_ball
    rw [hPhi_u] at this
    simpa [Complex.norm_real, Real.norm_eq_abs] using this.trans_le (min_le_left _ _)
  simp only [G, hPhi_u] at heq_u
  rw [show (ctMu c : ℂ) * (ctPhiR ε c u : ℂ) = ((ctMu c * ctPhiR ε c u : ℝ) : ℂ) by push_cast; ring,
    hΨ_real _ hΨ_u] at heq_u
  simpa using heq_u

/-! ### Part 4: Transferring `CtSd.cfu_K_airy_beta` to the Hankel chart `[-R', φ_c(R)]` -/

/-- **Step W3 (`ct:cfu` (1) in the Hankel chart `[-R', φ_c(R)]`)**: transfers `CtSd.cfu_K_airy_beta`
to all `x ∈ [-ctRprime ε c R, ctPhiR ε c R]` simultaneously, identifying `Itot` with `dualK`, `Uhat`
with `U_fn` (which satisfies `U_fn (ctPhiR ε c u) = u` on `u ∈ [-R, R]`), and replacing `ψ(a)` by
`ψ(0)` in the `c⁻¹` coefficient of `(Ai Bi)'` at cost `O(c^{-4/3} (1 + |x|)^{1/2})`. -/
theorem dualK_cfu_hankel_band {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ γ > (0 : ℝ), ∃ CK ≥ (0 : ℝ), ∃ q0c hh ψ₀ : ℝ, ∃ U_fn : ℝ → ℝ → ℝ,
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ → ∃ c₀ : ℝ, 3e6 ≤ c₀ ∧
        ∀ c : ℝ, c₀ ≤ c → ∀ R : ℝ, c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
          (∀ u ∈ Icc (-R) R, U_fn c (ctPhiR ε c u) = u) ∧
          (|1 + c⁻¹ * (-ψ₀ * q0c - 3 / 2 * hh)| ≤ 2) ∧
          (∀ x ∈ Icc (-ctRprime ε c R) (ctPhiR ε c R),
            |x| ≤ langerRadius c ∧ 0 < hankelXi c x ∧
            |CtDual.dualK ε c (hankelXi c x) -
              ((1 + c⁻¹ * (-ψ₀ * q0c - 3 / 2 * hh)) *
                  (-π * (airyAi' (U_fn c x) * airyBi (U_fn c x) + airyAi (U_fn c x) * airyBiDeriv (U_fn c x))) +
                c ^ (-(2 / 3 : ℝ)) * (q0c * (2 ^ (-(1 / 3 : ℝ)) * π)) *
                  (airyAi (U_fn c x) * airyBi (U_fn c x)))| ≤
              CK * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2)) := by
  obtain ⟨th, hth, hrel, s1, β0, c_cfu, hh, CK_sd, hs1, hβ0, hc_cfu, hCK_sd, hcfu⟩ := CtSd.cfu_K_airy_beta hε
  obtain ⟨δ_X, hδ_X, hXi_eq⟩ := ctCfu_Xi_eq_hankelXiUnit
  obtain ⟨M_AB, hM_AB, hAB⟩ := airyAiBiDeriv_abs_le
  obtain ⟨γ_u, hγ_u, hU_inv⟩ := ctPhiR_uhatAn_inv hε hth hrel
  obtain ⟨C_ch, c_ch, hC_ch, hCh⟩ := ctChartComplex_ctChartC1
  obtain ⟨ρW, MW, hρW, hMW, hWin⟩ := ctPsi_window hε
  obtain ⟨Kb, hKb, hDual⟩ := CtDual.ct_dual_id_part2 hε
  -- Continuity of `zA` at 0 gives `|zA a| < β0` for `|a| < δ_z`
  have hzA_cont : ContinuousAt CtCfu.zA 0 := CtCfu.analyticAt_zA.continuousAt
  obtain ⟨δ_z, hδ_z, hzA_lt⟩ := Metric.eventually_nhds_iff.mp
    (hzA_cont.eventually (by rw [CtCfu.zA_zero]; exact ball_mem_nhds 0 hβ0))
  -- Analyticity of `psiOf th` at 0 gives Lipschitz bound `|psiOf th a - psiOf th 0| ≤ L_ψ * |a|` on `|a| < δ_ψ`
  have hpsi_an := CtCfu.analyticAt_psiOf hth
  obtain ⟨rψ, hrψ, hrψ_an⟩ := analyticOnNhd_ball_of_analyticAt hpsi_an
  have hder_cont : ContinuousOn (deriv (CtCfu.psiOf th)) (closedBall 0 (rψ / 2)) :=
    hrψ_an.deriv.continuousOn.mono (closedBall_subset_ball (half_lt_self hrψ))
  obtain ⟨a_m, _, hmax_d⟩ := isCompact_closedBall (0 : ℝ) (rψ / 2) |>.exists_isMaxOn
    (⟨0, mem_closedBall_self (half_pos hrψ).le⟩) hder_cont.norm
  set δ_ψ : ℝ := rψ / 2 with hδψ_def
  set L_ψ : ℝ := ‖deriv (CtCfu.psiOf th) a_m‖
  have hL_ψ0 : 0 ≤ L_ψ := norm_nonneg _
  have hpsi_lip : ∀ a : ℝ, |a| ≤ δ_ψ → |CtCfu.psiOf th a - CtCfu.psiOf th 0| ≤ L_ψ * |a| := by
    intro a ha
    have hd_on : ∀ t ∈ Icc (min 0 a) (max 0 a), HasDerivWithinAt (CtCfu.psiOf th) (deriv (CtCfu.psiOf th) t) (Icc (min 0 a) (max 0 a)) t := by
      intro t ht
      have ht_mem : t ∈ ball (0 : ℝ) rψ := by
        rw [mem_ball_zero_iff, Real.norm_eq_abs]
        rcases le_total 0 a with ha0 | ha0
        · rw [min_eq_left ha0, max_eq_right ha0] at ht
          rw [abs_of_nonneg ha0] at ha
          have htb : |t| ≤ δ_ψ := abs_le.2 ⟨by linarith only [ht.1, hrψ, hδψ_def], by linarith only [ht.2, ha]⟩
          linarith only [htb, hδψ_def, half_lt_self hrψ]
        · rw [min_eq_right ha0, max_eq_left ha0] at ht
          rw [abs_of_nonpos ha0] at ha
          have htb : |t| ≤ δ_ψ := abs_le.2 ⟨by linarith only [ht.1, ha], by linarith only [ht.2, hrψ, hδψ_def]⟩
          linarith only [htb, hδψ_def, half_lt_self hrψ]
      exact ((hrψ_an t ht_mem).differentiableAt.hasDerivAt).hasDerivWithinAt
    have hbd_on : ∀ t ∈ Icc (min 0 a) (max 0 a), ‖deriv (CtCfu.psiOf th) t‖ ≤ L_ψ := by
      intro t ht
      have ht_cb : t ∈ closedBall (0 : ℝ) δ_ψ := by
        rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
        rcases le_total 0 a with ha0 | ha0
        · rw [min_eq_left ha0, max_eq_right ha0] at ht
          rw [abs_of_nonneg ht.1]; exact ht.2.trans (by rwa [abs_of_nonneg ha0] at ha)
        · rw [min_eq_right ha0, max_eq_left ha0] at ht
          rw [abs_of_nonpos ha0] at ha
          rw [abs_of_nonpos ht.2]; linarith only [ht.1, ha]
      exact hmax_d ht_cb
    have hmv' := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := CtCfu.psiOf th)
      (f' := deriv (CtCfu.psiOf th)) (C := L_ψ)
      (fun t ht => hd_on t ht) (fun t ht => hbd_on t ht)
      (convex_Icc (min 0 a) (max 0 a))
      ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    simpa [Real.norm_eq_abs] using hmv'
  -- Assemble constants independent of `c₁, c, R`
  set ψ₀ : ℝ := CtCfu.psiOf th 0
  set C_rep : ℝ := 2 ^ ((2 : ℝ) / 3) * L_ψ * |CtSd.q0c| * (π * M_AB) with hC_rep
  set CK : ℝ := CK_sd * Real.sqrt 2 + C_rep with hCK_def
  have hCK0 : 0 ≤ CK := by positivity
  set δ_all : ℝ := min δ_X (min δ_z (min δ_ψ ρW)) with hδ_all_def
  have hδ_all_pos : 0 < δ_all := lt_min hδ_X (lt_min hδ_z (lt_min (half_pos hrψ) hρW))
  set γ : ℝ := min (min γ_u (ctChartC1 / 2))
    (min (Real.sqrt (langerKappa * 4.94e-4 / 8)) (min (Real.sqrt (δ_all / 16)) (1 / 4)))
  have hγ_pos : 0 < γ :=
    lt_min (lt_min hγ_u (half_pos ctChartC1_pos))
      (lt_min (Real.sqrt_pos.mpr (by have := langerKappa_pos; positivity))
        (lt_min (Real.sqrt_pos.mpr (by positivity)) (by norm_num)))
  set U_fn : ℝ → ℝ → ℝ := fun c x => x + ctLam c * CtCfu.psiOf th (ctMu c * x)
  refine ⟨γ, hγ_pos, CK, hCK0, CtSd.q0c, hh, ψ₀, U_fn, fun c₁ hc₁_pos hc₁_le => ?_⟩
  obtain ⟨c_u, hc_u_ge, hU_c⟩ := hU_inv c₁ hc₁_pos (hc₁_le.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hc₁_C1 : c₁ ≤ ctChartC1 / 2 := hc₁_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  -- Bounds on `c₁`:
  have h4c₁_kap : 4 * c₁ ^ 2 ≤ langerKappa * 4.94e-4 / 2 := by
    have hs : c₁ ≤ Real.sqrt (langerKappa * 4.94e-4 / 8) :=
      hc₁_le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsq : c₁ ^ 2 ≤ langerKappa * 4.94e-4 / 8 := by
      calc c₁ ^ 2 ≤ Real.sqrt (langerKappa * 4.94e-4 / 8) ^ 2 :=
            sq_le_sq' (by linarith only [hc₁_pos, Real.sqrt_nonneg (langerKappa * 4.94e-4 / 8)]) hs
        _ = langerKappa * 4.94e-4 / 8 := Real.sq_sqrt (by have := langerKappa_pos; positivity)
    linarith only [hsq]
  have h8c₁_δ : 8 * c₁ ^ 2 ≤ δ_all / 2 := by
    have hs : c₁ ≤ Real.sqrt (δ_all / 16) :=
      hc₁_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hsq : c₁ ^ 2 ≤ δ_all / 16 := by
      calc c₁ ^ 2 ≤ Real.sqrt (δ_all / 16) ^ 2 :=
            sq_le_sq' (by linarith only [hc₁_pos, Real.sqrt_nonneg (δ_all / 16)]) hs
        _ = δ_all / 16 := Real.sq_sqrt (by positivity)
    linarith only [hsq]
  have h4c₁_14 : 4 * c₁ ^ 2 ≤ 1 / 4 := by
    have h1 : c₁ ≤ 1 / 4 := hc₁_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hc₁_pos, h1]
  -- Choose `c₀ ≥ 3e6`
  set B_ψ : ℝ := |ψ₀| + L_ψ * δ_ψ
  set c₀ : ℝ := max (max c_u (max c_cfu c_ch))
    (max (max ((2 * C_ch + 2) ^ 3) ((2 * MW + 1) ^ 3))
      (max (max (|ψ₀ * CtSd.q0c + 3 / 2 * hh| + 1) ((B_ψ + 1) ^ 3))
        (max ((4 / c₁ ^ 2 + 2) ^ 2)
          (max ((4 * (C_ch + 1) / (langerKappa * 4.94e-4) + 2) ^ 2)
               (max ((4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all + 2) ^ 2) ((4 * (C_ch + 1) + 2) ^ 2)))))) with hc₀_def
  refine ⟨c₀, hc_u_ge.trans (by simp only [hc₀_def, le_max_iff, le_rfl, true_or]), fun c hc R hR_lb hR_ub => ?_⟩
  have hc_u' : c_u ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or])
  have hc0 : 0 < c := by linarith only [hc_u_ge, hc_u']
  have hc_cfu' : c_cfu ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
  have hc_ch' : c_ch ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
  have hc12_le_c23 : c ^ ((1 : ℝ) / 2) ≤ c ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc_u_ge, hc_u']) (by norm_num)
  have hC13 : C_ch * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 := by
    have h1 : (2 * C_ch + 2) ^ 3 ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have h2 : 2 * C_ch + 2 ≤ c ^ ((1 : ℝ) / 3) := by
      have hpos : 0 ≤ 2 * C_ch + 2 := by linarith only [hC_ch]
      have hpow3 : (2 * C_ch + 2) ^ (3 : ℕ) = (2 * C_ch + 2) ^ (3 : ℝ) := by norm_cast
      calc 2 * C_ch + 2 = ((2 * C_ch + 2) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_mul hpos]; norm_num
        _ ≤ c ^ ((1 : ℝ) / 3) := by rw [← hpow3]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [Real.rpow_neg hc0.le, mul_inv_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
    nlinarith only [h2, hC_ch, Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3)]
  have Hchart : CtRealChartHyp ε c C_ch :=
    ⟨hCh ε hε c hc_ch', hC_ch, by linarith only [hc_u_ge, hc_u'], hC13⟩
  have hRm : R ≤ ctRmax ctChartC1 c := by
    have hc_sq : c₁ ^ 2 ≤ ctChartC1 ^ 2 := sq_le_sq' (by linarith only [ctChartC1_pos, hc₁_pos, hc₁_C1]) (by linarith only [ctChartC1_pos, hc₁_C1])
    unfold ctRmax
    nlinarith only [hc_sq, hR_ub, Real.rpow_pos_of_pos hc0 ((2 : ℝ) / 3)]
  have h_inv_ok := hU_c c hc_u' R hR_lb hR_ub
  have hα₁_bd : |1 + c⁻¹ * (-ψ₀ * CtSd.q0c - 3 / 2 * hh)| ≤ 2 := by
    have hc_big : |ψ₀ * CtSd.q0c + 3 / 2 * hh| + 1 ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have h1 : |c⁻¹ * (-ψ₀ * CtSd.q0c - 3 / 2 * hh)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hc0), show -ψ₀ * CtSd.q0c - 3 / 2 * hh = -(ψ₀ * CtSd.q0c + 3 / 2 * hh) by ring,
        abs_neg, inv_mul_le_iff₀ hc0]
      linarith only [hc_big]
    exact (abs_add_le _ _).trans (by rw [abs_one]; linarith only [h1])
  have h1_R : 1 < R := by
    have h4c₁ : (4 / c₁ ^ 2 + 2) ^ 2 ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have h2 : 4 / c₁ ^ 2 + 2 ≤ c ^ ((2 : ℝ) / 3) := by
      have h3 : 4 / c₁ ^ 2 + 2 ≤ c ^ ((1 : ℝ) / 2) := by
        calc 4 / c₁ ^ 2 + 2 = √((4 / c₁ ^ 2 + 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
          _ = ((4 / c₁ ^ 2 + 2) ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
          _ ≤ c ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h4c₁ (by norm_num)
      exact h3.trans hc12_le_c23
    have h4 : 4 ≤ c₁ ^ 2 * c ^ ((2 : ℝ) / 3) := by
      have h4a : 4 / c₁ ^ 2 ≤ c ^ ((2 : ℝ) / 3) := by linarith only [h2]
      rwa [div_le_iff₀ (sq_pos_of_pos hc₁_pos), mul_comm] at h4a
    linarith only [hR_lb, h4]
  have hcM : 2 * MW ≤ c := by
    have h1 : (2 * MW + 1) ^ 3 ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have hge : 1 ≤ (2 * MW + 1) ^ 2 := by nlinarith only [hMW]
    have hle3 : 2 * MW ≤ (2 * MW + 1) ^ 3 := by
      calc 2 * MW ≤ 2 * MW + 1 := by linarith only
        _ = (2 * MW + 1) * 1 := by ring
        _ ≤ (2 * MW + 1) * (2 * MW + 1) ^ 2 := mul_le_mul_of_nonneg_left hge (by linarith only [hMW])
        _ = (2 * MW + 1) ^ 3 := by ring
    linarith only [hle3, h1]
  have hlamMW : ctLam c * MW ≤ 1 / 2 := by
    unfold ctLam
    have h2 : (2 : ℝ) ^ (-(2 / 3) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have h1 : (2 * MW + 1) ^ 3 ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have hpow : 2 * MW + 1 ≤ c ^ ((1 : ℝ) / 3) := by
      have hpos : 0 ≤ 2 * MW + 1 := by linarith only [hMW]
      have hpow3 : (2 * MW + 1) ^ (3 : ℕ) = (2 * MW + 1) ^ (3 : ℝ) := by norm_cast
      calc 2 * MW + 1 = ((2 * MW + 1) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_mul hpos]; norm_num
        _ ≤ c ^ ((1 : ℝ) / 3) := by rw [← hpow3]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [Real.rpow_neg hc0.le, mul_assoc, inv_mul_eq_div]
    have hle : MW / c ^ ((1 : ℝ) / 3) ≤ 1 / 2 := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]; linarith only [hpow]
    nlinarith only [h2, hle, show 0 ≤ MW / c ^ ((1 : ℝ) / 3) by positivity]
  have hμR_8 : ctMu c * R ≤ 8 * c₁ ^ 2 := by
    have hμ0 := ctMu_pos hc0
    calc ctMu c * R ≤ ctMu c * (4 * c₁ ^ 2 * c ^ ((2 : ℝ) / 3)) := mul_le_mul_of_nonneg_left hR_ub hμ0.le
      _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 * (c ^ (-(2 / 3) : ℝ) * c ^ ((2 : ℝ) / 3)) := by unfold ctMu; ring
      _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 := by rw [← Real.rpow_add hc0]; simp
      _ ≤ 8 * c₁ ^ 2 := by
          have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
            calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          nlinarith only [h2, sq_nonneg c₁]
  refine ⟨h_inv_ok, hα₁_bd, fun x hx => ?_⟩
  -- Bound `-R ≤ -ctRprime ε c R` and `ctPhiR ε c R ≤ R + 1/2`, hence `|x| ≤ R + 1/2`
  have hR_pos : 0 < R := by linarith only [h1_R]
  have hR_abs : |R| ≤ ctRmax ctChartC1 c := by rw [abs_of_pos hR_pos]; exact hRm
  have hPhi_R := Hchart.abs_ctPhiR_sub_le hR_abs
  have haw : -ρW < ctMu c * (-R) := by
    have hρ1 : δ_all ≤ ρW := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hμlt : ctMu c * R < ρW := by linarith only [hμR_8, h8c₁_δ, hρ1, hδ_all_pos]
    linarith only [hμlt]
  obtain ⟨u_r, hu_r_mem, _, hu_r_phi⟩ := ctPhi_pre ⟨hρW, hMW, hWin⟩ hc0 hcM hlamMW (a := -R) (by linarith only [h1_R]) haw
  have hx_lb : -R ≤ x := by
    have heq : -ctRprime ε c R = u_r := by unfold ctRprime; rw [hu_r_phi, neg_neg]
    linarith only [hx.1, hu_r_mem.1, heq]
  have hx_ub : x ≤ R + 1 / 2 := by
    have hle := abs_le.1 hPhi_R
    linarith only [hx.2, hle.2, hC13]
  have hx_abs_R : |x| ≤ R + 1 := abs_le.2 ⟨by linarith only [hx_lb], by linarith only [hx_ub]⟩
  -- Check `c^(2/3)` lower bounds from `c₀`
  have h_c23_kap : 4 * (C_ch + 1) / (langerKappa * 4.94e-4) + 2 ≤ c ^ ((2 : ℝ) / 3) := by
    have h1 : (4 * (C_ch + 1) / (langerKappa * 4.94e-4) + 2) ^ 2 ≤ c :=
      hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have h2 : 4 * (C_ch + 1) / (langerKappa * 4.94e-4) + 2 ≤ c ^ ((1 : ℝ) / 2) := by
      have hκ := langerKappa_pos
      calc _ = √((4 * (C_ch + 1) / (langerKappa * 4.94e-4) + 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = ((4 * (C_ch + 1) / (langerKappa * 4.94e-4) + 2) ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
        _ ≤ c ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    exact h2.trans hc12_le_c23
  have h_c23_δ : 4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all + 2 ≤ c ^ ((2 : ℝ) / 3) := by
    have h1 : (4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all + 2) ^ 2 ≤ c :=
      hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have h2 : 4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all + 2 ≤ c ^ ((1 : ℝ) / 2) := by
      calc _ = √((4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all + 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = ((4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all + 2) ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
        _ ≤ c ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    exact h2.trans hc12_le_c23
  have h_c23_one : 4 * (C_ch + 1) + 2 ≤ c ^ ((2 : ℝ) / 3) := by
    have h1 : (4 * (C_ch + 1) + 2) ^ 2 ≤ c :=
      hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, or_true])
    have h2 : 4 * (C_ch + 1) + 2 ≤ c ^ ((1 : ℝ) / 2) := by
      calc _ = √((4 * (C_ch + 1) + 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ = ((4 * (C_ch + 1) + 2) ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
        _ ≤ c ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    exact h2.trans hc12_le_c23
  -- (1) `|x| ≤ langerRadius c` and `|x| ≤ c^(2/3)` and `|ctMu c * x| < δ_all`
  have hx_langer : |x| ≤ langerRadius c := by
    have hc23 : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hκpos := langerKappa_pos
    have h1 : (1 : ℝ) ≤ langerKappa * 4.94e-4 / 2 * c ^ ((2 : ℝ) / 3) := by
      have hdiv : 4 * (C_ch + 1) / (langerKappa * 4.94e-4) ≤ c ^ ((2 : ℝ) / 3) := by linarith only [h_c23_kap]
      rw [div_le_iff₀ (by positivity)] at hdiv
      nlinarith only [hdiv, hC_ch]
    have h2 : R + 1 ≤ langerKappa * 4.94e-4 * c ^ ((2 : ℝ) / 3) := by
      have hR1 : R ≤ (langerKappa * 4.94e-4 / 2) * c ^ ((2 : ℝ) / 3) :=
        hR_ub.trans (mul_le_mul_of_nonneg_right h4c₁_kap hc23.le)
      linarith only [h1, hR1]
    have hAr : langerRadius c = langerKappa * 4.94e-4 * c ^ ((2 : ℝ) / 3) := by
      rw [langerRadius_eq]; ring
    rw [hAr]; linarith only [hx_abs_R, h2]
  have hx_c23 : |x| ≤ c ^ ((2 : ℝ) / 3) := by
    have hc23 : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have h1 : (1 : ℝ) ≤ 1 / 2 * c ^ ((2 : ℝ) / 3) := by linarith only [hC_ch, h_c23_one]
    have h2 : R ≤ (1 / 4) * c ^ ((2 : ℝ) / 3) :=
      hR_ub.trans (mul_le_mul_of_nonneg_right h4c₁_14 hc23.le)
    linarith only [hx_abs_R, h1, h2]
  have hxi_pos : 0 < hankelXi c x := hankelXi_pos hc0 hx_langer
  have hμx_δ : |ctMu c * x| < δ_all := by
    have hμ0 := ctMu_pos hc0
    rw [abs_mul, abs_of_pos hμ0]
    have h1 : ctMu c * 1 < δ_all / 2 := by
      unfold ctMu
      rw [Real.rpow_neg hc0.le, mul_one]
      have hlt : 2 ^ ((2 : ℝ) / 3) / (δ_all / 2) < c ^ ((2 : ℝ) / 3) := by
        have h2d : 2 * 2 ^ ((2 : ℝ) / 3) / δ_all ≤ 4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all := by
          gcongr; linarith only [hC_ch]
        calc 2 ^ ((2 : ℝ) / 3) / (δ_all / 2) = 2 * 2 ^ ((2 : ℝ) / 3) / δ_all := by ring
          _ ≤ 4 * (C_ch + 1) * 2 ^ ((2 : ℝ) / 3) / δ_all := h2d
          _ < c ^ ((2 : ℝ) / 3) := by linarith only [h_c23_δ]
      rw [div_lt_iff₀ (half_pos hδ_all_pos)] at hlt
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) * (c ^ ((2 : ℝ) / 3))⁻¹
          = (2 : ℝ) ^ ((2 : ℝ) / 3) / c ^ ((2 : ℝ) / 3) := by ring
        _ < δ_all / 2 := (div_lt_iff₀ (Real.rpow_pos_of_pos hc0 _)).2 (by linarith only [hlt])
    calc ctMu c * |x| ≤ ctMu c * (R + 1) := mul_le_mul_of_nonneg_left hx_abs_R hμ0.le
      _ = ctMu c * R + ctMu c * 1 := by ring
      _ < δ_all / 2 + δ_all / 2 := by linarith only [hμR_8, h8c₁_δ, h1]
      _ = δ_all := by ring
  -- Apply `CtSd.cfu_K_airy_beta` at `lam := c^(-(1/3 : ℝ))`, `β := CtCfu.zA (ctMu c * x)`
  set a : ℝ := ctMu c * x with ha_def
  set β : ℝ := CtCfu.zA a with hβ_def
  set lam : ℝ := c ^ (-(1 / 3 : ℝ)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hc0 _
  have hclam3 : c * lam ^ 3 = 1 := by
    rw [hlam_def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
  have hβ_lt : |β| < β0 := by
    have ha_z : dist a 0 < δ_z := by
      rw [Real.dist_eq, sub_zero]
      exact hμx_δ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    simpa [β, Real.dist_eq, CtCfu.zA_zero] using hzA_lt ha_z
  have hX_res := hXi_eq a (hμx_δ.trans_le (min_le_left _ _))
  obtain ⟨Itot, hItot_ten, hItot_bd⟩ := hcfu hc_cfu' hlam_pos hclam3 hβ_lt
  -- Identify `-Itot.re = CtDual.dualK ε c (hankelXi c x)`
  have hItot_eq : Itot = ((Real.sqrt (π * c / 12) : ℝ) : ℂ) * CtDual.dualI ε c (hankelXi c x) := by
    have hdual := (hDual (by linarith only [hc_u_ge, hc_u'] : (2 : ℝ) ≤ c)).1 (hankelXi c x) hxi_pos
    have hten' : Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b,
        CtSd.Bfun ε c τ * Complex.exp (Complex.I * c * (CtSd.phaseL (CtCfu.NF β) τ : ℂ))) atTop
        (𝓝 (((Real.sqrt (π * c / 12) : ℝ) : ℂ) * CtDual.dualI ε c (hankelXi c x))) := by
      have hconst := (tendsto_const_nhds (x := ((Real.sqrt (π * c / 12) : ℝ) : ℂ))).mul hdual.1
      refine hconst.congr fun b => ?_
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun τ _ => ?_
      rw [CtSd.Bfun, CtDual.dualP_eq, hX_res.2.1, hankelXi_eq_hankelXiUnit hc0 x]
      ring
    exact tendsto_nhds_unique hItot_ten hten'
  have hdualK_eq : -Itot.re = CtDual.dualK ε c (hankelXi c x) := by
    rw [hItot_eq]
    unfold CtDual.dualK
    simp [Complex.mul_re]
  have hlam4 : lam ^ 4 = c ^ (-(4 / 3 : ℝ)) := by
    rw [hlam_def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; congr 1; norm_num
  have hlam3 : lam ^ 3 = c⁻¹ := by
    rw [hlam_def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num; exact Real.rpow_neg_one c
  have hlam2 : lam ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    rw [hlam_def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; congr 1; norm_num
  -- Identify `Uhat lam (AF β) (th β / dF β) = U_fn c x`
  have hUhat_eq : CtSd.Uhat lam (CtCfu.AF β) (th β / CtCfu.dF β) = U_fn c x := by
    have hAF_eq : CtCfu.AF β = a := hX_res.2.2
    have hkap_lam : CtSd.kap * lam ^ 2 = ctMu c := by
      unfold CtSd.kap ctMu
      rw [hlam2]; rfl
    have hlam_kap : lam ^ 3 / (CtSd.kap * lam ^ 2) = ctLam c := by
      have hkap_eq : CtSd.kap = (2 : ℝ) ^ ((2 : ℝ) / 3) := rfl
      rw [hkap_eq, hlam3, hlam2]
      unfold ctLam
      have h2eq : (2 : ℝ) ^ (-(2 / 3) : ℝ) = ((2 : ℝ) ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
      rw [h2eq]
      have hpi_2 : (2 : ℝ) ^ (2 / 3 : ℝ) ≠ 0 := by positivity
      have hcp : c ^ (-(2 / 3) : ℝ) ≠ 0 := by positivity
      have hadd : c ^ (-(1 / 3) : ℝ) * c ^ (-(2 / 3) : ℝ) = c⁻¹ := by
        rw [← Real.rpow_add hc0]; norm_num; exact Real.rpow_neg_one c
      rw [← hadd]
      field_simp
    unfold CtSd.Uhat U_fn CtCfu.psiOf
    rw [hAF_eq]
    have hμ_ne : ctMu c ≠ 0 := (ctMu_pos hc0).ne'
    calc (a + lam ^ 3 * (th (CtCfu.zA a) / CtCfu.dF (CtCfu.zA a))) / (CtSd.kap * lam ^ 2)
        = a / (CtSd.kap * lam ^ 2) + (lam ^ 3 / (CtSd.kap * lam ^ 2)) * (th (CtCfu.zA a) / CtCfu.dF (CtCfu.zA a)) := by ring
      _ = (ctMu c * x) / ctMu c + ctLam c * (th (CtCfu.zA a) / CtCfu.dF (CtCfu.zA a)) := by rw [hlam_kap, hkap_lam, ha_def]
      _ = x + ctLam c * (th (CtCfu.zA a) / CtCfu.dF (CtCfu.zA a)) := by rw [mul_div_cancel_left₀ _ hμ_ne]
  -- Simplify `(1 + |U|)^(1/2)` and `psi` replacement error
  have ha_δψ : |a| ≤ δ_ψ := (hμx_δ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hpsi_bd : |CtCfu.psiOf th a| ≤ B_ψ := by
    have h1 := hpsi_lip a ha_δψ
    have h2 : |CtCfu.psiOf th a| ≤ |ψ₀| + |CtCfu.psiOf th a - ψ₀| := by
      calc |CtCfu.psiOf th a| = |ψ₀ + (CtCfu.psiOf th a - ψ₀)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h3 : L_ψ * |a| ≤ L_ψ * δ_ψ := mul_le_mul_of_nonneg_left ha_δψ hL_ψ0
    linarith only [h2, h1, h3]
  have hU_diff : |U_fn c x - x| ≤ 1 := by
    have he : U_fn c x - x = ctLam c * CtCfu.psiOf th a := by unfold U_fn; ring
    rw [he, abs_mul, abs_of_pos (ctLam_pos hc0)]
    have h1 : (B_ψ + 1) ^ 3 ≤ c := hc.trans' (by simp only [hc₀_def, le_max_iff, le_rfl, true_or, or_true])
    have hpow : B_ψ + 1 ≤ c ^ ((1 : ℝ) / 3) := by
      have hpos : 0 ≤ B_ψ + 1 := by linarith only [show 0 ≤ B_ψ by positivity]
      have hpow3 : (B_ψ + 1) ^ (3 : ℕ) = (B_ψ + 1) ^ (3 : ℝ) := by norm_cast
      calc B_ψ + 1 = ((B_ψ + 1) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_mul hpos]; norm_num
        _ ≤ c ^ ((1 : ℝ) / 3) := by rw [← hpow3]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    unfold ctLam
    have h2 : (2 : ℝ) ^ (-(2 / 3) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    rw [Real.rpow_neg hc0.le]
    have h4 : (c ^ ((1 : ℝ) / 3))⁻¹ * |CtCfu.psiOf th a| ≤ (c ^ ((1 : ℝ) / 3))⁻¹ * B_ψ :=
      mul_le_mul_of_nonneg_left hpsi_bd (by positivity)
    have h5 : (c ^ ((1 : ℝ) / 3))⁻¹ * B_ψ ≤ 1 := by
      rw [inv_mul_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]; linarith only [hpow]
    calc (2 : ℝ) ^ (-(2 / 3) : ℝ) * (c ^ ((1 : ℝ) / 3))⁻¹ * |CtCfu.psiOf th a|
        = (2 : ℝ) ^ (-(2 / 3) : ℝ) * ((c ^ ((1 : ℝ) / 3))⁻¹ * |CtCfu.psiOf th a|) := by ring
      _ ≤ 1 * ((c ^ ((1 : ℝ) / 3))⁻¹ * |CtCfu.psiOf th a|) := by gcongr
      _ = (c ^ ((1 : ℝ) / 3))⁻¹ * |CtCfu.psiOf th a| := one_mul _
      _ ≤ 1 := h4.trans h5
  have h1U_le : 1 + |U_fn c x| ≤ 2 * (1 + |x|) := by
    have hle : |U_fn c x| ≤ |x| + 1 := by
      calc |U_fn c x| = |x + (U_fn c x - x)| := by ring_nf
        _ ≤ |x| + |U_fn c x - x| := abs_add_le _ _
        _ ≤ |x| + 1 := by linarith only [hU_diff]
    linarith only [hle, abs_nonneg x]
  have hU_pow : (1 + |U_fn c x|) ^ ((1 : ℝ) / 2) ≤ Real.sqrt 2 * (1 + |x|) ^ ((1 : ℝ) / 2) := by
    calc (1 + |U_fn c x|) ^ ((1 : ℝ) / 2) ≤ (2 * (1 + |x|)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) h1U_le (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 2) * (1 + |x|) ^ ((1 : ℝ) / 2) := Real.mul_rpow (by norm_num) (by positivity)
      _ = Real.sqrt 2 * (1 + |x|) ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
  -- Now compare `KMain` at `psiOf th a` vs `ψ₀`
  have hK_diff : |CtSd.KMain lam (th β / CtCfu.dF β) CtSd.q0c hh (U_fn c x) -
      ((1 + c⁻¹ * (-ψ₀ * CtSd.q0c - 3 / 2 * hh)) *
          (-π * (airyAi' (U_fn c x) * airyBi (U_fn c x) + airyAi (U_fn c x) * airyBiDeriv (U_fn c x))) +
        c ^ (-(2 / 3 : ℝ)) * (CtSd.q0c * (2 ^ (-(1 / 3 : ℝ)) * π)) *
          (airyAi (U_fn c x) * airyBi (U_fn c x)))| ≤ C_rep * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by
    set AB := airyAi' (U_fn c x) * airyBi (U_fn c x) + airyAi (U_fn c x) * airyBiDeriv (U_fn c x)
    have hEq : CtSd.KMain lam (th β / CtCfu.dF β) CtSd.q0c hh (U_fn c x) -
        ((1 + c⁻¹ * (-ψ₀ * CtSd.q0c - 3 / 2 * hh)) * (-π * AB) +
          c ^ (-(2 / 3 : ℝ)) * (CtSd.q0c * (2 ^ (-(1 / 3 : ℝ)) * π)) * (airyAi (U_fn c x) * airyBi (U_fn c x))) =
        c⁻¹ * (CtCfu.psiOf th a - ψ₀) * CtSd.q0c * (π * AB) := by
      unfold CtSd.KMain CtCfu.psiOf
      rw [hlam3, hlam2]
      ring
    rw [hEq, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hc0), abs_of_pos Real.pi_pos]
    have hAB' : π * |AB| ≤ π * M_AB := mul_le_mul_of_nonneg_left (hAB (U_fn c x)) Real.pi_pos.le
    have hpsi' : |CtCfu.psiOf th a - ψ₀| ≤ L_ψ * (ctMu c * |x|) := by
      have h1 := hpsi_lip a ha_δψ
      rwa [abs_mul, abs_of_pos (ctMu_pos hc0)] at h1
    have hx_half : c⁻¹ * (ctMu c * |x|) ≤ 2 ^ ((2 : ℝ) / 3) * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by
      have h1 : c⁻¹ * ctMu c = 2 ^ ((2 : ℝ) / 3) * c ^ (-(5 / 3 : ℝ)) := by
        unfold ctMu
        rw [← Real.rpow_neg_one c]
        rw [show c ^ (-1 : ℝ) * ((2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 / 3) : ℝ)) =
            2 ^ ((2 : ℝ) / 3) * (c ^ (-1 : ℝ) * c ^ (-(2 / 3) : ℝ)) by ring]
        rw [← Real.rpow_add hc0]
        norm_num
      have hx0 : 0 ≤ |x| := abs_nonneg _
      have hsq : |x| ≤ c ^ ((1 : ℝ) / 3) * (1 + |x|) ^ ((1 : ℝ) / 2) := by
        have hroot : |x| = |x| ^ ((1 : ℝ) / 2) * |x| ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add' hx0 (by norm_num)]; norm_num
        have h_half1 : |x| ^ ((1 : ℝ) / 2) ≤ (c ^ ((2 : ℝ) / 3)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hx0 hx_c23 (by norm_num)
        have h_c13 : (c ^ ((2 : ℝ) / 3)) ^ ((1 : ℝ) / 2) = c ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_mul hc0.le]; norm_num
        have h_half2 : |x| ^ ((1 : ℝ) / 2) ≤ (1 + |x|) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hx0 (by linarith only [abs_nonneg x]) (by norm_num)
        calc |x| = |x| ^ ((1 : ℝ) / 2) * |x| ^ ((1 : ℝ) / 2) := hroot
          _ ≤ c ^ ((1 : ℝ) / 3) * (1 + |x|) ^ ((1 : ℝ) / 2) :=
              mul_le_mul (h_half1.trans_eq h_c13) h_half2 (by positivity) (by positivity)
      have hpow_c : c ^ (-(5 / 3 : ℝ)) * c ^ ((1 : ℝ) / 3) = c ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc c⁻¹ * (ctMu c * |x|) = (c⁻¹ * ctMu c) * |x| := by ring
        _ = 2 ^ ((2 : ℝ) / 3) * c ^ (-(5 / 3 : ℝ)) * |x| := by rw [h1]
        _ ≤ 2 ^ ((2 : ℝ) / 3) * c ^ (-(5 / 3 : ℝ)) * (c ^ ((1 : ℝ) / 3) * (1 + |x|) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 2 ^ ((2 : ℝ) / 3) * (c ^ (-(5 / 3 : ℝ)) * c ^ ((1 : ℝ) / 3)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by ring
        _ = 2 ^ ((2 : ℝ) / 3) * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by rw [hpow_c]
    have hμ_nn : 0 ≤ ctMu c := (ctMu_pos hc0).le
    have hinv_nn : 0 ≤ c⁻¹ := (inv_pos.2 hc0).le
    calc c⁻¹ * |CtCfu.psiOf th a - ψ₀| * |CtSd.q0c| * (π * |AB|)
        ≤ c⁻¹ * (L_ψ * (ctMu c * |x|)) * |CtSd.q0c| * (π * M_AB) := by
          gcongr
      _ = (L_ψ * |CtSd.q0c| * (π * M_AB)) * (c⁻¹ * (ctMu c * |x|)) := by ring
      _ ≤ (L_ψ * |CtSd.q0c| * (π * M_AB)) * (2 ^ ((2 : ℝ) / 3) * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hx_half (by positivity)
      _ = C_rep * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by rw [hC_rep]; ring
  rw [hdualK_eq, hUhat_eq] at hItot_bd
  have hsd_bd : |CtDual.dualK ε c (hankelXi c x) - CtSd.KMain lam (th β / CtCfu.dF β) CtSd.q0c hh (U_fn c x)| ≤
      CK_sd * Real.sqrt 2 * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by
    rw [hlam4] at hItot_bd
    calc _ ≤ CK_sd * c ^ (-(4 / 3 : ℝ)) * (Real.sqrt 2 * (1 + |x|) ^ ((1 : ℝ) / 2)) :=
          hItot_bd.trans (mul_le_mul_of_nonneg_left hU_pow (by positivity))
      _ = CK_sd * Real.sqrt 2 * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by ring
  refine ⟨hx_langer, hxi_pos, ?_⟩
  calc |CtDual.dualK ε c (hankelXi c x) - _|
      ≤ |CtDual.dualK ε c (hankelXi c x) - CtSd.KMain lam (th β / CtCfu.dF β) CtSd.q0c hh (U_fn c x)| +
        |CtSd.KMain lam (th β / CtCfu.dF β) CtSd.q0c hh (U_fn c x) - _| := abs_sub_le _ _ _
    _ ≤ CK_sd * Real.sqrt 2 * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) +
        C_rep * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := add_le_add hsd_bd hK_diff
    _ = CK * c ^ (-(4 / 3 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := by rw [hCK_def]; ring

/-- info: 'FormalResearch.SignUncertainty.dualK_cfu_hankel_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dualK_cfu_hankel_band

end FormalResearch.SignUncertainty
