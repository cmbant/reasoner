/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpFJSetup
public import FormalResearch.SignUncertainty.FctInnerConcreteSetup

/-!
# Chart centering and class correspondence (`fct:warp-asymp` (1))

Constructs the centered Langer chart `W : FctWarpChartData K4 ε c` (`fctWarpFJ_center`),
and proves the forward (`fctWarpFJ_of_class`) and converse (`fctWarpClass_of_chart`)
links between `FctWarpClass` and the chart ball around `(airyZero 1, 0)`.

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped Real ContDiff
open FormalResearch.CohnElkies
open FormalResearch.Special
open FormalResearch.SignUncertainty.CtCfu
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

set_option maxHeartbeats 1600000 in
private lemma fctWarpFJ_center_eps {K4 ε : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) :
    ∃ C_ctr c₀ : ℝ, 0 ≤ C_ctr ∧ 3e6 ≤ c₀ ∧ ∀ {c : ℝ}, c₀ ≤ c →
      ∃ W : FctWarpChartData K4 ε c, W.C_ctr ≤ C_ctr ∧ W.S = concreteBoxS K4 ε c ∧ W.ellMin = pbellMin := by
  let ellMin := pbellMin
  let τ_lim_box := pbTauLim
  have hellMin_pos : 0 < ellMin := pbellMin_pos
  have hτlim_pos : 0 < τ_lim_box := pbTauLim_pos
  let τD := (fct_comp_D_part1 StripKernelChoice.star).choose
  have hτD_pos : 0 < τD := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1
  obtain ⟨Cv0, Cv1, Cv2, _, _, _, _, _, hthD_bd⟩ := thetaD_center_bounds
  obtain ⟨Cα, hCα_nn, hCα_bd⟩ := fctChart_uAlpha_bound
  obtain ⟨δz, s₀, Cfj, Kz, hδz, hδz_le, hs₀_pos, hCfj_nn, hKz_pos, hfj⟩ := fj_fold_taylor hε
  obtain ⟨C5, c5, hc5_3e6, hnode⟩ := ctNode_expansion hε
  obtain ⟨ρc, τ0_cf, ψ, Ξ, hρc_pos, _, _, hcfu, -, -, hΞ0, hΞ1, hΞ2, ⟨CC, hCC⟩⟩ := CtCfu.cfu_psi_langer hε
  obtain ⟨hθ_spec, Mθ, _, hθ_jc⟩ := concreteThetaT_spec hε
  have hMθ : 0 ≤ Mθ := (abs_nonneg _).trans
    (by simpa [Real.norm_eq_abs] using hθ_jc.2 0 (by simp) 0 (by constructor <;> norm_num))
  set θt := concreteThetaT ε
  have hev_n : ∀ᶠ z in 𝓝 (0 : ℝ), Real.pi ^ 2 / 24 ≤ nfun z + z * deriv nfun z ∧
      Real.pi ^ 2 / 16 ≤ nfun z ∧ nfun z ≤ Real.pi ^ 2 / 10 ∧
      Real.pi ^ 2 / 36 ≤ fF z ∧ fF z ≤ Real.pi ^ 2 / 10 := by
    have h0 : ContinuousAt (fun z : ℝ => nfun z + z * deriv nfun z) 0 :=
      contDiffAt_nfun.continuousAt.add (continuousAt_id.mul
        ((contDiffOn_deriv_nfun.contDiffAt (isOpen_Ioo.mem_nhds zero_mem_Ioo)).continuousAt))
    have ha_gt : Real.pi ^ 2 / 24 < nfun 0 + 0 * deriv nfun 0 := by
      rw [nfun_zero, zero_mul, add_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    have hb1_gt : Real.pi ^ 2 / 16 < nfun 0 := by rw [nfun_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    have hb2_lt : nfun 0 < Real.pi ^ 2 / 10 := by rw [nfun_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    have hc1_gt : Real.pi ^ 2 / 36 < fF 0 := by rw [fF_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    have hc2_lt : fF 0 < Real.pi ^ 2 / 10 := by rw [fF_zero]; linarith [sq_pos_of_pos Real.pi_pos]
    have ha := h0.eventually (lt_mem_nhds ha_gt)
    have hb := (contDiffAt_nfun.continuousAt.eventually (lt_mem_nhds hb1_gt)).and
      (contDiffAt_nfun.continuousAt.eventually (gt_mem_nhds hb2_lt))
    have hc := (contDiffAt_fF.continuousAt.eventually (lt_mem_nhds hc1_gt)).and
      (contDiffAt_fF.continuousAt.eventually (gt_mem_nhds hc2_lt))
    exact (ha.and (hb.and hc)).mono fun z ⟨p, ⟨q1, q2⟩, ⟨r1, r2⟩⟩ => ⟨p.le, q1.le, q2.le, r1.le, r2.le⟩
  obtain ⟨ρ_n, hρ_n, hball_n⟩ := Metric.eventually_nhds_iff.mp hev_n
  have hθ_d1 : ContDiffOn ℝ 17 (deriv θt) (Ioo (-1 : ℝ) 6) := hθ_jc.1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hθ_d2 : ContDiffOn ℝ 16 (deriv (deriv θt)) (Ioo (-1 : ℝ) 6) := hθ_d1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  set r₀ : ℝ := min (rr / 2) (1 / 4 : ℝ)
  have hr₀_pos : 0 < r₀ := lt_min (by linarith [rr_pos]) (by norm_num)
  have hr₀_14 : r₀ ≤ 1 / 4 := min_le_right _ _
  have hr₀_rr : r₀ < rr := (min_le_left _ _).trans_lt (by linarith [rr_pos])
  have hK_Ioo : Icc (-r₀) r₀ ⊆ Ioo (-rr) rr := fun z hz => ⟨by linarith [hz.1, hr₀_rr], by linarith [hz.2, hr₀_rr]⟩
  have hK_Yint : Icc (-r₀) r₀ ⊆ Ioo (-1 : ℝ) 6 := fun z hz =>
    ⟨by have := min_le_right (rr / 2) (1 / 4 : ℝ); linarith [hz.1],
     by have := min_le_right (rr / 2) (1 / 4 : ℝ); linarith [hz.2]⟩
  obtain ⟨BH10, hBH10⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hθ_jc.1.continuousOn.const_mul 3 |>.add ((continuousOn_id.const_mul 2).mul hθ_d1.continuousOn)).mono hK_Yint)
  obtain ⟨BH11, hBH11⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hθ_d1.continuousOn.const_mul 5 |>.add ((continuousOn_id.const_mul 2).mul hθ_d2.continuousOn)).mono hK_Yint)
  let δ_sm := min (δz / 4) (min (r₀ / 4) (ρ_n / 8))
  have hδsm_pos : 0 < δ_sm := lt_min (by linarith) (lt_min (by linarith) (by positivity))
  have hδsm_4 : ∀ {z : ℝ}, 0 ≤ z → z ≤ 4 * δ_sm → z < rr ∧ z ≤ r₀ ∧ z ≤ δz ∧
      Real.pi ^ 2 / 24 ≤ nfun z + z * deriv nfun z ∧
      Real.pi ^ 2 / 16 ≤ nfun z ∧ nfun z ≤ Real.pi ^ 2 / 10 ∧
      Real.pi ^ 2 / 36 ≤ fF z ∧ fF z ≤ Real.pi ^ 2 / 10 := fun {z} hz0 hz4 => by
    have h4z : 4 * δ_sm ≤ δz := by
      have := min_le_left (δz / 4) (min (r₀ / 4) (ρ_n / 8)); linarith
    have h4r : 4 * δ_sm ≤ r₀ := by
      have := (min_le_right (δz / 4) (min (r₀ / 4) (ρ_n / 8))).trans (min_le_left _ _); linarith
    have h4n : 4 * δ_sm ≤ ρ_n / 2 := by
      have := (min_le_right (δz / 4) (min (r₀ / 4) (ρ_n / 8))).trans (min_le_right _ _); linarith
    have hdz : z ≤ 4 * (rr / 4) :=
      ((by linarith : z ≤ 4 * δz).trans (mul_le_mul_of_nonneg_left hδz_le (by norm_num))).trans
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    exact ⟨by linarith [hdz, rr_pos], by linarith, by linarith,
      hball_n (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hz0]; linarith)⟩
  have hev_edge : 0 < edgePhi (hankelEdgeM (Real.sqrt δ_sm)) (Real.sqrt δ_sm) := by
    have hs_pos : 0 < Real.sqrt δ_sm := Real.sqrt_pos.mpr hδsm_pos
    have hsq2 : (Real.sqrt δ_sm) ^ 2 = δ_sm := Real.sq_sqrt hδsm_pos.le
    rw [edgePhi_crit hs_pos.le (by rw [hsq2]; exact (hδsm_4 hδsm_pos.le (by linarith)).1), hsq2]
    exact mul_pos (pow_pos hs_pos 3) (by linarith [(hδsm_4 hδsm_pos.le (by linarith)).2.2.2.2.2.2.1, sq_pos_of_pos Real.pi_pos])
  -- Uniform combined constant `C_ctr`
  let C_comp0 : ℝ := Cv0 * K4 * 8 ^ 11; let C_pinch : ℝ := 3 * C_comp0 + 1
  let C_Xi : ℝ := |CC| * (1.6 * 3) ^ 3 + |C5|; let C_u : ℝ := Cfj + C_pinch + 1
  let C_ctr : ℝ := max C_Xi C_u
  have hCctr_nn : 0 ≤ C_ctr := by positivity
  have ht_q : Tendsto (fun c : ℝ => c ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  have ht_t : Tendsto (fun c : ℝ => c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  have ht_half : Tendsto (fun c : ℝ => c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  have ht_inv : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      max (3e6 : ℝ) c5 ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ min τ_lim_box τD ∧
      K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧
      4 * c ^ (-(1 / 2 : ℝ)) ≤ 4 * δ_sm ∧
      c⁻¹ ≤ s₀ ∧
      c ^ (-(1 / 3 : ℝ)) ≤ Kz * 2 ∧
      4.8 * c ^ (-(2 / 3 : ℝ)) < ρc ∧
      4.8 * c ^ (-(2 / 3 : ℝ)) < (edgePhi (hankelEdgeM (Real.sqrt δ_sm)) (Real.sqrt δ_sm)) ^ (2 / 3 : ℝ) ∧
      (ellMin + |ctTheta1 ε| + 1) * c ^ (-(1 / 3 : ℝ)) < 0.05 ∧
      24 * c ^ (-(1 / 6 : ℝ)) + |ctTheta1 ε| * c ^ (-(1 / 2 : ℝ)) < 2.55 ∧
      (|BH10| + r₀ * |BH11| + Mθ + 1) * c⁻¹ ≤ 0.05 ∧
      Cv1 * K4 * c ^ (-(7 / 12 : ℝ)) ≤ 0.05 ∧
      Cv2 * K4 * 8 ^ 9 * c ^ (-(5 / 12 : ℝ)) ≤ Real.pi ^ 2 / 48 ∧
      C_comp0 * c ^ (-(17 / 12 : ℝ)) ≤ 0.01 ∧
      C_ctr * c ^ (-(4 / 3 : ℝ)) ≤ 0.05 ∧
      c ^ (-(7 / 6 : ℝ)) ≤ 0.05 ∧
      Cα * c ^ (-(13 / 12 : ℝ)) ≤ 0.05 := by
    have hc1 : ∀ {f : ℝ → ℝ} {a b : ℝ}, Tendsto f atTop (𝓝 0) → 0 < b → ∀ᶠ c in atTop, a * f c ≤ b :=
      fun h hb => by simpa [mul_zero] using (h.const_mul _).eventually (ge_mem_nhds (by simpa using hb))
    have hc2 : ∀ {f : ℝ → ℝ} {a b : ℝ}, Tendsto f atTop (𝓝 0) → 0 < b → ∀ᶠ c in atTop, a * f c < b :=
      fun h hb => by simpa [mul_zero] using (h.const_mul _).eventually (gt_mem_nhds (by simpa using hb))
    refine Eventually.and (eventually_ge_atTop _) ?_
    refine Eventually.and (ht_q.eventually (ge_mem_nhds (lt_min hτlim_pos hτD_pos))) ?_
    refine Eventually.and (hc1 ht_half (by positivity)) ?_
    refine Eventually.and (hc1 ht_half (by positivity)) ?_
    refine Eventually.and (ht_inv.eventually (ge_mem_nhds hs₀_pos)) ?_
    refine Eventually.and (ht_t.eventually (ge_mem_nhds (by positivity))) ?_
    refine Eventually.and (hc2 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)) hρc_pos) ?_
    refine Eventually.and (hc2 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)) (Real.rpow_pos_of_pos hev_edge _)) ?_
    refine Eventually.and (hc2 ht_t (by norm_num)) ?_
    refine Eventually.and (by
      have hm : Tendsto (fun c : ℝ => 24 * c ^ (-(1 / 6 : ℝ)) + |ctTheta1 ε| * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero, add_zero] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul 24).add
          (ht_half.const_mul |ctTheta1 ε|)
      exact hm.eventually (gt_mem_nhds (by norm_num))) ?_
    refine Eventually.and (hc1 ht_inv (by norm_num)) ?_
    refine Eventually.and (hc1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 12)) (by norm_num)) ?_
    refine Eventually.and (hc1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 12)) (by positivity)) ?_
    refine Eventually.and (hc1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17 / 12)) (by norm_num)) ?_
    refine Eventually.and (hc1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)) (by norm_num)) ?_
    refine Eventually.and ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).eventually (ge_mem_nhds (by norm_num))) ?_
    exact hc1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13 / 12)) (by norm_num)
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.mp hc_ev
  refine ⟨C_ctr, max c₀ 3e6, hCctr_nn, le_max_right _ _, fun {c} hc => ?_⟩
  obtain ⟨hc_35, hτ₁_bd, hK4t, h4τ, hcs₀, hKz_c, hρ_bd, hedge_bd, hell_bd, h255_bd, hBH_bd, hv1_bd, hv2_bd, hcomp_bd, hu_bd, hr_bd, hα_bd⟩ :=
    hc₀ c ((le_max_left c₀ 3e6).trans hc)
  have hc3e6 : 3e6 ≤ c := (le_max_left _ _).trans hc_35
  have hc5' : c5 ≤ c := (le_max_right _ _).trans hc_35
  have hc0 : 0 < c := by linarith
  have hc100 : 100 ≤ c := by linarith
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := rpow_neg_quarter_sq hc0
  have hτ₁_box : τ₁ ≤ τ_lim_box := hτ₁_bd.trans (min_le_left _ _)
  have hτ₁_τD : τ₁ ≤ τD := hτ₁_bd.trans (min_le_right _ _)
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hτ₁_box, by
    calc K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 = K4 * c ^ (-(1 / 2 : ℝ)) := by rw [rpow_neg_quarter_sq hc0]
      _ ≤ 1 := hK4t⟩
  set S := concreteBoxS K4 ε c
  obtain ⟨_, _, _, hSΩ, _, _, _, _, hPB, hdom_extra⟩ := concreteBox_spec hvalid
  obtain ⟨⟨φ, hφ_mem, hφ_eq⟩, hφ_node⟩ := hnode c hc5'
  have hφ_err := hφ_node φ hφ_mem hφ_eq
  set a_node : ℝ := ctMu c * φ
  have h223 := two_rpow_23_bounds
  have hneg_a_lo : 3.16 * c ^ (-(2 / 3 : ℝ)) ≤ -a_node := by
    have h23p : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    have hlo : 3.16 ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * (-φ) := by nlinarith only [h223.1, hφ_mem.2]
    calc 3.16 * c ^ (-(2 / 3 : ℝ)) ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * (-φ)) * c ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hlo h23p.le
      _ = -a_node := by unfold a_node ctMu; ring
  have hneg_a_hi : -a_node ≤ 4.8 * c ^ (-(2 / 3 : ℝ)) := by
    have h23p : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    have hhi : (2 : ℝ) ^ (2 / 3 : ℝ) * (-φ) ≤ 4.8 := by nlinarith only [h223.1, h223.2, hφ_mem.1]
    calc -a_node = ((2 : ℝ) ^ (2 / 3 : ℝ) * (-φ)) * c ^ (-(2 / 3 : ℝ)) := by unfold a_node ctMu; ring
      _ ≤ 4.8 * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hhi h23p.le
  have ha_mem_ρ : a_node ∈ Ioo (-ρc) 0 := ⟨by linarith only [hneg_a_hi, hρ_bd], by
    have h23p : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    linarith only [hneg_a_lo, h23p]⟩
  obtain ⟨hτ0_pos, hτ0_phi, hτ0_uniq, hψ_eq, hΞ_eq⟩ := hcfu a_node ha_mem_ρ
  set τ_Ph : ℝ := τ0_cf a_node
  set z_ctr : ℝ := τ_Ph ^ 2
  set L_ctr : ℝ := z_ctr * nfun z_ctr
  have hz_pos : 0 < z_ctr := sq_pos_of_pos hτ0_pos
  have hz_lt_δsm : z_ctr < δ_sm := by
    have hedge_lt : edgePhi (hankelEdgeM τ_Ph) τ_Ph < edgePhi (hankelEdgeM (Real.sqrt δ_sm)) (Real.sqrt δ_sm) := by
      rw [hτ0_phi]
      have ha_pos : 0 < -a_node := by linarith only [ha_mem_ρ.2]
      have hpow_lt : (-a_node) ^ ((3 : ℝ) / 2) <
          ((edgePhi (hankelEdgeM (Real.sqrt δ_sm)) (Real.sqrt δ_sm)) ^ (2 / 3 : ℝ)) ^ ((3 : ℝ) / 2) :=
        Real.rpow_lt_rpow ha_pos.le (by linarith only [hedge_bd, hneg_a_hi]) (by norm_num)
      have hrhs : ((edgePhi (hankelEdgeM (Real.sqrt δ_sm)) (Real.sqrt δ_sm)) ^ (2 / 3 : ℝ)) ^ ((3 : ℝ) / 2) =
          edgePhi (hankelEdgeM (Real.sqrt δ_sm)) (Real.sqrt δ_sm) := by
        rw [← Real.rpow_mul hev_edge.le]; norm_num
      calc (2 / 3 : ℝ) * (-a_node) ^ ((3 : ℝ) / 2) < 1 * (-a_node) ^ ((3 : ℝ) / 2) := by
            nlinarith only [Real.rpow_pos_of_pos ha_pos ((3 : ℝ) / 2)]
        _ < edgePhi (hankelEdgeM (Real.sqrt δ_sm)) (Real.sqrt δ_sm) := by rw [one_mul, ← hrhs]; exact hpow_lt
    have hτ_lt : τ_Ph < Real.sqrt δ_sm := by
      by_contra hle; push Not at hle
      exact absurd (critical_value_strictMonoOn.monotoneOn (Real.sqrt_nonneg _) hτ0_pos.le hle) (not_le_of_gt hedge_lt)
    calc z_ctr = τ_Ph ^ 2 := rfl
      _ < (Real.sqrt δ_sm) ^ 2 := pow_lt_pow_left₀ hτ_lt hτ0_pos.le (by norm_num)
      _ = δ_sm := Real.sq_sqrt hδsm_pos.le
  have hzm4 := hδsm_4 hz_pos.le (by linarith [hz_lt_δsm, hδsm_pos])
  have hdF_bds := one_sub_half_rpow_23 hzm4.2.2.2.2.2.2.1 hzm4.2.2.2.2.2.2.2
  have ha_eq_dF : z_ctr * dF z_ctr ^ 2 = -a_node := by
    have hed : τ_Ph ^ 3 * fF z_ctr = (2 / 3 : ℝ) * (-a_node) ^ ((3 : ℝ) / 2) := by
      rw [← edgePhi_crit hτ0_pos.le hzm4.1, hτ0_phi]
    have hpow23 : ((3 / 2 : ℝ) * (τ_Ph ^ 3 * fF z_ctr)) ^ (2 / 3 : ℝ) = -a_node := by
      rw [hed, show (3 / 2 : ℝ) * ((2 / 3 : ℝ) * (-a_node) ^ ((3 : ℝ) / 2)) = (-a_node) ^ ((3 : ℝ) / 2) by ring,
        ← Real.rpow_mul (by linarith only [ha_mem_ρ.2])]
      norm_num
    have hlhs : ((3 / 2 : ℝ) * (τ_Ph ^ 3 * fF z_ctr)) ^ (2 / 3 : ℝ) = z_ctr * dF z_ctr ^ 2 := by
      have hfpos : 0 < fF z_ctr := by linarith [hzm4.2.2.2.2.2.2.1, sq_pos_of_pos Real.pi_pos]
      have hmul : (3 / 2 : ℝ) * (τ_Ph ^ 3 * fF z_ctr) = τ_Ph ^ 3 * ((3 / 2 : ℝ) * fF z_ctr) := by ring
      rw [hmul, Real.mul_rpow (pow_nonneg hτ0_pos.le 3) (by positivity)]
      have ht3 : (τ_Ph ^ 3) ^ (2 / 3 : ℝ) = z_ctr := by
        rw [← Real.rpow_natCast τ_Ph 3, ← Real.rpow_mul hτ0_pos.le,
          show ((3 : ℕ) : ℝ) * (2 / 3 : ℝ) = 2 by norm_num, Real.rpow_two]
      have hd2 : dF z_ctr ^ 2 = ((3 / 2 : ℝ) * fF z_ctr) ^ (2 / 3 : ℝ) := by
        unfold dF; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
      rw [ht3, hd2]
    linarith
  have hdF_eq : dF z_ctr ^ 2 = ((3 / 2 : ℝ) * fF z_ctr) ^ (2 / 3 : ℝ) := by
    unfold dF; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by linarith [hzm4.2.2.2.2.2.2.1, sq_pos_of_pos Real.pi_pos])]; norm_num
  have hz_scale : 2 * c ^ (-(2 / 3 : ℝ)) ≤ z_ctr ∧ z_ctr ≤ 10 * c ^ (-(2 / 3 : ℝ)) := by
    rw [hdF_eq] at ha_eq_dF
    have h23p : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    constructor
    · have h1 : z_ctr * ((3 / 2 : ℝ) * fF z_ctr) ^ (2 / 3 : ℝ) ≤ z_ctr * 1.4 :=
        mul_le_mul_of_nonneg_left hdF_bds.2 hz_pos.le
      linarith only [h1, ha_eq_dF, hneg_a_lo, h23p]
    · have h1 : z_ctr * (1 / 2 : ℝ) ≤ z_ctr * ((3 / 2 : ℝ) * fF z_ctr) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hdF_bds.1 hz_pos.le
      linarith only [h1, ha_eq_dF, hneg_a_hi, h23p]
  have hpi2_bds : (9 : ℝ) < Real.pi ^ 2 ∧ Real.pi ^ 2 < 10 :=
    ⟨by nlinarith only [Real.pi_gt_three, Real.pi_pos], by nlinarith only [Real.pi_lt_d2, Real.pi_pos]⟩
  have hL_scale : 1 * c ^ (-(2 / 3 : ℝ)) ≤ L_ctr ∧ L_ctr ≤ 12 * c ^ (-(2 / 3 : ℝ)) := by
    constructor
    · have h5 : 0.5 ≤ nfun z_ctr := by linarith only [hzm4.2.2.2.2.1, hpi2_bds.1]
      have h1 : z_ctr * 0.5 ≤ z_ctr * nfun z_ctr := mul_le_mul_of_nonneg_left h5 hz_pos.le
      linarith only [h1, hz_scale.1]
    · have h1 : nfun z_ctr ≤ 1 := by linarith only [hzm4.2.2.2.2.2.1, hpi2_bds.2]
      have h2 : z_ctr * nfun z_ctr ≤ z_ctr * 1 := mul_le_mul_of_nonneg_left h1 hz_pos.le
      linarith only [h2, hz_scale.2, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
  have hT_ctr : |c / Real.pi ^ 2 * Real.exp L_ctr - ctDelta5 ε c| ≤ C_ctr * c⁻¹ := by
    have h1 := langer_node_exp_bound hc0 hφ_mem hφ_err hΞ_eq (hankelEdgeM_eq hτ0_pos.le hzm4.1).symm
      hΞ0 hΞ1 hΞ2 (hCC a_node (by rw [abs_of_neg (by linarith [hneg_a_lo, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))])]; linarith)).2
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hc0.le))
  let I : Set ℝ := Ioo (L_ctr / 2) (2 * L_ctr)
  let J : Set ℝ := Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ)))
  have h_rect_sub : I ×ˢ J ⊆ concretePhaseDom ellMin ε c :=
    center_rect_sub_phaseDom hc0 hL_scale.1 hL_scale.2 hell_bd h255_bd
  have hS_V_bounds : ∀ p ∈ concretePhaseDom ellMin ε c,
      100 / 95 ≤ S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ∧
      S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ≤ 100 / 92 := fun _ hp =>
    fctWarp_S_V_bounds hc0 hellMin_pos.le hSΩ hp
  have hV_eq : ∀ p ∈ concretePhaseDom ellMin ε c,
      concreteTau0 ε c S p = Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) *
        S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) := fun p hp =>
    fctWarp_V_eq hc0 hellMin_pos.le hSΩ hp (hdom_extra p hp).2.1.1
      (by simpa only [rpow_neg_quarter_sq hc0] using (hdom_extra p hp).2.2.1)
  -- Center approximation `|-fctKappa c * ã(L_ctr, 0) - airyZero 1| ≤ C_ctr c^(-4/3)` via FJ(1) + compensator pinch
  have h_u_ctr : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) - airyZero 1| ≤
      C_ctr * c ^ (-(4 / 3 : ℝ)) := by
    have hL_mem_dom : (L_ctr, (0 : ℝ)) ∈ concretePhaseDom ellMin ε c :=
      h_rect_sub ⟨⟨by linarith, by linarith⟩, ⟨by linarith [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))], by positivity⟩⟩
    have hKz_L : c⁻¹ ≤ Kz * z_ctr := by
      have hc13 : c⁻¹ = c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
      rw [hc13]
      calc c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) ≤ (Kz * 2) * c ^ (-(2 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hKz_c (Real.rpow_nonneg hc0.le _)
        _ = Kz * (2 * c ^ (-(2 / 3 : ℝ))) := by ring
        _ ≤ Kz * z_ctr := mul_le_mul_of_nonneg_left hz_scale.1 hKz_pos.le
    obtain ⟨z_s, hzs_mem, hzs_eq, _, hfj_bd⟩ := hfj hz_pos hzm4.2.2.1 (inv_nonneg.mpr hc0.le) hcs₀ hKz_L
    change fjFcrit nfun θt c⁻¹ z_s = L_ctr - c⁻¹ * ctTheta1 ε at hzs_eq
    change |fjAfold fF θt c⁻¹ z_s - (z_ctr * dF z_ctr ^ 2 + c⁻¹ * (-(outerTheta ε (Real.sqrt z_ctr) / (Real.sqrt z_ctr * dF z_ctr))))| ≤
      Cfj * (c⁻¹) ^ 2 at hfj_bd
    -- Exact match with `airyZero 1` via `ctPsi` and `ctUhat`
    have hct_eq : -fctKappa c * (z_ctr * dF z_ctr ^ 2 + c⁻¹ * (-(outerTheta ε (Real.sqrt z_ctr) / (Real.sqrt z_ctr * dF z_ctr)))) =
        airyZero 1 := by
      have ha_pos : 0 < -a_node := by linarith [Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
      have hτ_sq' : Real.sqrt z_ctr = τ_Ph := Real.sqrt_sq hτ0_pos.le
      have hdF_pos : 0 < dF z_ctr := by
        unfold dF; exact Real.rpow_pos_of_pos (by linarith [hzm4.2.2.2.2.2.2.1, sq_pos_of_pos Real.pi_pos]) _
      have hden_eq : Real.sqrt z_ctr * dF z_ctr = Real.sqrt (-a_node) := by
        rw [← ha_eq_dF, Real.sqrt_mul hz_pos.le, Real.sqrt_sq hdF_pos.le]
      have hctTau : ctTau0 a_node = τ_Ph := by
        have hspec := Classical.epsilon_spec (p := fun τ : ℝ => 0 < τ ∧ edgePhi (hankelEdgeM τ) τ = (2 / 3 : ℝ) * (-a_node) ^ ((3 : ℝ) / 2))
          ⟨τ_Ph, hτ0_pos, hτ0_phi⟩
        exact hτ0_uniq (ctTau0 a_node) hspec.1 hspec.2
      have hpsi_node : outerTheta ε (Real.sqrt z_ctr) / (Real.sqrt z_ctr * dF z_ctr) = ctPsi ε a_node := by
        rw [hden_eq, hτ_sq', ← hctTau]; rfl
      rw [ha_eq_dF, hpsi_node, ← hφ_eq]
      unfold ctUhat fctKappa ctLam a_node ctMu
      have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      have hc_eq1 : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add hc0]; norm_num
      have hc_eq2 : c ^ (2 / 3 : ℝ) * c⁻¹ = c ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      have h2_eq1 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      calc -((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * (-((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * φ) +
            c⁻¹ * -ctPsi ε ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * φ))
          = ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) * φ +
              (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (c ^ (2 / 3 : ℝ) * c⁻¹) * ctPsi ε ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * φ) := by ring
        _ = φ + (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * ctPsi ε ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * φ) := by
            rw [hc_eq1, hc_eq2, h2_eq1]; ring
    -- Interval `[τ_lo, τ_hi] = [√z_ctr / 2, 2 √z_ctr]` for the pinch
    let τ_0 := Real.sqrt z_s
    let τ_1 := concreteTau0 ε c S (L_ctr, 0)
    have hzs_pos : 0 < z_s := by linarith [hzs_mem.1]
    have hτ0_s_pos : 0 < τ_0 := Real.sqrt_pos.mpr hzs_pos
    have hτ1_pos : 0 < τ_1 := hPB.pos (L_ctr, 0) hL_mem_dom
    have hτ1_lt2 : τ_1 < 2 * τ₁ := (hdom_extra (L_ctr, 0) hL_mem_dom).1
    -- Common `fjFcrit` monotonicity & interval properties on `Icc (z_ctr / 4) (4 * z_ctr)`
    have hFcrit_ge : ∀ z ∈ Icc (z_ctr / 4) (4 * z_ctr), Real.pi ^ 2 / 48 ≤ deriv (fjFcrit nfun θt c⁻¹) z := by
      intro z hz
      have hzm : 0 ≤ z ∧ z ≤ 4 * δ_sm := ⟨by linarith [hz.1], by linarith [hz.2, hz_lt_δsm]⟩
      have hzm4' := hδsm_4 hzm.1 hzm.2
      have hzr0 : z ∈ Icc (-r₀) r₀ := ⟨by linarith, hzm4'.2.1⟩
      have hnd := (contDiffOn_nfun.contDiffAt (isOpen_Ioo.mem_nhds (hK_Ioo hzr0))).differentiableAt (by norm_num)
      have hθd := (hθ_jc.1.contDiffAt (isOpen_Ioo.mem_nhds (hK_Yint hzr0))).differentiableAt (by norm_num)
      have hθ1d := (hθ_d1.contDiffAt (isOpen_Ioo.mem_nhds (hK_Yint hzr0))).differentiableAt (by norm_num)
      have hH1d : DifferentiableAt ℝ (fjH1 θt) z := (hθd.const_mul 3).add ((differentiableAt_id.const_mul 2).fun_mul hθ1d)
      have hlin := hnd.hasDerivAt.add (hH1d.hasDerivAt.const_mul c⁻¹)
      have hder := (hasDerivAt_id' z).fun_mul hlin
      change HasDerivAt (fjFcrit nfun θt c⁻¹) _ z at hder
      rw [hder.deriv, one_mul]
      have h0b : |fjH1 θt z| ≤ |BH10| := by
        simpa [Real.norm_eq_abs, fjH1] using (le_trans (hBH10 z hzr0) (le_abs_self _))
      have h1b : |deriv (fjH1 θt) z| ≤ |BH11| := by
        have hd : HasDerivAt (fjH1 θt) (5 * deriv θt z + 2 * z * deriv (deriv θt) z) z := by
          change HasDerivAt (fun w => 3 * θt w + 2 * w * deriv θt w) _ z
          exact ((hθd.hasDerivAt.const_mul 3).fun_add (((hasDerivAt_id' z).const_mul 2).fun_mul hθ1d.hasDerivAt)).congr_deriv (by ring)
        rw [hd.deriv]; simpa [Real.norm_eq_abs] using (le_trans (hBH11 z hzr0) (le_abs_self _))
      have hz_r0 : |z| ≤ r₀ := abs_le.mpr hzr0
      have hsum : |fjH1 θt z + z * deriv (fjH1 θt) z| ≤ |BH10| + r₀ * |BH11| :=
        (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
      have hcinv_bd : c⁻¹ * |fjH1 θt z + z * deriv (fjH1 θt) z| ≤ Real.pi ^ 2 / 48 := by
        have hsum1 : |fjH1 θt z + z * deriv (fjH1 θt) z| ≤ |BH10| + r₀ * |BH11| + Mθ + 1 := by
          linarith only [hsum, hMθ]
        calc c⁻¹ * |fjH1 θt z + z * deriv (fjH1 θt) z| ≤ c⁻¹ * (|BH10| + r₀ * |BH11| + Mθ + 1) :=
              mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr hc0.le)
          _ ≤ 0.05 := by rw [mul_comm]; exact hBH_bd
          _ ≤ Real.pi ^ 2 / 48 := by linarith only [hpi2_bds.1]
      have habs := abs_le.mp (show |c⁻¹ * (fjH1 θt z + z * deriv (fjH1 θt) z)| ≤ Real.pi ^ 2 / 48 by
        rwa [abs_mul, abs_of_pos (inv_pos.mpr hc0)])
      have hsum_eq : (nfun + fun y => c⁻¹ * fjH1 θt y) z + z * (deriv nfun z + c⁻¹ * deriv (fjH1 θt) z) =
          (nfun z + z * deriv nfun z) + c⁻¹ * (fjH1 θt z + z * deriv (fjH1 θt) z) := by
        simp only [Pi.add_apply]; ring
      linarith only [hsum_eq, hzm4'.2.2.2.1, habs.1]
    -- Show `τ_1^2 ∈ [z_ctr / 4, 4 * z_ctr]` directly from `box.crit (L_ctr, 0)`
    set v01 := vTotal StripKernelChoice.star K4 c 0 τ₁
    have hv01_cd := (hthD_bd hK4 hc0 hτ₁_τD).2
    have hτ1_sq_lt4 : τ_1 ^ 2 < 4 * δ_sm := by
      have : τ_1 ^ 2 < (2 * τ₁) ^ 2 := pow_lt_pow_left₀ hτ1_lt2 hτ1_pos.le (by norm_num)
      rw [show (2 * τ₁) ^ 2 = 4 * τ₁ ^ 2 by ring, hτ₁_sq] at this; linarith [h4τ]
    have hτ1_4_lt : τ_1 ^ 2 ≤ 4 * δ_sm := hτ1_sq_lt4.le
    have hτ1_le12 : |τ_1| ≤ 12 * τ₁ := by rw [abs_of_pos hτ1_pos]; linarith
    have hPhi1_deriv_eq : ∀ τ : ℝ, 0 < τ → τ ^ 2 ≤ 4 * δ_sm →
        HasDerivAt (fun t => concretePhiTilde K4 ε c t (L_ctr, 0))
          (((L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (τ ^ 2)) + c⁻¹ * deriv (fctThetaD v01) τ) τ ∧
        fctPhTau (concretePhiTilde K4 ε c) τ (L_ctr, 0) =
          ((L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (τ ^ 2)) + c⁻¹ * deriv (fctThetaD v01) τ := fun τ hτp hτ4 => by
      have hm4 := hδsm_4 (sq_nonneg τ) hτ4
      have hτ_le2 : τ ≤ 2 := by
        have h14 : τ ^ 2 ≤ 4 := by linarith only [hm4.2.1, hr₀_pos, hr₀_14]
        by_contra hlt
        have hgt : (4 : ℝ) < τ ^ 2 := by nlinarith only [not_le.mp hlt]
        linarith only [h14, hgt]
      have hd0 := concretePhi0_hasDerivAt (K4 := K4) (ε := ε) (c := c) (L1 := L_ctr) hε hτp hm4.1 hτ_le2
      have hdD := ((hv01_cd.differentiable (by simp)).differentiableAt.hasDerivAt (x := τ)).const_mul c⁻¹
      have hd1 : HasDerivAt (fun t => concretePhiTilde K4 ε c t (L_ctr, 0))
          (((L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (τ ^ 2)) + c⁻¹ * deriv (fctThetaD v01) τ) τ := by
        refine (hd0.add hdD).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
        simp only [Pi.add_apply]; unfold concretePhiTilde concretePhiLambda; dsimp only [v01]; ring
      have hph : HasDerivAt (fun t => fctPh (concretePhiTilde K4 ε c) (t, (L_ctr, (0 : ℝ))))
          (fctPhTau (concretePhiTilde K4 ε c) τ (L_ctr, 0)) τ := by
        have hf : DifferentiableAt ℝ (fctPh (concretePhiTilde K4 ε c)) (τ, (L_ctr, (0 : ℝ))) :=
          (hPB.contDiffAt_ph hτp hL_mem_dom).differentiableAt (by simp)
        have hlin : HasDerivAt (fun t : ℝ => (t, (L_ctr, (0 : ℝ)))) (1, (0, 0)) τ :=
          (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ (L_ctr, (0 : ℝ)))
        have hc := hf.hasFDerivAt.comp_hasDerivAt τ hlin
        exact hc.congr_deriv (rfl)
      exact ⟨hd1, hph.unique hd1⟩
    have hτ1_mem : τ_1 ^ 2 ∈ Icc (z_ctr / 4) (4 * z_ctr) := by
      have hcrit := (hPhi1_deriv_eq τ_1 hτ1_pos hτ1_4_lt).2
      rw [hPB.crit (L_ctr, 0) hL_mem_dom] at hcrit
      have hFcrit_eq : fjFcrit nfun θt c⁻¹ (τ_1 ^ 2) = L_ctr - c⁻¹ * ctTheta1 ε + c⁻¹ * deriv (fctThetaD v01) τ_1 := by linarith
      have hm4 := hδsm_4 (sq_nonneg τ_1) hτ1_4_lt
      have hzr0 : τ_1 ^ 2 ∈ Icc (-r₀) r₀ := ⟨by linarith [sq_nonneg τ_1, hr₀_pos], hm4.2.1⟩
      have hH1_le : |fjH1 θt (τ_1 ^ 2)| ≤ |BH10| := by
        simpa [Real.norm_eq_abs, fjH1] using (le_trans (hBH10 _ hzr0) (le_abs_self _))
      have hθd_bd : |c⁻¹ * deriv (fctThetaD v01) τ_1| ≤ 0.05 * c ^ (-(2 / 3 : ℝ)) := by
        have hv1 := (hthD_bd hK4 hc0 hτ₁_τD).1 τ_1 hτ1_le12 |>.2.1
        have h54 : c⁻¹ * τ₁ = c ^ (-(5 / 4 : ℝ)) := by rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
        have h712 : c ^ (-(5 / 4 : ℝ)) = c ^ (-(7 / 12 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
        rw [abs_mul, abs_of_pos (inv_pos.mpr hc0)]
        calc c⁻¹ * |deriv (fctThetaD v01) τ_1| ≤ c⁻¹ * (Cv1 * K4 * τ₁) := mul_le_mul_of_nonneg_left hv1 (inv_nonneg.mpr hc0.le)
          _ = Cv1 * K4 * (c ^ (-(7 / 12 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by rw [← h712, ← h54]; ring
          _ ≤ 0.05 * c ^ (-(2 / 3 : ℝ)) := by nlinarith only [hv1_bd, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
      have hc1_bd : |c⁻¹ * ctTheta1 ε| ≤ 0.05 * c ^ (-(2 / 3 : ℝ)) := by
        have hc13 : c⁻¹ = c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
        have h1 : |ctTheta1 ε| * c ^ (-(1 / 3 : ℝ)) ≤ 0.05 := by
          have : |ctTheta1 ε| ≤ ellMin + |ctTheta1 ε| + 1 := by linarith only [hellMin_pos]
          nlinarith only [this, hell_bd, Real.rpow_pos_of_pos hc0 (-(1 / 3 : ℝ))]
        rw [abs_mul, abs_of_pos (inv_pos.mpr hc0), hc13]
        calc c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) * |ctTheta1 ε|
            = (|ctTheta1 ε| * c ^ (-(1 / 3 : ℝ))) * c ^ (-(2 / 3 : ℝ)) := by ring
          _ ≤ 0.05 * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hc0.le _)
      have hcH : |c⁻¹ * fjH1 θt (τ_1 ^ 2)| ≤ 0.25 := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hc0)]
        have : c⁻¹ * |fjH1 θt (τ_1 ^ 2)| ≤ c⁻¹ * (|BH10| + r₀ * |BH11| + Mθ + 1) := by
          have : |fjH1 θt (τ_1 ^ 2)| ≤ |BH10| + r₀ * |BH11| + Mθ + 1 := by
            nlinarith only [hH1_le, hr₀_pos, abs_nonneg BH11, hMθ]
          exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc0.le)
        linarith only [hBH_bd, this]
      have hH_le : -(0.25 : ℝ) ≤ c⁻¹ * fjH1 θt (τ_1 ^ 2) ∧ c⁻¹ * fjH1 θt (τ_1 ^ 2) ≤ 0.25 := abs_le.mp hcH
      have hc1_le := abs_le.mp hc1_bd; have hθd_le := abs_le.mp hθd_bd
      have h23p : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
      constructor
      · by_contra hlt; push Not at hlt
        have hup : fjFcrit nfun θt c⁻¹ (τ_1 ^ 2) ≤ (z_ctr / 4) * (Real.pi ^ 2 / 10 + 0.25) := by
          unfold fjFcrit
          exact mul_le_mul hlt.le (by linarith [hm4.2.2.2.2.2.1, hH_le.2]) (by linarith [hm4.2.2.2.2.1, hH_le.1]) (by linarith)
        have hlo : z_ctr * (Real.pi ^ 2 / 16) - 0.1 * c ^ (-(2 / 3 : ℝ)) ≤ fjFcrit nfun θt c⁻¹ (τ_1 ^ 2) := by
          have hLn : z_ctr * (Real.pi ^ 2 / 16) ≤ L_ctr := mul_le_mul_of_nonneg_left hzm4.2.2.2.2.1 hz_pos.le
          linarith only [hLn, hFcrit_eq, hc1_le.2, hθd_le.1]
        have hgap : (z_ctr / 4) * (Real.pi ^ 2 / 10 + 0.25) < z_ctr * (Real.pi ^ 2 / 16) - 0.1 * c ^ (-(2 / 3 : ℝ)) := by
          nlinarith only [hpi2_bds.1, hpi2_bds.2, hz_scale.1, h23p]
        linarith only [hup, hlo, hgap]
      · by_contra hlt; push Not at hlt
        have hlo : (4 * z_ctr) * (Real.pi ^ 2 / 16 - 0.25) ≤ fjFcrit nfun θt c⁻¹ (τ_1 ^ 2) := by
          unfold fjFcrit
          exact mul_le_mul hlt.le (by linarith [hm4.2.2.2.2.1, hH_le.1]) (by linarith [hpi2_bds.1]) (by positivity)
        have hup : fjFcrit nfun θt c⁻¹ (τ_1 ^ 2) ≤ z_ctr * (Real.pi ^ 2 / 10) + 0.1 * c ^ (-(2 / 3 : ℝ)) := by
          have hLn : L_ctr ≤ z_ctr * (Real.pi ^ 2 / 10) := mul_le_mul_of_nonneg_left hzm4.2.2.2.2.2.1 hz_pos.le
          linarith only [hLn, hFcrit_eq, hc1_le.1, hθd_le.2]
        have hgap : z_ctr * (Real.pi ^ 2 / 10) + 0.1 * c ^ (-(2 / 3 : ℝ)) < (4 * z_ctr) * (Real.pi ^ 2 / 16 - 0.25) := by
          nlinarith only [hpi2_bds.1, hpi2_bds.2, hz_scale.1, h23p]
        linarith
    -- Both `τ_0` and `τ_1` lie in `[τ_lo, τ_hi]` where `τ_lo := Real.sqrt (z_ctr / 4)`, `τ_hi := Real.sqrt (4 * z_ctr)`
    let τ_lo := Real.sqrt (z_ctr / 4)
    let τ_hi := Real.sqrt (4 * z_ctr)
    have hτlo_pos : 0 < τ_lo := Real.sqrt_pos.mpr (by positivity)
    have hτlo_hi : τ_lo ≤ τ_hi := Real.sqrt_le_sqrt (by linarith)
    have hτ0_in : τ_0 ∈ Icc τ_lo τ_hi := ⟨Real.sqrt_le_sqrt hzs_mem.1, Real.sqrt_le_sqrt hzs_mem.2⟩
    have hτ1_in : τ_1 ∈ Icc τ_lo τ_hi :=
      ⟨(Real.sqrt_le_sqrt hτ1_mem.1).trans_eq (Real.sqrt_sq hτ1_pos.le),
       (Real.sqrt_sq hτ1_pos.le).symm ▸ Real.sqrt_le_sqrt hτ1_mem.2⟩
    have hIcc_sq : ∀ {τ : ℝ}, τ ∈ Icc τ_lo τ_hi → τ ^ 2 ∈ Icc (z_ctr / 4) (4 * z_ctr) ∧ 0 < τ ∧ τ ^ 2 ≤ 4 * δ_sm ∧ |τ| ≤ 12 * τ₁ := fun {τ} hτ => by
      have hτp : 0 < τ := lt_of_lt_of_le hτlo_pos hτ.1
      have hsq_lo : z_ctr / 4 ≤ τ ^ 2 := by
        calc z_ctr / 4 = τ_lo ^ 2 := (Real.sq_sqrt (by positivity)).symm
          _ ≤ τ ^ 2 := pow_le_pow_left₀ hτlo_pos.le hτ.1 2
      have hsq_hi : τ ^ 2 ≤ 4 * z_ctr := by
        calc τ ^ 2 ≤ τ_hi ^ 2 := pow_le_pow_left₀ hτp.le hτ.2 2
          _ = 4 * z_ctr := Real.sq_sqrt (by positivity)
      have h4d : τ ^ 2 ≤ 4 * δ_sm := by linarith [hz_lt_δsm]
      have hle2τ : τ ≤ 8 * c ^ (-(1 / 3 : ℝ)) := by
        have h40 : τ ^ 2 ≤ 40 * c ^ (-(2 / 3 : ℝ)) := by linarith [hz_scale.2]
        have h64 : (8 * c ^ (-(1 / 3 : ℝ))) ^ 2 = 64 * c ^ (-(2 / 3 : ℝ)) := by rw [mul_pow, rpow_neg_third_sq hc0]; norm_num
        have hle2 : τ ^ 2 ≤ (8 * c ^ (-(1 / 3 : ℝ))) ^ 2 := by linarith [Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
        by_contra hc'; push Not at hc'; exact absurd (pow_lt_pow_left₀ hc' (by positivity) (by norm_num : 2 ≠ 0)) (not_lt_of_ge hle2)
      have hc13_lt : c ^ (-(1 / 3 : ℝ)) ≤ τ₁ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      exact ⟨⟨hsq_lo, hsq_hi⟩, hτp, h4d, by rw [abs_of_pos hτp]; linarith⟩
    have hτ_rat : ∀ {τ : ℝ}, τ ∈ Icc τ_lo τ_hi → |τ| / τ₁ ≤ 8 * c ^ (-(1 / 12 : ℝ)) := fun {τ} hτ => by
      have hsub := hIcc_sq hτ
      have h64 : (8 * c ^ (-(1 / 3 : ℝ))) ^ 2 = 64 * c ^ (-(2 / 3 : ℝ)) := by rw [mul_pow, rpow_neg_third_sq hc0]; norm_num
      have hle2 : τ ^ 2 ≤ (8 * c ^ (-(1 / 3 : ℝ))) ^ 2 := by linarith [hsub.1.2, hz_scale.2, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
      have hτ8 : |τ| ≤ 8 * c ^ (-(1 / 3 : ℝ)) := by
        rw [abs_of_pos hsub.2.1]; by_contra hc'; push Not at hc'
        exact absurd (pow_lt_pow_left₀ hc' (by positivity) (by norm_num : 2 ≠ 0)) (not_lt_of_ge hle2)
      calc |τ| / τ₁ ≤ (8 * c ^ (-(1 / 3 : ℝ))) / τ₁ := div_le_div_of_nonneg_right hτ8 hτ₁_pos.le
        _ = 8 * c ^ (-(1 / 12 : ℝ)) := by rw [← rpow_third_mul_neg_quarter hc0]; ring
    -- `Φ₀ τ_1 ≤ Φ₀ τ_0`
    have hFcrit_diff : ∀ z ∈ Icc (z_ctr / 4) (4 * z_ctr), DifferentiableAt ℝ (fjFcrit nfun θt c⁻¹) z := fun z hz => by
      have hm4 := hδsm_4 (z := z) (by linarith only [hz.1, hz_pos]) (by linarith only [hz.2, hz_lt_δsm])
      have hzr0 : z ∈ Icc (-r₀) r₀ := ⟨by linarith only [hz.1, hz_pos, hr₀_pos], hm4.2.1⟩
      have hnd := (contDiffOn_nfun.contDiffAt (isOpen_Ioo.mem_nhds (hK_Ioo hzr0))).differentiableAt (by norm_num)
      have hθd := (hθ_jc.1.contDiffAt (isOpen_Ioo.mem_nhds (hK_Yint hzr0))).differentiableAt (by norm_num)
      have hθ1d := (hθ_d1.contDiffAt (isOpen_Ioo.mem_nhds (hK_Yint hzr0))).differentiableAt (by norm_num)
      exact differentiableAt_id.fun_mul (hnd.add (((hθd.const_mul 3).add ((differentiableAt_id.const_mul 2).fun_mul hθ1d)).const_mul c⁻¹))
    have hFcrit_mono : MonotoneOn (fjFcrit nfun θt c⁻¹) (Icc (z_ctr / 4) (4 * z_ctr)) :=
      monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun z hz => (hFcrit_diff z hz).continuousAt.continuousWithinAt)
        (fun z hz => (hFcrit_diff z (interior_subset hz)).differentiableWithinAt)
        (fun z hz => by linarith [hFcrit_ge z (interior_subset hz), sq_pos_of_pos Real.pi_pos])
    have hFcrit_anti_tau : AntitoneOn (fun τ => (L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (τ ^ 2)) (Icc τ_lo τ_hi) := fun τ₁ h1 τ₂ h2 hle => by
      have hsq1 := hIcc_sq h1; have hsq2 := hIcc_sq h2
      have hsq_le : τ₁ ^ 2 ≤ τ₂ ^ 2 := pow_le_pow_left₀ hsq1.2.1.le hle 2
      exact sub_le_sub_left (hFcrit_mono hsq1.1 hsq2.1 hsq_le) _
    have hPhi0_crit : (L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (τ_0 ^ 2) = 0 := by
      have hsq : τ_0 ^ 2 = z_s := Real.sq_sqrt hzs_pos.le
      rw [hsq, hzs_eq, sub_self]
    have hPhi0_max : concretePhiLambda K4 ε c 0 τ_1 L_ctr 0 ≤ concretePhiLambda K4 ε c 0 τ_0 L_ctr 0 :=
      max_at_crit_of_antitone (lo := τ_lo) (hi := τ_hi) (ctr := τ_0)
        (fun τ hτ => by
          have hsub := hIcc_sq hτ
          have h4_τ : τ ^ 2 ≤ 4 := by linarith only [(hδsm_4 (z := τ ^ 2) (sq_nonneg _) hsub.2.2.1).2.1, hr₀_14]
          have hτ_2 : τ ≤ 2 := by
            by_contra hlt
            have : (4 : ℝ) < τ ^ 2 := by nlinarith only [not_le.mp hlt]
            linarith only [h4_τ, this]
          exact concretePhi0_hasDerivAt (K4 := K4) hε hsub.2.1 (hδsm_4 (z := τ ^ 2) (sq_nonneg _) hsub.2.2.1).1 hτ_2)
        hFcrit_anti_tau hPhi0_crit hτ0_in hτ1_in
    -- `Φ₁ τ_0 ≤ Φ₁ τ_1` via strict concavity of `Φ₁` on `[τ_lo, τ_hi]`
    have hv01_cd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (fctThetaD v01)) := (contDiff_infty_iff_deriv.mp hv01_cd).2
    let rhs1 : ℝ → ℝ := fun t => (L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (t ^ 2) + c⁻¹ * deriv (fctThetaD v01) t
    have hPhi1_tau_anti : AntitoneOn rhs1 (Icc τ_lo τ_hi) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
      · intro τ hτ; have hsub := hIcc_sq hτ
        have hsq_da : DifferentiableAt ℝ (fun t : ℝ => t ^ 2) τ := by fun_prop
        have hdF : ContinuousAt (fun t : ℝ => fjFcrit nfun θt c⁻¹ (t ^ 2)) τ :=
          ((hFcrit_diff (τ ^ 2) hsub.1).comp (f := fun t : ℝ => t ^ 2) τ hsq_da).continuousAt
        have hdV := hv01_cd1.continuous.continuousAt (x := τ)
        exact ((continuousAt_const.sub hdF).add (continuousAt_const.mul hdV)).continuousWithinAt
      · intro τ hτ; rw [interior_Icc] at hτ; have hsub := hIcc_sq (Ioo_subset_Icc_self hτ)
        have hsq_da : DifferentiableAt ℝ (fun t : ℝ => t ^ 2) τ := by fun_prop
        have hFc : DifferentiableAt ℝ (fun t : ℝ => fjFcrit nfun θt c⁻¹ (t ^ 2)) τ :=
          (hFcrit_diff (τ ^ 2) hsub.1).comp (f := fun t : ℝ => t ^ 2) τ hsq_da
        have hv1 := hv01_cd1.differentiable (by simp) τ
        exact ((differentiableAt_const _).sub hFc).add (hv1.const_mul c⁻¹) |>.differentiableWithinAt
      · intro τ hτ; rw [interior_Icc] at hτ
        have hsub := hIcc_sq (Ioo_subset_Icc_self hτ)
        have hfd : DifferentiableAt ℝ (fjFcrit nfun θt c⁻¹) (τ ^ 2) := hFcrit_diff (τ ^ 2) hsub.1
        have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
        have hFc_d : HasDerivAt (fun t : ℝ => fjFcrit nfun θt c⁻¹ (t ^ 2)) (deriv (fjFcrit nfun θt c⁻¹) (τ ^ 2) * (2 * τ)) τ :=
          HasDerivAt.comp (h := fun t : ℝ => t ^ 2) τ hfd.hasDerivAt hsq
        have hv1d : HasDerivAt (deriv (fctThetaD v01)) (iteratedDeriv 2 (fctThetaD v01) τ) τ := by
          have hd := (hv01_cd1.differentiable (by simp) τ).hasDerivAt
          rwa [iteratedDeriv_succ, iteratedDeriv_one]
        have htot_d : HasDerivAt rhs1 (-(deriv (fjFcrit nfun θt c⁻¹) (τ ^ 2) * (2 * τ)) + c⁻¹ * iteratedDeriv 2 (fctThetaD v01) τ) τ := by
          change HasDerivAt (fun t => (L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (t ^ 2) + c⁻¹ * deriv (fctThetaD v01) t) _ τ
          exact (((hasDerivAt_const τ (L_ctr - c⁻¹ * ctTheta1 ε)).sub hFc_d).add (hv1d.const_mul c⁻¹)).congr_deriv (by ring)
        rw [htot_d.deriv]
        have hDcrit : Real.pi ^ 2 / 48 ≤ deriv (fjFcrit nfun θt c⁻¹) (τ ^ 2) := hFcrit_ge (τ ^ 2) hsub.1
        have hτ_min : 0.7 * c ^ (-(1 / 3 : ℝ)) ≤ τ := by
          have h1 : 0.5 * c ^ (-(2 / 3 : ℝ)) ≤ z_ctr / 4 := by linarith only [hz_scale.1]
          have h2 : (0.7 * c ^ (-(1 / 3 : ℝ))) ^ 2 ≤ τ ^ 2 := by
            rw [mul_pow, rpow_neg_third_sq hc0]; nlinarith only [h1, hsub.1.1, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
          by_contra hlt; have : τ ^ 2 < (0.7 * c ^ (-(1 / 3 : ℝ))) ^ 2 :=
            pow_lt_pow_left₀ (not_le.mp hlt) hsub.2.1.le (by norm_num)
          linarith only [h2, this]
        have hmain_pos : 1.4 * (Real.pi ^ 2 / 48) * c ^ (-(1 / 3 : ℝ)) ≤ deriv (fjFcrit nfun θt c⁻¹) (τ ^ 2) * (2 * τ) := by
          have hm := mul_le_mul hDcrit (show 1.4 * c ^ (-(1 / 3 : ℝ)) ≤ 2 * τ by linarith only [hτ_min]) (by positivity)
            (by linarith only [hDcrit, sq_pos_of_pos Real.pi_pos])
          linarith only [hm]
        have hv2 := (hthD_bd hK4 hc0 hτ₁_τD).1 τ hsub.2.2.2 |>.2.2.1
        have hrat_le : |τ| / τ₁ ≤ 8 * c ^ (-(1 / 12 : ℝ)) := hτ_rat (Ioo_subset_Icc_self hτ)
        have hv2_bd' : |c⁻¹ * iteratedDeriv 2 (fctThetaD v01) τ| ≤ (Real.pi ^ 2 / 48) * c ^ (-(1 / 3 : ℝ)) := by
          have h9 : (|τ| / τ₁) ^ 9 ≤ 8 ^ 9 * (c ^ (-(1 / 12 : ℝ))) ^ 9 := by
            calc (|τ| / τ₁) ^ 9 ≤ (8 * c ^ (-(1 / 12 : ℝ))) ^ 9 := pow_le_pow_left₀ (by positivity) hrat_le 9
              _ = 8 ^ 9 * (c ^ (-(1 / 12 : ℝ))) ^ 9 := by ring
          have hc9 : (c ^ (-(1 / 12 : ℝ))) ^ 9 = c ^ (-(3 / 4 : ℝ)) := by
            rw [← Real.rpow_natCast _ 9, ← Real.rpow_mul hc0.le]; norm_num
          have hsum_exp : c⁻¹ * c ^ (-(3 / 4 : ℝ)) ≤ c ^ (-(5 / 12 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
            have h74 : c⁻¹ * c ^ (-(3 / 4 : ℝ)) = c ^ (-(17 / 12 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
              rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
            exact h74 ▸ mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (Real.rpow_nonneg hc0.le _)
          rw [abs_mul, abs_of_pos (inv_pos.mpr hc0)]
          calc c⁻¹ * |iteratedDeriv 2 (fctThetaD v01) τ|
              ≤ c⁻¹ * (Cv2 * K4 * (|τ| / τ₁) ^ 9) := mul_le_mul_of_nonneg_left hv2 (inv_nonneg.mpr hc0.le)
            _ ≤ c⁻¹ * (Cv2 * K4 * (8 ^ 9 * c ^ (-(3 / 4 : ℝ)))) := by gcongr; rw [← hc9]; exact h9
            _ = (Cv2 * K4 * 8 ^ 9) * (c⁻¹ * c ^ (-(3 / 4 : ℝ))) := by ring
            _ ≤ (Cv2 * K4 * 8 ^ 9) * (c ^ (-(5 / 12 : ℝ)) * c ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hsum_exp (by positivity)
            _ ≤ (Real.pi ^ 2 / 48) * c ^ (-(1 / 3 : ℝ)) := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hv2_bd (Real.rpow_nonneg hc0.le _)
        linarith [abs_le.mp hv2_bd', hmain_pos]
    have hPhi1_max : concretePhiTilde K4 ε c τ_0 (L_ctr, 0) ≤ concretePhiTilde K4 ε c τ_1 (L_ctr, 0) :=
      max_at_crit_of_antitone (lo := τ_lo) (hi := τ_hi) (ctr := τ_1)
        (fun τ hτ => (hPhi1_deriv_eq τ (hIcc_sq hτ).2.1 (hIcc_sq hτ).2.2.1).1)
        hPhi1_tau_anti (by
          change (L_ctr - c⁻¹ * ctTheta1 ε) - fjFcrit nfun θt c⁻¹ (τ_1 ^ 2) + c⁻¹ * deriv (fctThetaD v01) τ_1 = 0
          rw [← (hPhi1_deriv_eq τ_1 hτ1_pos hτ1_4_lt).2]
          exact hPB.crit (L_ctr, 0) hL_mem_dom)
        hτ1_in hτ0_in
    -- Pinch `|Φ₁(τ_1) - Φ₀(τ_0)| ≤ C_comp0 * c^(-29/12)`
    have h_v_bd : ∀ {τ : ℝ}, τ ∈ Icc τ_lo τ_hi → |c⁻¹ * fctThetaD v01 τ| ≤ C_comp0 * c ^ (-(29 / 12 : ℝ)) := fun {τ} hτ => by
      have hsub := hIcc_sq hτ
      have hv0 := (hthD_bd hK4 hc0 hτ₁_τD).1 τ hsub.2.2.2 |>.1
      have hrat : |τ| / τ₁ ≤ 8 * c ^ (-(1 / 12 : ℝ)) := hτ_rat hτ
      have h11 : (|τ| / τ₁) ^ 11 ≤ 8 ^ 11 * (c ^ (-(1 / 12 : ℝ))) ^ 11 := by
        calc (|τ| / τ₁) ^ 11 ≤ (8 * c ^ (-(1 / 12 : ℝ))) ^ 11 := pow_le_pow_left₀ (by positivity) hrat 11
          _ = _ := by ring
      have hexp : c⁻¹ * τ₁ ^ 2 * (c ^ (-(1 / 12 : ℝ))) ^ 11 = c ^ (-(29 / 12 : ℝ)) := by
        rw [hτ₁_sq, ← Real.rpow_natCast _ 11, ← Real.rpow_mul hc0.le, ← Real.rpow_neg_one c,
          ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      rw [abs_mul, abs_of_pos (inv_pos.mpr hc0)]
      calc c⁻¹ * |fctThetaD v01 τ| ≤ c⁻¹ * (Cv0 * K4 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11) :=
            mul_le_mul_of_nonneg_left hv0 (inv_nonneg.mpr hc0.le)
        _ ≤ c⁻¹ * (Cv0 * K4 * τ₁ ^ 2 * (8 ^ 11 * (c ^ (-(1 / 12 : ℝ))) ^ 11)) := by gcongr
        _ = (Cv0 * K4 * 8 ^ 11) * (c⁻¹ * τ₁ ^ 2 * (c ^ (-(1 / 12 : ℝ))) ^ 11) := by ring
        _ = C_comp0 * c ^ (-(29 / 12 : ℝ)) := by rw [hexp]
    have hPhi_diff : |concretePhiTilde K4 ε c τ_1 (L_ctr, 0) - concretePhiLambda K4 ε c 0 τ_0 L_ctr 0| ≤
        C_comp0 * c ^ (-(29 / 12 : ℝ)) := by
      have e0 : concretePhiTilde K4 ε c τ_0 (L_ctr, 0) - concretePhiLambda K4 ε c 0 τ_0 L_ctr 0 = c⁻¹ * fctThetaD v01 τ_0 := by
        unfold concretePhiTilde concretePhiLambda v01; ring
      have e1 : concretePhiTilde K4 ε c τ_1 (L_ctr, 0) - concretePhiLambda K4 ε c 0 τ_1 L_ctr 0 = c⁻¹ * fctThetaD v01 τ_1 := by
        unfold concretePhiTilde concretePhiLambda v01; ring
      have h0b := abs_le.mp (h_v_bd hτ0_in); have h1b := abs_le.mp (h_v_bd hτ1_in)
      rw [abs_le]; constructor <;> linarith [hPhi0_max, hPhi1_max, e0, e1, h0b.1, h1b.2]
    -- Apply `(3/2 * y)^(2/3)` MVT around `Φ₀(τ_0) ~ c⁻¹`
    have hQ_ge : 0.2 ≤ fjQ fF θt c⁻¹ z_s := by
      have hm4 := hδsm_4 (z := z_s) (by linarith only [hzs_mem.1, hz_pos]) (by linarith only [hzs_mem.2, hz_lt_δsm])
      have hzr0 : z_s ∈ Icc (-r₀) r₀ := ⟨by linarith only [hzs_mem.1, hz_pos, hr₀_pos], hm4.2.1⟩
      have hH0 : |fjH1 θt z_s| ≤ |BH10| := by simpa [Real.norm_eq_abs, fjH1] using le_trans (hBH10 z_s hzr0) (le_abs_self _)
      have hθ0 : |θt z_s| ≤ Mθ := by simpa [Real.norm_eq_abs] using hθ_jc.2 0 (by simp) z_s (hK_Yint hzr0)
      have hQ_eq : 2 * θt z_s + 2 * z_s * deriv θt z_s = fjH1 θt z_s - θt z_s := by unfold fjH1; ring
      have hQb : |c⁻¹ * (2 * θt z_s + 2 * z_s * deriv θt z_s)| ≤ 0.05 := by
        rw [hQ_eq, abs_mul, abs_of_pos (inv_pos.mpr hc0)]
        have : |fjH1 θt z_s - θt z_s| ≤ |BH10| + r₀ * |BH11| + Mθ + 1 := by
          have hab := abs_sub_le (fjH1 θt z_s) 0 (θt z_s)
          simp only [sub_zero, zero_sub, abs_neg] at hab
          have hr01 : 0 ≤ r₀ * |BH11| := mul_nonneg hr₀_pos.le (abs_nonneg BH11)
          linarith only [hab, hH0, hθ0, hr01]
        rw [mul_comm] at hBH_bd
        exact (mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc0.le)).trans hBH_bd
      unfold fjQ
      linarith only [(abs_le.mp hQb).1, hm4.2.2.2.2.2.2.1, hpi2_bds.1]
    have hPhi0_eq_fj : concretePhiLambda K4 ε c 0 τ_0 L_ctr 0 = (2 / 3 : ℝ) * (fjAfold fF θt c⁻¹ z_s) ^ ((3 : ℝ) / 2) := by
      have hm4 := hδsm_4 (z := z_s) (by linarith only [hzs_mem.1, hz_pos]) (by linarith only [hzs_mem.2, hz_lt_δsm])
      have hτ0_sq : τ_0 ^ 2 = z_s := Real.sq_sqrt hzs_pos.le
      rw [concretePhi0_eq hε hτ0_s_pos.le (by rw [hτ0_sq]; exact hm4.1), hτ0_sq, hzs_eq, sub_self, zero_mul, add_zero]
      have hfja_pos : 0 ≤ fjAfold fF θt c⁻¹ z_s := by unfold fjAfold; positivity
      have e1 : (fjAfold fF θt c⁻¹ z_s) ^ ((3 : ℝ) / 2) = z_s ^ ((3 : ℝ) / 2) * ((3 / 2 : ℝ) * fjQ fF θt c⁻¹ z_s) := by
        unfold fjAfold; rw [Real.mul_rpow hzs_pos.le (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith)]; norm_num
      have e2 : z_s ^ ((3 : ℝ) / 2) = τ_0 ^ 3 := by
        rw [← hτ0_sq, ← Real.rpow_natCast τ_0 2, ← Real.rpow_mul hτ0_s_pos.le, ← Real.rpow_natCast τ_0 3]; norm_num
      rw [e1, e2]; ring
    have hfja_lo : 0.2 * c ^ (-(2 / 3 : ℝ)) ≤ fjAfold fF θt c⁻¹ z_s := by
      have hq32 : (0.3 : ℝ) ≤ (3 / 2 : ℝ) * fjQ fF θt c⁻¹ z_s := by linarith
      have hrp : (0.4 : ℝ) ≤ ((3 / 2 : ℝ) * fjQ fF θt c⁻¹ z_s) ^ (2 / 3 : ℝ) := by
        have hpos32 : 0 < (3 / 2 : ℝ) * fjQ fF θt c⁻¹ z_s := by linarith
        have hpow : (0.4 : ℝ) ≤ (0.3 : ℝ) ^ (2 / 3 : ℝ) := by
          by_contra hc'; push Not at hc'
          have h3 := pow_lt_pow_left₀ hc' (by positivity) (by norm_num : 3 ≠ 0)
          have h03 : ((0.3 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (0.3 : ℝ) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
          rw [h03] at h3; norm_num at h3
        exact hpow.trans (Real.rpow_le_rpow (by norm_num) hq32 (by norm_num))
      have hzs_lo : 0.5 * c ^ (-(2 / 3 : ℝ)) ≤ z_s := by linarith [hzs_mem.1, hz_scale.1]
      unfold fjAfold; nlinarith only [hrp, hzs_lo, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
    have hPhi0_lo : 0.04 * c⁻¹ ≤ concretePhiLambda K4 ε c 0 τ_0 L_ctr 0 := by
      rw [hPhi0_eq_fj]
      have hpow : (0.2 * c ^ (-(2 / 3 : ℝ))) ^ (3 / 2 : ℝ) ≤ (fjAfold fF θt c⁻¹ z_s) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hfja_lo (by norm_num)
      have hc32 : (0.2 * c ^ (-(2 / 3 : ℝ))) ^ (3 / 2 : ℝ) = (0.2 : ℝ) ^ (3 / 2 : ℝ) * c⁻¹ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc0.le _), ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
      have h02 : (0.06 : ℝ) ≤ (0.2 : ℝ) ^ (3 / 2 : ℝ) := by
        by_contra hc'; push Not at hc'
        have h2 := pow_lt_pow_left₀ hc' (by positivity) (by norm_num : 2 ≠ 0)
        have h02s : ((0.2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (0.2 : ℝ) ^ 3 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        rw [h02s] at h2; norm_num at h2
      rw [hc32] at hpow
      calc 0.04 * c⁻¹ = (2 / 3 : ℝ) * (0.06 * c⁻¹) := by ring
        _ ≤ (2 / 3 : ℝ) * ((0.2 : ℝ) ^ (3 / 2 : ℝ) * c⁻¹) := by gcongr
        _ ≤ (2 / 3 : ℝ) * (fjAfold fF θt c⁻¹ z_s) ^ ((3 : ℝ) / 2) := by gcongr
    have hcomp_01 : C_comp0 * c ^ (-(29 / 12 : ℝ)) ≤ 0.01 * c⁻¹ := by
      have h29 : c ^ (-(29 / 12 : ℝ)) = c ^ (-(17 / 12 : ℝ)) * c⁻¹ := by rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      rw [h29, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hcomp_bd (inv_nonneg.mpr hc0.le)
    have hPhi1_lo : 0.03 * c⁻¹ ≤ concretePhiTilde K4 ε c τ_1 (L_ctr, 0) := by linarith [hPhi0_lo, (abs_le.mp hPhi_diff).1, hcomp_01]
    have h_lo_y : 0.045 * c⁻¹ ≤ (3 / 2 : ℝ) * concretePhiLambda K4 ε c 0 τ_0 L_ctr 0 ∧
        0.045 * c⁻¹ ≤ (3 / 2 : ℝ) * concretePhiTilde K4 ε c τ_1 (L_ctr, 0) :=
      ⟨by linarith only [hPhi0_lo, inv_nonneg.mpr hc0.le], by linarith only [hPhi1_lo, inv_nonneg.mpr hc0.le]⟩
    have hã_eq : fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) =
        ((3 / 2 : ℝ) * concretePhiTilde K4 ε c τ_1 (L_ctr, 0)) ^ (2 / 3 : ℝ) := rfl
    have hfj_eq : fjAfold fF θt c⁻¹ z_s = ((3 / 2 : ℝ) * concretePhiLambda K4 ε c 0 τ_0 L_ctr 0) ^ (2 / 3 : ℝ) := by
      rw [hPhi0_eq_fj, show (3 / 2 : ℝ) * ((2 / 3 : ℝ) * (fjAfold fF θt c⁻¹ z_s) ^ (3 / 2 : ℝ)) =
        (fjAfold fF θt c⁻¹ z_s) ^ (3 / 2 : ℝ) by ring, ← Real.rpow_mul (by linarith [hfja_lo, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))])]
      norm_num
    have hmvt := rpow_two_thirds_lip (lo := 0.045 * c⁻¹) (by positivity) h_lo_y.2 h_lo_y.1
    have h3_bd : (2 / 3 : ℝ) * (0.045 * c⁻¹) ^ (-(1 / 3 : ℝ)) ≤ 2 * c ^ (1 / 3 : ℝ) := by
      have h045 : (0.045 : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 3 := by
        have hpos : 0 < (0.045 : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
        by_contra hc'; push Not at hc'
        have h3 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num : 3 ≠ 0)
        have he : ((0.045 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 = (0.045 : ℝ)⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num [Real.rpow_neg_one]
        rw [he] at h3; norm_num at h3
      have hcinv13 : (c⁻¹) ^ (-(1 / 3 : ℝ)) = c ^ (1 / 3 : ℝ) := by rw [← Real.rpow_neg_one c, ← Real.rpow_mul hc0.le]; norm_num
      rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr hc0.le), hcinv13]; nlinarith only [h045, Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)]
    have hã_diff : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) - fjAfold fF θt c⁻¹ z_s| ≤ C_pinch * c ^ (-(25 / 12 : ℝ)) := by
      rw [hã_eq, hfj_eq]
      have h1 : |(3 / 2 : ℝ) * concretePhiTilde K4 ε c τ_1 (L_ctr, 0) - (3 / 2 : ℝ) * concretePhiLambda K4 ε c 0 τ_0 L_ctr 0| ≤
          (3 / 2 : ℝ) * (C_comp0 * c ^ (-(29 / 12 : ℝ))) := by
        rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; gcongr
      have hexp25 : c ^ (1 / 3 : ℝ) * c ^ (-(29 / 12 : ℝ)) = c ^ (-(25 / 12 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
      calc _ ≤ (2 / 3 : ℝ) * (0.045 * c⁻¹) ^ (-(1 / 3 : ℝ)) *
              |(3 / 2 : ℝ) * concretePhiTilde K4 ε c τ_1 (L_ctr, 0) - (3 / 2 : ℝ) * concretePhiLambda K4 ε c 0 τ_0 L_ctr 0| := hmvt
        _ ≤ (2 * c ^ (1 / 3 : ℝ)) * ((3 / 2 : ℝ) * (C_comp0 * c ^ (-(29 / 12 : ℝ)))) := mul_le_mul h3_bd h1 (abs_nonneg _) (by positivity)
        _ = 3 * C_comp0 * c ^ (-(25 / 12 : ℝ)) := by rw [← hexp25]; ring
        _ ≤ C_pinch * c ^ (-(25 / 12 : ℝ)) := by
            have := Real.rpow_nonneg hc0.le (-(25 / 12 : ℝ))
            dsimp only [C_pinch]; nlinarith only [this]
    have hκ_pos : 0 < fctKappa c := fctKappa_pos hc0
    have hκ_le : fctKappa c ≤ c ^ (2 / 3 : ℝ) := by
      unfold fctKappa
      have hle : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      nlinarith only [hle, Real.rpow_pos_of_pos hc0 (2 / 3 : ℝ)]
    have htri : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) - airyZero 1| ≤
        fctKappa c * (|fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) - fjAfold fF θt c⁻¹ z_s| +
          |fjAfold fF θt c⁻¹ z_s - (z_ctr * dF z_ctr ^ 2 + c⁻¹ * (-(outerTheta ε (Real.sqrt z_ctr) / (Real.sqrt z_ctr * dF z_ctr))))|) := by
      rw [← hct_eq]
      have e : -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) -
          -fctKappa c * (z_ctr * dF z_ctr ^ 2 + c⁻¹ * (-(outerTheta ε (Real.sqrt z_ctr) / (Real.sqrt z_ctr * dF z_ctr)))) =
          -fctKappa c * ((fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) - fjAfold fF θt c⁻¹ z_s) +
            (fjAfold fF θt c⁻¹ z_s - (z_ctr * dF z_ctr ^ 2 + c⁻¹ * (-(outerTheta ε (Real.sqrt z_ctr) / (Real.sqrt z_ctr * dF z_ctr)))))) := by ring
      rw [e, abs_mul, abs_neg, abs_of_pos hκ_pos]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hκ_pos.le
    have hc_2 : (c⁻¹) ^ 2 = c ^ (-(2 : ℝ)) := by rw [← Real.rpow_neg_one c, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]; norm_num
    have hc_25 : c ^ (-(25 / 12 : ℝ)) ≤ c ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hc_43 : c ^ (2 / 3 : ℝ) * c ^ (-(2 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
    calc _ ≤ c ^ (2 / 3 : ℝ) * (C_pinch * c ^ (-(2 : ℝ)) + Cfj * c ^ (-(2 : ℝ))) := by
            refine htri.trans (mul_le_mul hκ_le ?_ (by positivity) (by positivity))
            have h1 : C_pinch * c ^ (-(25 / 12 : ℝ)) ≤ C_pinch * c ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hc_25 (by dsimp only [C_pinch]; positivity)
            rw [hc_2] at hfj_bd
            linarith only [hã_diff, h1, hfj_bd]
      _ = (C_pinch + Cfj) * (c ^ (2 / 3 : ℝ) * c ^ (-(2 : ℝ))) := by ring
      _ ≤ C_ctr * c ^ (-(4 / 3 : ℝ)) := by
            rw [hc_43]
            have hle : C_pinch + Cfj ≤ C_u := by dsimp only [C_u]; linarith
            exact mul_le_mul_of_nonneg_right (hle.trans (le_max_right _ _)) (Real.rpow_nonneg hc0.le _)
  -- Surjectivity onto `closedBall (airyZero 1, 0) (c ^ (-(7/6)))`
  have h_surj : closedBall (airyZero 1, (0 : ℝ)) (c ^ (-(7 / 6 : ℝ))) ⊆
      fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c S) '' (I ×ˢ J) := by
    intro y hy
    rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero] at hy
    have hy1 : |y.1 - airyZero 1| ≤ c ^ (-(7 / 6 : ℝ)) := (le_max_left _ _).trans hy
    have hy2 : |y.2| ≤ c ^ (-(7 / 6 : ℝ)) := (le_max_right _ _).trans hy
    have hα_bd2 : |y.2 / c ^ (-(2 / 3 : ℝ))| ≤ c ^ (-(1 / 2 : ℝ)) := by
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))), div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
      calc |y.2| ≤ c ^ (-(7 / 6 : ℝ)) := hy2
        _ = c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
    have hα_mem : y.2 / c ^ (-(2 / 3 : ℝ)) ∈ J := by
      have hlt : c ^ (-(1 / 2 : ℝ)) < 3 / 2 * c ^ (-(1 / 2 : ℝ)) := by
        linarith [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
      exact abs_lt.mp (lt_of_le_of_lt hα_bd2 hlt)
    set α : ℝ := y.2 / c ^ (-(2 / 3 : ℝ))
    set Llo : ℝ := 3 / 4 * L_ctr
    set Lhi : ℝ := 3 / 2 * L_ctr
    have hL_pos : 0 < L_ctr := by linarith [hL_scale.1, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
    have hloI : Llo ∈ I := by dsimp only [I, Llo]; exact ⟨by linarith only [hL_pos], by linarith only [hL_pos]⟩
    have hctrI : L_ctr ∈ I := by dsimp only [I]; exact ⟨by linarith only [hL_pos], by linarith only [hL_pos]⟩
    have hhiI : Lhi ∈ I := by dsimp only [I, Lhi]; exact ⟨by linarith only [hL_pos], by linarith only [hL_pos]⟩
    have hα_shift : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0)| ≤ Cα * c ^ (-(5 / 4 : ℝ)) * |α| :=
      fctAtil_alpha_mvt hPB (L := L_ctr) (rJ := 3 / 2 * c ^ (-(1 / 2 : ℝ))) (M := Cα * c ^ (-(5 / 4 : ℝ)))
        (by positivity) (by positivity) (fun t ht => h_rect_sub ⟨hctrI, ht⟩)
        (fun t ht => hCα_bd hK4 hc100 hτ₁_τD (fun p hp => (hdom_extra p hp).1)
          (fun p hp => (hdom_extra p hp).2.2.2.2) hS_V_bounds hV_eq (fun p hp => hPB.atil_pos hp)
          (L_ctr, t) (h_rect_sub ⟨hctrI, ht⟩)) hα_mem
    have hκ_pos : 0 < fctKappa c := fctKappa_pos hc0
    have h_u_α : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, α) - airyZero 1| ≤ 0.1 := by
      have hκ_le : fctKappa c ≤ c ^ (2 / 3 : ℝ) := by
        unfold fctKappa
        have hle : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
        nlinarith only [hle, Real.rpow_pos_of_pos hc0 (2 / 3 : ℝ)]
      have h512 : c ^ (2 / 3 : ℝ) * c ^ (-(5 / 4 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(13 / 12 : ℝ)) := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      have hCα_err : fctKappa c * (Cα * c ^ (-(5 / 4 : ℝ)) * |α|) ≤ 0.05 := by
        calc fctKappa c * (Cα * c ^ (-(5 / 4 : ℝ)) * |α|)
            ≤ c ^ (2 / 3 : ℝ) * (Cα * c ^ (-(5 / 4 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by gcongr
          _ = Cα * c ^ (-(13 / 12 : ℝ)) := by rw [← h512]; ring
          _ ≤ 0.05 := hα_bd
      have hsub : -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, α) - airyZero 1 =
          (-fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, α) -
            fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0))) +
          (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) - airyZero 1) := by ring
      rw [hsub]
      refine (abs_add_le _ _).trans ?_
      have h1 : |-fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, α) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0))| ≤ 0.05 := by
        rw [abs_mul, abs_neg, abs_of_pos hκ_pos]
        exact (mul_le_mul_of_nonneg_left hα_shift hκ_pos.le).trans hCα_err
      linarith [h_u_ctr, hu_bd]
    have hκ_ge : (1 / 1.6 : ℝ) * c ^ (2 / 3 : ℝ) ≤ fctKappa c := by
      unfold fctKappa
      have h2inv : (1 / 1.6 : ℝ) ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), one_div, inv_le_inv₀ (by norm_num) (by positivity)]
        exact h223.2
      exact mul_le_mul_of_nonneg_right h2inv (Real.rpow_nonneg hc0.le _)
    have hL_diff_ge : ∀ {a b : ℝ}, a ≤ b → (∀ L ∈ Icc a b, (L, α) ∈ concretePhaseDom ellMin ε c) →
        (100 / 95 : ℝ) * (b - a) ≤ fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (b, α) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (a, α) := fun hle hsub =>
      fctAtil_L_mvt_ge hPB (α := α) hle hsub (fun L hL => by
        have hp := hsub L (Ioo_subset_Icc_self hL)
        rw [(hdom_extra (L, α) hp).2.2.2.1]; exact (hS_V_bounds (L, α) hp).1)
    have hLlo_ge := hL_diff_ge (a := Llo) (b := L_ctr) (by dsimp only [Llo]; linarith only [hL_pos])
      fun L hL => h_rect_sub ⟨by dsimp only [I, Llo] at *; exact ⟨by linarith only [hL.1, hL_pos], by linarith only [hL.2, hL_pos]⟩, hα_mem⟩
    have hLhi_ge := hL_diff_ge (a := L_ctr) (b := Lhi) (by dsimp only [Lhi]; linarith only [hL_pos])
      fun L hL => h_rect_sub ⟨by dsimp only [I, Lhi] at *; exact ⟨by linarith only [hL.1, hL_pos], by linarith only [hL.2, hL_pos]⟩, hα_mem⟩
    have hc_prod : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hc0]; norm_num
    have hstep1 : 0.16 ≤ -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (Llo, α) -
        (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, α)) := by
      have hge1 : 0.16 ≤ fctKappa c * ((100 / 95 : ℝ) * (L_ctr - Llo)) := by
        dsimp only [Llo]
        calc (0.16 : ℝ) ≤ (1 / 1.6 : ℝ) * (100 / 95 : ℝ) * (1 / 4 : ℝ) := by norm_num
          _ = ((1 / 1.6 : ℝ) * c ^ (2 / 3 : ℝ)) * ((100 / 95 : ℝ) * (1 * c ^ (-(2 / 3 : ℝ)) / 4)) := by
              rw [show ((1 / 1.6 : ℝ) * c ^ (2 / 3 : ℝ)) * ((100 / 95 : ℝ) * (1 * c ^ (-(2 / 3 : ℝ)) / 4)) =
                (1 / 1.6 : ℝ) * (100 / 95 : ℝ) * (1 / 4 : ℝ) * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) by ring, hc_prod]; ring
          _ ≤ fctKappa c * ((100 / 95 : ℝ) * (L_ctr - 3 / 4 * L_ctr)) := mul_le_mul hκ_ge (by gcongr; linarith only [hL_scale.1]) (by positivity) hκ_pos.le
      linarith [mul_le_mul_of_nonneg_left hLlo_ge hκ_pos.le]
    have hstep2 : 0.32 ≤ -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, α) -
        (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (Lhi, α)) := by
      have hge1 : 0.32 ≤ fctKappa c * ((100 / 95 : ℝ) * (Lhi - L_ctr)) := by
        dsimp only [Lhi]
        calc (0.32 : ℝ) ≤ (1 / 1.6 : ℝ) * (100 / 95 : ℝ) * (1 / 2 : ℝ) := by norm_num
          _ = ((1 / 1.6 : ℝ) * c ^ (2 / 3 : ℝ)) * ((100 / 95 : ℝ) * (1 * c ^ (-(2 / 3 : ℝ)) / 2)) := by
              rw [show ((1 / 1.6 : ℝ) * c ^ (2 / 3 : ℝ)) * ((100 / 95 : ℝ) * (1 * c ^ (-(2 / 3 : ℝ)) / 2)) =
                (1 / 1.6 : ℝ) * (100 / 95 : ℝ) * (1 / 2 : ℝ) * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) by ring, hc_prod]; ring
          _ ≤ fctKappa c * ((100 / 95 : ℝ) * (3 / 2 * L_ctr - L_ctr)) := mul_le_mul hκ_ge (by gcongr; linarith only [hL_scale.1]) (by positivity) hκ_pos.le
      linarith [mul_le_mul_of_nonneg_left hLhi_ge hκ_pos.le]
    have hy1_le : y.1 ≤ -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (Llo, y.2 / c ^ (-(2 / 3 : ℝ))) := by
      linarith [(abs_le.mp hy1).2, (abs_le.mp h_u_α).1, hr_bd]
    have hhi_le_y1 : -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (Lhi, y.2 / c ^ (-(2 / 3 : ℝ))) ≤ y.1 := by
      linarith [(abs_le.mp hy1).1, (abs_le.mp h_u_α).2, hr_bd]
    exact hPB.fctChart_surj_of_bracket (I := I) (J := J) (Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))).ne'
      ordConnected_Ioo h_rect_sub hα_mem hloI hhiI (by dsimp only [Llo, Lhi]; linarith only [hL_pos]) hy1_le hhi_le_y1
  refine ⟨⟨ellMin, S, hPB, L_ctr, z_ctr, C_ctr, hellMin_pos,
    fun p hp => (hdom_extra p hp).1,
    fun p hp => by simpa only [rpow_neg_quarter_sq hc0] using (hdom_extra p hp).2.2.1,
    fun p hp => (hdom_extra p hp).2.2.2.1,
    fun p hp => (hdom_extra p hp).2.2.2.2,
    hS_V_bounds, hV_eq, hz_pos, rfl, hL_scale, hT_ctr, h_rect_sub,
    ⟨by linarith [hL_scale.1, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))], by linarith [hL_scale.1, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]⟩,
    h_u_ctr, h_surj⟩, le_rfl, rfl, rfl⟩

/-- **`fct:warp-asymp` (1) chart centering**: uniform `C_ctr, c₀` over `ε = ±1`. -/
theorem fctWarpFJ_center {K4 : ℝ} (hK4 : 1 ≤ K4) :
    ∃ C_ctr c₀ : ℝ, 0 ≤ C_ctr ∧ 3e6 ≤ c₀ ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∃ W : FctWarpChartData K4 ε c, W.C_ctr ≤ C_ctr ∧ W.S = concreteBoxS K4 ε c ∧ W.ellMin = pbellMin := by
  obtain ⟨C1, c1, hC1, hc1, h1⟩ := fctWarpFJ_center_eps hK4 (Or.inl rfl)
  obtain ⟨Cm, cm, hCm, hcm, hm⟩ := fctWarpFJ_center_eps hK4 (Or.inr rfl)
  refine ⟨max C1 Cm, max c1 cm, le_max_of_le_left hC1, (le_max_left c1 cm).trans' hc1, fun hε hc => ?_⟩
  rcases hε with rfl | rfl
  · obtain ⟨W, hW, hS, hE⟩ := h1 ((le_max_left c1 cm).trans hc); exact ⟨W, hW.trans (le_max_left _ _), hS, hE⟩
  · obtain ⟨W, hW, hS, hE⟩ := hm ((le_max_right c1 cm).trans hc); exact ⟨W, hW.trans (le_max_right _ _), hS, hE⟩

/-- info: 'FormalResearch.SignUncertainty.fctWarpFJ_center' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpFJ_center

end FormalResearch.SignUncertainty
