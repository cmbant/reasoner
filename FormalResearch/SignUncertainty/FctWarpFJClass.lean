/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpFJCenter
public import FormalResearch.SignUncertainty.FctInnerB1

/-!
# Chart–class equivalence for `FctWarpSolveStmt` (`fct:warp-asymp` (1))

Connects `FctWarpClass C ε c L₁ α` (`FctWarpZero.lean`) with the centered Langer chart
`W : FctWarpChartData K4 ε c` of `fctWarpFJ_center` (`FctWarpFJCenter.lean`):
* `fctWarpFJ_of_class`: for any `C : ℝ`, all `(L₁, α)` in `FctWarpClass C ε c` lie inside `W`'s
  rectangle `I ×ˢ J` and map into `closedBall (airyZero 1, 0) (c ^ (-(7 / 6 : ℝ)))` for `c` large.
* `fctWarpClass_of_chart`: any `(L₁, α) ∈ I ×ˢ J` whose chart image lies in
  `closedBall (airyZero 1, 0) (Cρ * c ^ (-(4 / 3 : ℝ)))` belongs to `FctWarpClass C_cls ε c`.
* `fctWarpChart_mem_adm`: any `(L₁, α) ∈ I ×ˢ J` mapping into `closedBall (airyZero 1, 0) (c ^ (-(7 / 6 : ℝ)))`
  satisfies `(concreteInnerFamily K4 ε).adm c L₁ α`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped Real
open FormalResearch.Special FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

private lemma ev_mul_rpow_le (a : ℝ) {p : ℝ} (hp : 0 < p) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ c : ℝ in atTop, a * c ^ (-p) ≤ b := by
  have ht : Tendsto (fun c : ℝ => a * c ^ (-p)) atTop (𝓝 0) := by
    simpa [mul_zero] using (tendsto_rpow_neg_atTop hp).const_mul a
  exact ht.eventually (ge_mem_nhds hb)

private lemma ev_mul_rpow_lt (a : ℝ) {p : ℝ} (hp : 0 < p) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ c : ℝ in atTop, a * c ^ (-p) < b := by
  have ht : Tendsto (fun c : ℝ => a * c ^ (-p)) atTop (𝓝 0) := by
    simpa [mul_zero] using (tendsto_rpow_neg_atTop hp).const_mul a
  exact ht.eventually (gt_mem_nhds hb)

lemma fctAtil_L_mvt_abs_le {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}
    (hPB : FctPhaseBox Φ Ω τ0) {α L₁ L₂ MV : ℝ} (_hMV : 0 ≤ MV)
    (hsub : ∀ L ∈ Icc (min L₁ L₂) (max L₁ L₂), (L, α) ∈ Ω)
    (hbd : ∀ L ∈ Ioo (min L₁ L₂) (max L₁ L₂), |fderiv ℝ (fctAtil Φ τ0) (L, α) (1, 0)| ≤ MV) :
    |fctAtil Φ τ0 (L₂, α) - fctAtil Φ τ0 (L₁, α)| ≤ MV * |L₂ - L₁| := by
  have hAux : ∀ {a b : ℝ}, a ≤ b →
      (∀ L ∈ Icc a b, (L, α) ∈ Ω) →
      (∀ L ∈ Ioo a b, |fderiv ℝ (fctAtil Φ τ0) (L, α) (1, 0)| ≤ MV) →
      |fctAtil Φ τ0 (b, α) - fctAtil Φ τ0 (a, α)| ≤ MV * (b - a) := by
    intro a b hle hs hb
    rcases hle.eq_or_lt with rfl | hlt
    · simp
    · have hcont : ContinuousOn (fun L => fctAtil Φ τ0 (L, α)) (Icc a b) := fun L hL =>
        (((hPB.atil_contDiffAt (hs L hL)).differentiableAt (by simp)).continuousAt.comp_of_eq
          ((continuous_id.prodMk continuous_const).continuousAt (x := L)) rfl).continuousWithinAt
      have hderiv : ∀ L ∈ Ioo a b,
          HasDerivAt (fun t => fctAtil Φ τ0 (t, α)) (fderiv ℝ (fctAtil Φ τ0) (L, α) (1, 0)) L := fun L hL => by
        have hf : HasFDerivAt (fctAtil Φ τ0) (fderiv ℝ (fctAtil Φ τ0) (L, α)) (L, α) :=
          ((hPB.atil_contDiffAt (hs L (Ioo_subset_Icc_self hL))).differentiableAt (by simp)).hasFDerivAt
        have hlin : HasDerivAt (fun t : ℝ => (t, α)) (1, (0 : ℝ)) L :=
          (hasDerivAt_id' L).prodMk (hasDerivAt_const L α)
        exact hf.comp_hasDerivAt L hlin
      obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => fctAtil Φ τ0 (t, α)) _ hlt hcont hderiv
      have hsub_pos : 0 < b - a := sub_pos.mpr hlt
      rw [eq_div_iff hsub_pos.ne'] at hslope
      rw [← hslope, abs_mul, abs_of_pos hsub_pos]
      exact mul_le_mul_of_nonneg_right (hb ξ hξ) hsub_pos.le
  rcases le_total L₁ L₂ with hle | hle
  · have hm : min L₁ L₂ = L₁ ∧ max L₁ L₂ = L₂ := ⟨min_eq_left hle, max_eq_right hle⟩
    rw [hm.1, hm.2] at hsub hbd
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hAux hle hsub hbd
  · have hm : min L₁ L₂ = L₂ ∧ max L₁ L₂ = L₁ := ⟨min_eq_right hle, max_eq_left hle⟩
    rw [hm.1, hm.2] at hsub hbd
    rw [abs_sub_comm (fctAtil Φ τ0 (L₂, α)), abs_sub_comm L₂ L₁, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hAux hle hsub hbd

lemma fctWarpChart_mem_adm {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1)
    (hc_box : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim ∧ K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧ 100 ≤ c)
    (W : FctWarpChartData K4 ε c) (hWS : W.S = concreteBoxS K4 ε c) (hWell : W.ellMin = pbellMin)
    {p : ℝ × ℝ}
    (hp : p ∈ Ioo (W.L_ctr / 2) (2 * W.L_ctr) ×ˢ
      Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))))
    (hy : fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p ∈
      closedBall (airyZero 1, (0 : ℝ)) (c ^ (-(7 / 6 : ℝ)))) :
    (concreteInnerFamily K4 ε).adm c p.1 p.2 := by
  have hc0 : 0 < c := by linarith only [hc_box.2.2]
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hc_box.1, by
    rw [rpow_neg_quarter_sq hc0]; exact hc_box.2.1⟩
  have hpDom : p ∈ concretePhaseDom pbellMin ε c := by
    rw [← hWell]; exact W.h_rect_sub hp
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero] at hy
  have hy1 : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p - airyZero 1| ≤
      c ^ (-(7 / 6 : ℝ)) := (le_max_left _ _).trans hy
  have hy2 : |c ^ (-(2 / 3 : ℝ)) * p.2| ≤ c ^ (-(7 / 6 : ℝ)) := (le_max_right _ _).trans hy
  rw [hWS] at hy1
  have hα : |p.2| ≤ c ^ (-(1 / 2 : ℝ)) := by
    have hc23 : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    rw [abs_mul, abs_of_pos hc23] at hy2
    rw [← mul_le_mul_iff_of_pos_left hc23]
    calc c ^ (-(2 / 3 : ℝ)) * |p.2| ≤ c ^ (-(7 / 6 : ℝ)) := hy2
      _ = c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
  exact ⟨hvalid, hpDom, hy1, hα⟩

/-- Forward map (`fct:warp-asymp` (1)): any `(L₁, α)` in `FctWarpClass C ε c` lies in `W`'s
chart rectangle and maps into `closedBall (airyZero 1, 0) (c ^ (-(7 / 6 : ℝ)))` for `c` large. -/
theorem fctWarpFJ_of_class {K4 : ℝ} (hK4 : 1 ≤ K4) (C : ℝ) :
    ∃ C_ctr c₁ : ℝ, 0 ≤ C_ctr ∧ 3e6 ≤ c₁ ∧
      ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₁ ≤ c →
        ∃ W : FctWarpChartData K4 ε c, W.C_ctr ≤ C_ctr ∧ W.S = concreteBoxS K4 ε c ∧ W.ellMin = pbellMin ∧
          ∀ {L1 α : ℝ}, FctWarpClass C ε c L1 α →
            L1 ∈ Ioo (W.L_ctr / 2) (2 * W.L_ctr) ∧
            α ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) ∧
            fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) ∈
              closedBall (airyZero 1, (0 : ℝ)) (c ^ (-(7 / 6 : ℝ))) := by
  obtain ⟨C_ctr, c₀, hCctr_nn, hc₀_3e6, hcenter⟩ := fctWarpFJ_center hK4
  obtain ⟨Cα, hCα_nn, hCα_bd⟩ := fctChart_uAlpha_bound
  have hτD_pos : 0 < (fct_comp_D_part1 StripKernelChoice.star).choose :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1
  have hCL_pos : (0 : ℝ) < Real.pi ^ 2 * (|C| + C_ctr) + 1 := by positivity
  have hcev : ∀ᶠ c : ℝ in atTop,
      c₀ ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      Real.pi ^ 2 * (|C| + C_ctr) * c ^ (-(2 : ℝ)) < (1 / 2 : ℝ) * c ^ (-(2 / 3 : ℝ)) ∧
      |C| * c ^ (-(2 / 3 : ℝ)) < 3 / 2 * c ^ (-(1 / 2 : ℝ)) ∧
      (100 / 92 : ℝ) * (Real.pi ^ 2 * (|C| + C_ctr)) * c ^ (-(4 / 3 : ℝ)) +
        Cα * |C| * c ^ (-(5 / 4 : ℝ)) + C_ctr * c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) ∧
      |C| * c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) := by
    refine Eventually.and (eventually_ge_atTop c₀) ?_
    refine Eventually.and ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (ge_mem_nhds hτD_pos)) ?_
    refine Eventually.and (by
      filter_upwards [eventually_gt_atTop 0,
        ev_mul_rpow_lt (Real.pi ^ 2 * (|C| + C_ctr)) (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (0 : ℝ) < 1 / 2)] with c hc0 hlt
      have h23 : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
      have he : c ^ (-(2 : ℝ)) = c ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      rw [he, ← mul_assoc]
      exact mul_lt_mul_of_pos_right hlt h23) ?_
    refine Eventually.and (by
      filter_upwards [eventually_gt_atTop 0,
        ev_mul_rpow_lt |C| (by norm_num : (0 : ℝ) < 1 / 6) (by norm_num : (0 : ℝ) < 3 / 2)] with c hc0 hlt
      have h12 : 0 < c ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
      have he : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      rw [he, ← mul_assoc]
      exact mul_lt_mul_of_pos_right hlt h12) ?_
    refine Eventually.and (by
      filter_upwards [eventually_gt_atTop 0,
        ev_mul_rpow_le ((100 / 92 : ℝ) * (Real.pi ^ 2 * (|C| + C_ctr)) + C_ctr)
          (by norm_num : (0 : ℝ) < 1 / 6) (by norm_num : (0 : ℝ) < 1 / 2),
        ev_mul_rpow_le (Cα * |C|) (by norm_num : (0 : ℝ) < 1 / 12) (by norm_num : (0 : ℝ) < 1 / 2)] with c hc0 ha hb
      have h76 : 0 < c ^ (-(7 / 6 : ℝ)) := Real.rpow_pos_of_pos hc0 _
      have e43 : c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(7 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have e54 : c ^ (-(5 / 4 : ℝ)) = c ^ (-(1 / 12 : ℝ)) * c ^ (-(7 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      rw [e43, e54]
      nlinarith only [ha, hb, h76]) ?_
    filter_upwards [eventually_gt_atTop 0,
      ev_mul_rpow_le |C| (by norm_num : (0 : ℝ) < 1 / 6) zero_lt_one] with c hc0 ha
    have h76 : 0 < c ^ (-(7 / 6 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    have e43 : c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [e43, ← mul_assoc]
    calc |C| * c ^ (-(1 / 6 : ℝ)) * c ^ (-(7 / 6 : ℝ)) ≤ 1 * c ^ (-(7 / 6 : ℝ)) := by gcongr
      _ = _ := one_mul _
  obtain ⟨cₐ, hcₐ⟩ := Filter.eventually_atTop.mp hcev
  refine ⟨C_ctr, max c₀ (max 3e6 cₐ), hCctr_nn, le_trans (le_max_left _ _) (le_max_right _ _), fun {ε c} hε hc => ?_⟩
  have hcc0 : c₀ ≤ c := (le_max_left _ _).trans hc
  have hccₐ : cₐ ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc3e6 : 3e6 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := by linarith only [hc3e6]
  have hc100 : 100 ≤ c := by linarith only [hc3e6]
  obtain ⟨_, hτD, hL_small, hα_small, hball1, hball2⟩ := hcₐ c hccₐ
  obtain ⟨W, hW_C, hW_S, hW_ell⟩ := hcenter hε hcc0
  refine ⟨W, hW_C, hW_S, hW_ell, fun {L1 α} ⟨hL1_pos, hT1, hα_bd⟩ => ?_⟩
  have hL_ctr_pos : 0 < W.L_ctr := by linarith [W.hL_scale.1, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
  have hT_ctr : |c / Real.pi ^ 2 * Real.exp W.L_ctr - ctDelta5 ε c| ≤ C_ctr * c⁻¹ :=
    W.hT_ctr.trans (mul_le_mul_of_nonneg_right hW_C (inv_nonneg.mpr hc0.le))
  have hL_diff : |L1 - W.L_ctr| ≤ Real.pi ^ 2 * (|C| + C_ctr) * c ^ (-(2 : ℝ)) := by
    have h1 := l1_sub_ctr_of_exp_close hc100 hL1_pos hL_ctr_pos hT1 hT_ctr
    rwa [abs_of_nonneg hCctr_nn] at h1
  have hL_half : |L1 - W.L_ctr| < W.L_ctr / 2 :=
    lt_of_le_of_lt hL_diff (lt_of_lt_of_le hL_small (by linarith only [W.hL_scale.1]))
  have hL_mem : L1 ∈ Ioo (W.L_ctr / 2) (2 * W.L_ctr) := by
    have hab := abs_lt.mp hL_half
    exact ⟨by linarith only [hab.1], by linarith only [hab.2, hL_ctr_pos]⟩
  have hα_mem : α ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) := by
    have h1 : |α| ≤ |C| * c ^ (-(2 / 3 : ℝ)) :=
      hα_bd.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hc0.le _))
    exact abs_lt.mp (lt_of_le_of_lt h1 hα_small)
  refine ⟨hL_mem, hα_mem, ?_⟩
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
  refine max_le ?_ ?_
  · have h12_pos : 0 < c ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    have h_rect : ∀ L ∈ Icc (min W.L_ctr L1) (max W.L_ctr L1),
        (L, (0 : ℝ)) ∈ concretePhaseDom W.ellMin ε c := fun L hL =>
      W.h_rect_sub ⟨⟨by
        rcases le_total W.L_ctr L1 with hle | hle
        · rw [min_eq_left hle] at hL; linarith only [hL.1, hL_ctr_pos]
        · rw [min_eq_right hle] at hL; linarith only [hL.1, hL_mem.1],
        by
        rcases le_total W.L_ctr L1 with hle | hle
        · rw [max_eq_right hle] at hL; linarith only [hL.2, hL_mem.2]
        · rw [max_eq_left hle] at hL; linarith only [hL.2, hL_ctr_pos]⟩,
        ⟨by linarith only [h12_pos], by linarith only [h12_pos]⟩⟩
    have hMV : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0)| ≤
        (100 / 92 : ℝ) * |L1 - W.L_ctr| := by
      refine fctAtil_L_mvt_abs_le W.box (by norm_num) h_rect fun L hL => ?_
      have hp := h_rect L (Ioo_subset_Icc_self hL)
      rw [W.h_dL (L, 0) hp, abs_of_pos (lt_of_lt_of_le (by norm_num) (W.h_S_V_bounds (L, 0) hp).1)]
      exact (W.h_S_V_bounds (L, 0) hp).2
    have hctrI : L1 ∈ Ioo (W.L_ctr / 2) (2 * W.L_ctr) := hL_mem
    have hα_shift : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)| ≤
        Cα * c ^ (-(5 / 4 : ℝ)) * |α| :=
      fctAtil_alpha_mvt W.box (L := L1) (rJ := 3 / 2 * c ^ (-(1 / 2 : ℝ))) (M := Cα * c ^ (-(5 / 4 : ℝ)))
        (by positivity) (by positivity)
        (fun t ht => W.h_rect_sub ⟨hctrI, ht⟩)
        (fun t ht => hCα_bd hK4 hc100 hτD W.h_tau_lt2 W.h_dA W.h_S_V_bounds W.h_V_eq
          (fun p hp => W.box.atil_pos hp) (L1, t) (W.h_rect_sub ⟨hctrI, ht⟩)) hα_mem
    have hκ_pos : 0 < fctKappa c := fctKappa_pos hc0
    have hκ_le : fctKappa c ≤ c ^ (2 / 3 : ℝ) := by
      unfold fctKappa
      have hle : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      nlinarith only [hle, Real.rpow_pos_of_pos hc0 (2 / 3 : ℝ)]
    have hc_43 : c ^ (2 / 3 : ℝ) * c ^ (-(2 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hc_54 : c ^ (2 / 3 : ℝ) * c ^ (-(5 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    have h1 : fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0)| ≤
        (100 / 92 : ℝ) * (Real.pi ^ 2 * (|C| + C_ctr)) * c ^ (-(4 / 3 : ℝ)) := by
      calc fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
            fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0)|
          ≤ c ^ (2 / 3 : ℝ) * ((100 / 92 : ℝ) * (Real.pi ^ 2 * (|C| + C_ctr) * c ^ (-(2 : ℝ)))) :=
            mul_le_mul hκ_le (hMV.trans (mul_le_mul_of_nonneg_left hL_diff (by norm_num)))
              (abs_nonneg _) (Real.rpow_nonneg hc0.le _)
        _ = (100 / 92 : ℝ) * (Real.pi ^ 2 * (|C| + C_ctr)) * (c ^ (2 / 3 : ℝ) * c ^ (-(2 : ℝ))) := by ring
        _ = _ := by rw [hc_43]
    have h2 : fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)| ≤
        Cα * |C| * c ^ (-(5 / 4 : ℝ)) := by
      have hα1 : |α| ≤ |C| * c ^ (-(2 / 3 : ℝ)) :=
        hα_bd.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hc0.le _))
      calc fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
            fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)|
          ≤ c ^ (2 / 3 : ℝ) * (Cα * c ^ (-(5 / 4 : ℝ)) * (|C| * c ^ (-(2 / 3 : ℝ)))) :=
            mul_le_mul hκ_le (hα_shift.trans (mul_le_mul_of_nonneg_left hα1 (by positivity)))
              (abs_nonneg _) (Real.rpow_nonneg hc0.le _)
        _ = Cα * |C| * (c ^ (2 / 3 : ℝ) * c ^ (-(5 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by ring
        _ = _ := by rw [hc_54]
    have h3 : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0) - airyZero 1| ≤
        C_ctr * c ^ (-(4 / 3 : ℝ)) :=
      W.h_u_ctr.trans (mul_le_mul_of_nonneg_right hW_C (Real.rpow_nonneg hc0.le _))
    change |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) - airyZero 1| ≤ _
    have hsplit : -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) - airyZero 1 =
        (-fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0))) +
        ((-fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0))) +
        (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0) - airyZero 1)) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add le_rfl (abs_add_le _ _)).trans ?_
    rw [abs_mul, abs_neg, abs_mul, abs_neg, abs_of_pos hκ_pos]
    linarith only [h1, h2, h3, hball1]
  · change |c ^ (-(2 / 3 : ℝ)) * α| ≤ c ^ (-(7 / 6 : ℝ))
    have hc23 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hc43 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [abs_mul, abs_of_nonneg hc23]
    calc c ^ (-(2 / 3 : ℝ)) * |α| ≤ c ^ (-(2 / 3 : ℝ)) * (|C| * c ^ (-(2 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hα_bd.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hc23)) hc23
      _ = |C| * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by ring
      _ = |C| * c ^ (-(4 / 3 : ℝ)) := by rw [hc43]
      _ ≤ c ^ (-(7 / 6 : ℝ)) := hball2

/-- Converse map (`fct:warp-asymp` (1)): any `(L₁, α) ∈ I ×ˢ J` whose chart image lies in
`closedBall (airyZero 1, 0) (Cρ * c ^ (-(4 / 3 : ℝ)))` belongs to `FctWarpClass C_cls ε c`. -/
theorem fctWarpClass_of_chart {K4 : ℝ} (hK4 : 1 ≤ K4) {C_ctr Cρ : ℝ} (_hCctr : 0 ≤ C_ctr) (hCρ : 0 ≤ Cρ) :
    ∃ C_cls c₁ : ℝ, 0 ≤ C_cls ∧ 3e6 ≤ c₁ ∧
      ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₁ ≤ c →
        ∀ (W : FctWarpChartData K4 ε c), W.C_ctr ≤ C_ctr →
          ∀ {L1 α : ℝ},
            L1 ∈ Ioo (W.L_ctr / 2) (2 * W.L_ctr) →
            α ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) →
            fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) ∈
              closedBall (airyZero 1, (0 : ℝ)) (Cρ * c ^ (-(4 / 3 : ℝ))) →
            FctWarpClass C_cls ε c L1 α := by
  obtain ⟨Cα, hCα_nn, hCα_bd⟩ := fctChart_uAlpha_bound
  obtain ⟨_, _, _, Cα0, _, _, _, hCα0_nn, hth_bd⟩ := thetaD_center_bounds
  have hτD_pos : 0 < (fct_comp_D_part1 StripKernelChoice.star).choose :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1
  let C_α : ℝ := Cα0 * (3 : ℝ) ^ 11 / Real.sqrt 3
  have hCα_nn : 0 ≤ C_α := by positivity
  let C_u_tot : ℝ := Cρ + C_ctr + 1
  let C_L : ℝ := (95 / 100 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) * C_u_tot
  let C_cls : ℝ := max (C_ctr + Real.exp 2 / Real.pi ^ 2 * C_L) Cρ
  have hCcls_nn : 0 ≤ C_cls := le_max_of_le_right hCρ
  have hcev : ∀ᶠ c : ℝ in atTop,
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      12 * c ^ (-(2 / 3 : ℝ)) ≤ 1 ∧
      C_L * c ^ (-(2 : ℝ)) ≤ 1 ∧
      Cρ * c ^ (-(4 / 3 : ℝ)) ≤ (1 / 2 : ℝ) * c ^ (-(7 / 6 : ℝ)) ∧
      2 * Cα * Cρ * c ^ (-(5 / 4 : ℝ)) ≤ (1 / 2 : ℝ) * c ^ (-(7 / 6 : ℝ)) ∧
      3 * c ^ (-(1 / 3 : ℝ)) ≤ 12 * c ^ (-(1 / 4 : ℝ)) ∧
      C_α * Cρ * c ^ (-(25 / 12 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
    refine Eventually.and ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (ge_mem_nhds hτD_pos)) ?_
    refine Eventually.and (ev_mul_rpow_le 12 (by norm_num : (0 : ℝ) < 2 / 3) zero_lt_one) ?_
    refine Eventually.and (ev_mul_rpow_le C_L (by norm_num : (0 : ℝ) < 2) zero_lt_one) ?_
    refine Eventually.and (by
      filter_upwards [eventually_gt_atTop 0,
        ev_mul_rpow_le Cρ (by norm_num : (0 : ℝ) < 1 / 6) (by norm_num : (0 : ℝ) < 1 / 2)] with c hc0 hlt
      have e43 : c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(7 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have h76 : 0 ≤ c ^ (-(7 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
      rw [e43, ← mul_assoc]
      calc Cρ * c ^ (-(1 / 6 : ℝ)) * c ^ (-(7 / 6 : ℝ)) ≤ (1 / 2 : ℝ) * c ^ (-(7 / 6 : ℝ)) := by gcongr) ?_
    refine Eventually.and (by
      filter_upwards [eventually_gt_atTop 0,
        ev_mul_rpow_le (2 * Cα * Cρ) (by norm_num : (0 : ℝ) < 1 / 12) (by norm_num : (0 : ℝ) < 1 / 2)] with c hc0 hlt
      have e54 : c ^ (-(5 / 4 : ℝ)) = c ^ (-(1 / 12 : ℝ)) * c ^ (-(7 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have h76 : 0 ≤ c ^ (-(7 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
      rw [e54, ← mul_assoc]
      calc 2 * Cα * Cρ * c ^ (-(1 / 12 : ℝ)) * c ^ (-(7 / 6 : ℝ)) ≤ (1 / 2 : ℝ) * c ^ (-(7 / 6 : ℝ)) := by gcongr) ?_
    refine Eventually.and (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc1
      have hc0 : 0 ≤ c := by linarith only [hc1]
      have hle : c ^ (-(1 / 3 : ℝ)) ≤ c ^ (-(1 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      have hnn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0 _
      linarith only [hle, hnn]) ?_
    filter_upwards [eventually_gt_atTop 0,
      ev_mul_rpow_le (C_α * Cρ) (by norm_num : (0 : ℝ) < 3 / 4) zero_lt_one] with c hc0 hlt
    have e25 : c ^ (-(25 / 12 : ℝ)) = c ^ (-(3 / 4 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have h43 : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    rw [e25, ← mul_assoc]
    calc C_α * Cρ * c ^ (-(3 / 4 : ℝ)) * c ^ (-(4 / 3 : ℝ)) ≤ 1 * c ^ (-(4 / 3 : ℝ)) := by gcongr
      _ = _ := one_mul _
  obtain ⟨cₐ, hcₐ⟩ := Filter.eventually_atTop.mp hcev
  refine ⟨C_cls, max 3e6 cₐ, hCcls_nn, le_max_left _ _, fun {ε c} _ hc W hW_C {L1 α} hL1 hα hy => ?_⟩
  have hc3e6 : 3e6 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith only [hc3e6]
  have hc100 : 100 ≤ c := by linarith only [hc3e6]
  obtain ⟨hτD, hL12_le1, hCL_le1, hball76, hα54, h3_12, hα25⟩ := hcₐ c ((le_max_right _ _).trans hc)
  have hL_ctr_pos : 0 < W.L_ctr := by linarith [W.hL_scale.1, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
  have hL1_pos : 0 < L1 := by linarith only [hL1.1, hL_ctr_pos]
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero] at hy
  have hy1 : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) - airyZero 1| ≤
      Cρ * c ^ (-(4 / 3 : ℝ)) := (le_max_left _ _).trans hy
  have hy2 : |c ^ (-(2 / 3 : ℝ)) * α| ≤ Cρ * c ^ (-(4 / 3 : ℝ)) := (le_max_right _ _).trans hy
  have hα_cls : |α| ≤ Cρ * c ^ (-(2 / 3 : ℝ)) := by
    have hc23 : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    rw [abs_mul, abs_of_pos hc23] at hy2
    rw [← mul_le_mul_iff_of_pos_left hc23]
    calc c ^ (-(2 / 3 : ℝ)) * |α| ≤ Cρ * c ^ (-(4 / 3 : ℝ)) := hy2
      _ = c ^ (-(2 / 3 : ℝ)) * (Cρ * c ^ (-(2 / 3 : ℝ))) := by
          have : c ^ (-(4 / 3 : ℝ)) = c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
            rw [← Real.rpow_add hc0]; norm_num
          rw [this]; ring
  have hκ_pos : 0 < fctKappa c := fctKappa_pos hc0
  have hκ_le : fctKappa c ≤ c ^ (2 / 3 : ℝ) := by
    unfold fctKappa
    have hle : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    nlinarith only [hle, Real.rpow_pos_of_pos hc0 (2 / 3 : ℝ)]
  have hκ_ge : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = fctKappa c := rfl
  -- Bound `fctKappa c * |∂_α ã(L1, t)| ≤ C_α * c ^ (-(17/12))` for `t ∈ Ioo (-rJ) rJ` with `|t| ≤ |α|`
  have hα_shift : fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
      fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)| ≤ c ^ (-(4 / 3 : ℝ)) := by
    have hrJ_pos : (0 : ℝ) < 3 / 2 * c ^ (-(1 / 2 : ℝ)) := by positivity
    have h_seg_bd : ∀ t ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))),
        t ∈ Icc (min 0 α) (max 0 α) →
        fctKappa c * |fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) (L1, t) (0, 1)| ≤
          C_α * c ^ (-(17 / 12 : ℝ)) := by
      intro t ht ht_seg
      have hp : (L1, t) ∈ concretePhaseDom W.ellMin ε c := W.h_rect_sub ⟨hL1, ht⟩
      have h_sub_box : ∀ y ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))),
          (L1, y) ∈ concretePhaseDom W.ellMin ε c := fun y hy => W.h_rect_sub ⟨hL1, hy⟩
      -- Bound `|ã(L1, t) - ã(L1, α)| ≤ Cα * c^(-5/4) * |t - α|` via `fctAtil_alpha_mvt` twice (`0` pivot)
      have h0t : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)| ≤
          Cα * c ^ (-(5 / 4 : ℝ)) * |t| :=
        fctAtil_alpha_mvt W.box (L := L1) (rJ := 3 / 2 * c ^ (-(1 / 2 : ℝ))) (M := Cα * c ^ (-(5 / 4 : ℝ)))
          (by positivity) hrJ_pos h_sub_box
          (fun y hy => hCα_bd hK4 hc100 hτD W.h_tau_lt2 W.h_dA W.h_S_V_bounds W.h_V_eq
            (fun q hq => W.box.atil_pos hq) (L1, y) (h_sub_box y hy)) ht
      have h0α : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)| ≤
          Cα * c ^ (-(5 / 4 : ℝ)) * |α| :=
        fctAtil_alpha_mvt W.box (L := L1) (rJ := 3 / 2 * c ^ (-(1 / 2 : ℝ))) (M := Cα * c ^ (-(5 / 4 : ℝ)))
          (by positivity) hrJ_pos h_sub_box
          (fun y hy => hCα_bd hK4 hc100 hτD W.h_tau_lt2 W.h_dA W.h_S_V_bounds W.h_V_eq
            (fun q hq => W.box.atil_pos hq) (L1, y) (h_sub_box y hy)) hα
      have ht_abs : |t| ≤ Cρ * c ^ (-(2 / 3 : ℝ)) := by
        have ht_le : |t| ≤ |α| := by
          rcases le_total 0 α with ha0 | ha0
          · rw [min_eq_left ha0, max_eq_right ha0] at ht_seg
            rw [abs_of_nonneg ht_seg.1, abs_of_nonneg ha0]; exact ht_seg.2
          · rw [min_eq_right ha0, max_eq_left ha0] at ht_seg
            rw [abs_of_nonpos ht_seg.2, abs_of_nonpos ha0]; linarith only [ht_seg.1]
        exact ht_le.trans hα_cls
      have hc54 : c ^ (2 / 3 : ℝ) * (c ^ (-(5 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ))) = c ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      have hadm_t : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t) - airyZero 1| ≤
          c ^ (-(7 / 6 : ℝ)) := by
        have htri : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t) -
            fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α)| ≤
            2 * Cα * Cρ * c ^ (-(5 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
          have h0α' : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
              fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α)| ≤
              Cα * c ^ (-(5 / 4 : ℝ)) * |α| := by rw [abs_sub_comm]; exact h0α
          have hadd := (abs_sub_le _ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)) _).trans
            (add_le_add h0t h0α')
          refine hadd.trans ?_
          have h1 : Cα * c ^ (-(5 / 4 : ℝ)) * |t| ≤ Cα * c ^ (-(5 / 4 : ℝ)) * (Cρ * c ^ (-(2 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left ht_abs (by positivity)
          have h2 : Cα * c ^ (-(5 / 4 : ℝ)) * |α| ≤ Cα * c ^ (-(5 / 4 : ℝ)) * (Cρ * c ^ (-(2 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hα_cls (by positivity)
          linarith only [h1, h2]
        have hκ_tri : fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t) -
            fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α)| ≤
            2 * Cα * Cρ * c ^ (-(5 / 4 : ℝ)) := by
          calc fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t) -
                fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α)|
              ≤ c ^ (2 / 3 : ℝ) * (2 * Cα * Cρ * c ^ (-(5 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ))) :=
                mul_le_mul hκ_le htri (abs_nonneg _) (Real.rpow_nonneg hc0.le _)
            _ = 2 * Cα * Cρ * (c ^ (2 / 3 : ℝ) * (c ^ (-(5 / 4 : ℝ)) * c ^ (-(2 / 3 : ℝ)))) := by ring
            _ = 2 * Cα * Cρ * c ^ (-(5 / 4 : ℝ)) := by rw [hc54]
        have hsp : -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t) - airyZero 1 =
            (-fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t) -
              fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α))) +
            (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) - airyZero 1) := by ring
        rw [hsp]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_neg, abs_of_pos hκ_pos]
        linarith only [hκ_tri, hy1, hball76, hα54]
      have hsize := fctAtil_size hc100 (û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t))
        rfl hadm_t FormalResearch.Special.airyZero_one (W.box.atil_pos hp)
      have htau_le : concreteTau0 ε c W.S (L1, t) ≤ 3 * c ^ (-(1 / 3 : ℝ)) := by
        rw [W.h_V_eq (L1, t) hp]
        have hsq : Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t)) ≤
            2 * c ^ (-(1 / 3 : ℝ)) := by
          have hs := Real.sqrt_le_sqrt hsize.2
          have h4 : Real.sqrt (4 * c ^ (-(2 / 3 : ℝ))) = 2 * c ^ (-(1 / 3 : ℝ)) := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
              Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le]; norm_num
          linarith only [hs, h4]
        have hVb := W.h_S_V_bounds (L1, t) hp
        calc Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t)) *
              W.S.V ((concreteEll1 ε c L1, 1, t), W.S.A (concreteEll1 ε c L1, 1, t))
            ≤ (2 * c ^ (-(1 / 3 : ℝ))) * (100 / 92 : ℝ) :=
              mul_le_mul hsq hVb.2 (by linarith only [hVb.1]) (by positivity)
          _ ≤ 3 * c ^ (-(1 / 3 : ℝ)) := by nlinarith only [Real.rpow_pos_of_pos hc0 (-(1 / 3 : ℝ))]
      have htau_pos : 0 < concreteTau0 ε c W.S (L1, t) := W.box.pos (L1, t) hp
      have htau12 : |concreteTau0 ε c W.S (L1, t)| ≤ 12 * c ^ (-(1 / 4 : ℝ)) := by
        rw [abs_of_pos htau_pos]; exact htau_le.trans h3_12
      have hth_t := ((hth_bd hK4 hc0 hτD).1 (concreteTau0 ε c W.S (L1, t)) htau12).2.2.2
      have hrat : (|concreteTau0 ε c W.S (L1, t)| / c ^ (-(1 / 4 : ℝ))) ^ 11 ≤
          (3 : ℝ) ^ 11 * c ^ (-(11 / 12 : ℝ)) := by
        have hc12 : c ^ (-(1 / 3 : ℝ)) / c ^ (-(1 / 4 : ℝ)) = c ^ (-(1 / 12 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le]; rw [← Real.rpow_add hc0]; norm_num
        have htau_abs_le : |concreteTau0 ε c W.S (L1, t)| ≤ 3 * c ^ (-(1 / 3 : ℝ)) := by
          rw [abs_of_pos htau_pos]
          exact htau_le
        have h1 : |concreteTau0 ε c W.S (L1, t)| / c ^ (-(1 / 4 : ℝ)) ≤ 3 * c ^ (-(1 / 12 : ℝ)) := by
          rw [← hc12, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right htau_abs_le (Real.rpow_nonneg hc0.le _)
        calc (|concreteTau0 ε c W.S (L1, t)| / c ^ (-(1 / 4 : ℝ))) ^ 11 ≤ (3 * c ^ (-(1 / 12 : ℝ))) ^ 11 :=
              pow_le_pow_left₀ (by positivity) h1 11
          _ = (3 : ℝ) ^ 11 * c ^ (-(11 / 12 : ℝ)) := by
              rw [mul_pow]; congr 1
              rw [← Real.rpow_natCast (c ^ (-(1 / 12 : ℝ))) 11, ← Real.rpow_mul hc0.le]; norm_num
      have hsqrt_ge : Real.sqrt 3 * c ^ (-(1 / 3 : ℝ)) ≤
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t)) := by
        have hs := Real.sqrt_le_sqrt hsize.1
        have h3eq : Real.sqrt (3 * c ^ (-(2 / 3 : ℝ))) = Real.sqrt 3 * c ^ (-(1 / 3 : ℝ)) := by
          rw [Real.sqrt_mul (by norm_num)]; congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le]; norm_num
        linarith only [hs, h3eq]
      rw [W.h_dA (L1, t) hp, abs_div, abs_mul, abs_of_pos (inv_pos.mpr hc0),
        abs_of_pos (Real.sqrt_pos.mpr (W.box.atil_pos hp))]
      have hth_comb : |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S (L1, t))| ≤
          Cα0 * (3 : ℝ) ^ 11 * c ^ (-(17 / 12 : ℝ)) := by
        have hc17 : (c ^ (-(1 / 4 : ℝ))) ^ 2 * c ^ (-(11 / 12 : ℝ)) = c ^ (-(17 / 12 : ℝ)) := by
          rw [rpow_neg_quarter_sq hc0, ← Real.rpow_add hc0]; norm_num
        calc |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S (L1, t))|
            ≤ Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * (|concreteTau0 ε c W.S (L1, t)| / c ^ (-(1 / 4 : ℝ))) ^ 11 := hth_t
          _ ≤ Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * ((3 : ℝ) ^ 11 * c ^ (-(11 / 12 : ℝ))) := by gcongr
          _ = Cα0 * (3 : ℝ) ^ 11 * ((c ^ (-(1 / 4 : ℝ))) ^ 2 * c ^ (-(11 / 12 : ℝ))) := by ring
          _ = Cα0 * (3 : ℝ) ^ 11 * c ^ (-(17 / 12 : ℝ)) := by rw [hc17]
      have hnum : c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S (L1, t))| ≤
          Cα0 * (3 : ℝ) ^ 11 * c ^ (-(29 / 12 : ℝ)) := by
        have hc29 : c⁻¹ * c ^ (-(17 / 12 : ℝ)) = c ^ (-(29 / 12 : ℝ)) := by
          rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
        calc c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S (L1, t))|
            ≤ c⁻¹ * (Cα0 * (3 : ℝ) ^ 11 * c ^ (-(17 / 12 : ℝ))) := by gcongr
          _ = Cα0 * (3 : ℝ) ^ 11 * (c⁻¹ * c ^ (-(17 / 12 : ℝ))) := by ring
          _ = _ := by rw [hc29]
      have hdiv_bd : c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S (L1, t))| /
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t)) ≤
          C_α * c ^ (-(25 / 12 : ℝ)) := by
        have hc25 : c ^ (-(29 / 12 : ℝ)) / c ^ (-(1 / 3 : ℝ)) = c ^ (-(25 / 12 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
        calc c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S (L1, t))| /
              Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t))
            ≤ (Cα0 * (3 : ℝ) ^ 11 * c ^ (-(29 / 12 : ℝ))) / (Real.sqrt 3 * c ^ (-(1 / 3 : ℝ))) :=
              div_le_div₀ (by positivity) hnum (by positivity) hsqrt_ge
          _ = (Cα0 * (3 : ℝ) ^ 11 / Real.sqrt 3) * (c ^ (-(29 / 12 : ℝ)) / c ^ (-(1 / 3 : ℝ))) := by ring
          _ = C_α * c ^ (-(25 / 12 : ℝ)) := by rw [hc25]
      have hc17' : c ^ (2 / 3 : ℝ) * c ^ (-(25 / 12 : ℝ)) = c ^ (-(17 / 12 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc fctKappa c * (c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S (L1, t))| /
            Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t)))
          ≤ c ^ (2 / 3 : ℝ) * (C_α * c ^ (-(25 / 12 : ℝ))) :=
            mul_le_mul hκ_le hdiv_bd (by positivity) (Real.rpow_nonneg hc0.le _)
        _ = C_α * (c ^ (2 / 3 : ℝ) * c ^ (-(25 / 12 : ℝ))) := by ring
        _ = C_α * c ^ (-(17 / 12 : ℝ)) := by rw [hc17']
    -- Apply MVT on `[min 0 α, max 0 α]`
    have hcont : ContinuousOn (fun t => fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, t))
        (Icc (min 0 α) (max 0 α)) := fun t ht => by
      have ht' : t ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) :=
        ⟨lt_of_lt_of_le (lt_min (neg_lt_zero.mpr hrJ_pos) hα.1) ht.1,
         lt_of_le_of_lt ht.2 (max_lt hrJ_pos hα.2)⟩
      exact (((W.box.atil_contDiffAt (W.h_rect_sub ⟨hL1, ht'⟩)).differentiableAt (by simp)).continuousAt.comp_of_eq
        ((continuous_const.prodMk continuous_id).continuousAt (x := t)) rfl).continuousWithinAt
    have hMVT_α : |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)| ≤
        (C_α * c ^ (-(17 / 12 : ℝ)) / fctKappa c) * |α| := by
      rcases le_total 0 α with hle | hle
      · rcases hle.eq_or_lt with rfl | hlt
        · simp
        · have hmin : min 0 α = 0 := min_eq_left hle
          have hmax : max 0 α = α := max_eq_right hle
          rw [hmin, hmax] at hcont
          have hder : ∀ t ∈ Ioo 0 α, HasDerivAt (fun s => fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, s))
              (fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) (L1, t) (0, 1)) t := fun t ht => by
            have ht' : t ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) :=
              ⟨by linarith only [ht.1, hrJ_pos], by linarith only [ht.2, hα.2]⟩
            have hf := ((W.box.atil_contDiffAt (p := (L1, t)) (W.h_rect_sub ⟨hL1, ht'⟩)).differentiableAt (by simp)).hasFDerivAt
            exact hf.comp_hasDerivAt t ((hasDerivAt_const t L1).prodMk (hasDerivAt_id' t))
          obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
            (fun s => fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, s)) _ hlt hcont hder
          have hξ_mem : ξ ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) :=
            ⟨by linarith only [hξ.1, hrJ_pos], by linarith only [hξ.2, hα.2]⟩
          have hξ_bd := h_seg_bd ξ hξ_mem (by rw [hmin, hmax]; exact Ioo_subset_Icc_self hξ)
          have hsub_pos : 0 < α - 0 := sub_pos.mpr hlt
          rw [eq_div_iff hsub_pos.ne'] at hslope
          rw [← hslope, sub_zero, abs_mul, abs_of_pos hlt]
          refine mul_le_mul_of_nonneg_right ((le_div_iff₀ hκ_pos).mpr (by rw [mul_comm]; exact hξ_bd)) hle
      · rcases hle.eq_or_lt with hEq | hlt
        · subst hEq; simp
        · have hmin : min 0 α = α := min_eq_right hle
          have hmax : max 0 α = 0 := max_eq_left hle
          rw [hmin, hmax] at hcont
          have hder : ∀ t ∈ Ioo α 0, HasDerivAt (fun s => fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, s))
              (fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) (L1, t) (0, 1)) t := fun t ht => by
            have ht' : t ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) :=
              ⟨by linarith only [ht.1, hα.1], by linarith only [ht.2, hrJ_pos]⟩
            have hf := ((W.box.atil_contDiffAt (p := (L1, t)) (W.h_rect_sub ⟨hL1, ht'⟩)).differentiableAt (by simp)).hasFDerivAt
            exact hf.comp_hasDerivAt t ((hasDerivAt_const t L1).prodMk (hasDerivAt_id' t))
          obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
            (fun s => fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, s)) _ hlt hcont hder
          have hξ_mem : ξ ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) :=
            ⟨by linarith only [hξ.1, hα.1], by linarith only [hξ.2, hrJ_pos]⟩
          have hξ_bd := h_seg_bd ξ hξ_mem (by rw [hmin, hmax]; exact Ioo_subset_Icc_self hξ)
          have hsub_pos : 0 < 0 - α := sub_pos.mpr hlt
          rw [eq_div_iff hsub_pos.ne'] at hslope
          rw [abs_sub_comm, ← hslope, abs_mul, abs_of_pos hsub_pos, show 0 - α = |α| from by
            rw [abs_of_neg hlt]; ring]
          refine mul_le_mul_of_nonneg_right ((le_div_iff₀ hκ_pos).mpr (by rw [mul_comm]; exact hξ_bd)) (abs_nonneg α)
    have hc25' : c ^ (-(17 / 12 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(25 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)|
        ≤ fctKappa c * ((C_α * c ^ (-(17 / 12 : ℝ)) / fctKappa c) * (Cρ * c ^ (-(2 / 3 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hMVT_α.trans (mul_le_mul_of_nonneg_left hα_cls (by positivity))) hκ_pos.le
      _ = C_α * Cρ * (c ^ (-(17 / 12 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by
          have := hκ_pos.ne'; field_simp
      _ = C_α * Cρ * c ^ (-(25 / 12 : ℝ)) := by rw [hc25']
      _ ≤ c ^ (-(4 / 3 : ℝ)) := hα25
  -- Now compare `L1` and `W.L_ctr` using MVT lower bound `(100/95)` in `L`
  have h_u_ctr : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0) - airyZero 1| ≤
      C_ctr * c ^ (-(4 / 3 : ℝ)) :=
    W.h_u_ctr.trans (mul_le_mul_of_nonneg_right hW_C (Real.rpow_nonneg hc0.le _))
  have hκ_L_diff : fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
      fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0)| ≤
      C_u_tot * c ^ (-(4 / 3 : ℝ)) := by
    have hsp : -fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0)) =
        (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) - airyZero 1) -
        (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0) - airyZero 1) +
        fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)) := by ring
    have h1 := congrArg abs hsp
    rw [abs_mul, abs_neg, abs_of_pos hκ_pos] at h1
    rw [h1]
    have t1 := abs_add_le
      ((-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) - airyZero 1) -
        (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0) - airyZero 1))
      (fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)))
    have t2 := abs_sub
      (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) - airyZero 1)
      (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0) - airyZero 1)
    have t3 : |fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0))| =
        fctKappa c * |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0)| := by
      rw [abs_mul, abs_of_pos hκ_pos]
    dsimp only [C_u_tot]
    linarith only [t1, t2, t3, hy1, h_u_ctr, hα_shift]
  have hMV_lo : (100 / 95 : ℝ) * |L1 - W.L_ctr| ≤
      |fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (L1, 0) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) (W.L_ctr, 0)| := by
    have h0_mem : (0 : ℝ) ∈ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) :=
      ⟨by linarith [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))], by positivity⟩
    have hsub : ∀ {a b : ℝ}, min W.L_ctr L1 ≤ a → b ≤ max W.L_ctr L1 → a ≤ b →
        ∀ L ∈ Icc a b, (L, (0 : ℝ)) ∈ concretePhaseDom W.ellMin ε c := fun ha hb _ L hL =>
      W.h_rect_sub ⟨⟨by
        rcases le_total W.L_ctr L1 with hle | hle
        · rw [min_eq_left hle] at ha; linarith only [hL.1, ha, hL_ctr_pos]
        · rw [min_eq_right hle] at ha; linarith only [hL.1, ha, hL1.1],
        by
        rcases le_total W.L_ctr L1 with hle | hle
        · rw [max_eq_right hle] at hb; linarith only [hL.2, hb, hL1.2]
        · rw [max_eq_left hle] at hb; linarith only [hL.2, hb, hL_ctr_pos]⟩, h0_mem⟩
    rcases le_total W.L_ctr L1 with hle | hle
    · have hs := hsub (a := W.L_ctr) (b := L1) (min_le_left _ _) (le_max_right _ _) hle
      have hge := fctAtil_L_mvt_ge W.box hle hs fun L hL => by
        have hp := hs L (Ioo_subset_Icc_self hL)
        rw [W.h_dL (L, 0) hp]; exact (W.h_S_V_bounds (L, 0) hp).1
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hge.trans (le_abs_self _)
    · have hs := hsub (a := L1) (b := W.L_ctr) (min_le_right _ _) (le_max_left _ _) hle
      have hge := fctAtil_L_mvt_ge W.box hle hs fun L hL => by
        have hp := hs L (Ioo_subset_Icc_self hL)
        rw [W.h_dL (L, 0) hp]; exact (W.h_S_V_bounds (L, 0) hp).1
      rw [abs_sub_comm L1 W.L_ctr, abs_of_nonneg (sub_nonneg.mpr hle), abs_sub_comm]
      exact hge.trans (le_abs_self _)
  have hL_diff : |L1 - W.L_ctr| ≤ C_L * c ^ (-(2 : ℝ)) := by
    have hc2_pos : 0 < c ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    have h1 : fctKappa c * ((100 / 95 : ℝ) * |L1 - W.L_ctr|) ≤ C_u_tot * c ^ (-(4 / 3 : ℝ)) :=
      (mul_le_mul_of_nonneg_left hMV_lo hκ_pos.le).trans hκ_L_diff
    have h2 : (100 / 95 : ℝ) * |L1 - W.L_ctr| ≤ C_u_tot * c ^ (-(4 / 3 : ℝ)) / fctKappa c :=
      (le_div_iff₀ hκ_pos).mpr (by rw [mul_comm]; exact h1)
    have hc43_div : c ^ (-(4 / 3 : ℝ)) / c ^ (2 / 3 : ℝ) = c ^ (-(2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    have h3 : C_u_tot * c ^ (-(4 / 3 : ℝ)) / fctKappa c = (2 : ℝ) ^ (2 / 3 : ℝ) * C_u_tot * c ^ (-(2 : ℝ)) := by
      rw [← hκ_ge]
      have h2p : (2 : ℝ) ^ (-(2 / 3 : ℝ)) = ((2 : ℝ) ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
      calc C_u_tot * c ^ (-(4 / 3 : ℝ)) / ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ))
          = (2 : ℝ) ^ (2 / 3 : ℝ) * C_u_tot * (c ^ (-(4 / 3 : ℝ)) / c ^ (2 / 3 : ℝ)) := by
              rw [h2p]; field_simp
        _ = (2 : ℝ) ^ (2 / 3 : ℝ) * C_u_tot * c ^ (-(2 : ℝ)) := by rw [hc43_div]
    rw [h3] at h2
    calc |L1 - W.L_ctr| = (95 / 100 : ℝ) * ((100 / 95 : ℝ) * |L1 - W.L_ctr|) := by ring
      _ ≤ (95 / 100 : ℝ) * ((2 : ℝ) ^ (2 / 3 : ℝ) * C_u_tot * c ^ (-(2 : ℝ))) := by gcongr
      _ = C_L * c ^ (-(2 : ℝ)) := by dsimp only [C_L]; ring
  have hL_ctr_le1 : W.L_ctr ≤ 1 := W.hL_scale.2.trans hL12_le1
  have hT_ctr : |c / Real.pi ^ 2 * Real.exp W.L_ctr - ctDelta5 ε c| ≤ C_ctr * c⁻¹ :=
    W.hT_ctr.trans (mul_le_mul_of_nonneg_right hW_C (inv_nonneg.mpr hc0.le))
  have hT1 := exp_sub_ctr_of_l1_close hc100 hL_ctr_le1 hL_diff hCL_le1 hT_ctr
  refine ⟨hL1_pos, hT1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hc0.le)),
    hα_cls.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hc0.le _))⟩

/-- info: 'FormalResearch.SignUncertainty.fctWarpFJ_of_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpFJ_of_class

/-- info: 'FormalResearch.SignUncertainty.fctWarpClass_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpClass_of_chart

end FormalResearch.SignUncertainty
