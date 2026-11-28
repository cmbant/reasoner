/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinRSq
public import FormalResearch.SignUncertainty.FctExactIbp
public import FormalResearch.SignUncertainty.FctWarpTailBounds
public import FormalResearch.SignUncertainty.FctWarpLeftMidBand
public import FormalResearch.SignUncertainty.FctWarpSqOuter
public import FormalResearch.SignUncertainty.FctSplittingDescent
public import FormalResearch.SignUncertainty.FctWg1Win

/-!
# Airy-window asymptotic `(fct:warp-win)` for `ctWwarp` (`fct:warp-asymp` (2), item 1)

Proves the fixed Airy window lower bound `fct_warp_win_bound` for `normDensity (ctWwarp ...)` on
`L ∈ (fctWarpL1 h ε c, Sw * c^{-2/3}]` using:
* exact zero cancellation `warpSqDensity_at_L1` (`fctWarpI = 0`) before dividing by `L - L₁`;
* continuous Airy-square divided difference `[A](û_L, û_1)` via `airySq_divided_diff_bound`;
* uniform `S.V`-based slope matching `win_uhat_slope_approx` (`fctKappa c * warpTauStar = c^{2/3}/ceCs`);
* `win_RSqIn_bounds` (`O(c^{-1/2} (L - L₁))`), `warpSqOut_mvt_bound`, `warpRightTailDensity_bound`,
  and `warpLeftTailDensity_mid_bound`.

Also provides `win_arg_g1_sub_uhat` and `win_vhat_sub_a1_of_delta_ge` for `fct:physical-positive` (i).

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctSymA
open FormalResearch.SignUncertainty.FctSym

namespace FormalResearch.SignUncertainty

/-! ### 1. Airy-window variable and continuous Airy quotient -/

/-- The Airy-window spectral parameter `û_L = -κ_c * ã(L, α)` (`-v̂(L)` in the paper). -/
noncomputable def winUhat (K4 ε c α L : ℝ) : ℝ :=
  -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (L, α)

/-- The paper's `v̂(L) = -û_L`. -/
noncomputable def winVhat (K4 ε c α L : ℝ) : ℝ := -winUhat K4 ε c α L

/-- Continuous extension of `Ai(u)² / (a₁ - u)` (`Ai(-v)² / (v - |a₁|)` for `v = -u`). -/
noncomputable def winAiryQuot (u : ℝ) : ℝ := -(dslope airyAi (airyZero 1) u * airyAi u)

lemma winAiryQuot_eq_div {u : ℝ} (hu : u ≠ airyZero 1) :
    winAiryQuot u = airyAi u ^ 2 / (airyZero 1 - u) := by
  unfold winAiryQuot
  rw [dslope_of_ne _ hu, slope_def_field, airyAi_airyZero, sub_zero]
  have hne1 : u - airyZero 1 ≠ 0 := sub_ne_zero.mpr hu
  have hne2 : airyZero 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  field_simp [hne1, hne2]
  ring

lemma winAiryQuot_at_zero : winAiryQuot (airyZero 1) = 0 := by
  simp [winAiryQuot, airyAi_airyZero]

lemma winAiryQuot_nonneg_of_le {u : ℝ} (hu : u ≤ airyZero 1) : 0 ≤ winAiryQuot u := by
  rcases eq_or_lt_of_le hu with rfl | hlt
  · rw [winAiryQuot_at_zero]
  · rw [winAiryQuot_eq_div hlt.ne]
    exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr hu)

lemma winAiryQuot_eq_ceG1_mul (u : ℝ) :
    ceG1 (airyZero 1) u * (airyZero 1 - u) = winAiryQuot u := by
  rcases eq_or_ne u (airyZero 1) with rfl | hne
  · simp [winAiryQuot_at_zero]
  · rw [winAiryQuot_eq_div hne]
    have hsq := ceG1_mul_sub_sq u
    have hne1 : airyZero 1 - u ≠ 0 := sub_ne_zero.mpr hne.symm
    have hsq' : (u - airyZero 1) ^ 2 = (airyZero 1 - u) ^ 2 := by ring
    rw [hsq'] at hsq
    field_simp [hne1]
    linarith [hsq]

lemma winAiryQuot_abs_le {M : ℝ} (hM : |airyZero 1| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, |u| ≤ M → |winAiryQuot u| ≤ C * |u - airyZero 1| := by
  have hcont : ContinuousOn airyAi' (Icc (-M) M) := continuous_airyAi'.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let B0 : ℝ := max B 0
  refine ⟨B0 ^ 2, by positivity, fun {u} hu => ?_⟩
  rcases eq_or_ne u (airyZero 1) with rfl | hne
  · simp [winAiryQuot_at_zero]
  · have hmvt : |airyAi u| ≤ B0 * |u - airyZero 1| := by
      have ha1_b := abs_le.mp hM
      have hu_b := abs_le.mp hu
      have hsub : uIcc (airyZero 1) u ⊆ Icc (-M) M := fun x hx => by
        rw [Set.mem_uIcc] at hx
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨ha1_b.1.trans h1, h2.trans hu_b.2⟩
        · exact ⟨hu_b.1.trans h1, h2.trans ha1_b.2⟩
      have hder : ∀ x ∈ uIcc (airyZero 1) u,
          HasDerivWithinAt airyAi (airyAi' x) (uIcc (airyZero 1) u) x :=
        fun x _ => (hasDerivAt_airyAi x).hasDerivWithinAt
      have hbd : ∀ x ∈ uIcc (airyZero 1) u, ‖airyAi' x‖ ≤ B0 := fun x hx => by
        have hx' := hB x (hsub hx)
        rw [Real.norm_eq_abs] at hx' ⊢
        exact hx'.trans (le_max_left B 0)
      have hm := (convex_uIcc (airyZero 1) u).norm_image_sub_le_of_norm_hasDerivWithin_le
        hder hbd right_mem_uIcc left_mem_uIcc
      rw [Real.norm_eq_abs, Real.norm_eq_abs, airyAi_airyZero, zero_sub, abs_neg, abs_sub_comm] at hm
      exact hm
    rw [winAiryQuot_eq_div hne, abs_div, abs_sq, abs_sub_comm (airyZero 1) u]
    have hpos : 0 < |u - airyZero 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
    calc airyAi u ^ 2 / |u - airyZero 1|
        = |airyAi u| ^ 2 / |u - airyZero 1| := by rw [sq_abs]
      _ ≤ (B0 * |u - airyZero 1|) ^ 2 / |u - airyZero 1| := by gcongr
      _ = B0 ^ 2 * |u - airyZero 1| := by field_simp [hpos.ne']

/-! ### 2. Zero cancellation and continuous Airy-square divided difference -/

lemma warpSqDensity_at_L1 {K4 : ℝ} (h : FctWarpSolveStmt K4) {ε c : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hc : h.choose_spec.choose ≤ c) :
    warpSqDensity K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctXi1 (fctWarpL1 h ε c)) = 0 := by
  have hz : fctWarpI K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) = 0 := fctWarpI_pair h hε hc
  unfold fctWarpI fctWarpIntegrand at hz
  have hint0 : ∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 (fctWarpL1 h ε c)) *
      fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) = 0 := by
    rcases mul_eq_zero.mp hz with hI | h0
    · exact absurd hI Complex.I_ne_zero
    · exact h0
  unfold warpSqDensity
  rw [hint0, Complex.zero_re, mul_zero]

lemma airySq_divided_diff_bound {M : ℝ} (hM : |airyZero 1| ≤ M) :
    ∃ C_A : ℝ, 0 ≤ C_A ∧ ∀ {u u₁ : ℝ}, |u| ≤ M → |u₁| ≤ M → u ≠ u₁ →
      |(airyAi u ^ 2 - airyAi u₁ ^ 2) / (u₁ - u) - winAiryQuot u| ≤ C_A * |u₁ - airyZero 1| := by
  let g : ℝ → ℝ := fun x => airyAi x ^ 2
  let g' : ℝ → ℝ := fun x => 2 * airyAi x * airyAi' x
  let g'' : ℝ → ℝ := fun x => 2 * airyAi' x ^ 2 + 2 * x * airyAi x ^ 2
  have hg_deriv : ∀ x : ℝ, HasDerivAt g (g' x) x := fun x => by
    have h1 := (hasDerivAt_airyAi x).pow 2
    exact h1.congr_deriv (by dsimp [g']; ring)
  have hg'_deriv : ∀ x : ℝ, HasDerivAt g' (g'' x) x := fun x => by
    have h1 := ((hasDerivAt_airyAi x).const_mul 2).mul (hasDerivAt_airyAi' x)
    exact h1.congr_deriv (by dsimp [g', g'']; ring)
  have hg''_cont : Continuous g'' := by
    dsimp [g'']
    exact ((continuous_airyAi'.pow 2).const_mul 2).add
      (((continuous_id.const_mul 2)).mul (continuous_airyAi.pow 2))
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hg''_cont.continuousOn
  let M2_0 : ℝ := max M2 0
  refine ⟨M2_0, le_max_right _ _, fun {u u₁} hu hu₁ hne => ?_⟩
  let D : ℝ → ℝ := fun w => -∫ t in (0 : ℝ)..1, g' (u + t * (w - u))
  have hD_cont : ∀ w : ℝ, Continuous (fun t : ℝ => g' (u + t * (w - u))) := fun w => by
    have hcg' : Continuous g' := (continuous_airyAi.const_mul 2).mul continuous_airyAi'
    exact hcg'.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hD_eq : ∀ {w : ℝ}, w ≠ u → D w = (g u - g w) / (w - u) := fun {w} hwu => by
    let φ : ℝ → ℝ := fun t => g (u + t * (w - u))
    have hφ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt φ ((w - u) * g' (u + t * (w - u))) t := fun t _ => by
      have ha : HasDerivAt (fun s : ℝ => u + s * (w - u)) (w - u) t :=
        (((hasDerivAt_id t).mul_const (w - u)).const_add u).congr_deriv (by ring)
      exact ((hg_deriv _).comp t ha).congr_deriv (by ring)
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ
      (((hD_cont w).const_mul (w - u)).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_const_mul] at hint
    have hφ0 : φ 0 = g u := by simp [φ]
    have hφ1 : φ 1 = g w := by simp [φ]
    rw [hφ1, hφ0] at hint
    have hwu_ne : w - u ≠ 0 := sub_ne_zero.mpr hwu
    dsimp only [D]
    have heq : ∫ t in (0 : ℝ)..1, g' (u + t * (w - u)) = (g w - g u) / (w - u) := by
      field_simp [hwu_ne]; linarith [hint]
    rw [heq]; ring
  have hD_a1 : D (airyZero 1) = winAiryQuot u := by
    rcases eq_or_ne u (airyZero 1) with rfl | hua
    · rw [winAiryQuot_at_zero]
      dsimp only [D]
      have hz : (fun t : ℝ => g' (airyZero 1 + t * (airyZero 1 - airyZero 1))) = fun _ => 0 := by
        ext t; simp [g', airyAi_airyZero]
      rw [hz, intervalIntegral.integral_zero, neg_zero]
    · rw [hD_eq hua.symm, winAiryQuot_eq_div hua]
      dsimp [g]; rw [airyAi_airyZero, zero_pow two_ne_zero, sub_zero]
  have hsub_D : D u₁ - D (airyZero 1) =
      -∫ t in (0 : ℝ)..1, (g' (u + t * (u₁ - u)) - g' (u + t * (airyZero 1 - u))) := by
    dsimp only [D]
    rw [neg_sub_neg, ← neg_sub, intervalIntegral.integral_sub ((hD_cont u₁).intervalIntegrable 0 1)
      ((hD_cont (airyZero 1)).intervalIntegrable 0 1)]
  have hpt_bd : ∀ t ∈ Icc (0 : ℝ) 1,
      |g' (u + t * (u₁ - u)) - g' (u + t * (airyZero 1 - u))| ≤ M2_0 * |u₁ - airyZero 1| := by
    intro t ht
    set x1 : ℝ := u + t * (airyZero 1 - u)
    set x2 : ℝ := u + t * (u₁ - u)
    have hx_mem : ∀ w : ℝ, |w| ≤ M → u + t * (w - u) ∈ Icc (-M) M := fun w hw => by
      have ht0 : 0 ≤ t := ht.1
      have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      have h1 : u + t * (w - u) = (1 - t) * u + t * w := by ring
      rw [h1]
      have hu' := abs_le.mp hu
      have hw' := abs_le.mp hw
      constructor <;> nlinarith
    have hx1M : x1 ∈ Icc (-M) M := hx_mem (airyZero 1) hM
    have hx2M : x2 ∈ Icc (-M) M := hx_mem u₁ hu₁
    have hsub_mem : uIcc x1 x2 ⊆ Icc (-M) M := fun z hz => by
      rw [Set.mem_uIcc] at hz
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hx1M.1.trans h1, h2.trans hx2M.2⟩
      · exact ⟨hx2M.1.trans h1, h2.trans hx1M.2⟩
    have hmvt := (convex_uIcc x1 x2).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hg'_deriv z).hasDerivWithinAt)
      (fun z hz => by
        have hz' := hM2 z (hsub_mem hz)
        rw [Real.norm_eq_abs] at hz' ⊢
        exact hz'.trans (le_max_left M2 0))
      right_mem_uIcc left_mem_uIcc
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (g' x1) (g' x2), abs_sub_comm x1 x2] at hmvt
    have hdx : x2 - x1 = t * (u₁ - airyZero 1) := by dsimp [x1, x2]; ring
    rw [hdx, abs_mul, abs_of_nonneg ht.1] at hmvt
    calc |g' x2 - g' x1| ≤ M2_0 * (t * |u₁ - airyZero 1|) := hmvt
      _ ≤ M2_0 * (1 * |u₁ - airyZero 1|) := by gcongr; exact ht.2
      _ = M2_0 * |u₁ - airyZero 1| := by ring
  have hint_le : |D u₁ - D (airyZero 1)| ≤ M2_0 * |u₁ - airyZero 1| := by
    rw [hsub_D, abs_neg]
    have h01 : (0 : ℝ) ≤ 1 := zero_le_one
    have hib := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := M2_0 * |u₁ - airyZero 1|) fun t ht => by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le h01, Set.mem_Ioc] at ht
        exact hpt_bd t ⟨ht.1.le, ht.2⟩
    simpa [Real.norm_eq_abs] using hib
  rwa [hD_eq hne.symm, hD_a1] at hint_le

/-! ### 3. `winUhat` slope identity and leading coefficient normalization -/

lemma fctKappa_mul_warpTauStar {c : ℝ} (_hc : 0 < c) :
    fctKappa c * warpTauStar = c ^ (2 / 3 : ℝ) / ceCs := by
  unfold fctKappa warpTauStar ceCs
  have h1 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (12 / π ^ 2) ^ (1 / 3 : ℝ) = (π ^ 2 / 3) ^ (-(1 / 3 : ℝ)) := by
    have h2 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) = (1 / 4 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h2, ← Real.mul_rpow (by positivity) (by positivity)]
    have hmul : (1 / 4 : ℝ) * (12 / π ^ 2) = (π ^ 2 / 3)⁻¹ := by field_simp; ring
    rw [hmul, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  rw [show (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (12 / π ^ 2) ^ (1 / 3 : ℝ) =
      ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (12 / π ^ 2) ^ (1 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) by ring, h1,
    Real.rpow_neg (by positivity), inv_mul_eq_div]

private lemma sV_sub_tauStar_le {K4 ε c : ℝ} (hvalid : concreteBoxValid K4 ε c)
    {q : ℝ × ℝ × ℝ} (hq : q ∈ (concreteBoxS K4 ε c).Ω) {Y : ℝ} (hY : Y ∈ Yint) :
    |(concreteBoxS K4 ε c).V (q, Y) - warpTauStar| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
  have hc0 : 0 < c := hvalid.2.2.1
  obtain ⟨_, _, _, _, _, _, hSε, hScV, _, _⟩ := concreteBox_spec hvalid
  have hjc := (concreteBoxS K4 ε c).out.2.2.2.2.2.2.2.2.2.1.2 0 (by norm_num) (q, Y) ⟨hq, hY⟩
  simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs] at hjc
  change |(concreteBoxS K4 ε c).V (q, Y) - dStar⁻¹| ≤ (concreteBoxS K4 ε c).cV * (concreteBoxS K4 ε c).ε at hjc
  rw [← tauStar_eq_dStar_inv, hScV, hSε,
    show (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) by rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num] at hjc
  unfold warpTauStar; rw [← mul_assoc] at hjc; exact hjc

theorem win_uhat_slope_approx {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4)
    {Sw : ℝ} (hSw : 1 ≤ Sw) :
    ∃ (C_κ C_s c₀ : ℝ), 0 ≤ C_κ ∧ 0 ≤ C_s ∧ 15000 ≤ c₀ ∧ ∀ {ε c L : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c → fctWarpL1 h ε c < L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      let L1 := fctWarpL1 h ε c
      let α := fctWarpAlpha h ε c
      let κL := (1 / fctNc h ε c) * |uctCAi| * c ^ (-(5 / 6 : ℝ)) * winP0 K4 ε c L α *
        ((winUhat K4 ε c α L1 - winUhat K4 ε c α L) / (L - L1))
      |κL - ceK / ceCs| ≤ C_κ * c ^ (-(1 / 2 : ℝ)) ∧
      (3 / 4 : ℝ) * (ceK / ceCs) ≤ κL ∧ κL ≤ 2 * (ceK / ceCs) ∧
      |(winUhat K4 ε c α L1 - winUhat K4 ε c α L) - (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1)| ≤
        C_s * c ^ (1 / 6 : ℝ) * (L - L1) := by
  obtain ⟨_, c_wg, _, _, hwg⟩ := win_window_geom_props hK4 h hSw
  obtain ⟨_, _, c_P0, _, _, _, hP0⟩ := win_P0_bounds hK4 h hSw
  obtain ⟨c_Nc, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨C_N, c_N, hCN⟩ := fctSplittingNorm_of_descent (fctDescent_uncond hK4 h)
  let C_V : ℝ := 2 * pbcV * pbC0
  let C_N' : ℝ := 2 * |C_N|
  let K_P : ℝ := (2 * pbcV * pbC0 + pbcV * pbC0 / warpTauStar) * (ceK / ceCs)
  let K_slope : ℝ := K_P + (2 * ceK / ceCs) * (C_V / (warpTauStar / 2))
  let C_κ : ℝ := 2 * K_slope + C_N' * (ceK / ceCs)
  let C_s : ℝ := pbcV * pbC0 * 2 ^ (-(2 / 3 : ℝ))
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_wg ≤ c ∧ c_P0 ≤ c ∧ c_Nc ≤ c ∧ c_N ≤ c ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ warpTauStar / 2 ∧
      C_V / (warpTauStar / 2) * c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧
      K_slope * c ^ (-(1 / 2 : ℝ)) ≤ ceK / ceCs ∧
      C_κ * c ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 * (ceK / ceCs) := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and (eventually_ge_atTop _) (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ ?_)))))))
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds (by have := warpTauStar_ge; positivity))
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (C_V / (warpTauStar / 2))
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds zero_lt_one)
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K_slope
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds (by have := ceK_pos; have := ceCs_pos; positivity))
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C_κ
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds (by have := ceK_pos; have := ceCs_pos; positivity))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_κ, C_s, max 15000 c₀, ?_, ?_, le_max_left _ _, fun {ε c L} hε hc hL1_lt hL_Sw => ?_⟩
  · have := pbcV_nonneg; have := pbC0_nonneg; have := warpTauStar_ge; have := ceK_pos; have := ceCs_pos
    positivity
  · have := pbcV_nonneg; have := pbC0_nonneg; positivity
  obtain ⟨hc15, hcwg, hcP0, hcNc, hcN, hV_half, hV_ratio1, hK_sl, hκ_quart⟩ :=
    hc₀ c ((le_max_right _ _).trans hc)
  have hL1_le : fctWarpL1 h ε c ≤ L := hL1_lt.le
  have hg := hwg hε hcwg hL1_le hL_Sw
  have hP0_L := hP0 hε hcP0 hL1_le hL_Sw
  have hNc_b := hNc ε c hε hcNc
  have hN_b := hCN ε c hε hcN
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set S := concreteBoxS K4 ε c
  have hc0 : 0 < c := hg.hc0
  have hc1 : 1 ≤ c := by linarith only [hc15]
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hg.hτD, hg.hK4τ⟩
  obtain ⟨_, _, _, hSΩ, _, _, _, _, hPB, hbox⟩ := concreteBox_spec hvalid
  have hcont : ContinuousOn (fun x : ℝ => fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (x, α))
      (Icc L1 L) := fun x hx =>
    (((hPB.atil_contDiffAt (hg.hdom_all x hx)).differentiableAt (by simp)).continuousAt.comp_of_eq
      ((continuous_id.prodMk continuous_const).continuousAt (x := x)) rfl).continuousWithinAt
  have hdiff : ∀ x ∈ Ioo L1 L, HasDerivAt
      (fun t : ℝ => fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (t, α))
      (S.V ((concreteEll1 ε c x, 1, α), S.A (concreteEll1 ε c x, 1, α))) x := fun x hx => by
    have hmem := hg.hdom_all x (Ioo_subset_Icc_self hx)
    have hfd := ((hPB.atil_contDiffAt hmem).differentiableAt (by simp)).hasFDerivAt
    have hd1 : HasDerivAt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) ∘ fun t : ℝ => (t, α))
        (fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) (x, α) (1, 0)) x :=
      hfd.comp_hasDerivAt x ((hasDerivAt_id' x).prodMk (hasDerivAt_const x α))
    rwa [(hbox (x, α) hmem).2.2.2.1] at hd1
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope _ _ hL1_lt hcont hdiff
  have hL10 : 0 < L - L1 := sub_pos.mpr hL1_lt
  have hslope_eq : (winUhat K4 ε c α L1 - winUhat K4 ε c α L) / (L - L1) =
      fctKappa c * S.V ((concreteEll1 ε c ξ, 1, α), S.A (concreteEll1 ε c ξ, 1, α)) := by
    have ha_diff : fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α) -
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α) =
        S.V ((concreteEll1 ε c ξ, 1, α), S.A (concreteEll1 ε c ξ, 1, α)) * (L - L1) := by
      rw [hξ_eq, div_mul_cancel₀ _ hL10.ne']
    unfold winUhat
    rw [show -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α) -
        -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α) =
        fctKappa c * (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α) -
          fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)) by ring, ha_diff]
    field_simp [hL10.ne']
  have hq_mem : ∀ {x : ℝ}, x ∈ Icc L1 L → (concreteEll1 ε c x, (1 : ℝ), α) ∈ S.Ω ∧
      S.A (concreteEll1 ε c x, (1 : ℝ), α) ∈ Yint := fun {x} hx => by
    have hm := hg.hdom_all x hx
    refine ⟨?_, ?_⟩
    · rw [hSΩ]; exact concreteEll1_mem_OmT hc0 pbellMin_pos.le hm
    · exact Ioo_subset_Ioo_right (by norm_num) (Ioo_subset_Ioo_left (by norm_num) (hbox (x, α) hm).2.1)
  have hξ_b := sV_sub_tauStar_le hvalid (hq_mem (Ioo_subset_Icc_self hξ_mem)).1
    (hq_mem (Ioo_subset_Icc_self hξ_mem)).2
  have hL_b := sV_sub_tauStar_le hvalid (hq_mem (right_mem_Icc.mpr hL1_le)).1
    (hq_mem (right_mem_Icc.mpr hL1_le)).2
  set qL := (concreteEll1 ε c L, (1 : ℝ), α)
  set Vξ := S.V ((concreteEll1 ε c ξ, (1 : ℝ), α), S.A (concreteEll1 ε c ξ, (1 : ℝ), α))
  set VL := S.V (qL, S.A qL)
  have hVL_lo : warpTauStar / 2 ≤ VL := by
    linarith only [(abs_le.mp (hL_b.trans hV_half)).1]
  have hV_diff : |Vξ - VL| ≤ C_V * c ^ (-(1 / 2 : ℝ)) := by
    calc |Vξ - VL| = |(Vξ - warpTauStar) - (VL - warpTauStar)| := by ring_nf
      _ ≤ |Vξ - warpTauStar| + |VL - warpTauStar| := abs_sub _ _
      _ ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) + pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := add_le_add hξ_b hL_b
      _ = C_V * c ^ (-(1 / 2 : ℝ)) := by dsimp [C_V]; ring
  have hVL_pos : 0 < VL := lt_of_lt_of_le (by have := warpTauStar_ge; positivity) hVL_lo
  have hP_raw := hP0_L.2.2.2.2.2.2
  have hP0_nn : 0 ≤ winP0 K4 ε c L α :=
    le_trans (by have := ceCs_pos; have := Real.pi_pos; positivity) hP0_L.1
  let P_lead : ℝ := |uctCAi| * c ^ (-(5 / 6 : ℝ)) * winP0 K4 ε c L α * (fctKappa c * VL)
  have hP_lead_bd : |P_lead| ≤ 2 * (ceK / ceCs) := by
    have hK_le : K_P * c ^ (-(1 / 2 : ℝ)) ≤ ceK / ceCs := by
      have hV_nn : 0 ≤ 2 * ceK / ceCs * (C_V / (warpTauStar / 2)) := by
        have := pbcV_nonneg; have := pbC0_nonneg; have := warpTauStar_ge
        have := ceK_pos; have := ceCs_pos; dsimp [C_V]; positivity
      have : K_P ≤ K_slope := by dsimp [K_slope]; linarith only [hV_nn]
      exact (mul_le_mul_of_nonneg_right this (by positivity)).trans hK_sl
    have hup : P_lead ≤ ceK / ceCs + K_P * c ^ (-(1 / 2 : ℝ)) := (abs_le.mp hP_raw).2 |> fun h => by linarith
    have hP_nn : 0 ≤ P_lead := by
      dsimp only [P_lead]; unfold fctKappa; positivity
    rw [abs_of_nonneg hP_nn]; linarith only [hup, hK_le]
  let raw := |uctCAi| * c ^ (-(5 / 6 : ℝ)) * winP0 K4 ε c L α *
    ((winUhat K4 ε c α L1 - winUhat K4 ε c α L) / (L - L1))
  have hraw_eq : raw - P_lead = P_lead * ((Vξ - VL) / VL) := by
    dsimp only [raw, P_lead]
    rw [hslope_eq]
    field_simp [hVL_pos.ne']
  have hraw_sub : |raw - ceK / ceCs| ≤ K_slope * c ^ (-(1 / 2 : ℝ)) := by
    have h2 : |P_lead * ((Vξ - VL) / VL)| ≤ (2 * ceK / ceCs) * (C_V / (warpTauStar / 2)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [abs_mul, abs_div, abs_of_pos hVL_pos]
      have hrat : |Vξ - VL| / VL ≤ C_V / (warpTauStar / 2) * c ^ (-(1 / 2 : ℝ)) := by
        have hCV0 : 0 ≤ C_V * c ^ (-(1 / 2 : ℝ)) := by
          have := pbcV_nonneg; have := pbC0_nonneg; dsimp [C_V]; positivity
        calc |Vξ - VL| / VL ≤ (C_V * c ^ (-(1 / 2 : ℝ))) / (warpTauStar / 2) :=
              div_le_div₀ hCV0 hV_diff (by have := warpTauStar_ge; positivity) hVL_lo
          _ = C_V / (warpTauStar / 2) * c ^ (-(1 / 2 : ℝ)) := by ring
      calc |P_lead| * (|Vξ - VL| / VL) ≤ (2 * (ceK / ceCs)) * (C_V / (warpTauStar / 2) * c ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul hP_lead_bd hrat (by positivity) (by have := ceK_pos; have := ceCs_pos; positivity)
        _ = (2 * ceK / ceCs) * (C_V / (warpTauStar / 2)) * c ^ (-(1 / 2 : ℝ)) := by ring
    calc |raw - ceK / ceCs| = |(raw - P_lead) + (P_lead - ceK / ceCs)| := by ring_nf
      _ ≤ |raw - P_lead| + |P_lead - ceK / ceCs| := abs_add_le _ _
      _ ≤ (2 * ceK / ceCs) * (C_V / (warpTauStar / 2)) * c ^ (-(1 / 2 : ℝ)) + K_P * c ^ (-(1 / 2 : ℝ)) :=
          add_le_add (by rwa [hraw_eq]) hP_raw
      _ = K_slope * c ^ (-(1 / 2 : ℝ)) := by dsimp [K_slope]; ring
  have hraw_bd : |raw| ≤ 2 * (ceK / ceCs) := by
    have h1 : raw ≤ ceK / ceCs + K_slope * c ^ (-(1 / 2 : ℝ)) := by linarith [(abs_le.mp hraw_sub).2]
    have h0 : 0 ≤ raw := by
      dsimp only [raw]; rw [hslope_eq]
      have hVξ_pos : 0 < Vξ := by linarith only [(abs_le.mp (hξ_b.trans hV_half)).1, warpTauStar_ge]
      unfold fctKappa; positivity
    rw [abs_of_nonneg h0]; linarith only [h1, hK_sl]
  have hNc_lo : 1 / 2 ≤ fctNc h ε c := hNc_b.2.1
  have hNc_inv : |1 / fctNc h ε c - 1| ≤ C_N' * c ^ (-(1 / 2 : ℝ)) := by
    rw [show 1 / fctNc h ε c - 1 = -(fctNc h ε c - 1) / fctNc h ε c by
      field_simp [show fctNc h ε c ≠ 0 by linarith only [hNc_lo]]; ring]
    rw [abs_div, abs_neg, abs_of_pos (show 0 < fctNc h ε c by linarith only [hNc_lo])]
    have hc_inv : c⁻¹ ≤ c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc |fctNc h ε c - 1| / fctNc h ε c ≤ (|C_N| * c⁻¹) / (1 / 2) := by
          gcongr; exact hN_b.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      _ = C_N' * c⁻¹ := by dsimp [C_N']; ring
      _ ≤ C_N' * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hc_inv (by positivity)
  have hκ_sub : |(1 / fctNc h ε c) * raw - ceK / ceCs| ≤ C_κ * c ^ (-(1 / 2 : ℝ)) := by
    have heq : (1 / fctNc h ε c) * raw - ceK / ceCs = (1 / fctNc h ε c) * (raw - ceK / ceCs) +
        (1 / fctNc h ε c - 1) * (ceK / ceCs) := by ring
    have h1Nc_bd : |1 / fctNc h ε c| ≤ 2 := by
      rw [abs_of_pos (by positivity)]; exact div_le_of_le_mul₀ (by positivity) (by positivity) (by linarith)
    rw [heq]
    calc |(1 / fctNc h ε c) * (raw - ceK / ceCs) + (1 / fctNc h ε c - 1) * (ceK / ceCs)|
        ≤ |(1 / fctNc h ε c) * (raw - ceK / ceCs)| + |(1 / fctNc h ε c - 1) * (ceK / ceCs)| :=
          abs_add_le _ _
      _ = |1 / fctNc h ε c| * |raw - ceK / ceCs| + |1 / fctNc h ε c - 1| * |ceK / ceCs| := by
          rw [abs_mul, abs_mul]
      _ ≤ 2 * (K_slope * c ^ (-(1 / 2 : ℝ))) + (C_N' * c ^ (-(1 / 2 : ℝ))) * (ceK / ceCs) := by
          rw [abs_of_pos (div_pos ceK_pos ceCs_pos)]
          exact add_le_add (mul_le_mul h1Nc_bd hraw_sub (by positivity) (by positivity))
            (mul_le_mul_of_nonneg_right hNc_inv (by have := ceK_pos; have := ceCs_pos; positivity))
      _ = C_κ * c ^ (-(1 / 2 : ℝ)) := by dsimp [C_κ]; ring
  have hκ_lo : (3 / 4 : ℝ) * (ceK / ceCs) ≤ (1 / fctNc h ε c) * raw := by
    linarith only [(abs_le.mp hκ_sub).1, hκ_quart]
  have hκ_hi : (1 / fctNc h ε c) * raw ≤ 2 * (ceK / ceCs) := by
    have hdiv_nn : 0 ≤ ceK / ceCs := div_nonneg ceK_pos.le ceCs_pos.le
    linarith only [(abs_le.mp hκ_sub).2, hκ_quart, hdiv_nn]
  have hslope_diff : |(winUhat K4 ε c α L1 - winUhat K4 ε c α L) - (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1)| ≤
      C_s * c ^ (1 / 6 : ℝ) * (L - L1) := by
    rw [show winUhat K4 ε c α L1 - winUhat K4 ε c α L =
        ((winUhat K4 ε c α L1 - winUhat K4 ε c α L) / (L - L1)) * (L - L1) by field_simp [hL10.ne'],
      hslope_eq, ← fctKappa_mul_warpTauStar hc0, ← sub_mul, ← mul_sub, abs_mul, abs_mul,
      abs_of_pos (by unfold fctKappa; positivity), abs_of_pos hL10]
    have hc23_12 : c ^ (2 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) = c ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    unfold fctKappa
    calc (2 ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * |Vξ - warpTauStar| * (L - L1)
        ≤ (2 ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) * (L - L1) := by
          have := pbcV_nonneg; have := pbC0_nonneg; gcongr
      _ = C_s * (c ^ (2 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ))) * (L - L1) := by dsimp [C_s]; ring
      _ = C_s * c ^ (1 / 6 : ℝ) * (L - L1) := by rw [hc23_12]
  change |1 / fctNc h ε c * raw - ceK / ceCs| ≤ C_κ * c ^ (-(1 / 2 : ℝ)) at hκ_sub
  change (3 / 4 : ℝ) * (ceK / ceCs) ≤ 1 / fctNc h ε c * raw at hκ_lo
  change 1 / fctNc h ε c * raw ≤ 2 * (ceK / ceCs) at hκ_hi
  exact ⟨by dsimp [raw] at hκ_sub; simpa only [mul_assoc] using hκ_sub,
    by dsimp [raw] at hκ_lo; simpa only [mul_assoc] using hκ_lo,
    by dsimp [raw] at hκ_hi; simpa only [mul_assoc] using hκ_hi, hslope_diff⟩

/-! ### 4. Main fixed Airy window lower bound `(fct:warp-win)` -/

/-- **`fct:warp-win`** (Proposition FCT.5 (2), fixed Airy window `L ∈ (L₁, Sw c^{-2/3}]`):
for `1 ≤ K4`, `1 ≤ Sw`, `ε = ±1`, and `c ≥ c₀(K4, Sw)`,
`normDensity (ctWwarp (fctPhiHat h) (fctDcomp K4 (fctWarpAlpha h)) ε c) c (fctXi1 L)` is bounded below by
`(3 / 4) * (ceK / ceCs) * winAiryQuot (winUhat K4 ε c (fctWarpAlpha h ε c) L) - C_win * c ^ (-(4 / 3 : ℝ))`. -/
theorem fct_warp_win_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) (Sw : ℝ) (hSw : 1 ≤ Sw) :
    ∃ C_win c₀ : ℝ, 0 ≤ C_win ∧ 15000 ≤ c₀ ∧ ∀ {ε c L : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c → fctWarpL1 h ε c < L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      (3 / 4 : ℝ) * (ceK / ceCs) * winAiryQuot (winUhat K4 ε c (fctWarpAlpha h ε c) L) -
          C_win * c ^ (-(4 / 3 : ℝ)) ≤
        normDensity (ctWwarp (fctPhiHat h) (fctDcomp K4 (fctWarpAlpha h)) ε c) c (fctXi1 L) := by
  obtain ⟨M_u, c_sp, hMu4, _, hsplit_win⟩ := win_warpSqDensity_split hK4 h hSw
  obtain ⟨C_P, C_Pd, c_P0, hCP0, hCPd0, _, hP0_bds⟩ := win_P0_bounds hK4 h hSw
  obtain ⟨C_R, c_R, hCR0, _, hRSq⟩ := win_RSqIn_bounds hK4 h hSw
  obtain ⟨C_out, c_out, hCout0, _, hout⟩ := warpSqOut_mvt_bound
  obtain ⟨C_u, c_u, hCu0, _, hu_err⟩ := win_zero_a1_err hK4 h
  obtain ⟨C_κ, C_s, c_κ, hCκ0, hCs0, _, hκ_bds⟩ := win_uhat_slope_approx hK4 h hSw
  obtain ⟨c_ns, _, hns⟩ := normDensity_ctWwarp_split hK4 h
  obtain ⟨c_ibp, _, hibp⟩ := warpMainNoRightDensity_exact_ibp hK4 h
  obtain ⟨c_Nc, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨C_rt, c_rt, hCrt0, _, hrt⟩ := warpRightTailDensity_bound hK4 h
  obtain ⟨C_lt, c_lt, hClt0, _, hlt⟩ := warpLeftTailDensity_mid_bound hK4 h
  obtain ⟨a₀, _, c_δ, ha₀, _, _, hδ_bds⟩ := FctSym.physDelta_bounds
  let M : ℝ := max M_u (|airyZero 1| + 1)
  have hM_a1 : |airyZero 1| ≤ M := le_trans (by linarith) (le_max_right _ _)
  obtain ⟨C_A, hCA0, hDD⟩ := airySq_divided_diff_bound hM_a1
  obtain ⟨C_q, hCq0, hQ_lip⟩ := winAiryQuot_abs_le hM_a1
  let c_pair : ℝ := h.choose_spec.choose
  let C_win : ℝ := 2 * (ceK / ceCs) * C_A * C_u + (2 * (ceK / ceCs) + 1) * C_q * C_u +
    2 * |uctCAi| * (C_Pd * C_u + C_R + C_out) + C_rt + C_lt
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_sp ≤ c ∧ c_P0 ≤ c ∧ c_R ≤ c ∧ c_out ≤ c ∧ c_u ≤ c ∧ c_κ ≤ c ∧
      c_ns ≤ c ∧ c_ibp ≤ c ∧ c_Nc ≤ c ∧ c_rt ≤ c ∧ c_lt ≤ c ∧ c_δ ≤ c ∧ c_pair ≤ c ∧
      Sw * c ^ (-(1 / 6 : ℝ)) ≤ 3 * a₀ ∧ C_u * c ^ (-(4 / 3 : ℝ)) ≤ 1 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
          (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
            (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
              (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
                (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
                  (Eventually.and ?_ ?_))))))))))))))
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul Sw
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds (by positivity))
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)).const_mul C_u
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_win, max 15000 c₀, ?_, le_max_left _ _, fun {ε c L} hε hc hL1_lt hL_Sw => ?_⟩
  · have := ceK_pos; have := ceCs_pos; positivity
  obtain ⟨hc15, hcsp, hcP0, hcR, hcout, hcu, hck, hcns, hcibp, hcNc, hcrt, hclt, hcδ, hcpair, hSw_δ, hCu_1⟩ :=
    hc₀ c ((le_max_right _ _).trans hc)
  have hL1_le : fctWarpL1 h ε c ≤ L := hL1_lt.le
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have ⟨hg_L, hsq_L⟩ := hsplit_win hε hcsp hL1_le hL_Sw
  have ⟨hg_1, hsq_1⟩ := hsplit_win hε hcsp le_rfl (hL1_le.trans hL_Sw)
  have hc0 : 0 < c := hg_L.hc0
  have hc1 : 1 ≤ c := by linarith only [hc15]
  have hL_ξ : Real.log (Real.pi ^ 2 * fctXi1 L) = L := by
    unfold fctXi1
    rw [show π ^ 2 * (Real.exp L / π ^ 2) = Real.exp L by field_simp [Real.pi_pos.ne'], Real.log_exp]
  have hξ_pos : 0 < fctXi1 L := by unfold fctXi1; positivity
  have h_ns := hns ε c (fctXi1 L) hε hcns hξ_pos
  have h_ibp := (hibp ε c (fctXi1 L) hε hcibp hξ_pos (by rw [hL_ξ]; exact hL1_lt.ne')).2
  have h_sq0 : warpSqDensity K4 ε c L1 α (fctXi1 L1) = 0 := warpSqDensity_at_L1 h hε hcpair
  have hP0_L := hP0_bds hε hcP0 hL1_le hL_Sw
  have hRSq_L := hRSq hε hcR hL1_le hL_Sw
  have hα_2τ : |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have : c ^ (-(1 / 2 : ℝ)) = (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    linarith only [hg_L.hα, this, Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
  have hout_L := hout hK4 hε hcout hg_L.hτD_comp hg_L.hK4τ hg_L.hL1_c12 hα_2τ hL1_le hg_L.hell_L_Ioo.2
  have hu1_e := hu_err hε hcu
  have ⟨hκ_sub, hκ_lo, hκ_hi, _⟩ := hκ_bds hε hck hL1_lt hL_Sw
  have hNc_b := hNc ε c hε hcNc
  have hrt_L := hrt ε c (fctXi1 L) hε hcrt hξ_pos
  have hL_3δ : L ≤ 3 * FctSym.physDelta c := by
    have hδ := (hδ_bds c hcδ).1
    have h23 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc L ≤ Sw * c ^ (-(2 / 3 : ℝ)) := hL_Sw
      _ = (Sw * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [h23]; ring
      _ ≤ (3 * a₀) * c ^ (-(1 / 2 : ℝ)) := by gcongr
      _ ≤ 3 * FctSym.physDelta c := by linarith only [hδ]
  have hlt_L := hlt ε c (fctXi1 L) hε hclt hξ_pos (by rwa [hL_ξ])
  -- Decompose `warpSqDensity(L) = warpSqDensity(L) - warpSqDensity(L1)`
  set û_L := winUhat K4 ε c α L
  set û_1 := winUhat K4 ε c α L1
  have hû_L_M : |û_L| ≤ M := hg_L.hûL_M.trans (le_max_left _ _)
  have hû_1_M : |û_1| ≤ M := hg_1.hûL_M.trans (le_max_left _ _)
  have hû_ne : û_L ≠ û_1 := by
    have hpos : 0 < (100 / 95 : ℝ) * 2 ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) := by
      have := sub_pos.mpr hL1_lt; positivity
    have hdiff : 0 < û_1 - û_L := lt_of_lt_of_le hpos hg_L.hv_diff_lo
    exact (sub_pos.mp hdiff).ne
  have hû1_lt : û_L < û_1 := by
    have hpos : 0 < (100 / 95 : ℝ) * 2 ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) := by
      have := sub_pos.mpr hL1_lt; positivity
    exact sub_pos.mp (lt_of_lt_of_le hpos hg_L.hv_diff_lo)
  have hDD_L := hDD hû_L_M hû_1_M hû_ne
  have hL10 : 0 < L - L1 := sub_pos.mpr hL1_lt
  have hNc_inv_pos : 0 < 1 / fctNc h ε c := div_pos one_pos (by linarith only [hNc_b.2.1])
  have hNc_inv_2 : 1 / fctNc h ε c ≤ 2 :=
    div_le_of_le_mul₀ (by linarith only [hNc_b.2.1]) (by positivity) (by linarith only [hNc_b.2.1])
  -- Rewrite the IBP formula cleanly
  let pref : ℝ := (1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1))
  have hpref_pos : 0 ≤ pref := by positivity
  let Dq : ℝ := (airyAi û_L ^ 2 - airyAi û_1 ^ 2) / (û_1 - û_L)
  let κL : ℝ := (1 / fctNc h ε c) * |uctCAi| * c ^ (-(5 / 6 : ℝ)) * winP0 K4 ε c L α * ((û_1 - û_L) / (L - L1))
  let E_P0 : ℝ := pref * ((winP0 K4 ε c L α - winP0 K4 ε c L1 α) * airyAi û_1 ^ 2)
  let E_Rin : ℝ := pref * (winRSqIn K4 ε c L1 α L - winRSqIn K4 ε c L1 α L1)
  let E_out : ℝ := pref * (warpSqOut K4 ε c L1 α L - warpSqOut K4 ε c L1 α L1)
  have hmain_eq : warpMainNoRightDensity h ε c (fctXi1 L) = κL * Dq + E_P0 + E_Rin + E_out := by
    rw [h_ibp, hL_ξ]
    have hdiff_sq : warpSqDensity K4 ε c L1 α (fctXi1 L) =
        warpSqDensity K4 ε c L1 α (fctXi1 L) - warpSqDensity K4 ε c L1 α (fctXi1 L1) := by
      rw [h_sq0, sub_zero]
    rw [hdiff_sq, hsq_L, hsq_1]
    have hû_ne' : û_1 - û_L ≠ 0 := sub_ne_zero.mpr hû_ne.symm
    change pref * (winP0 K4 ε c L α * airyAi û_L ^ 2 + winRSqIn K4 ε c L1 α L + warpSqOut K4 ε c L1 α L -
      (winP0 K4 ε c L1 α * airyAi û_1 ^ 2 + winRSqIn K4 ε c L1 α L1 + warpSqOut K4 ε c L1 α L1)) =
      κL * Dq + E_P0 + E_Rin + E_out
    dsimp only [pref, κL, Dq, E_P0, E_Rin, E_out]
    field_simp [hL10.ne', hû_ne']
    ring
  -- Bounds on the 3 error terms `E_P0`, `E_Rin`, `E_out`
  have hpref_2 : pref ≤ 2 * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1)) :=
    mul_le_mul_of_nonneg_right hNc_inv_2 (by positivity)
  have hE_P0 : |E_P0| ≤ 2 * |uctCAi| * (C_Pd * C_u) * c ^ (-(4 / 3 : ℝ)) := by
    dsimp only [E_P0]
    rw [abs_mul, abs_of_nonneg hpref_pos, abs_mul]
    have hc_pow : c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 6 : ℝ) * c ^ (-(8 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hP0_d := (hP0_bds hε hcP0 hL1_le hL_Sw).2.2.1
    have hu1_sq : |airyAi û_1 ^ 2| ≤ C_u * c ^ (-(8 / 3 : ℝ)) := by
      rw [abs_of_nonneg (sq_nonneg _)]; exact hu1_e.2
    calc pref * (|winP0 K4 ε c L α - winP0 K4 ε c L1 α| * |airyAi û_1 ^ 2|)
        ≤ (2 * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1))) *
            ((C_Pd * c ^ (1 / 6 : ℝ) * (L - L1)) * (C_u * c ^ (-(8 / 3 : ℝ)))) :=
          mul_le_mul hpref_2 (mul_le_mul hP0_d hu1_sq (abs_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = 2 * |uctCAi| * (C_Pd * C_u) * (c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 6 : ℝ) * c ^ (-(8 / 3 : ℝ))) := by
          field_simp [hL10.ne']
      _ ≤ 2 * |uctCAi| * (C_Pd * C_u) * c ^ (-(4 / 3 : ℝ)) := by gcongr
  have hE_Rin : |E_Rin| ≤ 2 * |uctCAi| * C_R * c ^ (-(4 / 3 : ℝ)) := by
    dsimp only [E_Rin]
    rw [abs_mul, abs_of_nonneg hpref_pos]
    have hc43 : c ^ (-(5 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc pref * |winRSqIn K4 ε c L1 α L - winRSqIn K4 ε c L1 α L1|
        ≤ (2 * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1))) * (C_R * c ^ (-(1 / 2 : ℝ)) * (L - L1)) :=
          mul_le_mul hpref_2 hRSq_L.2 (abs_nonneg _) (by positivity)
      _ = 2 * |uctCAi| * C_R * (c ^ (-(5 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by
          field_simp [hL10.ne']
      _ = 2 * |uctCAi| * C_R * c ^ (-(4 / 3 : ℝ)) := by rw [hc43]
  have hE_out : |E_out| ≤ 2 * |uctCAi| * C_out * c ^ (-(4 / 3 : ℝ)) := by
    dsimp only [E_out]
    rw [abs_mul, abs_of_nonneg hpref_pos]
    have hc43 : c ^ (-(5 / 6 : ℝ)) * c ^ (-(61 / 24 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc pref * |warpSqOut K4 ε c L1 α L - warpSqOut K4 ε c L1 α L1|
        ≤ (2 * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1))) * (C_out * c ^ (-(61 / 24 : ℝ)) * (L - L1)) :=
          mul_le_mul hpref_2 hout_L.2.2 (abs_nonneg _) (by positivity)
      _ = 2 * |uctCAi| * C_out * (c ^ (-(5 / 6 : ℝ)) * c ^ (-(61 / 24 : ℝ))) := by
          field_simp [hL10.ne']
      _ ≤ 2 * |uctCAi| * C_out * c ^ (-(4 / 3 : ℝ)) := by gcongr
  -- Bound on `κL * Dq - (3 / 4) * (ceK / ceCs) * winAiryQuot û_L`
  have hκ_pos : 0 ≤ κL := le_trans (mul_nonneg (by norm_num) (div_nonneg ceK_pos.le ceCs_pos.le)) hκ_lo
  have hκ_Dq : (3 / 4 : ℝ) * (ceK / ceCs) * winAiryQuot û_L -
      (2 * (ceK / ceCs) * C_A * C_u + (2 * (ceK / ceCs) + 1) * C_q * C_u) * c ^ (-(4 / 3 : ℝ)) ≤ κL * Dq := by
    have hdd_mul : |κL * (Dq - winAiryQuot û_L)| ≤ 2 * (ceK / ceCs) * C_A * C_u * c ^ (-(4 / 3 : ℝ)) := by
      have h2ce : 0 ≤ 2 * (ceK / ceCs) := mul_nonneg (by norm_num) (div_nonneg ceK_pos.le ceCs_pos.le)
      rw [abs_mul, abs_of_nonneg hκ_pos]
      calc κL * |Dq - winAiryQuot û_L| ≤ (2 * (ceK / ceCs)) * |Dq - winAiryQuot û_L| :=
            mul_le_mul_of_nonneg_right hκ_hi (abs_nonneg _)
        _ ≤ (2 * (ceK / ceCs)) * (C_A * |û_1 - airyZero 1|) := mul_le_mul_of_nonneg_left hDD_L h2ce
        _ ≤ (2 * (ceK / ceCs)) * (C_A * (C_u * c ^ (-(4 / 3 : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu1_e.1 hCA0) h2ce
        _ = 2 * (ceK / ceCs) * C_A * C_u * c ^ (-(4 / 3 : ℝ)) := by ring
    have hq_main : (3 / 4 : ℝ) * (ceK / ceCs) * winAiryQuot û_L -
        (2 * (ceK / ceCs) + 1) * C_q * C_u * c ^ (-(4 / 3 : ℝ)) ≤ κL * winAiryQuot û_L := by
      rcases le_or_gt û_L (airyZero 1) with hle | hgt
      · have hqnn : 0 ≤ winAiryQuot û_L := winAiryQuot_nonneg_of_le hle
        have h1 : (3 / 4 : ℝ) * (ceK / ceCs) * winAiryQuot û_L ≤ κL * winAiryQuot û_L :=
          mul_le_mul_of_nonneg_right hκ_lo hqnn
        have h2 : 0 ≤ (2 * (ceK / ceCs) + 1) * C_q * C_u * c ^ (-(4 / 3 : ℝ)) := by
          have := ceK_pos; have := ceCs_pos; positivity
        linarith only [h1, h2]
      · have hû_diff_a1 : |û_L - airyZero 1| ≤ C_u * c ^ (-(4 / 3 : ℝ)) := by
          rw [abs_of_pos (sub_pos.mpr hgt)]
          have h1 : û_L - airyZero 1 ≤ û_1 - airyZero 1 := by linarith only [hû1_lt]
          exact h1.trans ((le_abs_self _).trans hu1_e.1)
        have hq_bd : |winAiryQuot û_L| ≤ C_q * C_u * c ^ (-(4 / 3 : ℝ)) :=
          ((hQ_lip hû_L_M).trans (mul_le_mul_of_nonneg_left hû_diff_a1 hCq0)).trans_eq (by ring)
        have hdiff_κ : |κL - (3 / 4 : ℝ) * (ceK / ceCs)| ≤ 2 * (ceK / ceCs) + 1 := by
          have := ceK_pos; have := ceCs_pos
          rw [abs_le]; constructor <;> linarith only [hκ_lo, hκ_hi]
        have hmul_bd : |(κL - (3 / 4 : ℝ) * (ceK / ceCs)) * winAiryQuot û_L| ≤
            (2 * (ceK / ceCs) + 1) * C_q * C_u * c ^ (-(4 / 3 : ℝ)) := by
          rw [abs_mul]
          have hnonneg : 0 ≤ 2 * (ceK / ceCs) + 1 := by have := ceK_pos; have := ceCs_pos; positivity
          calc |κL - (3 / 4 : ℝ) * (ceK / ceCs)| * |winAiryQuot û_L|
              ≤ (2 * (ceK / ceCs) + 1) * (C_q * C_u * c ^ (-(4 / 3 : ℝ))) := by gcongr
            _ = (2 * (ceK / ceCs) + 1) * C_q * C_u * c ^ (-(4 / 3 : ℝ)) := by ring
        linarith only [(abs_le.mp hmul_bd).1]
    have hdecomp : κL * Dq = κL * winAiryQuot û_L + κL * (Dq - winAiryQuot û_L) := by ring
    rw [hdecomp]
    linarith only [hq_main, (abs_le.mp hdd_mul).1]
  -- Left tail is ≤ C_lt c^{-4/3} since 15/8 ≥ 4/3
  have hlt_43 : |warpLeftTailDensity h ε c (fctXi1 L)| ≤ C_lt * c ^ (-(4 / 3 : ℝ)) := by
    have hc158 : c ^ (-(15 / 8 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    exact hlt_L.trans (mul_le_mul_of_nonneg_left hc158 hClt0)
  rw [h_ns.1, h_ns.2, hmain_eq]
  linarith only [hκ_Dq, (abs_le.mp hE_P0).1, (abs_le.mp hE_Rin).1, (abs_le.mp hE_out).1,
    (abs_le.mp hrt_L).1, (abs_le.mp hlt_43).1]

/-- info: 'FormalResearch.SignUncertainty.fct_warp_win_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_warp_win_bound

end FormalResearch.SignUncertainty
