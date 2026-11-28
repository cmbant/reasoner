/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinMu
public import FormalResearch.SignUncertainty.FctWarpWinNode

/-!
# Exact inner/outer decomposition and `winP0` bounds on the Airy window (`fct:warp-win`)

Splits `warpSqDensity K4 ε c L1 α (fctXi1 L)` on `L ∈ [fctWarpL1 h ε c, Sw * c^{-2/3}]` as
`winP0 K4 ε c L α * (airyAi û_L) ^ 2 + winRSqIn K4 ε c L1 α L + warpSqOut K4 ε c L1 α L`
and proves:
* `win_window_geom_props`: phase-domain membership, `(v̂_L - v̂_1)` two-sided `c^{2/3} (L - L_1)` bounds,
  and `|û_L| ≤ M_u`;
* `win_warpSqDensity_split`: exact inner/outer + Airy-square decomposition;
* `win_P0_bounds`: positive `c^{1/6}` bounds, exact `(ceK / ceCs)` product identity, and `C c^{1/6} (L - L1)` Lipschitz bound.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

/-! ### 1. Definitions and `fctS` linearity helpers -/

/-- Airy-square coefficient `P₀(L)` in `h_sq(L) = P₀(L) Ai(û_L)² + R_sq^in(L) + h_sq^out(L)`. -/
noncomputable def winP0 (K4 ε c L α : ℝ) : ℝ :=
  (c ^ (1 / 3 : ℝ) / π) / warpN0 c * warpNu K4 ε c L α * (2 * π ^ (3 / 2 : ℝ))

/-- Inner Abel-symbol remainder `R_sq^in(L)` in `h_sq(L)`. -/
noncomputable def winRSqIn (K4 ε c L1 α L : ℝ) : ℝ :=
  let V := concreteInnerV K4 ε c L α
  let S := concreteBoxS K4 ε c
  let û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α)
  ((c ^ (1 / 3 : ℝ) / π) / warpN0 c * warpNu K4 ε c L α) *
    (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
      winMuMix K4 ε c L1 L α u)) - fctS û (fun _ => (1 : ℂ))).re

lemma win_pref_simp {c : ℝ} (hc0 : 0 < c) :
    (c ^ (1 / 3 : ℝ) / π) / warpN0 c * (2 * π ^ (3 / 2 : ℝ)) =
      (1 / 2 : ℝ) * Real.sqrt π * ceCs ^ (5 / 2 : ℝ) * c ^ (1 / 6 : ℝ) := by
  have hpi : 0 < π := Real.pi_pos
  have hcs : 0 < ceCs := ceCs_pos
  have hk : 0 < ceK := ceK_pos
  have h2sq : (0 : ℝ) < (2 : ℝ) ^ 2 := by positivity
  have hpi3 : (0 : ℝ) < π ^ 2 / 3 := by positivity
  have hτs : warpTauStar = ceK / ceCs := by
    unfold warpTauStar ceK ceCs
    have h12 : (12 : ℝ) / π ^ 2 = (2 : ℝ) ^ 2 / (π ^ 2 / 3) := by ring
    rw [h12, Real.div_rpow h2sq.le hpi3.le, ← Real.rpow_natCast (2 : ℝ),
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hcs3 : ceCs ^ (3 : ℝ) = π ^ 2 / 3 := by
    unfold ceCs
    rw [← Real.rpow_mul hpi3.le]; norm_num
  have hsqrt_τ : Real.sqrt warpTauStar = (2 : ℝ) ^ (1 / 3 : ℝ) * ceCs ^ (-(1 / 2 : ℝ)) := by
    rw [hτs, Real.sqrt_div hk.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    unfold ceK
    rw [← Real.rpow_mul (by norm_num), div_eq_mul_inv, ← Real.rpow_neg hcs.le]
    norm_num
  have hc_pow : c ^ (1 / 3 : ℝ) / c ^ (1 / 6 : ℝ) = c ^ (1 / 6 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; congr 1; norm_num
  have hpi_pow : π * π ^ (3 / 2 : ℝ) = Real.sqrt π * π ^ 2 := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hpi,
      Real.rpow_one]; ring
  have hcs_pow : ceCs ^ (-(1 / 2 : ℝ)) * ceCs ^ (3 : ℝ) = ceCs ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_add hcs]; congr 1; norm_num
  unfold warpN0
  rw [hsqrt_τ]
  have h2ne : (2 : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := by positivity
  have hc16_ne : c ^ (1 / 6 : ℝ) ≠ 0 := by positivity
  calc (c ^ (1 / 3 : ℝ) / π) / (12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) /
          (π ^ 2 * ((2 : ℝ) ^ (1 / 3 : ℝ) * ceCs ^ (-(1 / 2 : ℝ))))) * (2 * π ^ (3 / 2 : ℝ))
      = (c ^ (1 / 3 : ℝ) / c ^ (1 / 6 : ℝ)) * (π * π ^ (3 / 2 : ℝ)) / 6 *
          ceCs ^ (-(1 / 2 : ℝ)) := by
        field_simp [hpi.ne', h2ne, hc16_ne]
        ring
    _ = c ^ (1 / 6 : ℝ) * (Real.sqrt π * π ^ 2) / 6 * ceCs ^ (-(1 / 2 : ℝ)) := by
        rw [hc_pow, hpi_pow]
    _ = (1 / 2 : ℝ) * Real.sqrt π * ((π ^ 2 / 3) * ceCs ^ (-(1 / 2 : ℝ))) * c ^ (1 / 6 : ℝ) := by ring
    _ = (1 / 2 : ℝ) * Real.sqrt π * (ceCs ^ (-(1 / 2 : ℝ)) * ceCs ^ (3 : ℝ)) * c ^ (1 / 6 : ℝ) := by
        rw [← hcs3]; ring
    _ = (1 / 2 : ℝ) * Real.sqrt π * ceCs ^ (5 / 2 : ℝ) * c ^ (1 / 6 : ℝ) := by rw [hcs_pow]

lemma win_fctS_split3 {M û p1 p2 p3 B1 B2 B3 : ℝ}
    (hM : 0 < M) (hû : |û| ≤ M)
    (hp1 : p1 ≤ 21) (hp2 : p2 ≤ 21) (hp3 : p3 ≤ 21)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3)
    {k1 k2 k3 : ℝ → ℂ}
    (hk1 : FctSymCls 8 p1 B1 k1) (hk2 : FctSymCls 8 p2 B2 k2) (hk3 : FctSymCls 8 p3 B3 k3) :
    fctS û (fun u => k1 u + k2 u - k3 u) = fctS û k1 + fctS û k2 - fctS û k3 := by
  have hDi := uniqueDiffOn_Ici (0 : ℝ)
  have hk1' := hk1.mono_p Set.Subset.rfl hB1 hp1
  have hk2' := hk2.mono_p Set.Subset.rfl hB2 hp2
  have hA1 := (FctSymA.fctInnerSymbolsA M 8 p1 hM (by norm_num) (by linarith)).choose_spec.2 û B1 k1 hû hB1 hk1
  have hA2 := (FctSymA.fctInnerSymbolsA M 8 p2 hM (by norm_num) (by linarith)).choose_spec.2 û B2 k2 hû hB2 hk2
  have hA3 := (FctSymA.fctInnerSymbolsA M 8 p3 hM (by norm_num) (by linarith)).choose_spec.2 û B3 k3 hû hB3 hk3
  obtain ⟨L1, hL1⟩ := hA1.1
  obtain ⟨L2, hL2⟩ := hA2.1
  obtain ⟨L3, hL3⟩ := hA3.1
  have hs1 : FctSLimit û k1 (fctS û k1) := hL1.fctS_eq ▸ hL1
  have hs2 : FctSLimit û k2 (fctS û k2) := hL2.fctS_eq ▸ hL2
  have hs3 : FctSLimit û k3 (fctS û k3) := hL3.fctS_eq ▸ hL3
  have hs12 := fctSLimit_add hB1 hB2 hk1' hk2' hs1 hs2
  have hs123 := fctSLimit_sub (add_nonneg hB1 hB2) hB3 (hk1'.add hDi hk2') hk3 hs12 hs3
  exact hs123.fctS_eq

lemma win_fctS_add {M û p1 p2 B1 B2 : ℝ}
    (hM : 0 < M) (hû : |û| ≤ M) (hp1 : p1 ≤ 21) (hp2 : p2 ≤ 21)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) {k1 k2 : ℝ → ℂ}
    (hk1 : FctSymCls 8 p1 B1 k1) (hk2 : FctSymCls 8 p2 B2 k2) :
    fctS û (fun u => k1 u + k2 u) = fctS û k1 + fctS û k2 := by
  have hk1' := hk1.mono_p Set.Subset.rfl hB1 hp1
  have hk2' := hk2.mono_p Set.Subset.rfl hB2 hp2
  have h1 := (FctSymA.fctInnerSymbolsA M 8 p1 hM (by norm_num) (by linarith)).choose_spec.2 û B1 k1 hû hB1 hk1
  have h2 := (FctSymA.fctInnerSymbolsA M 8 p2 hM (by norm_num) (by linarith)).choose_spec.2 û B2 k2 hû hB2 hk2
  obtain ⟨L1, hL1⟩ := h1.1; obtain ⟨L2, hL2⟩ := h2.1
  have hs1 : FctSLimit û k1 (fctS û k1) := hL1.fctS_eq ▸ hL1
  have hs2 : FctSLimit û k2 (fctS û k2) := hL2.fctS_eq ▸ hL2
  exact (fctSLimit_add hB1 hB2 hk1' hk2' hs1 hs2).fctS_eq

lemma win_fctS_sub {M û p1 p2 B1 B2 : ℝ}
    (hM : 0 < M) (hû : |û| ≤ M) (hp1 : p1 ≤ 21) (hp2 : p2 ≤ 21)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) {k1 k2 : ℝ → ℂ}
    (hk1 : FctSymCls 8 p1 B1 k1) (hk2 : FctSymCls 8 p2 B2 k2) :
    fctS û (fun u => k1 u - k2 u) = fctS û k1 - fctS û k2 := by
  have hk1' := hk1.mono_p Set.Subset.rfl hB1 hp1
  have hk2' := hk2.mono_p Set.Subset.rfl hB2 hp2
  have h1 := (FctSymA.fctInnerSymbolsA M 8 p1 hM (by norm_num) (by linarith)).choose_spec.2 û B1 k1 hû hB1 hk1
  have h2 := (FctSymA.fctInnerSymbolsA M 8 p2 hM (by norm_num) (by linarith)).choose_spec.2 û B2 k2 hû hB2 hk2
  obtain ⟨L1, hL1⟩ := h1.1; obtain ⟨L2, hL2⟩ := h2.1
  have hs1 : FctSLimit û k1 (fctS û k1) := hL1.fctS_eq ▸ hL1
  have hs2 : FctSLimit û k2 (fctS û k2) := hL2.fctS_eq ▸ hL2
  exact (fctSLimit_sub hB1 hB2 hk1' hk2' hs1 hs2).fctS_eq

/-! ### 2. Window phase-domain geometry and `û_L` slope / bounds -/

structure WinWindowGeom {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c L Sw M_u : ℝ) : Prop where
  hc0 : 0 < c
  hc10000 : 10000 ≤ c
  hτD : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim
  hτD_comp : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose
  hK4τ : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1
  hα : |fctWarpAlpha h ε c| ≤ c ^ (-(1 / 2 : ℝ))
  hL1_c12 : |fctWarpL1 h ε c| ≤ c ^ (-(1 / 2 : ℝ))
  hL1_abs : |fctWarpL1 h ε c| ≤ 1
  hL1_le : fctWarpL1 h ε c ≤ L
  hell_lo : 0 ≤ concreteEll1 ε c (fctWarpL1 h ε c)
  hell_hi : concreteEll1 ε c L ≤ (Sw + 1) * c ^ (-(1 / 6 : ℝ))
  hell_L_Ioo : concreteEll1 ε c L ∈ Ioo (0 : ℝ) 2.55
  hell_1_Ioo : concreteEll1 ε c (fctWarpL1 h ε c) ∈ Ioo (0 : ℝ) 2.55
  hdom_all : ∀ x ∈ Icc (fctWarpL1 h ε c) L, (x, fctWarpAlpha h ε c) ∈ concretePhaseDom pbellMin ε c
  hv_diff_lo : (100 / 95 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - fctWarpL1 h ε c) ≤
    (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (fctWarpL1 h ε c, fctWarpAlpha h ε c)) -
    (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (L, fctWarpAlpha h ε c))
  hv_diff_hi : (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (fctWarpL1 h ε c, fctWarpAlpha h ε c)) -
    (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (L, fctWarpAlpha h ε c)) ≤
    (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - fctWarpL1 h ε c)
  hû1_a1 : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (fctWarpL1 h ε c, fctWarpAlpha h ε c) - airyZero 1| ≤ 1
  hûL_M : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (L, fctWarpAlpha h ε c)| ≤ M_u

lemma win_window_geom_props {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4)
    {Sw : ℝ} (hSw : 1 ≤ Sw) :
    ∃ (M_u c₀ : ℝ), 4 ≤ M_u ∧ 15000 ≤ c₀ ∧ ∀ {ε c L : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c → fctWarpL1 h ε c ≤ L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      WinWindowGeom h ε c L Sw M_u := by
  obtain ⟨c0_L, c_wg, hc0L_pos, _, hwg⟩ := fctWarpZero_window_geom hK4 h hSw
  obtain ⟨Cz, c_zw, hzw⟩ := fctWarpZero_of_solve h
  obtain ⟨C_u, c_u, _, _, hnode⟩ := win_zero_a1_err hK4 h
  let Mθ : ℝ := max (|ctTheta1 1|) (|ctTheta1 (-1)|)
  have hMθ0 : 0 ≤ Mθ := by positivity
  let M_u : ℝ := 4 + (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * Sw
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_wg ≤ c ∧ c_zw ≤ c ∧ c_u ≤ c ∧
      (pbellMin + Mθ) * c ^ (-(1 / 3 : ℝ)) < c0_L ∧
      Mθ * c ^ (-(1 / 3 : ℝ)) ≤ 1 ∧
      |Cz| * c ^ (-(1 / 6 : ℝ)) ≤ 1 ∧
      C_u * c ^ (-(4 / 3 : ℝ)) ≤ 1 ∧
      c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_
          (Eventually.and ?_ ?_))))))))
    · have ht : Tendsto (fun c : ℝ => (pbellMin + Mθ) * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul _
      exact ht.eventually (gt_mem_nhds hc0L_pos)
    · have ht : Tendsto (fun c : ℝ => Mθ * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul _
      exact ht.eventually (Iic_mem_nhds zero_lt_one)
    · have ht : Tendsto (fun c : ℝ => |Cz| * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul _
      exact ht.eventually (Iic_mem_nhds zero_lt_one)
    · have ht : Tendsto (fun c : ℝ => C_u * c ^ (-(4 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)).const_mul _
      exact ht.eventually (Iic_mem_nhds zero_lt_one)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually (Iic_mem_nhds zero_lt_one)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iic_mem_nhds pbTauLim_pos)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨M_u, max 15000 c₀, by dsimp only [M_u]; linarith [show (0 : ℝ) ≤ (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * Sw by positivity],
    le_max_left _ _, fun {ε c L} hε hc hL1_L hL_Sw => ?_⟩
  obtain ⟨hc15000, hcwg, hczw, hcu, hpbell_lt, hMθ_le1, hCz_le1, hCu_le1, hc12_1, hτD⟩ :=
    hc₀ c ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith only [hc15000]
  have hc1 : 1 ≤ c := by linarith only [hc15000]
  obtain ⟨hL1_lo, hL1_c12, _, hell_L, hell_1, hK4τ, hτD_comp⟩ := hwg hε hcwg hL1_L hL_Sw
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hα_bd : |α| ≤ c ^ (-(1 / 2 : ℝ)) := by
    have h1 := (hzw ε c hε hczw).2
    have h2 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc |α| ≤ Cz * c ^ (-(2 / 3 : ℝ)) := h1
      _ ≤ |Cz| * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = (|Cz| * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [h2]; ring
      _ ≤ 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = c ^ (-(1 / 2 : ℝ)) := one_mul _
  have hθ_le : |ctTheta1 ε| ≤ Mθ := by
    rcases hε with rfl | rfl <;> [exact le_max_left _ _; exact le_max_right _ _]
  have hpbell_L1 : pbellMin * c ^ (-(1 / 2 : ℝ)) < concreteEll1 ε c L1 := by
    have hτ2 : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    unfold concreteEll1
    rw [hτ2, lt_div_iff₀ (Real.rpow_pos_of_pos hc0 _), lt_sub_iff_add_lt]
    have hc_16 : c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c⁻¹ := by
      rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
    have hc_12 : c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
    have h1 : ctTheta1 ε / c ≤ Mθ * c⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (le_abs_self _ |>.trans hθ_le) (by positivity)
    calc pbellMin * c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) + ctTheta1 ε / c
        = pbellMin * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ))) + ctTheta1 ε / c := by ring
      _ ≤ pbellMin * c⁻¹ + Mθ * c⁻¹ := by
          have : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c⁻¹ := by rw [← hc_12, hc_16]
          rw [this]; linarith only [h1]
      _ = ((pbellMin + Mθ) * c ^ (-(1 / 3 : ℝ))) * c ^ (-(2 / 3 : ℝ)) := by rw [← hc_16]; ring
      _ < c0_L * c ^ (-(2 / 3 : ℝ)) := by gcongr
      _ ≤ L1 := hL1_lo
  have hdom_all : ∀ x ∈ Icc L1 L, (x, α) ∈ concretePhaseDom pbellMin ε c := fun x hx => by
    have hx_sw : x ≤ Sw * c ^ (-(2 / 3 : ℝ)) := hx.2.trans hL_Sw
    have hx_ell := (hwg hε hcwg hx.1 hx_sw).2.2.2.1
    have hmono : concreteEll1 ε c L1 ≤ concreteEll1 ε c x := by
      unfold concreteEll1; exact div_le_div_of_nonneg_right (sub_le_sub_right hx.1 _) (sq_nonneg _)
    have hα_om : |α| < 2 * c ^ (-(1 / 2 : ℝ)) := by
      linarith only [hα_bd, Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
    exact ⟨lt_of_lt_of_le hpbell_L1 hmono, hx_ell.2, hα_om⟩
  have hell_hi : concreteEll1 ε c L ≤ (Sw + 1) * c ^ (-(1 / 6 : ℝ)) := by
    have hτ2 : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    unfold concreteEll1; rw [hτ2, div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
    have h1 : -(ctTheta1 ε / c) ≤ Mθ * c⁻¹ := by
      calc -(ctTheta1 ε / c) = (-ctTheta1 ε) * c⁻¹ := by ring
        _ ≤ Mθ * c⁻¹ := mul_le_mul_of_nonneg_right (neg_le_abs _ |>.trans hθ_le) (by positivity)
    have hc23 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hc13 : c⁻¹ = c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
    calc L - ctTheta1 ε / c ≤ Sw * c ^ (-(2 / 3 : ℝ)) + Mθ * c⁻¹ := by linarith only [hL_Sw, h1]
      _ = (Sw + Mθ * c ^ (-(1 / 3 : ℝ))) * c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
          rw [hc23, hc13]; ring
      _ ≤ (Sw + 1) * c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by gcongr
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hτD, hK4τ⟩
  obtain ⟨_, _, _, hSΩ, _, _, _, _, hPB, hbox⟩ := concreteBox_spec hvalid
  set S := concreteBoxS K4 ε c
  set A := fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)
  have hmv_lo : (100 / 95 : ℝ) * (L - L1) ≤ A (L, α) - A (L1, α) := by
    rcases hL1_L.eq_or_lt with heq | hlt
    · rw [← heq]; simp
    · have hcont : ContinuousOn (fun x => A (x, α)) (Icc L1 L) := fun x hx =>
        (((hPB.atil_contDiffAt (hdom_all x hx)).differentiableAt (by simp)).continuousAt.comp_of_eq
          ((continuous_id.prodMk continuous_const).continuousAt (x := x)) rfl).continuousWithinAt
      have hderiv : ∀ x ∈ Ioo L1 L, HasDerivAt (fun t => A (t, α)) (fderiv ℝ A (x, α) (1, 0)) x := fun x hx => by
        simpa only [Function.comp_def] using
          ((hPB.atil_contDiffAt (hdom_all x (Ioo_subset_Icc_self hx))).differentiableAt (by simp)
            |>.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id' x).prodMk (hasDerivAt_const x α)))
      obtain ⟨ξ, hξm, hξe⟩ := exists_hasDerivAt_eq_slope (fun t => A (t, α)) _ hlt hcont hderiv
      have hV_bd := (fctWarp_S_V_bounds hc0 pbellMin_pos.le hSΩ (hdom_all ξ (Ioo_subset_Icc_self hξm))).1
      have hd10 := (hbox (ξ, α) (hdom_all ξ (Ioo_subset_Icc_self hξm))).2.2.2.1
      have hslope : A (L, α) - A (L1, α) = fderiv ℝ A (ξ, α) (1, 0) * (L - L1) := by
        rw [hξe, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne']
      rw [hslope, hd10]
      exact mul_le_mul_of_nonneg_right hV_bd (sub_nonneg.mpr hL1_L)
  have hmv_hi : A (L, α) - A (L1, α) ≤ (100 / 92 : ℝ) * (L - L1) := by
    refine (abs_le.mp (fctAtil_L_mvt_abs_le hPB (by norm_num : (0 : ℝ) ≤ 100 / 92)
        (fun x hx => hdom_all x (by rwa [min_eq_left hL1_L, max_eq_right hL1_L] at hx)) fun x hx => ?_)).2.trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.mpr hL1_L)])
    rw [min_eq_left hL1_L, max_eq_right hL1_L] at hx
    have hV_bd := fctWarp_S_V_bounds hc0 pbellMin_pos.le hSΩ (hdom_all x (Ioo_subset_Icc_self hx))
    rw [(hbox (x, α) (hdom_all x (Ioo_subset_Icc_self hx))).2.2.2.1,
      abs_of_nonneg (by linarith only [hV_bd.1])]
    exact hV_bd.2
  have hκ0 : 0 ≤ fctKappa c := by unfold fctKappa; positivity
  have hκ_eq : fctKappa c = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) := rfl
  have hv_lo : (100 / 95 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) ≤
      (-fctKappa c * A (L1, α)) - (-fctKappa c * A (L, α)) := by
    calc (100 / 95 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1)
        = fctKappa c * ((100 / 95 : ℝ) * (L - L1)) := by rw [hκ_eq]; ring
      _ ≤ fctKappa c * (A (L, α) - A (L1, α)) := mul_le_mul_of_nonneg_left hmv_lo hκ0
      _ = (-fctKappa c * A (L1, α)) - (-fctKappa c * A (L, α)) := by ring
  have hv_hi : (-fctKappa c * A (L1, α)) - (-fctKappa c * A (L, α)) ≤
      (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) := by
    calc (-fctKappa c * A (L1, α)) - (-fctKappa c * A (L, α))
        = fctKappa c * (A (L, α) - A (L1, α)) := by ring
      _ ≤ fctKappa c * ((100 / 92 : ℝ) * (L - L1)) := mul_le_mul_of_nonneg_left hmv_hi hκ0
      _ = (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) := by rw [hκ_eq]; ring
  have hû1_a1 : |-fctKappa c * A (L1, α) - airyZero 1| ≤ 1 :=
    (hnode hε hcu).1.trans hCu_le1
  have hû1_35 : |-fctKappa c * A (L1, α)| ≤ 3.5 := by
    have ha1 := airyZero_one
    have ha1_abs : |airyZero 1| ≤ 2.4 := by
      rw [abs_of_neg (by linarith only [ha1.2])]; linarith only [ha1.1]
    have htri := abs_add_le (-fctKappa c * A (L1, α) - airyZero 1) (airyZero 1)
    have heq : (-fctKappa c * A (L1, α) - airyZero 1) + airyZero 1 = -fctKappa c * A (L1, α) := by ring
    rw [heq] at htri
    linarith only [htri, hû1_a1, ha1_abs]
  have hûL_M : |-fctKappa c * A (L, α)| ≤ M_u := by
    have htri : |-fctKappa c * A (L, α)| ≤
        |-fctKappa c * A (L1, α)| + |(-fctKappa c * A (L1, α)) - (-fctKappa c * A (L, α))| := by
      calc |-fctKappa c * A (L, α)|
          = |(-fctKappa c * A (L1, α)) - ((-fctKappa c * A (L1, α)) - (-fctKappa c * A (L, α)))| := by
            ring_nf
        _ ≤ _ := abs_sub _ _
    have hc23 : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have h0L1 : 0 ≤ L1 := by
      have : 0 < c0_L * c ^ (-(2 / 3 : ℝ)) := by positivity
      linarith only [this, hL1_lo]
    have hdiff_nn : 0 ≤ (-fctKappa c * A (L1, α)) - (-fctKappa c * A (L, α)) := by
      have : 0 ≤ (100 / 95 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) := by
        have := sub_nonneg.mpr hL1_L; positivity
      linarith only [this, hv_lo]
    rw [abs_of_nonneg hdiff_nn] at htri
    have hL_diff : L - L1 ≤ Sw * c ^ (-(2 / 3 : ℝ)) := by linarith only [h0L1, hL_Sw]
    calc |-fctKappa c * A (L, α)|
        ≤ 3.5 + (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (Sw * c ^ (-(2 / 3 : ℝ))) := by
          have := hv_hi
          have h1 : (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) ≤
              (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (Sw * c ^ (-(2 / 3 : ℝ))) := by gcongr
          linarith only [htri, hû1_35, this, h1]
      _ = 3.5 + (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * Sw * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by ring
      _ ≤ M_u := by rw [hc23, mul_one]; dsimp only [M_u]; linarith
  exact ⟨hc0, by linarith only [hc15000], hτD, hτD_comp, hK4τ, hα_bd, hL1_c12, hL1_c12.trans hc12_1, hL1_L,
    hell_1.1.le, hell_hi, hell_L, hell_1, hdom_all, hv_lo, hv_hi, hû1_a1, hûL_M⟩

/-! ### 3. Exact splitting of `warpSqDensity` on `[L₁, Sw c^{-2/3}]` -/

theorem win_warpSqDensity_split {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4)
    {Sw : ℝ} (hSw : 1 ≤ Sw) :
    ∃ (M_u c₀ : ℝ), 4 ≤ M_u ∧ 15000 ≤ c₀ ∧ ∀ {ε c L : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c → fctWarpL1 h ε c ≤ L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      WinWindowGeom h ε c L Sw M_u ∧
      warpSqDensity K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctXi1 L) =
        winP0 K4 ε c L (fctWarpAlpha h ε c) *
          (airyAi (-fctKappa c * fctAtil (concretePhiTilde K4 ε c)
            (concreteTau0 ε c (concreteBoxS K4 ε c)) (L, fctWarpAlpha h ε c))) ^ 2 +
        winRSqIn K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) L +
        warpSqOut K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) L := by
  obtain ⟨M_u, c_wg, hMu4, _, hwg⟩ := win_window_geom_props hK4 h hSw
  obtain ⟨c_V, _, hV_props⟩ := winVProps_of_window hK4 (show 1 ≤ Sw + 1 by linarith)
  obtain ⟨_, _, c_μ, _, _, _, hmuMix⟩ := win_muMix_diff_and_bounds hK4 (show 1 ≤ Sw + 1 by linarith)
  obtain ⟨_, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  obtain ⟨_, c_sh, _, _, hsh⟩ := warpSqOutComplex_bounds
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_wg ≤ c ∧ c_V ≤ c ∧ c_μ ≤ c ∧ c_χ ≤ c ∧ c_sh ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _) ?_)))))
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iic_mem_nhds (by norm_num))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨M_u, max 15000 c₀, hMu4, le_max_left _ _, fun {ε c L} hε hc hL1_L hL_Sw => ?_⟩
  obtain ⟨hc15, hcwg, hcv, hcμ, hcχ, hcsh, hτ1_14⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hg := hwg hε hcwg hL1_L hL_Sw
  refine ⟨hg, ?_⟩
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hc0 := hg.hc0
  have hc1 : 1 ≤ c := by linarith only [hg.hc10000]
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hg.hτD, hg.hK4τ⟩
  have hvp := hV_props hε hcv hg.hτD hg.hK4τ hg.hα hg.hell_lo hL1_L hg.hell_hi
  have hb2 := hB2 c hcχ _ hvp.hjets_hi
  obtain ⟨_, _, _, hSΩ, _, _, _, _, _, _⟩ := concreteBox_spec hvalid
  have hqΩ : (concreteEll1 ε c L, (1 : ℝ), α) ∈ (concreteBoxS K4 ε c).Ω := by
    rw [hSΩ]; exact concreteEll1_mem_OmT hc0 pbellMin_pos.le (hg.hdom_all L (right_mem_Icc.mpr hL1_L))
  obtain ⟨hT_mono, hT_img, hT_lo, hT_deriv⟩ :=
    fctInnerT_deriv_and_image hc0 hvp.hKV_small hvp.hjets_hi hqΩ hvp.heq_hi
  -- Full integral splits into inner (`1 - outerChiOut`) and outer (`outerChiOut`)
  have hint_full : IntegrableOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
      fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) (Ioi 0) := by
    have hfull0 := integrableOn_fctWarpIntegrand hK4 hε hc1 hg.hτD_comp L1 α
    have hm_eq : ∀ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) * fctWarpIntegrand K4 ε c L1 α τ := fun τ => by
      rw [mellinK0_fctXi1_shift (L1 := L1)]; unfold fctWarpIntegrand; ring
    have hce : Continuous (fun τ : ℝ => Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ))) :=
      Continuous.cexp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
    have hmeas : AEStronglyMeasurable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
        fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) (volume.restrict (Ioi 0)) :=
      (hce.aestronglyMeasurable.mul hfull0.aestronglyMeasurable).congr (ae_of_all _ fun τ => (hm_eq τ).symm)
    exact hfull0.integrable.mono hmeas (ae_of_all _ fun τ => by
      rw [hm_eq τ, norm_mul,
        show ‖Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ))‖ = 1 by
          simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (c * (L - L1) * τ), one_mul])
  have hα_2τ : |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have hsq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [hsq]
    calc |α| ≤ c ^ (-(1 / 2 : ℝ)) := hg.hα
      _ ≤ 2 * c ^ (-(1 / 2 : ℝ)) := by linarith [Real.rpow_nonneg hc0.le (-(1 / 2 : ℝ))]
  have hint_out := (hsh hK4 hε hcsh hg.hτD_comp hg.hK4τ hg.hL1_c12 hα_2τ hg.hell_L_Ioo.2).1
  have hint_in : IntegrableOn (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) *
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) (Ioi 0) := by
    have heq : (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) *
          (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) =
        fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) -
          ((outerChiOut c τ : ℝ) : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
            fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) := by
      ext τ; push_cast; ring
    rw [heq]; exact hint_full.sub hint_out
  have hsplit : ∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
        fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      (∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) +
      warpSqOutComplex K4 ε c L1 α L := by
    unfold warpSqOutComplex
    rw [← MeasureTheory.integral_add hint_in hint_out]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    push_cast; ring
  -- Inner pullback `u = T_L^{-1}(τ)`
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L α
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α)
  obtain ⟨_, _, hmu_pt⟩ := hmuMix hε hcμ hg.hτD hg.hK4τ hg.hα hg.hL1_abs hg.hell_lo hL1_L hg.hell_hi
  have hf_cont : ContinuousOn (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * winMuMix K4 ε c L1 L α u)
      (Icc 0 (fctUc c)) :=
    (hb2.2.2.1.1.continuousOn).mul hmu_pt.1.continuousOn
  have hS_lim := fctS_extUc_eq (c := c) (û := û) hc0 hf_cont
  have hin_eq : ((warpN0 c : ℝ) : ℂ) * ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
      ((warpNu K4 ε c L α : ℝ) : ℂ) *
        fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * winMuMix K4 ε c L1 L α u)) := by
    rw [hS_lim.fctS_eq, fctInner_split_integral hc0 hT_mono hT_img hT_lo.1 hT_deriv,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hT_lt : fctInnerT c V u < 2 * c ^ (-(1 / 4 : ℝ)) :=
      lt_trans (hT_mono (Ioo_subset_Icc_self hu) ⟨(fctUc_pos hc0).le, le_rfl⟩ hu.2) hb2.2.1
    have hT_pos : 0 < fctInnerT c V u := (hT_img ▸ mem_image_of_mem (fctInnerT c V) hu).1
    have hph := fctInnerT_phase_eq hvalid (hg.hdom_all L (right_mem_Icc.mpr hL1_L))
      hvp.hKV_small hvp.hjets_hi hvp.heq_hi (Ioo_subset_Icc_self hu) hT_lt.le
    have hα_τ₁ : |α| ≤ (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
      have : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      rw [this]; exact hg.hα
    have hamp := concreteEdgeAmp_inner (L1 := L1) hK4 hc0 hg.hτD_comp hα_τ₁ hT_pos hT_lt.le
    have hjac := fctInner_edge_jac_eq (K4 := K4) (ε := ε) (c := c) (L1 := L) (α := α) (u := u)
      hc0 hτ1_14 hvp.hKV_small hvp.hjets_hi hvp.heq_hi hu hT_lt
    have hjac_c := congrArg (fun r : ℝ => (r : ℂ)) hjac
    have hpk : phiKill (c ^ (-(1 / 12 : ℝ))) ((fctInnerT c V u : ℂ) * Complex.I) / (uctM (fctInnerT c V u) : ℂ) =
        phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u) := by
      unfold phiKillDivM; simp only [hT_pos.ne', ↓reduceIte]
    rw [mellin_fctWarpA_eq_edge hε hc0 hT_pos, outerPhi_eq_concretePhiTilde hT_pos, hph, hamp]
    simp_rw [mul_div_assoc, hpk]
    have hexp_eq : Complex.exp (Complex.I * ((-(û * u + u ^ 3 / 12) - π / 4 : ℝ) : ℂ)) =
        Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp_eq]
    set T' : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
      (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V ((concreteEll1 ε c L, 1, α), fctInnerY c u) (0, 1))
    dsimp only [winMuMix]
    have h1 : ((warpN0 c * (π ^ 2 / 12) * Real.sqrt (uctMderiv (fctInnerT c V u) / (2 * uctM (fctInnerT c V u))) * T' : ℝ) : ℂ) =
        ((warpNu K4 ε c L α * u ^ (-(1 / 2 : ℝ)) * Jfun S.V fctH ((c ^ (-(1 / 4 : ℝ))) ^ 2)
          ((concreteEll1 ε c L, 1, α), fctInnerY c u) : ℝ) : ℂ) := hjac_c
    calc ((warpN0 c : ℝ) : ℂ) *
          (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) *
              ((((π ^ 2 / 12 * Real.sqrt (uctMderiv (fctInnerT c V u) / (2 * uctM (fctInnerT c V u))) : ℝ) : ℂ)) *
                Complex.exp (-((K4 * fctInnerT c V u ^ 4 : ℝ) : ℂ) +
                  (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c V u) : ℂ) +
                  ((α * fctInnerT c V u ^ 2 : ℝ) : ℂ) + FormalResearch.Asymptotics.binetDiff c (Complex.I * (fctInnerT c V u : ℂ))) *
                ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)))) * ((T' : ℝ) : ℂ))
        = Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) *
            ((warpN0 c * (π ^ 2 / 12) * Real.sqrt (uctMderiv (fctInnerT c V u) / (2 * uctM (fctInnerT c V u))) * T' : ℝ) : ℂ) *
            ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            Complex.exp (-((K4 * fctInnerT c V u ^ 4 : ℝ) : ℂ) +
              (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c V u) : ℂ) +
              ((α * fctInnerT c V u ^ 2 : ℝ) : ℂ) + FormalResearch.Asymptotics.binetDiff c (Complex.I * (fctInnerT c V u : ℂ))) *
            ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)) := by push_cast; ring
      _ = _ := by rw [h1]; push_cast; ring
  have hN0_pos : 0 < warpN0 c := by unfold warpN0; have := warpTauStar_ge; positivity
  have hin_div : (c ^ (1 / 3 : ℝ) / π) * (∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))).re =
      ((c ^ (1 / 3 : ℝ) / π) / warpN0 c * warpNu K4 ε c L α) *
        (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * winMuMix K4 ε c L1 L α u))).re := by
    have hI := congrArg (fun z : ℂ => ((warpN0 c)⁻¹ : ℂ) * z) hin_eq
    have hI2 : ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) *
          (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
        (((warpNu K4 ε c L α / warpN0 c : ℝ) : ℂ)) *
          fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * winMuMix K4 ε c L1 L α u)) := by
      calc ∫ τ in Ioi (0 : ℝ), _ = ((warpN0 c)⁻¹ : ℂ) * (((warpN0 c : ℝ) : ℂ) * ∫ τ in Ioi (0 : ℝ), _) := by
            rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ hN0_pos.ne',
              Complex.ofReal_one, one_mul]
        _ = ((warpN0 c)⁻¹ : ℂ) * (((warpNu K4 ε c L α : ℝ) : ℂ) * fctS û _) := hI
        _ = _ := by push_cast; ring
    have hre := congrArg Complex.re hI2
    rw [Complex.re_ofReal_mul] at hre
    rw [hre]; ring
  have hS1_re : (fctS û (fun _ => (1 : ℂ))).re = 2 * π ^ (3 / 2 : ℝ) * (airyAi û) ^ 2 := by
    rw [(fctInnerSymbolsG0 û).fctS_eq]; unfold fctG0
    simp [Complex.sub_re, Complex.mul_re]
    left; norm_cast
  unfold warpSqDensity
  rw [hsplit, Complex.add_re, mul_add, hin_div]
  unfold winP0 winRSqIn warpSqOut
  dsimp only [V, S, û]
  rw [Complex.sub_re, hS1_re]
  ring

/-! ### 4. `winP0` bounds and Lipschitz estimate -/

lemma win_P0_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) {Sw : ℝ} (hSw : 1 ≤ Sw) :
    ∃ (C_P C_Pd c₀ : ℝ), 0 < C_P ∧ 0 ≤ C_Pd ∧ 15000 ≤ c₀ ∧ ∀ {ε c L : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c → fctWarpL1 h ε c ≤ L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      let L1 := fctWarpL1 h ε c
      let α := fctWarpAlpha h ε c
      let S := concreteBoxS K4 ε c
      let q := (concreteEll1 ε c L, (1 : ℝ), α)
      (1 / 2 : ℝ) * (1 / 2 * Real.sqrt π * ceCs ^ (5 / 2 : ℝ)) * c ^ (1 / 6 : ℝ) ≤ winP0 K4 ε c L α ∧
      winP0 K4 ε c L α ≤ C_P * c ^ (1 / 6 : ℝ) ∧
      |winP0 K4 ε c L α - winP0 K4 ε c L1 α| ≤ C_Pd * c ^ (1 / 6 : ℝ) * (L - L1) ∧
      |warpNu K4 ε c L α - warpNu K4 ε c L1 α| ≤ C_Pd * (L - L1) ∧
      |warpNu K4 ε c L α - 1| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ∧
      |warpNu K4 ε c L α| ≤ 2 ∧
      |(|uctCAi| * c ^ (-(5 / 6 : ℝ)) * winP0 K4 ε c L α * (fctKappa c * S.V (q, S.A q))) - ceK / ceCs| ≤
        ((2 * pbcV * pbC0 + pbcV * pbC0 / warpTauStar) * (ceK / ceCs)) * c ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨_, c_wg, _, _, hwg⟩ := win_window_geom_props hK4 h hSw
  obtain ⟨c_V, _, hV_props⟩ := winVProps_of_window hK4 (show 1 ≤ Sw + 1 by linarith)
  obtain ⟨C_V, c_Vd, hCV0, _, hV_diff⟩ := win_V_diff_sym hK4 (show 1 ≤ Sw + 1 by linarith)
  let C_nu : ℝ := C_V / (Real.sqrt warpTauStar * (Real.sqrt 1.04 + Real.sqrt 1.04))
  let C_P0 : ℝ := 1 / 2 * Real.sqrt π * ceCs ^ (5 / 2 : ℝ)
  let C_P : ℝ := 2 * C_P0
  let C_Pd : ℝ := max C_nu (C_P0 * C_nu)
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_wg ≤ c ∧ c_V ≤ c ∧ c_Vd ≤ c ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.02 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _) ?_)))
    have ht : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
      simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
    exact ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.02))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_P, C_Pd, max 15000 c₀, by have := Real.pi_pos; have := ceCs_pos; positivity,
    by positivity, le_max_left _ _, fun {ε c L} hε hc hL1_L hL_Sw => ?_⟩
  obtain ⟨hc15, hcwg, hcv, hcvd, hV0_sm⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hg := hwg hε hcwg hL1_L hL_Sw
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hc0 := hg.hc0
  have hvp := hV_props hε hcv hg.hτD hg.hK4τ hg.hα hg.hell_lo hL1_L hg.hell_hi
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hg.hτD, hg.hK4τ⟩
  obtain ⟨_, _, _, hSΩ, _, _, hSε, hScV, _, _⟩ := concreteBox_spec hvalid
  set S := concreteBoxS K4 ε c
  have hτ₁_sq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hSV_bd : ∀ q ∈ S.Ω, ∀ y ∈ Yint, |S.V (q, y) - warpTauStar| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
    intro q hq y hy
    have h0 := (S.out.2.2.2.2.2.2.2.2.2.1).2 0 (by norm_num) (q, y) ⟨hq, hy⟩
    rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs, hScV, hSε, hτ₁_sq] at h0
    simpa only [ChartSetup.V, ChartSetup.D, tauStar_eq_dStar_inv, warpTauStar, mul_assoc] using h0
  have hqL_Ω : (concreteEll1 ε c L, (1 : ℝ), α) ∈ S.Ω := by
    rw [hSΩ]; exact concreteEll1_mem_OmT hc0 pbellMin_pos.le (hg.hdom_all L (right_mem_Icc.mpr hL1_L))
  have hq1_Ω : (concreteEll1 ε c L1, (1 : ℝ), α) ∈ S.Ω := by
    rw [hSΩ]; exact concreteEll1_mem_OmT hc0 pbellMin_pos.le (hg.hdom_all L1 (left_mem_Icc.mpr hL1_L))
  have h0Y : (0 : ℝ) ∈ Yint := ⟨by norm_num, by norm_num⟩
  have hVL0 : |concreteInnerV K4 ε c L α 0 - warpTauStar| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
    rw [hvp.heq_hi 0 ⟨le_rfl, by norm_num⟩]; exact hSV_bd _ hqL_Ω 0 h0Y
  have hV10 : |concreteInnerV K4 ε c L1 α 0 - warpTauStar| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
    rw [hvp.heq_lo 0 ⟨le_rfl, by norm_num⟩]; exact hSV_bd _ hq1_Ω 0 h0Y
  have hnuL := warpNu_sub_one_le (K4 := K4) (ε := ε) (L1 := L) (α := α) hc0 hVL0 (by linarith only [hV0_sm])
  have hτs_ge : (1.06 : ℝ) ≤ warpTauStar := warpTauStar_ge
  have hτs_pos : 0 < warpTauStar := by linarith only [hτs_ge]
  have hVL0_ge : (1.04 : ℝ) ≤ concreteInnerV K4 ε c L α 0 := by
    have := (abs_le.mp (hVL0.trans hV0_sm)).1; linarith only [this, hτs_ge]
  have hV10_ge : (1.04 : ℝ) ≤ concreteInnerV K4 ε c L1 α 0 := by
    have := (abs_le.mp (hV10.trans hV0_sm)).1; linarith only [this, hτs_ge]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have h0Uc : (0 : ℝ) ∈ Icc 0 (fctUc c) := ⟨le_rfl, hUc0.le⟩
  have hV0_diff : |concreteInnerV K4 ε c L α 0 - concreteInnerV K4 ε c L1 α 0| ≤ C_V * (L - L1) := by
    have hd := (hV_diff hε hcvd hg.hτD hg.hK4τ hg.hα hg.hell_lo hL1_L hg.hell_hi).1.2 0 (by omega) 0 h0Uc
    rw [iteratedDerivWithin_zero] at hd
    dsimp only at hd
    have hY0 : fctInnerY c 0 = 0 := by unfold fctInnerY; simp
    rw [hY0, ← hvp.heq_hi 0 ⟨le_rfl, by norm_num⟩, ← hvp.heq_lo 0 ⟨le_rfl, by norm_num⟩] at hd
    simp only [add_zero, Nat.cast_zero, sub_self, Real.rpow_zero, mul_one,
      Complex.norm_real, Real.norm_eq_abs] at hd
    exact hd
  have hnu_diff : |warpNu K4 ε c L α - warpNu K4 ε c L1 α| ≤ C_nu * (L - L1) := by
    unfold warpNu
    have hVL_pos : 0 < concreteInnerV K4 ε c L α 0 := by linarith only [hVL0_ge]
    have hV1_pos : 0 < concreteInnerV K4 ε c L1 α 0 := by linarith only [hV10_ge]
    have hden_ge : Real.sqrt warpTauStar * (Real.sqrt 1.04 + Real.sqrt 1.04) ≤
        Real.sqrt warpTauStar * (Real.sqrt (concreteInnerV K4 ε c L α 0) +
          Real.sqrt (concreteInnerV K4 ε c L1 α 0)) := by
      gcongr
    have hden_pos : 0 < Real.sqrt warpTauStar * (Real.sqrt 1.04 + Real.sqrt 1.04) := by positivity
    have hden2_pos : 0 < Real.sqrt warpTauStar * (Real.sqrt (concreteInnerV K4 ε c L α 0) +
        Real.sqrt (concreteInnerV K4 ε c L1 α 0)) := lt_of_lt_of_le hden_pos hden_ge
    have hsq_eq : Real.sqrt (concreteInnerV K4 ε c L α 0 / warpTauStar) -
          Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) =
        (concreteInnerV K4 ε c L α 0 - concreteInnerV K4 ε c L1 α 0) /
          (Real.sqrt warpTauStar * (Real.sqrt (concreteInnerV K4 ε c L α 0) +
            Real.sqrt (concreteInnerV K4 ε c L1 α 0))) := by
      rw [Real.sqrt_div hVL_pos.le, Real.sqrt_div hV1_pos.le]
      have hsL := Real.sq_sqrt hVL_pos.le
      have hs1 := Real.sq_sqrt hV1_pos.le
      have hsτ : Real.sqrt warpTauStar ≠ 0 := (Real.sqrt_pos.mpr hτs_pos).ne'
      have hsum_ne : Real.sqrt (concreteInnerV K4 ε c L α 0) + Real.sqrt (concreteInnerV K4 ε c L1 α 0) ≠ 0 := by positivity
      field_simp [hsτ, hsum_ne]
      nlinarith only [hsL, hs1]
    rw [hsq_eq, abs_div, abs_of_pos hden2_pos]
    calc |concreteInnerV K4 ε c L α 0 - concreteInnerV K4 ε c L1 α 0| /
          (Real.sqrt warpTauStar * (Real.sqrt (concreteInnerV K4 ε c L α 0) +
            Real.sqrt (concreteInnerV K4 ε c L1 α 0)))
        ≤ (C_V * (L - L1)) / (Real.sqrt warpTauStar * (Real.sqrt (concreteInnerV K4 ε c L α 0) +
            Real.sqrt (concreteInnerV K4 ε c L1 α 0))) := div_le_div_of_nonneg_right hV0_diff hden2_pos.le
      _ ≤ (C_V * (L - L1)) / (Real.sqrt warpTauStar * (Real.sqrt 1.04 + Real.sqrt 1.04)) := by
          exact div_le_div_of_nonneg_left (mul_nonneg hCV0 (sub_nonneg.mpr hL1_L)) hden_pos hden_ge
      _ = C_nu * (L - L1) := by dsimp only [C_nu]; ring
  have hnuL_lo : (1 / 2 : ℝ) ≤ warpNu K4 ε c L α := by
    have := (abs_le.mp (hnuL.1.trans hV0_sm)).1; linarith only [this]
  have hP0_eq : ∀ x : ℝ, winP0 K4 ε c x α = C_P0 * c ^ (1 / 6 : ℝ) * warpNu K4 ε c x α := fun x => by
    unfold winP0
    rw [show (c ^ (1 / 3 : ℝ) / π) / warpN0 c * warpNu K4 ε c x α * (2 * π ^ (3 / 2 : ℝ)) =
        ((c ^ (1 / 3 : ℝ) / π) / warpN0 c * (2 * π ^ (3 / 2 : ℝ))) * warpNu K4 ε c x α by ring,
      win_pref_simp hc0]
  have hC_P0_pos : 0 < C_P0 := by have := Real.pi_pos; have := ceCs_pos; positivity
  have hP0_lo : (1 / 2 : ℝ) * C_P0 * c ^ (1 / 6 : ℝ) ≤ winP0 K4 ε c L α := by
    rw [hP0_eq L]
    calc (1 / 2 : ℝ) * C_P0 * c ^ (1 / 6 : ℝ) = C_P0 * c ^ (1 / 6 : ℝ) * (1 / 2 : ℝ) := by ring
      _ ≤ C_P0 * c ^ (1 / 6 : ℝ) * warpNu K4 ε c L α := by gcongr
  have hP0_hi : winP0 K4 ε c L α ≤ C_P * c ^ (1 / 6 : ℝ) := by
    rw [hP0_eq L]
    have hnu2 : warpNu K4 ε c L α ≤ 2 := (abs_le.mp hnuL.2).2
    calc C_P0 * c ^ (1 / 6 : ℝ) * warpNu K4 ε c L α ≤ C_P0 * c ^ (1 / 6 : ℝ) * 2 := by gcongr
      _ = C_P * c ^ (1 / 6 : ℝ) := by dsimp only [C_P]; ring
  have hP0_diff : |winP0 K4 ε c L α - winP0 K4 ε c L1 α| ≤ C_Pd * c ^ (1 / 6 : ℝ) * (L - L1) := by
    rw [hP0_eq L, hP0_eq L1, show C_P0 * c ^ (1 / 6 : ℝ) * warpNu K4 ε c L α -
        C_P0 * c ^ (1 / 6 : ℝ) * warpNu K4 ε c L1 α =
      (C_P0 * c ^ (1 / 6 : ℝ)) * (warpNu K4 ε c L α - warpNu K4 ε c L1 α) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < C_P0 * c ^ (1 / 6 : ℝ))]
    calc C_P0 * c ^ (1 / 6 : ℝ) * |warpNu K4 ε c L α - warpNu K4 ε c L1 α|
        ≤ C_P0 * c ^ (1 / 6 : ℝ) * (C_nu * (L - L1)) := by gcongr
      _ = (C_P0 * C_nu) * c ^ (1 / 6 : ℝ) * (L - L1) := by ring
      _ ≤ C_Pd * c ^ (1 / 6 : ℝ) * (L - L1) := by
          have := sub_nonneg.mpr hL1_L; gcongr; exact le_max_right _ _
  have hnorm_prod : |uctCAi| * c ^ (-(5 / 6 : ℝ)) * C_P0 * c ^ (1 / 6 : ℝ) * (fctKappa c * warpTauStar) = ceK / ceCs := by
    have hc_tot : c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 6 : ℝ) * c ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    have h2_tot : (2 : ℝ) ^ (5 / 3 : ℝ) * (1 / 2 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) = 2 ^ (0 : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num, ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num)]; congr 1; norm_num
    have hτs_eq : warpTauStar = ceK / ceCs := by
      unfold warpTauStar ceK ceCs
      have h12 : (12 : ℝ) / π ^ 2 = (2 : ℝ) ^ 2 / (π ^ 2 / 3) := by ring
      have h2sq : (0 : ℝ) < (2 : ℝ) ^ 2 := by positivity
      have hpi3 : (0 : ℝ) < π ^ 2 / 3 := by have := Real.pi_pos; positivity
      rw [h12, Real.div_rpow h2sq.le hpi3.le, ← Real.rpow_natCast (2 : ℝ),
        ← Real.rpow_mul (by norm_num)]; norm_num
    have huct_abs : |uctCAi| = (2 : ℝ) ^ (5 / 3 : ℝ) / (Real.sqrt π * ceCs ^ (5 / 2 : ℝ)) := by
      unfold uctCAi
      have hden : 0 < Real.sqrt π * ceCs ^ (5 / 2 : ℝ) := by
        have := Real.pi_pos; have := ceCs_pos; positivity
      rw [neg_div, abs_neg, abs_of_pos (div_pos (by positivity) hden)]
    rw [huct_abs]
    unfold fctKappa
    rw [hτs_eq]
    have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have hcs : 0 < ceCs := ceCs_pos
    calc ((2 : ℝ) ^ (5 / 3 : ℝ) / (Real.sqrt π * ceCs ^ (5 / 2 : ℝ))) * c ^ (-(5 / 6 : ℝ)) *
          (1 / 2 * Real.sqrt π * ceCs ^ (5 / 2 : ℝ)) * c ^ (1 / 6 : ℝ) *
          ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (ceK / ceCs))
        = ((2 : ℝ) ^ (5 / 3 : ℝ) * (1 / 2 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ))) *
            (c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 6 : ℝ) * c ^ (2 / 3 : ℝ)) *
            ((Real.sqrt π * ceCs ^ (5 / 2 : ℝ)) / (Real.sqrt π * ceCs ^ (5 / 2 : ℝ))) * (ceK / ceCs) := by ring
      _ = 1 * 1 * 1 * (ceK / ceCs) := by
          rw [h2_tot, Real.rpow_zero, hc_tot, div_self (by positivity)]
      _ = ceK / ceCs := by ring
  have hqA_mem : S.A (concreteEll1 ε c L, (1 : ℝ), α) ∈ Yint := S.A_mem hqL_Ω
  have hSVA : |S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) - warpTauStar| ≤
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := hSV_bd _ hqL_Ω _ hqA_mem
  have hSV_div : |S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar - 1| ≤
      (pbcV * pbC0 / warpTauStar) * c ^ (-(1 / 2 : ℝ)) := by
    rw [show S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar - 1 =
        (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) - warpTauStar) / warpTauStar by
      field_simp [hτs_pos.ne'], abs_div, abs_of_pos hτs_pos]
    calc _ ≤ (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) / warpTauStar :=
          div_le_div_of_nonneg_right hSVA hτs_pos.le
      _ = (pbcV * pbC0 / warpTauStar) * c ^ (-(1 / 2 : ℝ)) := by ring
  have hSV_le2 : |S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar| ≤ 2 := by
    have h1 := abs_le.mp (hSVA.trans hV0_sm)
    have hge : 0 ≤ S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar := by
      have : 0 ≤ S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) := by
        linarith only [h1.1, hτs_ge]
      exact div_nonneg this hτs_pos.le
    rw [abs_of_nonneg hge, div_le_iff₀ hτs_pos]
    linarith only [h1.2, hτs_ge]
  have hprod_err : |(|uctCAi| * c ^ (-(5 / 6 : ℝ)) * winP0 K4 ε c L α *
        (fctKappa c * S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)))) -
        ceK / ceCs| ≤ ((2 * pbcV * pbC0 + pbcV * pbC0 / warpTauStar) * (ceK / ceCs)) * c ^ (-(1 / 2 : ℝ)) := by
    have hfac : |uctCAi| * c ^ (-(5 / 6 : ℝ)) * winP0 K4 ε c L α *
          (fctKappa c * S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α))) =
        (ceK / ceCs) * (warpNu K4 ε c L α *
          (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar)) := by
      rw [hP0_eq L, ← hnorm_prod]
      field_simp [hτs_pos.ne']
    rw [hfac, show (ceK / ceCs) * (warpNu K4 ε c L α *
          (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar)) -
          ceK / ceCs =
        (ceK / ceCs) * ((warpNu K4 ε c L α - 1) *
          (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar) +
          (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar - 1)) by ring,
      abs_mul, abs_of_pos (div_pos ceK_pos ceCs_pos)]
    have hsub_le : |(warpNu K4 ε c L α - 1) *
          (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar) +
          (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar - 1)| ≤
        (2 * pbcV * pbC0 + pbcV * pbC0 / warpTauStar) * c ^ (-(1 / 2 : ℝ)) := by
      calc _ ≤ |(warpNu K4 ε c L α - 1) *
              (S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar)| +
            |S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar - 1| :=
            abs_add_le _ _
        _ = |warpNu K4 ε c L α - 1| *
              |S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar| +
            |S.V ((concreteEll1 ε c L, (1 : ℝ), α), S.A (concreteEll1 ε c L, (1 : ℝ), α)) / warpTauStar - 1| := by
            rw [abs_mul]
        _ ≤ (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) * 2 + (pbcV * pbC0 / warpTauStar) * c ^ (-(1 / 2 : ℝ)) :=
            add_le_add (mul_le_mul hnuL.1 hSV_le2 (abs_nonneg _) ((abs_nonneg _).trans hnuL.1)) hSV_div
        _ = (2 * pbcV * pbC0 + pbcV * pbC0 / warpTauStar) * c ^ (-(1 / 2 : ℝ)) := by ring
    calc ceK / ceCs * _ ≤ ceK / ceCs * ((2 * pbcV * pbC0 + pbcV * pbC0 / warpTauStar) * c ^ (-(1 / 2 : ℝ))) := by
          gcongr; exact (div_pos ceK_pos ceCs_pos).le
      _ = ((2 * pbcV * pbC0 + pbcV * pbC0 / warpTauStar) * (ceK / ceCs)) * c ^ (-(1 / 2 : ℝ)) := by ring
  refine ⟨hP0_lo, hP0_hi, hP0_diff, hnu_diff.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr hL1_L)),
    hnuL.1, hnuL.2, hprod_err⟩

/-- info: 'FormalResearch.SignUncertainty.win_warpSqDensity_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_warpSqDensity_split

/-- info: 'FormalResearch.SignUncertainty.win_P0_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_P0_bounds

end FormalResearch.SignUncertainty
