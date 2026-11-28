/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinLip

/-!
# Inner Abel-symbol remainder `winRSqIn` bounds on `[L₁, Sw c^{-2/3}]` (`fct:warp-win`)

Proves `win_RSqIn_bounds`:
* `|winRSqIn K4 ε c L1 α L| ≤ C_R * c^{-1}`;
* `|winRSqIn K4 ε c L1 α L - winRSqIn K4 ε c L1 α L1| ≤ C_R * c^{-(1/3)} * (L - L1)`
uniformly for `ε = ±1`, `c₀ ≤ c`, and `fctWarpL1 h ε c ≤ L ≤ Sw * c^{-(2/3)}`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

private lemma win_deltaS_sym_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4)
    {Sw : ℝ} (hSw : 1 ≤ Sw) :
    ∃ (C_pt C_lip M_u c₀ : ℝ), 0 ≤ C_pt ∧ 0 ≤ C_lip ∧ 4 ≤ M_u ∧ 15000 ≤ c₀ ∧
      ∀ {ε c L : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        fctWarpL1 h ε c ≤ L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
        let L1 := fctWarpL1 h ε c
        let α := fctWarpAlpha h ε c
        let S := concreteBoxS K4 ε c
        let deltaS : ℝ → ℂ := fun x =>
          fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (x, α))
            (extUc c (fun u => ((fctInnerChi outerChiIn c (concreteInnerV K4 ε c x α) u : ℝ) : ℂ) *
              winMuMix K4 ε c L1 x α u)) -
          fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (x, α))
            (fun _ => (1 : ℂ))
        ‖deltaS L‖ ≤ C_pt * c ^ (-(7 / 6 : ℝ)) ∧
        ‖deltaS L1‖ ≤ C_pt * c ^ (-(7 / 6 : ℝ)) ∧
        ‖deltaS L - deltaS L1‖ ≤ C_lip * c ^ (-(1 / 2 : ℝ)) * (L - L1) := by
  obtain ⟨M_u, c_wg, hMu4, _, hwg⟩ := win_window_geom_props hK4 h hSw
  obtain ⟨c_V, _, hV_props⟩ := winVProps_of_window hK4 (show 1 ≤ Sw + 1 by linarith)
  obtain ⟨C_μ, C_d, c_μ, hCμ0, hCd0, _, hmuMix⟩ := win_muMix_diff_and_bounds hK4 (show 1 ≤ Sw + 1 by linarith)
  obtain ⟨C_χd, c_χd, hCχd0, _, hχ_diff⟩ := win_chi_diff_sym hK4 (show 1 ≤ Sw + 1 by linarith)
  obtain ⟨C_χ, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  obtain ⟨C_1, c_1, hC10, _, hmu1⟩ := win_mu_diag_sub_one hK4
  obtain ⟨c_adm, _, hadm_fn⟩ := fctWarpPair_adm hK4 h
  have hMpos : 0 < M_u := by linarith only [hMu4]
  obtain ⟨C_lip10, hClip10, hLip10⟩ := win_fctS_û_lipschitz (M := M_u) (p := 10) hMpos (by norm_num)
  obtain ⟨C_lip20, hClip20, hLip20⟩ := win_fctS_û_lipschitz (M := M_u) (p := 20) hMpos (by norm_num)
  obtain ⟨C_S10, hCS10, hA10⟩ := FctSymA.fctInnerSymbolsA M_u 8 10 hMpos (by norm_num) (by norm_num)
  obtain ⟨C_S11, hCS11, hA11⟩ := FctSymA.fctInnerSymbolsA M_u 8 11 hMpos (by norm_num) (by norm_num)
  obtain ⟨C_S20, hCS20, hA20⟩ := FctSymA.fctInnerSymbolsA M_u 8 20 hMpos (by norm_num) (by norm_num)
  obtain ⟨C_S1, hCS1, hA1⟩ := FctSymA.fctInnerSymbolsA M_u 8 1 hMpos (by norm_num) (by norm_num)
  let cU_lim : ℝ := (max 6 (Real.sqrt (8 * M_u)) / 2.7) ^ (12 : ℕ)
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_wg ≤ c ∧ c_V ≤ c ∧ c_μ ≤ c ∧ c_χd ≤ c ∧ c_χ ≤ c ∧
      c_1 ≤ c ∧ c_adm ≤ c ∧ cU_lim ≤ c :=
    Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
          (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
            (eventually_ge_atTop _))))))))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  let Bχ : ℝ := |C_χ|
  let B_base : ℝ := 2 ^ 8 * Bχ * C_1
  let B_tail : ℝ := max Bχ 1
  let B_diff_coef : ℝ := 2 ^ 8 * Bχ * C_d
  let B_chi_base : ℝ := 2 ^ 8 * C_χd * C_1
  let C_pt : ℝ := C_S10 * B_diff_coef * (Sw + 1) + (C_S10 * B_base + C_S20 * B_tail)
  let K_slope : ℝ := (100 / 92 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ))
  let C_lip : ℝ := C_S10 * B_diff_coef + C_lip10 * B_base * K_slope +
    C_S11 * B_chi_base + C_lip20 * B_tail * K_slope + C_S1 * C_χd
  refine ⟨C_pt, C_lip, M_u, max 15000 c₀, by positivity, by positivity, hMu4, le_max_left _ _,
    fun {ε c L} hε hc hL1_L hL_Sw => ?_⟩
  obtain ⟨hc15, hcwg, hcv, hcμ, hcχd, hcχ, hc1_lim, hcadm, hcu_lim⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hg := hwg hε hcwg hL1_L hL_Sw
  have hg1 := hwg hε hcwg le_rfl (hg.hL1_le.trans hL_Sw)
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hc0 : 0 < c := hg.hc0
  have hc1 : 1 ≤ c := by linarith only [hc15]
  have hvp := hV_props hε hcv hg.hτD hg.hK4τ hg.hα hg.hell_lo hL1_L hg.hell_hi
  have hb2_L := hB2 c hcχ _ hvp.hjets_hi
  have hb2_1 := hB2 c hcχ _ hvp.hjets_lo
  have hadm := (hadm_fn hε hcadm).1
  have hμ_diff := (hmuMix hε hcμ hg.hτD hg.hK4τ hg.hα hg.hL1_abs hg.hell_lo hL1_L hg.hell_hi).1
  have hχd := hχ_diff hε hcχd hg.hτD hg.hK4τ hg.hα hg.hell_lo hL1_L hg.hell_hi
  have hμ1 := hmu1 hε hc1_lim hadm hg.hα
  set S := concreteBoxS K4 ε c
  set V_L := concreteInnerV K4 ε c L α
  set V_1 := concreteInnerV K4 ε c L1 α
  set û_L := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α)
  set û_1 := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  have hû_L : |û_L| ≤ M_u := hg.hûL_M
  have hû_1 : |û_1| ≤ M_u := hg1.hûL_M
  have hBχ_le : C_χ ≤ Bχ := le_abs_self C_χ
  have hBχ0 : 0 ≤ Bχ := abs_nonneg C_χ
  have hL10 : 0 ≤ L - L1 := sub_nonneg.mpr hL1_L
  have h_g_diff : FctSymCls 8 10 (B_diff_coef * c ^ (-(2 / 3 : ℝ)) * (L - L1))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V_L u : ℝ) : ℂ) *
        (winMuMix K4 ε c L1 L α u - winMuMix K4 ε c L1 L1 α u))) := by
    have hχ_s := hb2_L.2.2.1.mono_B Icc_subset_Ici_self hBχ_le
    have h0 := extUc_chi_symCls hc1 (by positivity) hBχ0 hχ_s hb2_L.1 hμ_diff
    exact h0.mono_B Set.Subset.rfl (le_of_eq (by dsimp [B_diff_coef]; ring))
  have h_g_base_L : FctSymCls 8 10 (B_base * c ^ (-(7 / 6 : ℝ)))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V_L u : ℝ) : ℂ) * (winMuMix K4 ε c L1 L1 α u - 1))) := by
    have hχ_s := hb2_L.2.2.1.mono_B Icc_subset_Ici_self hBχ_le
    exact (extUc_chi_symCls hc1 (by positivity) hBχ0 hχ_s hb2_L.1 hμ1).mono_B
      Set.Subset.rfl (le_of_eq (by dsimp [B_base]; ring))
  have h_g_base_1 : FctSymCls 8 10 (B_base * c ^ (-(7 / 6 : ℝ)))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ) * (winMuMix K4 ε c L1 L1 α u - 1))) := by
    have hχ_s := hb2_1.2.2.1.mono_B Icc_subset_Ici_self hBχ_le
    exact (extUc_chi_symCls hc1 (by positivity) hBχ0 hχ_s hb2_1.1 hμ1).mono_B
      Set.Subset.rfl (le_of_eq (by dsimp [B_base]; ring))
  have h_g_tail_L : FctSymCls 8 20 (B_tail * c ^ (-(5 / 3 : ℝ))) (fun u => 1 - chiExt c V_L u) :=
    (win_one_sub_chi_sym20 hc1 hBχ0 (hb2_L.2.2.2.1.mono_B Icc_subset_Ici_self hBχ_le)
      hb2_L.1 hb2_L.2.2.2.2).1
  have h_g_tail_1 : FctSymCls 8 20 (B_tail * c ^ (-(5 / 3 : ℝ))) (fun u => 1 - chiExt c V_1 u) :=
    (win_one_sub_chi_sym20 hc1 hBχ0 (hb2_1.2.2.2.1.mono_B Icc_subset_Ici_self hBχ_le)
      hb2_1.1 hb2_1.2.2.2.2).1
  have hDu := uniqueDiffOn_Icc (fctUc_pos hc0)
  have h_chi_diff_base : FctSymCls 8 11 (B_chi_base * c ^ (-(5 / 4 : ℝ)) * (L - L1))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V_L u - fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ) *
        (winMuMix K4 ε c L1 L1 α u - 1))) := by
    have hc54 : c ^ (-(1 / 12 : ℝ)) * c ^ (-(7 / 6 : ℝ)) = c ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hBeq : 2 ^ 8 * (C_χd * c ^ (-(1 / 12 : ℝ)) * (L - L1)) * (C_1 * c ^ (-(7 / 6 : ℝ))) =
        B_chi_base * c ^ (-(5 / 4 : ℝ)) * (L - L1) := by
      calc 2 ^ 8 * (C_χd * c ^ (-(1 / 12 : ℝ)) * (L - L1)) * (C_1 * c ^ (-(7 / 6 : ℝ)))
          = B_chi_base * (c ^ (-(1 / 12 : ℝ)) * c ^ (-(7 / 6 : ℝ))) * (L - L1) := by dsimp [B_chi_base]; ring
        _ = B_chi_base * c ^ (-(5 / 4 : ℝ)) * (L - L1) := by rw [hc54]
    have hmul := (hχd.1.mul Icc_subset_Ici_self hDu hμ1).mono_B Icc_subset_Ici_self hBeq.le
    refine extUc_mem_symCls hc1 (by positivity)
      (hmul.mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (1 + 10 : ℝ) ≤ 11))
      fun u hu => by rw [hχd.2.2 u hu]; simp
  have h_chi_diff_tail : FctSymCls 8 1 (C_χd * c ^ (-(1 / 12 : ℝ)) * (L - L1))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V_L u - fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ))) :=
    extUc_mem_symCls hc1 (by positivity) hχd.1 hχd.2.2
  let g_diff : ℝ → ℂ := extUc c (fun u => ((fctInnerChi outerChiIn c V_L u : ℝ) : ℂ) *
    (winMuMix K4 ε c L1 L α u - winMuMix K4 ε c L1 L1 α u))
  let g_baseL : ℝ → ℂ := extUc c (fun u => ((fctInnerChi outerChiIn c V_L u : ℝ) : ℂ) * (winMuMix K4 ε c L1 L1 α u - 1))
  let g_base1 : ℝ → ℂ := extUc c (fun u => ((fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ) * (winMuMix K4 ε c L1 L1 α u - 1))
  let g_tailL : ℝ → ℂ := fun u => 1 - chiExt c V_L u
  let g_tail1 : ℝ → ℂ := fun u => 1 - chiExt c V_1 u
  have hfL_eq : extUc c (fun u => ((fctInnerChi outerChiIn c V_L u : ℝ) : ℂ) * winMuMix K4 ε c L1 L α u) =
      fun u => g_diff u + g_baseL u - g_tailL u + 1 := by
    ext u; dsimp only [g_diff, g_baseL, g_tailL, chiExt, extUc]; split_ifs <;> ring
  have hf1_eq : extUc c (fun u => ((fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ) * winMuMix K4 ε c L1 L1 α u) =
      fun u => g_base1 u - g_tail1 u + 1 := by
    ext u; dsimp only [g_base1, g_tail1, chiExt, extUc]; split_ifs <;> ring
  have hSL : fctS û_L (extUc c (fun u => ((fctInnerChi outerChiIn c V_L u : ℝ) : ℂ) *
      winMuMix K4 ε c L1 L α u)) - fctS û_L (fun _ => (1 : ℂ)) =
      fctS û_L g_diff + fctS û_L g_baseL - fctS û_L g_tailL := by
    have h1 := one_symCls 8
    have hadd_gb : FctSymCls 8 10 (B_diff_coef * c ^ (-(2 / 3 : ℝ)) * (L - L1) + B_base * c ^ (-(7 / 6 : ℝ)))
        (fun u => g_diff u + g_baseL u) :=
      h_g_diff.add (uniqueDiffOn_Ici 0) h_g_base_L
    have hsub_t : FctSymCls 8 20 ((B_diff_coef * c ^ (-(2 / 3 : ℝ)) * (L - L1) + B_base * c ^ (-(7 / 6 : ℝ))) +
        B_tail * c ^ (-(5 / 3 : ℝ))) (fun u => g_diff u + g_baseL u - g_tailL u) :=
      (hadd_gb.mono_p Set.Subset.rfl (by positivity) (by norm_num)).sub (uniqueDiffOn_Ici 0) h_g_tail_L
    have hs1 := win_fctS_add hMpos hû_L (by norm_num) (by norm_num) (by positivity) (by positivity) hsub_t h1
    have hs2 := win_fctS_sub hMpos hû_L (by norm_num) (by norm_num) (by positivity) (by positivity) hadd_gb h_g_tail_L
    have hs3 := win_fctS_add hMpos hû_L (by norm_num) (by norm_num) (by positivity) (by positivity) h_g_diff h_g_base_L
    rw [hfL_eq, hs1, hs2, hs3]; ring
  have hS1 : fctS û_1 (extUc c (fun u => ((fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ) *
      winMuMix K4 ε c L1 L1 α u)) - fctS û_1 (fun _ => (1 : ℂ)) =
      fctS û_1 g_base1 - fctS û_1 g_tail1 := by
    have h1 := one_symCls 8
    have hsub_t : FctSymCls 8 20 (B_base * c ^ (-(7 / 6 : ℝ)) + B_tail * c ^ (-(5 / 3 : ℝ)))
        (fun u => g_base1 u - g_tail1 u) :=
      (h_g_base_1.mono_p Set.Subset.rfl (by positivity) (by norm_num)).sub (uniqueDiffOn_Ici 0) h_g_tail_1
    have hs1 := win_fctS_add hMpos hû_1 (by norm_num) (by norm_num) (by positivity) (by positivity) hsub_t h1
    have hs2 := win_fctS_sub hMpos hû_1 (by norm_num) (by norm_num) (by positivity) (by positivity) h_g_base_1 h_g_tail_1
    rw [hf1_eq, hs1, hs2]; ring
  have h_bd_gdiff : ‖fctS û_L g_diff‖ ≤ C_S10 * B_diff_coef * c ^ (-(2 / 3 : ℝ)) * (L - L1) :=
    (hA10 û_L _ g_diff hû_L (by positivity) h_g_diff).2.1.trans_eq (by ring)
  have h_bd_baseL : ‖fctS û_L g_baseL‖ ≤ C_S10 * B_base * c ^ (-(7 / 6 : ℝ)) :=
    (hA10 û_L _ g_baseL hû_L (by positivity) h_g_base_L).2.1.trans_eq (by ring)
  have h_bd_base1 : ‖fctS û_1 g_base1‖ ≤ C_S10 * B_base * c ^ (-(7 / 6 : ℝ)) :=
    (hA10 û_1 _ g_base1 hû_1 (by positivity) h_g_base_1).2.1.trans_eq (by ring)
  have h_bd_tailL : ‖fctS û_L g_tailL‖ ≤ C_S20 * B_tail * c ^ (-(5 / 3 : ℝ)) :=
    (hA20 û_L _ g_tailL hû_L (by positivity) h_g_tail_L).2.1.trans_eq (by ring)
  have h_bd_tail1 : ‖fctS û_1 g_tail1‖ ≤ C_S20 * B_tail * c ^ (-(5 / 3 : ℝ)) :=
    (hA20 û_1 _ g_tail1 hû_1 (by positivity) h_g_tail_1).2.1.trans_eq (by ring)
  have hc53_76 : c ^ (-(5 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have h_Δ1_bd : ‖fctS û_1 g_base1 - fctS û_1 g_tail1‖ ≤ C_pt * c ^ (-(7 / 6 : ℝ)) := by
    have ht1 : ‖fctS û_1 g_tail1‖ ≤ C_S20 * B_tail * c ^ (-(7 / 6 : ℝ)) :=
      h_bd_tail1.trans (mul_le_mul_of_nonneg_left hc53_76 (by positivity))
    have hsum : ‖fctS û_1 g_base1 - fctS û_1 g_tail1‖ ≤
        (C_S10 * B_base + C_S20 * B_tail) * c ^ (-(7 / 6 : ℝ)) := by
      calc ‖fctS û_1 g_base1 - fctS û_1 g_tail1‖ ≤ ‖fctS û_1 g_base1‖ + ‖fctS û_1 g_tail1‖ := norm_sub_le _ _
        _ ≤ C_S10 * B_base * c ^ (-(7 / 6 : ℝ)) + C_S20 * B_tail * c ^ (-(7 / 6 : ℝ)) := add_le_add h_bd_base1 ht1
        _ = (C_S10 * B_base + C_S20 * B_tail) * c ^ (-(7 / 6 : ℝ)) := by ring
    refine hsum.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    dsimp only [C_pt]
    have : 0 ≤ C_S10 * B_diff_coef * (Sw + 1) := by positivity
    linarith only [this]
  have hL_diff_12 : L - L1 ≤ (Sw + 1) * c ^ (-(1 / 2 : ℝ)) := by
    have h1 : Sw * c ^ (-(2 / 3 : ℝ)) ≤ Sw * c ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)) (by positivity)
    have h2 : -L1 ≤ c ^ (-(1 / 2 : ℝ)) := (neg_le_abs L1).trans hg.hL1_c12
    linarith only [hL_Sw, h1, h2]
  have h_ΔL_bd : ‖fctS û_L g_diff + fctS û_L g_baseL - fctS û_L g_tailL‖ ≤ C_pt * c ^ (-(7 / 6 : ℝ)) := by
    have hc76 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hgd : ‖fctS û_L g_diff‖ ≤ C_S10 * B_diff_coef * (Sw + 1) * c ^ (-(7 / 6 : ℝ)) := by
      calc ‖fctS û_L g_diff‖ ≤ C_S10 * B_diff_coef * c ^ (-(2 / 3 : ℝ)) * (L - L1) := h_bd_gdiff
        _ ≤ C_S10 * B_diff_coef * c ^ (-(2 / 3 : ℝ)) * ((Sw + 1) * c ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hL_diff_12 (by positivity)
        _ = C_S10 * B_diff_coef * (Sw + 1) * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by ring
        _ = C_S10 * B_diff_coef * (Sw + 1) * c ^ (-(7 / 6 : ℝ)) := by rw [hc76]
    have htL : ‖fctS û_L g_tailL‖ ≤ C_S20 * B_tail * c ^ (-(7 / 6 : ℝ)) :=
      h_bd_tailL.trans (mul_le_mul_of_nonneg_left hc53_76 (by positivity))
    calc ‖fctS û_L g_diff + fctS û_L g_baseL - fctS û_L g_tailL‖
        ≤ ‖fctS û_L g_diff‖ + ‖fctS û_L g_baseL‖ + ‖fctS û_L g_tailL‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C_S10 * B_diff_coef * (Sw + 1) * c ^ (-(7 / 6 : ℝ)) +
            C_S10 * B_base * c ^ (-(7 / 6 : ℝ)) + C_S20 * B_tail * c ^ (-(7 / 6 : ℝ)) :=
          add_le_add (add_le_add hgd h_bd_baseL) htL
      _ = C_pt * c ^ (-(7 / 6 : ℝ)) := by dsimp [C_pt]; ring
  have hû_diff : |û_L - û_1| ≤ K_slope * c ^ (2 / 3 : ℝ) * (L - L1) := by
    rw [abs_sub_comm, abs_of_nonneg (by
      linarith only [hg.hv_diff_lo,
        show (0 : ℝ) ≤ (100 / 95 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (L - L1) by positivity])]
    exact hg.hv_diff_hi.trans_eq (by dsimp [K_slope])
  have hdiff_base_û : ‖fctS û_L g_baseL - fctS û_1 g_baseL‖ ≤
      C_lip10 * B_base * K_slope * c ^ (-(1 / 2 : ℝ)) * (L - L1) := by
    have hc12 : c ^ (-(7 / 6 : ℝ)) * c ^ (2 / 3 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc ‖fctS û_L g_baseL - fctS û_1 g_baseL‖
        ≤ C_lip10 * (B_base * c ^ (-(7 / 6 : ℝ))) * |û_L - û_1| :=
          hLip10 hû_1 hû_L (by positivity) h_g_base_L
      _ ≤ C_lip10 * (B_base * c ^ (-(7 / 6 : ℝ))) * (K_slope * c ^ (2 / 3 : ℝ) * (L - L1)) :=
          mul_le_mul_of_nonneg_left hû_diff (by positivity)
      _ = C_lip10 * B_base * K_slope * c ^ (-(1 / 2 : ℝ)) * (L - L1) := by
          rw [show C_lip10 * (B_base * c ^ (-(7 / 6 : ℝ))) * (K_slope * c ^ (2 / 3 : ℝ) * (L - L1)) =
            C_lip10 * B_base * K_slope * (c ^ (-(7 / 6 : ℝ)) * c ^ (2 / 3 : ℝ)) * (L - L1) by ring, hc12]
  have hdiff_tail_û : ‖fctS û_L g_tailL - fctS û_1 g_tailL‖ ≤
      C_lip20 * B_tail * K_slope * c ^ (-1 : ℝ) * (L - L1) := by
    have hcm1 : c ^ (-(5 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = c ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc ‖fctS û_L g_tailL - fctS û_1 g_tailL‖
        ≤ C_lip20 * (B_tail * c ^ (-(5 / 3 : ℝ))) * |û_L - û_1| :=
          hLip20 hû_1 hû_L (by positivity) h_g_tail_L
      _ ≤ C_lip20 * (B_tail * c ^ (-(5 / 3 : ℝ))) * (K_slope * c ^ (2 / 3 : ℝ) * (L - L1)) :=
          mul_le_mul_of_nonneg_left hû_diff (by positivity)
      _ = C_lip20 * B_tail * K_slope * c ^ (-1 : ℝ) * (L - L1) := by
          rw [show C_lip20 * (B_tail * c ^ (-(5 / 3 : ℝ))) * (K_slope * c ^ (2 / 3 : ℝ) * (L - L1)) =
            C_lip20 * B_tail * K_slope * (c ^ (-(5 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * (L - L1) by ring, hcm1]
  have hdiff_base_χ : ‖fctS û_1 g_baseL - fctS û_1 g_base1‖ ≤ C_S11 * B_chi_base * c ^ (-(5 / 4 : ℝ)) * (L - L1) := by
    have hsub_fn : (fun u => g_baseL u - g_base1 u) =
        extUc c (fun u => ((fctInnerChi outerChiIn c V_L u - fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ) *
          (winMuMix K4 ε c L1 L1 α u - 1)) := by
      ext u; dsimp only [g_baseL, g_base1, extUc]; split_ifs <;> push_cast <;> ring
    have hs := win_fctS_sub hMpos hû_1 (by norm_num) (by norm_num) (by positivity) (by positivity) h_g_base_L h_g_base_1
    rw [← hs, hsub_fn]
    exact (hA11 û_1 _ _ hû_1 (by positivity) h_chi_diff_base).2.1.trans_eq (by ring)
  have hdiff_tail_χ : ‖fctS û_1 g_tailL - fctS û_1 g_tail1‖ ≤ C_S1 * C_χd * c ^ (-(1 / 2 : ℝ)) * (L - L1) := by
    let g_χd : ℝ → ℂ := extUc c (fun u => ((fctInnerChi outerChiIn c V_L u - fctInnerChi outerChiIn c V_1 u : ℝ) : ℂ))
    have hsub_fn : (fun u => g_tailL u - g_tail1 u) = fun u => (0 : ℂ) - g_χd u := by
      ext u; dsimp only [g_tailL, g_tail1, chiExt, g_χd, extUc]; split_ifs <;> push_cast <;> ring
    have hs := win_fctS_sub hMpos hû_1 (by norm_num) (by norm_num) (by positivity) (by positivity) h_g_tail_L h_g_tail_1
    have h0_sym : FctSymCls 8 1 0 (fun _ : ℝ => (0 : ℂ)) := by
      refine ⟨contDiffOn_const, fun r hr u hu => ?_⟩
      change ‖iteratedDerivWithin r (fun _ : ℝ => (0 : ℂ)) (Ici 0) u‖ ≤ _
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp
      · have hz_eq : (fun _ : ℝ => (0 : ℂ)) = fun _ => (0 : ℂ) * (fun _ : ℝ => (1 : ℂ)) 0 := by ext; simp
        rw [hz_eq, iteratedDerivWithin_const_mul hu (uniqueDiffOn_Ici 0) (0 : ℂ) contDiffWithinAt_const,
          zero_mul, norm_zero, zero_mul]
    have hs_0 := win_fctS_sub hMpos hû_1 (by norm_num) (by norm_num) le_rfl (by positivity) h0_sym h_chi_diff_tail
    have hS0 : fctS û_1 (fun _ : ℝ => (0 : ℂ)) = 0 := by
      refine FctSLimit.fctS_eq ?_
      unfold FctSLimit fctSEps
      simp
    rw [← hs, hsub_fn, hs_0, hS0, zero_sub, norm_neg]
    have hzero_ust : ∀ u ∈ Icc 0 (fctUstar c), g_χd u = 0 := fun u hu => by
      have huc : fctUstar c ≤ fctUc c := by
        unfold fctUstar fctUc
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      dsimp only [g_χd]; simp only [extUc, hu.2.trans huc, ↓reduceIte]; exact hχd.2.1 u hu
    have hust_ge : max 6 (Real.sqrt (8 * M_u)) ≤ fctUstar c := by
      have h1 : cU_lim ^ (1 / 12 : ℝ) ≤ c ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hcu_lim (by norm_num)
      have h2 : cU_lim ^ (1 / 12 : ℝ) = max 6 (Real.sqrt (8 * M_u)) / 2.7 := by
        dsimp [cU_lim]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [h2] at h1
      calc max 6 (Real.sqrt (8 * M_u)) = 2.7 * (max 6 (Real.sqrt (8 * M_u)) / 2.7) := by ring
        _ ≤ 2.7 * c ^ (1 / 12 : ℝ) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = fctUstar c := rfl
    have htail := (hA1 û_1 _ g_χd hû_1 (by positivity) h_chi_diff_tail).2.2 (fctUstar c) hust_ge hzero_ust
    have hc112_pos : 0 < c ^ (1 / 12 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have hpow_neg : (fctUstar c) ^ (1 + 1 / 2 - 3 * ((8 : ℕ) : ℝ)) ≤ c ^ (-(5 / 12 : ℝ)) := by
      have hust_ge_c112 : c ^ (1 / 12 : ℝ) ≤ fctUstar c := by unfold fctUstar; linarith only [hc112_pos]
      have h_le1 : (fctUstar c) ^ (1 + 1 / 2 - 3 * ((8 : ℕ) : ℝ)) ≤ (c ^ (1 / 12 : ℝ)) ^ (-(45 / 2 : ℝ)) := by
        rw [show (1 + 1 / 2 - 3 * ((8 : ℕ) : ℝ) : ℝ) = -(45 / 2 : ℝ) by norm_num]
        exact Real.rpow_le_rpow_of_nonpos hc112_pos hust_ge_c112 (by norm_num)
      have h_eq : (c ^ (1 / 12 : ℝ)) ^ (-(45 / 2 : ℝ)) = c ^ (-(15 / 8 : ℝ)) := by
        rw [← Real.rpow_mul hc0.le]; congr 1; norm_num
      have h_le2 : c ^ (-(15 / 8 : ℝ)) ≤ c ^ (-(5 / 12 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      linarith only [h_le1, h_eq, h_le2]
    have hc12_eq : c ^ (-(1 / 12 : ℝ)) * c ^ (-(5 / 12 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc ‖fctS û_1 g_χd‖
        ≤ C_S1 * (C_χd * c ^ (-(1 / 12 : ℝ)) * (L - L1)) *
            (fctUstar c) ^ (1 + 1 / 2 - 3 * ((8 : ℕ) : ℝ)) := htail
      _ ≤ C_S1 * (C_χd * c ^ (-(1 / 12 : ℝ)) * (L - L1)) * c ^ (-(5 / 12 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow_neg (by positivity)
      _ = C_S1 * C_χd * (c ^ (-(1 / 12 : ℝ)) * c ^ (-(5 / 12 : ℝ))) * (L - L1) := by ring
      _ = C_S1 * C_χd * c ^ (-(1 / 2 : ℝ)) * (L - L1) := by rw [hc12_eq]
  have hc23_12 : c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc54_12 : c ^ (-(5 / 4 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hcm1_12 : c ^ (-1 : ℝ) ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have h_diff_bd : ‖(fctS û_L g_diff + fctS û_L g_baseL - fctS û_L g_tailL) -
      (fctS û_1 g_base1 - fctS û_1 g_tail1)‖ ≤ C_lip * c ^ (-(1 / 2 : ℝ)) * (L - L1) := by
    have heq : (fctS û_L g_diff + fctS û_L g_baseL - fctS û_L g_tailL) -
          (fctS û_1 g_base1 - fctS û_1 g_tail1) =
        fctS û_L g_diff + ((fctS û_L g_baseL - fctS û_1 g_baseL) + (fctS û_1 g_baseL - fctS û_1 g_base1)) -
          ((fctS û_L g_tailL - fctS û_1 g_tailL) + (fctS û_1 g_tailL - fctS û_1 g_tail1)) := by ring
    have hb1 : ‖fctS û_L g_diff‖ ≤ C_S10 * B_diff_coef * c ^ (-(1 / 2 : ℝ)) * (L - L1) :=
      h_bd_gdiff.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc23_12 (by positivity)) hL10)
    have hb2 : ‖fctS û_1 g_baseL - fctS û_1 g_base1‖ ≤ C_S11 * B_chi_base * c ^ (-(1 / 2 : ℝ)) * (L - L1) :=
      hdiff_base_χ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc54_12 (by positivity)) hL10)
    have hb3 : ‖fctS û_L g_tailL - fctS û_1 g_tailL‖ ≤ C_lip20 * B_tail * K_slope * c ^ (-(1 / 2 : ℝ)) * (L - L1) :=
      hdiff_tail_û.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcm1_12 (by positivity)) hL10)
    rw [heq]
    calc ‖fctS û_L g_diff + ((fctS û_L g_baseL - fctS û_1 g_baseL) + (fctS û_1 g_baseL - fctS û_1 g_base1)) -
            ((fctS û_L g_tailL - fctS û_1 g_tailL) + (fctS û_1 g_tailL - fctS û_1 g_tail1))‖
        ≤ ‖fctS û_L g_diff‖ + (‖fctS û_L g_baseL - fctS û_1 g_baseL‖ + ‖fctS û_1 g_baseL - fctS û_1 g_base1‖) +
            (‖fctS û_L g_tailL - fctS û_1 g_tailL‖ + ‖fctS û_1 g_tailL - fctS û_1 g_tail1‖) :=
          (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _)))
            (norm_add_le _ _))
      _ ≤ _ := add_le_add (add_le_add hb1 (add_le_add hdiff_base_û hb2)) (add_le_add hb3 hdiff_tail_χ)
      _ = C_lip * c ^ (-(1 / 2 : ℝ)) * (L - L1) := by dsimp [C_lip]; ring
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only [V_L, V_1, û_L, û_1, S] at hSL hS1 ⊢
  · rw [hSL]; exact h_ΔL_bd
  · rw [hS1]; exact h_Δ1_bd
  · rw [hSL, hS1]; exact h_diff_bd

/-- Uniform `c^{-1}` pointwise bound and `c^{-1/3} (L - L1)` Lipschitz bound for
`winRSqIn` on the Airy window `[fctWarpL1 h ε c, Sw * c^{-2/3}]` (`fct:warp-win`). -/
theorem win_RSqIn_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) {Sw : ℝ} (hSw : 1 ≤ Sw) :
    ∃ (C_R c₀ : ℝ), 0 ≤ C_R ∧ 15000 ≤ c₀ ∧ ∀ {ε c L : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c → fctWarpL1 h ε c ≤ L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      let L1 := fctWarpL1 h ε c
      let α := fctWarpAlpha h ε c
      |winRSqIn K4 ε c L1 α L| ≤ C_R * c ^ (-1 : ℝ) ∧
      |winRSqIn K4 ε c L1 α L - winRSqIn K4 ε c L1 α L1| ≤ C_R * c ^ (-(1 / 3 : ℝ)) * (L - L1) := by
  obtain ⟨C_pt, C_lip, _, c_dS, hCpt0, hClip0, _, _, hdS⟩ := win_deltaS_sym_bounds hK4 h hSw
  obtain ⟨C_P, C_Pd, c_P0, hCP0, hCPd0, _, hP0_bds⟩ := win_P0_bounds hK4 h hSw
  let P_norm : ℝ := C_P / (2 * π ^ (3 / 2 : ℝ))
  let Pd_norm : ℝ := C_Pd / (2 * π ^ (3 / 2 : ℝ))
  let C_R : ℝ := max (P_norm * C_pt) (P_norm * C_lip + Pd_norm * C_pt)
  refine ⟨C_R, max 15000 (max c_dS c_P0), by positivity, le_max_left _ _,
    fun {ε c L} hε hc hL1_L hL_Sw => ?_⟩
  have hcdS : c_dS ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcP0 : c_P0 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc15 : 15000 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith only [hc15]
  have hc1 : 1 ≤ c := by linarith only [hc15]
  have hL10 : 0 ≤ L - fctWarpL1 h ε c := sub_nonneg.mpr hL1_L
  obtain ⟨hdSL, hdS1, hdSdiff⟩ := hdS hε hcdS hL1_L hL_Sw
  have hP0_L := hP0_bds hε hcP0 hL1_L hL_Sw
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  let P1 : ℝ → ℝ := fun x => (c ^ (1 / 3 : ℝ) / π) / warpN0 c * warpNu K4 ε c x α
  have hpi32_pos : 0 < 2 * π ^ (3 / 2 : ℝ) := by positivity
  have hP1_eq : ∀ x : ℝ, winP0 K4 ε c x α = P1 x * (2 * π ^ (3 / 2 : ℝ)) := fun _ => rfl
  have hP1_nn : 0 ≤ P1 L := by
    have hlo : 0 ≤ winP0 K4 ε c L α := le_trans (by have := Real.pi_pos; have := ceCs_pos; positivity) hP0_L.1
    rw [hP1_eq] at hlo
    exact nonneg_of_mul_nonneg_left hlo hpi32_pos
  have hP1_bd : |P1 L| ≤ P_norm * c ^ (1 / 6 : ℝ) := by
    rw [abs_of_nonneg hP1_nn]
    have hle := hP0_L.2.1
    rw [hP1_eq] at hle
    calc P1 L = (P1 L * (2 * π ^ (3 / 2 : ℝ))) / (2 * π ^ (3 / 2 : ℝ)) := by field_simp
      _ ≤ (C_P * c ^ (1 / 6 : ℝ)) / (2 * π ^ (3 / 2 : ℝ)) := div_le_div_of_nonneg_right hle hpi32_pos.le
      _ = P_norm * c ^ (1 / 6 : ℝ) := by dsimp [P_norm]; ring
  have hP1_diff : |P1 L - P1 L1| ≤ Pd_norm * c ^ (1 / 6 : ℝ) * (L - L1) := by
    have hle := hP0_L.2.2.1
    rw [hP1_eq, hP1_eq, ← sub_mul, abs_mul, abs_of_pos hpi32_pos] at hle
    calc |P1 L - P1 L1| = (|P1 L - P1 L1| * (2 * π ^ (3 / 2 : ℝ))) / (2 * π ^ (3 / 2 : ℝ)) := by field_simp
      _ ≤ (C_Pd * c ^ (1 / 6 : ℝ) * (L - L1)) / (2 * π ^ (3 / 2 : ℝ)) :=
            div_le_div_of_nonneg_right hle hpi32_pos.le
      _ = Pd_norm * c ^ (1 / 6 : ℝ) * (L - L1) := by dsimp [Pd_norm]; ring
  have hwin_eq : ∀ x : ℝ, winRSqIn K4 ε c L1 α x = P1 x *
      (fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (x, α))
        (extUc c (fun u => ((fctInnerChi outerChiIn c (concreteInnerV K4 ε c x α) u : ℝ) : ℂ) *
          winMuMix K4 ε c L1 x α u)) -
       fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (x, α))
        (fun _ => (1 : ℂ))).re := fun _ => rfl
  have hc_m1 : c ^ (1 / 6 : ℝ) * c ^ (-(7 / 6 : ℝ)) = c ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hc16_12 : c ^ (1 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hcm1_13 : c ^ (-1 : ℝ) ≤ c ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hwin_eq L, abs_mul]
    calc |P1 L| * |_|
        ≤ (P_norm * c ^ (1 / 6 : ℝ)) * (C_pt * c ^ (-(7 / 6 : ℝ))) :=
          mul_le_mul hP1_bd ((Complex.abs_re_le_norm _).trans hdSL) (abs_nonneg _) (by positivity)
      _ = P_norm * C_pt * (c ^ (1 / 6 : ℝ) * c ^ (-(7 / 6 : ℝ))) := by ring
      _ = P_norm * C_pt * c ^ (-1 : ℝ) := by rw [hc_m1]
      _ ≤ C_R * c ^ (-1 : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · rw [hwin_eq L, hwin_eq L1]
    set S := concreteBoxS K4 ε c
    set dL := fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α))
      (extUc c (fun u => ((fctInnerChi outerChiIn c (concreteInnerV K4 ε c L α) u : ℝ) : ℂ) *
        winMuMix K4 ε c L1 L α u)) -
      fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L, α)) (fun _ => (1 : ℂ))
    set d1 := fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α))
      (extUc c (fun u => ((fctInnerChi outerChiIn c (concreteInnerV K4 ε c L1 α) u : ℝ) : ℂ) *
        winMuMix K4 ε c L1 L1 α u)) -
      fctS (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)) (fun _ => (1 : ℂ))
    have hsplit : P1 L * dL.re - P1 L1 * d1.re = P1 L * (dL - d1).re + (P1 L - P1 L1) * d1.re := by
      simp only [Complex.sub_re]; ring
    rw [hsplit]
    calc |P1 L * (dL - d1).re + (P1 L - P1 L1) * d1.re|
        ≤ |P1 L| * |(dL - d1).re| + |P1 L - P1 L1| * |d1.re| := by
          simpa only [abs_mul] using abs_add_le (P1 L * (dL - d1).re) ((P1 L - P1 L1) * d1.re)
      _ ≤ (P_norm * c ^ (1 / 6 : ℝ)) * (C_lip * c ^ (-(1 / 2 : ℝ)) * (L - L1)) +
            (Pd_norm * c ^ (1 / 6 : ℝ) * (L - L1)) * (C_pt * c ^ (-(7 / 6 : ℝ))) :=
          add_le_add (mul_le_mul hP1_bd ((Complex.abs_re_le_norm _).trans hdSdiff) (abs_nonneg _) (by positivity))
            (mul_le_mul hP1_diff ((Complex.abs_re_le_norm _).trans hdS1) (abs_nonneg _) (by positivity))
      _ = P_norm * C_lip * c ^ (-(1 / 3 : ℝ)) * (L - L1) + Pd_norm * C_pt * c ^ (-1 : ℝ) * (L - L1) := by
          have h1 : P_norm * c ^ (1 / 6 : ℝ) * (C_lip * c ^ (-(1 / 2 : ℝ)) * (L - L1)) =
              P_norm * C_lip * (c ^ (1 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ))) * (L - L1) := by ring
          have h2 : Pd_norm * c ^ (1 / 6 : ℝ) * (L - L1) * (C_pt * c ^ (-(7 / 6 : ℝ))) =
              Pd_norm * C_pt * (c ^ (1 / 6 : ℝ) * c ^ (-(7 / 6 : ℝ))) * (L - L1) := by ring
          rw [h1, h2, hc16_12, hc_m1]
      _ ≤ P_norm * C_lip * c ^ (-(1 / 3 : ℝ)) * (L - L1) +
            Pd_norm * C_pt * c ^ (-(1 / 3 : ℝ)) * (L - L1) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcm1_13 (by positivity)) hL10)
      _ = (P_norm * C_lip + Pd_norm * C_pt) * c ^ (-(1 / 3 : ℝ)) * (L - L1) := by ring
      _ ≤ C_R * c ^ (-(1 / 3 : ℝ)) * (L - L1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hL10

/-- info: 'FormalResearch.SignUncertainty.win_RSqIn_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_RSqIn_bounds

end FormalResearch.SignUncertainty
