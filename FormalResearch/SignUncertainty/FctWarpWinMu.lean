/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinMix

/-!
# Window symbol and `L`-difference bounds for `J`, `winMuMix`, `χ`, and `1 - χ` (`fct:warp-win`)

Leaf module combining `FctWarpWinJ0`, `FctWarpWinJ1`, and `FctWarpWinMix` to prove:
* `win_J_diff_and_bounds`: `J(L_hi) - J(L_lo) ∈ 𝒮^8_{10} (C c^{-2/3} (L_hi - L_lo))` and `J(L) ∈ 𝒮^8_0 C`;
* `win_muMix_diff_and_bounds`: `winMuMix(L_hi) - winMuMix(L_lo) ∈ 𝒮^8_{10} (C c^{-2/3} (L_hi - L_lo))`
  and `winMuMix(L) ∈ 𝒮^8_0 C`;
* `win_chi_diff_sym`: `χ_2 - χ_1 ∈ 𝒮^8_1 (C c^{-1/12} (L_hi - L_lo))` vanishing on `[0, fctUstar c]` and
  `[2.95 c^{1/12}, fctUc c]`;
* `win_one_sub_chi_sym20`: `1 - chiExt c V ∈ 𝒮^8_{20} ((|C_χ| + 1) c^{-5/3})`, vanishing on `[0, fctUstar c]`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Finset
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

/-! ### 1. `J(L)` window difference and `𝒮^8_0` bound -/

theorem win_J_diff_and_bounds {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (hSw : 1 ≤ Sw_ell) :
    ∃ (C_J C_d c₀ : ℝ), 0 ≤ C_J ∧ 0 ≤ C_d ∧ 10000 ≤ c₀ ∧ ∀ {ε c α L_lo L_hi : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      0 ≤ concreteEll1 ε c L_lo → L_lo ≤ L_hi →
      concreteEll1 ε c L_hi ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      let S := concreteBoxS K4 ε c
      let τ₁ := c ^ (-(1 / 4 : ℝ))
      let J := fun (L u : ℝ) => ((Jfun S.V fctH (τ₁ ^ 2) ((concreteEll1 ε c L, 1, α), fctInnerY c u) : ℝ) : ℂ)
      FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_d * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo))
        (fun u => J L_hi u - J L_lo u) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_J (J L_lo) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_J (J L_hi) := by
  obtain ⟨C0, c0, hC00, _, hJ0⟩ := win_J0_sub_one_and_diff hK4 hSw
  obtain ⟨C1, c1, hC10, _, hJ1⟩ := win_J1_sub_J0_and_diff hK4 hSw
  let C_J : ℝ := 1 + 4 ^ 10 * C0 + 4 ^ 8 * C1
  let C_d : ℝ := C0 + C1
  refine ⟨C_J, C_d, max 10000 (max c0 c1), by positivity, by positivity, le_max_left _ _,
    fun {ε c α L_lo L_hi} hε hc hτ_lim hK4t hα hell1 h12 hell2 => ?_⟩
  have hc0_le : c0 ≤ c := (le_max_left _ _).trans ((le_max_right 10000 _).trans hc)
  have hc1_le : c1 ≤ c := (le_max_right _ _).trans ((le_max_right 10000 _).trans hc)
  have hc10000 : (10000 : ℝ) ≤ c := (le_max_left _ _).trans hc
  have hc1 : 1 ≤ c := by linarith only [hc10000]
  have hc0 : 0 < c := by linarith only [hc10000]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  set ell1 := concreteEll1 ε c L_lo
  set ell2 := concreteEll1 ε c L_hi
  have hell_le : ell1 ≤ ell2 := by
    dsimp only [ell1, ell2, concreteEll1]
    exact div_le_div_of_nonneg_right (sub_le_sub_right h12 _) (sq_nonneg _)
  have hell2_nn : 0 ≤ ell2 := hell1.trans hell_le
  have hdiff_ell : ell2 - ell1 = c ^ (1 / 2 : ℝ) * (L_hi - L_lo) := by
    dsimp only [ell1, ell2, concreteEll1]
    have hτ2 : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [← sub_div, hτ2, div_eq_mul_inv, Real.rpow_neg hc0.le, inv_inv]
    ring
  obtain ⟨_, hdJ0⟩ := hJ0 hε hc0_le hτ_lim hK4t hα hell1 hell_le hell2
  obtain ⟨_, hdJ1⟩ := hJ1 hε hc1_le hτ_lim hK4t hα hell1 hell_le hell2
  have hc34_23 : c ^ (-(3 / 4 : ℝ)) ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc76_12 : c ^ (-(7 / 6 : ℝ)) * c ^ (1 / 2 : ℝ) = c ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hc54_12 : c ^ (-(5 / 4 : ℝ)) * c ^ (1 / 2 : ℝ) = c ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hL0 : 0 ≤ L_hi - L_lo := sub_nonneg.mpr h12
  have hdJ0' : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C0 * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo)) _ :=
    hdJ0.mono_B Icc_subset_Ici_self (le_of_eq (by
      rw [hdiff_ell]; calc C0 * c ^ (-(7 / 6 : ℝ)) * (c ^ (1 / 2 : ℝ) * (L_hi - L_lo))
          = C0 * (c ^ (-(7 / 6 : ℝ)) * c ^ (1 / 2 : ℝ)) * (L_hi - L_lo) := by ring
        _ = C0 * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo) := by rw [hc76_12]))
  have hdJ1' : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C1 * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo)) _ :=
    (hdJ1.mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (8 : ℝ) ≤ 10)).mono_B Icc_subset_Ici_self (by
      rw [hdiff_ell]
      calc C1 * c ^ (-(5 / 4 : ℝ)) * (c ^ (1 / 2 : ℝ) * (L_hi - L_lo))
          = C1 * (c ^ (-(5 / 4 : ℝ)) * c ^ (1 / 2 : ℝ)) * (L_hi - L_lo) := by ring
        _ = C1 * c ^ (-(3 / 4 : ℝ)) * (L_hi - L_lo) := by rw [hc54_12]
        _ ≤ C1 * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo) := by gcongr)
  have hJ_diff : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_d * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((Jfun (concreteBoxS K4 ε c).V fctH ((c ^ (-(1 / 4 : ℝ))) ^ 2)
          ((concreteEll1 ε c L_hi, 1, α), fctInnerY c u) : ℝ) : ℂ) -
        ((Jfun (concreteBoxS K4 ε c).V fctH ((c ^ (-(1 / 4 : ℝ))) ^ 2)
          ((concreteEll1 ε c L_lo, 1, α), fctInnerY c u) : ℝ) : ℂ)) :=
    ((hdJ0'.add hDu hdJ1').mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_d]; ring))).congr hDu
      fun u _ => by push_cast; ring
  have hJ_pt : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_J
        (fun u => ((Jfun (concreteBoxS K4 ε c).V fctH ((c ^ (-(1 / 4 : ℝ))) ^ 2)
          ((ell, 1, α), fctInnerY c u) : ℝ) : ℂ)) := fun {ell} hell_0 hell_hi => by
    obtain ⟨h0_sub, _⟩ := hJ0 hε hc0_le hτ_lim hK4t hα hell_0 le_rfl hell_hi
    obtain ⟨h1_sub, _⟩ := hJ1 hε hc1_le hτ_lim hK4t hα hell_0 le_rfl hell_hi
    have h0_sh := h0_sub.shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 10)
    have h1_sh := h1_sub.shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 8)
    have hUc10 := one_add_Uc_rpow_le hc1 10 (by norm_num)
    have hUc8 := one_add_Uc_rpow_le hc1 8 (by norm_num)
    have h410 : (4 : ℝ) ^ (10 : ℝ) = 4 ^ 10 := by norm_num
    have h48 : (4 : ℝ) ^ (8 : ℝ) = 4 ^ 8 := by norm_num
    rw [h410] at hUc10; rw [h48] at hUc8
    have hc10 : c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12) ≤ 1 := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hc8 : c ^ (-(17 / 12 : ℝ)) * c ^ ((8 : ℝ) / 12) ≤ 1 := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have h0_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (4 ^ 10 * C0) _ :=
      h0_sh.mono_B Icc_subset_Ici_self (by
        calc C0 * c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (10 - 0 : ℝ)
            ≤ C0 * c ^ (-(4 / 3 : ℝ)) * (4 ^ 10 * c ^ ((10 : ℝ) / 12)) := by
              rw [show (10 : ℝ) - 0 = 10 by norm_num]; gcongr
          _ = 4 ^ 10 * C0 * (c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12)) := by ring
          _ ≤ 4 ^ 10 * C0 * 1 := by gcongr
          _ = 4 ^ 10 * C0 := mul_one _)
    have h1_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (4 ^ 8 * C1) _ :=
      h1_sh.mono_B Icc_subset_Ici_self (by
        calc C1 * c ^ (-(17 / 12 : ℝ)) * (1 + fctUc c) ^ (8 - 0 : ℝ)
            ≤ C1 * c ^ (-(17 / 12 : ℝ)) * (4 ^ 8 * c ^ ((8 : ℝ) / 12)) := by
              rw [show (8 : ℝ) - 0 = 8 by norm_num]; gcongr
          _ = 4 ^ 8 * C1 * (c ^ (-(17 / 12 : ℝ)) * c ^ ((8 : ℝ) / 12)) := by ring
          _ ≤ 4 ^ 8 * C1 * 1 := by gcongr
          _ = 4 ^ 8 * C1 := mul_one _)
    have hone := (one_symCls 8).mono_set Icc_subset_Ici_self hDu (uniqueDiffOn_Ici 0)
    exact (((hone.add hDu h0_0).add hDu h1_0).mono_B Icc_subset_Ici_self le_rfl).congr hDu
      fun u _ => by push_cast; ring
  exact ⟨hJ_diff, hJ_pt hell1 (hell_le.trans hell2), hJ_pt hell2_nn hell2⟩

/-! ### 2. `winMuMix` window difference and `𝒮^8_0` bound -/

theorem win_muMix_diff_and_bounds {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (hSw : 1 ≤ Sw_ell) :
    ∃ (C_μ C_d c₀ : ℝ), 0 ≤ C_μ ∧ 0 ≤ C_d ∧ 10000 ≤ c₀ ∧ ∀ {ε c α L1 L_lo L_hi : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) → |L1| ≤ 1 →
      0 ≤ concreteEll1 ε c L_lo → L_lo ≤ L_hi →
      concreteEll1 ε c L_hi ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_d * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo))
        (fun u => winMuMix K4 ε c L1 L_hi α u - winMuMix K4 ε c L1 L_lo α u) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_μ (winMuMix K4 ε c L1 L_lo α) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_μ (winMuMix K4 ε c L1 L_hi α) := by
  obtain ⟨C_J, C_Jd, c_J, hCJ0, hCJd0, _, hJ⟩ := win_J_diff_and_bounds hK4 hSw
  obtain ⟨C_E, C_Ed, c_E, hCE0, hCEd0, _, hE⟩ := win_E_diff_and_bounds hK4 hSw
  obtain ⟨C_K, C_Kd, c_K, hCK0, hCKd0, _, hK⟩ := win_K_diff_and_bounds hK4 hSw
  let C_μ : ℝ := 2 ^ 8 * (2 ^ 8 * C_J * C_E) * C_K
  let C_d : ℝ := 2 ^ 8 * (2 ^ 8 * (C_Jd * C_E) * C_K + 2 ^ 8 * (C_J * C_Ed) * C_K) +
    2 ^ 8 * (2 ^ 8 * C_J * C_E) * C_Kd
  refine ⟨C_μ, C_d, max 10000 (max c_J (max c_E c_K)), by positivity, by positivity, le_max_left _ _,
    fun {ε c α L1 L_lo L_hi} hε hc hτ_lim hK4t hα hL1 hell1 h12 hell2 => ?_⟩
  have hcJ : c_J ≤ c := (le_max_left _ _).trans ((le_max_right 10000 _).trans hc)
  have hcE : c_E ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right 10000 _).trans hc)
  have hcK : c_K ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right 10000 _).trans hc)
  have hc10000 : (10000 : ℝ) ≤ c := (le_max_left _ _).trans hc
  have hc1 : 1 ≤ c := by linarith only [hc10000]
  have hUc0 : 0 < fctUc c := fctUc_pos (by positivity)
  have hDu := uniqueDiffOn_Icc hUc0
  obtain ⟨hdJ, hJ1, hJ2⟩ := hJ hε hcJ hτ_lim hK4t hα hell1 h12 hell2
  obtain ⟨hdE, hE1, hE2⟩ := hE hε hcE hτ_lim hK4t hα hell1 h12 hell2
  obtain ⟨hdK, hK1, hK2⟩ := hK hε hcK hτ_lim hK4t hα hL1 hell1 h12 hell2
  have hL0 : 0 ≤ L_hi - L_lo := sub_nonneg.mpr h12
  have hc56 : c ^ (-(5 / 6 : ℝ)) ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc43 : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hJE_d :=
    ((hdJ.mul Icc_subset_Ici_self hDu hE1).mono_p Icc_subset_Ici_self
      (by positivity) (by norm_num : (10 : ℝ) + 0 ≤ 10)).add hDu
    (((hJ2.mul Icc_subset_Ici_self hDu hdE).mono_p Icc_subset_Ici_self
      (by positivity) (by norm_num : (0 : ℝ) + 4 ≤ 10)).mono_B Icc_subset_Ici_self (by
      calc 2 ^ 8 * C_J * (C_Ed * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo))
          = 2 ^ 8 * (C_J * C_Ed) * c ^ (-(5 / 6 : ℝ)) * (L_hi - L_lo) := by ring
        _ ≤ 2 ^ 8 * (C_J * C_Ed) * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo) := by gcongr))
  have hpart1 := (hJE_d.mul Icc_subset_Ici_self hDu hK2).mono_p Icc_subset_Ici_self
    (by positivity) (by norm_num : (10 : ℝ) + 0 ≤ 10)
  have hJE1 := (hJ1.mul Icc_subset_Ici_self hDu hE1).mono_p Icc_subset_Ici_self
    (by positivity) (by norm_num : (0 : ℝ) + 0 ≤ 0)
  have hpart2 := ((hJE1.mul Icc_subset_Ici_self hDu hdK).mono_p Icc_subset_Ici_self
    (by positivity) (by norm_num : (0 : ℝ) + 7 ≤ 10)).mono_B Icc_subset_Ici_self (by
    calc 2 ^ 8 * (2 ^ 8 * C_J * C_E) * (C_Kd * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo))
        = 2 ^ 8 * (2 ^ 8 * C_J * C_E) * C_Kd * c ^ (-(4 / 3 : ℝ)) * (L_hi - L_lo) := by ring
      _ ≤ 2 ^ 8 * (2 ^ 8 * C_J * C_E) * C_Kd * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo) := by gcongr)
  have hdiff : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_d * c ^ (-(2 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => winMuMix K4 ε c L1 L_hi α u - winMuMix K4 ε c L1 L_lo α u) :=
    ((hpart1.add hDu hpart2).mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_d]; ring))).congr hDu
      fun u _ => by dsimp only [winMuMix]; ring
  have hpt1 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_μ (winMuMix K4 ε c L1 L_lo α) :=
    ((hJE1.mul Icc_subset_Ici_self hDu hK1).mono_p Icc_subset_Ici_self
      (by positivity) (by norm_num : (0 : ℝ) + 0 ≤ 0)).mono_B Icc_subset_Ici_self le_rfl
  have hJE2 := (hJ2.mul Icc_subset_Ici_self hDu hE2).mono_p Icc_subset_Ici_self
    (by positivity) (by norm_num : (0 : ℝ) + 0 ≤ 0)
  have hpt2 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_μ (winMuMix K4 ε c L1 L_hi α) :=
    ((hJE2.mul Icc_subset_Ici_self hDu hK2).mono_p Icc_subset_Ici_self
      (by positivity) (by norm_num : (0 : ℝ) + 0 ≤ 0)).mono_B Icc_subset_Ici_self le_rfl
  exact ⟨hdiff, hpt1, hpt2⟩

/-! ### 3. Cutoff difference `χ₂ - χ₁` and tail `1 - chiExt` (`p = 20`) -/

theorem win_chi_diff_sym {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (hSw : 1 ≤ Sw_ell) :
    ∃ (C_χd c₀ : ℝ), 0 ≤ C_χd ∧ 15000 ≤ c₀ ∧ ∀ {ε c α L_lo L_hi : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      0 ≤ concreteEll1 ε c L_lo → L_lo ≤ L_hi →
      concreteEll1 ε c L_hi ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      let V1 := concreteInnerV K4 ε c L_lo α
      let V2 := concreteInnerV K4 ε c L_hi α
      FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_χd * c ^ (-(1 / 12 : ℝ)) * (L_hi - L_lo))
        (fun u => ((fctInnerChi outerChiIn c V2 u - fctInnerChi outerChiIn c V1 u : ℝ) : ℂ)) ∧
      (∀ u ∈ Icc 0 (fctUstar c), ((fctInnerChi outerChiIn c V2 u - fctInnerChi outerChiIn c V1 u : ℝ) : ℂ) = 0) ∧
      (∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c),
        ((fctInnerChi outerChiIn c V2 u - fctInnerChi outerChiIn c V1 u : ℝ) : ℂ) = 0) := by
  obtain ⟨c_V, _, hV_props⟩ := winVProps_of_window hK4 hSw
  obtain ⟨C_V, c_Vd, hCV0, _, hV_diff⟩ := win_V_diff_sym hK4 hSw
  obtain ⟨C_sc, hCsc0, hsc⟩ := win_comp_scale_T_diff_jc pbKV_nonneg
  obtain ⟨B_χ, hBχ0, hBχ⟩ := win_chi_deriv_jc
  obtain ⟨_, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  refine ⟨C_sc * B_χ * C_V, max 15000 (max c_V (max c_Vd c_χ)), by positivity, le_max_left _ _,
    fun {ε c α L_lo L_hi} hε hc hτ_lim hK4t hα hell1 h12 hell2 => ?_⟩
  have hcv : c_V ≤ c := (le_max_left _ _).trans ((le_max_right 15000 _).trans hc)
  have hcvd : c_Vd ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right 15000 _).trans hc)
  have hcχ : c_χ ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right 15000 _).trans hc)
  have hvp := hV_props hε hcv hτ_lim hK4t hα hell1 h12 hell2
  have hc0 := hvp.hc0
  have hc1 : 1 ≤ c := by linarith only [hvp.hc10000]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hT_diff : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_V * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((fctInnerT c (concreteInnerV K4 ε c L_hi α) u -
        fctInnerT c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ)) :=
    (hV_diff hε hcvd hτ_lim hK4t hα hell1 h12 hell2).2.congr hDu fun u hu => by
      have hy := fctInnerY_mem_35 hc1 hu
      unfold fctInnerT
      change ((2 ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * concreteInnerV K4 ε c L_hi α (fctInnerY c u) -
          2 ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * concreteInnerV K4 ε c L_lo α (fctInnerY c u) : ℝ) : ℂ) =
        ((2 ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u *
            (concreteBoxS K4 ε c).V ((concreteEll1 ε c L_hi, 1, α), fctInnerY c u) -
          2 ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u *
            (concreteBoxS K4 ε c).V ((concreteEll1 ε c L_lo, 1, α), fctInnerY c u) : ℝ) : ℂ)
      rw [hvp.heq_hi _ hy, hvp.heq_lo _ hy]
  have hT_diff_c : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_V * (L_hi - L_lo) * c ^ (-(1 / 3 : ℝ))) _ :=
    hT_diff.mono_B Icc_subset_Ici_self (le_of_eq (by ring))
  have hR3 : 3 * c ^ (1 / 4 : ℝ) * fctTau1 c ≤ 3 := by
    have hp : c ^ (1 / 4 : ℝ) * fctTau1 c = 1 := by
      unfold fctTau1; rw [← Real.rpow_add hc0]; norm_num
    linarith only [hp]
  have hchi_cd : ContDiffOn ℝ 10 (fun y : ℝ => ((outerChiIn y : ℝ) : ℂ)) (Ioo (-3 : ℝ) 3) :=
    (Complex.ofRealCLM.contDiff.comp (outerChiIn_cutoff.smooth.of_le
      (by norm_num : (10 : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))).contDiffOn
  have hcomp := hsc (B_g := B_χ) (D := C_V * (L_hi - L_lo))
    hvp.hc10000 hvp.hKV_small (Real.rpow_pos_of_pos hc0 _) le_rfl hR3
    hBχ0 (mul_nonneg hCV0 (sub_nonneg.mpr h12))
    hvp.hcd_lo hvp.hcd_hi hvp.hjets_lo hvp.hjets_hi hvp.hbd_lo hvp.hbd_hi hT_diff_c
    hchi_cd hBχ
  have hc14 : c ^ (1 / 4 : ℝ) * c ^ (-(1 / 3 : ℝ)) = c ^ (-(1 / 12 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hsym : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_sc * B_χ * C_V * c ^ (-(1 / 12 : ℝ)) * (L_hi - L_lo))
      (fun u => ((fctInnerChi outerChiIn c (concreteInnerV K4 ε c L_hi α) u -
        fctInnerChi outerChiIn c (concreteInnerV K4 ε c L_lo α) u : ℝ) : ℂ)) := by
    refine (hcomp.mono_B Icc_subset_Ici_self (le_of_eq ?_)).congr hDu fun u _ => ?_
    · calc C_sc * B_χ * c ^ (1 / 4 : ℝ) * (C_V * (L_hi - L_lo)) * c ^ (-(1 / 3 : ℝ))
          = (C_sc * B_χ * C_V) * (c ^ (1 / 4 : ℝ) * c ^ (-(1 / 3 : ℝ))) * (L_hi - L_lo) := by ring
        _ = C_sc * B_χ * C_V * c ^ (-(1 / 12 : ℝ)) * (L_hi - L_lo) := by rw [hc14]
    · dsimp only [fctInnerChi, fctTau1]
      have hdiv : ∀ V : ℝ → ℝ, fctInnerT c V u / c ^ (-(1 / 4 : ℝ)) = c ^ (1 / 4 : ℝ) * fctInnerT c V u := fun V => by
        rw [div_eq_mul_inv, Real.rpow_neg hc0.le, inv_inv, mul_comm]
      rw [hdiv, hdiv]; push_cast; rfl
  obtain ⟨hz1, _, _, _, hpl1⟩ := hB2 c hcχ _ hvp.hjets_lo
  obtain ⟨hz2, _, _, _, hpl2⟩ := hB2 c hcχ _ hvp.hjets_hi
  refine ⟨hsym, fun u hu => ?_, fun u hu => ?_⟩
  · have h1 := hpl1 u hu; have h2 := hpl2 u hu
    rw [show fctInnerChi outerChiIn c (concreteInnerV K4 ε c L_hi α) u -
        fctInnerChi outerChiIn c (concreteInnerV K4 ε c L_lo α) u = 0 by linarith only [h1, h2],
      Complex.ofReal_zero]
  · rw [hz1 u hu, hz2 u hu, sub_self, Complex.ofReal_zero]

lemma win_one_sub_chi_sym20 {c B_χ : ℝ} {V : ℝ → ℝ} (hc1 : 1 ≤ c) (hB0 : 0 ≤ B_χ)
    (h1m : FctSymClsOn (Icc 0 (fctUc c)) 8 0 B_χ (fun u => ((1 - fctInnerChi outerChiIn c V u : ℝ) : ℂ)))
    (hzero : ∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c), fctInnerChi outerChiIn c V u = 0)
    (hplat : ∀ u ∈ Icc 0 (fctUstar c), 1 - fctInnerChi outerChiIn c V u = 0) :
    FctSymCls 8 20 (max B_χ 1 * c ^ (-(5 / 3 : ℝ))) (fun u => 1 - chiExt c V u) ∧
    (∀ u ∈ Icc 0 (fctUstar c), (1 : ℂ) - chiExt c V u = 0) := by
  have hc0 : 0 < c := by linarith only [hc1]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDi : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hDu := uniqueDiffOn_Icc hUc0
  have huc : fctUstar c ≤ fctUc c := by
    dsimp only [fctUstar, fctUc]; linarith only [Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 12)]
  have h0s : FctSymCls 8 0 (max B_χ 1) (fun u => 1 - chiExt c V u) :=
    one_sub_chiExt_symCls hc1 hB0 (h1m.mono_set Set.Subset.rfl hDu hDu) hzero
  have hz_ustar : ∀ u ∈ Icc 0 (fctUstar c), (1 : ℂ) - chiExt c V u = 0 := fun u hu => by
    have hcu : u ≤ fctUc c := hu.2.trans huc
    simp only [chiExt, extUc, hcu, ↓reduceIte]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, hplat u hu, Complex.ofReal_zero]
  have hderiv_zero : ∀ r : ℕ, ∀ u ∈ Ico (0 : ℝ) (fctUstar c),
      iteratedDerivWithin r (fun x => 1 - chiExt c V x) (Ici 0) u = 0 := by
    intro r
    induction r with
    | zero =>
      intro u hu
      rw [iteratedDerivWithin_zero]
      exact hz_ustar u ⟨hu.1, hu.2.le⟩
    | succ m ihm =>
      intro u hu
      rw [iteratedDerivWithin_succ]
      have hev : iteratedDerivWithin m (fun x => 1 - chiExt c V x) (Ici 0) =ᶠ[𝓝[Ici 0] u] (fun _ => (0 : ℂ)) := by
        filter_upwards [inter_mem_nhdsWithin (Ici 0) (isOpen_Iio.mem_nhds hu.2)] with x hx
        exact ihm x ⟨hx.1, hx.2⟩
      change derivWithin (iteratedDerivWithin m (fun x => 1 - chiExt c V x) (Ici 0)) (Ici 0) u = 0
      rw [hev.derivWithin_eq (ihm u hu),
        (hasDerivWithinAt_const u (Ici 0) (0 : ℂ)).derivWithin (hDi u (mem_Ici.mpr hu.1))]
  refine ⟨⟨h0s.1, fun r hr u hu => ?_⟩, hz_ustar⟩
  rcases lt_or_ge u (fctUstar c) with hlt | hge
  · have hu1 : 0 ≤ 1 + u := by linarith only [hu.out]
    rw [hderiv_zero r u ⟨hu.out, hlt⟩, norm_zero]
    positivity
  · have h12_pos : 0 < c ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hc0 _
    have h12_ge1 : (1 : ℝ) ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow hc1 (by norm_num)
    have hustar_le : c ^ ((1 : ℝ) / 12) ≤ 1 + u := by
      have : c ^ ((1 : ℝ) / 12) ≤ fctUstar c := by dsimp only [fctUstar]; linarith only [h12_pos]
      linarith only [this, hge]
    have hpow20 : (1 + u) ^ (0 - (r : ℝ)) ≤ c ^ (-(5 / 3 : ℝ)) * (1 + u) ^ (20 - (r : ℝ)) := by
      have hu1 : 0 < 1 + u := by linarith only [hu.out]
      have hsub : (0 - (r : ℝ)) = (-20 : ℝ) + (20 - (r : ℝ)) := by ring
      rw [hsub, Real.rpow_add hu1]
      have hneg20 : (1 + u) ^ (-20 : ℝ) ≤ c ^ (-(5 / 3 : ℝ)) := by
        calc (1 + u) ^ (-20 : ℝ) ≤ (c ^ ((1 : ℝ) / 12)) ^ (-20 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos h12_pos hustar_le (by norm_num)
          _ = c ^ (-(5 / 3 : ℝ)) := by rw [← Real.rpow_mul hc0.le]; norm_num
      exact mul_le_mul_of_nonneg_right hneg20 (Real.rpow_nonneg hu1.le _)
    calc ‖iteratedDerivWithin r (fun x => 1 - chiExt c V x) (Ici 0) u‖
        ≤ max B_χ 1 * (1 + u) ^ (0 - (r : ℝ)) := h0s.2 r hr u hu
      _ ≤ max B_χ 1 * (c ^ (-(5 / 3 : ℝ)) * (1 + u) ^ (20 - (r : ℝ))) :=
          mul_le_mul_of_nonneg_left hpow20 (by positivity)
      _ = max B_χ 1 * c ^ (-(5 / 3 : ℝ)) * (1 + u) ^ (20 - (r : ℝ)) := by ring

/-- info: 'FormalResearch.SignUncertainty.win_J_diff_and_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_J_diff_and_bounds

/-- info: 'FormalResearch.SignUncertainty.win_muMix_diff_and_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_muMix_diff_and_bounds

/-- info: 'FormalResearch.SignUncertainty.win_chi_diff_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_chi_diff_sym

/-- info: 'FormalResearch.SignUncertainty.win_one_sub_chi_sym20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_one_sub_chi_sym20

end FormalResearch.SignUncertainty
