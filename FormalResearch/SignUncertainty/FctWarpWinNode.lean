/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpSqOuter
public import FormalResearch.SignUncertainty.FctWarpSolve

/-!
# Sharpened zero node error `O_{K4}(c^{-4/3})` on the Airy window (`fct:warp-win`)

Leaf helper module for `FctWarpWinJ0.lean`, `FctWarpWinInner.lean`, and `FctWarpAsympWin.lean`:
* `fctWarpPair_adm`: `(L₁, t)` belongs to `(concreteInnerFamily K4 ε).adm c` for all `t` between `0` and `α`.
* `win_zero_a1_err`: improves `|û₁ - a₁|` at `(L₁, α) = fctWarpPair h ε c` from `c^{-7/6}` to
  `O_{K4}(c^{-4/3})` and gives `Ai(û₁)² ≤ C c^{-8/3}`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

/-- `(L₁, t)` satisfies `(concreteInnerFamily K4 ε).adm c` for every `t` in `uIcc 0 α`. -/
lemma fctWarpPair_adm {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 32 ^ 4 ≤ c₀ ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      let L1 := fctWarpL1 h ε c
      let α := fctWarpAlpha h ε c
      (concreteInnerFamily K4 ε).adm c L1 α ∧
        ∀ t ∈ Set.uIcc 0 α, (concreteInnerFamily K4 ε).adm c L1 t := by
  let Ccl : ℝ := max h.choose 0
  obtain ⟨_, c_fj, _, _, hfj⟩ := fctWarpFJ_of_class hK4 Ccl
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      h.choose_spec.choose ≤ c ∧ (32 : ℝ) ^ 4 ≤ c ∧ c_fj ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim ∧ K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    refine Eventually.and (eventually_ge_atTop h.choose_spec.choose)
      (Eventually.and (eventually_ge_atTop (32 ^ 4 : ℝ))
        (Eventually.and (eventually_ge_atTop c_fj) (Eventually.and ?_ ?_)))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds pbTauLim_pos)
    · have h0 : Tendsto (fun c : ℝ => K4 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K4
      exact h0.eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨max (32 ^ 4) c₀, le_max_left _ _, fun {ε c} hε hc => ?_⟩
  obtain ⟨hc_h, hc32, hcfj, hτlim, hK4t⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hc100 : (100 : ℝ) ≤ c := le_trans (by norm_num) hc32
  have hpair := (fctWarpPair_spec h hε hc_h).1
  obtain ⟨W, _, hWS, hWell, hmem⟩ := hfj hε hcfj
  have hbox : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim ∧ K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧ 100 ≤ c :=
    ⟨hτlim, hK4t, hc100⟩
  have hadm : ∀ {t : ℝ}, |t| ≤ |fctWarpAlpha h ε c| → (concreteInnerFamily K4 ε).adm c (fctWarpL1 h ε c) t := by
    intro t ht
    have hcl : FctWarpClass Ccl ε c (fctWarpL1 h ε c) t := by
      refine ⟨hpair.1, (hpair.2.1).trans ?_, ?_⟩
      · have : 0 < c⁻¹ := inv_pos.mpr (by linarith only [hc100])
        have : h.choose ≤ Ccl := le_max_left _ _
        gcongr
      · have hα_bd : |fctWarpAlpha h ε c| ≤ Ccl * c ^ (-(2 / 3 : ℝ)) :=
          (hpair.2.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        exact ht.trans hα_bd
    obtain ⟨hL_mem, ht_mem, hΨ_mem⟩ := hmem hcl
    let p : ℝ × ℝ := (fctWarpL1 h ε c, t)
    exact fctWarpChart_mem_adm hK4 hε hbox W hWS hWell (p := p) ⟨hL_mem, ht_mem⟩ hΨ_mem
  refine ⟨hadm le_rfl, fun t ht => hadm ?_⟩
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨ht0, hta⟩ | ⟨hta, ht0⟩
  · have hα0 : 0 ≤ fctWarpAlpha h ε c := ht0.trans hta
    rw [abs_of_nonneg ht0, abs_of_nonneg hα0]; exact hta
  · have hα0 : fctWarpAlpha h ε c ≤ 0 := hta.trans ht0
    rw [abs_of_nonpos ht0, abs_of_nonpos hα0]; exact neg_le_neg hta

private lemma win_u_alpha_shift {K4 ε c L1 α Cα0 C_α : ℝ}
    (_hK4 : 1 ≤ K4) (hc100 : 100 ≤ c) (hCα0 : 0 ≤ Cα0) (hCα : 0 ≤ C_α)
    (_hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hc76_1 : c ^ (-(7 / 6 : ℝ)) ≤ 1) (hα_bd : |α| ≤ C_α * c ^ (-(2 / 3 : ℝ)))
    (hth_bd : ∀ τ : ℝ, |τ| ≤ 12 * c ^ (-(1 / 4 : ℝ)) →
      |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ| ≤
        Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * (|τ| / c ^ (-(1 / 4 : ℝ))) ^ 11)
    (hadm_t : ∀ t ∈ Set.uIcc 0 α, (concreteInnerFamily K4 ε).adm c L1 t)
    (W : FctWarpChartData K4 ε c) (hWS : W.S = concreteBoxS K4 ε c)
    (ht_dom : ∀ t ∈ Set.uIcc 0 α, (L1, t) ∈ concretePhaseDom W.ellMin ε c) :
    let S := concreteBoxS K4 ε c
    |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α) -
      (-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, 0))| ≤
        ((1 / 2 : ℝ) * Cα0 * 4 ^ 11 * C_α) * c ^ (-(4 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith only [hc100]
  have hc1 : 1 ≤ c := by linarith only [hc100]
  set S := concreteBoxS K4 ε c
  let g_u : ℝ → ℝ := fun t => -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t)
  have hg_der : ∀ t ∈ Set.uIcc 0 α, HasDerivWithinAt g_u
      (-fctKappa c * fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) (L1, t) (0, 1))
      (Set.uIcc 0 α) t := fun t ht => by
    have hcd := W.box.atil_contDiffAt (ht_dom t ht)
    have hfa : HasFDerivAt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S))
        (fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) (L1, t)) (L1, t) :=
      (hcd.differentiableAt (by simp)).hasFDerivAt
    have hγ : HasDerivAt (fun s : ℝ => (L1, s)) (0, 1) t := by
      simpa using (hasDerivAt_const t L1).prodMk (hasDerivAt_id t)
    have hc := (hfa.comp_hasDerivAt t hγ).const_mul (-fctKappa c)
    rw [hWS] at hc
    exact hc.hasDerivWithinAt
  have hg_bd : ∀ t ∈ Set.uIcc 0 α,
      ‖-fctKappa c * fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) (L1, t) (0, 1)‖ ≤
        (1 / 2) * Cα0 * 4 ^ 11 * c ^ (-(17 / 12 : ℝ)) := fun t ht => by
    have hp := ht_dom t ht
    have hû_pt : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t) - airyZero 1| ≤ 1 :=
      (hadm_t t ht).2.2.1.trans hc76_1
    have ha1 := airyZero_one
    have hka_lo : 1 ≤ fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t) := by
      linarith only [(abs_le.mp hû_pt).2, ha1.2]
    have hka_hi : fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t) ≤ 4 := by
      linarith only [(abs_le.mp hû_pt).1, ha1.1]
    have hκ_pos : 0 < fctKappa c := fctKappa_pos hc0
    have hã_pos : 0 < fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t) :=
      pos_of_mul_pos_right (by linarith only [hka_lo]) hκ_pos.le
    have h223_eq : ((2 : ℝ) ^ (-(2 / 3 : ℝ)))⁻¹ = (2 : ℝ) ^ (2 / 3 : ℝ) := by
      rw [Real.rpow_neg (by norm_num), inv_inv]
    have hã_lo : (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) ≤
        fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t) := by
      refine le_trans ?_ ((div_le_iff₀' hκ_pos).mpr hka_lo)
      unfold fctKappa; rw [one_div, mul_inv, h223_eq, Real.rpow_neg hc0.le]
    have hã_hi : fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t) ≤
        4 * (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by
      refine ((le_div_iff₀' hκ_pos).mpr hka_hi).trans_eq ?_
      unfold fctKappa; rw [div_eq_mul_inv, mul_inv, h223_eq, Real.rpow_neg hc0.le]; ring
    have hsqrt_lo : (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) ≤
        Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t)) := by
      have hsq : ((2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) ^ 2 =
          (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_natCast (c ^ _),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hc0.le]; norm_num
      exact Real.le_sqrt_of_sq_le (hsq.symm ▸ hã_lo)
    have hsqrt_hi : Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t)) ≤
        2 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) := by
      have hsq : (2 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) ^ 2 =
          4 * (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_natCast (c ^ _),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hc0.le]; norm_num
      exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq.symm ▸ hã_hi⟩
    have hV_bd : 100 / 95 ≤ S.V ((concreteEll1 ε c L1, 1, t), S.A (concreteEll1 ε c L1, 1, t)) ∧
        S.V ((concreteEll1 ε c L1, 1, t), S.A (concreteEll1 ε c L1, 1, t)) ≤ 100 / 92 := by
      simpa only [hWS] using W.h_S_V_bounds (L1, t) hp
    have hτ0_eq : concreteTau0 ε c S (L1, t) =
        Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t)) *
          S.V ((concreteEll1 ε c L1, 1, t), S.A (concreteEll1 ε c L1, 1, t)) := by
      simpa only [hWS] using W.h_V_eq (L1, t) hp
    have hτ0_nn : 0 ≤ concreteTau0 ε c S (L1, t) := by
      rw [hτ0_eq]; exact mul_nonneg (Real.sqrt_nonneg _) (by linarith only [hV_bd.1])
    have h213_le : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 1.3 := by
      by_contra hgt; push Not at hgt
      have h1 : (1.3 : ℝ) ^ 3 < ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
      have h2 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
    have hτ0_le : |concreteTau0 ε c S (L1, t)| ≤ 4 * c ^ (-(1 / 3 : ℝ)) := by
      rw [abs_of_nonneg hτ0_nn, hτ0_eq]
      calc Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t)) *
            S.V ((concreteEll1 ε c L1, 1, t), S.A (concreteEll1 ε c L1, 1, t))
          ≤ (2 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) * (100 / 92) :=
            mul_le_mul hsqrt_hi hV_bd.2 (by linarith only [hV_bd.1]) (by positivity)
        _ ≤ (2 * 1.3 * c ^ (-(1 / 3 : ℝ))) * (100 / 92) := by gcongr
        _ ≤ 4 * c ^ (-(1 / 3 : ℝ)) := by
            have : 0 ≤ c ^ (-(1 / 3 : ℝ)) := by positivity
            linarith
    have hc12_1 : c ^ (-(1 / 12 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hτ0_12 : |concreteTau0 ε c S (L1, t)| ≤ 12 * c ^ (-(1 / 4 : ℝ)) := by
      calc |concreteTau0 ε c S (L1, t)| ≤ 4 * c ^ (-(1 / 3 : ℝ)) := hτ0_le
        _ = 4 * c ^ (-(1 / 12 : ℝ)) * c ^ (-(1 / 4 : ℝ)) := by
            rw [mul_assoc, ← Real.rpow_add hc0]; norm_num
        _ ≤ 12 * c ^ (-(1 / 4 : ℝ)) := by gcongr; linarith
    have hth_vA := hth_bd _ hτ0_12
    have hrat_le : |concreteTau0 ε c S (L1, t)| / c ^ (-(1 / 4 : ℝ)) ≤ 4 * c ^ (-(1 / 12 : ℝ)) := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
      refine hτ0_le.trans_eq ?_
      rw [mul_assoc, ← Real.rpow_add hc0]; norm_num
    have hth_le : |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S (L1, t))| ≤
        Cα0 * 4 ^ 11 * c ^ (-(17 / 12 : ℝ)) := by
      have hc11 : (c ^ (-(1 / 4 : ℝ))) ^ 2 * (c ^ (-(1 / 12 : ℝ))) ^ 11 = c ^ (-(17 / 12 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_mul hc0.le,
          ← Real.rpow_add hc0]; norm_num
      calc |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S (L1, t))|
          ≤ Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * (|concreteTau0 ε c S (L1, t)| / c ^ (-(1 / 4 : ℝ))) ^ 11 := hth_vA
        _ ≤ Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * (4 * c ^ (-(1 / 12 : ℝ))) ^ 11 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (Real.rpow_nonneg hc0.le _)) hrat_le 11)
              (by positivity)
        _ = Cα0 * 4 ^ 11 * ((c ^ (-(1 / 4 : ℝ))) ^ 2 * (c ^ (-(1 / 12 : ℝ))) ^ 11) := by ring
        _ = Cα0 * 4 ^ 11 * c ^ (-(17 / 12 : ℝ)) := by rw [hc11]
    have hdA_eq : fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) (L1, t) (0, 1) =
        c⁻¹ * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S (L1, t)) /
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t)) := by
      simpa only [hWS] using W.h_dA (L1, t) hp
    have hκ_div_sqrt : fctKappa c * c⁻¹ /
        Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t)) ≤ 1 / 2 := by
      calc fctKappa c * c⁻¹ / Real.sqrt _
          ≤ (2 ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * c⁻¹ / ((2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by
            unfold fctKappa; gcongr
        _ = (2 ^ (-(2 / 3 : ℝ)) / (2 : ℝ) ^ (1 / 3 : ℝ)) * (c ^ (2 / 3 : ℝ) * c⁻¹ / c ^ (-(1 / 3 : ℝ))) := by ring
        _ = (1 / 2) * 1 := by
            congr 1
            · rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]; norm_num
            · rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, ← Real.rpow_neg_one, ← Real.rpow_add hc0,
                ← Real.rpow_add hc0]; norm_num [Real.rpow_zero]
        _ = 1 / 2 := mul_one _
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hκ_pos, hdA_eq]
    calc fctKappa c * |c⁻¹ * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S (L1, t)) /
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t))|
        = (fctKappa c * c⁻¹ / Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, t))) *
            |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S (L1, t))| := by
          rw [abs_div, abs_mul, abs_of_pos (inv_pos.mpr hc0),
            abs_of_pos (Real.sqrt_pos.mpr hã_pos)]; ring
      _ ≤ (1 / 2) * (Cα0 * 4 ^ 11 * c ^ (-(17 / 12 : ℝ))) := by gcongr
      _ = (1 / 2) * Cα0 * 4 ^ 11 * c ^ (-(17 / 12 : ℝ)) := by ring
  have hmv_u := (convex_uIcc 0 α).norm_image_sub_le_of_norm_hasDerivWithin_le
    hg_der hg_bd right_mem_uIcc left_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, zero_sub, abs_neg, abs_sub_comm (g_u 0) (g_u α)] at hmv_u
  have hc_pow : c ^ (-(17 / 12 : ℝ)) * c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  calc |g_u α - g_u 0| ≤ (1 / 2) * Cα0 * 4 ^ 11 * c ^ (-(17 / 12 : ℝ)) * |α| := hmv_u
    _ ≤ (1 / 2) * Cα0 * 4 ^ 11 * c ^ (-(17 / 12 : ℝ)) * (C_α * c ^ (-(2 / 3 : ℝ))) := by gcongr
    _ = ((1 / 2) * Cα0 * 4 ^ 11 * C_α) * (c ^ (-(17 / 12 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by ring
    _ ≤ ((1 / 2) * Cα0 * 4 ^ 11 * C_α) * c ^ (-(4 / 3 : ℝ)) := by gcongr

/-- **`win_zero_a1_err`**: at `(L₁, α) = fctWarpPair h ε c`, `|û₁ - a₁| = O_{K4}(c^{-4/3})` and `Ai(û₁)² = O_{K4}(c^{-8/3})`. -/
theorem win_zero_a1_err {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      let S := concreteBoxS K4 ε c
      let û1 := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (fctWarpL1 h ε c, fctWarpAlpha h ε c)
      |û1 - airyZero 1| ≤ C * c ^ (-(4 / 3 : ℝ)) ∧ (airyAi û1) ^ 2 ≤ C * c ^ (-(8 / 3 : ℝ)) := by
  obtain ⟨c_adm, _, hadm_all⟩ := fctWarpPair_adm hK4 h
  obtain ⟨CR1, cR1, hCR1, _, hRes1⟩ := fctWarpI_zero_residual (K4 := K4) (ε := 1) hK4
  obtain ⟨CRm1, cRm1, hCRm1, _, hResm1⟩ := fctWarpI_zero_residual (K4 := K4) (ε := -1) hK4
  obtain ⟨CDA1, cDA1, hCDA1, _, hDA1⟩ := fctWarpI_derivAlpha_at_a1_err (K4 := K4) (ε := 1) hK4
  obtain ⟨CDAm1, cDAm1, hCDAm1, _, hDAm1⟩ := fctWarpI_derivAlpha_at_a1_err (K4 := K4) (ε := -1) hK4
  obtain ⟨_, c_fj, _, _, hfj⟩ := fctWarpFJ_of_class hK4 (max h.choose 0)
  obtain ⟨_, _, _, Cα0, _, _, _, hCα0, hth_bd⟩ := thetaD_center_bounds
  obtain ⟨C_g, hCg0, hg_lip⟩ := fctG0_lipschitz_near_airyZero
  have hAi'_cont : ContinuousOn airyAi' (Icc (airyZero 1 - 1) (airyZero 1 + 1)) :=
    continuous_airyAi'.continuousOn
  obtain ⟨C_Ai, hCAi_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hAi'_cont
  let C_Ai0 : ℝ := max 0 C_Ai
  let C_R : ℝ := max CR1 CRm1
  let C_DA : ℝ := max CDA1 CDAm1
  let C_α : ℝ := |h.choose| + 1
  let C_N0_dA : ℝ := ‖-Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 (airyZero 1)‖ + C_DA
  let C_u10 : ℝ := 2 / Real.sqrt π * (C_R + C_N0_dA * C_α)
  let C_shift : ℝ := (1 / 2 : ℝ) * Cα0 * 4 ^ 11 * C_α
  let C_u : ℝ := C_u10 + C_shift
  let C_fin : ℝ := max C_u (C_Ai0 ^ 2 * C_u ^ 2)
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      c_adm ≤ c ∧ h.choose_spec.choose ≤ c ∧ cR1 ≤ c ∧ cRm1 ≤ c ∧ cDA1 ≤ c ∧ cDAm1 ≤ c ∧
      c_fj ≤ c ∧ c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      c ^ (-(7 / 6 : ℝ)) ≤ 1 ∧ C_g * c ^ (-(7 / 6 : ℝ)) ≤ Real.sqrt π / 2 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
          (Eventually.and (eventually_ge_atTop _) (Eventually.and ?_ (Eventually.and ?_ ?_))))))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).eventually (Iic_mem_nhds zero_lt_one)
    · have h0 : Tendsto (fun c : ℝ => C_g * c ^ (-(7 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).const_mul C_g
      exact h0.eventually (Iic_mem_nhds (half_pos (Real.sqrt_pos.mpr Real.pi_pos)))
  obtain ⟨c_ev, hc_ev⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_fin, max (32 ^ 4) c_ev, by positivity, le_max_left _ _, fun {ε c} hε hc => ?_⟩
  obtain ⟨hca, hch, hcR1', hcRm1', hcDA1', hcDAm1', hcfj, hτD, hc76_1, hCg_bd⟩ :=
    hc_ev c ((le_max_right _ _).trans hc)
  have hc32 : (32 : ℝ) ^ 4 ≤ c := (le_max_left _ _).trans hc
  have hc100 : (100 : ℝ) ≤ c := le_trans (by norm_num) hc32
  have hc0 : 0 < c := by linarith only [hc100]
  have hc1 : 1 ≤ c := by linarith only [hc100]
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hpair := fctWarpPair_spec h hε hch
  have hzero : fctWarpI K4 ε c L1 α = 0 := hpair.2.2
  have hadm_t := (hadm_all hε hca).2
  have hadm0 : (concreteInnerFamily K4 ε).adm c L1 0 := hadm_t 0 left_mem_uIcc
  have hadmα : (concreteInnerFamily K4 ε).adm c L1 α := hadm_t α right_mem_uIcc
  have hα_bd : |α| ≤ C_α * c ^ (-(2 / 3 : ℝ)) :=
    (hpair.1.2.2).trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self h.choose]) (by positivity))
  -- 1. MVT for `fctWarpI K4 ε c L1` from `0` to `α`
  have hder_I : ∀ t ∈ Set.uIcc 0 α, HasDerivWithinAt (fun s => fctWarpI K4 ε c L1 s)
      (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 t τ) (Set.uIcc 0 α) t :=
    fun t _ => (hasDerivAt_fctWarpI_alpha hK4 hε hc1 hτD L1 t).hasDerivWithinAt
  have hDA_bd : ∀ t ∈ Set.uIcc 0 α,
      ‖((warpN0 c : ℝ) : ℂ) * (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 t τ)‖ ≤
        C_N0_dA * c ^ (-(2 / 3 : ℝ)) := fun t ht => by
    have hDA_err : ‖((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
        (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 t τ) -
        (-Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 (airyZero 1))‖ ≤
        C_DA * c ^ (-(1 / 2 : ℝ)) := by
      rcases hε with rfl | rfl
      · exact (hDA1 hcDA1' (hadm_t t ht)).trans (by gcongr; exact le_max_left _ _)
      · exact (hDAm1 hcDAm1' (hadm_t t ht)).trans (by gcongr; exact le_max_right _ _)
    have hc12_1 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    let z_d : ℂ := ((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
      (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 t τ)
    let z_0 : ℂ := -Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 (airyZero 1)
    have htri_zd : ‖z_d‖ ≤ ‖z_0‖ + ‖z_d - z_0‖ := by
      calc ‖z_d‖ = ‖z_0 + (z_d - z_0)‖ := by ring_nf
        _ ≤ ‖z_0‖ + ‖z_d - z_0‖ := norm_add_le _ _
    have hCDA_nn : 0 ≤ C_DA := le_max_of_le_left hCDA1
    have hnorm_c23 : ‖z_d‖ ≤ C_N0_dA := by
      have h1 : ‖z_d - z_0‖ ≤ C_DA * 1 := hDA_err.trans (mul_le_mul_of_nonneg_left hc12_1 hCDA_nn)
      dsimp only [C_N0_dA, z_0]; linarith
    have hrew : ((warpN0 c : ℝ) : ℂ) * (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 t τ) =
        ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * z_d := by
      have hmul : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add hc0]; norm_num
      calc ((warpN0 c : ℝ) : ℂ) * (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 t τ)
          = ((c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
              (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 t τ) := by
            rw [hmul, one_mul]
        _ = ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * z_d := by dsimp only [z_d]; push_cast; ring
    rw [hrew, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc0.le _), mul_comm]
    exact mul_le_mul_of_nonneg_right hnorm_c23 (Real.rpow_nonneg hc0.le _)
  have hmv_I := (convex_uIcc 0 α).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hder_I t ht).const_mul ((warpN0 c : ℝ) : ℂ))
    hDA_bd right_mem_uIcc left_mem_uIcc
  have hI0_le : ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0‖ ≤ C_N0_dA * C_α * c ^ (-(4 / 3 : ℝ)) := by
    have h0eq : ((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 α = 0 := by rw [hzero, mul_zero]
    have hmv1 : ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0‖ ≤ C_N0_dA * c ^ (-(2 / 3 : ℝ)) * |α| := by
      calc ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0‖
          = ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - ((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 α‖ := by
            rw [h0eq, sub_zero]
        _ ≤ C_N0_dA * c ^ (-(2 / 3 : ℝ)) * ‖(0 : ℝ) - α‖ := hmv_I
        _ = C_N0_dA * c ^ (-(2 / 3 : ℝ)) * |α| := by rw [zero_sub, Real.norm_eq_abs, abs_neg]
    calc ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0‖
        ≤ C_N0_dA * c ^ (-(2 / 3 : ℝ)) * |α| := hmv1
      _ ≤ C_N0_dA * c ^ (-(2 / 3 : ℝ)) * (C_α * c ^ (-(2 / 3 : ℝ))) := by gcongr
      _ = C_N0_dA * C_α * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by ring
      _ = C_N0_dA * C_α * c ^ (-(4 / 3 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
  -- 2. `‖fctG0 û0‖ ≤ (C_R + C_N0_dA * C_α) * c^{-4/3}`
  let S := concreteBoxS K4 ε c
  let û0 := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, 0)
  let û1 := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  have hres0 : ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - Complex.I * fctG0 û0‖ ≤ C_R * c ^ (-(4 / 3 : ℝ)) := by
    rcases hε with rfl | rfl
    · exact (hRes1 hcR1' hadm0).trans (by gcongr; exact le_max_left _ _)
    · exact (hResm1 hcRm1' hadm0).trans (by gcongr; exact le_max_right _ _)
  have hG0_bd : ‖fctG0 û0‖ ≤ (C_R + C_N0_dA * C_α) * c ^ (-(4 / 3 : ℝ)) := by
    have hnormI : ‖Complex.I * fctG0 û0‖ = ‖fctG0 û0‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    have htri_I : ‖Complex.I * fctG0 û0‖ ≤ ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0‖ +
        ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - Complex.I * fctG0 û0‖ := by
      have heq_sub : Complex.I * fctG0 û0 = ((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 -
          (((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - Complex.I * fctG0 û0) := by ring
      calc ‖Complex.I * fctG0 û0‖
          = ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 -
              (((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - Complex.I * fctG0 û0)‖ := congrArg norm heq_sub
        _ ≤ _ := norm_sub_le _ _
    rw [← hnormI]
    calc ‖Complex.I * fctG0 û0‖
        ≤ ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0‖ +
            ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - Complex.I * fctG0 û0‖ := htri_I
      _ ≤ C_N0_dA * C_α * c ^ (-(4 / 3 : ℝ)) + C_R * c ^ (-(4 / 3 : ℝ)) := add_le_add hI0_le hres0
      _ = (C_R + C_N0_dA * C_α) * c ^ (-(4 / 3 : ℝ)) := by ring
  -- 3. `|û0 - airyZero 1| ≤ C_u10 * c^{-4/3}`
  have hû0_76 : |û0 - airyZero 1| ≤ c ^ (-(7 / 6 : ℝ)) := hadm0.2.2.1
  have hG_mvt : ‖fctG0 û0 - ((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1)‖ ≤
      C_g * |û0 - airyZero 1| * |û0 - airyZero 1| := by
    let g : ℝ → ℂ := fun w => fctG0 w - (w : ℂ) * deriv fctG0 (airyZero 1)
    have hg_der : ∀ w ∈ Set.uIcc (airyZero 1) û0, HasDerivWithinAt g
        (deriv fctG0 w - deriv fctG0 (airyZero 1)) (Set.uIcc (airyZero 1) û0) w := fun w _ => by
      have hf := (hasDerivAt_fctG0 w).sub (((hasDerivAt_id w).ofReal_comp).mul_const (deriv fctG0 (airyZero 1)))
      rw [← (hasDerivAt_fctG0 w).deriv] at hf
      exact (hf.congr_deriv (by rw [Complex.ofReal_one, one_mul])).hasDerivWithinAt
    have hg_bd : ∀ w ∈ Set.uIcc (airyZero 1) û0, ‖deriv fctG0 w - deriv fctG0 (airyZero 1)‖ ≤ C_g * |û0 - airyZero 1| := by
      intro w hw
      have hw1 : |w - airyZero 1| ≤ |û0 - airyZero 1| := by
        rw [Set.mem_uIcc] at hw
        rcases hw with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rw [abs_le] <;> constructor <;>
          linarith only [ha, hb, le_abs_self (û0 - airyZero 1), neg_abs_le (û0 - airyZero 1)]
      have h1 := hg_lip (k := 1) (by norm_num) w (hw1.trans (hû0_76.trans hc76_1))
      rw [iteratedDeriv_one] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hw1 hCg0)
    have hmv := (convex_uIcc (airyZero 1) û0).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg_der hg_bd right_mem_uIcc left_mem_uIcc
    have hlhs : ‖g (airyZero 1) - g û0‖ = ‖fctG0 û0 - ((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1)‖ := by
      rw [norm_sub_rev]; congr 1; dsimp only [g]; rw [fctG0_airyZero]; push_cast; ring
    have hrhs : ‖airyZero 1 - û0‖ = |û0 - airyZero 1| := by rw [Real.norm_eq_abs, abs_sub_comm]
    rw [hlhs, hrhs] at hmv
    exact hmv
  have hpi_pos : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hlin_norm : ‖((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1)‖ =
      2 * Real.sqrt π * |û0 - airyZero 1| := by
    rw [deriv_fctG0_airyZero, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    ring
  have hquad_le : C_g * |û0 - airyZero 1| * |û0 - airyZero 1| ≤ Real.sqrt π / 2 * |û0 - airyZero 1| := by
    have h1 : C_g * |û0 - airyZero 1| ≤ Real.sqrt π / 2 :=
      (mul_le_mul_of_nonneg_left hû0_76 hCg0).trans hCg_bd
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hû0_a1 : |û0 - airyZero 1| ≤ C_u10 * c ^ (-(4 / 3 : ℝ)) := by
    have htri : ‖((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1)‖ - ‖fctG0 û0‖ ≤
        ‖fctG0 û0 - ((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1)‖ := by
      calc ‖((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1)‖ - ‖fctG0 û0‖
          ≤ ‖((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1) - fctG0 û0‖ :=
            norm_sub_norm_le _ _
        _ = ‖fctG0 û0 - ((û0 - airyZero 1 : ℝ) : ℂ) * deriv fctG0 (airyZero 1)‖ := norm_sub_rev _ _
    have hbd_sqrt : (3 / 2 : ℝ) * Real.sqrt π * |û0 - airyZero 1| ≤ ‖fctG0 û0‖ := by
      linarith only [htri, hlin_norm, hG_mvt, hquad_le]
    have h1 : |û0 - airyZero 1| ≤ 2 / Real.sqrt π * ‖fctG0 û0‖ := by
      have hdiv : |û0 - airyZero 1| ≤ ‖fctG0 û0‖ / ((3 / 2) * Real.sqrt π) :=
        (le_div_iff₀ (by positivity)).mpr (by linarith only [hbd_sqrt])
      have hmul : ‖fctG0 û0‖ / ((3 / 2) * Real.sqrt π) ≤ 2 / Real.sqrt π * ‖fctG0 û0‖ := by
        rw [div_eq_mul_inv, mul_inv, mul_comm (‖fctG0 û0‖)]
        have hnum : ((3 / 2 : ℝ)⁻¹ * (Real.sqrt π)⁻¹) ≤ 2 / Real.sqrt π := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
      exact hdiv.trans hmul
    calc |û0 - airyZero 1| ≤ 2 / Real.sqrt π * ‖fctG0 û0‖ := h1
      _ ≤ 2 / Real.sqrt π * ((C_R + C_N0_dA * C_α) * c ^ (-(4 / 3 : ℝ))) := by gcongr
      _ = C_u10 * c ^ (-(4 / 3 : ℝ)) := by dsimp only [C_u10]; ring
  -- 4. `|û1 - û0| ≤ C_shift * c^{-4/3}`
  obtain ⟨W, _, hWS, _, hmemW⟩ := hfj hε hcfj
  have ht_dom : ∀ t ∈ Set.uIcc 0 α, (L1, t) ∈ concretePhaseDom W.ellMin ε c := fun t ht => by
    have hcl : FctWarpClass (max h.choose 0) ε c L1 t := by
      refine ⟨hpair.1.1, hpair.1.2.1.trans ?_, ?_⟩
      · have : 0 < c⁻¹ := inv_pos.mpr hc0; have : h.choose ≤ max h.choose 0 := le_max_left _ _; gcongr
      · have ht_abs : |t| ≤ |α| := by
          rw [Set.mem_uIcc] at ht
          rcases ht with ⟨ht0, hta⟩ | ⟨hta, ht0⟩
          · rw [abs_of_nonneg ht0, abs_of_nonneg (ht0.trans hta)]; exact hta
          · rw [abs_of_nonpos ht0, abs_of_nonpos (hta.trans ht0)]; exact neg_le_neg hta
        exact ht_abs.trans (hpair.1.2.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    obtain ⟨h1, h2, _⟩ := hmemW hcl
    exact W.h_rect_sub ⟨h1, h2⟩
  have hshift := win_u_alpha_shift hK4 hc100 hCα0 (by positivity) hτD hc76_1 hα_bd
    (fun τ hτ => (hth_bd hK4 hc0 hτD).1 τ hτ |>.2.2.2) hadm_t W hWS ht_dom
  have hû1_a1 : |û1 - airyZero 1| ≤ C_u * c ^ (-(4 / 3 : ℝ)) := by
    have hsplit : û1 - airyZero 1 = (û1 - û0) + (û0 - airyZero 1) := by ring
    calc |û1 - airyZero 1| = |(û1 - û0) + (û0 - airyZero 1)| := by rw [hsplit]
      _ ≤ |û1 - û0| + |û0 - airyZero 1| := abs_add_le _ _
      _ ≤ C_shift * c ^ (-(4 / 3 : ℝ)) + C_u10 * c ^ (-(4 / 3 : ℝ)) := add_le_add hshift hû0_a1
      _ = C_u * c ^ (-(4 / 3 : ℝ)) := by dsimp only [C_u, C_shift]; ring
  have hAi_le : |airyAi û1| ≤ C_Ai0 * |û1 - airyZero 1| := by
    have hû1_76 : |û1 - airyZero 1| ≤ 1 := hadmα.2.2.1.trans hc76_1
    have hmv_Ai := (convex_Icc (airyZero 1 - 1) (airyZero 1 + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hasDerivAt_airyAi x).hasDerivWithinAt)
      (fun x hx => (hCAi_bd x hx).trans (le_max_right 0 C_Ai))
      (show airyZero 1 ∈ Icc (airyZero 1 - 1) (airyZero 1 + 1) from
        ⟨sub_le_self _ zero_le_one, le_add_of_nonneg_right zero_le_one⟩)
      (show û1 ∈ Icc (airyZero 1 - 1) (airyZero 1 + 1) from by
        rw [abs_le] at hû1_76; exact ⟨by linarith only [hû1_76.1], by linarith only [hû1_76.2]⟩)
    have h_Ai0 : airyAi (airyZero 1) = 0 := airyAi_airyZero 1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h_Ai0, sub_zero] at hmv_Ai
    exact hmv_Ai
  have hAi_sq : (airyAi û1) ^ 2 ≤ C_Ai0 ^ 2 * C_u ^ 2 * c ^ (-(8 / 3 : ℝ)) := by
    have hc83 : (c ^ (-(4 / 3 : ℝ))) ^ 2 = c ^ (-(8 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    calc (airyAi û1) ^ 2 = |airyAi û1| ^ 2 := (sq_abs _).symm
      _ ≤ (C_Ai0 * |û1 - airyZero 1|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAi_le 2
      _ ≤ (C_Ai0 * (C_u * c ^ (-(4 / 3 : ℝ)))) ^ 2 := by gcongr
      _ = C_Ai0 ^ 2 * C_u ^ 2 * (c ^ (-(4 / 3 : ℝ))) ^ 2 := by ring
      _ = C_Ai0 ^ 2 * C_u ^ 2 * c ^ (-(8 / 3 : ℝ)) := by rw [hc83]
  refine ⟨hû1_a1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    hAi_sq.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-- info: 'FormalResearch.SignUncertainty.win_zero_a1_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_zero_a1_err

end FormalResearch.SignUncertainty
