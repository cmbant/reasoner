/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpInnerRed

/-!
# Derivative bounds of `(fct:RI-bounds)` for `fct:warp-asymp` (1)

Paper I (`constant_terms_five.tex`), Proposition FCT.5 (1), Step 3:
proves uniform `O(c^{-1/2})` error bounds for the normalized chart partial derivatives of `I_ε`
over admissible pairs `(L₁, α)`:
- `fctWarpI_derivL_at_a1_err`: `‖(N₀ / u_L) ∂_{L₁} I_ε(L₁, α) - i G₀'(a₁)‖ ≤ C_D c^{-1/2}`
- `fctWarpI_derivAlpha_at_a1_err`: `‖c^{2/3} N₀ ∂_α I_ε(L₁, α) + i c₂* G₀''(a₁)‖ ≤ C_D c^{-1/2}`.

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff
open FormalResearch.CohnElkies
open FormalResearch.Special
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

private lemma adm_mu_symCls {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ (C_μ c₀ : ℝ), 0 ≤ C_μ ∧ max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 α →
        FctSymClsOn (Icc 0 (fctUc c)) 8 10 C_μ ((concreteInnerFamily K4 ε).mu c L1 α) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  have hB3 := concreteInnerB3 (K4 := K4) (ε := ε) hK4
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ hB3.choose_spec.choose ≤ c ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.5 ∧
      c ^ (-(4 / 3 : ℝ)) ≤ 1 ∧ c ^ (-(7 / 6 : ℝ)) ≤ 1 := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop hB3.choose_spec.choose)
        (Eventually.and ?_ (Eventually.and ?_ ?_)))
    · have h0 : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)).eventually (Iic_mem_nhds zero_lt_one)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  let C_μ : ℝ := |hB3.choose| + 1 + 9 * 2 ^ 8
  refine ⟨C_μ, max cbase c₀, by positivity, le_max_left _ _, fun {c L1 α} hc hadm => ?_⟩
  obtain ⟨hcbase, hc3, hV0_small, hc43, hc76⟩ := hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hc0 : 0 < c := hfacts.1
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hDi := uniqueDiffOn_Ici (0 : ℝ)
  have hb3 := hB3.choose_spec.choose_spec c hc3 L1 α hadm
  set V := concreteInnerV K4 ε c L1 α
  have hδμ : FctSymClsOn (Icc 0 (fctUc c)) 8 10 |hB3.choose|
      (fun u => (concreteInnerFamily K4 ε).mu c L1 α u - 1 -
        ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)) := by
    refine hb3.mono_B Icc_subset_Ici_self ?_
    calc hB3.choose * c ^ (-(4 / 3 : ℝ)) ≤ |hB3.choose| * 1 := by
          gcongr; exact le_abs_self _
      _ = |hB3.choose| := mul_one _
  have h1_on : FctSymClsOn (Icc 0 (fctUc c)) 8 10 1 (fun _ : ℝ => (1 : ℂ)) :=
    ((one_symCls 8).mono_set Icc_subset_Ici_self hDu hDi).mono_p Icc_subset_Ici_self
      (by positivity) (by norm_num : (0 : ℝ) ≤ 10)
  have hc2_bd : |(concreteInnerFamily K4 ε).c2 c L1 α| ≤ 9 := by
    dsimp only [concreteInnerFamily]
    have hV0_abs := abs_le.mp (hfacts.2.2.2.2.2.2.2.2.2.2.2.trans hV0_small)
    have hτs_lt : (12 / π ^ 2) ^ (1 / 3 : ℝ) < 2 := by
      have hpi2 : (9 : ℝ) < π ^ 2 := by nlinarith only [Real.pi_gt_three]
      have h12 : (12 : ℝ) / π ^ 2 < 8 := by rw [div_lt_iff₀ (by positivity)]; linarith
      calc (12 / π ^ 2) ^ (1 / 3 : ℝ) < (8 : ℝ) ^ (1 / 3 : ℝ) :=
            Real.rpow_lt_rpow (by positivity) h12 (by norm_num)
        _ = 2 := by
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) from by norm_num, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num)]; norm_num
    have hV0_2 : |V 0| ≤ 3 := by
      have hτs0 : 0 ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := by positivity
      rw [abs_le]; constructor <;> linarith only [hV0_abs.1, hV0_abs.2, hτs_lt, hτs0]
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hV0_eq : (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), 0) = V 0 :=
      (hfacts.2.2.2.2.2.2.2.2.2.1.2 0 ⟨le_rfl, by norm_num⟩).symm
    change |((2 : ℝ) ^ (-(4 / 3 : ℝ))) * ((concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), 0)) ^ 2| ≤ 9
    rw [hV0_eq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _), abs_sq, ← sq_abs (V 0)]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |V 0| ^ 2 ≤ 1 * 3 ^ 2 := by gcongr
      _ = 9 := by norm_num
  let c2fac : ℝ := c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α
  have hc2fac_bd : |c2fac| ≤ 9 := by
    dsimp only [c2fac]
    have h76 : |α| * c ^ (-(2 / 3 : ℝ)) ≤ 1 := by
      have hpow : c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(7 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc |α| * c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
            gcongr; exact hadm.2.2.2
        _ = c ^ (-(7 / 6 : ℝ)) := hpow
        _ ≤ 1 := hc76
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    calc c ^ (-(2 / 3 : ℝ)) * |α| * |(concreteInnerFamily K4 ε).c2 c L1 α|
        = (|α| * c ^ (-(2 / 3 : ℝ))) * |(concreteInnerFamily K4 ε).c2 c L1 α| := by ring
      _ ≤ 1 * 9 := mul_le_mul h76 hc2_bd (abs_nonneg _) zero_le_one
      _ = 9 := one_mul 9
  have hq_on : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (9 * 2 ^ 8)
      (fun u => ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)) := by
    have heq : (fun u : ℝ => ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)) =
        fun u : ℝ => ((c2fac : ℝ) : ℂ) * (u : ℂ) ^ 2 := by ext u; dsimp only [c2fac]; push_cast; ring
    rw [heq]
    have hsm := (((sq_symCls 8).mono_set Icc_subset_Ici_self hDu hDi).mono_p Icc_subset_Ici_self
      (by positivity) (by norm_num : (2 : ℝ) ≤ 10)).const_mul hDu ((c2fac : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at hsm
    exact hsm.mono_B Icc_subset_Ici_self (by
      calc |c2fac| * 2 ^ 8 ≤ 9 * 2 ^ 8 := by gcongr)
  exact ((hδμ.add hDu h1_on).add hDu hq_on).congr hDu (fun u _ => by ring)

lemma fctWarpI_derivL_at_a1_err {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ (C_D c₀ : ℝ), 0 ≤ C_D ∧ max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 α →
        let S := concreteBoxS K4 ε c
        let uL := -fctKappa c * S.V ((concreteEll1 ε c L1, 1, α), S.A (concreteEll1 ε c L1, 1, α))
        ‖((warpN0 c / uL : ℝ) : ℂ) *
            (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c L1 α τ) -
          Complex.I * deriv fctG0 (airyZero 1)‖ ≤
          C_D * c ^ (-(1 / 2 : ℝ)) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  obtain ⟨c_in, hc_in_base, hin_eq⟩ := fctInner_warpI_derivL_in_eq (K4 := K4) (ε := ε) hK4
  obtain ⟨C_sym, c_sym, hCsym0, hc_sym_base, hsym_err⟩ := fctS_pow_chi_mu_err (K4 := K4) (ε := ε) hK4
  obtain ⟨C_μ, c_μ, hCμ0, hc_μ_base, hmu_cls⟩ := adm_mu_symCls (K4 := K4) (ε := ε) hK4
  have hB4 := concreteInnerB4 (K4 := K4) (ε := ε)
  obtain ⟨C_χ, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  have hA13 := fctInnerSymbolsA (M := 3) (n := 8) (p := 13) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C_sh, c_sh, hCsh0, _, hsh⟩ := fctWarpOuter_shoulder_bounds
  obtain ⟨C_g, hCg0, hg_lip⟩ := fctG0_lipschitz_near_airyZero
  set C_N0 : ℝ := 12 * (2 : ℝ) ^ (1 / 3 : ℝ) / (π ^ 2 * Real.sqrt 1.06)
  set C_uL : ℝ := 2 ^ (2 / 3 : ℝ) * C_N0
  have hCuL0 : 0 ≤ C_uL := by positivity
  have hCa13_nn : 0 ≤ hA13.choose := hA13.choose_spec.1
  let B_eA : ℝ := 2 ^ 8 * (|C_χ| + 1) * (2 ^ 8 * |hB4.choose| * C_μ)
  let C_eA : ℝ := 2 * hA13.choose * B_eA
  let C_g1 : ℝ := ‖deriv fctG0 (airyZero 1)‖
  let C_D : ℝ := 4 * C_sym + C_eA + pbcV * pbC0 * C_g1 + (pbcV * pbC0 + 2) * C_g + C_uL * C_sh
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ c_in ≤ c ∧ c_sym ≤ c ∧ c_μ ≤ c ∧
      hB4.choose_spec.choose ≤ c ∧ c_χ ≤ c ∧ c_sh ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3 ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.06 ∧
      c ^ (-(7 / 6 : ℝ)) ≤ 0.5 ∧
      c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) ∧
      c ^ (-(7 / 6 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) ∧
      c ^ (-(23 / 8 : ℝ)) ≤ 1 ∧
      1 ≤ c := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop c_in)
        (Eventually.and (eventually_ge_atTop c_sym)
          (Eventually.and (eventually_ge_atTop c_μ)
            (Eventually.and (eventually_ge_atTop hB4.choose_spec.choose)
              (Eventually.and (eventually_ge_atTop c_χ)
                (Eventually.and (eventually_ge_atTop c_sh)
                  (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_
                    (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_
                      (Eventually.and ?_ (eventually_ge_atTop 1))))))))))))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1)
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1e-3))
    · have h0 : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.06))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).eventually
        (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc1
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc1
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 23 / 8)).eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_D, max cbase c₀, by have := pbcV_nonneg; have := pbC0_nonneg; positivity,
    le_max_left _ _, fun {c L1 α} hc hadm => ?_⟩
  obtain ⟨hcbase, hcin, hcsym, hcμ, hc4, hcχ, hcsh, hτD, hKV, hV0_06, hc76, hc23_12, hc76_12, hc238, hc1⟩ :=
    hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hvalid := hadm.1
  have hε := hvalid.2.1
  have hc0 := hfacts.1
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hK4t : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 := hvalid.2.2.2.2
  have hell : concreteEll1 ε c L1 ∈ Ioo (0 : ℝ) 2.55 := hfacts.2.2.2.2.1
  have hα_bd : |α| ≤ c ^ (-(1 / 2 : ℝ)) := hadm.2.2.2
  have hα_2τ : |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
    rw [hfacts.2.2.1]; linarith only [hα_bd, Real.rpow_nonneg hc0.le (-(1 / 2 : ℝ))]
  have hsh_bds := hsh hK4 hε hcsh hτD hK4t hell hα_2τ
  have hint_full := integrableOn_fctWarpIntegrandDerivL hK4 hε hc1 hτD L1 α
  have hint_out := hsh_bds.2.1
  have hint_in : IntegrableOn (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) *
      fctWarpIntegrandDerivL K4 ε c L1 α τ) (Ioi 0) := by
    have heq : (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ) =
        fun τ => fctWarpIntegrandDerivL K4 ε c L1 α τ -
          ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ := by
      ext τ; push_cast; ring
    rw [heq]; exact hint_full.sub hint_out
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L1 α
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  set uL := -fctKappa c * S.V ((concreteEll1 ε c L1, 1, α), S.A (concreteEll1 ε c L1, 1, α))
  have hsplit : Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c L1 α τ =
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ) +
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ) := by
    rw [← mul_add, ← MeasureTheory.integral_add hint_in hint_out]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    push_cast; ring
  have hin := hin_eq hcin hadm
  dsimp only at hin
  -- Bounds on `nu`, `uL`, `N0/uL`
  have hnu := warpNu_sub_one_le (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc0
    hfacts.2.2.2.2.2.2.2.2.2.2.2 (hV0_06.trans (by norm_num))
  have hVA_ge1 : 1 ≤ S.V ((concreteEll1 ε c L1, 1, α), S.A (concreteEll1 ε c L1, 1, α)) := by
    have htau := (abs_le.mp (hfacts.2.2.2.2.2.2.2.2.2.2.1.trans hV0_06)).1
    have hwg : (1.06 : ℝ) ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := warpTauStar_ge
    linarith only [htau, hwg]
  have huL_ge : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) ≤ |uL| := by
    dsimp only [uL, fctKappa]
    rw [abs_mul, abs_neg, abs_of_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hc0 _)),
      abs_of_pos (by linarith only [hVA_ge1])]
    exact le_mul_of_one_le_right (by positivity) hVA_ge1
  have hN0_bd : |warpN0 c| ≤ C_N0 * c ^ (1 / 6 : ℝ) := by
    unfold warpN0
    have hws : Real.sqrt 1.06 ≤ Real.sqrt warpTauStar := Real.sqrt_le_sqrt warpTauStar_ge
    have hc16_pos : 0 ≤ c ^ (1 / 6 : ℝ) := Real.rpow_nonneg hc0.le _
    rw [abs_of_nonneg (by positivity)]
    calc 12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) / (π ^ 2 * Real.sqrt warpTauStar)
        ≤ 12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) / (π ^ 2 * Real.sqrt 1.06) := by gcongr
      _ = C_N0 * c ^ (1 / 6 : ℝ) := by dsimp only [C_N0]; ring
  have hN0_uL : |warpN0 c / uL| ≤ C_uL * c ^ (-(1 / 2 : ℝ)) := by
    rw [abs_div]
    have h2pos : 0 < (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) := by positivity
    have hpow : c ^ (1 / 6 : ℝ) / c ^ (2 / 3 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    have h2inv : ((2 : ℝ) ^ (-(2 / 3 : ℝ)))⁻¹ = (2 : ℝ) ^ (2 / 3 : ℝ) := by
      rw [Real.rpow_neg (by norm_num), inv_inv]
    calc |warpN0 c| / |uL|
        ≤ (C_N0 * c ^ (1 / 6 : ℝ)) / ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) :=
          div_le_div₀ (by positivity) hN0_bd h2pos huL_ge
      _ = ((2 : ℝ) ^ (-(2 / 3 : ℝ)))⁻¹ * C_N0 * (c ^ (1 / 6 : ℝ) / c ^ (2 / 3 : ℝ)) := by ring
      _ = C_uL * c ^ (-(1 / 2 : ℝ)) := by rw [h2inv, hpow]
  have hsh_prod : ‖((warpN0 c / uL : ℝ) : ℂ) *
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
        fctWarpIntegrandDerivL K4 ε c L1 α τ)‖ ≤ C_uL * C_sh * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, one_mul, Real.norm_eq_abs]
    calc |warpN0 c / uL| * ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
            fctWarpIntegrandDerivL K4 ε c L1 α τ‖
        ≤ (C_uL * c ^ (-(1 / 2 : ℝ))) * (C_sh * c ^ (-(23 / 8 : ℝ))) :=
          mul_le_mul hN0_uL hsh_bds.2.2.2.2.1 (norm_nonneg _) (by positivity)
      _ = C_uL * C_sh * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(23 / 8 : ℝ))) := by ring
      _ ≤ C_uL * C_sh * (c ^ (-(1 / 2 : ℝ)) * 1) := by gcongr
      _ = C_uL * C_sh * c ^ (-(1 / 2 : ℝ)) := by ring
  -- Inner `fctS` splitting
  have hVjets := hfacts.2.2.2.2.2.2.2.2.2.1.1
  have hb2 := hB2 c hcχ _ hVjets
  have hb4 := hB4.choose_spec.choose_spec c hc4 L1 α hadm
  have hmu := hmu_cls hcμ hadm
  have hb2_chi : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (|C_χ| + 1)
      (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ)) :=
    (hb2.2.2.1).mono_B Icc_subset_Ici_self (by linarith [le_abs_self C_χ])
  have heA_sym : FctSymCls 8 13 (B_eA * c ^ (-(2 / 3 : ℝ)))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u))) := by
    have heA_B : FctSymClsOn (Icc 0 (fctUc c)) 8 3 (|hB4.choose| * c ^ (-(2 / 3 : ℝ)))
        ((concreteInnerFamily K4 ε).eA c L1 α) :=
      hb4.2.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hc0.le _))
    have hprod := (hb2_chi.mul Icc_subset_Ici_self hDu (heA_B.mul Icc_subset_Ici_self hDu hmu)).mono_p
      Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + (3 + 10) ≤ 13)
    have h1 := extUc_mem_symCls hc1 (by positivity) hprod (fun u hu => by rw [hb2.1 u hu]; simp)
    exact h1.mono_B Subset.rfl (le_of_eq (by dsimp only [B_eA]; ring))
  have hû3 : |û| ≤ 3 := by
    have ha1 := airyZero_one
    have hsub := abs_le.mp (hadm.2.2.1.trans hc76)
    rw [abs_le]; constructor <;> linarith only [ha1.1, ha1.2, hsub.1, hsub.2]
  obtain ⟨⟨LeA, hLeA⟩, hbd_eA, _⟩ :=
    hA13.choose_spec.2 û (B_eA * c ^ (-(2 / 3 : ℝ))) _ hû3 (by positivity) heA_sym
  -- `fctS` of `(u : ℂ) * χ u * μ u` via `fctS_pow_chi_mu_err (k := 1)`
  have hsym1 := hsym_err (k := 1) hcsym (by norm_num) hadm
  dsimp only at hsym1
  simp only [pow_one] at hsym1
  have hmono1 := fctInnerSymbolsMonomial 1 û
  have hg0_eq : (fun w : ℝ => fctS w (fun _ => (1 : ℂ))) = fctG0 := funext fun w => (fctInnerSymbolsG0 w).fctS_eq
  rw [hg0_eq] at hmono1
  simp only [pow_one, iteratedDeriv_one] at hmono1
  rw [hmono1.fctS_eq] at hsym1
  -- Symbol class for `extUc c (u * χ * μ)` to apply `fctSLimit` linearity
  have hA11 := fctInnerSymbolsA (M := 3) (n := 8) (p := 11) (by norm_num) (by norm_num) (by norm_num)
  have hu_on : FctSymClsOn (Icc 0 (fctUc c)) 8 1 1 (fun u : ℝ => (u : ℂ)) :=
    (id_symCls 8).mono_set Icc_subset_Ici_self hDu (uniqueDiffOn_Ici 0)
  have humu_sym : FctSymCls 8 11 (2 ^ 8 * (|C_χ| + 1) * (2 ^ 8 * 1 * C_μ))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u))) := by
    have hprod := (hb2_chi.mul Icc_subset_Ici_self hDu (hu_on.mul Icc_subset_Ici_self hDu hmu)).mono_p
      Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + (1 + 10) ≤ 11)
    exact extUc_mem_symCls hc1 (by positivity) hprod (fun u hu => by rw [hb2.1 u hu]; simp)
  obtain ⟨⟨Lumu, hLumu⟩, _, _⟩ := hA11.choose_spec.2 û _ _ hû3 (by positivity) humu_sym
  have humu_cmul : FctSymCls 8 13 (‖-Complex.I‖ * (2 ^ 8 * (|C_χ| + 1) * (2 ^ 8 * 1 * C_μ)))
      (fun u => (-Complex.I) * extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u)) u) :=
    (humu_sym.mono_p Subset.rfl (by positivity) (by norm_num : (11 : ℝ) ≤ 13)).const_mul
      (uniqueDiffOn_Ici 0) (-Complex.I)
  have hs_umu : FctSLimit û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u)))
      (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u)))) := by
    rw [hLumu.fctS_eq]; exact hLumu
  have hs_eA : FctSLimit û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))
      (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))) := by
    rw [hLeA.fctS_eq]; exact hLeA
  have hsum_lim := fctSLimit_add (by positivity) (by positivity) humu_cmul heA_sym
    (fctSLimit_const_mul (-Complex.I) hs_umu) hs_eA
  have hfn_eq : (fun u : ℝ => (-Complex.I) * extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u)) u +
      extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)) u) =
      extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (-(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u) *
        (concreteInnerFamily K4 ε).mu c L1 α u) := by
    ext u; rcases le_or_gt u (fctUc c) with hle | hgt
    · simp only [extUc, hle, ↓reduceIte]; ring
    · simp only [extUc_zero_of_gt _ hgt, mul_zero, add_zero]
  rw [hfn_eq] at hsum_lim
  have hmu_order : (fun u : ℝ => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
      ((u : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u)) =
      fun u : ℝ => (u : ℂ) * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u := by
    ext u; ring
  have hS_split : fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (-(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) =
      (-Complex.I) * fctS û (extUc c (fun u => (u : ℂ) * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) +
      fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u))) := by
    rw [hsum_lim.fctS_eq, hmu_order]
  -- Assemble all four error pieces
  have hsym_12 : ‖fctS û (extUc c (fun u => (u : ℂ) * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) - Complex.I * deriv fctG0 û‖ ≤
      2 * C_sym * c ^ (-(1 / 2 : ℝ)) := by
    calc ‖_‖ ≤ C_sym * (c ^ (-(4 / 3 : ℝ)) + |α| * c ^ (-(2 / 3 : ℝ))) := hsym1
      _ ≤ C_sym * (c ^ (-(1 / 2 : ℝ)) + c ^ (-(7 / 6 : ℝ))) := by
          have hc43 : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
          have hαc : |α| * c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) := by
            have hpow : c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(7 / 6 : ℝ)) := by
              rw [← Real.rpow_add hc0]; norm_num
            calc |α| * c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by gcongr
              _ = c ^ (-(7 / 6 : ℝ)) := hpow
          gcongr
      _ ≤ C_sym * (c ^ (-(1 / 2 : ℝ)) + c ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = 2 * C_sym * c ^ (-(1 / 2 : ℝ)) := by ring
  have heA_12 : ‖fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))‖ ≤
      (C_eA / 2) * c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [C_eA]
    calc ‖_‖ ≤ hA13.choose * (B_eA * c ^ (-(2 / 3 : ℝ))) := hbd_eA
      _ ≤ hA13.choose * (B_eA * c ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = (2 * hA13.choose * B_eA / 2) * c ^ (-(1 / 2 : ℝ)) := by ring
  have hg_lip1 : ‖deriv fctG0 û - deriv fctG0 (airyZero 1)‖ ≤ C_g * c ^ (-(1 / 2 : ℝ)) := by
    have h1 := hg_lip (k := 1) (by norm_num) û (hadm.2.2.1.trans (hc76.trans (by norm_num)))
    simp only [iteratedDeriv_one] at h1
    calc ‖deriv fctG0 û - deriv fctG0 (airyZero 1)‖ ≤ C_g * |û - airyZero 1| := h1
      _ ≤ C_g * c ^ (-(7 / 6 : ℝ)) := by gcongr; exact hadm.2.2.1
      _ ≤ C_g * c ^ (-(1 / 2 : ℝ)) := by gcongr
  have hg_norm : ‖deriv fctG0 û‖ ≤ C_g1 + C_g := by
    have htr := norm_sub_le (deriv fctG0 û - deriv fctG0 (airyZero 1)) (-deriv fctG0 (airyZero 1))
    have h1 : ‖deriv fctG0 û - deriv fctG0 (airyZero 1)‖ ≤ C_g := by
      have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      calc _ ≤ C_g * c ^ (-(1 / 2 : ℝ)) := hg_lip1
        _ ≤ C_g * 1 := by gcongr
        _ = C_g := mul_one _
    calc ‖deriv fctG0 û‖ = ‖(deriv fctG0 û - deriv fctG0 (airyZero 1)) + deriv fctG0 (airyZero 1)‖ := by ring_nf
      _ ≤ ‖deriv fctG0 û - deriv fctG0 (airyZero 1)‖ + ‖deriv fctG0 (airyZero 1)‖ := norm_add_le _ _
      _ ≤ C_g + C_g1 := add_le_add h1 le_rfl
      _ = C_g1 + C_g := add_comm _ _
  have hsub_eq : ((warpN0 c / uL : ℝ) : ℂ) *
      (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c L1 α τ) -
      Complex.I * deriv fctG0 (airyZero 1) =
      Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
        ((-Complex.I) * (fctS û (extUc c (fun u => (u : ℂ) * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
          (concreteInnerFamily K4 ε).mu c L1 α u)) - Complex.I * deriv fctG0 û)) +
      Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
        fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
          ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u))) +
      ((warpNu K4 ε c L1 α - 1 : ℝ) : ℂ) * (Complex.I * deriv fctG0 û) +
      Complex.I * (deriv fctG0 û - deriv fctG0 (airyZero 1)) +
      ((warpN0 c / uL : ℝ) : ℂ) *
        (Complex.I * ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
          fctWarpIntegrandDerivL K4 ε c L1 α τ) := by
    rw [hsplit, mul_add, ← mul_assoc ((warpN0 c / uL : ℝ) : ℂ) Complex.I _, hin, hS_split]
    have hI2 : (-Complex.I) * Complex.I = (1 : ℂ) := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    push_cast
    linear_combination Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) * deriv fctG0 û * hI2
  dsimp only
  rw [hsub_eq]
  have h_nu1 : |warpNu K4 ε c L1 α - 1| * ‖deriv fctG0 û‖ ≤
      (pbcV * pbC0 * C_g1 + pbcV * pbC0 * C_g) * c ^ (-(1 / 2 : ℝ)) := by
    calc |warpNu K4 ε c L1 α - 1| * ‖deriv fctG0 û‖
        ≤ (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) * (C_g1 + C_g) :=
          mul_le_mul hnu.1 hg_norm (norm_nonneg _) (mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) (by positivity))
      _ = (pbcV * pbC0 * C_g1 + pbcV * pbC0 * C_g) * c ^ (-(1 / 2 : ℝ)) := by ring
  have ht1 : ‖Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
      ((-Complex.I) * (fctS û (extUc c (fun u => (u : ℂ) * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) - Complex.I * deriv fctG0 û))‖ ≤
      4 * C_sym * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_neg, Complex.norm_I, one_mul]
    calc |warpNu K4 ε c L1 α| * ‖_‖ ≤ 2 * (2 * C_sym * c ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hnu.2 hsym_12 (norm_nonneg _) (by norm_num)
      _ = 4 * C_sym * c ^ (-(1 / 2 : ℝ)) := by ring
  have ht2 : ‖Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
      fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eA c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))‖ ≤
      C_eA * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |warpNu K4 ε c L1 α| * ‖_‖ ≤ 2 * ((C_eA / 2) * c ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hnu.2 heA_12 (norm_nonneg _) (by norm_num)
      _ = C_eA * c ^ (-(1 / 2 : ℝ)) := by ring
  have ht3 : ‖((warpNu K4 ε c L1 α - 1 : ℝ) : ℂ) * (Complex.I * deriv fctG0 û)‖ ≤
      (pbcV * pbC0 * C_g1 + pbcV * pbC0 * C_g) * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, one_mul]
    exact h_nu1
  have ht4 : ‖Complex.I * (deriv fctG0 û - deriv fctG0 (airyZero 1))‖ ≤ C_g * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact hg_lip1
  calc ‖_ + _ + _ + _ + _‖
      ≤ ‖_‖ + ‖_‖ + ‖_‖ + ‖_‖ + ‖_‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ 4 * C_sym * c ^ (-(1 / 2 : ℝ)) + C_eA * c ^ (-(1 / 2 : ℝ)) +
          (pbcV * pbC0 * C_g1 + pbcV * pbC0 * C_g) * c ^ (-(1 / 2 : ℝ)) +
          C_g * c ^ (-(1 / 2 : ℝ)) + C_uL * C_sh * c ^ (-(1 / 2 : ℝ)) :=
        add_le_add (add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4) hsh_prod
    _ ≤ C_D * c ^ (-(1 / 2 : ℝ)) := by
        have hpos : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
        have hnn : 0 ≤ pbcV * pbC0 * C_g := mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) hCg0
        dsimp only [C_D]; nlinarith only [hpos, hnn, hCg0]

lemma fctWarpI_derivAlpha_at_a1_err {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ (C_D c₀ : ℝ), 0 ≤ C_D ∧ max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 α →
        ‖((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
            (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) -
          (-Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 (airyZero 1))‖ ≤
          C_D * c ^ (-(1 / 2 : ℝ)) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  obtain ⟨c_in, hc_in_base, hin_eq⟩ := fctInner_warpI_derivAlpha_in_eq (K4 := K4) (ε := ε) hK4
  obtain ⟨C_sym, c_sym, hCsym0, hc_sym_base, hsym_err⟩ := fctS_pow_chi_mu_err (K4 := K4) (ε := ε) hK4
  obtain ⟨C_μ, c_μ, hCμ0, hc_μ_base, hmu_cls⟩ := adm_mu_symCls (K4 := K4) (ε := ε) hK4
  have hB4 := concreteInnerB4 (K4 := K4) (ε := ε)
  obtain ⟨C_χ, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  have hA21 := fctInnerSymbolsA (M := 3) (n := 8) (p := 21) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C_sh, c_sh, hCsh0, _, hsh⟩ := fctWarpOuter_shoulder_bounds
  obtain ⟨C_g, hCg0, hg_lip⟩ := fctG0_lipschitz_near_airyZero
  set C_N0 : ℝ := 12 * (2 : ℝ) ^ (1 / 3 : ℝ) / (π ^ 2 * Real.sqrt 1.06)
  have hCN0 : 0 ≤ C_N0 := by positivity
  have hc2s0 : 0 ≤ warpC2Star := by unfold warpC2Star warpTauStar; positivity
  let B_eB : ℝ := 2 ^ 8 * (|C_χ| + 1) * (2 ^ 8 * |hB4.choose| * C_μ)
  let C_eB : ℝ := 2 * hA21.choose * B_eB
  let C_g2 : ℝ := ‖iteratedDeriv 2 fctG0 (airyZero 1)‖
  let C_D : ℝ := 4 * warpC2Star * C_sym + C_eB +
    pbcV * pbC0 * warpC2Star * C_g2 + (pbcV * pbC0 + 1) * warpC2Star * C_g + C_N0 * C_sh
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ c_in ≤ c ∧ c_sym ≤ c ∧ c_μ ≤ c ∧
      hB4.choose_spec.choose ≤ c ∧ c_χ ≤ c ∧ c_sh ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3 ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.5 ∧
      c ^ (-(7 / 6 : ℝ)) ≤ 0.5 ∧
      c ^ (-(7 / 6 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) ∧
      c ^ (-(61 / 24 : ℝ)) ≤ 1 ∧
      1 ≤ c := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop c_in)
        (Eventually.and (eventually_ge_atTop c_sym)
          (Eventually.and (eventually_ge_atTop c_μ)
            (Eventually.and (eventually_ge_atTop hB4.choose_spec.choose)
              (Eventually.and (eventually_ge_atTop c_χ)
                (Eventually.and (eventually_ge_atTop c_sh)
                  (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_
                    (Eventually.and ?_ (Eventually.and ?_
                      (Eventually.and ?_ (eventually_ge_atTop 1)))))))))))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1)
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1e-3))
    · have h0 : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).eventually
        (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc1
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 61 / 24)).eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_D, max cbase c₀,
    by have := pbcV_nonneg; have := pbC0_nonneg; have := hA21.choose_spec.1; positivity,
    le_max_left _ _, fun {c L1 α} hc hadm => ?_⟩
  obtain ⟨hcbase, hcin, hcsym, hcμ, hc4, hcχ, hcsh, hτD, hKV, hV0_small, hc76, hc76_12, hc61, hc1⟩ :=
    hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hvalid := hadm.1
  have hε := hvalid.2.1
  have hc0 := hfacts.1
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hK4t : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 := hvalid.2.2.2.2
  have hell : concreteEll1 ε c L1 ∈ Ioo (0 : ℝ) 2.55 := hfacts.2.2.2.2.1
  have hα_bd : |α| ≤ c ^ (-(1 / 2 : ℝ)) := hadm.2.2.2
  have hα_2τ : |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
    rw [hfacts.2.2.1]; linarith only [hα_bd, Real.rpow_nonneg hc0.le (-(1 / 2 : ℝ))]
  have hsh_bds := hsh hK4 hε hcsh hτD hK4t hell hα_2τ
  have hint_full := integrableOn_fctWarpIntegrandDerivAlpha hK4 hε hc1 hτD L1 α
  have hint_out := hsh_bds.2.2.1
  have hint_in : IntegrableOn (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) *
      fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) (Ioi 0) := by
    have heq : (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) =
        fun τ => fctWarpIntegrandDerivAlpha K4 ε c L1 α τ -
          ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ := by
      ext τ; push_cast; ring
    rw [heq]; exact hint_full.sub hint_out
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L1 α
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  have hsplit : Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 α τ =
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) +
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) := by
    rw [← mul_add, ← MeasureTheory.integral_add hint_in hint_out]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    push_cast; ring
  have hin := hin_eq hcin hadm
  dsimp only at hin
  have hnu := warpNu_sub_one_le (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc0
    hfacts.2.2.2.2.2.2.2.2.2.2.2 hV0_small
  have hN0_bd : |c ^ (2 / 3 : ℝ) * warpN0 c| ≤ C_N0 * c ^ (5 / 6 : ℝ) := by
    unfold warpN0
    have hws : Real.sqrt 1.06 ≤ Real.sqrt warpTauStar := Real.sqrt_le_sqrt warpTauStar_ge
    have hc16_pos : 0 ≤ c ^ (1 / 6 : ℝ) := Real.rpow_nonneg hc0.le _
    have hc23_pos : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    have hpow : c ^ (2 / 3 : ℝ) * c ^ (1 / 6 : ℝ) = c ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [abs_of_nonneg (by positivity)]
    calc c ^ (2 / 3 : ℝ) * (12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) / (π ^ 2 * Real.sqrt warpTauStar))
        ≤ c ^ (2 / 3 : ℝ) * (12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) / (π ^ 2 * Real.sqrt 1.06)) := by gcongr
      _ = C_N0 * (c ^ (2 / 3 : ℝ) * c ^ (1 / 6 : ℝ)) := by dsimp only [C_N0]; ring
      _ = C_N0 * c ^ (5 / 6 : ℝ) := by rw [hpow]
  have hsh_prod : ‖((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
        fctWarpIntegrandDerivAlpha K4 ε c L1 α τ)‖ ≤ C_N0 * C_sh * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, one_mul, Real.norm_eq_abs]
    have hpow : c ^ (5 / 6 : ℝ) * c ^ (-(31 / 8 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c ^ (-(61 / 24 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    calc |c ^ (2 / 3 : ℝ) * warpN0 c| * ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
            fctWarpIntegrandDerivAlpha K4 ε c L1 α τ‖
        ≤ (C_N0 * c ^ (5 / 6 : ℝ)) * (C_sh * c ^ (-(31 / 8 : ℝ))) :=
          mul_le_mul hN0_bd hsh_bds.2.2.2.2.2 (norm_nonneg _) (by positivity)
      _ = C_N0 * C_sh * (c ^ (5 / 6 : ℝ) * c ^ (-(31 / 8 : ℝ))) := by ring
      _ = C_N0 * C_sh * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(61 / 24 : ℝ))) := by rw [hpow]
      _ ≤ C_N0 * C_sh * (c ^ (-(1 / 2 : ℝ)) * 1) := by gcongr
      _ = C_N0 * C_sh * c ^ (-(1 / 2 : ℝ)) := by ring
  have hVjets := hfacts.2.2.2.2.2.2.2.2.2.1.1
  have hb2 := hB2 c hcχ _ hVjets
  have hb4 := hB4.choose_spec.choose_spec c hc4 L1 α hadm
  have hmu := hmu_cls hcμ hadm
  have hb2_chi : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (|C_χ| + 1)
      (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ)) :=
    (hb2.2.2.1).mono_B Icc_subset_Ici_self (by linarith [le_abs_self C_χ])
  have heB_sym : FctSymCls 8 21 (B_eB * c ^ (-(1 / 2 : ℝ)))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u))) := by
    have heB_B : FctSymClsOn (Icc 0 (fctUc c)) 8 11 (|hB4.choose| * c ^ (-(1 / 2 : ℝ)))
        ((concreteInnerFamily K4 ε).eB c L1 α) :=
      hb4.1.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hc0.le _))
    have hprod := (hb2_chi.mul Icc_subset_Ici_self hDu (heB_B.mul Icc_subset_Ici_self hDu hmu)).mono_p
      Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + (11 + 10) ≤ 21)
    have h1 := extUc_mem_symCls hc1 (by positivity) hprod (fun u hu => by rw [hb2.1 u hu]; simp)
    exact h1.mono_B Subset.rfl (le_of_eq (by dsimp only [B_eB]; ring))
  have hû3 : |û| ≤ 3 := by
    have ha1 := airyZero_one
    have hsub := abs_le.mp (hadm.2.2.1.trans hc76)
    rw [abs_le]; constructor <;> linarith only [ha1.1, ha1.2, hsub.1, hsub.2]
  obtain ⟨⟨LeB, hLeB⟩, hbd_eB, _⟩ :=
    hA21.choose_spec.2 û (B_eB * c ^ (-(1 / 2 : ℝ))) _ hû3 (by positivity) heB_sym
  have hsym2 := hsym_err (k := 2) hcsym (by norm_num) hadm
  dsimp only at hsym2
  have hmono2 := fctInnerSymbolsMonomial 2 û
  have hg0_eq : (fun w : ℝ => fctS w (fun _ => (1 : ℂ))) = fctG0 := funext fun w => (fctInnerSymbolsG0 w).fctS_eq
  rw [hg0_eq] at hmono2
  rw [hmono2.fctS_eq] at hsym2
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  rw [hI2, neg_one_mul] at hsym2
  -- Symbol class for `extUc c (u^2 * χ * μ)`
  have hA12 := fctInnerSymbolsA (M := 3) (n := 8) (p := 12) (by norm_num) (by norm_num) (by norm_num)
  have hu2_on : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (2 ^ 8) (fun u : ℝ => (u : ℂ) ^ 2) :=
    (sq_symCls 8).mono_set Icc_subset_Ici_self hDu (uniqueDiffOn_Ici 0)
  have hu2mu_sym : FctSymCls 8 12 (2 ^ 8 * (|C_χ| + 1) * (2 ^ 8 * 2 ^ 8 * C_μ))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ 2 * (concreteInnerFamily K4 ε).mu c L1 α u))) := by
    have hprod := (hb2_chi.mul Icc_subset_Ici_self hDu (hu2_on.mul Icc_subset_Ici_self hDu hmu)).mono_p
      Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + (2 + 10) ≤ 12)
    exact extUc_mem_symCls hc1 (by positivity) hprod (fun u hu => by rw [hb2.1 u hu]; simp)
  obtain ⟨⟨Lu2mu, hLu2mu⟩, _, _⟩ := hA12.choose_spec.2 û _ _ hû3 (by positivity) hu2mu_sym
  have hu2mu_cmul : FctSymCls 8 21 (‖(warpC2Star : ℂ)‖ * (2 ^ 8 * (|C_χ| + 1) * (2 ^ 8 * 2 ^ 8 * C_μ)))
      (fun u => ((warpC2Star : ℝ) : ℂ) * extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ 2 * (concreteInnerFamily K4 ε).mu c L1 α u)) u) :=
    (hu2mu_sym.mono_p Subset.rfl (by positivity) (by norm_num : (12 : ℝ) ≤ 21)).const_mul
      (uniqueDiffOn_Ici 0) (warpC2Star : ℂ)
  have hs_u2mu : FctSLimit û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ 2 * (concreteInnerFamily K4 ε).mu c L1 α u)))
      (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ 2 * (concreteInnerFamily K4 ε).mu c L1 α u)))) := by
    rw [hLu2mu.fctS_eq]; exact hLu2mu
  have hs_eB : FctSLimit û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))
      (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))) := by
    rw [hLeB.fctS_eq]; exact hLeB
  have hsum_lim := fctSLimit_add (by positivity) (by positivity) hu2mu_cmul heB_sym
    (fctSLimit_const_mul (warpC2Star : ℂ) hs_u2mu) hs_eB
  have hfn_eq : (fun u : ℝ => ((warpC2Star : ℝ) : ℂ) * extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ 2 * (concreteInnerFamily K4 ε).mu c L1 α u)) u +
      extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)) u) =
      extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (((warpC2Star * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u) *
        (concreteInnerFamily K4 ε).mu c L1 α u) := by
    ext u; rcases le_or_gt u (fctUc c) with hle | hgt
    · simp only [extUc, hle, ↓reduceIte]; push_cast; ring
    · simp only [extUc_zero_of_gt _ hgt, mul_zero, add_zero]
  rw [hfn_eq] at hsum_lim
  have hmu2_order : (fun u : ℝ => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
      ((u : ℂ) ^ 2 * (concreteInnerFamily K4 ε).mu c L1 α u)) =
      fun u : ℝ => (u : ℂ) ^ 2 * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u := by
    ext u; ring
  have hS_split : fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (((warpC2Star * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) =
      ((warpC2Star : ℝ) : ℂ) * fctS û (extUc c (fun u => (u : ℂ) ^ 2 * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) +
      fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u))) := by
    rw [hsum_lim.fctS_eq, hmu2_order]
  have hsym_12 : ‖fctS û (extUc c (fun u => (u : ℂ) ^ 2 * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) - (-iteratedDeriv 2 fctG0 û)‖ ≤
      2 * C_sym * c ^ (-(1 / 2 : ℝ)) := by
    calc ‖_‖ ≤ C_sym * (c ^ (-(4 / 3 : ℝ)) + |α| * c ^ (-(2 / 3 : ℝ))) := hsym2
      _ ≤ C_sym * (c ^ (-(1 / 2 : ℝ)) + c ^ (-(7 / 6 : ℝ))) := by
          have hc43 : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
          have hαc : |α| * c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) := by
            have hpow : c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(7 / 6 : ℝ)) := by
              rw [← Real.rpow_add hc0]; norm_num
            calc |α| * c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by gcongr
              _ = c ^ (-(7 / 6 : ℝ)) := hpow
          gcongr
      _ ≤ C_sym * (c ^ (-(1 / 2 : ℝ)) + c ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = 2 * C_sym * c ^ (-(1 / 2 : ℝ)) := by ring
  have heB_12 : ‖fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))‖ ≤
      (C_eB / 2) * c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [C_eB]
    calc ‖_‖ ≤ hA21.choose * (B_eB * c ^ (-(1 / 2 : ℝ))) := hbd_eB
      _ = (2 * hA21.choose * B_eB / 2) * c ^ (-(1 / 2 : ℝ)) := by ring
  have hg_lip2 : ‖iteratedDeriv 2 fctG0 û - iteratedDeriv 2 fctG0 (airyZero 1)‖ ≤
      C_g * c ^ (-(1 / 2 : ℝ)) := by
    have h1 := hg_lip (k := 2) le_rfl û (hadm.2.2.1.trans (hc76.trans (by norm_num)))
    calc ‖_‖ ≤ C_g * |û - airyZero 1| := h1
      _ ≤ C_g * c ^ (-(7 / 6 : ℝ)) := by gcongr; exact hadm.2.2.1
      _ ≤ C_g * c ^ (-(1 / 2 : ℝ)) := by gcongr
  have hg_norm : ‖iteratedDeriv 2 fctG0 û‖ ≤ C_g2 + C_g := by
    have h1 : ‖iteratedDeriv 2 fctG0 û - iteratedDeriv 2 fctG0 (airyZero 1)‖ ≤ C_g := by
      have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      calc _ ≤ C_g * c ^ (-(1 / 2 : ℝ)) := hg_lip2
        _ ≤ C_g * 1 := by gcongr
        _ = C_g := mul_one _
    calc ‖iteratedDeriv 2 fctG0 û‖
        = ‖(iteratedDeriv 2 fctG0 û - iteratedDeriv 2 fctG0 (airyZero 1)) + iteratedDeriv 2 fctG0 (airyZero 1)‖ := by ring_nf
      _ ≤ ‖iteratedDeriv 2 fctG0 û - iteratedDeriv 2 fctG0 (airyZero 1)‖ + ‖iteratedDeriv 2 fctG0 (airyZero 1)‖ :=
          norm_add_le _ _
      _ ≤ C_g + C_g2 := add_le_add h1 le_rfl
      _ = C_g2 + C_g := add_comm _ _
  have hsub_eq : ((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
      (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) -
      (-Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 (airyZero 1)) =
      Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) * ((warpC2Star : ℝ) : ℂ) *
        (fctS û (extUc c (fun u => (u : ℂ) ^ 2 * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
          (concreteInnerFamily K4 ε).mu c L1 α u)) - (-iteratedDeriv 2 fctG0 û)) +
      Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
        fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
          ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u))) +
      ((warpNu K4 ε c L1 α - 1 : ℝ) : ℂ) *
        (-Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 û) +
      (-Complex.I * ((warpC2Star : ℝ) : ℂ)) *
        (iteratedDeriv 2 fctG0 û - iteratedDeriv 2 fctG0 (airyZero 1)) +
      ((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
        (Complex.I * ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
          fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) := by
    rw [hsplit, mul_add, ← mul_assoc ((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) Complex.I _, hin, hS_split]
    push_cast; ring
  rw [hsub_eq]
  have ht1 : ‖Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) * ((warpC2Star : ℝ) : ℂ) *
      (fctS û (extUc c (fun u => (u : ℂ) ^ 2 * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) - (-iteratedDeriv 2 fctG0 û))‖ ≤
      4 * warpC2Star * C_sym * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_of_nonneg hc2s0]
    calc |warpNu K4 ε c L1 α| * warpC2Star * ‖_‖
        ≤ 2 * warpC2Star * (2 * C_sym * c ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hnu.2 hc2s0) hsym_12 (norm_nonneg _) (by positivity)
      _ = 4 * warpC2Star * C_sym * c ^ (-(1 / 2 : ℝ)) := by ring
  have ht2 : ‖Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
      fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((concreteInnerFamily K4 ε).eB c L1 α u * (concreteInnerFamily K4 ε).mu c L1 α u)))‖ ≤
      C_eB * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |warpNu K4 ε c L1 α| * ‖_‖ ≤ 2 * ((C_eB / 2) * c ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hnu.2 heB_12 (norm_nonneg _) (by norm_num)
      _ = C_eB * c ^ (-(1 / 2 : ℝ)) := by ring
  have ht3 : ‖((warpNu K4 ε c L1 α - 1 : ℝ) : ℂ) *
      (-Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 û)‖ ≤
      (pbcV * pbC0 * warpC2Star * C_g2 + pbcV * pbC0 * warpC2Star * C_g) * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg hc2s0]
    calc |warpNu K4 ε c L1 α - 1| * (warpC2Star * ‖iteratedDeriv 2 fctG0 û‖)
        ≤ (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) * (warpC2Star * (C_g2 + C_g)) :=
          mul_le_mul hnu.1 (mul_le_mul_of_nonneg_left hg_norm hc2s0) (by positivity)
            (mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) (by positivity))
      _ = (pbcV * pbC0 * warpC2Star * C_g2 + pbcV * pbC0 * warpC2Star * C_g) * c ^ (-(1 / 2 : ℝ)) := by ring
  have ht4 : ‖(-Complex.I * ((warpC2Star : ℝ) : ℂ)) *
      (iteratedDeriv 2 fctG0 û - iteratedDeriv 2 fctG0 (airyZero 1))‖ ≤
      warpC2Star * C_g * c ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hc2s0]
    calc warpC2Star * ‖iteratedDeriv 2 fctG0 û - iteratedDeriv 2 fctG0 (airyZero 1)‖
        ≤ warpC2Star * (C_g * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hg_lip2 hc2s0
      _ = warpC2Star * C_g * c ^ (-(1 / 2 : ℝ)) := by ring
  calc ‖_ + _ + _ + _ + _‖
      ≤ ‖_‖ + ‖_‖ + ‖_‖ + ‖_‖ + ‖_‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ 4 * warpC2Star * C_sym * c ^ (-(1 / 2 : ℝ)) + C_eB * c ^ (-(1 / 2 : ℝ)) +
          (pbcV * pbC0 * warpC2Star * C_g2 + pbcV * pbC0 * warpC2Star * C_g) * c ^ (-(1 / 2 : ℝ)) +
          warpC2Star * C_g * c ^ (-(1 / 2 : ℝ)) + C_N0 * C_sh * c ^ (-(1 / 2 : ℝ)) :=
        add_le_add (add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4) hsh_prod
    _ ≤ C_D * c ^ (-(1 / 2 : ℝ)) := by
        have hpos : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
        have hnn : 0 ≤ pbcV * pbC0 * warpC2Star * C_g :=
          mul_nonneg (mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) hc2s0) hCg0
        dsimp only [C_D]; nlinarith only [hpos, hnn]

/-- info: 'FormalResearch.SignUncertainty.fctWarpI_derivL_at_a1_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpI_derivL_at_a1_err

/-- info: 'FormalResearch.SignUncertainty.fctWarpI_derivAlpha_at_a1_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpI_derivAlpha_at_a1_err

end FormalResearch.SignUncertainty
