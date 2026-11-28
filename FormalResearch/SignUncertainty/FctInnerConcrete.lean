/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerConcreteSetup
public import FormalResearch.SignUncertainty.FctInnerJ0Scale
public import FormalResearch.SignUncertainty.FctInnerFactorsA
public import FormalResearch.SignUncertainty.FctInnerFactorsB

/-!
# Instantiation of `fct:inner-symbols` (b3) and (b4) for the concrete family (`FctInnerB3`, `FctInnerB4`)

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (b3)–(b4):
uses `concreteInnerFamily K4 ε` (`FctInnerConcreteSetup`) and proves:
* `concreteInnerB3`: `FctInnerB3 (concreteInnerFamily K4 ε)` (`δμ ∈ 𝒮^{10}(C c^{-4/3})`);
* `concreteInnerB4`: `FctInnerB4 (concreteInnerFamily K4 ε)` (`e_B ∈ 𝒮^{11}(C c^{-1/2})`, `e_A ∈ 𝒮^3(C c^{-2/3})`).

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real ContDiff
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

local notation "τs" => ((12 / π ^ 2) ^ (1 / 3 : ℝ))

/-! ### 4. Exponential & Jacobian symbol pieces for `FctInnerB3` -/

private lemma concrete_exp_in_sym {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 100 ≤ c₀ ∧ ∀ {c : ℝ}, c₀ ≤ c →
      ∀ {L1 α : ℝ}, (concreteInnerFamily K4 ε).adm c L1 α →
        FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C * c ^ (-(4 / 3 : ℝ)))
          (fun u => Complex.exp (-((K4 * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 4 : ℝ) : ℂ) +
            ((v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) : ℝ) : ℂ) +
            FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L1 α) u : ℝ) : ℂ))) - 1) := by
  let K_V : ℝ := pbKV
  have hKV0 : 0 ≤ K_V := pbKV_nonneg
  obtain ⟨C_T4, hCT40, hT4⟩ := fctInner_T4_sym hKV0
  obtain ⟨C_v1, c_v1, hCv10, hc_v1, hv1⟩ := fctInner_v1_sym hKV0
  obtain ⟨C_bin, hCbin0, hbin⟩ := fctInner_binet_sym hKV0
  let C_arg : ℝ := C_T4 * K4 + C_v1 + C_bin
  have hCarg0 : 0 ≤ C_arg := by positivity
  let thresh : ℝ := max (max 100 ((30 * pbC0 + 1) ^ 2))
    (max (max c_v1 (K4 ^ 2)) (max ((1000 * K_V + 1) ^ 2) ((4 ^ 10 * C_arg + 1) ^ 2)))
  have h100_th : 100 ≤ thresh := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨3 * (Nat.factorial 8 : ℝ) * C_arg, thresh, by positivity, h100_th, fun {c} hc {L1 α} hadm => ?_⟩
  have hfacts := concrete_adm_facts ((le_max_left _ _).trans hc) hadm
  rcases hfacts with ⟨hc0, hc100, hτ₁_sq, _, _, _, _, _, _, hVj, _, _⟩
  obtain ⟨hVjets, _⟩ := hVj
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hKV_small : K_V * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 := by
    have hc_KV : (1000 * K_V + 1) ^ 2 ≤ c :=
      (le_max_left _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : 1000 * K_V + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_KV
    have hpos : (0 : ℝ) < 1000 * K_V + 1 := by linarith only [hKV0]
    rw [Real.rpow_neg hc0.le]
    calc K_V * (c ^ (1 / 2 : ℝ))⁻¹ ≤ K_V * (1000 * K_V + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) hKV0
      _ ≤ 0.001 := by rw [← div_eq_mul_inv, div_le_iff₀ hpos]; linarith only [hKV0]
  have hK4_small : K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have hc_K4 : K4 ^ 2 ≤ c := (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : K4 ≤ c ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_K4
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
    exact h1
  have hcv1 : c_v1 ≤ c := (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
  have hs1 := (hT4 hK4 hc1 hKV_small hVjets).mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (4 : ℝ) ≤ 10)
  have hs2 := (hv1 hK4 hcv1 hK4_small hKV_small hadm.2.2.2 hVjets).mono_p Icc_subset_Ici_self
    (by positivity) (by norm_num : (8 : ℝ) ≤ 10)
  have hcexp17 : c ^ (-(17 / 12 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hs2' := hs2.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_left hcexp17 hCv10)
  have hs3 := (hbin hc1 hKV_small hVjets).mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (1 : ℝ) ≤ 10)
  have hsum : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_arg * c ^ (-(4 / 3 : ℝ))) _ :=
    ((hs1.add hDu hs2').add hDu hs3).mono_B Icc_subset_Ici_self (le_of_eq (by
      dsimp only [C_arg]; ring))
  have hBU : C_arg * c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (10 : ℝ) ≤ 1 := by
    have hc_arg : (4 ^ 10 * C_arg + 1) ^ 2 ≤ c :=
      (le_max_right _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : 4 ^ 10 * C_arg + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_arg
    have hpos : (0 : ℝ) < 4 ^ 10 * C_arg + 1 := by positivity
    have hUc := one_add_Uc_rpow_le hc1 10 (by norm_num)
    have h410 : (4 : ℝ) ^ (10 : ℝ) = 4 ^ 10 := by norm_num
    rw [h410] at hUc
    have hc_pow : c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc C_arg * c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (10 : ℝ)
        ≤ C_arg * c ^ (-(4 / 3 : ℝ)) * (4 ^ 10 * c ^ ((10 : ℝ) / 12)) := by gcongr
      _ = (4 ^ 10 * C_arg) * (c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12)) := by ring
      _ = (4 ^ 10 * C_arg) * (c ^ (1 / 2 : ℝ))⁻¹ := by rw [hc_pow, Real.rpow_neg hc0.le]
      _ ≤ (4 ^ 10 * C_arg) * (4 ^ 10 * C_arg + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) (by positivity)
      _ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hpos]; linarith only
  have hexp := hsum.cexp_sub_one hUc0 (by norm_num) (by positivity) hBU
  refine (hexp.mono_B Icc_subset_Ici_self (le_of_eq (by ring))).congr hDu fun u _ => ?_
  dsimp only
  congr 1; push_cast; ring

private lemma concrete_exp_alpha_sym {K4 ε : ℝ} :
    ∃ C_rem C_lin c₀ : ℝ, 0 ≤ C_rem ∧ 0 ≤ C_lin ∧ 100 ≤ c₀ ∧ ∀ {c : ℝ}, c₀ ≤ c →
      ∀ {L1 α : ℝ}, (concreteInnerFamily K4 ε).adm c L1 α →
        let V := concreteInnerV K4 ε c L1 α
        let T := fctInnerT c V
        let L_α : ℝ → ℂ := fun u =>
          ((c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * V 0 ^ 2) * u ^ 2 : ℝ) : ℂ)
        FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_rem * c ^ (-(4 / 3 : ℝ)))
          (fun u => Complex.exp (((α * (T u) ^ 2 : ℝ) : ℂ)) - 1 - L_α u) ∧
        FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C_lin * c ^ (-(7 / 6 : ℝ))) L_α := by
  let K_V : ℝ := pbKV
  have hKV0 : 0 ≤ K_V := pbKV_nonneg
  obtain ⟨C_V2, hCV20, hV2⟩ := fctInner_V_sq_sub_V0_sym hKV0
  let C_R : ℝ := 2 ^ 8 * (C_V2 * K_V) * 2
  let C_L : ℝ := 2 * (τs + 1) ^ 2
  let C_E : ℝ := C_L + C_R
  let C_rem : ℝ := 3 * 2 ^ 8 * (Nat.factorial 8 : ℝ) * C_E ^ 2 + C_R
  let thresh : ℝ := max (max 100 ((30 * pbC0 + 1) ^ 2))
    (max (max ((pbcV * pbC0 + 1) ^ 2) ((1000 * K_V + 1) ^ 2)) (16 * C_E + 1))
  have h100_th : 100 ≤ thresh := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨C_rem, C_L, thresh, by positivity, by positivity, h100_th, fun {c} hc {L1 α} hadm => ?_⟩
  have hfacts := concrete_adm_facts ((le_max_left _ _).trans hc) hadm
  rcases hfacts with ⟨hc0, hc100, _, _, _, _, _, _, _, hVj, _, hV0_sub⟩
  obtain ⟨hVjets, _⟩ := hVj
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hKV_small : K_V * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 := by
    have hc_KV : (1000 * K_V + 1) ^ 2 ≤ c :=
      (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : 1000 * K_V + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_KV
    have hpos : (0 : ℝ) < 1000 * K_V + 1 := by linarith only [hKV0]
    rw [Real.rpow_neg hc0.le]
    calc K_V * (c ^ (1 / 2 : ℝ))⁻¹ ≤ K_V * (1000 * K_V + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) hKV0
      _ ≤ 0.001 := by rw [← div_eq_mul_inv, div_le_iff₀ hpos]; linarith only [hKV0]
  have hV0_bd : |concreteInnerV K4 ε c L1 α 0| ≤ τs + 1 := by
    have hc_V0 : (pbcV * pbC0 + 1) ^ 2 ≤ c :=
      (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : pbcV * pbC0 + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_V0
    have hpos : (0 : ℝ) < pbcV * pbC0 + 1 := by linarith only [mul_nonneg pbcV_nonneg pbC0_nonneg]
    have hsub1 : |concreteInnerV K4 ε c L1 α 0 - τs| ≤ 1 := by
      calc |concreteInnerV K4 ε c L1 α 0 - τs| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := hV0_sub
        _ = pbcV * pbC0 * (c ^ (1 / 2 : ℝ))⁻¹ := by rw [Real.rpow_neg hc0.le]
        _ ≤ pbcV * pbC0 * (pbcV * pbC0 + 1)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) (mul_nonneg pbcV_nonneg pbC0_nonneg)
        _ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hpos]; linarith only [mul_nonneg pbcV_nonneg pbC0_nonneg]
    have htau0 : 0 ≤ τs := by positivity
    calc |concreteInnerV K4 ε c L1 α 0| = |(concreteInnerV K4 ε c L1 α 0 - τs) + τs| := by ring_nf
      _ ≤ |concreteInnerV K4 ε c L1 α 0 - τs| + |τs| := abs_add_le _ _
      _ ≤ 1 + τs := by rw [abs_of_nonneg htau0]; linarith only [hsub1]
      _ = τs + 1 := by ring
  have hα_bd : |c ^ (-(2 / 3 : ℝ)) * α| ≤ c ^ (-(7 / 6 : ℝ)) := by
    have hc76 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    calc c ^ (-(2 / 3 : ℝ)) * |α| ≤ c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
          gcongr; exact hadm.2.2.2
      _ = c ^ (-(7 / 6 : ℝ)) := hc76
  have h243_le : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  -- `L_α ∈ 𝒮^8_2(C_L * c^{-7/6})`
  have hLα_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C_L * c ^ (-(7 / 6 : ℝ)))
      (fun u => ((c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) *
        concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 : ℝ) : ℂ)) := by
    let kL : ℝ := c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * concreteInnerV K4 ε c L1 α 0 ^ 2)
    have hsc := (concrete_u_sq_sym hc0).const_mul hDu (kL : ℂ)
    have hkL_le : |kL| ≤ (τs + 1) ^ 2 * c ^ (-(7 / 6 : ℝ)) := by
      dsimp only [kL]
      rw [abs_mul, abs_mul ((2 : ℝ) ^ _), abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _), abs_pow]
      have hV0_sq : |concreteInnerV K4 ε c L1 α 0| ^ 2 ≤ (τs + 1) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hV0_bd 2
      calc |c ^ (-(2 / 3 : ℝ)) * α| * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * |concreteInnerV K4 ε c L1 α 0| ^ 2)
          ≤ c ^ (-(7 / 6 : ℝ)) * (1 * (τs + 1) ^ 2) := by gcongr
        _ = (τs + 1) ^ 2 * c ^ (-(7 / 6 : ℝ)) := by ring
    have hle : ‖(kL : ℂ)‖ * 2 ≤ C_L * c ^ (-(7 / 6 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |kL| * 2 ≤ (τs + 1) ^ 2 * c ^ (-(7 / 6 : ℝ)) * 2 := by gcongr
        _ = C_L * c ^ (-(7 / 6 : ℝ)) := by dsimp only [C_L]; ring
    refine (hsc.mono_B Icc_subset_Ici_self hle).congr hDu fun u _ => ?_
    dsimp only [kL]; push_cast; ring
  -- `R_α ∈ 𝒮^8_2(C_R * c^{-5/3})`
  have hRα_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C_R * c ^ (-(5 / 3 : ℝ)))
      (fun u => ((c ^ (-(2 / 3 : ℝ)) * α * (2 : ℝ) ^ (-(4 / 3 : ℝ)) *
        (concreteInnerV K4 ε c L1 α (fctInnerY c u) ^ 2 -
          concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 : ℝ) : ℂ)) := by
    have hsq := hV2 hc1 hKV_small hVjets
    have hmul := hsq.mul Icc_subset_Ici_self hDu (concrete_u_sq_sym hc0)
    have hmul' := hmul.mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + 2 ≤ 2)
    let kR : ℝ := c ^ (-(2 / 3 : ℝ)) * α * (2 : ℝ) ^ (-(4 / 3 : ℝ))
    have hsc := hmul'.const_mul hDu (kR : ℂ)
    have hc53 : c ^ (-(7 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(5 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hle : ‖(kR : ℂ)‖ * (2 ^ 8 * (C_V2 * K_V * c ^ (-(1 / 2 : ℝ))) * 2) ≤ C_R * c ^ (-(5 / 3 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hkR_le : |kR| ≤ c ^ (-(7 / 6 : ℝ)) := by
        dsimp only [kR]
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
        calc |c ^ (-(2 / 3 : ℝ)) * α| * (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) * 1 := by gcongr
          _ = c ^ (-(7 / 6 : ℝ)) := mul_one _
      calc |kR| * (2 ^ 8 * (C_V2 * K_V * c ^ (-(1 / 2 : ℝ))) * 2)
          ≤ c ^ (-(7 / 6 : ℝ)) * (2 ^ 8 * (C_V2 * K_V * c ^ (-(1 / 2 : ℝ))) * 2) := by gcongr
        _ = (2 ^ 8 * (C_V2 * K_V) * 2) * (c ^ (-(7 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by ring
        _ = C_R * c ^ (-(5 / 3 : ℝ)) := by dsimp only [C_R]; rw [hc53]
    refine (hsc.mono_B Icc_subset_Ici_self hle).congr hDu fun u _ => ?_
    dsimp only [kR]; push_cast; ring
  have hc53_76 : c ^ (-(5 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc53_43 : c ^ (-(5 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hRα_43 := (hRα_sym.mono_B Icc_subset_Ici_self
    (mul_le_mul_of_nonneg_left hc53_43 (by positivity))).mono_p Icc_subset_Ici_self (by positivity)
    (by norm_num : (2 : ℝ) ≤ 10)
  have hRα_76 := hRα_sym.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_left hc53_76 (by positivity))
  have hEα_eq : ∀ u : ℝ,
      ((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ) =
        ((c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) *
          concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 : ℝ) : ℂ) +
        ((c ^ (-(2 / 3 : ℝ)) * α * (2 : ℝ) ^ (-(4 / 3 : ℝ)) *
          (concreteInnerV K4 ε c L1 α (fctInnerY c u) ^ 2 -
            concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 : ℝ) : ℂ) := fun u => by
    have hc23 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have h243 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 = (2 : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hT_eq : fctInnerT c (concreteInnerV K4 ε c L1 α) u =
        (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * concreteInnerV K4 ε c L1 α (fctInnerY c u) := rfl
    have hr : α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 =
        c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 +
        c ^ (-(2 / 3 : ℝ)) * α * (2 : ℝ) ^ (-(4 / 3 : ℝ)) *
          (concreteInnerV K4 ε c L1 α (fctInnerY c u) ^ 2 - concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 := by
      rw [hT_eq, mul_pow, mul_pow, mul_pow, hc23, h243]; ring
    rw [hr]; push_cast; ring
  have hEα_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C_E * c ^ (-(7 / 6 : ℝ)))
      (fun u => ((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ)) :=
    ((hLα_sym.add hDu hRα_76).mono_B Icc_subset_Ici_self (le_of_eq (by
      dsimp only [C_E]; ring))).congr hDu fun u _ => hEα_eq u
  have hBU : C_E * c ^ (-(7 / 6 : ℝ)) * (1 + fctUc c) ^ (2 : ℝ) ≤ 1 := by
    have hc_E : 16 * C_E + 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
    have hUc := one_add_Uc_rpow_le hc1 2 (by norm_num)
    have h42 : (4 : ℝ) ^ (2 : ℝ) = 16 := by norm_num
    have hc_pow : c ^ (-(7 / 6 : ℝ)) * c ^ ((2 : ℝ) / 12) = c⁻¹ := by
      rw [← Real.rpow_add hc0, show (-(7 / 6 : ℝ) + 2 / 12 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    calc C_E * c ^ (-(7 / 6 : ℝ)) * (1 + fctUc c) ^ (2 : ℝ)
        ≤ C_E * c ^ (-(7 / 6 : ℝ)) * (4 ^ (2 : ℝ) * c ^ ((2 : ℝ) / 12)) := by gcongr
      _ = 16 * C_E * (c ^ (-(7 / 6 : ℝ)) * c ^ ((2 : ℝ) / 12)) := by rw [h42]; ring
      _ = 16 * C_E * c⁻¹ := by rw [hc_pow]
      _ ≤ 16 * C_E * (16 * C_E + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hc_E) (by positivity)
      _ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith only [show (0 : ℝ) ≤ C_E by positivity]
  have hsub_E := hEα_sym.cexp_sub_one_sub hUc0 (by omega) (by norm_num) (by positivity) hBU
  have hc73_43 : c ^ (-(7 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc_sq : (c ^ (-(7 / 6 : ℝ))) ^ 2 = c ^ (-(7 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hsub_E' : FctSymClsOn (Icc 0 (fctUc c)) 8 10
      ((3 * 2 ^ 8 * (Nat.factorial 8 : ℝ) * C_E ^ 2) * c ^ (-(4 / 3 : ℝ)))
      (fun u => Complex.exp (((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ)) - 1 -
        ((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ)) := by
    refine ((hsub_E.mono_B Icc_subset_Ici_self ?_).mono_p Icc_subset_Ici_self (by positivity)
      (by norm_num : 2 * (2 : ℝ) ≤ 10))
    rw [mul_pow, hc_sq]
    calc 3 * 2 ^ 8 * (Nat.factorial 8 : ℝ) * (C_E ^ 2 * c ^ (-(7 / 3 : ℝ)))
        ≤ 3 * 2 ^ 8 * (Nat.factorial 8 : ℝ) * (C_E ^ 2 * c ^ (-(4 / 3 : ℝ))) := by gcongr
      _ = (3 * 2 ^ 8 * (Nat.factorial 8 : ℝ) * C_E ^ 2) * c ^ (-(4 / 3 : ℝ)) := by ring
  refine ⟨?_, hLα_sym⟩
  refine ((hsub_E'.add hDu hRα_43).mono_B Icc_subset_Ici_self (le_of_eq (by
    dsimp only [C_rem]; ring))).congr hDu fun u _ => ?_
  simp only [hEα_eq u]; ring

/-- **`fct:inner-symbols` (b3)** for `concreteInnerFamily K4 ε`:
`μ - 1 - α̃ c₂ u² ∈ 𝒮^{10}(C c^{-4/3})` on `[0, U_c]`. -/
theorem concreteInnerB3 {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    FctInnerB3 (concreteInnerFamily K4 ε) := by
  let K_V : ℝ := pbKV
  have hKV0 : 0 ≤ K_V := pbKV_nonneg
  obtain ⟨δH_1, C_J1, c_J1, hδH1_pos, hCJ10, hc_J1, hJ1_sub⟩ :=
    fctInner_J1_sub_J0_sym pbM_nonneg pbC0_nonneg
  obtain ⟨δH_0, C_J0, c_J0, hδH0_pos, hCJ00, hc_J0, hJ0_sub⟩ :=
    fctInner_J0_sub_one_sym pbM_nonneg pbC0_nonneg
  obtain ⟨C_ein, c_ein, hCein0, hc_ein, hEin⟩ := concrete_exp_in_sym (ε := ε) hK4
  obtain ⟨C_eα, C_Lα, c_eα, hCeα0, hCLα0, hc_eα, hEα⟩ := concrete_exp_alpha_sym (K4 := K4) (ε := ε)
  obtain ⟨C_pk, c_pk, hCpk0, hc_pk, hPk⟩ := fctInner_phiKillDivM_sym hKV0
  let C_J : ℝ := C_J1 + C_J0
  let C_K : ℝ := (8 + |ctTheta1 ε|) * C_pk
  let C_eα_full : ℝ := 1 + C_eα + C_Lα
  let C_K_full : ℝ := 1 + C_K
  let C_δE : ℝ := 2 ^ 8 * C_ein * C_eα_full + C_eα
  let C_E_tot : ℝ := 2 ^ 8 * C_ein * C_eα_full + C_eα_full
  let C_EK : ℝ := 2 ^ 8 * C_E_tot * C_K_full
  let C_fin : ℝ := 2 ^ 8 * C_δE * C_K_full + 2 ^ 8 * (1 + C_Lα) * C_K + 2 ^ 8 * C_J * C_EK
  let δH : ℝ := min δH_1 δH_0
  have hδH_pos : 0 < δH := lt_min hδH1_pos hδH0_pos
  let thresh : ℝ := max (max (max 100 ((30 * pbC0 + 1) ^ 2)) (max c_J1 c_J0))
    (max (max c_ein c_eα) (max (max c_pk ((6 / δH + 1) ^ 2)) ((4 ^ 10 + 1) ^ 2)))
  refine ⟨C_fin, thresh, fun c hc L1 α hadm => ?_⟩
  have h100_c0 : max 100 ((30 * pbC0 + 1) ^ 2) ≤ c :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hfacts := concrete_adm_facts h100_c0 hadm
  rcases hfacts with ⟨hc0, hc100, hτ₁_sq, _, hell1, _, hSA_hi, hL1_bd, _, hVj, _, _⟩
  obtain ⟨hVjets, _⟩ := hVj
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  rcases concreteBox_spec hadm.1 with ⟨hTM, hTmt, _, hSΩ, hSℓ, hSr, hSε, _, _, _⟩
  have hτ1_δH : (c ^ (-(1 / 4 : ℝ))) ^ 2 < δH / 6 := by
    have hc_d : (6 / δH + 1) ^ 2 ≤ c :=
      (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : 6 / δH + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_d
    have h6 : 6 / δH < c ^ (1 / 2 : ℝ) := by linarith only [h1]
    have hinv : (c ^ (1 / 2 : ℝ))⁻¹ < δH / 6 := by
      rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      have := (div_lt_iff₀ hδH_pos).mp h6
      linarith only [this]
    rwa [hτ₁_sq, Real.rpow_neg hc0.le]
  have hc_J1' : c_J1 ≤ c := (le_max_left _ _ |>.trans (le_max_right _ _) |>.trans (le_max_left _ _)).trans hc
  have hc_J0' : c_J0 ≤ c := (le_max_right _ _ |>.trans (le_max_right _ _) |>.trans (le_max_left _ _)).trans hc
  have hc_ein' : c_ein ≤ c := (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
  have hc_eα' : c_eα ≤ c := (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
  have hc_pk' : c_pk ≤ c :=
    (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hc
  have hJ10 := hJ1_sub hK4 hadm.1.2.1 hc_J1' (hτ1_δH.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))
    hadm.1.2.2.2.2 hTM hSΩ hSℓ hSr hSε hell1 hadm.2.2.2 hSA_hi
  have hJ01 := hJ0_sub hK4 hadm.1.2.1 hc_J0' (hτ1_δH.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)))
    hadm.1.2.2.2.2 hTM hTmt hSΩ hSℓ hSr hSε hell1 hadm.2.2.2 hSA_hi
  have hcexp17 : c ^ (-(17 / 12 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hJ10' := ((hJ10.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_left hcexp17 hCJ10)).mono_p
    Icc_subset_Ici_self (by positivity) (by norm_num : (8 : ℝ) ≤ 10))
  have hδJ : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_J * c ^ (-(4 / 3 : ℝ)))
      (fun u => ((Jfun (concreteBoxS K4 ε c).V fctH ((c ^ (-(1 / 4 : ℝ))) ^ 2)
        ((concreteEll1 ε c L1, (1 : ℝ), α), fctInnerY c u) - 1 : ℝ) : ℂ)) := by
    refine ((hJ10'.add hDu hJ01).mono_B Icc_subset_Ici_self (le_of_eq (by
      dsimp only [C_J]; ring))).congr hDu fun u _ => ?_
    push_cast; ring
  have hEin_s := hEin hc_ein' hadm
  obtain ⟨hEα_rem, hLα_sym⟩ := hEα hc_eα' hadm
  have hPk_s := hPk hc_pk' hVjets
  -- `δK := L1 * phiKillDivM`
  have hδK_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 6 (C_K * c ^ (-(2 : ℝ)))
      (fun u => (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)) := by
    have hsc := hPk_s.const_mul hDu (L1 : ℂ)
    have hc2_eq : c ^ (-(2 / 3 : ℝ)) * c ^ (-(4 / 3 : ℝ)) = c ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hle : ‖(L1 : ℂ)‖ * (C_pk * c ^ (-(4 / 3 : ℝ))) ≤ C_K * c ^ (-(2 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |L1| * (C_pk * c ^ (-(4 / 3 : ℝ)))
          ≤ ((8 + |ctTheta1 ε|) * c ^ (-(2 / 3 : ℝ))) * (C_pk * c ^ (-(4 / 3 : ℝ))) := by gcongr
        _ = C_K * c ^ (-(2 : ℝ)) := by dsimp only [C_K]; rw [← hc2_eq]; ring
    exact hsc.mono_B Icc_subset_Ici_self hle
  -- Uniform shrinking factor `4^{10} c^{-1/2} ≤ 1`
  have h410 : (4 : ℝ) ^ (10 : ℝ) * c ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have hc_410 : (4 ^ 10 + 1) ^ 2 ≤ c :=
      (le_max_right _ _ |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : (4 : ℝ) ^ 10 + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_410
    rw [Real.rpow_neg hc0.le]
    calc (4 : ℝ) ^ (10 : ℝ) * (c ^ (1 / 2 : ℝ))⁻¹ ≤ (4 : ℝ) ^ 10 * ((4 : ℝ) ^ 10 + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by norm_num at h1 ⊢; exact h1)) (by positivity)
      _ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one (by positivity)]; norm_num
  have hUc_10 : c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (10 : ℝ) ≤ 1 := by
    have h1 := one_add_Uc_rpow_le hc1 10 (by norm_num)
    have h410' : (4 : ℝ) ^ (10 : ℝ) = 4 ^ 10 := by norm_num
    rw [h410'] at h1
    have hcp : c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (10 : ℝ)
        ≤ c ^ (-(4 / 3 : ℝ)) * ((4 : ℝ) ^ (10 : ℝ) * c ^ ((10 : ℝ) / 12)) := by
            rw [h410']; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (4 : ℝ) ^ (10 : ℝ) * (c ^ (-(4 / 3 : ℝ)) * c ^ ((10 : ℝ) / 12)) := by ring
      _ = (4 : ℝ) ^ (10 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by rw [hcp]
      _ ≤ 1 := h410
  have hUc_2 : c ^ (-(7 / 6 : ℝ)) * (1 + fctUc c) ^ (2 : ℝ) ≤ 1 := by
    have h1 := one_add_Uc_rpow_le hc1 2 (by norm_num)
    have h42' : (4 : ℝ) ^ (2 : ℝ) = 4 ^ 2 := by norm_num
    rw [h42'] at h1
    have hcp : c ^ (-(7 / 6 : ℝ)) * c ^ ((2 : ℝ) / 12) = c⁻¹ := by
      rw [← Real.rpow_add hc0, show (-(7 / 6 : ℝ) + 2 / 12 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have h4le : (4 : ℝ) ^ (2 : ℝ) ≤ (4 : ℝ) ^ (10 : ℝ) := by norm_num
    have hcinv : c⁻¹ ≤ c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc c ^ (-(7 / 6 : ℝ)) * (1 + fctUc c) ^ (2 : ℝ)
        ≤ c ^ (-(7 / 6 : ℝ)) * ((4 : ℝ) ^ (2 : ℝ) * c ^ ((2 : ℝ) / 12)) := by
            rw [h42']; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (4 : ℝ) ^ (2 : ℝ) * (c ^ (-(7 / 6 : ℝ)) * c ^ ((2 : ℝ) / 12)) := by ring
      _ = (4 : ℝ) ^ (2 : ℝ) * c⁻¹ := by rw [hcp]
      _ ≤ (4 : ℝ) ^ (10 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by gcongr
      _ ≤ 1 := h410
  have hUc_6 : c ^ (-(2 : ℝ)) * (1 + fctUc c) ^ (6 : ℝ) ≤ 1 := by
    have h1 := one_add_Uc_rpow_le hc1 6 (by norm_num)
    have h46' : (4 : ℝ) ^ (6 : ℝ) = 4 ^ 6 := by norm_num
    rw [h46'] at h1
    have hcp : c ^ (-(2 : ℝ)) * c ^ ((6 : ℝ) / 12) = c ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have h4le : (4 : ℝ) ^ (6 : ℝ) ≤ (4 : ℝ) ^ (10 : ℝ) := by norm_num
    have hc32 : c ^ (-(3 / 2 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc c ^ (-(2 : ℝ)) * (1 + fctUc c) ^ (6 : ℝ)
        ≤ c ^ (-(2 : ℝ)) * ((4 : ℝ) ^ (6 : ℝ) * c ^ ((6 : ℝ) / 12)) := by
            rw [h46']; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (4 : ℝ) ^ (6 : ℝ) * (c ^ (-(2 : ℝ)) * c ^ ((6 : ℝ) / 12)) := by ring
      _ = (4 : ℝ) ^ (6 : ℝ) * c ^ (-(3 / 2 : ℝ)) := by rw [hcp]
      _ ≤ (4 : ℝ) ^ (10 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by gcongr
      _ ≤ 1 := h410
  have shrink10 : ∀ {B : ℝ} {f : ℝ → ℂ}, 0 ≤ B →
      FctSymClsOn (Icc 0 (fctUc c)) 8 10 (B * c ^ (-(4 / 3 : ℝ))) f →
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 B f := fun {B f} hB hf => by
    refine (hf.shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 10)).mono_B Icc_subset_Ici_self ?_
    rw [sub_zero, mul_assoc]
    exact mul_le_of_le_one_right hB hUc_10
  have hEin_0 := shrink10 hCein0 hEin_s
  have hEα_rem_0 := shrink10 hCeα0 hEα_rem
  have hLα_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_Lα
      (fun u => ((c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) *
        concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 : ℝ) : ℂ)) := by
    refine (hLα_sym.shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 2)).mono_B
      Icc_subset_Ici_self ?_
    rw [sub_zero, mul_assoc]
    exact mul_le_of_le_one_right hCLα0 hUc_2
  have hδK_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_K
      (fun u => (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)) := by
    refine (hδK_sym.shrink_p hUc0.le (by positivity) (by norm_num : (0 : ℝ) ≤ 6)).mono_B
      Icc_subset_Ici_self ?_
    rw [sub_zero, mul_assoc]
    exact mul_le_of_le_one_right (by positivity) hUc_6
  -- Assemble `E_α`, `K`, `δE`, and `E`
  have h1_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 0 1 (fun _ : ℝ => (1 : ℂ)) :=
    (FctSymClsOn.const Icc_subset_Ici_self 8 (1 : ℂ)).mono_B Icc_subset_Ici_self (by norm_num)
  have hEα_full : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_eα_full
      (fun u => Complex.exp (((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ))) := by
    have hsum : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_eα_full _ :=
      ((hEα_rem_0.add hDu hLα_0).add hDu h1_sym).mono_B Icc_subset_Ici_self (le_of_eq (by
        dsimp only [C_eα_full]; ring))
    refine hsum.congr hDu fun u _ => ?_
    ring
  have hK_full : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_K_full
      (fun u => 1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)) :=
    ((h1_sym.sub hDu hδK_0).mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_K_full]))).congr
      hDu fun u _ => rfl
  have hexp_split : ∀ u : ℝ,
      Complex.exp (-((K4 * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 4 : ℝ) : ℂ) +
        ((v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) : ℝ) : ℂ) +
        ((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L1 α) u : ℝ) : ℂ))) =
      Complex.exp (-((K4 * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 4 : ℝ) : ℂ) +
        ((v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L1 α) u : ℝ) : ℂ))) *
      Complex.exp (((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ)) := fun u => by
    rw [← Complex.exp_add]; congr 1; ring
  have hδE_10 : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_δE * c ^ (-(4 / 3 : ℝ)))
      (fun u => Complex.exp (-((K4 * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 4 : ℝ) : ℂ) +
        ((v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) : ℝ) : ℂ) +
        ((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L1 α) u : ℝ) : ℂ))) -
        1 - ((c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) *
          concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 : ℝ) : ℂ)) := by
    have hm1 := hEin_s.mul Icc_subset_Ici_self hDu hEα_full
    have hm1' : FctSymClsOn (Icc 0 (fctUc c)) 8 10 ((2 ^ 8 * C_ein * C_eα_full) * c ^ (-(4 / 3 : ℝ))) _ :=
      (hm1.mono_B Icc_subset_Ici_self (le_of_eq (by ring))).mono_p Icc_subset_Ici_self
        (by positivity) (by norm_num : (10 : ℝ) + 0 ≤ 10)
    refine ((hm1'.add hDu hEα_rem).mono_B Icc_subset_Ici_self (le_of_eq (by
      dsimp only [C_δE]; ring))).congr hDu fun u _ => ?_
    rw [hexp_split u]; ring
  have hE_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_E_tot
      (fun u => Complex.exp (-((K4 * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 4 : ℝ) : ℂ) +
        ((v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) : ℝ) : ℂ) +
        ((α * (fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetDiff c (Complex.I * ((fctInnerT c (concreteInnerV K4 ε c L1 α) u : ℝ) : ℂ)))) := by
    have hm0 := (hEin_0.mul Icc_subset_Ici_self hDu hEα_full).mono_p Icc_subset_Ici_self
      (by positivity) (by norm_num : (0 : ℝ) + 0 ≤ 0)
    have hm1 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_E_tot _ :=
      (hm0.add hDu hEα_full).mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_E_tot]))
    refine hm1.congr hDu fun u _ => ?_
    rw [hexp_split u]; ring
  have hEK_0 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_EK _ :=
    ((hE_0.mul Icc_subset_Ici_self hDu hK_full).mono_B Icc_subset_Ici_self
      (le_of_eq (by dsimp only [C_EK]))).mono_p Icc_subset_Ici_self
        (by positivity) (by norm_num : (0 : ℝ) + 0 ≤ 0)
  -- Assemble the 3 error terms in `μ - 1 - α̃ c₂ u²`
  have ht1 : FctSymClsOn (Icc 0 (fctUc c)) 8 10 ((2 ^ 8 * C_δE * C_K_full) * c ^ (-(4 / 3 : ℝ))) _ :=
    ((hδE_10.mul Icc_subset_Ici_self hDu hK_full).mono_B Icc_subset_Ici_self
      (le_of_eq (by ring))).mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (10 : ℝ) + 0 ≤ 10)
  have h1pL : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (1 + C_Lα)
      (fun u => 1 + ((c ^ (-(2 / 3 : ℝ)) * α * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) *
        concreteInnerV K4 ε c L1 α 0 ^ 2) * u ^ 2 : ℝ) : ℂ)) := by
    have h1_2 := h1_sym.mono_p Icc_subset_Ici_self (by norm_num) (by norm_num : (0 : ℝ) ≤ 2)
    have hL1 := hLα_sym.mono_B Icc_subset_Ici_self (mul_le_of_le_one_right hCLα0
      (Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)))
    exact h1_2.add hDu hL1
  have hc2_43 : c ^ (-(2 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hδK_43 := hδK_sym.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_left hc2_43 (by positivity))
  have ht2 : FctSymClsOn (Icc 0 (fctUc c)) 8 10 ((2 ^ 8 * (1 + C_Lα) * C_K) * c ^ (-(4 / 3 : ℝ))) _ :=
    ((h1pL.mul Icc_subset_Ici_self hDu hδK_43).mono_B Icc_subset_Ici_self
      (le_of_eq (by ring))).mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (2 : ℝ) + 6 ≤ 10)
  have ht3 : FctSymClsOn (Icc 0 (fctUc c)) 8 10 ((2 ^ 8 * C_J * C_EK) * c ^ (-(4 / 3 : ℝ))) _ :=
    ((hδJ.mul Icc_subset_Ici_self hDu hEK_0).mono_B Icc_subset_Ici_self
      (le_of_eq (by ring))).mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (10 : ℝ) + 0 ≤ 10)
  have hcomb : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_fin * c ^ (-(4 / 3 : ℝ))) _ :=
    ((ht1.sub hDu ht2).add hDu ht3).mono_B Icc_subset_Ici_self (le_of_eq (by
      dsimp only [C_fin]; ring))
  refine hcomb.congr hDu fun u _ => ?_
  dsimp only [concreteInnerFamily]
  have hV0_eq : concreteInnerV K4 ε c L1 α 0 =
      (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), 0) := by
    simp [concreteInnerV, clampY_eq_self (by norm_num : (0 : ℝ) ≤ 3.5)]
  rw [← hV0_eq]
  push_cast; ring

/-! ### 5. Proof of `FctInnerB4` (`concreteInnerB4`) -/

/-- **`fct:inner-symbols` (b4)** for `concreteInnerFamily K4 ε`:
`e_B ∈ 𝒮^{11}(C c^{-1/2})` and `e_A ∈ 𝒮^3(C c^{-2/3})` on `[0, U_c]`. -/
theorem concreteInnerB4 {K4 ε : ℝ} :
    FctInnerB4 (concreteInnerFamily K4 ε) := by
  let K_V : ℝ := pbKV
  have hKV0 : 0 ≤ K_V := pbKV_nonneg
  obtain ⟨C_Vts, hCVts0, hVts⟩ := fctInner_V_sub_tauStar_sym hKV0
  obtain ⟨C_th, c_th, hCth0, hc_th, hTh⟩ := fctInner_theta1_sym hKV0
  obtain ⟨C_VA, hCVA0, hVA_sym⟩ := fctInner_V_sub_VA_sym hKV0 (by norm_num : (0 : ℝ) ≤ 4)
  obtain ⟨C_pk, c_pk, hCpk0, hc_pk, hPk⟩ := fctInner_phiKillDivM_sym hKV0
  -- Uniform `e_B` constant
  let C_Vts_sq : ℝ := 2 ^ 8 * (C_Vts * K_V) * (C_Vts * K_V + 2 * τs)
  let C_eB : ℝ := 2 ^ 8 * C_Vts_sq * 2 + C_th
  -- Uniform `e_A` constant
  let tauLo : ℝ := τs / 2
  have htauLo_pos : 0 < tauLo := by positivity
  let κ0 : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * tauLo
  have hκ0_pos : 0 < κ0 := by positivity
  let C_K : ℝ := (8 + |ctTheta1 ε|) * C_pk
  let C_eA1 : ℝ := 2 ^ 8 * (1 : ℝ) * (tauLo⁻¹ * (C_VA * K_V))
  let C_eA2 : ℝ := κ0⁻¹ * (4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8)))
  let C_eA : ℝ := C_eA1 + C_eA2
  let C_all : ℝ := max C_eB C_eA
  let thresh : ℝ := max (max (max 100 ((30 * pbC0 + 1) ^ 2)) (max c_th c_pk))
    (max (max ((1000 * K_V + 1) ^ 2) ((2 * pbcV * pbC0 / τs + 1) ^ 2))
      ((2 * 4 ^ 6 * C_K + 1) ^ 2))
  refine ⟨C_all, thresh, fun c hc L1 α hadm => ?_⟩
  have h100_c0 : max 100 ((30 * pbC0 + 1) ^ 2) ≤ c :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hfacts := concrete_adm_facts h100_c0 hadm
  rcases hfacts with ⟨hc0, hc100, hτ₁_sq, _, _, hA_mem, hSA_hi, hL1_bd, _, hVj, hVA_sub, _⟩
  obtain ⟨hVjets, hVeq_slice⟩ := hVj
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hKV_small : K_V * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 := by
    have hc_KV : (1000 * K_V + 1) ^ 2 ≤ c :=
      (le_max_left _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
    have h1 : 1000 * K_V + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_KV
    have hpos : (0 : ℝ) < 1000 * K_V + 1 := by linarith only [hKV0]
    rw [Real.rpow_neg hc0.le]
    calc K_V * (c ^ (1 / 2 : ℝ))⁻¹ ≤ K_V * (1000 * K_V + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) hKV0
      _ ≤ 0.001 := by rw [← div_eq_mul_inv, div_le_iff₀ hpos]; linarith only [hKV0]
  have hc_th' : c_th ≤ c := (le_max_left _ _ |>.trans (le_max_right _ _) |>.trans (le_max_left _ _)).trans hc
  have hc_pk' : c_pk ≤ c := (le_max_right _ _ |>.trans (le_max_right _ _) |>.trans (le_max_left _ _)).trans hc
  -- 1. `e_B ∈ 𝒮^{11}(C_all * c^{-1/2})`
  have heB_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 11 (C_all * c ^ (-(1 / 2 : ℝ)))
      ((concreteInnerFamily K4 ε).eB c L1 α) := by
    have hsub := hVts hc1 hVjets
    have hts2 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C_Vts * K_V + 2 * τs)
        (fun u => ((concreteInnerV K4 ε c L1 α (fctInnerY c u) - τs + 2 * τs : ℝ) : ℂ)) := by
      have h1 := hsub.mono_B Icc_subset_Ici_self (mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)))
      have h2 : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (2 * τs) (fun _ => ((2 * τs : ℝ) : ℂ)) :=
        (FctSymClsOn.const Icc_subset_Ici_self 8 ((2 * τs : ℝ) : ℂ)).mono_B Icc_subset_Ici_self
          (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)])
      refine (h1.add hDu h2).congr hDu fun u _ => ?_
      push_cast; ring
    have hsq_sub : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C_Vts_sq * c ^ (-(1 / 2 : ℝ)))
        (fun u => ((concreteInnerV K4 ε c L1 α (fctInnerY c u) ^ 2 - τs ^ 2 : ℝ) : ℂ)) := by
      have hm := hsub.mul Icc_subset_Ici_self hDu hts2
      refine ((hm.mono_B Icc_subset_Ici_self (le_of_eq (by
        dsimp only [C_Vts_sq]; ring))).mono_p Icc_subset_Ici_self (by positivity)
        (by norm_num : (0 : ℝ) + 0 ≤ 0)).congr hDu fun u _ => ?_
      push_cast; ring
    have hterm1 := (hsq_sub.mul Icc_subset_Ici_self hDu (concrete_u_sq_sym hc0)).const_mul hDu
      (((2 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ)
    have h243_le : ‖(((2 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hterm1' := (hterm1.mono_B Icc_subset_Ici_self (by
      calc ‖(((2 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ)‖ * (2 ^ 8 * (C_Vts_sq * c ^ (-(1 / 2 : ℝ))) * 2)
          ≤ 1 * (2 ^ 8 * (C_Vts_sq * c ^ (-(1 / 2 : ℝ))) * 2) := by gcongr
        _ = (2 ^ 8 * C_Vts_sq * 2) * c ^ (-(1 / 2 : ℝ)) := by ring)).mono_p
      Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + 2 ≤ 11)
    have hth := hTh hc_th' hKV_small hVjets
    have hc34_12 : c ^ (-(3 / 4 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hth' := hth.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_left hc34_12 hCth0)
    have hsum := hterm1'.add hDu hth'
    refine (hsum.mono_B Icc_subset_Ici_self ?_).congr hDu fun u _ => ?_
    · have hle : C_eB ≤ C_all := le_max_left _ _
      calc (2 ^ 8 * C_Vts_sq * 2) * c ^ (-(1 / 2 : ℝ)) + C_th * c ^ (-(1 / 2 : ℝ))
          = C_eB * c ^ (-(1 / 2 : ℝ)) := by dsimp only [C_eB]; ring
        _ ≤ C_all * c ^ (-(1 / 2 : ℝ)) := by gcongr
    · dsimp only [concreteInnerFamily]; push_cast; ring
  -- 2. `e_A ∈ 𝒮^3(C_all * c^{-2/3})`
  have heA_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 3 (C_all * c ^ (-(2 / 3 : ℝ)))
      ((concreteInnerFamily K4 ε).eA c L1 α) := by
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    have hVA_lo : tauLo ≤ S.V (q, S.A q) := by
      have hc_va : (2 * pbcV * pbC0 / τs + 1) ^ 2 ≤ c :=
        (le_max_right _ _ |>.trans (le_max_left _ _) |>.trans (le_max_right _ _)).trans hc
      have h1 : 2 * pbcV * pbC0 / τs + 1 ≤ c ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_va
      have htau_pos : 0 < τs := by positivity
      have hpos : (0 : ℝ) < 2 * pbcV * pbC0 / τs + 1 := by
        have : 0 ≤ 2 * pbcV * pbC0 / τs := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) pbcV_nonneg) pbC0_nonneg) htau_pos.le
        linarith only [this]
      have hsub : pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ τs / 2 := by
        rw [Real.rpow_neg hc0.le]
        calc pbcV * pbC0 * (c ^ (1 / 2 : ℝ))⁻¹
            ≤ pbcV * pbC0 * (2 * pbcV * pbC0 / τs + 1)⁻¹ :=
              mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) (mul_nonneg pbcV_nonneg pbC0_nonneg)
          _ ≤ τs / 2 := by
              rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]
              have hnn : 0 ≤ pbcV * pbC0 := mul_nonneg pbcV_nonneg pbC0_nonneg
              have hkey : (2 * pbcV * pbC0 / τs) * τs = 2 * pbcV * pbC0 := by
                field_simp [htau_pos.ne']
              nlinarith only [hkey, htau_pos]
      dsimp only [tauLo]; linarith only [abs_le.mp hVA_sub |>.1, hsub]
    have hY_sub : ∀ u ∈ Icc 0 (fctUc c), |fctInnerY c u - S.A q| ≤ 4 * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by
      intro u hu
      have hY0 : 0 ≤ fctInnerY c u := by unfold fctInnerY; have := hu.1; positivity
      have hY_le : fctInnerY c u ≤ c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by
        unfold fctInnerY
        have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
        have hu2 : u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith only [hu.1]
        calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
            ≤ 1 * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by gcongr
          _ = c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by ring
      have h1u2 : 1 ≤ (1 + u) ^ 2 := by nlinarith only [hu.1]
      have hc160 : 0 ≤ c ^ (-(1 / 6 : ℝ)) := by positivity
      have hA_le : S.A q ≤ 4 * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by
        calc S.A q ≤ 4 * c ^ (-(1 / 6 : ℝ)) := hSA_hi
          _ ≤ 4 * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := le_mul_of_one_le_right (by positivity) h1u2
      have hY4 : fctInnerY c u ≤ 4 * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by
        nlinarith only [hY_le, hc160, h1u2]
      exact abs_sub_le_iff.mpr ⟨by linarith only [hY4, hA_mem.1], by linarith only [hY0, hA_le]⟩
    have hV_VA := hVA_sym hc1 ⟨hA_mem.1.le, by linarith only [hA_mem.2]⟩ hY_sub hVjets
    have hVA_inv_bd : |(S.V (q, S.A q))⁻¹| ≤ tauLo⁻¹ := by
      rw [abs_inv, abs_of_pos (lt_of_lt_of_le htauLo_pos hVA_lo)]
      exact inv_anti₀ htauLo_pos hVA_lo
    have hV_VA_div : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (tauLo⁻¹ * (C_VA * K_V) * c ^ (-(2 / 3 : ℝ)))
        (fun u => (((concreteInnerV K4 ε c L1 α (fctInnerY c u) - S.V (q, S.A q)) / S.V (q, S.A q) : ℝ) : ℂ)) := by
      have hVA_eq : concreteInnerV K4 ε c L1 α (S.A q) = S.V (q, S.A q) :=
        hVeq_slice (S.A q) ⟨hA_mem.1.le, by linarith only [hA_mem.2]⟩
      have hsc := hV_VA.const_mul hDu ((S.V (q, S.A q))⁻¹ : ℂ)
      have hle : ‖((S.V (q, S.A q))⁻¹ : ℂ)‖ * (C_VA * K_V * c ^ (-(2 / 3 : ℝ))) ≤
          tauLo⁻¹ * (C_VA * K_V) * c ^ (-(2 / 3 : ℝ)) := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv]
        calc |(S.V (q, S.A q))⁻¹| * (C_VA * K_V * c ^ (-(2 / 3 : ℝ)))
            ≤ tauLo⁻¹ * (C_VA * K_V * c ^ (-(2 / 3 : ℝ))) := by gcongr
          _ = tauLo⁻¹ * (C_VA * K_V) * c ^ (-(2 / 3 : ℝ)) := by ring
      refine (hsc.mono_B Icc_subset_Ici_self hle).congr hDu fun u _ => ?_
      rw [hVA_eq, div_eq_mul_inv]; push_cast; ring
    have hiu : FctSymClsOn (Icc 0 (fctUc c)) 8 1 1 (fun u => -(Complex.I * (u : ℂ))) := by
      refine ((concrete_u_sym hc0).const_mul hDu (-Complex.I)).mono_B Icc_subset_Ici_self ?_ |>.congr
        hDu fun u _ => by ring
      simp [norm_neg, Complex.norm_I]
    have hterm1 : FctSymClsOn (Icc 0 (fctUc c)) 8 3 (C_eA1 * c ^ (-(2 / 3 : ℝ)))
        (fun u => -(Complex.I * (u : ℂ)) * (((concreteInnerV K4 ε c L1 α (fctInnerY c u) -
          S.V (q, S.A q)) / S.V (q, S.A q) : ℝ) : ℂ)) := by
      have hm := hiu.mul Icc_subset_Ici_self hDu hV_VA_div
      exact (hm.mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_eA1]; ring))).mono_p
        Icc_subset_Ici_self (by positivity) (by norm_num : (1 : ℝ) + 2 ≤ 3)
    -- Term 2: `- phiKillDivM / ((1 - L1 * phiKillDivM) * uL)`
    have hPk_s := hPk hc_pk' hVjets
    have hδK_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 6 (C_K * c ^ (-(2 : ℝ)))
        (fun u => -((L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u))) := by
      have hsc := hPk_s.const_mul hDu (-(L1 : ℂ))
      have hc2_eq : c ^ (-(2 / 3 : ℝ)) * c ^ (-(4 / 3 : ℝ)) = c ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have hle : ‖-(L1 : ℂ)‖ * (C_pk * c ^ (-(4 / 3 : ℝ))) ≤ C_K * c ^ (-(2 : ℝ)) := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
        calc |L1| * (C_pk * c ^ (-(4 / 3 : ℝ)))
            ≤ ((8 + |ctTheta1 ε|) * c ^ (-(2 / 3 : ℝ))) * (C_pk * c ^ (-(4 / 3 : ℝ))) := by gcongr
          _ = C_K * c ^ (-(2 : ℝ)) := by dsimp only [C_K]; rw [← hc2_eq]; ring
      exact (hsc.mono_B Icc_subset_Ici_self hle).congr hDu fun u _ => by ring
    have hBU_K : C_K * c ^ (-(2 : ℝ)) * (1 + fctUc c) ^ (6 : ℝ) ≤ 1 / 2 := by
      have hc_CK : (2 * 4 ^ 6 * C_K + 1) ^ 2 ≤ c :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans hc
      have h1 : 2 * 4 ^ 6 * C_K + 1 ≤ c ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_CK
      have hpos : (0 : ℝ) < 2 * 4 ^ 6 * C_K + 1 := by positivity
      have hUc := one_add_Uc_rpow_le hc1 6 (by norm_num)
      have h46 : (4 : ℝ) ^ (6 : ℝ) = 4 ^ 6 := by norm_num
      rw [h46] at hUc
      have hcp : c ^ (-(2 : ℝ)) * c ^ ((6 : ℝ) / 12) = c ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have hc32 : c ^ (-(3 / 2 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      calc C_K * c ^ (-(2 : ℝ)) * (1 + fctUc c) ^ (6 : ℝ)
          ≤ C_K * c ^ (-(2 : ℝ)) * (4 ^ 6 * c ^ ((6 : ℝ) / 12)) := by gcongr
        _ = (4 ^ 6 * C_K) * (c ^ (-(2 : ℝ)) * c ^ ((6 : ℝ) / 12)) := by ring
        _ = (4 ^ 6 * C_K) * c ^ (-(3 / 2 : ℝ)) := by rw [hcp]
        _ ≤ (4 ^ 6 * C_K) * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ ≤ (4 ^ 6 * C_K) * (2 * 4 ^ 6 * C_K + 1)⁻¹ := by
            rw [Real.rpow_neg hc0.le]; exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) (by positivity)
        _ ≤ 1 / 2 := by
            rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]
            linarith only [show (0 : ℝ) ≤ C_K by positivity]
    have hK_inv := hδK_sym.inv_one_add hUc0 (by norm_num) (by positivity) hBU_K
    have hpk_div : FctSymClsOn (Icc 0 (fctUc c)) 8 6 ((2 ^ 8 * (C_pk * invSymBound 8)) * c ^ (-(4 / 3 : ℝ)))
        (fun u => phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) *
          (1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u))⁻¹) := by
      have hm := hPk_s.mul Icc_subset_Ici_self hDu hK_inv
      have hB0 : 0 ≤ (2 ^ 8 * (C_pk * invSymBound 8)) * c ^ (-(4 / 3 : ℝ)) :=
        mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hCpk0 (invSymBound_nonneg 8))) (by positivity)
      refine ((hm.mono_B Icc_subset_Ici_self (le_of_eq (by ring))).mono_p Icc_subset_Ici_self
        hB0 (by norm_num : (6 : ℝ) + 0 ≤ 6)).congr hDu fun u _ => ?_
      rw [sub_eq_add_neg]
    have hpk_3 : FctSymClsOn (Icc 0 (fctUc c)) 8 3
        ((4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8))) * c ^ (-(13 / 12 : ℝ)))
        (fun u => phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) *
          (1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u))⁻¹) := by
      have hB0 : 0 ≤ (2 ^ 8 * (C_pk * invSymBound 8)) * c ^ (-(4 / 3 : ℝ)) :=
        mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hCpk0 (invSymBound_nonneg 8))) (by positivity)
      have hs := hpk_div.shrink_p hUc0.le hB0 (by norm_num : (3 : ℝ) ≤ 6)
      have hUc3 := one_add_Uc_rpow_le hc1 3 (by norm_num)
      have h43 : (4 : ℝ) ^ (3 : ℝ) = 4 ^ 3 := by norm_num
      have hcp : c ^ (-(4 / 3 : ℝ)) * c ^ ((3 : ℝ) / 12) = c ^ (-(13 / 12 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      refine hs.mono_B Icc_subset_Ici_self ?_
      rw [show (6 : ℝ) - 3 = 3 by norm_num]
      calc (2 ^ 8 * (C_pk * invSymBound 8)) * c ^ (-(4 / 3 : ℝ)) * (1 + fctUc c) ^ (3 : ℝ)
          ≤ (2 ^ 8 * (C_pk * invSymBound 8)) * c ^ (-(4 / 3 : ℝ)) * ((4 : ℝ) ^ (3 : ℝ) * c ^ ((3 : ℝ) / 12)) := by
              gcongr
        _ = (4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8))) * (c ^ (-(4 / 3 : ℝ)) * c ^ ((3 : ℝ) / 12)) := by
              rw [h43]; ring
        _ = (4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8))) * c ^ (-(13 / 12 : ℝ)) := by rw [hcp]
    let uL : ℝ := -fctKappa c * S.V (q, S.A q)
    have huL_abs : κ0 * c ^ (2 / 3 : ℝ) ≤ |uL| := by
      have hκ_eq : fctKappa c = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) := rfl
      dsimp only [uL, κ0]
      rw [hκ_eq, neg_mul, abs_neg, abs_mul, abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _),
        abs_of_pos (Real.rpow_pos_of_pos hc0 _),
        abs_of_pos (lt_of_lt_of_le htauLo_pos hVA_lo)]
      calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * tauLo * c ^ (2 / 3 : ℝ)
          = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * tauLo := by ring
        _ ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * S.V (q, S.A q) := by gcongr
    have huL_inv : |-(uL⁻¹)| ≤ κ0⁻¹ * c ^ (-(2 / 3 : ℝ)) := by
      rw [abs_neg, abs_inv]
      have h1 := inv_anti₀ (mul_pos hκ0_pos (Real.rpow_pos_of_pos hc0 _)) huL_abs
      rwa [mul_inv, ← Real.rpow_neg hc0.le] at h1
    have hterm2 : FctSymClsOn (Icc 0 (fctUc c)) 8 3 (C_eA2 * c ^ (-(2 / 3 : ℝ)))
        (fun u => -(phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) /
          ((1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)) *
            (uL : ℂ)))) := by
      have hsc := hpk_3.const_mul hDu (-(uL⁻¹ : ℝ) : ℂ)
      have hc13_le1 : c ^ (-(13 / 12 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      have hle : ‖(-(uL⁻¹ : ℝ) : ℂ)‖ * ((4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8))) * c ^ (-(13 / 12 : ℝ))) ≤
          C_eA2 * c ^ (-(2 / 3 : ℝ)) := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, ← abs_neg]
        have h48_nn : 0 ≤ 4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8)) :=
          mul_nonneg (by positivity) (mul_nonneg (by positivity) (mul_nonneg hCpk0 (invSymBound_nonneg 8)))
        calc |-(uL⁻¹)| * ((4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8))) * c ^ (-(13 / 12 : ℝ)))
            ≤ (κ0⁻¹ * c ^ (-(2 / 3 : ℝ))) * ((4 ^ 3 * (2 ^ 8 * (C_pk * invSymBound 8))) * 1) := by gcongr
          _ = C_eA2 * c ^ (-(2 / 3 : ℝ)) := by dsimp only [C_eA2]; ring
      refine (hsc.mono_B Icc_subset_Ici_self hle).congr hDu fun u _ => ?_
      rw [div_eq_mul_inv, mul_inv]; push_cast; ring
    have hsum := hterm1.add hDu hterm2
    refine (hsum.mono_B Icc_subset_Ici_self ?_).congr hDu fun u _ => ?_
    · have hle : C_eA ≤ C_all := le_max_right _ _
      calc C_eA1 * c ^ (-(2 / 3 : ℝ)) + C_eA2 * c ^ (-(2 / 3 : ℝ))
          = C_eA * c ^ (-(2 / 3 : ℝ)) := by dsimp only [C_eA]; ring
        _ ≤ C_all * c ^ (-(2 / 3 : ℝ)) := by gcongr
    · dsimp only [concreteInnerFamily]; ring
  exact ⟨heB_sym, heA_sym⟩

/-- info: 'FormalResearch.SignUncertainty.concreteInnerB3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concreteInnerB3

/-- info: 'FormalResearch.SignUncertainty.concreteInnerB4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concreteInnerB4

end FormalResearch.SignUncertainty
