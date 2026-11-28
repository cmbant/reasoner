/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerFactorsB
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Inner symbol bounds for `V`-differences and smooth `V` extension

For `FctVJets K c V` on `[0, U_c]` (`U_c = 2.96 c^{1/12}`):
* `fctInner_V_sub_tauStar_sym`, `fctInner_V_sq_sub_tauStar_sym`, `fctInner_V_sq_sub_V0_sym`:
  `V(Y(u)) - τ_* ∈ S⁰(C K c^{-1/2})` and `V(Y(u))² - V(0)² ∈ S⁰(C K c^{-1/2})`;
* `fctInner_V_sub_VA_sym`: `V(Y(u)) - V(A) ∈ S²(C K c^{-2/3})` when `|Y(u) - A| ≤ C_A c^{-1/6} (1+u)²`;
* `fctVJets_of_chartV`: extends `ChartSetup` slice `V₀` on `Yint = (-1/5, 3.6)` to `FctVJets` on `[0, 3.6]`,
  preserving `V₀` identically on `[0, 3.5]`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real ContDiff BigOperators
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

local notation "τs" => (12 / π ^ 2) ^ (1 / 3 : ℝ)

/-! ### `V(Y) - τ_*`, `V(Y)² - V(0)²`, and `V(Y) - V(A)` symbol bounds -/

private lemma fctInnerY_deriv_bounds {c : ℝ} (hc : 1 ≤ c) :
    ContDiffOn ℝ 8 (fctInnerY c) (Icc 0 (fctUc c)) ∧
    (∀ u ∈ Icc 0 (fctUc c), 0 ≤ fctInnerY c u ∧ fctInnerY c u ≤ c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ u ∈ Icc 0 (fctUc c),
      |iteratedDerivWithin j (fctInnerY c) (Icc 0 (fctUc c)) u| ≤ 8 * c ^ (-(1 / 12 : ℝ)) * (1 + u) ^ ((1 : ℝ) - j) ∧
      |iteratedDerivWithin j (fctInnerY c) (Icc 0 (fctUc c)) u| ≤ 2 * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ ((2 : ℝ) - j)) := by
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  have hcd : ContDiff ℝ 8 (fctInnerY c) := by unfold fctInnerY; fun_prop
  refine ⟨hcd.contDiffOn, fun u hu => ?_, fun j hj1 hj8 u hu => ?_⟩
  · have h2 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := by linarith [fctB2_two_rpow_neg43_le]
    have h20 : 0 ≤ (2 : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
    have hu2 : u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith [hu.1]
    refine ⟨by unfold fctInnerY; have := hu.1; positivity, ?_⟩
    unfold fctInnerY
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
        ≤ 1 * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by gcongr
      _ = c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2 := by rw [one_mul]
  · set κ : ℝ := 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))
    have hκ0 : 0 ≤ κ := by positivity
    have hκ_le : κ ≤ c ^ (-(1 / 6 : ℝ)) := by
      have h2 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := by linarith [fctB2_two_rpow_neg43_le]
      calc κ = (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := rfl
        _ ≤ 1 * c ^ (-(1 / 6 : ℝ)) := by gcongr
        _ = c ^ (-(1 / 6 : ℝ)) := one_mul _
    have h1u0 : 0 < 1 + u := by linarith [hu.1]
    have h1u_le : 1 + u ≤ 4 * c ^ ((1 : ℝ) / 12) := by
      have := one_add_fctUc_le hc; linarith [hu.2]
    have hit : iteratedDerivWithin j (fctInnerY c) (Icc 0 (fctUc c)) u = iteratedDeriv j (fctInnerY c) u :=
      iteratedDerivWithin_eq_iteratedDeriv hDu (hcd.contDiffAt.of_le (by exact_mod_cast hj8)) hu
    rw [hit]
    have hYeq : fctInnerY c = fun x => κ * x ^ 2 := rfl
    rcases (by omega : j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl | rfl | hj3
    · have hd1 : iteratedDeriv 1 (fun x => κ * x ^ 2) u = 2 * κ * u := by
        rw [iteratedDeriv_one, ((hasDerivAt_pow 2 u).const_mul κ).deriv]; ring
      rw [hYeq, hd1, abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hκ0, abs_of_nonneg hu.1]
      have h_2j : (1 + u) ^ ((2 : ℝ) - (1 : ℕ)) = 1 + u := by norm_num
      have h_1j : (1 + u) ^ ((1 : ℝ) - (1 : ℕ)) = 1 := by norm_num
      rw [h_2j, h_1j, mul_one]
      have hle2 : 2 * κ * u ≤ 2 * c ^ (-(1 / 6 : ℝ)) * (1 + u) := by
        have : u ≤ 1 + u := by linarith
        have hu0 : 0 ≤ u := hu.1
        gcongr
      refine ⟨?_, hle2⟩
      have hu4 : u ≤ 4 * c ^ ((1 : ℝ) / 12) := by linarith [hu.1]
      have hu0 : 0 ≤ u := hu.1
      calc 2 * κ * u ≤ 2 * c ^ (-(1 / 6 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
        _ = 8 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
        _ = 8 * c ^ (-(1 / 12 : ℝ)) := by rw [← Real.rpow_add hc0]; congr 1; norm_num
    · have hd2 : iteratedDeriv 2 (fun x => κ * x ^ 2) u = 2 * κ := by
        have hfn : (iteratedDeriv 1 fun x => κ * x ^ 2) = fun x => 2 * κ * x := by
          ext x; rw [iteratedDeriv_one, ((hasDerivAt_pow 2 x).const_mul κ).deriv]; ring
        rw [iteratedDeriv_succ, hfn]
        simpa only [id_eq, mul_one] using ((hasDerivAt_id u).const_mul (2 * κ)).deriv
      rw [hYeq, hd2, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hκ0]
      have h_2j : (1 + u) ^ ((2 : ℝ) - (2 : ℕ)) = 1 := by norm_num
      have h_1j : (1 + u) ^ ((1 : ℝ) - (2 : ℕ)) = (1 + u)⁻¹ := by
        rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
      rw [h_2j, h_1j, mul_one]
      have hle2 : 2 * κ ≤ 2 * c ^ (-(1 / 6 : ℝ)) := mul_le_mul_of_nonneg_left hκ_le zero_le_two
      refine ⟨?_, hle2⟩
      have h1 : 2 * κ * (1 + u) ≤ 8 * c ^ (-(1 / 12 : ℝ)) := by
        calc 2 * κ * (1 + u) ≤ 2 * c ^ (-(1 / 6 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
          _ = 8 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
          _ = 8 * c ^ (-(1 / 12 : ℝ)) := by rw [← Real.rpow_add hc0]; congr 1; norm_num
      calc 2 * κ = (2 * κ * (1 + u)) * (1 + u)⁻¹ := by field_simp [h1u0.ne']
        _ ≤ 8 * c ^ (-(1 / 12 : ℝ)) * (1 + u)⁻¹ := by gcongr
    · have hd3 : iteratedDeriv j (fun x => κ * x ^ 2) u = 0 := by
        have hfn2 : (iteratedDeriv 2 fun x => κ * x ^ 2) = fun _ => 2 * κ := by
          ext x
          have hfn : (iteratedDeriv 1 fun x => κ * x ^ 2) = fun x => 2 * κ * x := by
            ext z; rw [iteratedDeriv_one, ((hasDerivAt_pow 2 z).const_mul κ).deriv]; ring
          rw [iteratedDeriv_succ, hfn]
          simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (2 * κ)).deriv
        have hsplit : j = (j - 2) + 2 := by omega
        rw [hsplit, ← iteratedDeriv_iteratedDeriv_eq, hfn2, iteratedDeriv_const,
          show (if j - 2 = 0 then 2 * κ else 0) = 0 by simp only [show j - 2 ≠ 0 by omega, ↓reduceIte]]
      rw [hYeq, hd3, abs_zero]
      exact ⟨by positivity, by positivity⟩

lemma fctInner_V_sub_tauStar_sym {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ}, 1 ≤ c →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C * K * c ^ (-(1 / 2 : ℝ)))
          (fun u => ((V (fctInnerY c u) - τs : ℝ) : ℂ)) := by
  refine ⟨(Nat.factorial 8 : ℝ) * 32 ^ 8, by positivity, fun {c} hc {V} hV => ?_⟩
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  obtain ⟨hYcd, _, hYd⟩ := fctInnerY_deriv_bounds hc
  have hDu36 : UniqueDiffOn ℝ (Icc (0 : ℝ) 3.6) := uniqueDiffOn_Icc (by norm_num)
  have hg_cd : ContDiffOn ℝ 8 (fun y : ℝ => ((V y - τs : ℝ) : ℂ)) (Icc (0 : ℝ) 3.6) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((hV.1.of_le (by norm_num : ((8 : ℕ) : WithTop ℕ∞) ≤ 14)).sub contDiffOn_const)
  have hg_bd : ∀ i ≤ 8, ∀ y ∈ Icc (0 : ℝ) 3.6,
      ‖iteratedDerivWithin i (fun y : ℝ => ((V y - τs : ℝ) : ℂ)) (Icc (0 : ℝ) 3.6) y‖ ≤
        K * c ^ (-(1 / 2 : ℝ)) := by
    intro i hi y hy
    rw [iteratedDerivWithin_ofReal_cast hDu36 (n := 8)
      ((hV.1.of_le (by norm_num : ((8 : ℕ) : WithTop ℕ∞) ≤ 14)).sub contDiffOn_const) hi y hy,
      Complex.norm_real, Real.norm_eq_abs]
    exact hV.2 i (by omega) y hy
  have hmaps : MapsTo (fctInnerY c) (Icc 0 (fctUc c)) (Icc (0 : ℝ) 3.6) := fun u hu =>
    have h := fctInnerY_mem_35 hc hu; ⟨h.1, by linarith [h.2]⟩
  have hBfM : 8 * c ^ (-(1 / 12 : ℝ)) * (1 + fctUc c) ≤ 32 := by
    have h1 := one_add_fctUc_le hc
    have hc0_eq : c ^ (-(1 / 12 : ℝ)) * c ^ ((1 : ℝ) / 12) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    calc 8 * c ^ (-(1 / 12 : ℝ)) * (1 + fctUc c)
        ≤ 8 * c ^ (-(1 / 12 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 32 * (c ^ (-(1 / 12 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ = 32 := by rw [hc0_eq, mul_one]
  have hsym := FctSymClsOn.comp_T_zero hUc0 (by norm_num : (1 : ℝ) ≤ 32) hDu36 hg_cd
    (by positivity) hg_bd hYcd hmaps (by positivity) hBfM (fun j hj1 hj8 u hu => (hYd j hj1 hj8 u hu).1)
  refine hsym.mono_B Icc_subset_Ici_self (le_of_eq ?_)
  ring

lemma fctInner_V_sq_sub_V0_sym {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ}, 1 ≤ c → K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C * K * c ^ (-(1 / 2 : ℝ)))
          (fun u => ((V (fctInnerY c u) ^ 2 - V 0 ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨C1, hC10, hSub⟩ := fctInner_V_sub_tauStar_sym hK
  set C_sq : ℝ := 2 * (2 ^ 8 * C1 ^ 2 * 0.001 + 2 * 1.068 * C1)
  refine ⟨C_sq, by positivity, fun {c} hc hη {V} hV => ?_⟩
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  have hS := hSub hc hV
  have hS2 := hS.mul Icc_subset_Ici_self hDu hS
  rw [zero_add] at hS2
  have hLin := hS.const_mul hDu (((2 * τs : ℝ) : ℂ))
  have hadd := hS2.add hDu hLin
  have h0_mem : (0 : ℝ) ∈ Icc 0 (fctUc c) := ⟨le_rfl, hUc0.le⟩
  have hY0 : fctInnerY c 0 = 0 := by unfold fctInnerY; simp
  have h0_bd : ‖((V 0 ^ 2 - τs ^ 2 : ℝ) : ℂ)‖ ≤ (2 ^ 8 * C1 ^ 2 * 0.001 + 2 * 1.068 * C1) * K * c ^ (-(1 / 2 : ℝ)) := by
    have h0 := hadd.2 0 (Nat.zero_le _) 0 h0_mem
    rw [iteratedDerivWithin_zero, hY0, Nat.cast_zero, sub_zero, add_zero, Real.rpow_zero, mul_one] at h0
    have heq : (((V 0 - τs : ℝ) : ℂ) * ((V 0 - τs : ℝ) : ℂ) + ((2 * τs : ℝ) : ℂ) * ((V 0 - τs : ℝ) : ℂ)) =
        ((V 0 ^ 2 - τs ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [heq] at h0
    refine h0.trans ?_
    have hτs0 : 0 ≤ τs := by positivity
    have hτs_norm : ‖((2 * τs : ℝ) : ℂ)‖ ≤ 2 * 1.068 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [tauStar_le_1068]
    have hc0_eq : (C1 * K * c ^ (-(1 / 2 : ℝ))) ^ 2 = C1 ^ 2 * (K * c ^ (-(1 / 2 : ℝ))) * K * c ^ (-(1 / 2 : ℝ)) := by ring
    calc 2 ^ 8 * (C1 * K * c ^ (-(1 / 2 : ℝ))) * (C1 * K * c ^ (-(1 / 2 : ℝ))) +
          ‖((2 * τs : ℝ) : ℂ)‖ * (C1 * K * c ^ (-(1 / 2 : ℝ)))
        = 2 ^ 8 * (C1 * K * c ^ (-(1 / 2 : ℝ))) ^ 2 + ‖((2 * τs : ℝ) : ℂ)‖ * (C1 * K * c ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 2 ^ 8 * (C1 ^ 2 * 0.001 * K * c ^ (-(1 / 2 : ℝ))) + (2 * 1.068) * (C1 * K * c ^ (-(1 / 2 : ℝ))) := by
          rw [hc0_eq]; gcongr
      _ = (2 ^ 8 * C1 ^ 2 * 0.001 + 2 * 1.068 * C1) * K * c ^ (-(1 / 2 : ℝ)) := by ring
  have hY_sq : FctSymClsOn (Icc 0 (fctUc c)) 8 0 ((2 ^ 8 * C1 ^ 2 * 0.001 + 2 * 1.068 * C1) * K * c ^ (-(1 / 2 : ℝ)))
      (fun u => ((V (fctInnerY c u) ^ 2 - τs ^ 2 : ℝ) : ℂ)) := by
    have hcon := hadd.congr hDu (fun u _ => show ((V (fctInnerY c u) ^ 2 - τs ^ 2 : ℝ) : ℂ) = _ by push_cast; ring)
    refine hcon.mono_B Icc_subset_Ici_self ?_
    have hτs_norm : ‖((2 * τs : ℝ) : ℂ)‖ ≤ 2 * 1.068 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [tauStar_le_1068]
    have hc0_eq : (C1 * K * c ^ (-(1 / 2 : ℝ))) ^ 2 = C1 ^ 2 * (K * c ^ (-(1 / 2 : ℝ))) * K * c ^ (-(1 / 2 : ℝ)) := by ring
    calc 2 ^ 8 * (C1 * K * c ^ (-(1 / 2 : ℝ))) * (C1 * K * c ^ (-(1 / 2 : ℝ))) +
          ‖((2 * τs : ℝ) : ℂ)‖ * (C1 * K * c ^ (-(1 / 2 : ℝ)))
        = 2 ^ 8 * (C1 * K * c ^ (-(1 / 2 : ℝ))) ^ 2 + ‖((2 * τs : ℝ) : ℂ)‖ * (C1 * K * c ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 2 ^ 8 * (C1 ^ 2 * 0.001 * K * c ^ (-(1 / 2 : ℝ))) + (2 * 1.068) * (C1 * K * c ^ (-(1 / 2 : ℝ))) := by
          rw [hc0_eq]; gcongr
      _ = (2 ^ 8 * C1 ^ 2 * 0.001 + 2 * 1.068 * C1) * K * c ^ (-(1 / 2 : ℝ)) := by ring
  have hconst := (FctSymClsOn.const (D := Icc 0 (fctUc c)) Icc_subset_Ici_self 8
    ((V 0 ^ 2 - τs ^ 2 : ℝ) : ℂ)).mono_B Icc_subset_Ici_self h0_bd
  have hsub := hY_sq.sub hDu hconst
  refine (hsub.congr hDu fun u _ => by push_cast; ring).mono_B Icc_subset_Ici_self (le_of_eq ?_)
  dsimp only [C_sq]; ring

lemma fctInner_V_sub_VA_sym {K C_A : ℝ} (hK : 0 ≤ K) (_hCA : 0 ≤ C_A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c A : ℝ}, 1 ≤ c → A ∈ Icc (0 : ℝ) 3.6 →
      (∀ u ∈ Icc 0 (fctUc c), |fctInnerY c u - A| ≤ C_A * c ^ (-(1 / 6 : ℝ)) * (1 + u) ^ 2) →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C * K * c ^ (-(2 / 3 : ℝ)))
          (fun u => ((V (fctInnerY c u) - V A : ℝ) : ℂ)) := by
  set M_Y : ℝ := max 1 4
  set C_all : ℝ := (Nat.factorial 8 : ℝ) * max C_A (16 ^ 7) * 4 ^ 8
  refine ⟨C_all, by positivity, fun {c A} hc hA hYA {V} hV => ?_⟩
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  have hDu36 : UniqueDiffOn ℝ (Icc (0 : ℝ) 3.6) := uniqueDiffOn_Icc (by norm_num)
  obtain ⟨hYcd, _, hYd⟩ := fctInnerY_deriv_bounds hc
  have hmaps : MapsTo (fctInnerY c) (Icc 0 (fctUc c)) (Icc (0 : ℝ) 3.6) := fun u hu =>
    have h := fctInnerY_mem_35 hc hu; ⟨h.1, by linarith [h.2]⟩
  have hcd_VA : ContDiffOn ℝ 8 (fun y : ℝ => ((V y - V A : ℝ) : ℂ)) (Icc (0 : ℝ) 3.6) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((hV.1.of_le (by norm_num)).sub contDiffOn_const)
  have hcd_main : ContDiffOn ℝ 8 (fun u => ((V (fctInnerY c u) - V A : ℝ) : ℂ)) (Icc 0 (fctUc c)) :=
    hcd_VA.comp hYcd hmaps
  refine ⟨hcd_main, fun r hr u hu => ?_⟩
  have h1u0 : 0 < 1 + u := by linarith [hu.1]
  have h1u_le : 1 + u ≤ 4 * c ^ ((1 : ℝ) / 12) := by
    have := one_add_fctUc_le hc; linarith [hu.2]
  set R₀ : ℝ := 1 + u
  set Scl : ℝ := c ^ (-(1 / 6 : ℝ)) * R₀ ^ 2
  have hScl0 : 0 < Scl := mul_pos (Real.rpow_pos_of_pos hc0 _) (sq_pos_of_pos h1u0)
  have hScl16 : Scl ≤ 16 := by
    have hsq : R₀ ^ 2 ≤ 16 * c ^ ((1 : ℝ) / 6) := by
      have h16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
        rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
      calc R₀ ^ 2 ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ h1u0.le h1u_le 2
        _ = 16 * (c ^ ((1 : ℝ) / 12)) ^ 2 := by ring
        _ = 16 * c ^ ((1 : ℝ) / 6) := by rw [h16]
    have hc_prod : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    calc Scl ≤ c ^ (-(1 / 6 : ℝ)) * (16 * c ^ ((1 : ℝ) / 6)) := by dsimp only [Scl]; gcongr
      _ = 16 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
      _ = 16 := by rw [hc_prod, mul_one]
  let ψ : ℝ → ℝ := fun v => u + R₀ * v
  let S : Set ℝ := ψ ⁻¹' Icc 0 (fctUc c)
  have hSu : UniqueDiffOn ℝ S := by
    have hpre : ψ ⁻¹' Icc 0 (fctUc c) = Icc (-u / R₀) ((fctUc c - u) / R₀) := by
      ext v; simp only [mem_preimage, mem_Icc, ψ]
      constructor <;> intro ⟨h1, h2⟩ <;> constructor
      · rw [div_le_iff₀ h1u0]; linarith
      · rw [le_div_iff₀ h1u0]; linarith
      · rw [div_le_iff₀ h1u0] at h1; linarith
      · rw [le_div_iff₀ h1u0] at h2; linarith
    dsimp only [S]; rw [hpre]; exact uniqueDiffOn_Icc (by rw [div_lt_div_iff_of_pos_right h1u0]; linarith)
  have hu_aff : u + R₀ * 0 ∈ Icc 0 (fctUc c) := by simpa using hu
  have h0S : (0 : ℝ) ∈ S := hu_aff
  have hψ_maps : MapsTo ψ S (Icc 0 (fctUc c)) := fun _ hv => hv
  have hψ_cd : ContDiffOn ℝ 8 ψ S := (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  let φ : ℝ → ℝ := fun w => fctInnerY c u + Scl * w
  let E_G : Set ℝ := φ ⁻¹' Icc (0 : ℝ) 3.6
  have hEGu : UniqueDiffOn ℝ E_G := by
    have hpre : E_G = Icc (-fctInnerY c u / Scl) ((3.6 - fctInnerY c u) / Scl) := by
      ext w; simp only [E_G, mem_preimage, mem_Icc, φ]
      constructor <;> intro ⟨h1, h2⟩ <;> constructor
      · rw [div_le_iff₀ hScl0]; linarith
      · rw [le_div_iff₀ hScl0]; linarith
      · rw [div_le_iff₀ hScl0] at h1; linarith
      · rw [le_div_iff₀ hScl0] at h2; linarith
    rw [hpre]; exact uniqueDiffOn_Icc (by rw [div_lt_div_iff_of_pos_right hScl0]; norm_num)
  let H : ℝ → ℝ := fun v => Scl⁻¹ * (fctInnerY c (ψ v) - fctInnerY c u)
  let G : ℝ → ℂ := fun w => ((V (φ w) - V A : ℝ) : ℂ)
  have hH_cd : ContDiffOn ℝ 8 H S :=
    contDiffOn_const.mul ((hYcd.comp hψ_cd hψ_maps).sub contDiffOn_const)
  have hφ_maps : MapsTo φ E_G (Icc (0 : ℝ) 3.6) := fun _ hw => hw
  have hφ_cd : ContDiffOn ℝ 8 φ E_G := (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  have hG_cd : ContDiffOn ℝ 8 G E_G := hcd_VA.comp hφ_cd hφ_maps
  have hmaps_H : MapsTo H S E_G := fun v hv => by
    show fctInnerY c u + Scl * (Scl⁻¹ * (fctInnerY c (ψ v) - fctInnerY c u)) ∈ Icc (0 : ℝ) 3.6
    rw [mul_inv_cancel_left₀ hScl0.ne', add_sub_cancel]
    exact hmaps (hψ_maps hv)
  have hH0 : H 0 = 0 := by simp [H, ψ]
  have hH_bd : ∀ j : ℕ, 1 ≤ j → j ≤ r → ‖iteratedFDerivWithin ℝ j H S 0‖ ≤ 4 ^ j := by
    intro j hj1 hjr
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have hHeq : H = (fun v => Scl⁻¹ * (fctInnerY c ∘ ψ) v) - fun _ : ℝ => Scl⁻¹ * fctInnerY c u := by
      ext v; simp [H, mul_sub]
    have hs1 : ContDiffWithinAt ℝ j (fun v => Scl⁻¹ * (fctInnerY c ∘ ψ) v) S 0 :=
      (contDiffWithinAt_const.mul ((hYcd.comp hψ_cd hψ_maps).contDiffWithinAt h0S)).of_le
        (by exact_mod_cast (hjr.trans hr))
    have hs2 : ContDiffWithinAt ℝ j (fun _ : ℝ => Scl⁻¹ * fctInnerY c u) S 0 := contDiffWithinAt_const
    rw [hHeq, iteratedDerivWithin_sub h0S hSu hs1 hs2, iteratedDerivWithin_const,
      show (if j = 0 then Scl⁻¹ * fctInnerY c u else 0) = 0 by simp only [show j ≠ 0 by omega, ↓reduceIte],
      sub_zero, iteratedDerivWithin_const_mul h0S hSu Scl⁻¹
        (((hYcd.comp hψ_cd hψ_maps).contDiffWithinAt h0S).of_le (by exact_mod_cast (hjr.trans hr))),
      Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hScl0),
      iteratedDerivWithin_comp_affine hDu hSu hYcd (hjr.trans hr) hu_aff]
    simp only [mul_zero, add_zero, smul_eq_mul, abs_mul, abs_pow, abs_of_pos h1u0]
    have hYj := (hYd j hj1 (hjr.trans hr) u hu).2
    have hR2 : R₀ ^ j * (2 * c ^ (-(1 / 6 : ℝ)) * R₀ ^ ((2 : ℝ) - j)) = 2 * Scl := by
      have h1 : R₀ ^ ((2 : ℝ) - j) = R₀ ^ 2 * (R₀ ^ j)⁻¹ := by
        rw [Real.rpow_sub h1u0, Real.rpow_two, Real.rpow_natCast, div_eq_mul_inv]
      rw [h1]; dsimp only [Scl]; field_simp [h1u0.ne']
    have h4j : (2 : ℝ) ≤ 4 ^ j := le_trans (by norm_num) (le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega))
    calc Scl⁻¹ * (R₀ ^ j * |iteratedDerivWithin j (fctInnerY c) (Icc 0 (fctUc c)) u|)
        ≤ Scl⁻¹ * (R₀ ^ j * (2 * c ^ (-(1 / 6 : ℝ)) * R₀ ^ ((2 : ℝ) - j))) := by
          gcongr
      _ = 2 := by rw [hR2]; field_simp [hScl0.ne']
      _ ≤ 4 ^ j := h4j
  have hG_bd : ∀ i ≤ r, ‖iteratedFDerivWithin ℝ i G E_G (H 0)‖ ≤ max C_A (16 ^ 7) * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2) := by
    intro i hir
    rw [hH0, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have h0_mem_EG : (0 : ℝ) ∈ E_G := by simpa [E_G, φ] using hmaps hu
    have hGe := iteratedDerivWithin_comp_affine hDu36 hEGu hcd_VA (hir.trans hr) (u₀ := fctInnerY c u)
      (R₀ := Scl) (v := 0) (by simpa [φ] using hmaps hu)
    change iteratedDerivWithin i G E_G 0 = Scl ^ i • iteratedDerivWithin i (fun y => ((V y - V A : ℝ) : ℂ))
      (Icc (0 : ℝ) 3.6) (fctInnerY c u + Scl * 0) at hGe
    rw [mul_zero, add_zero] at hGe
    rw [hGe, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hScl0]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero, one_mul, iteratedDerivWithin_zero, Complex.norm_real, Real.norm_eq_abs]
      change |V (fctInnerY c u) - V A| ≤ _
      have hmvt : |(V (fctInnerY c u) - τs) - (V A - τs)| ≤
          (K * c ^ (-(1 / 2 : ℝ))) * |fctInnerY c u - A| := by
        refine Convex.norm_image_sub_le_of_norm_derivWithin_le (f := fun y => V y - τs)
          ((hV.1.sub contDiffOn_const).differentiableOn (by norm_num))
          (fun y hy => by
            have h1 := hV.2 1 (by norm_num) y hy
            rw [iteratedDerivWithin_one] at h1
            simpa [Real.norm_eq_abs] using h1)
          (convex_Icc (0 : ℝ) 3.6) hA (hmaps hu)
      have hsub_eq : (V (fctInnerY c u) - τs) - (V A - τs) = V (fctInnerY c u) - V A := by ring
      rw [hsub_eq] at hmvt
      have hc23 : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      calc |V (fctInnerY c u) - V A| ≤ K * c ^ (-(1 / 2 : ℝ)) * |fctInnerY c u - A| := hmvt
        _ ≤ K * c ^ (-(1 / 2 : ℝ)) * (C_A * c ^ (-(1 / 6 : ℝ)) * R₀ ^ 2) := by
            gcongr; exact hYA u hu
        _ = C_A * (K * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ))) * R₀ ^ 2) := by ring
        _ = C_A * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2) := by rw [hc23]
        _ ≤ max C_A (16 ^ 7) * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2) := by gcongr; exact le_max_left _ _
    · have hreal : iteratedDerivWithin i (fun y => ((V y - V A : ℝ) : ℂ)) (Icc (0 : ℝ) 3.6) (fctInnerY c u) =
          ((iteratedDerivWithin i (fun y => V y - τs) (Icc (0 : ℝ) 3.6) (fctInnerY c u) : ℝ) : ℂ) := by
        have hy_mem := hmaps hu
        have hVA_cd : ContDiffOn ℝ 8 (fun y => V y - V A) (Icc (0 : ℝ) 3.6) :=
          (hV.1.of_le (by norm_num : ((8 : ℕ) : WithTop ℕ∞) ≤ 14)).sub contDiffOn_const
        have hVt_cd : ContDiffOn ℝ 8 (fun y => V y - τs) (Icc (0 : ℝ) 3.6) :=
          (hV.1.of_le (by norm_num : ((8 : ℕ) : WithTop ℕ∞) ≤ 14)).sub contDiffOn_const
        rw [iteratedDerivWithin_ofReal_cast hDu36 hVA_cd (by omega : i ≤ 8) (fctInnerY c u) hy_mem]
        congr 1
        have hsplit : (fun y => V y - V A) = (fun y => V y - τs) + fun _ : ℝ => τs - V A := by
          ext y; simp only [Pi.add_apply]; ring
        have hcd_f1 : ContDiffWithinAt ℝ i (fun y => V y - τs) (Icc (0 : ℝ) 3.6) (fctInnerY c u) :=
          (hVt_cd.contDiffWithinAt hy_mem).of_le (by exact_mod_cast (by omega : i ≤ 8))
        rw [hsplit, iteratedDerivWithin_add hy_mem hDu36 hcd_f1 contDiffWithinAt_const,
          iteratedDerivWithin_const,
          show (if i = 0 then τs - V A else 0) = 0 by simp only [hi0.ne', ↓reduceIte], add_zero]
      rw [hreal, Complex.norm_real, Real.norm_eq_abs]
      have hVi := hV.2 i (by omega) (fctInnerY c u) (hmaps hu)
      have hScl_split : Scl ^ i = Scl ^ (i - 1) * Scl := by
        conv_lhs => rw [← Nat.sub_add_cancel hi0, pow_succ]
      have hScl_pow : Scl ^ (i - 1) ≤ 16 ^ 7 := by
        calc Scl ^ (i - 1) ≤ 16 ^ (i - 1) := pow_le_pow_left₀ hScl0.le hScl16 _
          _ ≤ 16 ^ 7 := pow_le_pow_right₀ (by norm_num) (by omega)
      have hc23 : c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      calc Scl ^ i * |iteratedDerivWithin i (fun y => V y - τs) (Icc (0 : ℝ) 3.6) (fctInnerY c u)|
          ≤ Scl ^ i * (K * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hVi (pow_nonneg hScl0.le i)
        _ = Scl ^ (i - 1) * (K * (c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ))) * R₀ ^ 2) := by
            rw [hScl_split]; dsimp only [Scl]; ring
        _ = Scl ^ (i - 1) * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2) := by rw [hc23]
        _ ≤ 16 ^ 7 * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2) := by gcongr
        _ ≤ max C_A (16 ^ 7) * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2) := by
            gcongr; exact le_max_right _ _
  have hle := norm_iteratedFDerivWithin_comp_le (g := G) (f := H) (n := r) (N := 8)
    hG_cd hH_cd (by exact_mod_cast hr) hEGu hSu hmaps_H h0S
    (C := max C_A (16 ^ 7) * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2)) (D := 4)
    (fun i hi => hG_bd i hi) (fun i hi1 hir => hH_bd i hi1 hir)
  have hcomp_eq : (G ∘ H) = (fun u => ((V (fctInnerY c u) - V A : ℝ) : ℂ)) ∘ ψ := by
    ext v; simp only [G, H, φ, Function.comp]
    rw [mul_inv_cancel_left₀ hScl0.ne', add_sub_cancel]
  have hgf_aff : iteratedDerivWithin r (G ∘ H) S 0 =
      R₀ ^ r * iteratedDerivWithin r (fun u => ((V (fctInnerY c u) - V A : ℝ) : ℂ)) (Icc 0 (fctUc c)) u := by
    rw [hcomp_eq]
    have h := iteratedDerivWithin_comp_affine hDu hSu hcd_main hr hu_aff
    simpa [ψ, smul_eq_mul] using h
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at hle
  change ‖iteratedDerivWithin r (G ∘ H) S 0‖ ≤ _ at hle
  rw [hgf_aff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1u0] at hle
  have hpowr : (1 + u) ^ ((2 : ℝ) - r) = R₀ ^ 2 / R₀ ^ r := by
    rw [Real.rpow_sub h1u0, Real.rpow_natCast, Real.rpow_two]
  rw [hpowr]
  have hr_fac : (r.factorial : ℝ) ≤ Nat.factorial 8 := by exact_mod_cast Nat.factorial_le hr
  have h4r : (4 : ℝ) ^ r ≤ 4 ^ 8 := pow_le_pow_right₀ (by norm_num) hr
  have hCg0 : 0 ≤ max C_A (16 ^ 7) * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2) := by positivity
  have hbound : R₀ ^ r * ‖iteratedDerivWithin r (fun u => ((V (fctInnerY c u) - V A : ℝ) : ℂ)) (Icc 0 (fctUc c)) u‖ ≤
      R₀ ^ r * (C_all * K * c ^ (-(2 / 3 : ℝ)) * (R₀ ^ 2 / R₀ ^ r)) := by
    have heq : R₀ ^ r * (C_all * K * c ^ (-(2 / 3 : ℝ)) * (R₀ ^ 2 / R₀ ^ r)) =
        (Nat.factorial 8 : ℝ) * (max C_A (16 ^ 7) * (K * c ^ (-(2 / 3 : ℝ)) * R₀ ^ 2)) * 4 ^ 8 := by
      dsimp only [C_all]; field_simp [h1u0.ne']
    rw [heq]
    exact hle.trans (mul_le_mul (mul_le_mul_of_nonneg_right hr_fac hCg0) h4r (by positivity) (by positivity))
  exact le_of_mul_le_mul_left hbound (pow_pos h1u0 r)

/-! ### Smooth extension of `ChartSetup` slice `V₀` on `(-1/5, 3.6)` to `FctVJets` on `[0, 3.6]` -/

lemma tauStar_eq_dStar_inv : τs = dStar⁻¹ := by
  have hd0 : 0 < dStar := lt_trans (by norm_num) dStar_bounds.1
  have hτ0 : 0 < τs := by positivity
  have h1 : τs ^ 3 = 12 / π ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have h2 : (dStar⁻¹) ^ 3 = 12 / π ^ 2 := by
    have hcube : dStar ^ 3 = π ^ 2 / 12 := by
      have hc0 := dRoot_cube (s := 0) (by rw [mul_zero, sub_zero]; positivity)
      simpa [dRoot_zero] using hc0
    rw [inv_pow, hcube]; field_simp
  have h3 : (τs - dStar⁻¹) * (τs ^ 2 + τs * dStar⁻¹ + (dStar⁻¹) ^ 2) = 0 := by
    calc (τs - dStar⁻¹) * (τs ^ 2 + τs * dStar⁻¹ + (dStar⁻¹) ^ 2) = τs ^ 3 - (dStar⁻¹) ^ 3 := by ring
      _ = 0 := by rw [h1, h2, sub_self]
  have hpos : 0 < τs ^ 2 + τs * dStar⁻¹ + (dStar⁻¹) ^ 2 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hpos.ne')

/-- Smooth clamp `[0, 3.6] → [0, 3.55]` that is the identity on `[0, 3.5]`. -/
noncomputable def clampY (y : ℝ) : ℝ :=
  3.5 + (1 - Real.smoothTransition ((y - 3.5) / 0.05)) * (y - 3.5)

lemma clampY_eq_self {y : ℝ} (hy : y ≤ 3.5) : clampY y = y := by
  unfold clampY
  have h : (y - 3.5) / 0.05 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)
  rw [Real.smoothTransition.zero_of_nonpos h, sub_zero, one_mul]; ring

lemma clampY_mem_Yint {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 3.6) : clampY y ∈ Yint := by
  unfold clampY Yint
  have hs0 : 0 ≤ Real.smoothTransition ((y - 3.5) / 0.05) := Real.smoothTransition.nonneg _
  have hs1 : Real.smoothTransition ((y - 3.5) / 0.05) ≤ 1 := Real.smoothTransition.le_one _
  rcases le_or_gt y 3.5 with hle | hgt
  · have h : (y - 3.5) / 0.05 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)
    rw [Real.smoothTransition.zero_of_nonpos h, sub_zero, one_mul]
    exact ⟨by linarith [hy.1], by linarith⟩
  · rcases lt_or_ge y 3.55 with hlt | hge
    · have hpos : 0 ≤ (1 - Real.smoothTransition ((y - 3.5) / 0.05)) * (y - 3.5) :=
        mul_nonneg (sub_nonneg.mpr hs1) (by linarith)
      have h1 : 1 - Real.smoothTransition ((y - 3.5) / 0.05) ≤ 1 := sub_le_self _ hs0
      have hhi : (1 - Real.smoothTransition ((y - 3.5) / 0.05)) * (y - 3.5) < 0.05 :=
        calc (1 - Real.smoothTransition ((y - 3.5) / 0.05)) * (y - 3.5)
            ≤ 1 * (y - 3.5) := mul_le_mul_of_nonneg_right h1 (by linarith)
          _ < 0.05 := by linarith
      exact ⟨by linarith, by linarith⟩
    · have h1 : 1 ≤ (y - 3.5) / 0.05 := by rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.05)]; linarith
      rw [Real.smoothTransition.one_of_one_le h1, sub_self, zero_mul, add_zero]
      constructor <;> norm_num

lemma clampY_contDiff : ContDiff ℝ 16 clampY := by
  unfold clampY
  exact contDiff_const.add ((contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const 0.05))).mul
      (contDiff_id.sub contDiff_const))

lemma fctVJets_of_chartV :
    ∃ C_ext : ℝ, 0 < C_ext ∧ ∀ {c K₀ : ℝ}, 0 < c → 0 ≤ K₀ →
      ∀ {V₀ : ℝ → ℝ}, JC 16 Yint (fun y => V₀ y - τs) (K₀ * c ^ (-(1 / 2 : ℝ))) →
        FctVJets (C_ext * K₀) c (fun y => V₀ (clampY y)) ∧
        (∀ y ∈ Icc (0 : ℝ) 3.5, V₀ (clampY y) = V₀ y) := by
  have hDu : UniqueDiffOn ℝ (Icc (0 : ℝ) 3.6) := uniqueDiffOn_Icc (by norm_num)
  have hbdd : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (1 ≤ j → j ≤ 14 →
      ∀ y ∈ Icc (0 : ℝ) 3.6, ‖iteratedFDerivWithin ℝ j clampY (Icc (0 : ℝ) 3.6) y‖ ≤ B) := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ 14
    · have hj16 : ((j : ℕ) : WithTop ℕ∞) ≤ (16 : ℕ) := by norm_cast; exact hj.2.trans (by norm_num)
      have hcont : ContinuousOn (iteratedFDerivWithin ℝ j clampY (Icc (0 : ℝ) 3.6)) (Icc (0 : ℝ) 3.6) :=
        ((clampY_contDiff.contDiffOn.of_le hj16).continuousOn_iteratedFDerivWithin le_rfl hDu)
      obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 3.6)).exists_bound_of_continuousOn hcont
      exact ⟨max B 0, le_max_right _ _, fun _ _ y hy => (hB y hy).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h1 h14 => absurd ⟨h1, h14⟩ hj⟩
  choose B hB0 hB using hbdd
  set B_cl : ℝ := max 1 (∑ j ∈ Finset.range 15, B j)
  have hBcl1 : 1 ≤ B_cl := le_max_left _ _
  set C_ext : ℝ := (Nat.factorial 14 : ℝ) * B_cl ^ 14
  refine ⟨C_ext, by positivity, fun {c K₀} hc hK0 {V₀} hV0 => ?_⟩
  have hmap : MapsTo clampY (Icc (0 : ℝ) 3.6) Yint := fun y hy => clampY_mem_Yint hy
  have hg : ContDiffOn ℝ 14 (fun y => V₀ y - τs) Yint := hV0.1.of_le (by norm_num)
  have hV_ext_sub : ContDiffOn ℝ 14 (fun y => V₀ (clampY y) - τs) (Icc (0 : ℝ) 3.6) :=
    hg.comp (clampY_contDiff.contDiffOn.of_le (by norm_num)) hmap
  have hV_ext : ContDiffOn ℝ 14 (fun y => V₀ (clampY y)) (Icc (0 : ℝ) 3.6) :=
    (hV_ext_sub.add contDiffOn_const).congr fun y _ => by ring
  have hjb := JB.comp (k := 14) hDu isOpen_Ioo.uniqueDiffOn (g := fun y => V₀ y - τs)
    hg (clampY_contDiff.contDiffOn.of_le (by norm_num)) hmap (by positivity)
    (fun y hy i hi => hV0.2 i (by omega) (clampY y) (hmap hy))
    (fun i hi1 hi14 y hy => (hB i hi1 hi14 y hy).trans
      ((Finset.single_le_sum (fun k _ => hB0 k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi14))).trans
        (le_max_right (1 : ℝ) _)))
  refine ⟨⟨hV_ext, fun j hj y hy => ?_⟩, fun y hy => by rw [clampY_eq_self hy.2]⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  exact (hjb j hj y hy).trans (le_of_eq (by rw [max_eq_right hBcl1]; dsimp only [C_ext]; ring))


/-- info: 'FormalResearch.SignUncertainty.fctInner_V_sub_VA_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInner_V_sub_VA_sym

/-- info: 'FormalResearch.SignUncertainty.fctVJets_of_chartV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctVJets_of_chartV

end FormalResearch.SignUncertainty
