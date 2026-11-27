/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerFactorsA
public import FormalResearch.SignUncertainty.FctInnerPhase
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Inner symbol bounds Part B (`v₁`, `ϑ^{(1)}`, `V`-differences, and smooth `V` extension)

For `FctVJets K c V` on `[0, U_c]` (`U_c = 2.96 c^{1/12}`):
* `fctInnerT_le_two_tau1`: `0 ≤ T(u) ≤ 2 τ₁`;
* `fctInner_v1_sym`: `v₁(T(u)) ∈ S⁸(C c^{-17/12})`;
* `fctInner_theta1_sym`: `i c^{2/3} ϑ^{(1)}(T(u)) ∈ S^{11}(C c^{-3/4})`;
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

/-- `Y(c, u) = 2^{-4/3} c^{-1/6} u²`. -/
noncomputable def fctInnerY (c u : ℝ) : ℝ :=
  2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2

private lemma fctInnerY_mem_35 {c u : ℝ} (hc : 1 ≤ c) (hu : u ∈ Icc 0 (fctUc c)) :
    fctInnerY c u ∈ Icc (0 : ℝ) 3.5 := by
  have hc0 : 0 < c := by linarith
  have h16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
  have hu2 : u ^ 2 ≤ 2.96 ^ 2 * c ^ ((1 : ℝ) / 6) := by
    calc u ^ 2 ≤ (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
      _ = 2.96 ^ 2 * (c ^ ((1 : ℝ) / 12)) ^ 2 := by ring
      _ = 2.96 ^ 2 * c ^ ((1 : ℝ) / 6) := by rw [h16]
  have hc_prod : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
    rw [← Real.rpow_add hc0]; norm_num
  have hmle : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 0.3969 := fctB2_two_rpow_neg43_le
  refine ⟨by unfold fctInnerY; exact mul_nonneg (by positivity) (sq_nonneg u), ?_⟩
  calc fctInnerY c u
      ≤ 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (2.96 ^ 2 * c ^ ((1 : ℝ) / 6)) := by
        unfold fctInnerY; gcongr
    _ = 2 ^ (-(4 / 3 : ℝ)) * 2.96 ^ 2 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
    _ = 2 ^ (-(4 / 3 : ℝ)) * 2.96 ^ 2 := by rw [hc_prod, mul_one]
    _ ≤ 0.3969 * 2.96 ^ 2 := by gcongr
    _ ≤ 3.5 := by norm_num

private lemma tauStar_le_1068 : τs ≤ 1.068 := by
  have hpi2 : (3.14 : ℝ) ^ 2 < π ^ 2 := by
    have := Real.pi_gt_d2; nlinarith
  have h12 : 12 / π ^ 2 < 12 / 3.14 ^ 2 :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) hpi2
  have hc3 : τs ^ 3 = 12 / π ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  by_contra hgt; push Not at hgt
  have : (1.068 : ℝ) ^ 3 < τs ^ 3 := pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
  rw [hc3] at this; linarith

lemma fctInnerT_le_two_tau1 {K : ℝ} (_hK : 0 ≤ K) {c : ℝ} (hc : 1 ≤ c)
    (hη : K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001) {V : ℝ → ℝ} (hV : FctVJets K c V)
    {u : ℝ} (hu : u ∈ Icc 0 (fctUc c)) :
    0 ≤ fctInnerT c V u ∧ fctInnerT c V u ≤ 2 * fctTau1 c := by
  have hc0 : 0 < c := by linarith
  have hY35 := fctInnerY_mem_35 hc hu
  have hY36 : fctInnerY c u ∈ Icc (0 : ℝ) 3.6 := ⟨hY35.1, by linarith [hY35.2]⟩
  have hVb := abs_le.mp (hV.2 0 (Nat.zero_le _) (fctInnerY c u) hY36)
  rw [iteratedDerivWithin_zero] at hVb
  have hV_eq : V (2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2) = V (fctInnerY c u) := rfl
  have hτs_ge : (1 : ℝ) ≤ τs := by
    have hpi2 : π ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    exact Real.one_le_rpow ((one_le_div (by positivity)).mpr hpi2.le) (by norm_num)
  have hV0 : 0 ≤ V (fctInnerY c u) := by linarith [hVb.1, hη, hτs_ge]
  have hVhi : V (fctInnerY c u) ≤ 1.069 := by linarith [hVb.2, hη, tauStar_le_1068]
  have h23 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 0.63 := fctB2_two_rpow_neg23_le
  have hc_prod : c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = fctTau1 c := by
    unfold fctTau1; rw [← Real.rpow_add hc0]; congr 1; norm_num
  refine ⟨by unfold fctInnerT; exact mul_nonneg (by have := hu.1; positivity) hV0, ?_⟩
  unfold fctInnerT
  rw [hV_eq]
  calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * V (fctInnerY c u)
      ≤ 0.63 * c ^ (-(1 / 3 : ℝ)) * (2.96 * c ^ ((1 : ℝ) / 12)) * 1.069 := by
        have h23_nn : 0 ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
        have huc : u ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu.2
        gcongr; exact hu.1
    _ = (0.63 * 2.96 * 1.069) * (c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
    _ = (0.63 * 2.96 * 1.069) * fctTau1 c := by rw [hc_prod]
    _ ≤ 2 * fctTau1 c := by
        have hτ1_0 : 0 ≤ fctTau1 c := by unfold fctTau1; positivity
        linarith

private lemma contDiffOn_Ioo_bdd_on_half {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} (hR : 0 < R) {n : ℕ} {g : ℝ → F} (hg : ContDiffOn ℝ n g (Ioo (-R) R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ t ∈ Ioo (-(R / 2)) (R / 2),
      ‖iteratedDerivWithin i g (Ioo (-(R / 2)) (R / 2)) t‖ ≤ C := by
  have hsub : Icc (-(R / 2)) (R / 2) ⊆ Ioo (-R) R := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub' : Ioo (-(R / 2)) (R / 2) ⊆ Icc (-(R / 2)) (R / 2) := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hcd_k : ∀ k : ℕ, k ≤ n →
      ContDiffOn ℝ ((n - k : ℕ) : WithTop ℕ∞) (iteratedDerivWithin k g (Ioo (-R) R)) (Ioo (-R) R) := by
    intro k
    induction k with
    | zero => intro _; simpa using hg
    | succ k ih =>
      intro hk
      have hprev := ih (Nat.le_of_succ_le hk)
      have hsplit : ((n - k : ℕ) : WithTop ℕ∞) = (((n - (k + 1) : ℕ) : ℕ∞) + 1 : ℕ∞) := by
        have hn : n - k = (n - (k + 1)) + 1 := by omega
        rw [hn]; push_cast; rfl
      rw [hsplit] at hprev
      have hd := hprev.derivWithin (m := ((n - (k + 1) : ℕ) : ℕ∞)) isOpen_Ioo.uniqueDiffOn
        (by rw [← WithTop.coe_one, ← WithTop.coe_add])
      simpa [iteratedDerivWithin_succ] using hd.of_le (by norm_cast)
  have hbd : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (k ≤ n → ∀ t ∈ Icc (-(R / 2)) (R / 2), ‖iteratedDeriv k g t‖ ≤ B) := by
    intro k
    by_cases hk : k ≤ n
    · obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(R / 2)) (b := R / 2)).exists_bound_of_continuousOn
        ((hcd_k k hk).continuousOn.mono hsub)
      refine ⟨max B 0, le_max_right _ _, fun _ t ht => ?_⟩
      rw [← iteratedDerivWithin_of_isOpen isOpen_Ioo (hsub ht)]
      exact (hB t ht).trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun hkn => absurd hkn hk⟩
  choose B hB0 hB using hbd
  refine ⟨∑ i ∈ Finset.range (n + 1), B i, Finset.sum_nonneg fun i _ => hB0 i, fun i hi t ht => ?_⟩
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioo ht]
  exact (hB i hi t (hsub' ht)).trans (Finset.single_le_sum (fun k _ => hB0 k) (Finset.mem_range.mpr (by omega)))

private lemma invMD_invMQ_bdd :
    ∃ C_mD C_mQ : ℝ, 0 ≤ C_mD ∧ 0 ≤ C_mQ ∧
      ContDiffOn ℝ 8 (fun t : ℝ => ((mD t : ℝ) : ℂ)⁻¹) (Ioo (-(1 / 8 : ℝ)) (1 / 8)) ∧
      ContDiffOn ℝ 8 (fun t : ℝ => ((mQ t : ℝ) : ℂ)⁻¹) (Ioo (-(1 / 8 : ℝ)) (1 / 8)) ∧
      (∀ i ≤ 8, ∀ t ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8),
        ‖iteratedDerivWithin i (fun t : ℝ => ((mD t : ℝ) : ℂ)⁻¹) (Ioo (-(1 / 8 : ℝ)) (1 / 8)) t‖ ≤ C_mD) ∧
      (∀ i ≤ 8, ∀ t ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8),
        ‖iteratedDerivWithin i (fun t : ℝ => ((mQ t : ℝ) : ℂ)⁻¹) (Ioo (-(1 / 8 : ℝ)) (1 / 8)) t‖ ≤ C_mQ) := by
  have hle8 : (8 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hmD_cd : ContDiffOn ℝ 8 (fun t : ℝ => ((mD t : ℝ) : ℂ)⁻¹) (Ioo (-(1 / 4 : ℝ)) (1 / 4)) := by
    have h1 : ContDiffOn ℝ 8 (fun t : ℝ => ((mD t : ℝ) : ℂ)) (Ioo (-(1 / 4 : ℝ)) (1 / 4)) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_mD.of_le hle8)).mono
        fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact h1.inv fun t ht => Complex.ofReal_ne_zero.mpr (mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  have hmQ_cd : ContDiffOn ℝ 8 (fun t : ℝ => ((mQ t : ℝ) : ℂ)⁻¹) (Ioo (-(1 / 4 : ℝ)) (1 / 4)) := by
    have h1 : ContDiffOn ℝ 8 (fun t : ℝ => ((mQ t : ℝ) : ℂ)) (Ioo (-(1 / 4 : ℝ)) (1 / 4)) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_mQ.of_le hle8)).mono
        fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact h1.inv fun t ht => Complex.ofReal_ne_zero.mpr (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  obtain ⟨CmD, hCmD0, hCmD⟩ := contDiffOn_Ioo_bdd_on_half (by norm_num : (0 : ℝ) < 1 / 4) hmD_cd
  obtain ⟨CmQ, hCmQ0, hCmQ⟩ := contDiffOn_Ioo_bdd_on_half (by norm_num : (0 : ℝ) < 1 / 4) hmQ_cd
  have hsub : Ioo (-(1 / 8 : ℝ)) (1 / 8) ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h14_half : -(1 / 4 / 2 : ℝ) = -(1 / 8 : ℝ) ∧ (1 / 4 / 2 : ℝ) = 1 / 8 := by constructor <;> norm_num
  rw [h14_half.1, h14_half.2] at hCmD hCmQ
  exact ⟨CmD, CmQ, hCmD0, hCmQ0, hmD_cd.mono hsub, hmQ_cd.mono hsub, hCmD, hCmQ⟩

/-! ### `v₁(T) ∈ S⁸(C c^{-17/12})` -/

lemma fctInner_v1_sym {K : ℝ} (hK : 0 ≤ K) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ {K4 c α : ℝ}, 1 ≤ K4 → c₀ ≤ c →
      K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 → K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 → |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 8 (C * c ^ (-(17 / 12 : ℝ)))
          (fun u => ((v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) (fctInnerT c V u) : ℝ) : ℂ)) := by
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds hK
  obtain ⟨C_mD, C_mQ, hCmD0, hCmQ0, hmD_cd, hmQ_cd, hmD_bd, hmQ_bd⟩ := invMD_invMQ_bdd
  obtain ⟨τ_D, hτD0, hτD_20, _Cv0b, _Cv0m, _Cva, _Cv1b, _Cv1m, C_th0b, C_th0m, _Ctha, _Cth1b, _Cth1m,
    _CL0b, _CL0m, _CLa, _CL1b, _CL1m, _Ctail, _Cint, _hCv_nn, hCth_nn, _hCL_nn, _hCtail_nn, hDmain⟩ :=
    fct_comp_D_part1 StripKernelChoice.star
  set C_th3 : ℝ := ∑ i ∈ Finset.range 9, (C_th0b (3 + i) + C_th0m (3 + i))
  have hCth3_nn : 0 ≤ C_th3 := Finset.sum_nonneg fun i _ =>
    add_nonneg (hCth_nn (3 + i)).1 (hCth_nn (3 + i)).2.1
  set M_m : ℝ := max 1 (4 * B_T)
  set C_mD_sym : ℝ := (Nat.factorial 8 : ℝ) * C_mD * M_m ^ 8
  set C_mQ_sym : ℝ := (Nat.factorial 8 : ℝ) * C_mQ * M_m ^ 8
  set C_div_sym : ℝ := (Nat.factorial 8 : ℝ) * C_th3 * B_T ^ 8
  set C_all : ℝ := (1 / 2 : ℝ) * (2 ^ 8 * (C_div_sym * C_mD_sym + C_div_sym * C_mQ_sym))
  set c₀ : ℝ := max 1 (τ_D ^ (-4 : ℝ))
  refine ⟨C_all, c₀, by positivity, le_max_left _ _, fun {K4 c α} hK4 hc hK4c hη hα {V} hV => ?_⟩
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_le : τ₁ ≤ τ_D := by
    have hτDc : τ_D ^ (-4 : ℝ) ≤ c := (le_max_right _ _).trans hc
    calc τ₁ = c ^ (-(1 / 4 : ℝ)) := rfl
      _ ≤ (τ_D ^ (-4 : ℝ)) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτD0 _) hτDc (by norm_num)
      _ = τ_D := by rw [← Real.rpow_mul hτD0.le]; norm_num
  have hτ₁_20 : τ₁ ≤ 1 / 20 := hτ₁_le.trans hτD_20
  have hτ₁_12 : 3 * τ₁ ≤ 12 * τ₁ := by linarith
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hK4_τ₁ : K4 * τ₁ ^ 2 ≤ 1 := by rw [hτ₁_sq]; exact hK4c
  have hα_τ₁ : |α| ≤ τ₁ ^ 2 := by rw [hτ₁_sq]; exact hα
  obtain ⟨hTcd, _, hTderiv, _⟩ := hBT hc1 hη hV
  have hT_tau1 : ∀ u ∈ Icc 0 (fctUc c), 0 ≤ fctInnerT c V u ∧ fctInnerT c V u ≤ 2 * τ₁ :=
    fun u hu => fctInnerT_le_two_tau1 hK hc1 hη hV hu
  obtain ⟨hcd_v, _, _, hsupp_v, _, hinner, _, _, hth_in, _⟩ :=
    hDmain hK4 hc0 hτ₁_pos hτ₁_le hcτ hα_τ₁
  have hvb0_cs : HasCompactSupport (v0Base StripKernelChoice.star τ₁) := hsupp_v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvm0_cs : HasCompactSupport (v0Marg τ₁) := hsupp_v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hθ0b_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (v0Base StripKernelChoice.star τ₁)) :=
    contDiff_fctThetaD hcd_v.1 hvb0_cs
  have hθ0m_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (v0Marg τ₁)) :=
    contDiff_fctThetaD hcd_v.2.1 hvm0_cs
  let θ₀ : ℝ → ℝ := fctThetaD (v0 StripKernelChoice.star K4 τ₁)
  have hθ0_eq : ∀ t : ℝ, θ₀ t = fctThetaD (v0Base StripKernelChoice.star τ₁) t +
      K4 * fctThetaD (v0Marg τ₁) t := fun t => by
    have hlin := fctThetaD_linear hcd_v.1 hvb0_cs hcd_v.2.1 hvm0_cs 1 K4 t
    change fctThetaD (fun s => v0Base StripKernelChoice.star τ₁ s + K4 * v0Marg τ₁ s) t = _
    simpa only [one_mul] using hlin
  have hθ0_cd : ContDiff ℝ (⊤ : ℕ∞) θ₀ := by
    have heq : θ₀ = fun t => fctThetaD (v0Base StripKernelChoice.star τ₁) t +
        K4 * fctThetaD (v0Marg τ₁) t := funext hθ0_eq
    rw [heq]; exact hθ0b_cd.add (contDiff_const.mul hθ0m_cd)
  have hθ0_deriv_bd : ∀ i ≤ 8, ∀ t : ℝ, 0 ≤ t → t ≤ 3 * τ₁ →
      |iteratedDeriv (3 + i) θ₀ t| ≤ C_th3 * τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := by
    intro i hi t ht0 ht3
    have heq : θ₀ = fun s => fctThetaD (v0Base StripKernelChoice.star τ₁) s +
        K4 * fctThetaD (v0Marg τ₁) s := funext hθ0_eq
    have hd_sum : iteratedDeriv (3 + i) θ₀ t =
        iteratedDeriv (3 + i) (fctThetaD (v0Base StripKernelChoice.star τ₁)) t +
        K4 * iteratedDeriv (3 + i) (fctThetaD (v0Marg τ₁)) t := by
      have c1 : ContDiffAt ℝ (3 + i : ℕ) (fctThetaD (v0Base StripKernelChoice.star τ₁)) t :=
        hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have c2 : ContDiffAt ℝ (3 + i : ℕ) (fun s => K4 * fctThetaD (v0Marg τ₁) s) t :=
        (contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hc_fun : (fun s => fctThetaD (v0Base StripKernelChoice.star τ₁) s + K4 * fctThetaD (v0Marg τ₁) s) =
          fctThetaD (v0Base StripKernelChoice.star τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s := rfl
      rw [heq, hc_fun, iteratedDeriv_add c1 c2, iteratedDeriv_const_mul_field]
    have ht12 : |t| ≤ 12 * τ₁ := by rw [abs_of_nonneg ht0]; linarith
    obtain ⟨hb, hm, _, _, _⟩ := hth_in (3 + i) t ht12
    have hpow_min : min (1 : ℝ) ((|t| / τ₁) ^ (11 - (3 + i))) ≤ (t / τ₁) ^ (8 - i) := by
      rw [show 11 - (3 + i) = 8 - i by omega, abs_of_nonneg ht0]; exact min_le_right _ _
    have hpb : τ₁ ^ ((2 : ℤ) - ((3 + i : ℕ) : ℤ)) * (t / τ₁) ^ (8 - i) = τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := by
      rw [div_pow, ← zpow_natCast τ₁ (8 - i), div_eq_mul_inv, ← zpow_neg, mul_comm (t ^ (8 - i))]
      rw [← mul_assoc, ← zpow_add₀ hτ₁_pos.ne']
      congr 2; omega
    have hpm : K4 * (τ₁ ^ ((4 : ℤ) - ((3 + i : ℕ) : ℤ)) * (t / τ₁) ^ (8 - i)) ≤ τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := by
      have hpeq : τ₁ ^ ((4 : ℤ) - ((3 + i : ℕ) : ℤ)) * (t / τ₁) ^ (8 - i) =
          τ₁ ^ 2 * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by
        rw [div_pow, ← zpow_natCast τ₁ (8 - i), div_eq_mul_inv, ← zpow_neg, mul_comm (t ^ (8 - i))]
        rw [← zpow_natCast τ₁ 2, ← mul_assoc, ← mul_assoc, ← zpow_add₀ hτ₁_pos.ne',
          ← zpow_add₀ hτ₁_pos.ne']
        congr 2; omega
      rw [hpeq]
      calc K4 * (τ₁ ^ 2 * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)))
          = (K4 * τ₁ ^ 2) * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by ring
        _ ≤ 1 * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by gcongr
        _ = τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := one_mul _
    have hb' : |iteratedDeriv (3 + i) (fctThetaD (v0Base StripKernelChoice.star τ₁)) t| ≤
        C_th0b (3 + i) * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by
      calc _ ≤ C_th0b (3 + i) * τ₁ ^ ((2 : ℤ) - ((3 + i : ℕ) : ℤ)) * (t / τ₁) ^ (8 - i) :=
          hb.trans (mul_le_mul_of_nonneg_left hpow_min (mul_nonneg (hCth_nn (3 + i)).1 (zpow_nonneg hτ₁_pos.le _)))
        _ = C_th0b (3 + i) * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by rw [mul_assoc, hpb]
    have hm' : K4 * |iteratedDeriv (3 + i) (fctThetaD (v0Marg τ₁)) t| ≤
        C_th0m (3 + i) * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by
      have hm1 : |iteratedDeriv (3 + i) (fctThetaD (v0Marg τ₁)) t| ≤
          C_th0m (3 + i) * (τ₁ ^ ((4 : ℤ) - ((3 + i : ℕ) : ℤ)) * (t / τ₁) ^ (8 - i)) := by
        rw [← mul_assoc]
        exact hm.trans (mul_le_mul_of_nonneg_left hpow_min (mul_nonneg (hCth_nn (3 + i)).2.1 (zpow_nonneg hτ₁_pos.le _)))
      calc K4 * |iteratedDeriv (3 + i) (fctThetaD (v0Marg τ₁)) t|
          ≤ K4 * (C_th0m (3 + i) * (τ₁ ^ ((4 : ℤ) - ((3 + i : ℕ) : ℤ)) * (t / τ₁) ^ (8 - i))) :=
            mul_le_mul_of_nonneg_left hm1 (by linarith)
        _ = C_th0m (3 + i) * (K4 * (τ₁ ^ ((4 : ℤ) - ((3 + i : ℕ) : ℤ)) * (t / τ₁) ^ (8 - i))) := by ring
        _ ≤ C_th0m (3 + i) * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by gcongr; exact (hCth_nn (3 + i)).2.1
    have htri := abs_add_le (iteratedDeriv (3 + i) (fctThetaD (v0Base StripKernelChoice.star τ₁)) t)
      (K4 * iteratedDeriv (3 + i) (fctThetaD (v0Marg τ₁)) t)
    rw [abs_mul, abs_of_pos (by linarith : 0 < K4)] at htri
    have hci : C_th0b (3 + i) + C_th0m (3 + i) ≤ C_th3 :=
      Finset.single_le_sum (f := fun k => C_th0b (3 + k) + C_th0m (3 + k))
        (fun k _ => add_nonneg (hCth_nn (3 + k)).1 (hCth_nn (3 + k)).2.1)
        (Finset.mem_range.mpr (by omega))
    calc |iteratedDeriv (3 + i) θ₀ t|
        ≤ |iteratedDeriv (3 + i) (fctThetaD (v0Base StripKernelChoice.star τ₁)) t| +
            K4 * |iteratedDeriv (3 + i) (fctThetaD (v0Marg τ₁)) t| := by rw [hd_sum]; exact htri
      _ ≤ (C_th0b (3 + i) + C_th0m (3 + i)) * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by linarith
      _ ≤ C_th3 * (τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) := by gcongr
      _ = C_th3 * τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := by ring
  -- Apply `comp_T_pow` to `divT_theta2 θ₀` and `divT2_theta1 θ₀` on `E_τ = Ioo (-3 τ₁) (3 τ₁)`
  set E_τ : Set ℝ := Ioo (-3 * τ₁) (3 * τ₁)
  have hEτ_open : IsOpen E_τ := isOpen_Ioo
  have hT_maps_τ : MapsTo (fctInnerT c V) (Icc 0 (fctUc c)) E_τ := fun u hu =>
    ⟨by linarith [(hT_tau1 u hu).1], by linarith [(hT_tau1 u hu).2]⟩
  have hθ0_3_cd : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 3 θ₀) := by
    have hstep : ∀ {f : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) (deriv f) := fun {f} hf => by
      have hf1 : ContDiffOn ℝ (((⊤ : ℕ∞) + (1 : ℕ∞) : ℕ∞) : WithTop ℕ∞) f univ := hf.contDiffOn
      have hd := hf1.derivWithin (m := (⊤ : ℕ∞)) uniqueDiffOn_univ (by rw [← WithTop.coe_one, ← WithTop.coe_add])
      rw [derivWithin_univ] at hd
      exact contDiffOn_univ.mp hd
    have heq : iteratedDeriv 3 θ₀ = deriv (deriv (deriv θ₀)) := by
      ext x; simp [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [heq]; exact hstep (hstep (hstep hθ0_cd))
  have had_bd : ∀ (w : ℝ → ℝ), Continuous w → (∀ s ∈ Icc (0 : ℝ) 1, |w s| ≤ 1) →
      ∀ i ≤ 8, ∀ t ∈ E_τ, 0 ≤ t →
        ‖iteratedDerivWithin i (fun x => ((∫ s in (0 : ℝ)..1, w s * iteratedDeriv 3 θ₀ (s * x) : ℝ) : ℂ)) E_τ t‖ ≤
          C_th3 * τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := by
    intro w hw hw1 i hi t ht ht0
    have hcd_int : ContDiff ℝ 8 (fun x => ∫ s in (0 : ℝ)..1, w s * iteratedDeriv 3 θ₀ (s * x)) :=
      (contDiff_hadamard_integral hw hθ0_3_cd).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [iteratedDerivWithin_ofReal_cast hEτ_open.uniqueDiffOn hcd_int.contDiffOn hi t ht,
      Complex.norm_real, iteratedDerivWithin_of_isOpen hEτ_open ht,
      iteratedDeriv_hadamard_integral i hw hθ0_3_cd t]
    have heq_idx : ∀ s : ℝ, iteratedDeriv i (iteratedDeriv 3 θ₀) (s * t) = iteratedDeriv (3 + i) θ₀ (s * t) := by
      intro s; rw [iteratedDeriv_iteratedDeriv_eq, Nat.add_comm i 3]
    have hbd_in : ∀ s ∈ Icc (0 : ℝ) 1, ‖(w s * s ^ i) * iteratedDeriv i (iteratedDeriv 3 θ₀) (s * t)‖ ≤
        C_th3 * τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := by
      intro s hs
      have hst0 : 0 ≤ s * t := mul_nonneg hs.1 ht0
      have hst3 : s * t ≤ 3 * τ₁ := by
        calc s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs.2 ht0
          _ ≤ 3 * τ₁ := by linarith [ht.2]
      have hst_le_t : s * t ≤ t := by nlinarith [hs.2, ht0]
      have hws : |w s * s ^ i| ≤ 1 := by
        rw [abs_mul, abs_pow, abs_of_nonneg hs.1]
        have hs_pow : s ^ i ≤ 1 := pow_le_one₀ hs.1 hs.2
        calc |w s| * s ^ i ≤ 1 * 1 := mul_le_mul (hw1 s hs) hs_pow (pow_nonneg hs.1 i) zero_le_one
          _ = 1 := one_mul 1
      rw [Real.norm_eq_abs, abs_mul, heq_idx]
      have h3i := hθ0_deriv_bd i hi (s * t) hst0 hst3
      have hpow_st : (s * t) ^ (8 - i) ≤ t ^ (8 - i) := pow_le_pow_left₀ hst0 hst_le_t (8 - i)
      calc |w s * s ^ i| * |iteratedDeriv (3 + i) θ₀ (s * t)|
          ≤ 1 * (C_th3 * τ₁ ^ (-9 : ℤ) * (s * t) ^ (8 - i)) :=
            mul_le_mul hws h3i (abs_nonneg _) zero_le_one
        _ = C_th3 * τ₁ ^ (-9 : ℤ) * (s * t) ^ (8 - i) := one_mul _
        _ ≤ C_th3 * τ₁ ^ (-9 : ℤ) * t ^ (8 - i) := by gcongr
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := C_th3 * τ₁ ^ (-9 : ℤ) * t ^ (8 - i)) fun s hs => by
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
        exact hbd_in s ⟨hs.1.le, hs.2⟩
    simpa [Real.norm_eq_abs] using hint
  have hdiv1_real : ContDiff ℝ 8 (divT_theta2 θ₀) := by
    have h := (contDiff_hadamard_integral continuous_const hθ0_3_cd).of_le
      (m := ((8 : ℕ) : WithTop ℕ∞)) (WithTop.coe_le_coe.mpr le_top)
    simpa [divT_theta2] using h
  have hdiv2_real : ContDiff ℝ 8 (divT2_theta1 θ₀) := by
    have h := (contDiff_hadamard_integral (continuous_const.sub continuous_id) hθ0_3_cd).of_le
      (m := ((8 : ℕ) : WithTop ℕ∞)) (WithTop.coe_le_coe.mpr le_top)
    simpa [divT2_theta1] using h
  have hdiv1_cd : ContDiffOn ℝ 8 (fun t : ℝ => ((divT_theta2 θ₀ t : ℝ) : ℂ)) E_τ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hdiv1_real.contDiffOn
  have hdiv2_cd : ContDiffOn ℝ 8 (fun t : ℝ => ((divT2_theta1 θ₀ t : ℝ) : ℂ)) E_τ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hdiv2_real.contDiffOn
  have hdiv1_sym := FctSymClsOn.comp_T_pow hUc0 (by norm_num : 8 ≤ 8) hEτ_open hdiv1_cd
    (mul_nonneg hCth3_nn (zpow_nonneg hτ₁_pos.le _))
    (fun i hi t ht ht0 => by
      simpa [divT_theta2] using had_bd (fun _ => 1) continuous_const (fun _ _ => by norm_num) i hi t ht ht0)
    hTcd hT_maps_τ (by positivity)
    (fun u hu => ⟨(hT_tau1 u hu).1, by linarith [(hBT hc1 hη hV).2.1 u hu]⟩)
    (fun j hj1 hj8 u hu => hTderiv j hj1 hj8 u hu)
  have hdiv2_sym := FctSymClsOn.comp_T_pow hUc0 (by norm_num : 8 ≤ 8) hEτ_open hdiv2_cd
    (mul_nonneg hCth3_nn (zpow_nonneg hτ₁_pos.le _))
    (fun i hi t ht ht0 => by
      simpa [divT2_theta1] using had_bd (fun s => 1 - s) (continuous_const.sub continuous_id)
        (fun s hs => abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩) i hi t ht ht0)
    hTcd hT_maps_τ (by positivity)
    (fun u hu => ⟨(hT_tau1 u hu).1, by linarith [(hBT hc1 hη hV).2.1 u hu]⟩)
    (fun j hj1 hj8 u hu => hTderiv j hj1 hj8 u hu)
  have hBfM : B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c) ≤ M_m := by
    have hUc4 := one_add_fctUc_le hc1
    have hc14 : c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hc_le1 : c ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    calc B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c)
        ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 4 * B_T * (c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ ≤ 4 * B_T * 1 := by rw [hc14]; gcongr
      _ ≤ M_m := by rw [mul_one]; exact le_max_right _ _
  have hT_maps_m : MapsTo (fctInnerT c V) (Icc 0 (fctUc c)) (Ioo (-(1 / 8 : ℝ)) (1 / 8)) := fun u hu => by
    have h2 := hT_tau1 u hu
    exact ⟨by linarith, by linarith⟩
  have hinvMD_sym := FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_m) isOpen_Ioo.uniqueDiffOn
    hmD_cd hCmD0 hmD_bd hTcd hT_maps_m (by positivity) hBfM (fun j hj1 hj8 u hu => hTderiv j hj1 hj8 u hu)
  have hinvMQ_sym := FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_m) isOpen_Ioo.uniqueDiffOn
    hmQ_cd hCmQ0 hmQ_bd hTcd hT_maps_m (by positivity) hBfM (fun j hj1 hj8 u hu => hTderiv j hj1 hj8 u hu)
  have hterm1 := hdiv1_sym.mul Icc_subset_Ici_self hDu hinvMD_sym
  have hterm2 := hdiv2_sym.mul Icc_subset_Ici_self hDu hinvMQ_sym
  have hdiff := hterm1.sub hDu hterm2
  have hscaled := hdiff.const_mul hDu ((-(1 / (2 * c) : ℝ) : ℂ))
  have hpow_eq : (B_T * c ^ (-(1 / 3 : ℝ))) ^ 8 = B_T ^ 8 * c ^ (-(8 / 3 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
  have hτ9_eq : τ₁ ^ (-9 : ℤ) = c ^ (9 / 4 : ℝ) := by
    dsimp only [τ₁]
    rw [← Real.rpow_intCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
  have hc_exp : c⁻¹ * (c ^ (9 / 4 : ℝ) * c ^ (-(8 / 3 : ℝ))) = c ^ (-(17 / 12 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
  have hnorm_half : ‖((-(1 / (2 * c) : ℝ) : ℂ))‖ = (1 / 2 : ℝ) * c⁻¹ := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
  have hmain_eq : EqOn (fun u => ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c V u) : ℝ) : ℂ))
      (fun u => ((-(1 / (2 * c) : ℝ) : ℂ)) * (((divT_theta2 θ₀ ∘ fctInnerT c V) u : ℝ) *
        (((fun t => ((mD t : ℝ) : ℂ)⁻¹) ∘ fctInnerT c V) u) -
        ((divT2_theta1 θ₀ ∘ fctInnerT c V) u : ℝ) *
        (((fun t => ((mQ t : ℝ) : ℂ)⁻¹) ∘ fctInnerT c V) u))) (Icc 0 (fctUc c)) := by
    intro u hu
    have h2 := hT_tau1 u hu
    have hv1_eq := (hinner (fctInnerT c V u) (by rw [abs_of_nonneg h2.1]; exact h2.2)).2.2.2.1
    change ((v1 StripKernelChoice.star K4 c τ₁ (fctInnerT c V u) : ℝ) : ℂ) = _
    rw [hv1_eq, deltaCurvSmooth]
    simp only [Function.comp_apply, div_eq_mul_inv]
    push_cast; ring
  have hB_eq : ‖(-(1 / (2 * c) : ℝ) : ℂ)‖ *
      (2 ^ 8 * ((Nat.factorial 8 : ℝ) * (C_th3 * τ₁ ^ (-9 : ℤ)) * (B_T * c ^ (-(1 / 3 : ℝ))) ^ 8) * C_mD_sym +
       2 ^ 8 * ((Nat.factorial 8 : ℝ) * (C_th3 * τ₁ ^ (-9 : ℤ)) * (B_T * c ^ (-(1 / 3 : ℝ))) ^ 8) * C_mQ_sym) =
      C_all * c ^ (-(17 / 12 : ℝ)) := by
    rw [hnorm_half, hpow_eq, hτ9_eq]
    dsimp only [C_all, C_div_sym]
    calc (1 / 2 : ℝ) * c⁻¹ *
          (2 ^ 8 * ((Nat.factorial 8 : ℝ) * (C_th3 * c ^ (9 / 4 : ℝ)) * (B_T ^ 8 * c ^ (-(8 / 3 : ℝ)))) * C_mD_sym +
           2 ^ 8 * ((Nat.factorial 8 : ℝ) * (C_th3 * c ^ (9 / 4 : ℝ)) * (B_T ^ 8 * c ^ (-(8 / 3 : ℝ)))) * C_mQ_sym)
        = ((1 / 2 : ℝ) * (2 ^ 8 * (((Nat.factorial 8 : ℝ) * C_th3 * B_T ^ 8) * C_mD_sym +
            ((Nat.factorial 8 : ℝ) * C_th3 * B_T ^ 8) * C_mQ_sym))) *
            (c⁻¹ * (c ^ (9 / 4 : ℝ) * c ^ (-(8 / 3 : ℝ)))) := by ring
      _ = C_all * c ^ (-(17 / 12 : ℝ)) := by rw [hc_exp]
  rw [show ((8 : ℕ) : ℝ) + 0 = 8 by ring] at hscaled
  exact (hscaled.mono_B Icc_subset_Ici_self hB_eq.le).congr hDu hmain_eq

/-! ### `i c^{2/3} ϑ^{(1)}(T) ∈ S^{11}(C c^{-3/4})` -/

lemma fctInner_theta1_sym {K : ℝ} (hK : 0 ≤ K) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ {c : ℝ}, c₀ ≤ c →
      K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 11 (C * c ^ (-(3 / 4 : ℝ)))
          (fun u => Complex.I * ((c ^ ((2 : ℝ) / 3) * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))
            (fctInnerT c V u) : ℝ) : ℂ)) := by
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds hK
  obtain ⟨τ_D, hτD0, hτD_20, _Cv0b, _Cv0m, _Cva, _Cv1b, _Cv1m, _Cth0b, _Cth0m, C_tha, _Cth1b, _Cth1m,
    _CL0b, _CL0m, _CLa, _CL1b, _CL1m, _Ctail, _Cint, _hCv_nn, hCth_nn, _hCL_nn, _hCtail_nn, hDmain⟩ :=
    fct_comp_D_part1 StripKernelChoice.star
  set C_tha_max : ℝ := ∑ i ∈ Finset.range 9, C_tha i
  have hCtha_nn : 0 ≤ C_tha_max := Finset.sum_nonneg fun i _ => (hCth_nn i).2.2.1
  set C_all : ℝ := (Nat.factorial 8 : ℝ) * C_tha_max * B_T ^ 11
  set c₀ : ℝ := max 1 (τ_D ^ (-4 : ℝ))
  refine ⟨C_all, c₀, by positivity, le_max_left _ _, fun {c} hc hη {V} hV => ?_⟩
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_le : τ₁ ≤ τ_D := by
    have hτDc : τ_D ^ (-4 : ℝ) ≤ c := (le_max_right _ _).trans hc
    calc τ₁ = c ^ (-(1 / 4 : ℝ)) := rfl
      _ ≤ (τ_D ^ (-4 : ℝ)) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτD0 _) hτDc (by norm_num)
      _ = τ_D := by rw [← Real.rpow_mul hτD0.le]; norm_num
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  obtain ⟨hTcd, _, hTderiv, _⟩ := hBT hc1 hη hV
  have hT_tau1 : ∀ u ∈ Icc 0 (fctUc c), 0 ≤ fctInnerT c V u ∧ fctInnerT c V u ≤ 2 * τ₁ :=
    fun u hu => fctInnerT_le_two_tau1 hK hc1 hη hV hu
  obtain ⟨hcd_v, _, _, hsupp_v, _, _, _, _, hth_in, _⟩ :=
    hDmain (K4 := 1) (α := τ₁ ^ 2) le_rfl hc0 hτ₁_pos hτ₁_le hcτ (by rw [abs_of_nonneg (sq_nonneg τ₁)])
  have hva_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha (τ₁ ^ 2) τ₁) := hcd_v.2.2.1
  have hv1a_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha 1 τ₁) := by
    have heq : vAlpha 1 τ₁ = fun s => (τ₁ ^ 2)⁻¹ * vAlpha (τ₁ ^ 2) τ₁ s := by
      ext s; rw [vAlpha_eq_smul (τ₁ ^ 2) τ₁ s, inv_mul_cancel_left₀ (sq_pos_of_pos hτ₁_pos).ne']
    rw [heq]; exact contDiff_const.mul hva_cd
  have hv1a_cs : HasCompactSupport (vAlpha 1 τ₁) := by
    have hva_cs : HasCompactSupport (vAlpha (τ₁ ^ 2) τ₁) := hasCompactSupport_of_support_Ioo hsupp_v.2.2.1
    have heq : vAlpha 1 τ₁ = fun s => (τ₁ ^ 2)⁻¹ * vAlpha (τ₁ ^ 2) τ₁ s := by
      ext s; rw [vAlpha_eq_smul (τ₁ ^ 2) τ₁ s, inv_mul_cancel_left₀ (sq_pos_of_pos hτ₁_pos).ne']
    rw [heq]; exact hva_cs.comp_left (mul_zero _)
  have hθ1_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vAlpha 1 τ₁)) := contDiff_fctThetaD hv1a_cd hv1a_cs
  have hθ_rel : fctThetaD (vAlpha (τ₁ ^ 2) τ₁) = fun s => τ₁ ^ 2 * fctThetaD (vAlpha 1 τ₁) s := by
    ext s
    have hsm : vAlpha (τ₁ ^ 2) τ₁ = fun t => τ₁ ^ 2 * vAlpha 1 τ₁ t := funext (vAlpha_eq_smul (τ₁ ^ 2) τ₁)
    have hlin := fctThetaD_linear hv1a_cd hv1a_cs hv1a_cd hv1a_cs (τ₁ ^ 2) 0 s
    simp only [zero_mul, add_zero] at hlin
    rw [hsm]; exact hlin
  set E_τ : Set ℝ := Ioo (-3 * τ₁) (3 * τ₁)
  have hEτ_open : IsOpen E_τ := isOpen_Ioo
  have hT_maps_τ : MapsTo (fctInnerT c V) (Icc 0 (fctUc c)) E_τ := fun u hu =>
    ⟨by linarith [(hT_tau1 u hu).1], by linarith [(hT_tau1 u hu).2]⟩
  have hθ1_bd : ∀ i ≤ 8, ∀ t ∈ E_τ, 0 ≤ t →
      ‖iteratedDerivWithin i (fun t => ((fctThetaD (vAlpha 1 τ₁) t : ℝ) : ℂ)) E_τ t‖ ≤
        C_tha_max * τ₁ ^ (-9 : ℤ) * t ^ (11 - i) := by
    intro i hi t ht ht0
    rw [iteratedDerivWithin_ofReal_cast hEτ_open.uniqueDiffOn (n := 8)
      ((hθ1_cd.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn.mono (subset_univ _)) hi t ht,
      Complex.norm_real, iteratedDerivWithin_of_isOpen hEτ_open ht]
    have ht12 : |t| ≤ 12 * τ₁ := by rw [abs_of_nonneg ht0]; linarith [ht.2]
    have h := (hth_in i t ht12).2.2.1
    rw [hθ_rel, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (sq_pos_of_pos hτ₁_pos)] at h
    have hpow_min : min (1 : ℝ) ((|t| / τ₁) ^ (11 - i)) ≤ (t / τ₁) ^ (11 - i) := by
      rw [abs_of_nonneg ht0]; exact min_le_right _ _
    have h1 : τ₁ ^ 2 * |iteratedDeriv i (fctThetaD (vAlpha 1 τ₁)) t| ≤
        C_tha i * τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - i) * (t / τ₁) ^ (11 - i) :=
      h.trans (mul_le_mul_of_nonneg_left hpow_min
        (mul_nonneg (mul_nonneg (hCth_nn i).2.2.1 (sq_nonneg _)) (zpow_nonneg hτ₁_pos.le _)))
    have h2 : |iteratedDeriv i (fctThetaD (vAlpha 1 τ₁)) t| ≤
        C_tha i * τ₁ ^ ((2 : ℤ) - i) * (t / τ₁) ^ (11 - i) := by
      have h1' : τ₁ ^ 2 * |iteratedDeriv i (fctThetaD (vAlpha 1 τ₁)) t| ≤
          τ₁ ^ 2 * (C_tha i * τ₁ ^ ((2 : ℤ) - i) * (t / τ₁) ^ (11 - i)) := h1.trans_eq (by ring)
      exact le_of_mul_le_mul_left h1' (sq_pos_of_pos hτ₁_pos)
    have hp : τ₁ ^ ((2 : ℤ) - i) * (t / τ₁) ^ (11 - i) = τ₁ ^ (-9 : ℤ) * t ^ (11 - i) := by
      rw [div_pow, ← zpow_natCast τ₁ (11 - i), div_eq_mul_inv, ← zpow_neg, mul_comm (t ^ (11 - i))]
      rw [← mul_assoc, ← zpow_add₀ hτ₁_pos.ne']
      congr 2; omega
    have hci : C_tha i ≤ C_tha_max :=
      Finset.single_le_sum (fun k _ => (hCth_nn k).2.2.1) (Finset.mem_range.mpr (by omega))
    calc ‖iteratedDeriv i (fctThetaD (vAlpha 1 τ₁)) t‖ = |iteratedDeriv i (fctThetaD (vAlpha 1 τ₁)) t| := Real.norm_eq_abs _
      _ ≤ C_tha i * (τ₁ ^ ((2 : ℤ) - i) * (t / τ₁) ^ (11 - i)) := h2.trans_eq (by ring)
      _ = C_tha i * (τ₁ ^ (-9 : ℤ) * t ^ (11 - i)) := by rw [hp]
      _ ≤ C_tha_max * (τ₁ ^ (-9 : ℤ) * t ^ (11 - i)) := by gcongr
      _ = C_tha_max * τ₁ ^ (-9 : ℤ) * t ^ (11 - i) := by ring
  have hθ1_cdC : ContDiffOn ℝ 8 (fun t : ℝ => ((fctThetaD (vAlpha 1 τ₁) t : ℝ) : ℂ)) E_τ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((hθ1_cd.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn.mono (subset_univ _))
  have hθ1_sym := FctSymClsOn.comp_T_pow hUc0 (by norm_num : 8 ≤ 11) hEτ_open hθ1_cdC
    (mul_nonneg hCtha_nn (zpow_nonneg hτ₁_pos.le _)) hθ1_bd
    hTcd hT_maps_τ (by positivity)
    (fun u hu => ⟨(hT_tau1 u hu).1, by linarith [(hBT hc1 hη hV).2.1 u hu]⟩)
    (fun j hj1 hj8 u hu => hTderiv j hj1 hj8 u hu)
  have hscaled := hθ1_sym.const_mul (uniqueDiffOn_Icc hUc0) (Complex.I * ((c ^ ((2 : ℝ) / 3) : ℝ) : ℂ))
  have hpow_eq : (B_T * c ^ (-(1 / 3 : ℝ))) ^ 11 = B_T ^ 11 * c ^ (-(11 / 3 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
  have hτ9_eq : τ₁ ^ (-9 : ℤ) = c ^ (9 / 4 : ℝ) := by
    dsimp only [τ₁]; rw [← Real.rpow_intCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
  have hc_exp : c ^ ((2 : ℝ) / 3) * (c ^ (9 / 4 : ℝ) * c ^ (-(11 / 3 : ℝ))) = c ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
  have hnorm_sc : ‖Complex.I * ((c ^ ((2 : ℝ) / 3) : ℝ) : ℂ)‖ = c ^ ((2 : ℝ) / 3) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hB_eq : ‖Complex.I * ((c ^ ((2 : ℝ) / 3) : ℝ) : ℂ)‖ *
      ((Nat.factorial 8 : ℝ) * (C_tha_max * τ₁ ^ (-9 : ℤ)) * (B_T * c ^ (-(1 / 3 : ℝ))) ^ 11) =
      C_all * c ^ (-(3 / 4 : ℝ)) := by
    rw [hnorm_sc, hpow_eq, hτ9_eq]
    dsimp only [C_all]
    calc c ^ ((2 : ℝ) / 3) * ((Nat.factorial 8 : ℝ) * (C_tha_max * c ^ (9 / 4 : ℝ)) *
            (B_T ^ 11 * c ^ (-(11 / 3 : ℝ))))
        = (Nat.factorial 8 : ℝ) * C_tha_max * B_T ^ 11 *
            (c ^ ((2 : ℝ) / 3) * (c ^ (9 / 4 : ℝ) * c ^ (-(11 / 3 : ℝ)))) := by ring
      _ = C_all * c ^ (-(3 / 4 : ℝ)) := by rw [hc_exp]
  refine (hscaled.mono_B Icc_subset_Ici_self hB_eq.le).congr (uniqueDiffOn_Icc hUc0) fun u _ => ?_
  simp only [Function.comp_apply, Complex.ofReal_mul]; ring

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

/-- info: 'FormalResearch.SignUncertainty.fctInner_v1_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInner_v1_sym

/-- info: 'FormalResearch.SignUncertainty.fctInner_theta1_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInner_theta1_sym

/-- info: 'FormalResearch.SignUncertainty.fctVJets_of_chartV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctVJets_of_chartV

end FormalResearch.SignUncertainty


