/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerFactorsA
public import FormalResearch.SignUncertainty.FctInnerPhase

/-!
# Inner symbol bounds Part B (`v₁` and `ϑ^{(1)}`)

For `FctVJets K c V` on `[0, U_c]` (`U_c = 2.96 c^{1/12}`):
* `fctInnerT_le_two_tau1`: `0 ≤ T(u) ≤ 2 τ₁`;
* `fctInner_v1_sym`: `v₁(T(u)) ∈ S⁸(C c^{-17/12})`;
* `fctInner_theta1_sym`: `i c^{2/3} ϑ^{(1)}(T(u)) ∈ S^{11}(C c^{-3/4})`;

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

lemma fctInnerY_mem_35 {c u : ℝ} (hc : 1 ≤ c) (hu : u ∈ Icc 0 (fctUc c)) :
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

lemma tauStar_le_1068 : τs ≤ 1.068 := by
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
    have h : ContDiff ℝ 8 (fun x => ∫ s in (0 : ℝ)..1, (1 : ℝ) * iteratedDeriv 3 θ₀ (s * x)) :=
      (contDiff_hadamard_integral (w := fun _ : ℝ => (1 : ℝ)) continuous_const hθ0_3_cd).of_le
        (WithTop.coe_le_coe.mpr le_top)
    simp only [one_mul] at h
    exact h
  have hdiv2_real : ContDiff ℝ 8 (divT2_theta1 θ₀) := by
    have h := (contDiff_hadamard_integral (w := fun s : ℝ => 1 - s)
      (continuous_const.sub continuous_id) hθ0_3_cd).of_le
      (m := ((8 : ℕ) : WithTop ℕ∞)) (WithTop.coe_le_coe.mpr le_top)
    exact h
  have hdiv1_cd : ContDiffOn ℝ 8 (fun t : ℝ => ((divT_theta2 θ₀ t : ℝ) : ℂ)) E_τ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hdiv1_real.contDiffOn
  have hdiv2_cd : ContDiffOn ℝ 8 (fun t : ℝ => ((divT2_theta1 θ₀ t : ℝ) : ℂ)) E_τ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hdiv2_real.contDiffOn
  have hdiv1_sym := FctSymClsOn.comp_T_pow hUc0 (by norm_num : 8 ≤ 8) hEτ_open hdiv1_cd
    (mul_nonneg hCth3_nn (zpow_nonneg hτ₁_pos.le _))
    (fun i hi t ht ht0 => by
      simpa only [divT_theta2, one_mul] using had_bd (fun _ => 1) continuous_const (fun _ _ => by norm_num) i hi t ht ht0)
    hTcd hT_maps_τ (by positivity)
    (fun u hu => ⟨(hT_tau1 u hu).1, by linarith [(hBT hc1 hη hV).2.1 u hu]⟩)
    (fun j hj1 hj8 u hu => hTderiv j hj1 hj8 u hu)
  have hdiv2_sym := FctSymClsOn.comp_T_pow hUc0 (by norm_num : 8 ≤ 8) hEτ_open hdiv2_cd
    (mul_nonneg hCth3_nn (zpow_nonneg hτ₁_pos.le _))
    (fun i hi t ht ht0 => had_bd (fun s => 1 - s) (continuous_const.sub continuous_id)
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

/-- info: 'FormalResearch.SignUncertainty.fctInner_v1_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInner_v1_sym

/-- info: 'FormalResearch.SignUncertainty.fctInner_theta1_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInner_theta1_sym

end FormalResearch.SignUncertainty
