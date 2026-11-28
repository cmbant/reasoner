/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpOuterPhi
public import FormalResearch.SignUncertainty.FctPhiKillSymbol
public import FormalResearch.SignUncertainty.FctInnerSymbols

/-!
# Outer shoulder integration by parts for `fct:warp-asymp` (1)

Uses `fct_edge_ibp_shoulder` (`n = 15`) with `r = 1.85 τ₁` (`τ₁ = c^{-1/4}`), `u = c^{-1/2}`,
and the cutoff `outerChiOut c τ = 1 - outerChiIn (τ / τ₁)` (`outerChiIn : FctCutoffIn`) to bound
the outer shoulder integrals of `fctWarpIntegrand`, `fctWarpIntegrandDerivL`, and
`fctWarpIntegrandDerivAlpha` on `(0, ∞)` by `C * c ^ (-(23 / 8 : ℝ))` (`C * c ^ (-(31 / 8 : ℝ))`
for `I_out` and `∂_α I_out`) uniformly for `1 ≤ K4`, `K4 τ₁² ≤ 1`, `τ₁ ≤ pbTauLim`,
`concreteEll1 ε c L1 ∈ Ioo 0 2.55`, `|α| ≤ 2 τ₁²`, and `C_c₀ ≤ c`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctEdgeIbp FormalResearch.SignUncertainty.FctSym

namespace FormalResearch.SignUncertainty

/-! ### 1. Explicit `FctCutoffIn` bump cutoff `outerChiIn` and outer `edgeW`-bounds -/

/-- Smooth bump on `ℝ` equal to `1` on `[-1.85, 1.85]` and `0` outside `(-1.98, 1.98)`. -/
noncomputable def outerChiBump : ContDiffBump (0 : ℝ) := ⟨1.85, 1.98, by norm_num, by norm_num⟩

/-- Concrete `FctCutoffIn` cutoff `χ_in`. -/
noncomputable def outerChiIn (x : ℝ) : ℝ := outerChiBump x

lemma outerChiIn_cutoff : FctCutoffIn outerChiIn where
  smooth := outerChiBump.contDiff
  zero x hx := by
    by_contra hne
    have hm : x ∈ Function.support outerChiBump := hne
    rw [outerChiBump.support_eq] at hm
    simp only [outerChiBump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hm
    linarith only [hx, hm]
  one x hx := by
    apply outerChiBump.one_of_mem_closedBall
    simpa [outerChiBump, Real.norm_eq_abs] using hx
  mem x := ⟨outerChiBump.nonneg' x, outerChiBump.le_one⟩

/-- Smooth outer cutoff `χ_out(τ) = 1 - χ_in(τ / τ₁)`. -/
noncomputable def outerChiOut (c τ : ℝ) : ℝ := 1 - outerChiIn (τ / c ^ (-(1 / 4 : ℝ)))

private lemma iteratedDeriv_comp_const_mul (k : ℕ) (f : ℝ → ℝ) (a : ℝ) :
    ∀ x : ℝ, iteratedDeriv k (fun t => f (a * t)) x = a ^ k * iteratedDeriv k f (a * x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun t => f (a * t)) =
        fun t => a ^ k * iteratedDeriv k f (a * t) from funext ih,
      deriv_const_mul_field']
    dsimp only
    rw [deriv_comp_mul_left a (iteratedDeriv k f) x, ← iteratedDeriv_succ, pow_succ]
    ring

private lemma outerChiOut_edge_bounds (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ {c : ℝ}, 0 < c →
      let τ₁ := c ^ (-(1 / 4 : ℝ))
      ContDiff ℝ ∞ (outerChiOut c) ∧
      (∀ τ : ℝ, |τ| ≤ 1.85 * τ₁ → outerChiOut c τ = 0) ∧
      (∀ τ : ℝ, 1.98 * τ₁ ≤ |τ| → outerChiOut c τ = 1) ∧
      (∀ k ≤ n, ∀ τ : ℝ, 0 < τ → |iteratedDeriv k (outerChiOut c) τ| ≤ B k * edgeW τ ^ (-(k : ℤ))) := by
  have hb : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv k outerChiIn x| ≤ M := fun k => by
    have hc : ContinuousOn (iteratedDeriv k outerChiIn) (Icc (-1.98 : ℝ) 1.98) :=
      ((outerChiIn_cutoff.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedDeriv
        k (WithTop.coe_le_coe.mpr le_top)).continuousOn
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : |x| ≤ 1.98
    · exact (Real.norm_eq_abs _ ▸ hM x ⟨by linarith only [neg_abs_le x, hx],
        by linarith only [le_abs_self x, hx]⟩).trans (le_max_left _ _)
    · push Not at hx
      have hev : outerChiIn =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds
          (show (1.98 : ℝ) < |x| from hx)] with y hy
        exact outerChiIn_cutoff.zero y (le_of_lt hy)
      rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_zero, abs_zero]
      exact le_max_right _ _
  choose M hM0 hM using hb
  refine ⟨fun k => (1.98 : ℝ) ^ k * max (M k) 1, fun k => by positivity, fun {c} hc => ?_⟩
  dsimp only
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hcd : ContDiff ℝ ∞ (outerChiOut c) := by
    have hcomp : ContDiff ℝ ∞ (fun τ : ℝ => outerChiIn (τ / τ₁)) :=
      (outerChiIn_cutoff.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_id.div_const τ₁)
    exact contDiff_const.sub hcomp
  refine ⟨hcd, fun τ hτ => ?_, fun τ hτ => ?_, fun k _ τ hτ => ?_⟩
  · have h1 : |τ / τ₁| ≤ 1.85 := by
      rw [abs_div, abs_of_pos hτ₁, div_le_iff₀ hτ₁]; exact hτ
    unfold outerChiOut
    rw [outerChiIn_cutoff.one _ h1, sub_self]
  · have h1 : 1.98 ≤ |τ / τ₁| := by
      rw [abs_div, abs_of_pos hτ₁, le_div_iff₀ hτ₁]; exact hτ
    unfold outerChiOut
    rw [outerChiIn_cutoff.zero _ h1, sub_zero]
  · rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · have hm := outerChiIn_cutoff.mem (τ / τ₁)
      have hab : |outerChiOut c τ| ≤ 1 := by
        unfold outerChiOut; rw [abs_le]; constructor <;> linarith only [hm.1, hm.2]
      simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
      exact hab.trans (le_max_right (M 0) 1)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
      have hc_zero : iteratedDeriv (m + 1) (fun _ : ℝ => (1 : ℝ)) τ = 0 := by
        rw [iteratedDeriv_succ', deriv_const']; simp
      rcases le_or_gt τ (1.98 * τ₁) with hle | hgt
      · have hw_le : edgeW τ ≤ 1.98 * τ₁ := (edgeW_le_abs τ).trans (by rwa [abs_of_pos hτ])
        have hw_pos : 0 < edgeW τ := edgeW_pos hτ.ne'
        have hinv : τ₁⁻¹ ≤ 1.98 * (edgeW τ)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hw_pos, inv_mul_le_iff₀ hτ₁]; linarith only [hw_le]
        have hpow_inv : (τ₁⁻¹) ^ (m + 1) ≤ 1.98 ^ (m + 1) * edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by
          rw [zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
          exact pow_le_pow_left₀ (inv_nonneg.mpr hτ₁.le) hinv (m + 1)
        have hcomp_deriv : iteratedDeriv (m + 1) (outerChiOut c) τ =
            -(τ₁⁻¹ ^ (m + 1) * iteratedDeriv (m + 1) outerChiIn (τ / τ₁)) := by
          have heq : outerChiOut c = (fun _ : ℝ => (1 : ℝ)) - fun s : ℝ => outerChiIn (τ₁⁻¹ * s) := by
            ext s; unfold outerChiOut; congr 2; ring
          have hcd_in : ContDiffAt ℝ (m + 1) (fun s : ℝ => outerChiIn (τ₁⁻¹ * s)) τ :=
            ((outerChiIn_cutoff.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp
              (contDiff_const.mul contDiff_id)).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
          rw [heq, iteratedDeriv_sub (contDiff_const.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hcd_in,
            hc_zero, zero_sub, iteratedDeriv_comp_const_mul (m + 1) outerChiIn τ₁⁻¹ τ,
            show τ₁⁻¹ * τ = τ / τ₁ by ring]
        rw [hcomp_deriv, abs_neg, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hτ₁.le) (m + 1))]
        calc (τ₁⁻¹) ^ (m + 1) * |iteratedDeriv (m + 1) outerChiIn (τ / τ₁)|
            ≤ (1.98 ^ (m + 1) * edgeW τ ^ (-((m + 1 : ℕ) : ℤ))) * M (m + 1) :=
              mul_le_mul hpow_inv (hM (m + 1) (τ / τ₁)) (abs_nonneg _) (by positivity)
          _ ≤ (1.98 ^ (m + 1) * edgeW τ ^ (-((m + 1 : ℕ) : ℤ))) * max (M (m + 1)) 1 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
          _ = 1.98 ^ (m + 1) * max (M (m + 1)) 1 * edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by ring
      · have hev : outerChiOut c =ᶠ[𝓝 τ] fun _ => (1 : ℝ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
          have hs' : 1.98 * τ₁ ≤ |s| := by
            have h198 : 1.98 * τ₁ < s := hs
            have hs0 : 0 < s := lt_trans (by positivity) h198
            rw [abs_of_pos hs0]; exact h198.le
          have h1 : 1.98 ≤ |s / τ₁| := by rw [abs_div, abs_of_pos hτ₁, le_div_iff₀ hτ₁]; exact hs'
          unfold outerChiOut; rw [outerChiIn_cutoff.zero _ h1, sub_zero]
        rw [hev.iteratedDeriv_eq (m + 1), hc_zero, abs_zero]
        exact mul_nonneg (by positivity) (zpow_nonneg (edgeW_pos hτ.ne').le _)

/-! ### 2. `ℂ`-valued `edgeW` bounds for `ofReal`, `phiKill / m`, and `exp(binet + v)` -/

private lemma ofReal_iteratedDeriv_eq {S : Set ℝ} (hS : IsOpen S) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g S) :
    ∀ k : ℕ, ∀ t ∈ S, iteratedDeriv k (fun s => ((g s : ℝ) : ℂ)) t = ((iteratedDeriv k g t : ℝ) : ℂ) := by
  intro k t ht
  induction k generalizing t with
  | zero => simp
  | succ m ih =>
    have hev : iteratedDeriv m (fun s => ((g s : ℝ) : ℂ)) =ᶠ[𝓝 t] fun s => ((iteratedDeriv m g s : ℝ) : ℂ) :=
      Filter.eventually_of_mem (hS.mem_nhds ht) fun s hs => ih s hs
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hev.deriv_eq]
    have hd_g : HasDerivAt (iteratedDeriv m g) (deriv (iteratedDeriv m g) t) t :=
      (((FctSym.contDiffOn_iteratedDeriv_gen hS hg m).differentiableOn (by simp)).differentiableAt
        (hS.mem_nhds ht)).hasDerivAt
    exact (hd_g.ofReal_comp).deriv

private lemma ofReal_edge_bounds {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {g : ℝ → ℝ} {w : ℝ → ℝ} {C : ℕ → ℝ}
    (hg : ContDiffOn ℝ ∞ g S)
    (hbd : ∀ k ≤ n, ∀ τ ∈ S, |iteratedDeriv k g τ| ≤ C k * w τ * edgeW τ ^ (-(k : ℤ))) :
    ∀ k ≤ n, ∀ τ ∈ S, ‖iteratedDeriv k (fun s => ((g s : ℝ) : ℂ)) τ‖ ≤ C k * w τ * edgeW τ ^ (-(k : ℤ)) := by
  intro k hk τ hτ
  rw [ofReal_iteratedDeriv_eq hS hg k τ hτ, Complex.norm_real, Real.norm_eq_abs]
  exact hbd k hk τ hτ

private lemma phiKill_edge_bounds (n : ℕ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ {a τ : ℝ}, 0 < a → 0 < τ → ∀ k ≤ n,
      ‖iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ‖ ≤
        C k * edgeW τ ^ (-(k : ℤ)) := by
  obtain ⟨Cpk, hCpk0, hCpk⟩ := FctSym.phiKill_tsymbol
  refine ⟨fun k => 2 * Cpk k, fun k => mul_nonneg zero_le_two (hCpk0 k), ?_⟩
  intro a τ ha hτ k _
  have hcd := FctSym.contDiff_phiKill_imag ha
  have hre_bd := (hCpk a τ ha hτ Complex.reCLM (fun z => Complex.abs_re_le_norm z) k).1
  have him_bd := (hCpk a τ ha hτ Complex.imCLM (fun z => Complex.abs_im_le_norm z) k).1
  have hre_clm : iteratedDeriv k (fun s : ℝ => Complex.reCLM (FctPhiKill.phiKill a ((s : ℂ) * Complex.I))) τ =
      (iteratedDeriv k (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) τ).re :=
    FctSym.iteratedDeriv_clm_comp isOpen_univ hcd.contDiffOn Complex.reCLM k τ (mem_univ _)
  have him_clm : iteratedDeriv k (fun s : ℝ => Complex.imCLM (FctPhiKill.phiKill a ((s : ℂ) * Complex.I))) τ =
      (iteratedDeriv k (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) τ).im :=
    FctSym.iteratedDeriv_clm_comp isOpen_univ hcd.contDiffOn Complex.imCLM k τ (mem_univ _)
  rw [hre_clm] at hre_bd
  rw [him_clm] at him_bd
  have hmin : min (1 : ℝ) ((τ / a) ^ 8) ≤ 1 := min_le_left _ _
  have hpk : 0 < τ ^ k := pow_pos hτ k
  have hτ_inv : (τ ^ k)⁻¹ ≤ edgeW τ ^ (-(k : ℤ)) := by
    have h1 := abs_inv_le_edgeW_inv hτ.ne' k
    rwa [zpow_neg, zpow_natCast, abs_of_pos hτ] at h1
  have hre1 : |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).re| ≤
      Cpk k * edgeW τ ^ (-(k : ℤ)) := by
    rw [abs_mul, abs_of_pos hpk] at hre_bd
    have h1 : τ ^ k * |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).re| ≤ Cpk k :=
      hre_bd.trans ((mul_le_mul_of_nonneg_left hmin (hCpk0 k)).trans (le_of_eq (mul_one _)))
    calc |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).re|
        ≤ Cpk k * (τ ^ k)⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hpk, mul_comm]; exact h1
      _ ≤ Cpk k * edgeW τ ^ (-(k : ℤ)) := mul_le_mul_of_nonneg_left hτ_inv (hCpk0 k)
  have him1 : |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).im| ≤
      Cpk k * edgeW τ ^ (-(k : ℤ)) := by
    rw [abs_mul, abs_of_pos hpk] at him_bd
    have h1 : τ ^ k * |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).im| ≤ Cpk k :=
      him_bd.trans ((mul_le_mul_of_nonneg_left hmin (hCpk0 k)).trans (le_of_eq (mul_one _)))
    calc |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).im|
        ≤ Cpk k * (τ ^ k)⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hpk, mul_comm]; exact h1
      _ ≤ Cpk k * edgeW τ ^ (-(k : ℤ)) := mul_le_mul_of_nonneg_left hτ_inv (hCpk0 k)
  calc ‖iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ‖
      ≤ |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).re| +
          |(iteratedDeriv k (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ Cpk k * edgeW τ ^ (-(k : ℤ)) + Cpk k * edgeW τ ^ (-(k : ℤ)) := add_le_add hre1 him1
    _ = 2 * Cpk k * edgeW τ ^ (-(k : ℤ)) := by ring

private lemma mInv_tau1_edge_bounds (n : ℕ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ContDiffOn ℝ ∞ (fun t : ℝ => (uctM t)⁻¹) (Ioi 0) ∧
      ∀ {c τ : ℝ}, 1 ≤ c → 1.85 * c ^ (-(1 / 4 : ℝ)) < τ → ∀ k ≤ n,
        |iteratedDeriv k (fun t : ℝ => (uctM t)⁻¹) τ| ≤
          C k * c ^ (1 / 2 : ℝ) * edgeW τ ^ (-(k : ℤ)) := by
  obtain ⟨K, hmInv⟩ := FctSym.mInv_symW_all
  obtain ⟨U, _, hIU, hcd⟩ := hmInv.smooth
  refine ⟨K, hmInv.K_nonneg, hcd.mono hIU, fun {c τ} hc1 hτ k _ => ?_⟩
  have hc0 : 0 < c := by linarith only [hc1]
  have hτ₁ : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hτ_pos : 0 < τ := lt_trans (by positivity) hτ
  have hb := hmInv.bound k τ hτ_pos
  have hwA_le : FctSym.wA τ ≤ c ^ (1 / 2 : ℝ) := by
    unfold FctSym.wA
    refine max_le (Real.one_le_rpow hc1 (by norm_num)) ?_
    have hτ₁_lt : c ^ (-(1 / 4 : ℝ)) < τ := by linarith only [hτ₁, hτ]
    have hr1 : τ ^ (-2 : ℝ) ≤ (c ^ (-(1 / 4 : ℝ))) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hτ₁ hτ₁_lt.le (by norm_num)
    have hr2 : (c ^ (-(1 / 4 : ℝ))) ^ (-2 : ℝ) = c ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_mul hc0.le]; norm_num
    rw [← Real.rpow_natCast τ 2, ← Real.rpow_neg hτ_pos.le]
    exact hr1.trans_eq hr2
  have hτ_inv : (τ ^ k)⁻¹ ≤ edgeW τ ^ (-(k : ℤ)) := by
    have h1 := abs_inv_le_edgeW_inv hτ_pos.ne' k
    rwa [zpow_neg, zpow_natCast, abs_of_pos hτ_pos] at h1
  calc |iteratedDeriv k (fun t : ℝ => (uctM t)⁻¹) τ|
      ≤ K k * FctSym.wA τ * (τ ^ k)⁻¹ := hb
    _ ≤ K k * c ^ (1 / 2 : ℝ) * edgeW τ ^ (-(k : ℤ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hwA_le (hmInv.K_nonneg k)) hτ_inv
          (inv_nonneg.mpr (pow_nonneg hτ_pos.le k)) (mul_nonneg (hmInv.K_nonneg k) (by positivity))

/-! ### 3. Shared IBP wrapper on `(0, ∞)` and outer shoulder bounds -/

private lemma outer_shoulder_ibp_helper {n : ℕ} {κ_Phi : ℝ} {K_Phi C_χ : ℕ → ℝ} {C_ibp : ℝ}
    {c A_f : ℝ} {f : ℝ → ℂ} {Φ : ℝ → ℝ}
    (hc0 : 0 < c) (_hCibp_nn : 0 ≤ C_ibp) (hAf_nn : 0 ≤ A_f)
    (hCχ0 : ∀ k, 0 ≤ C_χ k)
    (hibp : ∀ {u r A : ℝ} {a : ℝ → ℂ},
      0 < u → 0 < r → r ≤ 1 → 0 ≤ A →
      ContDiff ℝ (n : ℕ) a →
      (∀ τ : ℝ, |τ| < r → a τ = 0) →
      (∀ k ≤ n, ∀ τ : ℝ, r < |τ| →
        ‖iteratedDeriv k a τ‖ ≤ A * edgeW τ ^ (-(k : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ)) →
      ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ {τ : ℝ | r < |τ|} →
      (∀ τ : ℝ, r < |τ| → κ_Phi * u ≤ |deriv Φ τ|) →
      (∀ k, 1 ≤ k → k ≤ n → ∀ τ : ℝ, r < |τ| →
        |iteratedDeriv (k + 1) Φ τ| ≤ K_Phi k * edgeW τ ^ (-(k : ℤ)) * |deriv Φ τ|) →
      Integrable (fun τ : ℝ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) ∧
      ‖∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))‖ ≤
        C_ibp * A * ((c * u) ^ n)⁻¹ * r ^ (1 / 2 - (n : ℝ)))
    (hc16 : (16 : ℝ) ≤ c)
    (hΦ_cd : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ {τ : ℝ | 1.85 * c ^ (-(1 / 4 : ℝ)) < |τ|})
    (hΦ'_lb : ∀ τ : ℝ, 1.85 * c ^ (-(1 / 4 : ℝ)) < |τ| → κ_Phi * c ^ (-(1 / 2 : ℝ)) ≤ |deriv Φ τ|)
    (hΦ_bd : ∀ k, 1 ≤ k → k ≤ n → ∀ τ : ℝ, 1.85 * c ^ (-(1 / 4 : ℝ)) < |τ| →
      |iteratedDeriv (k + 1) Φ τ| ≤ K_Phi k * edgeW τ ^ (-(k : ℤ)) * |deriv Φ τ|)
    (hχ_cd : ContDiff ℝ ∞ (outerChiOut c))
    (hχ_zero : ∀ τ : ℝ, |τ| ≤ 1.85 * c ^ (-(1 / 4 : ℝ)) → outerChiOut c τ = 0)
    (hχ_bd : ∀ k ≤ n, ∀ τ : ℝ, 0 < τ → |iteratedDeriv k (outerChiOut c) τ| ≤ C_χ k * edgeW τ ^ (-(k : ℤ)))
    (hf_cd : ContDiffOn ℝ (n : ℕ) f (Ioi 0))
    (hf_bd : ∀ k ≤ n, ∀ τ : ℝ, 1.85 * c ^ (-(1 / 4 : ℝ)) < τ →
      ‖iteratedDeriv k f τ‖ ≤ A_f * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) :
    let B_chi := (2 : ℝ) ^ n * ∑ j ∈ range (n + 1), C_χ j
    IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * f τ *
      Complex.exp (Complex.I * ((c * Φ τ - π / 4 : ℝ) : ℂ))) (Ioi 0) ∧
    ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * f τ *
      Complex.exp (Complex.I * ((c * Φ τ - π / 4 : ℝ) : ℂ))‖ ≤
      C_ibp * (B_chi * A_f) * ((c * c ^ (-(1 / 2 : ℝ))) ^ n)⁻¹ *
        (1.85 * c ^ (-(1 / 4 : ℝ))) ^ (1 / 2 - (n : ℝ)) := by
  intro B_chi
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  set r := 1.85 * τ₁
  set u := c ^ (-(1 / 2 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hu : 0 < u := Real.rpow_pos_of_pos hc0 _
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    have hc4 : (2 : ℝ) ^ 4 ≤ c := by linarith only [hc16]
    have hτ₁_le : τ₁ ≤ (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = ((16 : ℝ) ^ (-(1 / 4 : ℝ))) by
        rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hc16 (by norm_num)
    dsimp only [r]; linarith only [hτ₁_le]
  let a : ℝ → ℂ := fun τ => if 0 < τ then ((outerChiOut c τ : ℝ) : ℂ) * f τ else 0
  have ha_zero : ∀ τ : ℝ, |τ| < r → a τ = 0 := fun τ hτ => by
    by_cases hpos : 0 < τ
    · dsimp only [a]; rw [ite_eq_left_iff.mpr fun h => absurd hpos h, hχ_zero τ hτ.le, Complex.ofReal_zero, zero_mul]
    · dsimp only [a]; exact ite_eq_right_iff.mpr fun h => absurd h hpos
  have ha_prod_cd : ContDiffOn ℝ (n : ℕ) (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * f τ) (Ioi 0) :=
    ((Complex.ofRealCLM.contDiff.comp (hχ_cd.of_le (WithTop.coe_le_coe.mpr le_top))).contDiffOn.of_le
      (by exact_mod_cast le_top)).mul hf_cd
  have ha_cd : ContDiff ℝ (n : ℕ) a := by
    rw [contDiff_iff_contDiffAt]
    intro τ
    rcases lt_or_ge τ r with hlt | hge
    · have hev : a =ᶠ[𝓝 τ] (0 : ℝ → ℂ) := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
        by_cases hpos : 0 < s
        · exact ha_zero s (by rw [abs_of_pos hpos]; exact hs)
        · dsimp only [a]; exact ite_eq_right_iff.mpr fun h => absurd h hpos
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · have hpos : 0 < τ := lt_of_lt_of_le hr hge
      have hev : a =ᶠ[𝓝 τ] fun s => ((outerChiOut c s : ℝ) : ℂ) * f s := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
        dsimp only [a]; exact ite_eq_left_iff.mpr fun h => absurd hs h
      exact (ha_prod_cd.contDiffAt (isOpen_Ioi.mem_nhds hpos)).congr_of_eventuallyEq hev
  have hBχ_nn : 0 ≤ B_chi :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hCχ0 j)
  have hBA_nn : 0 ≤ B_chi * A_f := mul_nonneg hBχ_nn hAf_nn
  have ha_bd : ∀ k ≤ n, ∀ τ : ℝ, r < |τ| →
      ‖iteratedDeriv k a τ‖ ≤
        (B_chi * A_f) * edgeW τ ^ (-(k : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := by
    intro k hk τ hτ
    have hτ0 : τ ≠ 0 := abs_pos.mp (lt_trans hr hτ)
    have hwk_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos hτ0).le _
    have hrp_nn : 0 ≤ |τ| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    have h1t_nn : 0 ≤ (1 + |τ|) ^ (-2 : ℤ) := zpow_nonneg (by linarith only [abs_nonneg τ]) _
    rcases lt_or_gt_of_ne hτ0 with hneg | hpos
    · have hev : a =ᶠ[𝓝 τ] (0 : ℝ → ℂ) := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with s hs
        dsimp only [a]; exact ite_eq_right_iff.mpr fun h => absurd h (not_lt_of_gt hs)
      rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hBA_nn hwk_nn) hrp_nn) h1t_nn
    · have hτr : r < τ := by simpa [abs_of_pos hpos] using hτ
      have hev : a =ᶠ[𝓝 τ] fun s => ((outerChiOut c s : ℝ) : ℂ) * f s := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
        dsimp only [a]; exact ite_eq_left_iff.mpr fun h => absurd hs h
      rw [hev.iteratedDeriv_eq k]
      have hSr : IsOpen (Ioi r) := isOpen_Ioi
      have hSr0 : ∀ t ∈ Ioi r, t ≠ 0 := fun t ht => (lt_trans hr ht).ne'
      have hχ_C : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => ((outerChiOut c t : ℝ) : ℂ)) (Ioi r) :=
        ((Complex.ofRealCLM.contDiff.comp (hχ_cd.of_le (WithTop.coe_le_coe.mpr le_top))).contDiffOn.of_le
          (by exact_mod_cast le_top)).mono fun t ht => mem_univ t
      have hχ_C_bd : ∀ j ≤ n, ∀ t ∈ Ioi r,
          ‖iteratedDeriv j (fun s : ℝ => ((outerChiOut c s : ℝ) : ℂ)) t‖ ≤
            C_χ j * (1 : ℝ) * edgeW t ^ (-(j : ℤ)) :=
        ofReal_edge_bounds hSr (hχ_cd.contDiffOn.mono (subset_univ _))
          fun j hj t ht => by rw [mul_one]; exact hχ_bd j hj t (lt_trans hr ht)
      have hf_Sr : ContDiffOn ℝ (n : ℕ) f (Ioi r) := hf_cd.mono fun t ht => lt_trans hr ht
      have hf_Sr_bd : ∀ j ≤ n, ∀ t ∈ Ioi r,
          ‖iteratedDeriv j f t‖ ≤ A_f * (t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) * edgeW t ^ (-(j : ℤ)) :=
        fun j hj t ht => by
          have := hf_bd j hj t ht
          linarith only [this, show A_f * edgeW t ^ (-(j : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ) =
            A_f * (t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) * edgeW t ^ (-(j : ℤ)) by ring]
      have hmul := iteratedDeriv_mul_edgeW hSr hSr0 hχ_C hf_Sr
        (fun _ _ => zero_le_one)
        (fun t ht => mul_nonneg (Real.rpow_nonneg (lt_trans hr ht).le _)
          (zpow_nonneg (by linarith only [lt_trans hr ht]) _))
        (fun j _ => hCχ0 j) (fun _ _ => hAf_nn) hχ_C_bd hf_Sr_bd k hk τ hτr
      have hsum_le : ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * C_χ j * A_f ≤ B_chi * A_f := by
        have h1 : ∀ j ∈ range (k + 1), (Nat.choose k j : ℝ) * C_χ j ≤ (2 : ℝ) ^ n * C_χ j := fun j hj => by
          have hj_le : Nat.choose k j ≤ 2 ^ k := by
            calc Nat.choose k j ≤ ∑ i ∈ range (k + 1), Nat.choose k i :=
                  Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
              _ = 2 ^ k := Nat.sum_range_choose k
          have h2kn : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
            pow_le_pow_right₀ (by norm_num) hk
          have hch : (Nat.choose k j : ℝ) ≤ (2 : ℝ) ^ n :=
            le_trans (by exact_mod_cast hj_le) h2kn
          exact mul_le_mul_of_nonneg_right hch (hCχ0 j)
        have h2 : ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * C_χ j ≤
            ∑ j ∈ range (k + 1), (2 : ℝ) ^ n * C_χ j := Finset.sum_le_sum h1
        have h3 : ∑ j ∈ range (k + 1), (2 : ℝ) ^ n * C_χ j ≤ B_chi := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hk))
              fun j _ _ => hCχ0 j) (by positivity)
        calc ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * C_χ j * A_f
            = (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * C_χ j) * A_f := by rw [Finset.sum_mul]
          _ ≤ B_chi * A_f := mul_le_mul_of_nonneg_right (h2.trans h3) hAf_nn
      rw [one_mul] at hmul
      rw [abs_of_pos hpos] at hrp_nn h1t_nn ⊢
      refine hmul.trans ?_
      calc (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * C_χ j * A_f) *
            (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ))
          ≤ (B_chi * A_f) * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum_le (mul_nonneg hrp_nn h1t_nn)) hwk_nn
        _ = (B_chi * A_f) * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring
  obtain ⟨hint_R, hbd_R⟩ := hibp hu hr hr1 hBA_nn ha_cd ha_zero ha_bd hΦ_cd hΦ'_lb hΦ_bd
  set ζ : ℂ := Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ)))
  have hζ_norm : ‖ζ‖ = 1 := by
    dsimp only [ζ]
    rw [show -(Complex.I * ((π / 4 : ℝ) : ℂ)) = ((-π / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h_eq_Ioi : EqOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * f τ *
      Complex.exp (Complex.I * ((c * Φ τ - π / 4 : ℝ) : ℂ)))
      (fun τ : ℝ => ζ * (a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ)))) (Ioi 0) := by
    intro τ hτ
    have hτ0 : 0 < τ := mem_Ioi.mp hτ
    dsimp only [a, ζ]
    rw [ite_eq_left_iff.mpr (fun h => absurd hτ0 h), mul_left_comm ζ, ← Complex.exp_add]
    have hex : -(Complex.I * ((π / 4 : ℝ) : ℂ)) + Complex.I * ((c * Φ τ : ℝ) : ℂ) =
        Complex.I * ((c * Φ τ - π / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [hex]
  have hint_Ioi : IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * f τ *
      Complex.exp (Complex.I * ((c * Φ τ - π / 4 : ℝ) : ℂ))) (Ioi 0) :=
    IntegrableOn.congr_fun (hint_R.integrableOn.const_mul ζ)
      (fun τ hτ => (h_eq_Ioi hτ).symm) measurableSet_Ioi
  refine ⟨hint_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi h_eq_Ioi, integral_const_mul, norm_mul, hζ_norm, one_mul]
  have h_compl : ∀ τ ∉ Ioi (0 : ℝ), a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ)) = 0 := by
    intro τ hτ
    have hnot : ¬ (0 < τ) := hτ
    dsimp only [a]; rw [ite_eq_right_iff.mpr fun h => absurd h hnot, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_compl]
  exact hbd_R

private noncomputable def expDerivC (Cf : ℕ → ℝ) (k : ℕ) : ℝ :=
  match k with
  | 0 => 1
  | m + 1 => (range (m + 1)).attach.sum fun p =>
      (Nat.choose m p.1 : ℝ) * expDerivC Cf p.1 * Cf (m + 1 - p.1)
termination_by k
decreasing_by
  have hj := p.2
  simp only [Finset.mem_range] at hj
  omega

private lemma expDerivC_zero (Cf : ℕ → ℝ) : expDerivC Cf 0 = 1 := by rw [expDerivC]

private lemma expDerivC_succ (Cf : ℕ → ℝ) (m : ℕ) :
    expDerivC Cf (m + 1) = ∑ j ∈ range (m + 1), (Nat.choose m j : ℝ) * expDerivC Cf j * Cf (m + 1 - j) := by
  conv_lhs => rw [expDerivC]
  exact Finset.sum_attach (range (m + 1)) fun j => (Nat.choose m j : ℝ) * expDerivC Cf j * Cf (m + 1 - j)

private lemma expDerivC_nonneg {Cf : ℕ → ℝ} (hCf : ∀ k, 0 ≤ Cf k) (m : ℕ) : 0 ≤ expDerivC Cf m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    cases m with
    | zero => simp [expDerivC_zero]
    | succ k =>
      rw [expDerivC_succ]
      exact Finset.sum_nonneg fun j hj =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih j (Finset.mem_range.mp hj))) (hCf _)

private lemma cexp_iteratedDeriv_uniform {Cf : ℕ → ℝ} (hCf : ∀ k, 0 ≤ Cf k) {n : ℕ}
    {S : Set ℝ} (hS : IsOpen S) (hS0 : ∀ τ ∈ S, τ ≠ 0)
    {f : ℝ → ℂ} {B : ℝ} (hf_cd : ContDiffOn ℝ (n : ℕ) f S) (hB : 0 ≤ B)
    (hexp : ∀ τ ∈ S, ‖Complex.exp (f τ)‖ ≤ B)
    (hf_bd : ∀ k, 1 ≤ k → k ≤ n → ∀ τ ∈ S, ‖iteratedDeriv k f τ‖ ≤ Cf k * edgeW τ ^ (-(k : ℤ))) :
    ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t => Complex.exp (f t)) τ‖ ≤ expDerivC Cf k * B * edgeW τ ^ (-(k : ℤ)) := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro τ hτ
    have hτ0 : τ ≠ 0 := hS0 τ hτ
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simpa [expDerivC_zero] using hexp τ hτ
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm_le : m ≤ n := by omega
      have hf_exp_cd : ContDiffOn ℝ (n : ℕ) (fun t => Complex.exp (f t)) S := hf_cd.cexp
      have hev_deriv : EqOn (deriv (fun t => Complex.exp (f t)))
          (fun t => Complex.exp (f t) * deriv f t) S := fun t ht => by
        have hdf : HasDerivAt f (deriv f t) t :=
          ((hf_cd.differentiableOn (by exact_mod_cast (show n ≠ 0 by omega))).differentiableAt
            (hS.mem_nhds ht)).hasDerivAt
        exact (hdf.cexp).deriv
      have hev_eq : deriv (fun t => Complex.exp (f t)) =ᶠ[𝓝 τ] fun t => Complex.exp (f t) * deriv f t :=
        Filter.eventually_of_mem (hS.mem_nhds hτ) fun t ht => hev_deriv ht
      rw [iteratedDeriv_succ', hev_eq.iteratedDeriv_eq m]
      have hcd_m1 : ContDiffAt ℝ m (fun t => Complex.exp (f t)) τ :=
        (hf_exp_cd.contDiffAt (hS.mem_nhds hτ)).of_le (by exact_mod_cast hm_le)
      have hcd_m2 : ContDiffAt ℝ m (deriv f) τ := by
        have hdf : ContDiffOn ℝ m (deriv f) S := by
          have : (m : WithTop ℕ∞) + 1 ≤ n := by exact_mod_cast (by omega : m + 1 ≤ n)
          exact ((contDiffOn_succ_iff_deriv_of_isOpen hS (n := m)).mp (hf_cd.of_le this)).2.2
        exact hdf.contDiffAt (hS.mem_nhds hτ)
      rw [show (fun t => Complex.exp (f t) * deriv f t) = (fun t => Complex.exp (f t)) * deriv f from rfl,
        iteratedDeriv_mul hcd_m1 hcd_m2]
      refine (norm_sum_le _ _).trans ?_
      rw [expDerivC_succ, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj_lt : j < m + 1 := Finset.mem_range.mp hj
      have hj_le : j ≤ m := Nat.lt_succ_iff.mp hj_lt
      have hm_sub : iteratedDeriv (m - j) (deriv f) τ = iteratedDeriv (m - j + 1) f τ := by
        rw [iteratedDeriv_succ']
      rw [norm_mul, norm_mul, Complex.norm_natCast, hm_sub]
      have hih_j := ih j hj_lt (hj_le.trans hm_le) τ hτ
      have hbd_df := hf_bd (m - j + 1) (Nat.succ_pos _) (by omega) τ hτ
      have hw_eq : edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((m - j + 1 : ℕ) : ℤ)) =
          edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by
        rw [edgeW_zpow_mul hτ0]; congr 2; omega
      have h1 : m + 1 - j = m - j + 1 := by omega
      rw [h1]
      calc (Nat.choose m j : ℝ) * ‖iteratedDeriv j (fun t => Complex.exp (f t)) τ‖ *
            ‖iteratedDeriv (m - j + 1) f τ‖
          ≤ (Nat.choose m j : ℝ) * (expDerivC Cf j * B * edgeW τ ^ (-(j : ℤ))) *
              (Cf (m - j + 1) * edgeW τ ^ (-((m - j + 1 : ℕ) : ℤ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hih_j (Nat.cast_nonneg _)) hbd_df (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (expDerivC_nonneg hCf j) hB)
                (zpow_nonneg (edgeW_pos hτ0).le _)))
        _ = (Nat.choose m j : ℝ) * expDerivC Cf j * Cf (m - j + 1) * B *
              (edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((m - j + 1 : ℕ) : ℤ))) := by ring
        _ = _ := by rw [hw_eq]

/-- Uniform outer shoulder IBP bounds for `fctWarpIntegrand`, `fctWarpIntegrandDerivL`, and
`fctWarpIntegrandDerivAlpha` on `(0, ∞)` using `outerChiOut c`. -/
theorem fctWarpOuter_shoulder_bounds :
    ∃ (C c₀ : ℝ), 0 ≤ C ∧ 16 ≤ c₀ ∧
      ∀ {K4 ε c L1 α : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
        concreteEll1 ε c L1 ∈ Set.Ioo (0 : ℝ) 2.55 →
        |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 →
        IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ) (Ioi 0) ∧
        IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ) (Ioi 0) ∧
        IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) (Ioi 0) ∧
        ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ‖ ≤ C * c ^ (-(31 / 8 : ℝ)) ∧
        ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ‖ ≤ C * c ^ (-(23 / 8 : ℝ)) ∧
        ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ‖ ≤ C * c ^ (-(31 / 8 : ℝ)) := by
  let n : ℕ := 15
  obtain ⟨κ_Phi, C_phi0, K_Phi, hκ_pos, hCc0_ge1, hK_nn, hPhi_sh⟩ := outerPhi_shoulder_bounds n (by norm_num)
  obtain ⟨C_ibp, hCibp_nn, hibp⟩ := fct_edge_ibp_shoulder (n := n) (by norm_num) hκ_pos hK_nn
  obtain ⟨C_χ, hCχ0, hχ_all⟩ := outerChiOut_edge_bounds n
  obtain ⟨B_v, _, C_v, _, _, C_α, hBv0, _, hCv0, _, _, hCα0, hv_th⟩ := vTotal_thetaD_edge_bounds n
  obtain ⟨C_w, hCw0, hCw_bd⟩ := warpAmpScal_edge_bounds n
  obtain ⟨C_tw, hCtw0, hCtw_bd⟩ := tau_mul_warpAmpScal_edge_bounds n
  obtain ⟨C_pk, hCpk0, hCpk_bd⟩ := phiKill_edge_bounds n
  obtain ⟨C_mInv, hCmInv0, hmInv_cd, hmInv_bd⟩ := mInv_tau1_edge_bounds n
  let B_chi : ℝ := (2 : ℝ) ^ n * ∑ j ∈ range (n + 1), C_χ j
  have hBχ_nn : 0 ≤ B_chi := mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hCχ0 j)
  let Cf_exp : ℕ → ℝ := fun k => (n.factorial : ℝ) / 12 + C_v k
  have hCf_exp0 : ∀ k, 0 ≤ Cf_exp k := fun k => add_nonneg (by positivity) (hCv0 k)
  let B_exp : ℝ := Real.exp (1 / 6 + B_v)
  have hBexp0 : 0 ≤ B_exp := (Real.exp_pos _).le
  let D_exp : ℕ → ℝ := expDerivC Cf_exp
  have hD_exp0 : ∀ k, 0 ≤ D_exp k := expDerivC_nonneg hCf_exp0
  let Mθ1 : ℝ := max (|ctTheta1 1|) (|ctTheta1 (-1)|)
  let c₀ : ℝ := max 16 (max C_phi0 (max (10 * Mθ1) 1) ^ 2)
  have hc0_16 : 16 ≤ c₀ := le_max_left _ _
  have hc0_phi : C_phi0 ≤ c₀ := by
    have h1 : C_phi0 ≤ max C_phi0 (max (10 * Mθ1) 1) := le_max_left _ _
    have h2 : 1 ≤ max C_phi0 (max (10 * Mθ1) 1) := le_trans hCc0_ge1 h1
    have h3 : max C_phi0 (max (10 * Mθ1) 1) ≤ max C_phi0 (max (10 * Mθ1) 1) ^ 2 := by nlinarith only [h2]
    exact (h1.trans h3).trans (le_max_right _ _)
  let K_pkM : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * C_pk j * C_mInv (k - j)
  have hKpkM0 : ∀ k, 0 ≤ K_pkM k := fun k =>
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCpk0 _)) (hCmInv0 _)
  let K_fac : ℕ → ℝ := fun k => 1 + 3 * K_pkM k
  have hKfac0 : ∀ k, 0 ≤ K_fac k := fun k => add_nonneg zero_le_one (mul_nonneg (by norm_num) (hKpkM0 k))
  let K_base : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * (D_exp j * B_exp) * C_w
  let K_baseL1 : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * (D_exp j * B_exp) * C_tw
  let K_amp0 : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * K_base j * K_fac (k - j)
  let K_ampAlpha : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * K_amp0 j * C_α (k - j)
  let K_ampL1 : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * K_baseL1 j * K_fac (k - j)
  let K_ampL2 : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * K_base j * K_pkM (k - j)
  have hKbase0 : ∀ k, 0 ≤ K_base k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hD_exp0 j) hBexp0)) hCw0
  have hKbaseL10 : ∀ k, 0 ≤ K_baseL1 k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hD_exp0 j) hBexp0)) hCtw0
  have hKamp00 : ∀ k, 0 ≤ K_amp0 k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKbase0 j)) (hKfac0 _)
  have hKampA0 : ∀ k, 0 ≤ K_ampAlpha k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKamp00 j)) (hCα0 _)
  have hKampL10 : ∀ k, 0 ≤ K_ampL1 k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKbaseL10 j)) (hKfac0 _)
  have hKampL20 : ∀ k, 0 ≤ K_ampL2 k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hKbase0 j)) (hKpkM0 _)
  let A_0 : ℝ := ∑ k ∈ range (n + 1), K_amp0 k
  let A_α : ℝ := ∑ k ∈ range (n + 1), K_ampAlpha k
  let A_L1 : ℝ := ∑ k ∈ range (n + 1), K_ampL1 k
  let A_L2 : ℝ := ∑ k ∈ range (n + 1), K_ampL2 k
  have hA0 : 0 ≤ A_0 := Finset.sum_nonneg fun k _ => hKamp00 k
  have hAα : 0 ≤ A_α := Finset.sum_nonneg fun k _ => hKampA0 k
  have hAL1 : 0 ≤ A_L1 := Finset.sum_nonneg fun k _ => hKampL10 k
  have hAL2 : 0 ≤ A_L2 := Finset.sum_nonneg fun k _ => hKampL20 k
  let C_fin : ℝ := C_ibp * B_chi * (A_0 + A_α + (A_L1 + A_L2)) * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))
  have hCfin : 0 ≤ C_fin := mul_nonneg (mul_nonneg (mul_nonneg hCibp_nn hBχ_nn)
    (by linarith only [hA0, hAα, hAL1, hAL2])) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨C_fin, c₀, hCfin, hc0_16, fun {K4 ε c L1 α} hK4 hε hc hτD hK4τ hL1 hα => ?_⟩
  have hc16 : (16 : ℝ) ≤ c := hc0_16.trans hc
  have hc_phi : C_phi0 ≤ c := hc0_phi.trans hc
  have hc1 : 1 ≤ c := by linarith only [hc16]
  have hc0 : 0 < c := by linarith only [hc1]
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hL1_abs : |L1| ≤ 3 * c ^ (-(1 / 2 : ℝ)) := by
    have hτ₁2 : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hL1_eq : L1 = concreteEll1 ε c L1 * τ₁ ^ 2 + ctTheta1 ε / c := by
      unfold concreteEll1; have hne := (sq_pos_of_pos hτ₁).ne'; field_simp [hne]; ring
    have hM_bd : |ctTheta1 ε| ≤ Mθ1 := by rcases hε with rfl | rfl; exact le_max_left _ _; exact le_max_right _ _
    have h10M : max (10 * Mθ1) 1 ^ 2 ≤ c :=
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2).trans ((le_max_right _ _).trans hc)
    have h_sqrt : max (10 * Mθ1) 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le h10M
    have hθ_c : |ctTheta1 ε| * c ^ (-(1 / 2 : ℝ)) ≤ 0.45 := by
      by_cases hM0 : Mθ1 = 0
      · have : |ctTheta1 ε| = 0 := le_antisymm (by linarith only [hM_bd, hM0]) (abs_nonneg _)
        rw [this, zero_mul]; norm_num
      · have hMpos : 0 < 10 * Mθ1 := by
          have : 0 ≤ Mθ1 := (abs_nonneg _).trans (le_max_left _ _)
          linarith only [lt_of_le_of_ne this (Ne.symm (by intro h; apply hM0; linarith only [h]))]
        have hc12_ge : 10 * Mθ1 ≤ c ^ (1 / 2 : ℝ) := (le_max_left _ _).trans h_sqrt
        rw [Real.rpow_neg hc0.le]
        calc |ctTheta1 ε| * (c ^ (1 / 2 : ℝ))⁻¹ ≤ Mθ1 * (10 * Mθ1)⁻¹ :=
              mul_le_mul hM_bd (inv_anti₀ hMpos hc12_ge) (inv_nonneg.mpr (by positivity)) (by linarith only [hMpos])
          _ = 0.1 := by field_simp [hMpos.ne']; norm_num
          _ ≤ 0.45 := by norm_num
    have hc_split : c⁻¹ = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
    have hell_abs : |concreteEll1 ε c L1| ≤ 2.55 := by rw [abs_of_pos hL1.1]; exact hL1.2.le
    rw [hL1_eq]
    calc |concreteEll1 ε c L1 * τ₁ ^ 2 + ctTheta1 ε / c|
        ≤ |concreteEll1 ε c L1| * |τ₁ ^ 2| + |ctTheta1 ε| * c⁻¹ :=
            (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]) (by rw [abs_div, abs_of_pos hc0, div_eq_mul_inv]))
      _ ≤ 2.55 * c ^ (-(1 / 2 : ℝ)) + (|ctTheta1 ε| * c ^ (-(1 / 2 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by
            rw [abs_of_pos (sq_pos_of_pos hτ₁), hτ₁2, hc_split, ← mul_assoc]
            exact add_le_add (mul_le_mul_of_nonneg_right hell_abs (by positivity)) le_rfl
      _ ≤ 2.55 * c ^ (-(1 / 2 : ℝ)) + 0.45 * c ^ (-(1 / 2 : ℝ)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hθ_c (by positivity))
      _ = 3 * c ^ (-(1 / 2 : ℝ)) := by ring
  obtain ⟨hPhi_cd, hPhi'_lb, hPhi_bd⟩ := hPhi_sh hK4 hε hc_phi hτD hK4τ hL1.2 hα
  obtain ⟨hχ_cd, hχ_zero, _, hχ_bd⟩ := hχ_all hc0
  obtain ⟨hv_cd, _, hva_cd, htha_cd, hv_pt⟩ := hv_th hK4 hc1 hτD hK4τ hα
  obtain ⟨hbin_cd, hbin_0, hbin_k⟩ := binetImag_edge_bounds n hc1
  have hc_a : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hrpow_ibp : ((c * c ^ (-(1 / 2 : ℝ))) ^ n)⁻¹ * (1.85 * c ^ (-(1 / 4 : ℝ))) ^ (1 / 2 - (n : ℝ)) =
      (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)) := by
    have hcu : c * c ^ (-(1 / 2 : ℝ)) = c ^ (1 / 2 : ℝ) := by
      conv_lhs => arg 1; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc0]; norm_num
    have hpow : ((c ^ (1 / 2 : ℝ)) ^ n)⁻¹ = c ^ (-(15 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_neg hc0.le]; dsimp only [n]; norm_num
    have hmul : (1.85 * c ^ (-(1 / 4 : ℝ))) ^ (1 / 2 - (n : ℝ)) =
        (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (29 / 8 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hτ₁.le, ← Real.rpow_mul hc0.le]; dsimp only [n]; congr 2; norm_num
    rw [hcu, hpow, hmul]
    calc c ^ (-(15 / 2 : ℝ)) * ((1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (29 / 8 : ℝ))
        = (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * (c ^ (-(15 / 2 : ℝ)) * c ^ (29 / 8 : ℝ)) := by ring
      _ = (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)) := by
          rw [← Real.rpow_add hc0]; congr 2; norm_num
  set S : Set ℝ := Ioi (1.85 * τ₁)
  have hS : IsOpen S := isOpen_Ioi
  have hS0 : ∀ τ ∈ S, τ ≠ 0 := fun τ hτ => (lt_trans (by positivity) hτ).ne'
  let f1_exp : ℝ → ℂ := fun t => FormalResearch.Asymptotics.binetDiff c (Complex.I * (t : ℂ))
  let f2_exp : ℝ → ℂ := fun t => ((vTotal StripKernelChoice.star K4 c α τ₁ t : ℝ) : ℂ)
  let f_exp : ℝ → ℂ := fun t => f1_exp t + f2_exp t
  have hf1_exp_cd : ContDiff ℝ ∞ f1_exp := hbin_cd.of_le le_top
  have hf2_exp_cd : ContDiff ℝ ∞ f2_exp :=
    (Complex.ofRealCLM.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).comp hv_cd
  have hf_exp_cd : ContDiff ℝ ∞ f_exp := hf1_exp_cd.add hf2_exp_cd
  have h_cexp_cd : ContDiffOn ℝ (n : ℕ) (fun t => Complex.exp (f_exp t)) (Ioi 0) :=
    hf_exp_cd.cexp.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)
  have h_cexp_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t => Complex.exp (f_exp t)) τ‖ ≤ D_exp k * B_exp * edgeW τ ^ (-(k : ℤ)) := by
    refine cexp_iteratedDeriv_uniform hCf_exp0 hS hS0 (hf_exp_cd.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)) hBexp0 ?_ ?_
    · intro τ hτ
      have hv0 : |vTotal StripKernelChoice.star K4 c α τ₁ τ| ≤ B_v := by
        have := (hv_pt τ hτ).1; linarith only [this, abs_nonneg (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁) τ)]
      have hre : (f_exp τ).re ≤ 1 / 6 + B_v := by
        have hr1 : (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))).re ≤ 1 / 6 :=
          (abs_le.mp ((Complex.abs_re_le_norm _).trans (hbin_0 τ))).2
        have hr3 : (f_exp τ).re = (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))).re +
            vTotal StripKernelChoice.star K4 c α τ₁ τ := by simp [f_exp, f1_exp, f2_exp]
        linarith only [hr1, hr3, (abs_le.mp hv0).2]
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hre
    · intro k hk1 hkn τ hτ
      have hτ0 : τ ≠ 0 := hS0 τ hτ
      have hcd1 : ContDiffAt ℝ k f1_exp τ := hf1_exp_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hcd2 : ContDiffAt ℝ k f2_exp τ := hf2_exp_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      change ‖iteratedDeriv k (f1_exp + f2_exp) τ‖ ≤ _
      rw [iteratedDeriv_add hcd1 hcd2]
      have h1 := hbin_k k hk1 hkn τ hτ0
      have h2 := ((hv_pt τ hτ).2.2.1 k hkn).1
      have h2C : ‖iteratedDeriv k f2_exp τ‖ ≤ C_v k * edgeW τ ^ (-(k : ℤ)) := by
        rw [ofReal_iteratedDeriv_eq hS (hv_cd.contDiffOn.mono (subset_univ _)) k τ hτ,
          Complex.norm_real, Real.norm_eq_abs]
        exact h2
      calc ‖iteratedDeriv k f1_exp τ + iteratedDeriv k f2_exp τ‖
          ≤ ‖iteratedDeriv k f1_exp τ‖ + ‖iteratedDeriv k f2_exp τ‖ := norm_add_le _ _
        _ ≤ (n.factorial : ℝ) / 12 * edgeW τ ^ (-(k : ℤ)) + C_v k * edgeW τ ^ (-(k : ℤ)) := add_le_add h1 h2C
        _ = Cf_exp k * edgeW τ ^ (-(k : ℤ)) := by dsimp only [Cf_exp]; ring
  have hw_cd : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => ((warpAmpScal t : ℝ) : ℂ)) (Ioi 0) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_warpAmpScal).of_le (WithTop.coe_le_coe.mpr le_top)
  have htw_cd : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => (((t * warpAmpScal t : ℝ) : ℂ))) (Ioi 0) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_id.contDiffOn.mul contDiffOn_warpAmpScal)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hw_S_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t : ℝ => ((warpAmpScal t : ℝ) : ℂ)) τ‖ ≤
        C_w * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
    refine ofReal_edge_bounds hS (contDiffOn_warpAmpScal.mono (fun _ ht => lt_trans (by positivity) ht)) ?_
    intro k hk τ hτ
    have := hCw_bd k hk τ (lt_trans (by positivity) hτ)
    linarith only [this, show C_w * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) =
      C_w * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) by ring]
  have htw_S_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t : ℝ => (((t * warpAmpScal t : ℝ) : ℂ))) τ‖ ≤
        C_tw * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
    refine ofReal_edge_bounds hS ((contDiff_id.contDiffOn.mul contDiffOn_warpAmpScal).mono
      (fun _ ht => lt_trans (by positivity) ht)) ?_
    intro k hk τ hτ
    have := hCtw_bd k hk τ (lt_trans (by positivity) hτ)
    linarith only [this, show C_tw * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) =
      C_tw * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) by ring]
  have hbase_cd : ContDiffOn ℝ (n : ℕ) (concreteEdgeAmpBase K4 c α) (Ioi 0) :=
    (h_cexp_cd.mul hw_cd).congr fun t _ => rfl
  have hbase_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (concreteEdgeAmpBase K4 c α) τ‖ ≤
        K_base k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk τ hτ
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (h_cexp_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hw_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun _ _ => zero_le_one)
      (fun t ht => mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) ht).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) ht]) _))
      (fun j _ => mul_nonneg (hD_exp0 j) hBexp0) (fun _ _ => hCw0)
      (fun j hj t ht => by rw [mul_one]; exact h_cexp_bd j hj t ht)
      hw_S_bd k hk τ hτ
    rw [one_mul] at hmul; exact hmul
  let baseL1 : ℝ → ℂ := fun t => Complex.exp (f_exp t) * (((t * warpAmpScal t : ℝ) : ℂ))
  have hbaseL1_cd : ContDiffOn ℝ (n : ℕ) baseL1 (Ioi 0) := h_cexp_cd.mul htw_cd
  have hbaseL1_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k baseL1 τ‖ ≤
        K_baseL1 k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk τ hτ
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (h_cexp_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (htw_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun _ _ => zero_le_one)
      (fun t ht => mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) ht).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) ht]) _))
      (fun j _ => mul_nonneg (hD_exp0 j) hBexp0) (fun _ _ => hCtw0)
      (fun j hj t ht => by rw [mul_one]; exact h_cexp_bd j hj t ht)
      htw_S_bd k hk τ hτ
    rw [one_mul] at hmul; exact hmul
  let pkM : ℝ → ℂ := fun t => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) / (uctM t : ℂ)
  have hpkM_cd : ContDiffOn ℝ (n : ℕ) pkM (Ioi 0) := by
    have h1 : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)) (Ioi 0) :=
      (FctSym.contDiff_phiKill_imag hc_a).contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)
    have h2 : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => (((uctM t)⁻¹ : ℝ) : ℂ)) (Ioi 0) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hmInv_cd).of_le (WithTop.coe_le_coe.mpr le_top)
    exact (h1.mul h2).congr fun t _ => by dsimp only [pkM]; rw [Complex.ofReal_inv, div_eq_mul_inv]
  have hpkM_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k pkM τ‖ ≤ K_pkM k * c ^ (1 / 2 : ℝ) * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk τ hτ
    have h1 : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)) S :=
      ((FctSym.contDiff_phiKill_imag hc_a).contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)).mono (subset_univ _)
    have h2 : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => (((uctM t)⁻¹ : ℝ) : ℂ)) S :=
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hmInv_cd).of_le (WithTop.coe_le_coe.mpr le_top)).mono
        fun _ ht => lt_trans (by positivity) ht
    have hmInv_C_bd : ∀ j ≤ n, ∀ t ∈ S,
        ‖iteratedDeriv j (fun s : ℝ => (((uctM s)⁻¹ : ℝ) : ℂ)) t‖ ≤
          C_mInv j * c ^ (1 / 2 : ℝ) * edgeW t ^ (-(j : ℤ)) := by
      refine ofReal_edge_bounds hS (hmInv_cd.mono (fun _ ht => lt_trans (by positivity) ht)) ?_
      intro j hj t ht; exact hmInv_bd hc1 ht j hj
    have hmul := iteratedDeriv_mul_edgeW hS hS0 h1 h2 (fun _ _ => zero_le_one)
      (fun _ _ => Real.rpow_nonneg hc0.le _) (fun j _ => hCpk0 j) (fun j _ => hCmInv0 j)
      (fun j hj t ht => by rw [mul_one]; exact hCpk_bd hc_a (lt_trans (by positivity) ht) j hj)
      hmInv_C_bd k hk τ hτ
    rw [one_mul] at hmul
    rwa [show pkM = fun t : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) * (((uctM t)⁻¹ : ℝ) : ℂ) from by
      ext t; dsimp only [pkM]; rw [Complex.ofReal_inv, div_eq_mul_inv]]
  let fac : ℝ → ℂ := fun t => (1 : ℂ) - (L1 : ℂ) * pkM t
  have hfac_cd : ContDiffOn ℝ (n : ℕ) fac (Ioi 0) := contDiffOn_const.sub (contDiffOn_const.mul hpkM_cd)
  have hfac_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k fac τ‖ ≤ K_fac k * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk τ hτ
    have hτ0 : τ ≠ 0 := hS0 τ hτ
    have hw_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos hτ0).le _
    have h1_w : 1 ≤ edgeW τ ^ (-(k : ℤ)) := one_le_edgeW_inv hτ0 k
    have hcd1 : ContDiffAt ℝ k (fun _ : ℝ => (1 : ℂ)) τ := contDiffAt_const
    have hcd2 : ContDiffAt ℝ k (fun t : ℝ => (L1 : ℂ) * pkM t) τ :=
      contDiffAt_const.mul ((hpkM_cd.contDiffAt (isOpen_Ioi.mem_nhds (lt_trans (by positivity) hτ))).of_le
        (by exact_mod_cast hk))
    change ‖iteratedDeriv k ((fun _ : ℝ => (1 : ℂ)) - fun t => (L1 : ℂ) * pkM t) τ‖ ≤ _
    rw [iteratedDeriv_sub hcd1 hcd2, iteratedDeriv_const_mul_field]
    have hpk := hpkM_bd k hk τ hτ
    have hLpk : ‖(L1 : ℂ) * iteratedDeriv k pkM τ‖ ≤ 3 * K_pkM k * edgeW τ ^ (-(k : ℤ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hcc : c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; norm_num
      calc |L1| * ‖iteratedDeriv k pkM τ‖
          ≤ (3 * c ^ (-(1 / 2 : ℝ))) * (K_pkM k * c ^ (1 / 2 : ℝ) * edgeW τ ^ (-(k : ℤ))) :=
            mul_le_mul hL1_abs hpk (norm_nonneg _) (by positivity)
        _ = 3 * K_pkM k * (c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ)) * edgeW τ ^ (-(k : ℤ)) := by ring
        _ = 3 * K_pkM k * edgeW τ ^ (-(k : ℤ)) := by rw [hcc, mul_one]
    have hc_bd : ‖iteratedDeriv k (fun _ : ℝ => (1 : ℂ)) τ‖ ≤ 1 * edgeW τ ^ (-(k : ℤ)) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · rw [iteratedDeriv_zero, norm_one, one_mul]; exact h1_w
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
        rw [iteratedDeriv_succ', deriv_const', show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl,
          iteratedDeriv_const_zero, norm_zero, one_mul]
        exact hw_nn
    calc ‖iteratedDeriv k (fun _ => (1 : ℂ)) τ - (L1 : ℂ) * iteratedDeriv k pkM τ‖
        ≤ ‖iteratedDeriv k (fun _ => (1 : ℂ)) τ‖ + ‖(L1 : ℂ) * iteratedDeriv k pkM τ‖ := norm_sub_le _ _
      _ ≤ 1 * edgeW τ ^ (-(k : ℤ)) + 3 * K_pkM k * edgeW τ ^ (-(k : ℤ)) := add_le_add hc_bd hLpk
      _ = K_fac k * edgeW τ ^ (-(k : ℤ)) := by dsimp only [K_fac]; ring
  have hibp_c := fun {A_f : ℝ} (hAf : 0 ≤ A_f) {f : ℝ → ℂ} hf_cd hf_bd =>
    outer_shoulder_ibp_helper (κ_Phi := κ_Phi) (f := f) (Φ := outerPhi K4 ε c L1 α) hc0 hCibp_nn hAf hCχ0
      (fun {u r A a} => hibp (c := c) (u := u) (r := r) (A := A) (a := a) (Φ := outerPhi K4 ε c L1 α) hc0)
      hc16 hPhi_cd hPhi'_lb hPhi_bd hχ_cd hχ_zero hχ_bd hf_cd hf_bd
  -- (1) `I_out`
  have hamp0_cd : ContDiffOn ℝ (n : ℕ) (concreteEdgeAmp K4 c L1 α) (Ioi 0) :=
    (hbase_cd.mul hfac_cd).congr fun t _ => by
      dsimp only [fac, pkM]
      rw [← mul_div_assoc]
      exact concreteEdgeAmp_eq_base_mul K4 c L1 α t
  have hamp0_K : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (concreteEdgeAmp K4 c L1 α) τ‖ ≤
        K_amp0 k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk τ hτ
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (hbase_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hfac_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun t ht => mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) ht).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) ht]) _))
      (fun _ _ => zero_le_one) (fun j _ => hKbase0 j) (fun j _ => hKfac0 j) hbase_bd
      (fun j hj t ht => by rw [mul_one]; exact hfac_bd j hj t ht) k hk τ hτ
    rw [mul_one, show (fun t => concreteEdgeAmpBase K4 c α t * fac t) = concreteEdgeAmp K4 c L1 α from by
      ext t; dsimp only [fac, pkM]
      rw [← mul_div_assoc]
      exact (concreteEdgeAmp_eq_base_mul K4 c L1 α t).symm] at hmul
    exact hmul
  have hamp0_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (concreteEdgeAmp K4 c L1 α) τ‖ ≤
        A_0 * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := fun k hk τ hτ => by
    have hK_le : K_amp0 k ≤ A_0 := Finset.single_le_sum (fun j _ => hKamp00 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have htw_nn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) :=
      mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) hτ).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) hτ]) _)
    refine (hamp0_K k hk τ hτ).trans ?_
    calc K_amp0 k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ))
        ≤ A_0 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le htw_nn)
            (zpow_nonneg (edgeW_pos (hS0 τ hτ)).le _)
      _ = A_0 * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring
  obtain ⟨hI0_int, hI0_bd⟩ := hibp_c hA0 hamp0_cd hamp0_bd
  have hI0_eqOn : EqOn (fun τ => ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ)
      (fun τ => ((outerChiOut c τ : ℝ) : ℂ) * concreteEdgeAmp K4 c L1 α τ *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L1 α τ - π / 4 : ℝ) : ℂ))) (Ioi 0) := fun τ hτ => by
    dsimp only
    rw [fctWarpIntegrand_eq_edge hε hc0 hτ, outerPhi_eq_concretePhiTilde hτ]; ring
  have hI0_int' := IntegrableOn.congr_fun hI0_int (fun τ hτ => (hI0_eqOn hτ).symm) measurableSet_Ioi
  have hI0_bd' : ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ‖ ≤
      C_fin * c ^ (-(31 / 8 : ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hI0_eqOn]
    refine hI0_bd.trans ?_; rw [mul_assoc _ (((c * c ^ (-(1 / 2 : ℝ))) ^ n)⁻¹), hrpow_ibp]; dsimp only [B_chi, C_fin]
    have hsum : A_0 ≤ A_0 + A_α + (A_L1 + A_L2) := by linarith only [hAα, hAL1, hAL2]
    calc C_ibp * (B_chi * A_0) * ((1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)))
        = (C_ibp * B_chi * A_0 * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(31 / 8 : ℝ)) := by ring
      _ ≤ _ := by gcongr
  -- (2) `Ialpha_out`
  let vα_C : ℝ → ℂ := fun t => ((vAlpha 1 τ₁ t : ℝ) : ℂ) + Complex.I * ((fctThetaD (vAlpha 1 τ₁) t : ℝ) : ℂ)
  have hva_C_cd : ContDiff ℝ ∞ (fun t : ℝ => ((vAlpha 1 τ₁ t : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).comp hva_cd
  have htha_C_cd : ContDiff ℝ ∞ (fun t : ℝ => Complex.I * ((fctThetaD (vAlpha 1 τ₁) t : ℝ) : ℂ)) :=
    contDiff_const.mul ((Complex.ofRealCLM.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).comp htha_cd)
  have hvα_cd : ContDiffOn ℝ (n : ℕ) vα_C (Ioi 0) :=
    (hva_C_cd.add htha_C_cd).contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)
  have hvα_bd : ∀ k ≤ n, ∀ τ ∈ S, ‖iteratedDeriv k vα_C τ‖ ≤ C_α k * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk τ hτ
    have hcd1 : ContDiffAt ℝ k (fun t : ℝ => ((vAlpha 1 τ₁ t : ℝ) : ℂ)) τ :=
      hva_C_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hcd2 : ContDiffAt ℝ k (fun t : ℝ => Complex.I * ((fctThetaD (vAlpha 1 τ₁) t : ℝ) : ℂ)) τ :=
      htha_C_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    change ‖iteratedDeriv k ((fun t : ℝ => ((vAlpha 1 τ₁ t : ℝ) : ℂ)) +
      fun t => Complex.I * ((fctThetaD (vAlpha 1 τ₁) t : ℝ) : ℂ)) τ‖ ≤ _
    rw [iteratedDeriv_add hcd1 hcd2, iteratedDeriv_const_mul_field]
    have h1 := ((hv_pt τ hτ).2.2.1 k hk).2.2
    have h_v : ‖iteratedDeriv k (fun t : ℝ => ((vAlpha 1 τ₁ t : ℝ) : ℂ)) τ‖ ≤
        |iteratedDeriv k (vAlpha 1 τ₁) τ| := by
      rw [ofReal_iteratedDeriv_eq hS (hva_cd.contDiffOn.mono (subset_univ _)) k τ hτ,
        Complex.norm_real, Real.norm_eq_abs]
    have h_th : ‖Complex.I * iteratedDeriv k (fun t : ℝ => ((fctThetaD (vAlpha 1 τ₁) t : ℝ) : ℂ)) τ‖ ≤
        |iteratedDeriv k (fctThetaD (vAlpha 1 τ₁)) τ| := by
      rw [norm_mul, Complex.norm_I, one_mul,
        ofReal_iteratedDeriv_eq hS (htha_cd.contDiffOn.mono (subset_univ _)) k τ hτ,
        Complex.norm_real, Real.norm_eq_abs]
    exact (norm_add_le _ _).trans ((add_le_add h_v h_th).trans h1)
  let ampAlpha : ℝ → ℂ := fun t => concreteEdgeAmp K4 c L1 α t * vα_C t
  have hampA_cd : ContDiffOn ℝ (n : ℕ) ampAlpha (Ioi 0) := hamp0_cd.mul hvα_cd
  have hampA_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k ampAlpha τ‖ ≤
        A_α * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by
    intro k hk τ hτ
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (hamp0_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hvα_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun t ht => mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) ht).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) ht]) _))
      (fun _ _ => zero_le_one) (fun j _ => hKamp00 j) (fun j _ => hCα0 j)
      hamp0_K (fun j hj t ht => by rw [mul_one]; exact hvα_bd j hj t ht) k hk τ hτ
    rw [mul_one] at hmul
    have hK_le : K_ampAlpha k ≤ A_α := Finset.single_le_sum (fun j _ => hKampA0 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have htw_nn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) :=
      mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) hτ).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) hτ]) _)
    refine hmul.trans ?_
    calc K_ampAlpha k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ))
        ≤ A_α * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le htw_nn)
            (zpow_nonneg (edgeW_pos (hS0 τ hτ)).le _)
      _ = A_α * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring
  obtain ⟨hIa_int, hIa_bd⟩ := hibp_c hAα hampA_cd hampA_bd
  have hIa_eqOn : EqOn (fun τ => ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ)
      (fun τ => ((outerChiOut c τ : ℝ) : ℂ) * ampAlpha τ *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L1 α τ - π / 4 : ℝ) : ℂ))) (Ioi 0) := fun τ hτ => by
    dsimp only
    rw [fctWarpIntegrandDerivAlpha_eq_edge hε hc0 hτ, outerPhi_eq_concretePhiTilde hτ]; dsimp only [ampAlpha, vα_C]; ring
  have hIa_int' := IntegrableOn.congr_fun hIa_int (fun τ hτ => (hIa_eqOn hτ).symm) measurableSet_Ioi
  have hIa_bd' : ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivAlpha K4 ε c L1 α τ‖ ≤
      C_fin * c ^ (-(31 / 8 : ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hIa_eqOn]
    refine hIa_bd.trans ?_; rw [mul_assoc _ (((c * c ^ (-(1 / 2 : ℝ))) ^ n)⁻¹), hrpow_ibp]; dsimp only [B_chi, C_fin]
    have hsum : A_α ≤ A_0 + A_α + (A_L1 + A_L2) := by linarith only [hA0, hAL1, hAL2]
    calc C_ibp * (B_chi * A_α) * ((1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)))
        = (C_ibp * B_chi * A_α * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(31 / 8 : ℝ)) := by ring
      _ ≤ _ := by gcongr
  -- (3) `IL_out = IL_1 - IL_2`
  let ampL1 : ℝ → ℂ := fun t => Complex.I * (c : ℂ) * (baseL1 t * fac t)
  let ampL2 : ℝ → ℂ := fun t => concreteEdgeAmpBase K4 c α t * pkM t
  have hampL1_cd : ContDiffOn ℝ (n : ℕ) ampL1 (Ioi 0) :=
    contDiffOn_const.mul (hbaseL1_cd.mul hfac_cd)
  have hampL2_cd : ContDiffOn ℝ (n : ℕ) ampL2 (Ioi 0) := hbase_cd.mul hpkM_cd
  have hampL1_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k ampL1 τ‖ ≤
        (c * A_L1) * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by
    intro k hk τ hτ
    have hprod_cd : ContDiffAt ℝ k (fun t => baseL1 t * fac t) τ :=
      ((hbaseL1_cd.mul hfac_cd).contDiffAt (isOpen_Ioi.mem_nhds (lt_trans (by positivity) hτ))).of_le
        (by exact_mod_cast hk)
    change ‖iteratedDeriv k (fun t => (Complex.I * (c : ℂ)) * (baseL1 t * fac t)) τ‖ ≤ _
    rw [iteratedDeriv_const_mul_field, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hc0.le]
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (hbaseL1_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hfac_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun t ht => mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) ht).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) ht]) _))
      (fun _ _ => zero_le_one) (fun j _ => hKbaseL10 j) (fun j _ => hKfac0 j) hbaseL1_bd
      (fun j hj t ht => by rw [mul_one]; exact hfac_bd j hj t ht) k hk τ hτ
    rw [mul_one] at hmul
    have hK_le : K_ampL1 k ≤ A_L1 := Finset.single_le_sum (fun j _ => hKampL10 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have htw_nn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) :=
      mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) hτ).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) hτ]) _)
    calc c * ‖iteratedDeriv k (fun t => baseL1 t * fac t) τ‖
        ≤ c * (K_ampL1 k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ))) :=
          mul_le_mul_of_nonneg_left hmul hc0.le
      _ ≤ c * (A_L1 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le htw_nn)
              (zpow_nonneg (edgeW_pos (hS0 τ hτ)).le _))
            hc0.le
      _ = (c * A_L1) * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring
  have hampL2_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k ampL2 τ‖ ≤
        (c * A_L2) * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by
    intro k hk τ hτ
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (hbase_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hpkM_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun t ht => mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) ht).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) ht]) _))
      (fun _ _ => Real.rpow_nonneg hc0.le _) (fun j _ => hKbase0 j) (fun j _ => hKpkM0 j)
      hbase_bd hpkM_bd k hk τ hτ
    have hK_le : K_ampL2 k ≤ A_L2 := Finset.single_le_sum (fun j _ => hKampL20 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have hc12_le : c ^ (1 / 2 : ℝ) ≤ c := by
      conv_rhs => rw [← Real.rpow_one c]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have htw_nn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) :=
      mul_nonneg (Real.rpow_nonneg (lt_trans (by positivity) hτ).le _)
        (zpow_nonneg (by linarith only [lt_trans (by positivity) hτ]) _)
    refine hmul.trans ?_
    calc K_ampL2 k * ((τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * c ^ (1 / 2 : ℝ)) * edgeW τ ^ (-(k : ℤ))
        ≤ A_L2 * ((τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * c) * edgeW τ ^ (-(k : ℤ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hK_le (mul_le_mul_of_nonneg_left hc12_le htw_nn)
              (mul_nonneg htw_nn (Real.rpow_nonneg hc0.le _)) hAL2)
            (zpow_nonneg (edgeW_pos (hS0 τ hτ)).le _)
      _ = (c * A_L2) * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring
  obtain ⟨hIL1_int, hIL1_bd⟩ := hibp_c (mul_nonneg hc0.le hAL1) hampL1_cd hampL1_bd
  obtain ⟨hIL2_int, hIL2_bd⟩ := hibp_c (mul_nonneg hc0.le hAL2) hampL2_cd hampL2_bd
  have hIL_eqOn : EqOn (fun τ => ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ)
      (fun τ => ((outerChiOut c τ : ℝ) : ℂ) * ampL1 τ *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L1 α τ - π / 4 : ℝ) : ℂ)) -
      ((outerChiOut c τ : ℝ) : ℂ) * ampL2 τ *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L1 α τ - π / 4 : ℝ) : ℂ))) (Ioi 0) := fun τ hτ => by
    dsimp only
    rw [fctWarpIntegrandDerivL_eq_edge hε hc0 hτ, outerPhi_eq_concretePhiTilde hτ]
    dsimp only [ampL1, ampL2, baseL1, fac, pkM, concreteEdgeAmpBase, f_exp, f1_exp, f2_exp, warpAmpScal]
    have hsq : Real.sqrt (6 / π ^ 2 * uctMderiv τ) = Real.sqrt (π⁻¹ ^ 2 * uctMderiv τ * 6) := by
      congr 1; ring
    have hti : (τ : ℂ) * Complex.I = Complex.I * (τ : ℂ) := mul_comm _ _
    rw [hsq, hti]
    push_cast; ring
  have hIL_int' := IntegrableOn.congr_fun (hIL1_int.sub hIL2_int) (fun τ hτ => (hIL_eqOn hτ).symm) measurableSet_Ioi
  have hIL_bd' : ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrandDerivL K4 ε c L1 α τ‖ ≤
      C_fin * c ^ (-(23 / 8 : ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hIL_eqOn, integral_sub hIL1_int hIL2_int]
    have hc_mul : c * c ^ (-(31 / 8 : ℝ)) = c ^ (-(23 / 8 : ℝ)) := by
      conv_lhs => arg 1; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc0]; norm_num
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * ampL1 τ *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L1 α τ - π / 4 : ℝ) : ℂ))‖ ≤
        (C_ibp * B_chi * A_L1 * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(23 / 8 : ℝ)) := by
      refine hIL1_bd.trans ?_; rw [mul_assoc _ (((c * c ^ (-(1 / 2 : ℝ))) ^ n)⁻¹), hrpow_ibp]
      exact le_of_eq <| calc C_ibp * (B_chi * (c * A_L1)) * ((1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)))
          = (C_ibp * B_chi * A_L1 * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * (c * c ^ (-(31 / 8 : ℝ))) := by ring
        _ = _ := by rw [hc_mul]
    have h2 : ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * ampL2 τ *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L1 α τ - π / 4 : ℝ) : ℂ))‖ ≤
        (C_ibp * B_chi * A_L2 * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(23 / 8 : ℝ)) := by
      refine hIL2_bd.trans ?_; rw [mul_assoc _ (((c * c ^ (-(1 / 2 : ℝ))) ^ n)⁻¹), hrpow_ibp]
      exact le_of_eq <| calc C_ibp * (B_chi * (c * A_L2)) * ((1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)))
          = (C_ibp * B_chi * A_L2 * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * (c * c ^ (-(31 / 8 : ℝ))) := by ring
        _ = _ := by rw [hc_mul]
    refine (add_le_add h1 h2).trans ?_
    have hsum : A_L1 + A_L2 ≤ A_0 + A_α + (A_L1 + A_L2) := by linarith only [hA0, hAα]
    calc (C_ibp * B_chi * A_L1 * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(23 / 8 : ℝ)) +
          (C_ibp * B_chi * A_L2 * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(23 / 8 : ℝ))
        = (C_ibp * B_chi * (A_L1 + A_L2) * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(23 / 8 : ℝ)) := by ring
      _ ≤ (C_ibp * B_chi * (A_0 + A_α + (A_L1 + A_L2)) * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))) * c ^ (-(23 / 8 : ℝ)) := by
          gcongr
  exact ⟨hI0_int', hIL_int', hIa_int', hI0_bd', hIL_bd', hIa_bd'⟩

/-- info: 'FormalResearch.SignUncertainty.fctWarpOuter_shoulder_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpOuter_shoulder_bounds

end FormalResearch.SignUncertainty
