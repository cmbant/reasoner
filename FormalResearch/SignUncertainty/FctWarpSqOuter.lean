/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpOuterIbp
public import FormalResearch.SignUncertainty.FctExactIbp
public import FormalResearch.SignUncertainty.FctPhysicalBudgetConcrete

/-!
# Outer shoulder bounds and MVT estimate for `warpSqDensity` on the Airy window (`fct:warp-win`)

Leaf helper module for `FctWarpAsympWin.lean`:
* Splits off the outer shoulder tail `warpSqOut` of `warpSqDensity` using `outerChiOut c τ`
  on the Airy window `L ∈ [fctWarpL1 h ε c, Sw * c^{-2/3}]`.
* Shows that `warpSqOut K4 ε c L1 α L` and its `L`-derivative `warpSqOutDeriv` satisfy uniform
  shoulder IBP bounds `|warpSqOut| ≤ C * c^{-(85/24)}` and `|warpSqOutDeriv| ≤ C * c^{-(61/24)}`
  via `fct_edge_ibp_shoulder` (`n = 15`) and `outerPhi_shoulder_bounds`, yielding the MVT bound
  `|warpSqOut L - warpSqOut L1| ≤ C * c^{-(61/24)} * (L - L1)`.
* Establishes `fctWarpZero_window_geom`: uniform lower/upper `c^{-2/3}` bounds on `fctWarpL1` and
  verification that `concreteEll1 ε c L ∈ Ioo 0 2.55` across `[fctWarpL1 h ε c, Sw * c^{-2/3}]`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctEdgeIbp FormalResearch.SignUncertainty.FctSym

namespace FormalResearch.SignUncertainty

/-! ### 1. Outer shoulder tail definitions and phase factorization -/

/-- Complex outer-shoulder integral of `warpSqDensity` (`outerChiOut c τ` cutoff). -/
noncomputable def warpSqOutComplex (K4 ε c L1 α L : ℝ) : ℂ :=
  ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
    (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
      fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))

/-- Real outer-shoulder contribution to `warpSqDensity` at `ξ = fctXi1 L`. -/
noncomputable def warpSqOut (K4 ε c L1 α L : ℝ) : ℝ :=
  (c ^ (1 / 3 : ℝ) / π) * (warpSqOutComplex K4 ε c L1 α L).re

/-- `L`-derivative of `warpSqOutComplex`. -/
noncomputable def warpSqOutDerivComplex (K4 ε c L1 α L : ℝ) : ℂ :=
  ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) *
    (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
      fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))

/-- `L`-derivative of `warpSqOut`. -/
noncomputable def warpSqOutDeriv (K4 ε c L1 α L : ℝ) : ℝ :=
  (c ^ (1 / 3 : ℝ) / π) * (warpSqOutDerivComplex K4 ε c L1 α L).re

lemma mellinK0_fctXi1_shift {c L L1 τ : ℝ} :
    mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) =
      Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) *
        mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) := by
  have hξ : 0 < fctXi1 L := by unfold fctXi1; positivity
  have hξ1 : 0 < fctXi1 L1 := by unfold fctXi1; positivity
  rw [FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 L) τ hξ,
    FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 L1) τ hξ1]
  have hlogL : Real.log (π ^ 2 * fctXi1 L) = L := by
    unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
  have hlog1 : Real.log (π ^ 2 * fctXi1 L1) = L1 := by
    unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
  rw [hlogL, hlog1]
  have hex : Complex.I * (c : ℂ) * ((L * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) =
      Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ) +
        Complex.I * (c : ℂ) * ((L1 * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) := by
    push_cast; ring
  rw [hex, Complex.exp_add]; ring

lemma mellin_fctWarpA_eq_edge {K4 ε c L1 α L τ : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hc : 0 < c) (hτ : 0 < τ) :
    mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ)) *
        concreteEdgeAmp K4 c L1 α τ := by
  have h1 : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) * fctWarpIntegrand K4 ε c L1 α τ := by
    rw [mellinK0_fctXi1_shift (L1 := L1)]; unfold fctWarpIntegrand; ring
  have hphi : concretePhiTilde K4 ε c τ (L, α) = concretePhiTilde K4 ε c τ (L1, α) + (L - L1) * τ := by
    simp only [concretePhiTilde, concretePhiLambda, concretePhiPh]; ring
  rw [h1, fctWarpIntegrand_eq_edge hε hc hτ, outerPhi_eq_concretePhiTilde hτ, hphi]
  have hex : Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ) +
      Complex.I * ((c * concretePhiTilde K4 ε c τ (L1, α) - π / 4 : ℝ) : ℂ) =
      Complex.I * ((c * (concretePhiTilde K4 ε c τ (L1, α) + (L - L1) * τ) - π / 4 : ℝ) : ℂ) := by
    push_cast; ring
  rw [← mul_assoc, ← Complex.exp_add, hex]

/-! ### 2. `edgeW`-bounds for `outerChiOut`, `phiKill / uctM`, and `concreteEdgeAmp` -/

private lemma iteratedDeriv_const_mul_comp (k : ℕ) (f : ℝ → ℝ) (a : ℝ) :
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

private lemma outerChiOut_edge_bounds_pub (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ {c : ℝ}, 0 < c →
      let τ₁ := c ^ (-(1 / 4 : ℝ))
      ContDiff ℝ ∞ (outerChiOut c) ∧
      (∀ τ : ℝ, |τ| ≤ 1.85 * τ₁ → outerChiOut c τ = 0) ∧
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
  have hcd : ContDiff ℝ ∞ (outerChiOut c) :=
    contDiff_const.sub ((outerChiIn_cutoff.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp
      (contDiff_id.div_const τ₁))
  refine ⟨hcd, fun τ hτ => ?_, fun k _ τ hτ => ?_⟩
  · unfold outerChiOut
    have hdiv : |τ / τ₁| ≤ 1.85 := by
      rw [abs_div, abs_of_pos hτ₁, div_le_iff₀ hτ₁]; exact hτ
    rw [outerChiIn_cutoff.one _ hdiv, sub_self]
  · have hτ0 : τ ≠ 0 := hτ.ne'
    have hwk_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos hτ0).le _
    rcases lt_or_ge (1.98 * τ₁) τ with hlt_outer | hle_outer
    · have hev : outerChiOut c =ᶠ[𝓝 τ] (1 : ℝ → ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hlt_outer] with s hs
        dsimp only [outerChiOut]
        have hs0 : 0 < s := lt_trans (by positivity) hs
        have hs_abs : 1.98 ≤ |s / τ₁| := by
          rw [abs_div, abs_of_pos hτ₁, abs_of_pos hs0, le_div_iff₀ hτ₁]
          exact le_of_lt hs
        rw [outerChiIn_cutoff.zero _ hs_abs, sub_zero]; rfl
      rw [hev.iteratedDeriv_eq k]
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · simp only [iteratedDeriv_zero, Pi.one_apply, abs_one, pow_zero, one_mul, Nat.cast_zero,
          neg_zero, zpow_zero, mul_one]
        exact le_max_right _ _
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
        rw [iteratedDeriv_succ', show deriv (1 : ℝ → ℝ) = 0 from funext fun _ => deriv_const _ _,
          iteratedDeriv_const_zero, abs_zero]
        exact mul_nonneg (by positivity) hwk_nn
    · rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · simp only [iteratedDeriv_zero, pow_zero, one_mul, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
        have hmem := outerChiIn_cutoff.mem (τ / τ₁)
        have hbd : |outerChiOut c τ| ≤ 1 := by
          dsimp only [outerChiOut]; rw [abs_le]; constructor <;> linarith only [hmem.1, hmem.2]
        exact hbd.trans (le_max_right _ _)
      · have h_sub_id : outerChiOut c = fun t => 1 - outerChiIn (τ₁⁻¹ * t) := by
          ext t; dsimp only [outerChiOut]; rw [div_eq_mul_inv, mul_comm]
        rw [h_sub_id, iteratedDeriv_const_sub hk_pos]
        change |iteratedDeriv k (fun t => -(outerChiIn (τ₁⁻¹ * t))) τ| ≤ _
        rw [iteratedDeriv_fun_neg, abs_neg,
          iteratedDeriv_const_mul_comp k outerChiIn τ₁⁻¹ τ, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hτ₁.le) k)]
        have hτ₁_inv : τ₁⁻¹ ^ k ≤ 1.98 ^ k * edgeW τ ^ (-(k : ℤ)) := by
          have h1 : τ₁⁻¹ ≤ 1.98 * (edgeW τ)⁻¹ := by
            have hw : edgeW τ ≤ τ := by
              have h := edgeW_le_abs τ; rwa [abs_of_pos hτ] at h
            have hw0 : 0 < edgeW τ := edgeW_pos hτ0
            calc τ₁⁻¹ ≤ 1.98 * τ⁻¹ := by
                  rw [inv_le_iff_one_le_mul₀ hτ₁]
                  calc (1 : ℝ) = τ * τ⁻¹ := (mul_inv_cancel₀ hτ.ne').symm
                    _ ≤ (1.98 * τ₁) * τ⁻¹ := mul_le_mul_of_nonneg_right hle_outer (inv_nonneg.mpr hτ.le)
                    _ = 1.98 * τ⁻¹ * τ₁ := by ring
              _ ≤ 1.98 * (edgeW τ)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hw0 hw) (by positivity)
          calc (τ₁⁻¹) ^ k ≤ (1.98 * (edgeW τ)⁻¹) ^ k :=
                pow_le_pow_left₀ (inv_nonneg.mpr hτ₁.le) h1 k
            _ = 1.98 ^ k * edgeW τ ^ (-(k : ℤ)) := by
                rw [mul_pow, inv_pow, zpow_neg, zpow_natCast]
        calc (τ₁⁻¹) ^ k * |iteratedDeriv k outerChiIn (τ₁⁻¹ * τ)|
            ≤ (1.98 ^ k * edgeW τ ^ (-(k : ℤ))) * max (M k) 1 :=
              mul_le_mul hτ₁_inv ((hM k _).trans (le_max_left _ _)) (abs_nonneg _) (by positivity)
          _ = 1.98 ^ k * max (M k) 1 * edgeW τ ^ (-(k : ℤ)) := by ring

private lemma ofReal_iteratedDeriv_pub {S : Set ℝ} (hS : IsOpen S) {g : ℝ → ℝ}
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

private lemma ofReal_edge_bounds_pub {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {g : ℝ → ℝ} {w : ℝ → ℝ} {C : ℕ → ℝ}
    (hg : ContDiffOn ℝ ∞ g S)
    (hbd : ∀ k ≤ n, ∀ τ ∈ S, |iteratedDeriv k g τ| ≤ C k * w τ * edgeW τ ^ (-(k : ℤ))) :
    ∀ k ≤ n, ∀ τ ∈ S, ‖iteratedDeriv k (fun s => ((g s : ℝ) : ℂ)) τ‖ ≤ C k * w τ * edgeW τ ^ (-(k : ℤ)) := by
  intro k hk τ hτ
  rw [ofReal_iteratedDeriv_pub hS hg k τ hτ, Complex.norm_real, Real.norm_eq_abs]
  exact hbd k hk τ hτ

private noncomputable def expDerivCoeffOut (Cf : ℕ → ℝ) (k : ℕ) : ℝ :=
  match k with
  | 0 => 1
  | m + 1 => (range (m + 1)).attach.sum fun p =>
      (Nat.choose m p.1 : ℝ) * expDerivCoeffOut Cf p.1 * Cf (m + 1 - p.1)
termination_by k
decreasing_by
  have hj := p.2
  simp only [Finset.mem_range] at hj
  omega

private lemma expDerivCoeffOut_zero (Cf : ℕ → ℝ) : expDerivCoeffOut Cf 0 = 1 := by
  rw [expDerivCoeffOut]

private lemma expDerivCoeffOut_succ (Cf : ℕ → ℝ) (m : ℕ) :
    expDerivCoeffOut Cf (m + 1) =
      ∑ j ∈ range (m + 1), (Nat.choose m j : ℝ) * expDerivCoeffOut Cf j * Cf (m + 1 - j) := by
  conv_lhs => rw [expDerivCoeffOut]
  exact Finset.sum_attach (range (m + 1)) fun j => (Nat.choose m j : ℝ) * expDerivCoeffOut Cf j * Cf (m + 1 - j)

private lemma expDerivCoeffOut_nonneg {Cf : ℕ → ℝ} (hCf : ∀ k, 0 ≤ Cf k) (m : ℕ) :
    0 ≤ expDerivCoeffOut Cf m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    cases m with
    | zero => simp [expDerivCoeffOut_zero]
    | succ k =>
      rw [expDerivCoeffOut_succ]
      exact Finset.sum_nonneg fun j hj =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (ih j (Nat.lt_succ_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))))) (hCf _)

private lemma cexp_iteratedDeriv_unif {S : Set ℝ} (hS : IsOpen S) (hS0 : ∀ τ ∈ S, τ ≠ 0)
    {n : ℕ} {f : ℝ → ℂ} {B : ℝ} {Cf : ℕ → ℝ}
    (hf_cd : ContDiffOn ℝ (n : ℕ) f S) (hB : 0 ≤ B)
    (hCf : ∀ k, 0 ≤ Cf k)
    (hexp : ∀ τ ∈ S, ‖Complex.exp (f τ)‖ ≤ B)
    (hf_bd : ∀ k, 1 ≤ k → k ≤ n → ∀ τ ∈ S, ‖iteratedDeriv k f τ‖ ≤ Cf k * edgeW τ ^ (-(k : ℤ))) :
    ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t => Complex.exp (f t)) τ‖ ≤ expDerivCoeffOut Cf k * B * edgeW τ ^ (-(k : ℤ)) := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro τ hτ
    have hτ0 : τ ≠ 0 := hS0 τ hτ
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
      rw [expDerivCoeffOut_zero, one_mul]
      exact hexp τ hτ
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm_le : m ≤ n := by omega
      have hf_exp_cd : ContDiffOn ℝ (n : ℕ) (fun t => Complex.exp (f t)) S := hf_cd.cexp
      have hev_deriv : EqOn (deriv (fun t => Complex.exp (f t)))
          (fun t => Complex.exp (f t) * deriv f t) S := fun t ht => by
        have hdf : HasDerivAt f (deriv f t) t :=
          ((hf_cd.differentiableOn (by exact_mod_cast (show n ≠ 0 by omega))).differentiableAt
            (hS.mem_nhds ht)).hasDerivAt
        exact hdf.cexp.deriv
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
      have hsum : expDerivCoeffOut Cf (m + 1) * B * edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) =
          ∑ j ∈ range (m + 1), ((Nat.choose m j : ℝ) * expDerivCoeffOut Cf j * Cf (m + 1 - j)) *
            B * edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by
        rw [expDerivCoeffOut_succ, Finset.sum_mul, Finset.sum_mul]
      rw [hsum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj_le : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hj_lt : j < m + 1 := Nat.lt_succ_of_le hj_le
      have hj_n : j ≤ n := hj_le.trans hm_le
      have h1 := ih j hj_lt hj_n τ hτ
      have h2 : ‖iteratedDeriv (m - j) (deriv f) τ‖ ≤ Cf (m + 1 - j) * edgeW τ ^ (-((m + 1 - j : ℕ) : ℤ)) := by
        rw [← iteratedDeriv_succ' (f := f)]
        have hidx : m - j + 1 = m + 1 - j := by omega
        rw [hidx]
        exact hf_bd (m + 1 - j) (by omega) (by omega) τ hτ
      have hw_mul : edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((m + 1 - j : ℕ) : ℤ)) =
          edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ (edgeW_pos hτ0).ne']
        congr 1; omega
      change ‖((Nat.choose m j : ℝ) : ℂ) * iteratedDeriv j (fun t => Complex.exp (f t)) τ *
          iteratedDeriv (m - j) (deriv f) τ‖ ≤ _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
      have hDj0 : 0 ≤ expDerivCoeffOut Cf j := expDerivCoeffOut_nonneg hCf j
      have hCj0 : 0 ≤ Cf (m + 1 - j) := hCf _
      have hwj0 : 0 ≤ edgeW τ ^ (-(j : ℤ)) := zpow_nonneg (edgeW_pos hτ0).le _
      calc (m.choose j : ℝ) * ‖iteratedDeriv j (fun t => Complex.exp (f t)) τ‖ *
              ‖iteratedDeriv (m - j) (deriv f) τ‖
          ≤ (m.choose j : ℝ) * (expDerivCoeffOut Cf j * B * edgeW τ ^ (-(j : ℤ))) *
              (Cf (m + 1 - j) * edgeW τ ^ (-((m + 1 - j : ℕ) : ℤ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hDj0 hB) hwj0))
        _ = (m.choose j : ℝ) * expDerivCoeffOut Cf j * Cf (m + 1 - j) * B *
              (edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((m + 1 - j : ℕ) : ℤ))) := by ring
        _ = (m.choose j : ℝ) * expDerivCoeffOut Cf j * Cf (m + 1 - j) * B *
              edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by rw [hw_mul]

private lemma phiKill_over_m_edge_bounds (n : ℕ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ {c L1 : ℝ}, 1 ≤ c → |L1| ≤ c ^ (-(1 / 2 : ℝ)) →
      let S := {τ : ℝ | 1.85 * c ^ (-(1 / 4 : ℝ)) < τ}
      ContDiffOn ℝ (n : ℕ) (fun t : ℝ => (1 : ℂ) -
        (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) / (uctM t : ℂ)) (Ioi 0) ∧
      ∀ k ≤ n, ∀ τ ∈ S,
        ‖iteratedDeriv k (fun t : ℝ => (1 : ℂ) -
          (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) / (uctM t : ℂ)) τ‖ ≤
          C k * edgeW τ ^ (-(k : ℤ)) := by
  obtain ⟨Cpk, hCpk0, hCpk⟩ := FctSym.phiKill_tsymbol
  obtain ⟨Km, hmInv⟩ := FctSym.mInv_symW_all
  obtain ⟨Um, _, hIUm, hm_cd⟩ := hmInv.smooth
  let Cφ : ℕ → ℝ := fun k => 2 * Cpk k
  let KmC : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (k.choose j : ℝ) * Cφ j * Km (k - j)
  refine ⟨fun k => KmC k + 1, fun k => by
    have : 0 ≤ KmC k := Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two (hCpk0 j))) (hmInv.K_nonneg _)
    linarith, fun {c L1} hc1 hL1 => ?_⟩
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hτ₁ : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hpk_cd : ContDiff ℝ ∞ (fun t : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)) :=
    FctSym.contDiff_phiKill_imag ha0
  have hmInv_cd : ContDiffOn ℝ ∞ (fun t : ℝ => (uctM t)⁻¹) (Ioi 0) := hm_cd.mono hIUm
  have hmInvC_cd : ContDiffOn ℝ ∞ (fun t : ℝ => (((uctM t)⁻¹ : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hmInv_cd
  have h_fac_eq : (fun t : ℝ => (1 : ℂ) -
      (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) / (uctM t : ℂ)) =
      fun t : ℝ => (1 : ℂ) - ((L1 : ℂ) *
        (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) * (((uctM t)⁻¹ : ℝ) : ℂ))) := by
    ext t; rw [div_eq_mul_inv, Complex.ofReal_inv]; ring
  have hcd : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => (1 : ℂ) -
      (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) / (uctM t : ℂ)) (Ioi 0) := by
    rw [h_fac_eq]
    exact (contDiffOn_const.sub (contDiffOn_const.mul (hpk_cd.contDiffOn.mul hmInvC_cd))).of_le
      (by exact_mod_cast le_top)
  refine ⟨hcd, fun k hk τ (hτ : 1.85 * c ^ (-(1 / 4 : ℝ)) < τ) => ?_⟩
  have hτ_pos : 0 < τ := lt_trans (by positivity) hτ
  have hS : IsOpen {t : ℝ | 1.85 * c ^ (-(1 / 4 : ℝ)) < t} := isOpen_Ioi
  have hS0 : ∀ t ∈ {t : ℝ | 1.85 * c ^ (-(1 / 4 : ℝ)) < t}, t ≠ 0 := fun t ht =>
    (lt_trans (by positivity) ht).ne'
  have hpk_bd : ∀ j ≤ n, ∀ t ∈ {t : ℝ | 1.85 * c ^ (-(1 / 4 : ℝ)) < t},
      ‖iteratedDeriv j (fun s : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((s : ℂ) * Complex.I)) t‖ ≤
        Cφ j * 1 * edgeW t ^ (-(j : ℤ)) := by
    intro j _ t ht
    have ht0 : 0 < t := lt_trans (by positivity) ht
    have hre := (hCpk (c ^ (-(1 / 12 : ℝ))) t ha0 ht0 Complex.reCLM (fun z => Complex.abs_re_le_norm z) j).1
    have him := (hCpk (c ^ (-(1 / 12 : ℝ))) t ha0 ht0 Complex.imCLM (fun z => Complex.abs_im_le_norm z) j).1
    rw [FctSym.iteratedDeriv_clm_comp isOpen_univ hpk_cd.contDiffOn Complex.reCLM j t (mem_univ _)] at hre
    rw [FctSym.iteratedDeriv_clm_comp isOpen_univ hpk_cd.contDiffOn Complex.imCLM j t (mem_univ _)] at him
    have hmin : min (1 : ℝ) ((t / c ^ (-(1 / 12 : ℝ))) ^ 8) ≤ 1 := min_le_left _ _
    have ht_inv : (t ^ j)⁻¹ ≤ edgeW t ^ (-(j : ℤ)) := by
      have h1 := abs_inv_le_edgeW_inv ht0.ne' j; rwa [zpow_neg, zpow_natCast, abs_of_pos ht0] at h1
    have h_part : ∀ x : ℝ, t ^ j * x ≤ Cpk j * min 1 ((t / c ^ (-(1 / 12 : ℝ))) ^ 8) →
        x ≤ Cpk j * edgeW t ^ (-(j : ℤ)) := fun x hx => by
      have h1 : t ^ j * x ≤ Cpk j := hx.trans (by simpa using mul_le_mul_of_nonneg_left hmin (hCpk0 j))
      calc x ≤ Cpk j * (t ^ j)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos ht0 j), mul_comm]; exact h1
        _ ≤ Cpk j * edgeW t ^ (-(j : ℤ)) := mul_le_mul_of_nonneg_left ht_inv (hCpk0 j)
    have hre1 := h_part _ (by rwa [abs_mul, abs_of_pos (pow_pos ht0 j)] at hre)
    have him1 := h_part _ (by rwa [abs_mul, abs_of_pos (pow_pos ht0 j)] at him)
    rw [mul_one]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre1 him1
    calc ‖iteratedDeriv j (fun s : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((s : ℂ) * Complex.I)) t‖
        ≤ |(iteratedDeriv j (fun s : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((s : ℂ) * Complex.I)) t).re| +
          |(iteratedDeriv j (fun s : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((s : ℂ) * Complex.I)) t).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ Cφ j * edgeW t ^ (-(j : ℤ)) := by dsimp only [Cφ]; linarith only [hre1, him1]
  have hmInv_bd : ∀ j ≤ n, ∀ t ∈ {t : ℝ | 1.85 * c ^ (-(1 / 4 : ℝ)) < t},
      ‖iteratedDeriv j (fun s : ℝ => (((uctM s)⁻¹ : ℝ) : ℂ)) t‖ ≤ Km j * c ^ (1 / 2 : ℝ) * edgeW t ^ (-(j : ℤ)) := by
    refine ofReal_edge_bounds_pub hS (hmInv_cd.mono fun _ ht => lt_trans (by positivity) ht) fun j _ t ht => ?_
    have ht0 : 0 < t := lt_trans (by positivity) ht
    have hb := hmInv.bound j t ht0
    have hwA : FctSym.wA t ≤ c ^ (1 / 2 : ℝ) := by
      unfold FctSym.wA
      refine max_le (Real.one_le_rpow hc1 (by norm_num)) ?_
      have ht_ge : c ^ (-(1 / 4 : ℝ)) < t := by
        have hc14 : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
        have hht : 1.85 * c ^ (-(1 / 4 : ℝ)) < t := ht
        linarith only [hc14, hht]
      have hr1 : t ^ (-2 : ℝ) ≤ (c ^ (-(1 / 4 : ℝ))) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hτ₁ ht_ge.le (by norm_num)
      have hr2 : (c ^ (-(1 / 4 : ℝ))) ^ (-2 : ℝ) = c ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul hc0.le]; norm_num
      rw [← Real.rpow_natCast t 2, ← Real.rpow_neg ht0.le]
      exact hr1.trans_eq hr2
    have ht_inv : (t ^ j)⁻¹ ≤ edgeW t ^ (-(j : ℤ)) := by
      have h1 := abs_inv_le_edgeW_inv ht0.ne' j; rwa [zpow_neg, zpow_natCast, abs_of_pos ht0] at h1
    calc |iteratedDeriv j (fun s : ℝ => (uctM s)⁻¹) t| ≤ Km j * FctSym.wA t * (t ^ j)⁻¹ := hb
      _ ≤ Km j * c ^ (1 / 2 : ℝ) * edgeW t ^ (-(j : ℤ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hwA (hmInv.K_nonneg j)) ht_inv
            (inv_nonneg.mpr (pow_nonneg ht0.le j)) (mul_nonneg (hmInv.K_nonneg j) (by positivity))
  have hprod := iteratedDeriv_mul_edgeW hS hS0 (hpk_cd.contDiffOn.of_le (by exact_mod_cast le_top))
    ((hmInvC_cd.mono fun _ ht => lt_trans (by positivity) ht).of_le (by exact_mod_cast le_top))
    (fun _ _ => zero_le_one) (fun _ _ => Real.rpow_nonneg hc0.le _)
    (fun j _ => mul_nonneg zero_le_two (hCpk0 j)) (fun j _ => hmInv.K_nonneg j) hpk_bd hmInv_bd k hk τ hτ
  rw [one_mul] at hprod
  have hL_cancel : |L1| * c ^ (1 / 2 : ℝ) ≤ 1 := by
    calc |L1| * c ^ (1 / 2 : ℝ) ≤ c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hL1 (Real.rpow_nonneg hc0.le _)
      _ = 1 := by rw [← Real.rpow_add hc0]; norm_num
  have hwk_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos hτ_pos.ne').le _
  have hKmC_nn : 0 ≤ KmC k := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two (hCpk0 j))) (hmInv.K_nonneg _)
  have hsub_bd : ‖iteratedDeriv k (fun t : ℝ => (1 : ℂ) - ((L1 : ℂ) *
      (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) * (((uctM t)⁻¹ : ℝ) : ℂ)))) τ‖ ≤
      (KmC k + 1) * edgeW τ ^ (-(k : ℤ)) := by
    have hcd_pk_m : ContDiffAt ℝ k (fun t : ℝ => (L1 : ℂ) *
        (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) * (((uctM t)⁻¹ : ℝ) : ℂ))) τ :=
      ((contDiffOn_const.mul (hpk_cd.contDiffOn.mul hmInvC_cd)).contDiffAt
        (isOpen_Ioi.mem_nhds hτ_pos)).of_le (by exact_mod_cast le_top)
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hprod ⊢
      have h1 : ‖(1 : ℂ) - (L1 : ℂ) * (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
          (((uctM τ)⁻¹ : ℝ) : ℂ))‖ ≤ 1 + ‖(L1 : ℂ)‖ *
            ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) * (((uctM τ)⁻¹ : ℝ) : ℂ)‖ := by
        calc _ ≤ ‖(1 : ℂ)‖ + ‖(L1 : ℂ) * _‖ := norm_sub_le _ _
          _ = 1 + ‖(L1 : ℂ)‖ * _ := by rw [norm_one, norm_mul]
      refine h1.trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc 1 + |L1| * ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
              (((uctM τ)⁻¹ : ℝ) : ℂ)‖
          ≤ 1 + |L1| * (KmC 0 * c ^ (1 / 2 : ℝ)) := by gcongr
        _ = 1 + KmC 0 * (|L1| * c ^ (1 / 2 : ℝ)) := by ring
        _ ≤ 1 + KmC 0 * 1 := by gcongr
        _ = KmC 0 + 1 := by ring
    · rw [iteratedDeriv_const_sub hk_pos]
      change ‖iteratedDeriv k (fun t : ℝ => -((L1 : ℂ) *
          (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) * (((uctM t)⁻¹ : ℝ) : ℂ)))) τ‖ ≤ _
      rw [iteratedDeriv_fun_neg, iteratedDeriv_const_mul_field,
        norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |L1| * ‖iteratedDeriv k (fun t : ℝ =>
              FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) * (((uctM t)⁻¹ : ℝ) : ℂ)) τ‖
          ≤ |L1| * (KmC k * c ^ (1 / 2 : ℝ) * edgeW τ ^ (-(k : ℤ))) :=
            mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
        _ = (|L1| * c ^ (1 / 2 : ℝ)) * KmC k * edgeW τ ^ (-(k : ℤ)) := by ring
        _ ≤ 1 * KmC k * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL_cancel hKmC_nn) hwk_nn
        _ = KmC k * edgeW τ ^ (-(k : ℤ)) := by ring
        _ ≤ (KmC k + 1) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hwk_nn
  simpa only [← h_fac_eq] using hsub_bd

private lemma concreteEdgeAmp_edge_bounds (n : ℕ) :
    ∃ (A0 A1 : ℝ), 0 ≤ A0 ∧ 0 ≤ A1 ∧
      ∀ {K4 c L1 α : ℝ}, 1 ≤ K4 → 1 ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
        |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 →
        |L1| ≤ c ^ (-(1 / 2 : ℝ)) →
        ContDiffOn ℝ (n : ℕ) (concreteEdgeAmp K4 c L1 α) (Ioi 0) ∧
        ContDiffOn ℝ (n : ℕ) (fun t : ℝ => (t : ℂ) * concreteEdgeAmp K4 c L1 α t) (Ioi 0) ∧
        (∀ k ≤ n, ∀ τ : ℝ, 1.85 * c ^ (-(1 / 4 : ℝ)) < τ →
          ‖iteratedDeriv k (concreteEdgeAmp K4 c L1 α) τ‖ ≤
            A0 * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) ∧
        (∀ k ≤ n, ∀ τ : ℝ, 1.85 * c ^ (-(1 / 4 : ℝ)) < τ →
          ‖iteratedDeriv k (fun t : ℝ => (t : ℂ) * concreteEdgeAmp K4 c L1 α t) τ‖ ≤
            A1 * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) := by
  let Cb : ℕ → ℝ := fun _ => (n.factorial : ℝ) / 12
  have hCb0 : ∀ k, 0 ≤ Cb k := fun k => by positivity
  obtain ⟨Bv, _, Cv, _, _, _, hBv0, _, hCv0, _, _, _, hvth⟩ := vTotal_thetaD_edge_bounds n
  obtain ⟨Cfac, hCfac0, hfac⟩ := phiKill_over_m_edge_bounds n
  obtain ⟨Cw0, hCw0_0, hw0⟩ := warpAmpScal_edge_bounds n
  obtain ⟨Cw1, hCw1_0, hw1⟩ := tau_mul_warpAmpScal_edge_bounds n
  let Cf : ℕ → ℝ := fun k => Cb k + Cv k
  have hCf0 : ∀ k, 0 ≤ Cf k := fun k => add_nonneg (hCb0 k) (hCv0 k)
  let Bexp : ℝ := Real.exp (1 / 6 + Bv)
  have hBexp0 : 0 ≤ Bexp := (Real.exp_pos _).le
  let Dexp : ℕ → ℝ := expDerivCoeffOut Cf
  have hDexp0 : ∀ k, 0 ≤ Dexp k := expDerivCoeffOut_nonneg hCf0
  let Cef : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (Dexp j * Bexp) * Cfac (k - j)
  have hCef0 : ∀ k, 0 ≤ Cef k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hDexp0 j) hBexp0)) (hCfac0 _)
  let Kamp0 : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (k.choose j : ℝ) * Cef j * Cw0
  let Kamp1 : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), (k.choose j : ℝ) * Cef j * Cw1
  have hKamp0_0 : ∀ k, 0 ≤ Kamp0 k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCef0 j)) hCw0_0
  have hKamp1_0 : ∀ k, 0 ≤ Kamp1 k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCef0 j)) hCw1_0
  let A0 : ℝ := ∑ k ∈ range (n + 1), Kamp0 k
  let A1 : ℝ := ∑ k ∈ range (n + 1), Kamp1 k
  refine ⟨A0, A1, Finset.sum_nonneg fun k _ => hKamp0_0 k, Finset.sum_nonneg fun k _ => hKamp1_0 k, ?_⟩
  intro K4 c L1 α hK4 hc1 hτD hK4τ hα hL1
  have hc0 : 0 < c := by linarith
  obtain ⟨hbin_cd, hbin0, hbink⟩ := binetImag_edge_bounds n hc1
  obtain ⟨hv_cd, _, _, _, hvth_pt⟩ := hvth hK4 hc1 hτD hK4τ hα
  obtain ⟨hfac_cd, hfac_bd⟩ := hfac hc1 hL1
  let S := {τ : ℝ | 1.85 * c ^ (-(1 / 4 : ℝ)) < τ}
  have hS : IsOpen S := isOpen_Ioi
  have hS0 : ∀ τ ∈ S, τ ≠ 0 := fun τ (hτ : 1.85 * c ^ (-(1 / 4 : ℝ)) < τ) =>
    (lt_trans (by positivity) hτ).ne'
  let f : ℝ → ℂ := fun t => FormalResearch.Asymptotics.binetDiff c (Complex.I * (t : ℂ)) +
    ((vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) t : ℝ) : ℂ)
  let fexp : ℝ → ℂ := fun t => Complex.exp (f t)
  have hf_cd : ContDiff ℝ ∞ f :=
    (hbin_cd.of_le le_top).add (Complex.ofRealCLM.contDiff.comp hv_cd)
  have hexp_pt : ∀ τ ∈ S, ‖Complex.exp (f τ)‖ ≤ Bexp := fun τ hτ => by
    rw [Complex.norm_exp, Complex.add_re, Complex.ofReal_re]
    apply Real.exp_le_exp.mpr
    have hre_bd : (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))).re ≤ 1 / 6 :=
      (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (hbin0 τ))
    have hv_bd : vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) τ ≤ Bv := by
      have hp := (hvth_pt τ hτ).1
      have hva : |vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) τ| ≤ Bv := by
        linarith only [hp, abs_nonneg (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) τ)]
      exact (le_abs_self _).trans hva
    linarith only [hre_bd, hv_bd]
  have hf_bd : ∀ k, 1 ≤ k → k ≤ n → ∀ τ ∈ S, ‖iteratedDeriv k f τ‖ ≤ Cf k * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk1 hkn τ hτ
    have hτ0 : τ ≠ 0 := hS0 τ hτ
    have hb_cd : ContDiffAt ℝ k (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c (Complex.I * (t : ℂ))) τ :=
      (hbin_cd.of_le (by exact_mod_cast le_top)).contDiffAt
    have hv_cd_at : ContDiffAt ℝ k (fun t => ((vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) t : ℝ) : ℂ)) τ :=
      ((Complex.ofRealCLM.contDiff.comp hv_cd).of_le (by exact_mod_cast le_top)).contDiffAt
    change ‖iteratedDeriv k ((fun t : ℝ => FormalResearch.Asymptotics.binetDiff c (Complex.I * (t : ℂ))) +
      fun t : ℝ => ((vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) t : ℝ) : ℂ)) τ‖ ≤ _
    rw [iteratedDeriv_add hb_cd hv_cd_at]
    have h1 := hbink k hk1 hkn τ hτ0
    have h2 : ‖iteratedDeriv k (fun t => ((vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) t : ℝ) : ℂ)) τ‖ ≤
        Cv k * edgeW τ ^ (-(k : ℤ)) := by
      rw [ofReal_iteratedDeriv_pub isOpen_univ hv_cd.contDiffOn k τ (mem_univ _),
        Complex.norm_real, Real.norm_eq_abs]
      exact ((hvth_pt τ hτ).2.2.1 k (by omega)).1
    exact (norm_add_le _ _).trans (by
      calc _ ≤ Cb k * edgeW τ ^ (-(k : ℤ)) + Cv k * edgeW τ ^ (-(k : ℤ)) := add_le_add h1 h2
        _ = Cf k * edgeW τ ^ (-(k : ℤ)) := by ring)
  have hfexp_bd := cexp_iteratedDeriv_unif hS hS0 (hf_cd.contDiffOn.of_le (by exact_mod_cast le_top))
    hBexp0 hCf0 hexp_pt hf_bd
  have hfexp_cd : ContDiffOn ℝ (n : ℕ) fexp (Ioi 0) :=
    (hf_cd.cexp.contDiffOn).of_le (by exact_mod_cast le_top)
  let ef : ℝ → ℂ := fun t => fexp t * ((1 : ℂ) -
    (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I) / (uctM t : ℂ))
  have hef_cd : ContDiffOn ℝ (n : ℕ) ef (Ioi 0) := hfexp_cd.mul hfac_cd
  have hef_bd : ∀ k ≤ n, ∀ τ ∈ S, ‖iteratedDeriv k ef τ‖ ≤ Cef k * 1 * edgeW τ ^ (-(k : ℤ)) := by
    intro k hk τ hτ
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (hfexp_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hfac_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) (fun j _ => mul_nonneg (hDexp0 j) hBexp0)
      (fun k _ => hCfac0 k)
      (fun j hj t ht => by simpa only [mul_assoc, mul_one, Dexp] using hfexp_bd j hj t ht)
      (fun j hj t ht => by rw [mul_one]; exact hfac_bd j hj t ht) k hk τ hτ
    rw [one_mul, mul_one] at hmul
    simpa only [ef, Cef, mul_one] using hmul
  have hw0C_cd : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => (warpAmpScal t : ℂ)) (Ioi 0) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_warpAmpScal).of_le (by exact_mod_cast le_top)
  have hw1C_cd : ContDiffOn ℝ (n : ℕ) (fun t : ℝ => ((t * warpAmpScal t : ℝ) : ℂ)) (Ioi 0) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_id.contDiffOn.mul contDiffOn_warpAmpScal)).of_le
      (by exact_mod_cast le_top)
  have hw0_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t : ℝ => (warpAmpScal t : ℂ)) τ‖ ≤
        Cw0 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
    refine ofReal_edge_bounds_pub hS (contDiffOn_warpAmpScal.mono fun _ ht => lt_trans (by positivity) ht)
      fun k hk τ hτ => ?_
    calc |iteratedDeriv k warpAmpScal τ| ≤ Cw0 * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) :=
          hw0 k hk τ (lt_trans (by positivity) hτ)
      _ = Cw0 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by ring
  have hw1_bd : ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t : ℝ => ((t * warpAmpScal t : ℝ) : ℂ)) τ‖ ≤
        Cw1 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
    refine ofReal_edge_bounds_pub hS
      ((contDiff_id.contDiffOn.mul contDiffOn_warpAmpScal).mono fun _ ht => lt_trans (by positivity) ht)
      fun k hk τ hτ => ?_
    calc |iteratedDeriv k (fun t => t * warpAmpScal t) τ|
        ≤ Cw1 * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) :=
          hw1 k hk τ (lt_trans (by positivity) hτ)
      _ = Cw1 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by ring
  have hamp_eq : concreteEdgeAmp K4 c L1 α = fun t : ℝ => ef t * (warpAmpScal t : ℂ) := by
    ext t
    rw [concreteEdgeAmp_eq_base_mul]
    have hbase : concreteEdgeAmpBase K4 c α t = fexp t * (warpAmpScal t : ℂ) := by
      unfold concreteEdgeAmpBase warpAmpScal; dsimp only [fexp, f]
    rw [hbase]; dsimp only [ef]; ring
  have htau_amp_eq : (fun t : ℝ => (t : ℂ) * concreteEdgeAmp K4 c L1 α t) =
      fun t : ℝ => ef t * ((t * warpAmpScal t : ℝ) : ℂ) := by
    ext t; rw [hamp_eq, Complex.ofReal_mul]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hamp_eq]; exact hef_cd.mul hw0C_cd
  · rw [htau_amp_eq]; exact hef_cd.mul hw1C_cd
  · intro k hk τ hτ
    have hτ_pos : 0 < τ := lt_trans (by positivity) hτ
    rw [hamp_eq]
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (hef_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hw0C_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun _ _ => zero_le_one)
      (fun (t : ℝ) (ht : t ∈ S) => by
        have ht0 : 0 < t := lt_trans (by positivity) ht
        exact mul_nonneg (Real.rpow_nonneg ht0.le _) (zpow_nonneg (by linarith only [ht0]) _))
      (fun k _ => hCef0 k) (fun _ _ => hCw0_0) hef_bd hw0_bd k hk τ hτ
    rw [one_mul] at hmul
    have hK_le : Kamp0 k ≤ A0 := Finset.single_le_sum (fun j _ => hKamp0_0 j) (Finset.mem_range.mpr (by omega))
    have htw_nn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) :=
      mul_nonneg (Real.rpow_nonneg hτ_pos.le _) (zpow_nonneg (by linarith only [hτ_pos]) _)
    have hwk_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos (hS0 τ hτ)).le _
    calc ‖iteratedDeriv k (fun t => ef t * (warpAmpScal t : ℂ)) τ‖
        ≤ Kamp0 k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := hmul
      _ ≤ A0 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le htw_nn) hwk_nn
      _ = A0 * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring
  · intro k hk τ hτ
    have hτ_pos : 0 < τ := lt_trans (by positivity) hτ
    rw [htau_amp_eq]
    have hmul := iteratedDeriv_mul_edgeW hS hS0 (hef_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (hw1C_cd.mono fun _ ht => lt_trans (by positivity) ht)
      (fun _ _ => zero_le_one)
      (fun (t : ℝ) (ht : t ∈ S) => by
        have ht0 : 0 < t := lt_trans (by positivity) ht
        exact mul_nonneg (Real.rpow_nonneg ht0.le _) (zpow_nonneg (by linarith only [ht0]) _))
      (fun k _ => hCef0 k) (fun _ _ => hCw1_0) hef_bd hw1_bd k hk τ hτ
    rw [one_mul] at hmul
    have hK_le : Kamp1 k ≤ A1 := Finset.single_le_sum (fun j _ => hKamp1_0 j) (Finset.mem_range.mpr (by omega))
    have htw_nn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) :=
      mul_nonneg (Real.rpow_nonneg hτ_pos.le _) (zpow_nonneg (by linarith only [hτ_pos]) _)
    have hwk_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos (hS0 τ hτ)).le _
    calc ‖iteratedDeriv k (fun t => ef t * ((t * warpAmpScal t : ℝ) : ℂ)) τ‖
        ≤ Kamp1 k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := hmul
      _ ≤ A1 * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le htw_nn) hwk_nn
      _ = A1 * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring

/-! ### 3. Shoulder IBP wrapper, bounds on `warpSqOut` / `warpSqOutDeriv`, and MVT -/

private lemma shoulder_ibp_of_edge_amp :
    ∃ (C_ibp c₀ : ℝ), 0 ≤ C_ibp ∧ 16 ≤ c₀ ∧
      ∀ {K4 ε c L α A : ℝ} {amp : ℝ → ℂ},
        1 ≤ K4 → (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
        concreteEll1 ε c L < 2.55 →
        |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 →
        0 ≤ A →
        ContDiffOn ℝ (15 : ℕ) amp (Ioi 0) →
        (∀ k ≤ 15, ∀ τ : ℝ, 1.85 * c ^ (-(1 / 4 : ℝ)) < τ →
          ‖iteratedDeriv k amp τ‖ ≤ A * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) →
        IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * amp τ *
          Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ))) (Ioi 0) ∧
        ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * amp τ *
          Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ))‖ ≤
          C_ibp * A * c ^ (-(31 / 8 : ℝ)) := by
  let n : ℕ := 15
  obtain ⟨κ_ph, c_ph, K_ph, hκph0, hcph1, hKph0, hph⟩ := outerPhi_shoulder_bounds n (by norm_num)
  obtain ⟨Cχ, hCχ0, hχ_eb⟩ := outerChiOut_edge_bounds_pub n
  obtain ⟨C_ibp0, hCibp0_nn, hibp⟩ := fct_edge_ibp_shoulder (n := n) (by norm_num) hκph0 hKph0
  let Bχ : ℝ := (2 : ℝ) ^ n * ∑ j ∈ range (n + 1), Cχ j
  have hBχ0 : 0 ≤ Bχ := mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hCχ0 j)
  let C_tot : ℝ := C_ibp0 * Bχ * (1.85 : ℝ) ^ (1 / 2 - (n : ℝ))
  refine ⟨C_tot, max 16 c_ph, by positivity, le_max_left _ _, ?_⟩
  intro K4 ε c L α A amp hK4 hε hc hτD hK4τ hell hα hA0 hamp_cd hamp_bd
  have hc16 : 16 ≤ c := (le_max_left _ _).trans hc
  have hcph : c_ph ≤ c := (le_max_right _ _).trans hc
  have hc1 : 1 ≤ c := by linarith only [hc16]
  have hc0 : 0 < c := by linarith only [hc1]
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  set r := 1.85 * τ₁
  set u := c ^ (-(1 / 2 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hu : 0 < u := Real.rpow_pos_of_pos hc0 _
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    have hτ₁_le : τ₁ ≤ (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = ((16 : ℝ) ^ (-(1 / 4 : ℝ))) by
        rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hc16 (by norm_num)
    dsimp only [r]; linarith only [hτ₁_le]
  obtain ⟨hΦ_cd, hΦ'_lb, hΦ_bd⟩ := hph hK4 hε hcph hτD hK4τ hell hα
  obtain ⟨hχ_cd, hχ_zero, hχ_bd⟩ := hχ_eb hc0
  let a : ℝ → ℂ := fun τ => if 0 < τ then ((outerChiOut c τ : ℝ) : ℂ) * amp τ else 0
  have ha_zero : ∀ τ : ℝ, |τ| < r → a τ = 0 := fun τ hτ => by
    by_cases hpos : 0 < τ
    · dsimp only [a]; rw [ite_eq_left_iff.mpr fun h => absurd hpos h, hχ_zero τ hτ.le, Complex.ofReal_zero, zero_mul]
    · dsimp only [a]; exact ite_eq_right_iff.mpr fun h => absurd h hpos
  have ha_prod_cd : ContDiffOn ℝ (n : ℕ) (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * amp τ) (Ioi 0) :=
    ((Complex.ofRealCLM.contDiff.comp (hχ_cd.of_le (WithTop.coe_le_coe.mpr le_top))).contDiffOn.of_le
      (by exact_mod_cast le_top)).mul hamp_cd
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
      have hev : a =ᶠ[𝓝 τ] fun s => ((outerChiOut c s : ℝ) : ℂ) * amp s := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
        dsimp only [a]; exact ite_eq_left_iff.mpr fun h => absurd hs h
      exact (ha_prod_cd.contDiffAt (isOpen_Ioi.mem_nhds hpos)).congr_of_eventuallyEq hev
  have ha_bd : ∀ k ≤ n, ∀ τ : ℝ, r < |τ| →
      ‖iteratedDeriv k a τ‖ ≤ (Bχ * A) * edgeW τ ^ (-(k : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := by
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
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hBχ0 hA0) hwk_nn) hrp_nn) h1t_nn
    · rw [abs_of_pos hpos] at hτ ⊢
      have hS : IsOpen (Ioi r) := isOpen_Ioi
      have hS0 : ∀ t ∈ Ioi r, t ≠ 0 := fun t ht => (lt_trans hr ht).ne'
      have hev_a : a =ᶠ[𝓝 τ] fun s => ((outerChiOut c s : ℝ) : ℂ) * amp s := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
        dsimp only [a]; exact ite_eq_left_iff.mpr fun h => absurd hs h
      rw [hev_a.iteratedDeriv_eq k]
      have hχC_cd : ContDiffOn ℝ (n : ℕ) (fun s : ℝ => ((outerChiOut c s : ℝ) : ℂ)) (Ioi r) :=
        ((Complex.ofRealCLM.contDiff.comp (hχ_cd.of_le (WithTop.coe_le_coe.mpr le_top))).contDiffOn.of_le
          (by exact_mod_cast le_top)).mono fun _ ht => mem_univ _
      have hχC_bd : ∀ j ≤ n, ∀ t ∈ Ioi r,
          ‖iteratedDeriv j (fun s : ℝ => ((outerChiOut c s : ℝ) : ℂ)) t‖ ≤ Cχ j * 1 * edgeW t ^ (-(j : ℤ)) := by
        intro j hj t ht
        have ht0 : 0 < t := lt_trans hr ht
        rw [ofReal_iteratedDeriv_pub hS ((hχ_cd.contDiffOn).mono fun _ _ => mem_univ _) j t ht,
          Complex.norm_real, Real.norm_eq_abs, mul_one]
        exact hχ_bd j hj t ht0
      have hmul := iteratedDeriv_mul_edgeW (wg := fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ))
        hS hS0 hχC_cd (hamp_cd.mono fun _ ht => lt_trans hr ht)
        (fun _ _ => zero_le_one)
        (fun t ht => by
          have ht0 : 0 < t := lt_trans hr ht
          exact mul_nonneg (Real.rpow_nonneg ht0.le _) (zpow_nonneg (by linarith only [ht0]) _))
        (fun k _ => hCχ0 k) (fun _ _ => hA0) hχC_bd
        (fun j hj t ht => by
          calc ‖iteratedDeriv j amp t‖ ≤ A * edgeW t ^ (-(j : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ) :=
                hamp_bd j hj t ht
            _ = A * (t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) * edgeW t ^ (-(j : ℤ)) := by ring)
        k hk τ hτ
      rw [one_mul] at hmul
      let K_k : ℝ := ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * Cχ j * A
      have hK_le : K_k ≤ Bχ * A := by
        dsimp only [K_k, Bχ]
        have hch : ∀ j ∈ range (k + 1), (Nat.choose k j : ℝ) ≤ (2 : ℝ) ^ n := fun j _ => by
          have : (Nat.choose k j : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast Nat.choose_le_two_pow k j
          exact this.trans (pow_le_pow_right₀ (by norm_num) hk)
        calc ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * Cχ j * A
            ≤ ∑ j ∈ range (k + 1), (2 : ℝ) ^ n * Cχ j * A :=
              Finset.sum_le_sum fun j hj =>
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hch j hj) (hCχ0 j)) hA0
          _ ≤ ∑ j ∈ range (n + 1), (2 : ℝ) ^ n * Cχ j * A :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hk))
                fun j _ _ => mul_nonneg (mul_nonneg (by positivity) (hCχ0 j)) hA0
          _ = (2 : ℝ) ^ n * (∑ j ∈ range (n + 1), Cχ j) * A := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
      calc ‖iteratedDeriv k (fun s => ((outerChiOut c s : ℝ) : ℂ) * amp s) τ‖
          ≤ K_k * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := hmul
        _ ≤ (Bχ * A) * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hK_le
                (mul_nonneg (Real.rpow_nonneg hpos.le _) (zpow_nonneg (by linarith only [hpos]) _)))
              hwk_nn
        _ = (Bχ * A) * edgeW τ ^ (-(k : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by ring
  obtain ⟨hibp_int, hibp_bd⟩ := hibp hc0 hu hr hr1 (mul_nonneg hBχ0 hA0) ha_cd ha_zero ha_bd
    hΦ_cd hΦ'_lb hΦ_bd
  have hphase_eq : ∀ τ : ℝ, 0 < τ →
      ((outerChiOut c τ : ℝ) : ℂ) * amp τ * Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((-(π / 4) : ℝ) : ℂ)) *
          (a τ * Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ : ℝ) : ℂ))) := fun τ hτ => by
    dsimp only [a]
    rw [ite_eq_left_iff.mpr fun h => absurd hτ h]
    have hex : Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ) =
        Complex.I * ((-(π / 4) : ℝ) : ℂ) + Complex.I * ((c * outerPhi K4 ε c L α τ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hex, Complex.exp_add]; ring
  have hsub_int : IntegrableOn (fun τ : ℝ => Complex.exp (Complex.I * ((-(π / 4) : ℝ) : ℂ)) *
      (a τ * Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ : ℝ) : ℂ)))) (Ioi 0) :=
    (hibp_int.integrableOn).const_mul _
  refine ⟨hsub_int.congr_fun (fun τ hτ => (hphase_eq τ hτ).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hphase_eq, integral_const_mul, norm_mul]
  have hrot1 : ‖Complex.exp (Complex.I * ((-(π / 4) : ℝ) : ℂ))‖ = 1 := by
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (-(π / 4))
  have hzero_Iic : ∫ τ in Iic (0 : ℝ), a τ * Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ : ℝ) : ℂ)) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => ?_
    have hnot : ¬ (0 < τ) := not_lt.mpr hτ
    dsimp only [a]; rw [ite_eq_right_iff.mpr fun h => absurd h hnot, zero_mul]
  have hsplit := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hibp_int
  rw [hzero_Iic, zero_add, show (Iic (0 : ℝ))ᶜ = Set.Ioi (0 : ℝ) by ext τ; simp] at hsplit
  have hrpow : ((c * u) ^ n)⁻¹ * r ^ (1 / 2 - (n : ℝ)) =
      (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)) := by
    have hcu : c * u = c ^ (1 / 2 : ℝ) := by
      dsimp only [u]
      conv_lhs => arg 1; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc0]; norm_num
    have h1 : ((c * u) ^ n)⁻¹ = c ^ (-((n : ℝ) / 2)) := by
      rw [hcu, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_neg hc0.le]; congr 1; ring
    have h2 : r ^ (1 / 2 - (n : ℝ)) = (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(1 / 4 : ℝ) * (1 / 2 - (n : ℝ))) := by
      dsimp only [r]
      rw [Real.mul_rpow (by norm_num) hτ₁.le]
      congr 1; exact (Real.rpow_mul hc0.le _ _).symm
    rw [h1, h2]
    calc c ^ (-((n : ℝ) / 2)) * ((1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(1 / 4 : ℝ) * (1 / 2 - (n : ℝ))))
        = (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * (c ^ (-((n : ℝ) / 2)) * c ^ (-(1 / 4 : ℝ) * (1 / 2 - (n : ℝ)))) := by ring
      _ = (1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ)) := by
          congr 1; rw [← Real.rpow_add hc0]; congr 1; dsimp only [n]; norm_num
  rw [hrot1, one_mul, hsplit]
  calc ‖∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ : ℝ) : ℂ))‖
      ≤ C_ibp0 * (Bχ * A) * ((c * u) ^ n)⁻¹ * r ^ (1 / 2 - (n : ℝ)) := hibp_bd
    _ = C_ibp0 * (Bχ * A) * (((c * u) ^ n)⁻¹ * r ^ (1 / 2 - (n : ℝ))) := by ring
    _ = C_ibp0 * (Bχ * A) * ((1.85 : ℝ) ^ (1 / 2 - (n : ℝ)) * c ^ (-(31 / 8 : ℝ))) := by rw [hrpow]
    _ = C_tot * A * c ^ (-(31 / 8 : ℝ)) := by dsimp only [C_tot]; ring

/-- Shoulder IBP bounds on `warpSqOutComplex` and `warpSqOutDerivComplex`. -/
lemma warpSqOutComplex_bounds :
    ∃ (C_out c₀ : ℝ), 0 ≤ C_out ∧ 16 ≤ c₀ ∧
      ∀ {K4 ε c L1 α L : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
        |L1| ≤ c ^ (-(1 / 2 : ℝ)) →
        |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 →
        concreteEll1 ε c L < 2.55 →
        IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
          (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) (Ioi 0) ∧
        IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
          (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
            fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) (Ioi 0) ∧
        ‖warpSqOutComplex K4 ε c L1 α L‖ ≤ C_out * c ^ (-(31 / 8 : ℝ)) ∧
        ‖warpSqOutDerivComplex K4 ε c L1 α L‖ ≤ C_out * c ^ (-(23 / 8 : ℝ)) := by
  obtain ⟨A0, A1, hA0, hA1, hamp⟩ := concreteEdgeAmp_edge_bounds 15
  obtain ⟨C_ibp, c_sh, hCibp0, hc_sh16, hibp⟩ := shoulder_ibp_of_edge_amp
  let C_out : ℝ := C_ibp * max A0 A1
  refine ⟨C_out, c_sh, mul_nonneg hCibp0 (le_trans hA0 (le_max_left _ _)), hc_sh16, ?_⟩
  intro K4 ε c L1 α L hK4 hε hc hτD hK4τ hL1 hα hell
  have hc1 : 1 ≤ c := by linarith only [hc_sh16, hc]
  have hc0 : 0 < c := by linarith only [hc1]
  obtain ⟨hamp0_cd, hamp1_cd, hamp0_bd, hamp1_bd⟩ := hamp hK4 hc1 hτD hK4τ hα hL1
  have h1 := hibp hK4 hε hc hτD hK4τ hell hα hA0 hamp0_cd hamp0_bd
  have h2 := hibp hK4 hε hc hτD hK4τ hell hα hA1 hamp1_cd hamp1_bd
  have h_eq0 : EqOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)))
      (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * concreteEdgeAmp K4 c L1 α τ *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ))) (Ioi 0) := fun τ hτ => by
    dsimp only; rw [mellin_fctWarpA_eq_edge hε hc0 hτ]; ring
  have h_eq1 : EqOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
      (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
        fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)))
      (fun τ : ℝ => (Complex.I * (c : ℂ)) * (((outerChiOut c τ : ℝ) : ℂ) * ((τ : ℂ) * concreteEdgeAmp K4 c L1 α τ) *
        Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ)))) (Ioi 0) := fun τ hτ => by
    dsimp only
    rw [mul_assoc (Complex.I * ((c * τ : ℝ) : ℂ)) (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L)),
      mellin_fctWarpA_eq_edge hε hc0 hτ]
    push_cast; ring
  have hint0 := h1.1.congr_fun (fun τ hτ => (h_eq0 hτ).symm) measurableSet_Ioi
  have hint1 : IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
      (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
        fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) (Ioi 0) :=
    IntegrableOn.congr_fun (h2.1.const_mul (Complex.I * (c : ℂ))) (fun τ hτ => (h_eq1 hτ).symm) measurableSet_Ioi
  refine ⟨hint0, hint1, ?_, ?_⟩
  · unfold warpSqOutComplex
    rw [setIntegral_congr_fun measurableSet_Ioi h_eq0]
    refine h1.2.trans ?_
    have hc318 : 0 ≤ c ^ (-(31 / 8 : ℝ)) := Real.rpow_nonneg hc0.le _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left A0 A1) hCibp0) hc318
  · unfold warpSqOutDerivComplex
    rw [setIntegral_congr_fun measurableSet_Ioi h_eq1, integral_const_mul, norm_mul, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    calc c * ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * ((τ : ℂ) * concreteEdgeAmp K4 c L1 α τ) *
            Complex.exp (Complex.I * ((c * outerPhi K4 ε c L α τ - π / 4 : ℝ) : ℂ))‖
        ≤ c * (C_ibp * A1 * c ^ (-(31 / 8 : ℝ))) := mul_le_mul_of_nonneg_left h2.2 hc0.le
      _ ≤ c * (C_ibp * max A0 A1 * c ^ (-(31 / 8 : ℝ))) := by
          gcongr; exact le_max_right _ _
      _ = C_out * (c * c ^ (-(31 / 8 : ℝ))) := by dsimp only [C_out]; ring
      _ = C_out * c ^ (-(23 / 8 : ℝ)) := by
          congr 1; conv_lhs => arg 1; rw [← Real.rpow_one c]
          rw [← Real.rpow_add hc0]; norm_num

private lemma hasDerivAt_warpSqOut {K4 ε c L1 α L : ℝ}
    (_hK4 : 1 ≤ K4) (_hε : ε = 1 ∨ ε = -1) (_hc1 : 1 ≤ c)
    (_hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hint0_L : ∀ x : ℝ, IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) (Ioi 0))
    (hint1_L : IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
      (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) *
        fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) (Ioi 0)) :
    HasDerivAt (warpSqOut K4 ε c L1 α) (warpSqOutDeriv K4 ε c L1 α L) L := by
  let F : ℝ → ℝ → ℂ := fun x τ => ((outerChiOut c τ : ℝ) : ℂ) *
    (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))
  let F' : ℝ → ℝ → ℂ := fun x τ => ((outerChiOut c τ : ℝ) : ℂ) *
    (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) *
      fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))
  have hm_norm_eq : ∀ x τ : ℝ, ‖F' x τ‖ = ‖F' L τ‖ := fun x τ => by
    dsimp only [F']
    rw [mellinK0_fctXi1_shift (L1 := L)]
    have hex1 : ‖Complex.exp (Complex.I * ((c * (x - L) * τ : ℝ) : ℂ))‖ = 1 := by
      simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (c * (x - L) * τ)
    have hrew : ((outerChiOut c τ : ℝ) : ℂ) * (Complex.I * ((c * τ : ℝ) : ℂ) *
        (Complex.exp (Complex.I * ((c * (x - L) * τ : ℝ) : ℂ)) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L)) *
        fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * ((c * (x - L) * τ : ℝ) : ℂ)) * F' L τ := by
      dsimp only [F']; ring
    rw [hrew, norm_mul, hex1, one_mul]
  have hF_meas : ∀ x : ℝ, AEStronglyMeasurable (F x) (volume.restrict (Ioi 0)) := fun x =>
    (hint0_L x).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' L) (volume.restrict (Ioi 0)) :=
    hint1_L.aestronglyMeasurable
  have hdC : HasDerivAt (warpSqOutComplex K4 ε c L1 α) (warpSqOutDerivComplex K4 ε c L1 α L) L := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := F) (F' := F') (x₀ := L) (s := univ) (bound := fun τ => ‖F' L τ‖) univ_mem
      (Eventually.of_forall hF_meas) (hint0_L L) hF'_meas ?_ hint1_L.norm ?_).2
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ _ x _ => ?_
      rw [hm_norm_eq]
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ _ x _ => ?_
      have hξ : ∀ y : ℝ, 0 < fctXi1 y := fun y => by unfold fctXi1; positivity
      have hlog : ∀ y : ℝ, Real.log (π ^ 2 * fctXi1 y) = y := fun y => by
        unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
      set Km : ℂ := (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
        Complex.exp (Complex.I * (c : ℂ) * ((-π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ))
      have hm_eq : ∀ y : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 y) =
          Km * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ)) := fun y => by
        rw [FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 y) τ (hξ y), hlog y]
        dsimp only [Km]
        have hex : Complex.I * (c : ℂ) * ((y * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) =
            Complex.I * (c : ℂ) * ((-π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) +
              Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ) := by push_cast; ring
        rw [hex, Complex.exp_add]; ring
      have hdm : HasDerivAt (fun y : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 y))
          (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x)) x := by
        rw [show (fun y : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 y)) =
            fun y : ℝ => Km * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ)) from funext hm_eq]
        have he1 : HasDerivAt (fun y : ℝ => Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ))
            (Complex.I * ((c * τ : ℝ) : ℂ)) x := by
          simpa using ((Complex.ofRealCLM.hasDerivAt).const_mul (Complex.I * ((c * τ : ℝ) : ℂ)))
        have he2 := (he1.cexp.const_mul Km)
        convert he2 using 1; rw [hm_eq x]; ring
      have htot := (hdm.mul_const (fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))).const_mul ((outerChiOut c τ : ℝ) : ℂ)
      convert htot using 1
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt L hdC).const_mul (c ^ (1 / 3 : ℝ) / π)

/-- Uniform bounds and MVT difference bound for `warpSqOut` on `[L1, L]` when `concreteEll1 ε c L < 2.55`.
Class: proved (`fct:warp-win` outer shoulder tail). -/
theorem warpSqOut_mvt_bound :
    ∃ (C c₀ : ℝ), 0 ≤ C ∧ 16 ≤ c₀ ∧
      ∀ {K4 ε c L1 α L : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
        |L1| ≤ c ^ (-(1 / 2 : ℝ)) →
        |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 →
        L1 ≤ L →
        concreteEll1 ε c L < 2.55 →
        |warpSqOut K4 ε c L1 α L| ≤ C * c ^ (-(85 / 24 : ℝ)) ∧
        |warpSqOutDeriv K4 ε c L1 α L| ≤ C * c ^ (-(61 / 24 : ℝ)) ∧
        |warpSqOut K4 ε c L1 α L - warpSqOut K4 ε c L1 α L1| ≤
          C * c ^ (-(61 / 24 : ℝ)) * (L - L1) := by
  obtain ⟨C_out, c_sh, hCout0, hc16, hsh⟩ := warpSqOutComplex_bounds
  refine ⟨C_out / π, c_sh, by positivity, hc16, ?_⟩
  intro K4 ε c L1 α L hK4 hε hc hτD hK4τ hL1 hα hL1_le_L hell
  have hc1 : 1 ≤ c := by linarith only [hc16, hc]
  have hc0 : 0 < c := by linarith only [hc1]
  have hsh_L := hsh hK4 hε hc hτD hK4τ hL1 hα hell
  have hpref0 : 0 ≤ c ^ (1 / 3 : ℝ) / π := by positivity
  have hc13_318 : c ^ (1 / 3 : ℝ) * c ^ (-(31 / 8 : ℝ)) = c ^ (-(85 / 24 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hc13_238 : c ^ (1 / 3 : ℝ) * c ^ (-(23 / 8 : ℝ)) = c ^ (-(61 / 24 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hw0 : |warpSqOut K4 ε c L1 α L| ≤ C_out / π * c ^ (-(85 / 24 : ℝ)) := by
    unfold warpSqOut
    rw [abs_mul, abs_of_nonneg hpref0]
    calc (c ^ (1 / 3 : ℝ) / π) * |(warpSqOutComplex K4 ε c L1 α L).re|
        ≤ (c ^ (1 / 3 : ℝ) / π) * (C_out * c ^ (-(31 / 8 : ℝ))) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hsh_L.2.2.1) hpref0
      _ = C_out / π * (c ^ (1 / 3 : ℝ) * c ^ (-(31 / 8 : ℝ))) := by ring
      _ = C_out / π * c ^ (-(85 / 24 : ℝ)) := by rw [hc13_318]
  have hw1_all : ∀ x : ℝ, concreteEll1 ε c x < 2.55 →
      |warpSqOutDeriv K4 ε c L1 α x| ≤ C_out / π * c ^ (-(61 / 24 : ℝ)) := fun x hx => by
    have hsh_x := hsh hK4 hε hc hτD hK4τ hL1 hα hx
    unfold warpSqOutDeriv
    rw [abs_mul, abs_of_nonneg hpref0]
    calc (c ^ (1 / 3 : ℝ) / π) * |(warpSqOutDerivComplex K4 ε c L1 α x).re|
        ≤ (c ^ (1 / 3 : ℝ) / π) * (C_out * c ^ (-(23 / 8 : ℝ))) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hsh_x.2.2.2) hpref0
      _ = C_out / π * (c ^ (1 / 3 : ℝ) * c ^ (-(23 / 8 : ℝ))) := by ring
      _ = C_out / π * c ^ (-(61 / 24 : ℝ)) := by rw [hc13_238]
  have hint0_all : ∀ x : ℝ, IntegrableOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) (Ioi 0) := by
    intro x
    have hm_eq : EqOn (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)))
        (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) * concreteEdgeAmp K4 c L1 α τ *
          Complex.exp (Complex.I * ((c * outerPhi K4 ε c x α τ - π / 4 : ℝ) : ℂ))) (Ioi 0) := fun τ hτ => by
      dsimp only; rw [mellin_fctWarpA_eq_edge hε hc0 hτ]; ring
    have h_shift : ∀ τ : ℝ, ((outerChiOut c τ : ℝ) : ℂ) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * ((c * (x - L) * τ : ℝ) : ℂ)) * (((outerChiOut c τ : ℝ) : ℂ) *
          (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) := fun τ => by
      rw [mellinK0_fctXi1_shift (L1 := L)]; ring
    have h_norm_int : Integrable (fun τ : ℝ => ‖((outerChiOut c τ : ℝ) : ℂ) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))‖)
        (volume.restrict (Ioi 0)) := by
      refine hsh_L.1.norm.congr (ae_of_all _ fun τ => ?_)
      dsimp only
      have hex1 : ‖Complex.exp (Complex.I * ((c * (x - L) * τ : ℝ) : ℂ))‖ = 1 := by
        simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (c * (x - L) * τ)
      have heq_f : ((outerChiOut c τ : ℝ) : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) *
          fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
          Complex.exp (Complex.I * ((c * (x - L) * τ : ℝ) : ℂ)) * (((outerChiOut c τ : ℝ) : ℂ) *
            (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) := by
        rw [mellinK0_fctXi1_shift (L1 := L)]; ring
      rw [heq_f, norm_mul (Complex.exp _) _, hex1, one_mul]
    have hmeas : AEStronglyMeasurable (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)))
        (volume.restrict (Ioi 0)) := by
      have hmul : (fun τ : ℝ => ((outerChiOut c τ : ℝ) : ℂ) *
          (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) =
          fun τ => Complex.exp (Complex.I * ((c * (x - L) * τ : ℝ) : ℂ)) * (((outerChiOut c τ : ℝ) : ℂ) *
            (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))) :=
        funext h_shift
      rw [hmul]
      refine AEStronglyMeasurable.mul ?_ hsh_L.1.aestronglyMeasurable
      exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    exact h_norm_int.mono' hmeas (ae_of_all _ fun τ => le_of_eq rfl)
  have hmvt : |warpSqOut K4 ε c L1 α L - warpSqOut K4 ε c L1 α L1| ≤
      C_out / π * c ^ (-(61 / 24 : ℝ)) * (L - L1) := by
    have h_deriv : ∀ x ∈ Icc L1 L, HasDerivWithinAt (warpSqOut K4 ε c L1 α)
        (warpSqOutDeriv K4 ε c L1 α x) (Icc L1 L) x := fun x hx => by
      have hxL : concreteEll1 ε c x < 2.55 := by
        have : concreteEll1 ε c x ≤ concreteEll1 ε c L := by
          unfold concreteEll1
          exact div_le_div_of_nonneg_right (sub_le_sub_right hx.2 _) (by positivity)
        linarith only [this, hell]
      have hx_sh := hsh hK4 hε hc hτD hK4τ hL1 hα hxL
      exact (hasDerivAt_warpSqOut hK4 hε hc1 hτD hint0_all hx_sh.2.1).hasDerivWithinAt
    have h_bd : ∀ x ∈ Icc L1 L, ‖warpSqOutDeriv K4 ε c L1 α x‖ ≤ C_out / π * c ^ (-(61 / 24 : ℝ)) := fun x hx => by
      have hxL : concreteEll1 ε c x < 2.55 := by
        have : concreteEll1 ε c x ≤ concreteEll1 ε c L := by
          unfold concreteEll1
          exact div_le_div_of_nonneg_right (sub_le_sub_right hx.2 _) (by positivity)
        linarith only [this, hell]
      rw [Real.norm_eq_abs]; exact hw1_all x hxL
    have hmv := (convex_Icc L1 L).norm_image_sub_le_of_norm_hasDerivWithin_le h_deriv h_bd
      (left_mem_Icc.mpr hL1_le_L) (right_mem_Icc.mpr hL1_le_L)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hL1_le_L)] at hmv
  exact ⟨hw0, hw1_all L hell, hmvt⟩

/-! ### 4. Airy-window geometry of the zero pair `(L₁, α)` -/

/-- For `h : FctWarpSolveStmt K4` (`1 ≤ K4`) and any `Sw ≥ 1`, for `c` sufficiently large and
`L ∈ [fctWarpL1 h ε c, Sw * c^{-2/3}]`, the zero pair satisfies positive `c^{-2/3}` lower/upper
bounds and `concreteEll1 ε c L, concreteEll1 ε c (fctWarpL1 h ε c) ∈ Ioo 0 2.55`.
Class: proved (`fct:warp-win` domain geometry). -/
lemma fctWarpZero_window_geom {K4 : ℝ} (_hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4)
    {Sw : ℝ} (_hSw : 1 ≤ Sw) :
    ∃ (c0_L c₀ : ℝ), 0 < c0_L ∧ 32 ^ 4 ≤ c₀ ∧
      ∀ {ε c L : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        fctWarpL1 h ε c ≤ L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
        c0_L * c ^ (-(2 / 3 : ℝ)) ≤ fctWarpL1 h ε c ∧
        |fctWarpL1 h ε c| ≤ c ^ (-(1 / 2 : ℝ)) ∧
        |fctWarpAlpha h ε c| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ∧
        concreteEll1 ε c L ∈ Ioo (0 : ℝ) 2.55 ∧
        concreteEll1 ε c (fctWarpL1 h ε c) ∈ Ioo (0 : ℝ) 2.55 ∧
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 ∧
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose := by
  obtain ⟨Cz, cz, hzw⟩ := fctWarpZero_of_solve h
  obtain ⟨KL, cL, hcL1, hL_ub⟩ := FctSym.physL1_le (fctWarpT1 h) ⟨Cz, cz, fun ε c hε hc => (hzw ε c hε hc).1⟩
  have hc0_z : 0 ≤ Cz := by
    have h1 := (abs_nonneg _).trans (hzw 1 (max cz 1) (Or.inl rfl) (le_max_left _ _)).1
    exact nonneg_of_mul_nonneg_left h1 (inv_pos.mpr (by linarith [le_max_right cz 1]))
  set c0_L : ℝ := π ^ 2 * airyOrderCoeff / 4
  have hc0L_pos : 0 < c0_L := by
    have := airyOrderCoeff_pos; positivity
  let Kk : ℝ := |ctKappa 1| + |ctKappa (-1)|
  let Kd : ℝ := |ctD2star 1| + |ctD2star (-1)|
  let K_rem : ℝ := π ^ 2 * (|Cz| + Kk + |ctC1Langer| + Kd)
  have hKrem0 : 0 ≤ K_rem := by positivity
  let Mθ : ℝ := max (|ctTheta1 1|) (|ctTheta1 (-1)|)
  have hMθ0 : 0 ≤ Mθ := by positivity
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (32 : ℝ) ^ 4 ≤ c ∧ cz ≤ c ∧ cL ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 ∧
      K_rem * c ^ (-(1 / 3 : ℝ)) ≤ π ^ 2 * airyOrderCoeff / 2 ∧
      π ^ 2 * airyOrderCoeff * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 2 ∧
      Mθ * c⁻¹ < c0_L * c ^ (-(2 / 3 : ℝ)) ∧
      KL * c ^ (-(1 / 6 : ℝ)) ≤ 1 ∧
      |Cz| * c ^ (-(1 / 6 : ℝ)) ≤ 1 ∧
      Sw * c ^ (-(1 / 6 : ℝ)) + Mθ * c ^ (-(1 / 2 : ℝ)) < 2.55 := by
    refine Eventually.and (eventually_ge_atTop (32 ^ 4))
      (Eventually.and (eventually_ge_atTop cz)
        (Eventually.and (eventually_ge_atTop cL)
          (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_
            (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ ?_)))))))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1)
    · have ht : Tendsto (fun c : ℝ => K4 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K4
      filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually (Iic_mem_nhds zero_lt_one)] with c hc1 hcK
      have hc0 : 0 < c := by linarith
      rwa [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le,
        show (-(1 / 4 : ℝ) * (2 : ℕ)) = -(1 / 2 : ℝ) by norm_num]
    · have ht : Tendsto (fun c : ℝ => K_rem * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul K_rem
      have hAi := airyOrderCoeff_pos
      exact ht.eventually (Iic_mem_nhds (by positivity))
    · have ht : Tendsto (fun c : ℝ => π ^ 2 * airyOrderCoeff * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _
      exact ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    · have ht : Tendsto (fun c : ℝ => Mθ * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul Mθ
      filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually (Iio_mem_nhds hc0L_pos)] with c hc1 hlt
      have hc0 : 0 < c := by linarith
      have hmul := mul_lt_mul_of_pos_right hlt (Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ)))
      have hc13_23 : c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c⁻¹ := by
        rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
      rwa [mul_assoc, hc13_23] at hmul
    · have ht : Tendsto (fun c : ℝ => KL * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul KL
      exact ht.eventually (Iic_mem_nhds zero_lt_one)
    · have ht : Tendsto (fun c : ℝ => |Cz| * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul |Cz|
      exact ht.eventually (Iic_mem_nhds zero_lt_one)
    · have h1 : Tendsto (fun c : ℝ => Sw * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul Sw
      have h2 : Tendsto (fun c : ℝ => Mθ * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul Mθ
      have ht : Tendsto (fun c : ℝ => Sw * c ^ (-(1 / 6 : ℝ)) + Mθ * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [add_zero] using h1.add h2
      exact ht.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨c0_L, max (32 ^ 4) c₀, hc0L_pos, le_max_left _ _, ?_⟩
  intro ε c L hε hc hL1_L hL_Sw
  obtain ⟨hc32, hcz, hcL, hτD, hK4τ, hKrem_bd, hAi_le1, hMθ_lt, hKL_le, hCz_le, h255_lt⟩ :=
    hc₀ c ((le_max_right _ _).trans hc)
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc32
  have hc0 : 0 < c := by linarith
  have hzw_c := hzw ε c hε hcz
  set L1 := fctWarpL1 h ε c
  have hL1_eq : L1 = FctSym.physL1 (fctWarpT1 h) ε c := (physL1_fctWarpT1 h hc0).symm
  have hL1_ub := hL_ub ε c hε hcL
  rw [← hL1_eq] at hL1_ub
  have hL1_lo : c0_L * c ^ (-(2 / 3 : ℝ)) ≤ L1 := by
    have hmul : ∀ r : ℝ, c⁻¹ * c ^ r = c ^ (r - 1) := fun r => by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; ring_nf
    have e1 : c⁻¹ * c ^ (1 / 3 : ℝ) = c ^ (-(2 / 3 : ℝ)) := by
      rw [hmul]; norm_num
    have hinv : c⁻¹ ≤ c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have e2 : c⁻¹ * c ^ (-(1 / 3 : ℝ)) ≤ c⁻¹ := by
      rw [hmul, ← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have e3 : c⁻¹ * c ^ (-(2 / 3 : ℝ)) ≤ c⁻¹ := by
      rw [hmul, ← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hk : |ctKappa ε| ≤ Kk := by
      rcases hε with rfl | rfl <;> simp [Kk]
    have hd : |ctD2star ε| ≤ Kd := by
      rcases hε with rfl | rfl <;> simp [Kd]
    have hy : π ^ 2 * fctWarpT1 h ε c / c - 1 = π ^ 2 * airyOrderCoeff * c ^ (-(2 / 3 : ℝ)) +
        (π ^ 2 * c⁻¹ * (fctWarpT1 h ε c - ctDelta5 ε c) +
          π ^ 2 * (ctKappa ε * c⁻¹ + ctC1Langer * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) +
            ctD2star ε * (c⁻¹ * c ^ (-(2 / 3 : ℝ))))) := by
      unfold ctDelta5; rw [← e1]; field_simp; ring
    have hrem : |π ^ 2 * c⁻¹ * (fctWarpT1 h ε c - ctDelta5 ε c) +
        π ^ 2 * (ctKappa ε * c⁻¹ + ctC1Langer * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) +
          ctD2star ε * (c⁻¹ * c ^ (-(2 / 3 : ℝ))))| ≤ K_rem * c⁻¹ := by
      have ht1 : |π ^ 2 * c⁻¹ * (fctWarpT1 h ε c - ctDelta5 ε c)| ≤ π ^ 2 * |Cz| * c⁻¹ := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        calc π ^ 2 * c⁻¹ * |fctWarpT1 h ε c - ctDelta5 ε c| ≤ π ^ 2 * c⁻¹ * (Cz * c⁻¹) :=
              mul_le_mul_of_nonneg_left hzw_c.1 (by positivity)
          _ ≤ π ^ 2 * c⁻¹ * (|Cz| * 1) := by gcongr; exact le_abs_self _; exact inv_le_one_of_one_le₀ hc1
          _ = π ^ 2 * |Cz| * c⁻¹ := by ring
      have ht2 : |π ^ 2 * (ctKappa ε * c⁻¹ + ctC1Langer * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) +
          ctD2star ε * (c⁻¹ * c ^ (-(2 / 3 : ℝ))))| ≤ π ^ 2 * (Kk + |ctC1Langer| + Kd) * c⁻¹ := by
        have hpi0 : 0 ≤ π ^ 2 := by positivity
        rw [abs_mul, abs_of_nonneg hpi0, mul_assoc (π ^ 2)]
        refine mul_le_mul_of_nonneg_left ?_ hpi0
        have htri : |ctKappa ε * c⁻¹ + ctC1Langer * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) + ctD2star ε * (c⁻¹ * c ^ (-(2 / 3 : ℝ)))| ≤
            |ctKappa ε * c⁻¹| + |ctC1Langer * (c⁻¹ * c ^ (-(1 / 3 : ℝ)))| + |ctD2star ε * (c⁻¹ * c ^ (-(2 / 3 : ℝ)))| := by
          have ha := abs_add_le (ctKappa ε * c⁻¹ + ctC1Langer * (c⁻¹ * c ^ (-(1 / 3 : ℝ)))) (ctD2star ε * (c⁻¹ * c ^ (-(2 / 3 : ℝ))))
          have hb := abs_add_le (ctKappa ε * c⁻¹) (ctC1Langer * (c⁻¹ * c ^ (-(1 / 3 : ℝ))))
          linarith only [ha, hb]
        refine htri.trans ?_
        simp only [abs_mul, abs_of_pos (inv_pos.mpr hc0), abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
        calc |ctKappa ε| * c⁻¹ + |ctC1Langer| * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) + |ctD2star ε| * (c⁻¹ * c ^ (-(2 / 3 : ℝ)))
            ≤ Kk * c⁻¹ + |ctC1Langer| * c⁻¹ + Kd * c⁻¹ := by gcongr
          _ = (Kk + |ctC1Langer| + Kd) * c⁻¹ := by ring
      calc _ ≤ |π ^ 2 * c⁻¹ * _| + |π ^ 2 * _| := abs_add_le _ _
        _ ≤ π ^ 2 * |Cz| * c⁻¹ + π ^ 2 * (Kk + |ctC1Langer| + Kd) * c⁻¹ := add_le_add ht1 ht2
        _ = K_rem * c⁻¹ := by dsimp only [K_rem]; ring
    have hc_13_23 : c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c⁻¹ := by
      rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
    have hrem_bd : K_rem * c⁻¹ ≤ π ^ 2 * airyOrderCoeff / 2 * c ^ (-(2 / 3 : ℝ)) := by
      rw [← hc_13_23, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKrem_bd (by positivity)
    set y : ℝ := π ^ 2 * fctWarpT1 h ε c / c - 1
    have hlo_y : π ^ 2 * airyOrderCoeff / 2 * c ^ (-(2 / 3 : ℝ)) ≤ y := by
      have ha := (abs_le.mp hrem).1; linarith only [hy, ha, hrem_bd]
    have h_val : π ^ 2 * fctWarpT1 h ε c / c = 1 + y := by dsimp only [y]; ring
    have h_log : Real.log (1 + y) ≥ y / 2 := by
      have hy0 : 0 ≤ y := by
        have hAi := airyOrderCoeff_pos
        have hcr := Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))
        have : 0 ≤ π ^ 2 * airyOrderCoeff / 2 * c ^ (-(2 / 3 : ℝ)) := by positivity
        linarith only [hlo_y, this]
      have h1y : 0 < 1 + y := by linarith only [hy0]
      have hlog_lb := Real.one_sub_inv_le_log_of_pos h1y
      have h_simp : 1 - (1 + y)⁻¹ = y / (1 + y) := by
        have hne : 1 + y ≠ 0 := h1y.ne'
        field_simp [hne]; ring
      rw [h_simp] at hlog_lb
      have hdiv : y / 2 ≤ y / (1 + y) := by
        rw [div_le_div_iff₀ (by norm_num) h1y]
        have hb := (abs_le.mp hrem).2
        have hy_le1 : y ≤ 1 := by linarith only [hy, hb, hrem_bd, hAi_le1]
        nlinarith only [hy0, hy_le1]
      exact hdiv.trans hlog_lb
    rw [hL1_eq]; unfold FctSym.physL1
    rw [h_val]
    calc (c0_L * c ^ (-(2 / 3 : ℝ))) = (π ^ 2 * airyOrderCoeff / 2 * c ^ (-(2 / 3 : ℝ))) / 2 := by
            dsimp only [c0_L]; ring
      _ ≤ y / 2 := by linarith only [hlo_y]
      _ ≤ Real.log (1 + y) := h_log
  have hL1_c12 : |L1| ≤ c ^ (-(1 / 2 : ℝ)) := by
    have hc23_12 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc |L1| ≤ KL * c ^ (-(2 / 3 : ℝ)) := hL1_ub
      _ = (KL * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [hc23_12]; ring
      _ ≤ 1 * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hKL_le (Real.rpow_nonneg hc0.le _)
      _ = c ^ (-(1 / 2 : ℝ)) := one_mul _
  have hα_bd : |fctWarpAlpha h ε c| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have hτ₁_sq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hc23_12 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    rw [hτ₁_sq]
    calc |fctWarpAlpha h ε c| ≤ Cz * c ^ (-(2 / 3 : ℝ)) := hzw_c.2
      _ ≤ |Cz| * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hc0.le _)
      _ = (|Cz| * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [hc23_12]; ring
      _ ≤ 1 * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hCz_le (Real.rpow_nonneg hc0.le _)
      _ ≤ 2 * c ^ (-(1 / 2 : ℝ)) := by linarith [Real.rpow_nonneg hc0.le (-(1 / 2 : ℝ))]
  have hell_gen : ∀ x : ℝ, L1 ≤ x → x ≤ Sw * c ^ (-(2 / 3 : ℝ)) → concreteEll1 ε c x ∈ Ioo (0 : ℝ) 2.55 := by
    intro x hx1 hx2
    have hτ₁_pos : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    have hτ₁_sq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hθ_le : |ctTheta1 ε| ≤ Mθ := by
      rcases hε with rfl | rfl <;> [exact le_max_left _ _; exact le_max_right _ _]
    have hθ_bd : |ctTheta1 ε / c| ≤ Mθ * c⁻¹ := by
      rw [abs_div, abs_of_pos hc0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hθ_le (inv_nonneg.mpr hc0.le)
    have hx_pos : 0 < x - ctTheta1 ε / c := by
      have h1 : ctTheta1 ε / c ≤ Mθ * c⁻¹ := (le_abs_self _).trans hθ_bd
      linarith only [hL1_lo, hx1, h1, hMθ_lt]
    have hell_lo : 0 < concreteEll1 ε c x := by
      unfold concreteEll1; exact div_pos hx_pos (sq_pos_of_pos hτ₁_pos)
    have hell_hi : concreteEll1 ε c x < 2.55 := by
      unfold concreteEll1; rw [hτ₁_sq, div_lt_iff₀ (Real.rpow_pos_of_pos hc0 _)]
      have h1 : -(ctTheta1 ε / c) ≤ Mθ * c⁻¹ := by
        have := (abs_le.mp hθ_bd).1; linarith only [this]
      have hc23_12 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have hc1_12 : c⁻¹ = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
      calc x - ctTheta1 ε / c ≤ Sw * c ^ (-(2 / 3 : ℝ)) + Mθ * c⁻¹ := by linarith only [hx2, h1]
        _ = (Sw * c ^ (-(1 / 6 : ℝ)) + Mθ * c ^ (-(1 / 2 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by
            rw [hc23_12, hc1_12]; ring
        _ < 2.55 * c ^ (-(1 / 2 : ℝ)) := mul_lt_mul_of_pos_right h255_lt (Real.rpow_pos_of_pos hc0 _)
    exact ⟨hell_lo, hell_hi⟩
  have hL1_Sw : L1 ≤ Sw * c ^ (-(2 / 3 : ℝ)) := hL1_L.trans hL_Sw
  exact ⟨hL1_lo, hL1_c12, hα_bd, hell_gen L hL1_L hL_Sw, hell_gen L1 le_rfl hL1_Sw, hK4τ, hτD⟩

/-- info: 'FormalResearch.SignUncertainty.warpSqOut_mvt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpSqOut_mvt_bound

/-- info: 'FormalResearch.SignUncertainty.fctWarpZero_window_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpZero_window_geom

end FormalResearch.SignUncertainty
