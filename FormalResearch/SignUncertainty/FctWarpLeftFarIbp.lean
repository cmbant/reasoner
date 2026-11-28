/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpLeftMidBand

/-!
# Left-tail oscillatory error: Macro and Far bound (`3 * physDelta c ≤ L`, `fct:warp-asymp`)

Leaf module for `FctPhysicalPositive.lean`:
* `warpLeftTailDensity_far_bound`: uniformly for all `c₀ ≤ c`, `ε = ±1`, and `ξ > 0` with
  `3 * FctSym.physDelta c ≤ Real.log (π² * ξ)`,
  `|warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-2 : ℝ) * (Real.log (π² * ξ)) ^ (-(3 / 2 : ℝ))`.

Proof architecture (parametrized by sign `σ ∈ {1, -1}`):
* Split at `r = (c * L)⁻¹`: the core `Ioc (-r) r` gives `O(c⁻³ L^{-3/2})` directly.
* Case `3 * physDelta c ≤ L ≤ 1`: 4-zone VdC split at `r`, `3/4 * tau0 L`, `3/2 * tau0 L` using
  `van_der_corput_first` (`λ₁ = 1/32 * L`) and `van_der_corput_second` (`λ₂ = 3/40 * √L`).
* Case `1 ≤ L ≤ 2`: same 4-zone VdC split (`λ₁ = 1/32`, `λ₂ = 1/164`).
* Case `2 ≤ L`: split `[r, ∞)` at `s₁ = tau0 (L / 2)`, `s₂ = 3/4 * tau0 L`, `s₃ = 3/2 * tau0 L`;
  use one IBP step (`ibpStep_integral`, `ibpStep_deriv_bound (n := 1)`) plus `van_der_corput_first`
  on `[r, s₁]`, and VdC1/VdC2 with half-exponential decay `e^{-π τ / 2}` on `[s₁, ∞)`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.Analysis FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctCuspEdge

namespace FormalResearch.SignUncertainty

/-! ### Integral splitting, sign helpers, and second-derivative VdC wrapper -/

lemma integral_Ioi_eq_interval_add_Ioi {f : ℝ → ℂ} {r b : ℝ} (hrb : r ≤ b)
    (hf : IntegrableOn f (Ioi r)) :
    ∫ τ in Ioi r, f τ = (∫ τ in r..b, f τ) + ∫ τ in Ioi b, f τ := by
  rw [intervalIntegral.integral_of_le hrb]
  have hdisj : Disjoint (Ioc r b) (Ioi b) := by
    rw [Set.disjoint_iff_forall_ne]
    intro x hx y hy hxy; subst hxy; linarith [(mem_Ioc.mp hx).2, mem_Ioi.mp hy]
  have hunion : Ioc r b ∪ Ioi b = Ioi r := Ioc_union_Ioi_eq_Ioi hrb
  rw [← hunion]
  exact setIntegral_union hdisj measurableSet_Ioi
    (hf.mono_set (hunion ▸ subset_union_left))
    (hf.mono_set (hunion ▸ subset_union_right))

lemma edgePhi_sign_mul {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (L τ : ℝ) :
    edgePhi L (σ * τ) = σ * edgePhi L τ := by
  rcases hσ with rfl | rfl
  · simp
  · simpa using edgePhi_neg L τ

lemma edgePhiDeriv_sign_mul {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (L τ : ℝ) :
    edgePhiDeriv L (σ * τ) = edgePhiDeriv L τ := by
  rcases hσ with rfl | rfl
  · simp
  · simpa using edgePhiDeriv_neg L τ

lemma abs_mul_sign {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (x : ℝ) : |σ * x| = |x| := by
  rw [abs_mul]; rcases hσ with rfl | rfl <;> norm_num

lemma warpAmpLeft_sign_CD {K4 : ℝ} {h : FctWarpSolveStmt K4} {ε c ξ σ : ℝ}
    (hCD : ContDiffOn ℝ 2 (warpAmpLeft h ε c ξ) {τ : ℝ | τ ≠ 0})
    (hσ : σ = 1 ∨ σ = -1) :
    ContDiffOn ℝ 2 (fun τ => warpAmpLeft h ε c ξ (σ * τ)) (Ioi 0) := by
  have hne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  exact hCD.comp (contDiff_const.mul contDiff_id).contDiffOn
    fun x hx => mul_ne_zero hne (mem_Ioi.mp hx).ne'

lemma vdc1_Icc_edgePhi_sign {a b L c lam M_bd V_bd σ : ℝ} (hab : a ≤ b) (ha : 0 < a) (hc : 0 < c)
    (hlam : 0 < lam) (hσ : σ = 1 ∨ σ = -1) {amp : ℝ → ℂ}
    (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hLam : ∀ x ∈ Icc a b, lam ≤ |edgePhiDeriv L x|)
    (hM : ∀ x ∈ Icc a b, ‖amp x‖ ≤ M_bd)
    (hV : ∫ x in Icc a b, ‖deriv amp x‖ ≤ V_bd) :
    ‖∫ τ in a..b, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
      3 * (M_bd + V_bd) / (c * lam) := by
  have hIcc_pos : Icc a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have heq : (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))) =
      fun τ => amp τ * Complex.exp (Complex.I * (c : ℂ) * ((σ * edgePhi L τ : ℝ) : ℂ)) := by
    ext τ; rw [edgePhi_sign_mul hσ L τ]
  rw [heq]
  have hφ : ∀ y ∈ Icc a b, HasDerivAt (fun x => σ * edgePhi L x) (σ * edgePhiDeriv L y) y :=
    fun y _ => (hasDerivAt_edgePhi L y).const_mul σ
  have hφ'_cont : ContinuousOn (fun y => σ * edgePhiDeriv L y) (Icc a b) :=
    (continuous_const.mul (contDiff_edgePhiDeriv L).continuous).continuousOn
  have hφ'_mono : MonotoneOn (fun y => σ * edgePhiDeriv L y) (Icc a b) ∨
      AntitoneOn (fun y => σ * edgePhiDeriv L y) (Icc a b) := by
    rcases hσ with rfl | rfl
    · right
      intro x hx y hy hxy
      simpa using (edgePhiDeriv_antitoneOn_nonneg L) (le_trans ha.le hx.1) (le_trans ha.le hy.1) hxy
    · left
      intro x hx y hy hxy
      simpa using neg_le_neg ((edgePhiDeriv_antitoneOn_nonneg L)
        (le_trans ha.le hx.1) (le_trans ha.le hy.1) hxy)
  have hφ'_lb : ∀ y ∈ Icc a b, lam ≤ |σ * edgePhiDeriv L y| := fun y hy => by
    rw [abs_mul_sign hσ]; exact hLam y hy
  have hamp_cont : ContinuousOn amp (Icc a b) := hCD.continuousOn.mono hIcc_pos
  obtain ⟨hamp_bv, hamp_var⟩ := vdc_variation_on_Icc hab ha hCD hV
  have hvdc := van_der_corput_first hab hc hlam hφ hφ'_cont hφ'_mono hφ'_lb hamp_cont hamp_bv hM
  have hden : 0 < c * lam := mul_pos hc hlam
  exact hvdc.trans (by gcongr)

lemma vdc2_Icc_edgePhi_sign {a b L c lam M_bd V_bd σ : ℝ} (hab : a ≤ b) (ha : 0 < a) (hc : 0 < c)
    (hlam : 0 < lam) (hσ : σ = 1 ∨ σ = -1) {amp : ℝ → ℂ}
    (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hLam2 : ∀ x ∈ Icc a b, lam ≤ |edgePhiDeriv2 x|)
    (hM : ∀ x ∈ Icc a b, ‖amp x‖ ≤ M_bd)
    (hV : ∫ x in Icc a b, ‖deriv amp x‖ ≤ V_bd) :
    ‖∫ τ in a..b, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
      8 * (M_bd + V_bd) / Real.sqrt (c * lam) := by
  have hIcc_pos : Icc a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have heq : (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))) =
      fun τ => amp τ * Complex.exp (Complex.I * (c : ℂ) * ((σ * edgePhi L τ : ℝ) : ℂ)) := by
    ext τ; rw [edgePhi_sign_mul hσ L τ]
  rw [heq]
  have hφ : ∀ y ∈ Icc a b, HasDerivAt (fun x => σ * edgePhi L x) (σ * edgePhiDeriv L y) y :=
    fun y _ => (hasDerivAt_edgePhi L y).const_mul σ
  have hφ' : ∀ y ∈ Icc a b, HasDerivAt (fun x => σ * edgePhiDeriv L x) (σ * edgePhiDeriv2 y) y :=
    fun y _ => (hasDerivAt_edgePhiDeriv L y).const_mul σ
  have hφ'_mono : MonotoneOn (fun y => σ * edgePhiDeriv L y) (Icc a b) ∨
      AntitoneOn (fun y => σ * edgePhiDeriv L y) (Icc a b) := by
    rcases hσ with rfl | rfl
    · right
      intro x hx y hy hxy
      simpa using (edgePhiDeriv_antitoneOn_nonneg L) (le_trans ha.le hx.1) (le_trans ha.le hy.1) hxy
    · left
      intro x hx y hy hxy
      simpa using neg_le_neg ((edgePhiDeriv_antitoneOn_nonneg L)
        (le_trans ha.le hx.1) (le_trans ha.le hy.1) hxy)
  have hφ''_lb : ∀ y ∈ Icc a b, lam ≤ |σ * edgePhiDeriv2 y| := fun y hy => by
    rw [abs_mul_sign hσ]; exact hLam2 y hy
  have hamp_cont : ContinuousOn amp (Icc a b) := hCD.continuousOn.mono hIcc_pos
  obtain ⟨hamp_bv, hamp_var⟩ := vdc_variation_on_Icc hab ha hCD hV
  have hvdc := van_der_corput_second hab hc hlam hφ hφ' hφ'_mono hφ''_lb hamp_cont hamp_bv hM
  have hden : 0 < Real.sqrt (c * lam) := Real.sqrt_pos.mpr (mul_pos hc hlam)
  exact hvdc.trans (by gcongr)

lemma abs_edgePhiDeriv2_eq_hankelEdgeM' {x : ℝ} (hx : 0 < x) :
    |edgePhiDeriv2 x| = hankelEdgeM' x := by
  have hm := (hankelEdgeM'_bounds hx).1
  have hpos : 0 < hankelEdgeM' x := lt_of_lt_of_le (by positivity) hm
  have hdef : hankelEdgeM' x = -edgePhiDeriv2 x := rfl
  rw [hdef, abs_of_neg (by linarith)]

/-! ### Exponential decay tails on `[a, ∞)` (`1 / 16 ≤ a`) and `L ≥ 2` comparisons -/

lemma poly14_exp_half_le {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ 14 * Real.exp (-(π / 2 * x)) ≤ 3 * (Nat.factorial 15 : ℝ) := by
  have h1x : 0 ≤ 1 + x := by linarith
  have hsum : (1 + x) ^ 15 / (Nat.factorial 15 : ℝ) ≤ Real.exp (1 + x) := by
    have hs := Real.sum_le_exp_of_nonneg h1x 16
    have hsingle : (1 + x) ^ 15 / (Nat.factorial 15 : ℝ) ≤
        ∑ i ∈ Finset.range 16, (1 + x) ^ i / (Nat.factorial i : ℝ) :=
      Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg h1x i) (Nat.cast_nonneg _))
        (Finset.mem_range.mpr (by norm_num))
    exact hsingle.trans hs
  have h15 : (1 + x) ^ 14 ≤ (1 + x) ^ 15 := by
    have : 1 ≤ 1 + x := by linarith
    calc (1 + x) ^ 14 = (1 + x) ^ 14 * 1 := (mul_one _).symm
      _ ≤ (1 + x) ^ 14 * (1 + x) := mul_le_mul_of_nonneg_left this (pow_nonneg h1x 14)
      _ = (1 + x) ^ 15 := by ring
  have hexp_15 : (1 + x) ^ 14 ≤ (Nat.factorial 15 : ℝ) * Real.exp (1 + x) := by
    calc (1 + x) ^ 14 ≤ (1 + x) ^ 15 := h15
      _ = (Nat.factorial 15 : ℝ) * ((1 + x) ^ 15 / (Nat.factorial 15 : ℝ)) := by
            field_simp [show (Nat.factorial 15 : ℝ) ≠ 0 by positivity]
      _ ≤ (Nat.factorial 15 : ℝ) * Real.exp (1 + x) :=
            mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
  have hexp_dec : Real.exp (1 + x) * Real.exp (-(π / 2 * x)) ≤ 3 := by
    rw [← Real.exp_add]
    have harg : 1 + x + -(π / 2 * x) ≤ 1 := by nlinarith [Real.pi_gt_three]
    have he1 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.le).trans (by norm_num)
    exact (Real.exp_le_exp.mpr harg).trans he1
  calc (1 + x) ^ 14 * Real.exp (-(π / 2 * x))
      ≤ ((Nat.factorial 15 : ℝ) * Real.exp (1 + x)) * Real.exp (-(π / 2 * x)) :=
        mul_le_mul_of_nonneg_right hexp_15 (Real.exp_pos _).le
    _ = (Nat.factorial 15 : ℝ) * (Real.exp (1 + x) * Real.exp (-(π / 2 * x))) := by ring
    _ ≤ (Nat.factorial 15 : ℝ) * 3 := mul_le_mul_of_nonneg_left hexp_dec (Nat.cast_nonneg _)
    _ = 3 * (Nat.factorial 15 : ℝ) := by ring

lemma integrable_pow14_exp_half :
    Integrable (fun τ : ℝ => (1 + |τ|) ^ 14 * Real.exp (-(π / 2 * |τ|))) := by
  refine ((poly14_exp_half_le (x := 0) le_rfl |> fun _ =>
    integrable_inv_one_add_abs_sq.const_mul (Nat.factorial 17 * 3 : ℝ))).mono' ?_ (ae_of_all _ fun τ => ?_)
  · exact (((continuous_const.add continuous_abs).pow 14).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)).aestronglyMeasurable
  · have hnn : 0 ≤ (1 + |τ|) ^ 14 * Real.exp (-(π / 2 * |τ|)) := by positivity
    rw [Real.norm_of_nonneg hnn]
    have h1x : 0 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    have hsum : (1 + |τ|) ^ 17 / (Nat.factorial 17 : ℝ) ≤ Real.exp (1 + |τ|) := by
      have hs := Real.sum_le_exp_of_nonneg h1x 18
      exact (Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg h1x i) (Nat.cast_nonneg _))
        (Finset.mem_range.mpr (by norm_num))).trans hs
    have h16_17 : (1 + |τ|) ^ 16 ≤ (1 + |τ|) ^ 17 := by
      have : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
      calc (1 + |τ|) ^ 16 = (1 + |τ|) ^ 16 * 1 := (mul_one _).symm
        _ ≤ (1 + |τ|) ^ 16 * (1 + |τ|) := mul_le_mul_of_nonneg_left this (pow_nonneg h1x 16)
        _ = (1 + |τ|) ^ 17 := by ring
    have hexp_dec : Real.exp (1 + |τ|) * Real.exp (-(π / 2 * |τ|)) ≤ 3 := by
      rw [← Real.exp_add]
      have harg : 1 + |τ| + -(π / 2 * |τ|) ≤ 1 := by nlinarith [Real.pi_gt_three, abs_nonneg τ]
      exact (Real.exp_le_exp.mpr harg).trans ((Real.exp_one_lt_d9.le).trans (by norm_num))
    have h16 : (1 + |τ|) ^ 16 * Real.exp (-(π / 2 * |τ|)) ≤ (Nat.factorial 17 : ℝ) * 3 := by
      have h16' : (1 + |τ|) ^ 16 ≤ (Nat.factorial 17 : ℝ) * Real.exp (1 + |τ|) := by
        calc (1 + |τ|) ^ 16 ≤ (1 + |τ|) ^ 17 := h16_17
          _ = (Nat.factorial 17 : ℝ) * ((1 + |τ|) ^ 17 / (Nat.factorial 17 : ℝ)) := by
                field_simp [show (Nat.factorial 17 : ℝ) ≠ 0 by positivity]
          _ ≤ (Nat.factorial 17 : ℝ) * Real.exp (1 + |τ|) :=
                mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
      calc (1 + |τ|) ^ 16 * Real.exp (-(π / 2 * |τ|))
          ≤ ((Nat.factorial 17 : ℝ) * Real.exp (1 + |τ|)) * Real.exp (-(π / 2 * |τ|)) :=
            mul_le_mul_of_nonneg_right h16' (Real.exp_pos _).le
        _ = (Nat.factorial 17 : ℝ) * (Real.exp (1 + |τ|) * Real.exp (-(π / 2 * |τ|))) := by ring
        _ ≤ (Nat.factorial 17 : ℝ) * 3 := mul_le_mul_of_nonneg_left hexp_dec (Nat.cast_nonneg _)
    rw [show (Nat.factorial 17 * 3 : ℝ) * (1 / (1 + |τ|) ^ 2) = (Nat.factorial 17 * 3 : ℝ) / (1 + |τ|) ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    calc (1 + |τ|) ^ 14 * Real.exp (-(π / 2 * |τ|)) * (1 + |τ|) ^ 2
        = (1 + |τ|) ^ 16 * Real.exp (-(π / 2 * |τ|)) := by ring
      _ ≤ (Nat.factorial 17 : ℝ) * 3 := h16

lemma warpAmpLeft_M_V_exp_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ M1 V1 c₀ : ℝ, 0 < M1 ∧ 0 < V1 ∧ 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ (σ a : ℝ), (σ = 1 ∨ σ = -1) → 1 / 16 ≤ a →
        (∀ x ∈ Ici a, ‖warpAmpLeft h ε c ξ (σ * x)‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * a))) ∧
        (∀ T : ℝ, a ≤ T →
          ∫ x in Icc a T, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤
            V1 * c⁻¹ * Real.exp (-(π / 2 * a))) := by
  obtain ⟨C, c₀, hC0, hc0, hB⟩ := warpAmpLeft_bounds hK4 h
  set I14_h : ℝ := ∫ τ : ℝ, (1 + |τ|) ^ 14 * Real.exp (-(π / 2 * |τ|))
  have hI_int := integrable_pow14_exp_half
  have hI_nn : 0 ≤ I14_h := integral_nonneg fun _ => by positivity
  set C1 : ℝ := max C 1
  set M1 : ℝ := C1 * (3 * (Nat.factorial 15 : ℝ))
  set V1 : ℝ := C1 * max I14_h 1
  refine ⟨M1, V1, c₀, by positivity, by positivity, hc0, fun ε c ξ hε hc σ a hσ ha => ?_⟩
  obtain ⟨hCD, _, hOuter⟩ := hB ε c ξ hε hc
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one (hc0.trans hc)
  have hCC1 : C ≤ C1 := le_max_left C 1
  have ha_pos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hexp_split : ∀ x : ℝ, a ≤ x →
      Real.exp (-(π * x)) = Real.exp (-(π / 2 * x)) * Real.exp (-(π / 2 * x)) ∧
      Real.exp (-(π / 2 * x)) ≤ Real.exp (-(π / 2 * a)) := fun x hax => by
    refine ⟨by rw [← Real.exp_add]; congr 1; ring,
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hax (by positivity)))⟩
  have hM : ∀ x ∈ Ici a, ‖warpAmpLeft h ε c ξ (σ * x)‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * a)) := by
    intro x hx
    have hax : a ≤ x := hx
    have hx0 : 0 ≤ x := le_trans ha_pos.le hax
    have h16 : 1 / 16 ≤ |σ * x| := by rw [abs_mul_sign hσ, abs_of_nonneg hx0]; exact le_trans ha hax
    have h0 := (hOuter (σ * x) h16).1
    rw [abs_mul_sign hσ, abs_of_nonneg hx0] at h0
    obtain ⟨heq, hdec⟩ := hexp_split x hax
    have hpe := poly14_exp_half_le hx0
    calc ‖warpAmpLeft h ε c ξ (σ * x)‖
        ≤ C * c⁻¹ * (1 + x) ^ 14 * (Real.exp (-(π / 2 * x)) * Real.exp (-(π / 2 * x))) := by
            rw [← heq]; exact h0
      _ = C * c⁻¹ * ((1 + x) ^ 14 * Real.exp (-(π / 2 * x))) * Real.exp (-(π / 2 * x)) := by ring
      _ ≤ C1 * c⁻¹ * (3 * (Nat.factorial 15 : ℝ)) * Real.exp (-(π / 2 * a)) := by gcongr
      _ = M1 * c⁻¹ * Real.exp (-(π / 2 * a)) := by simp only [M1]; ring
  set g_dom : ℝ → ℝ := fun x => C1 * c⁻¹ * Real.exp (-(π / 2 * a)) * ((1 + |x|) ^ 14 * Real.exp (-(π / 2 * |x|)))
  have hg_int : Integrable g_dom := hI_int.const_mul _
  have hg_val : ∫ x : ℝ, g_dom x ≤ V1 * c⁻¹ * Real.exp (-(π / 2 * a)) := by
    rw [integral_const_mul]
    have hI_le : I14_h ≤ max I14_h 1 := le_max_left _ _
    calc C1 * c⁻¹ * Real.exp (-(π / 2 * a)) * I14_h
        ≤ C1 * c⁻¹ * Real.exp (-(π / 2 * a)) * max I14_h 1 := by gcongr
      _ = V1 * c⁻¹ * Real.exp (-(π / 2 * a)) := by simp only [V1]; ring
  have hderiv_sign_norm : ∀ x : ℝ, x ≠ 0 →
      ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ = ‖deriv (warpAmpLeft h ε c ξ) (σ * x)‖ := by
    intro x hx
    rcases hσ with rfl | rfl
    · simp
    · simp only [neg_one_mul]
      have hnx : -x ∈ {τ : ℝ | τ ≠ 0} := neg_ne_zero.mpr hx
      have h1 : HasDerivAt (warpAmpLeft h ε c ξ) (deriv (warpAmpLeft h ε c ξ) (-x)) (-x) :=
        ((hCD.contDiffAt (isOpen_ne.mem_nhds hnx)).differentiableAt (by norm_num)).hasDerivAt
      have h2 := h1.scomp x (hasDerivAt_neg x)
      change ‖deriv (warpAmpLeft h ε c ξ ∘ Neg.neg) x‖ = ‖deriv (warpAmpLeft h ε c ξ) (-x)‖
      rw [h2.deriv, norm_smul]; simp
  have hV : ∀ T : ℝ, a ≤ T →
      ∫ x in Icc a T, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤ V1 * c⁻¹ * Real.exp (-(π / 2 * a)) := by
    intro T _
    have hIcc_pos : ∀ x ∈ Icc a T, 0 < x := fun x hx => lt_of_lt_of_le ha_pos hx.1
    have hcd1 : ContDiffOn ℝ 1 (fun t => warpAmpLeft h ε c ξ (σ * t)) (Ioi 0) :=
      (warpAmpLeft_sign_CD hCD hσ).of_le (by norm_num)
    have hcont : ContinuousOn (fun x => ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖) (Icc a T) := by
      have hc0' : ContinuousOn (deriv (fun t => warpAmpLeft h ε c ξ (σ * t))) (Ioi 0) :=
        (hcd1.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
          fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm
      exact hc0'.norm.mono fun x hx => hIcc_pos x hx
    have hint1 : IntegrableOn (fun x => ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖) (Icc a T) :=
      hcont.integrableOn_Icc
    have hpt : ∀ x ∈ Icc a T, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤ g_dom x := by
      intro x hx
      have hxpos : 0 < x := hIcc_pos x hx
      have hax : a ≤ x := hx.1
      have h16 : 1 / 16 ≤ |σ * x| := by rw [abs_mul_sign hσ, abs_of_pos hxpos]; exact le_trans ha hax
      have hd1 := (hOuter (σ * x) h16).2.1
      rw [abs_mul_sign hσ, abs_of_pos hxpos] at hd1
      obtain ⟨heq, hdec⟩ := hexp_split x hax
      rw [hderiv_sign_norm x hxpos.ne']
      calc ‖deriv (warpAmpLeft h ε c ξ) (σ * x)‖
          ≤ C * c⁻¹ * (1 + x) ^ 14 * (Real.exp (-(π / 2 * x)) * Real.exp (-(π / 2 * x))) := by
              rw [← heq]; exact hd1
        _ = C * c⁻¹ * Real.exp (-(π / 2 * x)) * ((1 + x) ^ 14 * Real.exp (-(π / 2 * x))) := by ring
        _ ≤ C1 * c⁻¹ * Real.exp (-(π / 2 * a)) * ((1 + |x|) ^ 14 * Real.exp (-(π / 2 * |x|))) := by
              rw [abs_of_pos hxpos]; gcongr
        _ = g_dom x := rfl
    have hmono := setIntegral_mono_on hint1 hg_int.integrableOn measurableSet_Icc hpt
    have hbound_int : ∫ x in Icc a T, g_dom x ≤ ∫ x : ℝ, g_dom x :=
      setIntegral_le_integral hg_int (Eventually.of_forall fun x => by positivity)
    exact (hmono.trans hbound_int).trans hg_val
  exact ⟨hM, hV⟩

lemma exp_neg_half_tau0_half_le {L : ℝ} (hL : 2 ≤ L) :
    Real.exp (-(π / 2 * tau0 (L / 2))) ≤ 48 * L ^ (-(3 / 2 : ℝ)) := by
  have hL2 : 1 ≤ L / 2 := by linarith
  have hL0 : 0 < L := by linarith
  have htau := (tau0_large_bounds hL2).1
  set u := Real.exp (L / 2) / 2
  have hu0 : 0 ≤ u := by positivity
  have hu_le : u ≤ π / 2 * tau0 (L / 2) := by
    calc u = π / 2 * (Real.exp (L / 2) / π) := by dsimp [u]; field_simp [Real.pi_ne_zero]
      _ ≤ π / 2 * tau0 (L / 2) := mul_le_mul_of_nonneg_left htau (by positivity)
  have hexp_u : u ^ 2 / 2 ≤ Real.exp u := by
    have hs := Real.sum_le_exp_of_nonneg hu0 3
    have h1 := Finset.single_le_sum (f := fun i : ℕ => u ^ i / (Nat.factorial i : ℝ))
      (fun i _ => div_nonneg (pow_nonneg hu0 i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (by decide : 2 < 3))
    simpa [Nat.factorial] using h1.trans hs
  have hexp_L : L ^ 3 / 6 ≤ Real.exp L := by
    have hs := Real.sum_le_exp_of_nonneg hL0.le 4
    have h1 := Finset.single_le_sum (f := fun i : ℕ => L ^ i / (Nat.factorial i : ℝ))
      (fun i _ => div_nonneg (pow_nonneg hL0.le i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (by decide : 3 < 4))
    simpa [Nat.factorial] using h1.trans hs
  have hu2 : u ^ 2 / 2 = Real.exp L / 8 := by
    dsimp [u]
    rw [div_pow, ← Real.exp_nat_mul]
    ring_nf
  have hL3_le : L ^ (3 / 2 : ℝ) ≤ L ^ 3 := by
    have h1 : (1 : ℝ) ≤ L := by linarith
    calc L ^ (3 / 2 : ℝ) ≤ L ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = L ^ 3 := Real.rpow_natCast L 3
  have hL32_pos : 0 < L ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have h1 : Real.exp L / 8 ≤ Real.exp (π / 2 * tau0 (L / 2)) := by
    calc Real.exp L / 8 = u ^ 2 / 2 := hu2.symm
      _ ≤ Real.exp u := hexp_u
      _ ≤ Real.exp (π / 2 * tau0 (L / 2)) := Real.exp_le_exp.mpr hu_le
  have h2 : L ^ (3 / 2 : ℝ) ≤ 48 * Real.exp (π / 2 * tau0 (L / 2)) := by
    calc L ^ (3 / 2 : ℝ) ≤ L ^ 3 := hL3_le
      _ = 48 * ((L ^ 3 / 6) / 8) := by ring
      _ ≤ 48 * (Real.exp L / 8) := by gcongr
      _ ≤ 48 * Real.exp (π / 2 * tau0 (L / 2)) := by gcongr
  rw [Real.exp_neg]
  calc (Real.exp (π / 2 * tau0 (L / 2)))⁻¹
      = 48 * (48 * Real.exp (π / 2 * tau0 (L / 2)))⁻¹ := by field_simp
    _ ≤ 48 * (L ^ (3 / 2 : ℝ))⁻¹ := by
          gcongr
    _ = 48 * L ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_neg hL0.le]

lemma exp_half_L_mul_exp_s2_le {L : ℝ} (hL : 2 ≤ L) :
    Real.exp (L / 2) * Real.exp (-(π / 2 * (3 / 4 * tau0 L))) ≤ 100 * L ^ (-(3 / 2 : ℝ)) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have htau := (tau0_large_bounds hL1).1
  set v : ℝ := 3 / 8 * Real.exp L
  have hv0 : 0 ≤ v := by positivity
  have hv_le : v ≤ π / 2 * (3 / 4 * tau0 L) := by
    calc v = π / 2 * (3 / 4 * (Real.exp L / π)) := by dsimp [v]; field_simp [Real.pi_ne_zero]; ring
      _ ≤ π / 2 * (3 / 4 * tau0 L) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htau (by norm_num)) (by positivity)
  have hexp_v : v ^ 2 / 2 ≤ Real.exp v := by
    have hs := Real.sum_le_exp_of_nonneg hv0 3
    have h1 := Finset.single_le_sum (f := fun i : ℕ => v ^ i / (Nat.factorial i : ℝ))
      (fun i _ => div_nonneg (pow_nonneg hv0 i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (by decide : 2 < 3))
    simpa [Nat.factorial] using h1.trans hs
  have hexp_L : L ^ 3 / 6 ≤ Real.exp L := by
    have hs := Real.sum_le_exp_of_nonneg hL0.le 4
    have h1 := Finset.single_le_sum (f := fun i : ℕ => L ^ i / (Nat.factorial i : ℝ))
      (fun i _ => div_nonneg (pow_nonneg hL0.le i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (by decide : 3 < 4))
    simpa [Nat.factorial] using h1.trans hs
  have hexp_L2 : Real.exp (L / 2) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
  have hv2 : (9 / 128 : ℝ) * Real.exp L ^ 2 ≤ Real.exp (π / 2 * (3 / 4 * tau0 L)) := by
    calc (9 / 128 : ℝ) * Real.exp L ^ 2 = v ^ 2 / 2 := by dsimp [v]; ring
      _ ≤ Real.exp v := hexp_v
      _ ≤ Real.exp (π / 2 * (3 / 4 * tau0 L)) := Real.exp_le_exp.mpr hv_le
  have hL3_le : L ^ (3 / 2 : ℝ) ≤ L ^ 3 := by
    calc L ^ (3 / 2 : ℝ) ≤ L ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L ^ 3 := Real.rpow_natCast L 3
  have hexpL_pos : 0 < Real.exp L := Real.exp_pos L
  have hprod : L ^ (3 / 2 : ℝ) * Real.exp (L / 2) ≤ 100 * Real.exp (π / 2 * (3 / 4 * tau0 L)) := by
    calc L ^ (3 / 2 : ℝ) * Real.exp (L / 2) ≤ L ^ 3 * Real.exp L := by gcongr
      _ ≤ (6 * Real.exp L) * Real.exp L := by gcongr; linarith
      _ = 6 * Real.exp L ^ 2 := by ring
      _ ≤ 100 * ((9 / 128 : ℝ) * Real.exp L ^ 2) := by
          nlinarith [sq_nonneg (Real.exp L)]
      _ ≤ 100 * Real.exp (π / 2 * (3 / 4 * tau0 L)) := by gcongr
  rw [Real.exp_neg]
  have h1_cancel : L ^ (3 / 2 : ℝ) * (L ^ (3 / 2 : ℝ))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hL0 _).ne'
  calc Real.exp (L / 2) * (Real.exp (π / 2 * (3 / 4 * tau0 L)))⁻¹
      = (L ^ (3 / 2 : ℝ) * Real.exp (L / 2) * (Real.exp (π / 2 * (3 / 4 * tau0 L)))⁻¹) * L ^ (-(3 / 2 : ℝ)) := by
          rw [Real.rpow_neg hL0.le]; linear_combination -Real.exp (L / 2) * (Real.exp (π / 2 * (3 / 4 * tau0 L)))⁻¹ * h1_cancel
    _ ≤ 100 * L ^ (-(3 / 2 : ℝ)) := by
          gcongr
          rw [mul_inv_le_iff₀ (Real.exp_pos _)]
          exact hprod

/-! ### Threshold ordering helpers (`r = (c * L)⁻¹`) -/

lemma r_le_three_quarters_tau0 {c L : ℝ} (hc : 32 ^ 4 ≤ c) (hL_low : 3 * FctSym.physDelta c ≤ L) :
    (c * L)⁻¹ ≤ 1 / 16 ∧ (c * L)⁻¹ ≤ 3 / 4 * tau0 L := by
  have hcpos : 0 < c := by positivity
  have hpd := physDelta_ge hc
  have hL_ge : (3 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) ≤ L := by linarith
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_ge
  have hcL : (3 / 2 : ℝ) * c ^ (1 / 2 : ℝ) ≤ c * L := by
    have hpow : c ^ (1 / 2 : ℝ) = c * c ^ (-(1 / 2 : ℝ)) := by
      nth_rw 2 [← Real.rpow_one c]; rw [← Real.rpow_add hcpos]; congr 1; norm_num
    calc (3 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c * ((3 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ))) := by rw [hpow]; ring
      _ ≤ c * L := mul_le_mul_of_nonneg_left hL_ge hcpos.le
  have hc12 : (32 : ℝ) ^ 2 ≤ c ^ (1 / 2 : ℝ) := by
    have h1 : (32 : ℝ) ^ 2 = ((32 : ℝ) ^ 4) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (32 : ℝ) 4, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h1]; exact Real.rpow_le_rpow (by positivity) hc (by norm_num)
  have hcL16 : (16 : ℝ) ≤ c * L := by linarith
  have hr16 : (c * L)⁻¹ ≤ 1 / 16 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hcL16
  refine ⟨hr16, ?_⟩
  rcases le_or_gt L 1 with hL1 | hL1
  · have htau := (tau0_small_bounds hL_pos hL1).1
    have hL32 : c ^ (-(3 / 4 : ℝ)) ≤ L ^ (3 / 2 : ℝ) := by
      have hc12' : c ^ (-(1 / 2 : ℝ)) ≤ L := by linarith
      have h1 : c ^ (-(3 / 4 : ℝ)) = (c ^ (-(1 / 2 : ℝ))) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul hcpos.le]; congr 1; norm_num
      rw [h1]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hcpos.le _) hc12' (by norm_num)
    have hc14 : (32 : ℝ) ≤ c * L ^ (3 / 2 : ℝ) := by
      have h1 : c * c ^ (-(3 / 4 : ℝ)) = c ^ (1 / 4 : ℝ) := by
        nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hcpos]; congr 1; norm_num
      have h2 : (32 : ℝ) ≤ c ^ (1 / 4 : ℝ) := by
        have h3 : (32 : ℝ) = ((32 : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_natCast (32 : ℝ) 4, ← Real.rpow_mul (by norm_num)]; norm_num
        rw [h3]; exact Real.rpow_le_rpow (by positivity) hc (by norm_num)
      calc (32 : ℝ) ≤ c ^ (1 / 4 : ℝ) := h2
        _ = c * c ^ (-(3 / 4 : ℝ)) := h1.symm
        _ ≤ c * L ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hL32 hcpos.le
    have hLsqrt : L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_add hL_pos]; congr 1; norm_num
    have h34 : (c * L)⁻¹ ≤ 3 / 4 * Real.sqrt L := by
      rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = (3 / 4) * (4 / 3) := by norm_num
        _ ≤ (3 / 4) * (c * L ^ (3 / 2 : ℝ)) := by gcongr; linarith
        _ = 3 / 4 * Real.sqrt L * (c * L) := by rw [← hLsqrt]; ring
    exact h34.trans (mul_le_mul_of_nonneg_left htau (by norm_num))
  · have htau := (tau0_large_bounds hL1.le).1
    have h_e : (2 : ℝ) ≤ Real.exp L := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := (by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)])
      exact he1.trans (Real.exp_le_exp.mpr hL1.le)
    have htau_ge : 1 / 2 ≤ tau0 L := by
      have : π ≤ 4 := Real.pi_lt_four.le
      calc (1 / 2 : ℝ) = 2 / 4 := by norm_num
        _ ≤ Real.exp L / π := div_le_div₀ (by positivity) h_e Real.pi_pos this
        _ ≤ tau0 L := htau
    linarith

lemma s1_le_s2 {L : ℝ} (hL : 2 ≤ L) :
    1 / 16 ≤ tau0 (L / 2) ∧ tau0 (L / 2) ≤ 3 / 4 * tau0 L := by
  have hL2 : 1 ≤ L / 2 := by linarith
  have hL1 : 1 ≤ L := by linarith
  have ht1 := tau0_large_bounds hL2
  have ht2 := tau0_large_bounds hL1
  have he1 : (8 / 3 : ℝ) ≤ Real.exp (L / 2) := by
    have := Real.exp_one_gt_d9
    have h1 : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith
    exact h1.trans (Real.exp_le_exp.mpr hL2)
  have hpi4 : π ≤ 4 := Real.pi_lt_four.le
  refine ⟨?_, ?_⟩
  · calc (1 / 16 : ℝ) ≤ (8 / 3) / 4 := by norm_num
      _ ≤ Real.exp (L / 2) / π := div_le_div₀ (by positivity) he1 Real.pi_pos hpi4
      _ ≤ tau0 (L / 2) := ht1.1
  · have hexp_mul : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hineq : 2 * Real.exp (L / 2) ≤ 3 / 4 * Real.exp L := by
      rw [hexp_mul]
      nlinarith [Real.exp_pos (L / 2)]
    calc tau0 (L / 2) ≤ 2 * Real.exp (L / 2) / π := ht1.2
      _ ≤ (3 / 4 * Real.exp L) / π := div_le_div_of_nonneg_right hineq Real.pi_pos.le
      _ = 3 / 4 * (Real.exp L / π) := by ring
      _ ≤ 3 / 4 * tau0 L := mul_le_mul_of_nonneg_left ht2.1 (by norm_num)

/-! ### One-step IBP + VdC1 on `[r, s₁]` for `2 ≤ L` -/

lemma warpAmpLeft_sign_iteratedDeriv_norm {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c ξ σ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → (σ = 1 ∨ σ = -1) →
      ContDiffOn ℝ 2 (fun t => warpAmpLeft h ε c ξ (σ * t)) (Ioi 0) ∧
      (∀ t : ℝ, 0 < t → t ≤ 1 / 16 → ∀ j ≤ 2,
        ‖iteratedDeriv j (fun s => warpAmpLeft h ε c ξ (σ * s)) t‖ ≤
          (C * c⁻¹ * t ^ (1 / 2 : ℝ)) * t ^ (-(j : ℤ))) ∧
      (∀ t : ℝ, 1 / 16 ≤ t → ∀ j ≤ 2,
        ‖iteratedDeriv j (fun s => warpAmpLeft h ε c ξ (σ * s)) t‖ ≤
          C * c⁻¹ * (1 + t) ^ 14 * Real.exp (-(π * t))) := by
  obtain ⟨C, c₀, hC0, hc0, hW⟩ := warpAmpLeft_bounds hK4 h
  refine ⟨C, c₀, hC0, hc0, fun ε c ξ σ hε hc hσ => ?_⟩
  obtain ⟨hCD, hNear, hOuter⟩ := hW ε c ξ hε hc
  have hCD_pos : ContDiffOn ℝ 2 (fun t => warpAmpLeft h ε c ξ (σ * t)) (Ioi 0) :=
    warpAmpLeft_sign_CD hCD hσ
  have hnorm_iter : ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ, 0 < t →
      ‖iteratedDeriv j (fun s => warpAmpLeft h ε c ξ (σ * s)) t‖ =
        ‖iteratedDeriv j (warpAmpLeft h ε c ξ) (σ * t)‖ := by
    intro j hj t ht
    rcases hσ with rfl | rfl
    · simp
    · simp only [neg_one_mul]
      have hnt : -t ≠ 0 := neg_ne_zero.mpr ht.ne'
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp [iteratedDeriv_zero]
      · simp only [iteratedDeriv_one]
        have h1 : HasDerivAt (warpAmpLeft h ε c ξ) (deriv (warpAmpLeft h ε c ξ) (-t)) (-t) :=
          ((hCD.contDiffAt (isOpen_ne.mem_nhds hnt)).differentiableAt (by norm_num)).hasDerivAt
        have h2 := h1.scomp t (hasDerivAt_neg t)
        change ‖deriv (warpAmpLeft h ε c ξ ∘ Neg.neg) t‖ = _
        rw [h2.deriv, norm_smul]; simp
      · simp only [iteratedDeriv_succ', iteratedDeriv_zero]
        have hd1_eq : ∀ᶠ s in 𝓝 t,
            deriv (fun u => warpAmpLeft h ε c ξ (-u)) s =
              -(deriv (warpAmpLeft h ε c ξ) (-s)) := by
          filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
          have hns : -s ≠ 0 := neg_ne_zero.mpr (mem_Ioi.mp hs).ne'
          have h1 : HasDerivAt (warpAmpLeft h ε c ξ) (deriv (warpAmpLeft h ε c ξ) (-s)) (-s) :=
            ((hCD.contDiffAt (isOpen_ne.mem_nhds hns)).differentiableAt (by norm_num)).hasDerivAt
          have h2 := h1.scomp s (hasDerivAt_neg s)
          change deriv (warpAmpLeft h ε c ξ ∘ Neg.neg) s = _
          rw [h2.deriv, neg_one_smul]
        have hd_cd : ContDiffOn ℝ 1 (deriv (warpAmpLeft h ε c ξ)) {τ : ℝ | τ ≠ 0} :=
          (hCD.derivWithin isOpen_ne.uniqueDiffOn (m := 1) (by norm_num)).congr
            fun u hu => (derivWithin_of_isOpen isOpen_ne hu).symm
        have h1' : HasDerivAt (deriv (warpAmpLeft h ε c ξ))
            (deriv (deriv (warpAmpLeft h ε c ξ)) (-t)) (-t) :=
          ((hd_cd.contDiffAt (isOpen_ne.mem_nhds hnt)).differentiableAt (by norm_num)).hasDerivAt
        have h2' := (h1'.scomp t (hasDerivAt_neg t)).neg
        have hd2_eq : deriv (fun s => deriv (fun u => warpAmpLeft h ε c ξ (-u)) s) t =
            deriv (fun s => -(deriv (warpAmpLeft h ε c ξ) (-s))) t := Filter.EventuallyEq.deriv_eq hd1_eq
        rw [show (fun s => deriv (fun u => warpAmpLeft h ε c ξ (-u)) s) =
            deriv (fun u => warpAmpLeft h ε c ξ (-u)) from rfl] at hd2_eq
        rw [hd2_eq]
        change ‖deriv (Neg.neg ∘ deriv (warpAmpLeft h ε c ξ) ∘ Neg.neg) t‖ = _
        have h2'_eq : HasDerivAt (Neg.neg ∘ deriv (warpAmpLeft h ε c ξ) ∘ Neg.neg)
            (-((-1 : ℝ) • deriv (deriv (warpAmpLeft h ε c ξ)) (-t))) t := h2'
        rw [h2'_eq.deriv]
        simp
  refine ⟨hCD_pos, fun t ht ht16 j hj => ?_, fun t ht16 j hj => ?_⟩
  · rw [hnorm_iter j hj t ht]
    have hst : σ * t ≠ 0 := by rcases hσ with rfl | rfl <;> [simpa using ht.ne'; simpa using neg_ne_zero.mpr ht.ne']
    have habs : |σ * t| = t := by rw [abs_mul_sign hσ, abs_of_pos ht]
    have hnb := hNear (σ * t) hst (habs.le.trans ht16)
    rw [habs] at hnb
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one]; exact hnb.1
    · simp only [iteratedDeriv_one, Nat.cast_one]
      calc ‖deriv (warpAmpLeft h ε c ξ) (σ * t)‖ ≤ C * c⁻¹ * t ^ (-(1 / 2 : ℝ)) := hnb.2.1
        _ = (C * c⁻¹ * t ^ (1 / 2 : ℝ)) * t ^ (-1 : ℤ) := by
            rw [zpow_neg_one, ← Real.rpow_neg_one t, mul_assoc (C * c⁻¹), ← Real.rpow_add ht]
            congr 2; norm_num
    · simp only [iteratedDeriv_succ', iteratedDeriv_zero]
      calc ‖deriv (deriv (warpAmpLeft h ε c ξ)) (σ * t)‖ ≤ C * c⁻¹ * t ^ (-(3 / 2 : ℝ)) := hnb.2.2
        _ = (C * c⁻¹ * t ^ (1 / 2 : ℝ)) * t ^ (-(2 : ℤ)) := by
            rw [← Real.rpow_intCast t (-(2 : ℤ)), mul_assoc (C * c⁻¹), ← Real.rpow_add ht]
            congr 2; norm_num
  · rw [hnorm_iter j hj t (lt_of_lt_of_le (by norm_num) ht16)]
    have habs : |σ * t| = t := by
      rw [abs_mul_sign hσ, abs_of_pos (lt_of_lt_of_le (by norm_num) ht16)]
    have hob := hOuter (σ * t) (by rw [habs]; exact ht16)
    rw [habs] at hob
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simpa [iteratedDeriv_zero] using hob.1
    · simpa [iteratedDeriv_one] using hob.2.1
    · simpa [iteratedDeriv_succ', iteratedDeriv_zero] using hob.2.2

lemma warp_ibp1_vdc1_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ ε c ξ σ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (σ = 1 ∨ σ = -1) → ∀ L : ℝ, 2 ≤ L →
      ‖∫ τ in (c * L)⁻¹..(tau0 (L / 2)),
          warpAmpLeft h ε c ξ (σ * τ) *
            Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
        C * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Cw, c0w, hCw0, hc0w, hW⟩ := warpAmpLeft_sign_iteratedDeriv_norm hK4 h
  obtain ⟨C2, hC20, hPhi2⟩ := edgePhi_iteratedDeriv_bound 2 (by norm_num)
  obtain ⟨C3, hC30, hPhi3⟩ := edgePhi_iteratedDeriv_bound 3 (by norm_num)
  obtain ⟨C4, hC40, hPhi4⟩ := edgePhi_iteratedDeriv_bound 4 (by norm_num)
  set K_phi : ℝ := max 1 (max C2 (max C3 C4))
  have hK_phi : 1 ≤ K_phi := le_max_left _ _
  set I14 : ℝ := ∫ τ : ℝ, (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|))
  have hI14_int : Integrable (fun τ : ℝ => (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|))) :=
    integrable_pow_mul_exp_neg_pi 14
  have hI14_nn : 0 ≤ I14 := integral_nonneg fun _ => by positivity
  set C_bd : ℝ := 2 * Cw * (1 + 3 * (Nat.factorial 15 : ℝ) * 48)
  set A_ibp : ℝ := 104 * K_phi ^ 3 * Cw * 2
  set M_1 : ℝ := A_ibp * (1 + 3 * (Nat.factorial 15 : ℝ))
  set V_1 : ℝ := A_ibp * (2 + I14)
  set C : ℝ := C_bd + 6 * (M_1 + V_1)
  refine ⟨C, max (32 ^ 4) c0w, by positivity, le_max_left _ _, fun ε c ξ σ hε hc hσ L hL => ?_⟩
  have hc32 : (32 : ℝ) ^ 4 ≤ c := (le_max_left _ _).trans hc
  have hcw : c0w ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by positivity
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc32
  have hLpos : 0 < L := by linarith
  set r : ℝ := (c * L)⁻¹
  set s1 : ℝ := tau0 (L / 2)
  have hr_pos : 0 < r := by positivity
  have hcL16 : (16 : ℝ) ≤ c * L := by
    calc (16 : ℝ) ≤ 32 ^ 4 * 2 := by norm_num
      _ ≤ c * L := mul_le_mul hc32 hL (by positivity) (by positivity)
  have hr16 : r ≤ 1 / 16 := by rw [one_div]; exact inv_anti₀ (by norm_num) hcL16
  have hs1_16 : 1 / 16 ≤ s1 := (s1_le_s2 hL).1
  have hrs1 : r ≤ s1 := hr16.trans hs1_16
  set ampσ : ℝ → ℂ := fun τ => warpAmpLeft h ε c ξ (σ * τ)
  set phi : ℝ → ℝ := fun τ => c * (σ * edgePhi L τ)
  have heq_int : (fun τ => ampσ τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))) =
      fun τ => Complex.exp (Complex.I * (phi τ : ℂ)) * ampσ τ := by
    ext τ
    rw [edgePhi_sign_mul hσ L τ, mul_comm (ampσ τ)]
    congr 2; dsimp [phi]; push_cast; ring
  rw [heq_int]
  set U : Set ℝ := Ioo 0 (tau0 L)
  have hU : IsOpen U := isOpen_Ioo
  have hs1_lt_tau0 : s1 < tau0 L := by
    have h1 : s1 ≤ 3 / 4 * tau0 L := (s1_le_s2 hL).2
    have h2 : 0 < tau0 L := tau0_pos (by linarith)
    linarith
  have hsub : Icc r s1 ⊆ U := fun x hx =>
    ⟨lt_of_lt_of_le hr_pos hx.1, lt_of_le_of_lt hx.2 hs1_lt_tau0⟩
  have hphi_cd4 : ContDiffOn ℝ 4 phi U :=
    (contDiff_const.mul (contDiff_const.mul (contDiff_edgePhi L))).contDiffOn.of_le (by simp)
  have hphi_deriv : ∀ τ : ℝ, deriv phi τ = c * σ * edgePhiDeriv L τ := fun τ => by
    have hd := ((hasDerivAt_edgePhi L τ).const_mul σ).const_mul c
    simpa [phi, mul_assoc] using hd.deriv
  have hphi_lb : ∀ τ : ℝ, 0 ≤ τ → τ ≤ s1 → c * (L / 2) ≤ |deriv phi τ| := fun τ hτ0 hτs1 => by
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [hphi_deriv τ, abs_mul, abs_mul, abs_of_pos hcpos, hσ1, mul_one,
      edgePhiDeriv_eq_sub_hankelEdgeM hτ0]
    have hs1_0 : 0 ≤ s1 := le_trans (by norm_num) hs1_16
    have hm_le : hankelEdgeM τ ≤ hankelEdgeM s1 :=
      hankelEdgeM_strictMonoOn.monotoneOn hτ0 hs1_0 hτs1
    have hs1_val : hankelEdgeM s1 = L / 2 := ceEll_tau0 (by linarith)
    have hge : L / 2 ≤ L - hankelEdgeM τ := by linarith
    rw [abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hge hcpos.le
  have hphi_ne : ∀ τ ∈ U, deriv phi τ ≠ 0 := fun τ hτ => by
    rw [hphi_deriv τ]
    have hm_lt : hankelEdgeM τ < L := by
      rw [← ceEll_tau0 (by linarith : 0 < L)]
      exact hankelEdgeM_strictMonoOn hτ.1.le (tau0_pos (by linarith)).le hτ.2
    have hed : edgePhiDeriv L τ ≠ 0 := by
      rw [edgePhiDeriv_eq_sub_hankelEdgeM hτ.1.le]; linarith
    have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    exact mul_ne_zero (mul_ne_zero hcpos.ne' hσne) hed
  obtain ⟨hCD_ampσ, hNear_ampσ, hOuter_ampσ⟩ := hW ε c ξ σ hε hcw hσ
  have hh_cd2 : ContDiffOn ℝ 2 ampσ U := hCD_ampσ.mono fun _ hx => hx.1
  have hibp := ibpStep_integral hrs1 hU hsub (hphi_cd4.of_le (by norm_num)) (hh_cd2.of_le (by norm_num)) hphi_ne
  -- Boundary terms `[exp(I * phi) * ampσ / (I * deriv phi)]_{r}^{s1}`
  have hbd_r : ‖Complex.exp (Complex.I * (phi r : ℂ)) * (ampσ r / (Complex.I * ((deriv phi r : ℝ) : ℂ)))‖ ≤
      2 * Cw * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hexp1 : ‖Complex.exp (Complex.I * (phi r : ℂ))‖ = 1 := by
      rw [Complex.norm_exp, Complex.I_mul_re, Complex.ofReal_im, neg_zero, Real.exp_zero]
    rw [norm_mul, hexp1, one_mul, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hamp_r := hNear_ampσ r hr_pos hr16 0 (by norm_num)
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hamp_r
    have hder_r := hphi_lb r hr_pos.le hrs1
    have hr12 : r ^ (1 / 2 : ℝ) = c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
      dsimp [r]
      rw [Real.inv_rpow (by positivity), Real.mul_rpow hcpos.le hLpos.le, mul_inv,
        ← Real.rpow_neg hcpos.le, ← Real.rpow_neg hLpos.le]
    have hden_pos : 0 < c * (L / 2) := by positivity
    calc ‖ampσ r‖ / |deriv phi r| ≤ (Cw * c⁻¹ * r ^ (1 / 2 : ℝ)) / (c * (L / 2)) :=
          div_le_div₀ (by positivity) hamp_r hden_pos hder_r
      _ = 2 * Cw * (c⁻¹ * c⁻¹ * c ^ (-(1 / 2 : ℝ))) * (L⁻¹ * L ^ (-(1 / 2 : ℝ))) := by
          rw [hr12]; ring
      _ ≤ 2 * Cw * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
          have hc_eq : c⁻¹ * c⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤ c ^ (-(3 / 2 : ℝ)) := by
            have h1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
            have hc32' : c⁻¹ * c ^ (-(1 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) := by
              rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
            calc c⁻¹ * c⁻¹ * c ^ (-(1 / 2 : ℝ)) = c⁻¹ * (c⁻¹ * c ^ (-(1 / 2 : ℝ))) := by ring
              _ ≤ 1 * c ^ (-(3 / 2 : ℝ)) := by rw [hc32']; exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hcpos.le _)
              _ = c ^ (-(3 / 2 : ℝ)) := one_mul _
          have hL_eq : L⁻¹ * L ^ (-(1 / 2 : ℝ)) = L ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_neg_one L, ← Real.rpow_add hLpos]; congr 1; norm_num
          rw [hL_eq]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_eq (by positivity))
            (Real.rpow_nonneg hLpos.le _)
  have hbd_s1 : ‖Complex.exp (Complex.I * (phi s1 : ℂ)) * (ampσ s1 / (Complex.I * ((deriv phi s1 : ℝ) : ℂ)))‖ ≤
      2 * Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hexp1 : ‖Complex.exp (Complex.I * (phi s1 : ℂ))‖ = 1 := by
      rw [Complex.norm_exp, Complex.I_mul_re, Complex.ofReal_im, neg_zero, Real.exp_zero]
    rw [norm_mul, hexp1, one_mul, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hamp_s1 := hOuter_ampσ s1 hs1_16 0 (by norm_num)
    simp only [iteratedDeriv_zero] at hamp_s1
    have hexp_split : Real.exp (-(π * s1)) = Real.exp (-(π / 2 * s1)) * Real.exp (-(π / 2 * s1)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hs1_0 : 0 ≤ s1 := by linarith
    have hpoly_h := poly14_exp_half_le hs1_0
    have hexp_h := exp_neg_half_tau0_half_le hL
    have hamp_bd : ‖ampσ s1‖ ≤ Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
      calc ‖ampσ s1‖ ≤ Cw * c⁻¹ * (1 + s1) ^ 14 * (Real.exp (-(π / 2 * s1)) * Real.exp (-(π / 2 * s1))) := by
            rw [← hexp_split]; exact hamp_s1
        _ = Cw * c⁻¹ * ((1 + s1) ^ 14 * Real.exp (-(π / 2 * s1))) * Real.exp (-(π / 2 * s1)) := by ring
        _ ≤ Cw * c⁻¹ * (3 * (Nat.factorial 15 : ℝ)) * (48 * L ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by ring
    have hder_s1 := hphi_lb s1 hs1_0 le_rfl
    have hden_s1 : c * 1 ≤ |deriv phi s1| := by
      have : c * 1 ≤ c * (L / 2) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
      exact this.trans hder_s1
    have hc_2_32 : c⁻¹ * c⁻¹ ≤ c ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc ‖ampσ s1‖ / |deriv phi s1| ≤ (Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * c⁻¹ * L ^ (-(3 / 2 : ℝ))) / (c * 1) :=
          div_le_div₀ (by positivity) hamp_bd (by positivity) hden_s1
      _ = Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * (c⁻¹ * c⁻¹) * L ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ 2 * Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
          have h1 : Cw * (3 * (Nat.factorial 15 : ℝ) * 48) ≤ 2 * Cw * (3 * (Nat.factorial 15 : ℝ) * 48) := by
            linarith [show 0 ≤ Cw * (3 * (Nat.factorial 15 : ℝ) * 48) by positivity]
          calc Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * (c⁻¹ * c⁻¹) * L ^ (-(3 / 2 : ℝ))
              ≤ (2 * Cw * (3 * (Nat.factorial 15 : ℝ) * 48)) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
                gcongr
            _ = _ := by ring
  -- Pointwise bounds on `ibpStep phi ampσ` and its derivative via `ibpStep_deriv_bound`
  have hphi_high : ∀ (w τ : ℝ), 0 < w → w ≤ 1 → 0 < τ → τ ≤ s1 → ∀ j ∈ ({1, 2, 3} : Finset ℕ),
      |iteratedDeriv (j + 1) phi τ| ≤ K_phi * w ^ (-(j : ℤ)) * |deriv phi τ| := by
    intro w τ hw0 hw1 hτ hτs1 j hj
    have hiter_eq : iteratedDeriv (j + 1) phi τ = c * (σ * iteratedDeriv (j + 1) (edgePhi L) τ) := by
      have hcd_sig : ContDiff ℝ (j + 1 : ℕ) (fun t => σ * edgePhi L t) :=
        (contDiff_const.mul (contDiff_edgePhi L)).of_le (by simp)
      have hcd_edge : ContDiff ℝ (j + 1 : ℕ) (edgePhi L) :=
        (contDiff_edgePhi L).of_le (by simp)
      have h1 : iteratedDeriv (j + 1) (fun t => c * (σ * edgePhi L t)) τ =
          c * iteratedDeriv (j + 1) (fun t => σ * edgePhi L t) τ :=
        iteratedDeriv_const_mul c hcd_sig.contDiffAt
      have h2 : iteratedDeriv (j + 1) (fun t => σ * edgePhi L t) τ =
          σ * iteratedDeriv (j + 1) (edgePhi L) τ :=
        iteratedDeriv_const_mul σ hcd_edge.contDiffAt
      change iteratedDeriv (j + 1) (fun t => c * (σ * edgePhi L t)) τ = _
      rw [h1, h2]
    have habs_le : |iteratedDeriv (j + 1) (edgePhi L) τ| ≤ K_phi := by
      have h1τ : 1 ≤ (1 + |τ|) ^ (2 - 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact (hPhi2 L τ).trans ((div_le_self hC20 h1τ).trans (le_max_of_le_right (le_max_left _ _)))
      · rcases Finset.mem_insert.mp hj' with rfl | hj''
        · exact (hPhi3 L τ).trans ((div_le_self hC30 (one_le_pow₀ (by linarith [abs_nonneg τ]))).trans
            (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
        · rw [Finset.mem_singleton.mp hj'']
          exact (hPhi4 L τ).trans ((div_le_self hC40 (one_le_pow₀ (by linarith [abs_nonneg τ]))).trans
            (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
    have hder_c : c ≤ |deriv phi τ| := by
      calc c = c * 1 := (mul_one c).symm
        _ ≤ c * (L / 2) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
        _ ≤ |deriv phi τ| := hphi_lb τ hτ.le hτs1
    have hw_ge1 : (1 : ℝ) ≤ w ^ (-(j : ℤ)) := by
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact one_le_pow₀ ((one_le_inv₀ hw0).mpr hw1)
    calc |iteratedDeriv (j + 1) phi τ| = c * |iteratedDeriv (j + 1) (edgePhi L) τ| := by
          rw [hiter_eq, abs_mul, abs_of_pos hcpos, abs_mul_sign hσ]
      _ ≤ c * K_phi := mul_le_mul_of_nonneg_left habs_le hcpos.le
      _ ≤ |deriv phi τ| * K_phi := mul_le_mul_of_nonneg_right hder_c (by positivity)
      _ = K_phi * 1 * |deriv phi τ| := by ring
      _ ≤ K_phi * w ^ (-(j : ℤ)) * |deriv phi τ| := by gcongr
  have hibp_pt : ∀ τ ∈ Icc r s1,
      (τ ≤ 1 / 16 →
        ‖ibpStep phi ampσ τ‖ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * τ ^ (-(1 / 2 : ℝ)) ∧
        ‖deriv (ibpStep phi ampσ) τ‖ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * τ ^ (-(3 / 2 : ℝ))) ∧
      (1 / 16 ≤ τ →
        ‖ibpStep phi ampσ τ‖ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * ((1 + τ) ^ 14 * Real.exp (-(π * τ))) ∧
        ‖deriv (ibpStep phi ampσ) τ‖ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * ((1 + τ) ^ 14 * Real.exp (-(π * τ)))) := by
    intro τ hτ
    have hτU : τ ∈ U := hsub hτ
    have hτpos : 0 < τ := hτU.1
    have hphi_l := hphi_lb τ hτpos.le hτ.2
    have hL2_pos : 0 < c * (L / 2) := by positivity
    refine ⟨fun hτ16 => ?_, fun hτ16 => ?_⟩
    · have hbd := ibpStep_deriv_bound (n := 1) (by norm_num) hU hphi_cd4 hh_cd2 hτU
        hL2_pos hτpos hK_phi (by positivity : 0 ≤ Cw * c⁻¹ * τ ^ (1 / 2 : ℝ))
        hphi_l (fun j hj => hphi_high τ τ hτpos (by linarith) hτpos hτ.2 j hj)
        (fun j hj => hNear_ampσ τ hτpos hτ16 j hj)
      have hcoef : 104 * K_phi ^ 3 * (Cw * c⁻¹ * τ ^ (1 / 2 : ℝ)) / (c * (L / 2) * τ) =
          A_ibp * c ^ (-2 : ℝ) * L⁻¹ * τ ^ (-(1 / 2 : ℝ)) := by
        have hpow : τ ^ (1 / 2 : ℝ) / τ = τ ^ (-(1 / 2 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one τ, ← Real.rpow_add hτpos]; congr 1; norm_num
        have hc2 : c⁻¹ / c = c ^ (-2 : ℝ) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
        calc 104 * K_phi ^ 3 * (Cw * c⁻¹ * τ ^ (1 / 2 : ℝ)) / (c * (L / 2) * τ)
            = (104 * K_phi ^ 3 * Cw * 2) * (c⁻¹ / c) * L⁻¹ * (τ ^ (1 / 2 : ℝ) / τ) := by ring
          _ = A_ibp * c ^ (-2 : ℝ) * L⁻¹ * τ ^ (-(1 / 2 : ℝ)) := by simp only [A_ibp, hc2, hpow]
      refine ⟨?_, ?_⟩
      · have h0 := hbd 0 (by norm_num)
        simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at h0
        exact h0.trans_eq hcoef
      · have h1 := hbd 1 le_rfl
        simp only [iteratedDeriv_one, Nat.cast_one, zpow_neg_one] at h1
        rw [hcoef, mul_assoc (A_ibp * c ^ (-2 : ℝ) * L⁻¹), ← Real.rpow_neg_one τ,
          ← Real.rpow_add hτpos] at h1
        exact h1.trans_eq (by congr 2; norm_num)
    · have hM_nn : 0 ≤ Cw * c⁻¹ * (1 + τ) ^ 14 * Real.exp (-(π * τ)) := by positivity
      have hbd := ibpStep_deriv_bound (n := 1) (by norm_num) hU hphi_cd4 hh_cd2 hτU
        hL2_pos zero_lt_one hK_phi hM_nn hphi_l
        (fun j hj => hphi_high 1 τ zero_lt_one le_rfl hτpos hτ.2 j hj)
        (fun j hj => by simpa using hOuter_ampσ τ hτ16 j hj)
      have hcoef : 104 * K_phi ^ 3 * (Cw * c⁻¹ * (1 + τ) ^ 14 * Real.exp (-(π * τ))) / (c * (L / 2)) =
          A_ibp * c ^ (-2 : ℝ) * L⁻¹ * ((1 + τ) ^ 14 * Real.exp (-(π * τ))) := by
        have hc2 : c⁻¹ / c = c ^ (-2 : ℝ) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
        calc 104 * K_phi ^ 3 * (Cw * c⁻¹ * (1 + τ) ^ 14 * Real.exp (-(π * τ))) / (c * (L / 2))
            = (104 * K_phi ^ 3 * Cw * 2) * (c⁻¹ / c) * L⁻¹ * ((1 + τ) ^ 14 * Real.exp (-(π * τ))) := by ring
          _ = A_ibp * c ^ (-2 : ℝ) * L⁻¹ * ((1 + τ) ^ 14 * Real.exp (-(π * τ))) := by simp only [A_ibp, hc2]
      refine ⟨?_, ?_⟩
      · have h0 := hbd 0 (by norm_num)
        simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at h0
        exact h0.trans_eq hcoef
      · have h1 := hbd 1 le_rfl
        simp only [iteratedDeriv_one, Nat.cast_one, zpow_neg_one, inv_one, mul_one] at h1
        exact h1.trans_eq hcoef
  -- VdC1 on `ibpStep phi ampσ` over `[r, s1]`
  have h1_cd : ContDiffOn ℝ 1 (ibpStep phi ampσ) U :=
    contDiffOn_ibpStep (n := 1) hU (hphi_cd4.of_le (by norm_num)) hh_cd2 hphi_ne
  have h1_cont : ContinuousOn (ibpStep phi ampσ) (Icc r s1) := h1_cd.continuousOn.mono hsub
  have hd1 : ∀ x ∈ Icc r s1, HasDerivAt (ibpStep phi ampσ) (deriv (ibpStep phi ampσ) x) x := fun x hx =>
    ((h1_cd.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by norm_num)).hasDerivAt
  have hderiv1_cont : ContinuousOn (deriv (ibpStep phi ampσ)) (Icc r s1) := by
    have hc0' : ContinuousOn (deriv (ibpStep phi ampσ)) U :=
      (h1_cd.derivWithin hU.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
        fun t ht => (derivWithin_of_isOpen hU ht).symm
    exact hc0'.mono hsub
  have hr12_pow : r ^ (-(1 / 2 : ℝ)) = (c * L) ^ (1 / 2 : ℝ) := by
    dsimp [r]; rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  have hM1_bd : ∀ x ∈ Icc r s1, ‖ibpStep phi ampσ x‖ ≤ M_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have hc_le : c ^ (-2 : ℝ) * L⁻¹ * r ^ (-(1 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
      rw [hr12_pow, Real.mul_rpow hcpos.le hLpos.le]
      have hca : c ^ (-2 : ℝ) * c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hcpos]; congr 1; norm_num
      have hLa : L⁻¹ * L ^ (1 / 2 : ℝ) = L ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one L, ← Real.rpow_add hLpos]; congr 1; norm_num
      calc c ^ (-2 : ℝ) * L⁻¹ * (c ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ))
          = (c ^ (-2 : ℝ) * c ^ (1 / 2 : ℝ)) * (L⁻¹ * L ^ (1 / 2 : ℝ)) := by ring
        _ = c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by rw [hca, hLa]
    have hc_le2 : c ^ (-2 : ℝ) * L⁻¹ ≤ c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
      have h1 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      have h2 : L⁻¹ ≤ L ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one L]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    rcases le_or_gt x (1 / 16) with hx16 | hx16
    · have hxpos : 0 < x := lt_of_lt_of_le hr_pos hx.1
      have hxr : x ^ (-(1 / 2 : ℝ)) ≤ r ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hxpos.le, Real.rpow_neg hr_pos.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hr_pos _)
          (Real.rpow_le_rpow hr_pos.le hx.1 (by norm_num))
      have h0 := (hibp_pt x hx).1 hx16 |>.1
      have hM1_ge : A_ibp ≤ M_1 := by
        simp only [M_1]
        have : (1 : ℝ) ≤ 1 + 3 * (Nat.factorial 15 : ℝ) := by linarith [show 0 ≤ (Nat.factorial 15 : ℝ) by positivity]
        calc A_ibp = A_ibp * 1 := (mul_one _).symm
          _ ≤ A_ibp * (1 + 3 * (Nat.factorial 15 : ℝ)) := mul_le_mul_of_nonneg_left this (by positivity)
      calc ‖ibpStep phi ampσ x‖ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * x ^ (-(1 / 2 : ℝ)) := h0
        _ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * r ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = A_ibp * (c ^ (-2 : ℝ) * L⁻¹ * r ^ (-(1 / 2 : ℝ))) := by ring
        _ = A_ibp * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) := by rw [hc_le]
        _ ≤ M_1 * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = M_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by ring
    · have h0 := (hibp_pt x hx).2 hx16.le |>.1
      have hpe := poly14_exp_le (lt_of_lt_of_le hr_pos hx.1).le
      have hM1_ge : A_ibp * (3 * (Nat.factorial 15 : ℝ)) ≤ M_1 := by
        simp only [M_1]
        linarith [show 0 ≤ A_ibp by positivity]
      calc ‖ibpStep phi ampσ x‖ ≤ A_ibp * (c ^ (-2 : ℝ) * L⁻¹) * ((1 + x) ^ 14 * Real.exp (-(π * x))) := by
            linarith [show A_ibp * c ^ (-2 : ℝ) * L⁻¹ * ((1 + x) ^ 14 * Real.exp (-(π * x))) =
              A_ibp * (c ^ (-2 : ℝ) * L⁻¹) * ((1 + x) ^ 14 * Real.exp (-(π * x))) by ring]
        _ ≤ A_ibp * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) * (3 * (Nat.factorial 15 : ℝ)) := by gcongr
        _ = (A_ibp * (3 * (Nat.factorial 15 : ℝ))) * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ M_1 * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = M_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by ring
  have hV1_bd : ∫ x in Icc r s1, ‖deriv (ibpStep phi ampσ) x‖ ≤
      V_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
    set g_n : ℝ → ℝ := (Icc r (1 / 16)).indicator (fun x : ℝ => x ^ (-(3 / 2 : ℝ)))
    set g_f : ℝ → ℝ := fun x => (1 + |x|) ^ 14 * Real.exp (-(π * |x|))
    have hg_n_int : Integrable g_n := by
      have hcont_rpow : ContinuousOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (Icc r (1 / 16)) :=
        continuousOn_id.rpow_const fun x hx => Or.inl (lt_of_lt_of_le hr_pos hx.1).ne'
      exact hcont_rpow.integrableOn_Icc.integrable_indicator measurableSet_Icc
    have hg_n_eval : ∫ x : ℝ, g_n x ≤ 2 * (c * L) ^ (1 / 2 : ℝ) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hr16]
      have hnz : ∀ x ∈ uIcc r (1 / 16 : ℝ), x ≠ 0 := fun x hx =>
        (lt_of_lt_of_le hr_pos (uIcc_of_le hr16 ▸ hx).1).ne'
      rw [integral_rpow (Or.inr ⟨by norm_num, fun hm => hnz 0 hm rfl⟩)]
      have h_pow_r : r ^ (-(3 / 2 : ℝ) + 1) = (c * L) ^ (1 / 2 : ℝ) := by
        rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num]; exact hr12_pow
      have h_pow_16 : 0 ≤ (1 / 16 : ℝ) ^ (-(3 / 2 : ℝ) + 1) := by positivity
      rw [h_pow_r]; norm_num at h_pow_16 ⊢
      linarith [h_pow_16]
    have hdom_int : Integrable (fun x : ℝ => A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (g_n x + g_f x)) :=
      (hg_n_int.add hI14_int).const_mul _
    have hpt_d : ∀ x ∈ Icc r s1, ‖deriv (ibpStep phi ampσ) x‖ ≤
        A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (g_n x + g_f x) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hr_pos hx.1
      have hgf0 : 0 ≤ g_f x := by positivity
      have hgn0 : 0 ≤ g_n x := Set.indicator_nonneg (fun _ hy => Real.rpow_nonneg (lt_of_lt_of_le hr_pos (mem_Icc.mp hy).1).le _) x
      rcases le_or_gt x (1 / 16) with hx16 | hx16
      · have hd1 := (hibp_pt x hx).1 hx16 |>.2
        have hmem : x ∈ Icc r (1 / 16) := ⟨hx.1, hx16⟩
        have hgn : g_n x = x ^ (-(3 / 2 : ℝ)) := Set.indicator_of_mem hmem _
        calc ‖deriv (ibpStep phi ampσ) x‖ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * g_n x := by rw [hgn]; exact hd1
          _ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (g_n x + g_f x) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hgf0) (by positivity)
      · have hd1 := (hibp_pt x hx).2 hx16.le |>.2
        have hgf_eq : g_f x = (1 + x) ^ 14 * Real.exp (-(π * x)) := by
          simp only [g_f, abs_of_pos hxpos]
        calc ‖deriv (ibpStep phi ampσ) x‖ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * g_f x := by
              rw [hgf_eq]; exact hd1
          _ ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (g_n x + g_f x) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hgn0) (by positivity)
    have hint_lhs : IntegrableOn (fun x => ‖deriv (ibpStep phi ampσ) x‖) (Icc r s1) :=
      hderiv1_cont.norm.integrableOn_Icc
    have hbound1 := setIntegral_mono_on hint_lhs hdom_int.integrableOn measurableSet_Icc hpt_d
    have hbound2 : ∫ x in Icc r s1, A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (g_n x + g_f x) ≤
        ∫ x : ℝ, A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (g_n x + g_f x) :=
      setIntegral_le_integral hdom_int (Eventually.of_forall fun x => by
        have hgf0 : 0 ≤ g_f x := by positivity
        have hgn0 : 0 ≤ g_n x := Set.indicator_nonneg (fun _ hy => Real.rpow_nonneg (lt_of_lt_of_le hr_pos (mem_Icc.mp hy).1).le _) x
        positivity)
    have hfull_eq : ∫ x : ℝ, A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (g_n x + g_f x) ≤
        A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (2 * (c * L) ^ (1 / 2 : ℝ) + I14) := by
      rw [integral_const_mul, integral_add hg_n_int hI14_int]
      have hI14_eq : ∫ x : ℝ, g_f x = I14 := rfl
      rw [hI14_eq]
      exact mul_le_mul_of_nonneg_left (add_le_add hg_n_eval le_rfl) (by positivity)
    have hpow_1 : (c * L) ^ (1 / 2 : ℝ) = c ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) :=
      Real.mul_rpow hcpos.le hLpos.le
    have hpow_ge : (1 : ℝ) ≤ (c * L) ^ (1 / 2 : ℝ) := by
      rw [hpow_1]
      exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hc1 (by norm_num))
        (Real.one_le_rpow (by linarith) (by norm_num))
    have hc_L_prod : c ^ (-2 : ℝ) * L⁻¹ * (c * L) ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
      rw [hpow_1]
      have hca : c ^ (-2 : ℝ) * c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hcpos]; congr 1; norm_num
      have hLa : L⁻¹ * L ^ (1 / 2 : ℝ) = L ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one L, ← Real.rpow_add hLpos]; congr 1; norm_num
      calc c ^ (-2 : ℝ) * L⁻¹ * (c ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ))
          = (c ^ (-2 : ℝ) * c ^ (1 / 2 : ℝ)) * (L⁻¹ * L ^ (1 / 2 : ℝ)) := by ring
        _ = c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by rw [hca, hLa]
    refine (hbound1.trans hbound2).trans (hfull_eq.trans ?_)
    calc A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (2 * (c * L) ^ (1 / 2 : ℝ) + I14)
        ≤ A_ibp * c ^ (-2 : ℝ) * L⁻¹ * (2 * (c * L) ^ (1 / 2 : ℝ) + I14 * (c * L) ^ (1 / 2 : ℝ)) := by
          gcongr
          exact le_mul_of_one_le_right hI14_nn hpow_ge
      _ = (A_ibp * (2 + I14)) * (c ^ (-2 : ℝ) * L⁻¹ * (c * L) ^ (1 / 2 : ℝ)) := by ring
      _ = V_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by rw [hc_L_prod]; simp only [V_1]; ring
  have hvdc_rem : ‖∫ x in r..s1, Complex.exp (Complex.I * (phi x : ℂ)) * ibpStep phi ampσ x‖ ≤
      6 * (M_1 + V_1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have heq : (fun x => Complex.exp (Complex.I * (phi x : ℂ)) * ibpStep phi ampσ x) =
        fun x => ibpStep phi ampσ x * Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (phi x : ℂ)) := by
      ext x; rw [mul_comm]; simp
    rw [heq]
    have hphi_vdc : ∀ y ∈ Icc r s1, HasDerivAt phi (deriv phi y) y := fun y hy =>
      ((hphi_cd4.contDiffAt (hU.mem_nhds (hsub hy))).differentiableAt (by norm_num)).hasDerivAt
    have hphi'_cont : ContinuousOn (deriv phi) (Icc r s1) := by
      have heq_d : deriv phi = fun τ => c * σ * edgePhiDeriv L τ := funext hphi_deriv
      rw [heq_d]
      exact (continuous_const.mul (contDiff_edgePhiDeriv L).continuous).continuousOn
    have hphi'_mono : MonotoneOn (deriv phi) (Icc r s1) ∨ AntitoneOn (deriv phi) (Icc r s1) := by
      have heq_d : deriv phi = fun τ => (c * σ) * edgePhiDeriv L τ := funext hphi_deriv
      rw [heq_d]
      rcases hσ with rfl | rfl
      · right
        intro x hx y hy hxy
        exact mul_le_mul_of_nonneg_left
          ((edgePhiDeriv_antitoneOn_nonneg L) (le_trans hr_pos.le hx.1) (le_trans hr_pos.le hy.1) hxy)
          (by positivity)
      · left
        intro x hx y hy hxy
        have h_ant := (edgePhiDeriv_antitoneOn_nonneg L) (le_trans hr_pos.le hx.1) (le_trans hr_pos.le hy.1) hxy
        have : c * -1 * edgePhiDeriv L x = -(c * edgePhiDeriv L x) := by ring
        have h1 : c * -1 * edgePhiDeriv L y = -(c * edgePhiDeriv L y) := by ring
        dsimp only; rw [this, h1]
        exact neg_le_neg (mul_le_mul_of_nonneg_left h_ant hcpos.le)
    have hphi'_lb : ∀ y ∈ Icc r s1, c * (L / 2) ≤ |deriv phi y| := fun y hy =>
      hphi_lb y (le_trans hr_pos.le hy.1) hy.2
    have hci : IntervalIntegrable (deriv (ibpStep phi ampσ)) volume r s1 :=
      hderiv1_cont.intervalIntegrable_of_Icc hrs1
    have hev := eVariationOn_le_integral_norm_deriv hrs1 hd1 hci
    have hX : ∫ t in r..s1, ‖deriv (ibpStep phi ampσ) t‖ ≤ V_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_of_le hrs1, ← integral_Icc_eq_integral_Ioc]
      exact hV1_bd
    have hbv : BoundedVariationOn (ibpStep phi ampσ) (Icc r s1) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hev
    have hvar : (eVariationOn (ibpStep phi ampσ) (Icc r s1)).toReal ≤ V_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hev.trans (ENNReal.ofReal_le_ofReal hX))
    have hvdc := van_der_corput_first hrs1 zero_lt_one (by positivity : 0 < c * (L / 2))
      hphi_vdc hphi'_cont hphi'_mono hphi'_lb h1_cont hbv hM1_bd
    have hden_pos : 0 < 1 * (c * (L / 2)) := by positivity
    have h1 : 3 * (M_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) +
          (eVariationOn (ibpStep phi ampσ) (Icc r s1)).toReal) / (1 * (c * (L / 2))) ≤
        6 * (M_1 + V_1) * c ^ (-(5 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
      have hc_eq : c ^ (-(3 / 2 : ℝ)) / c = c ^ (-(5 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
      have hL_eq : L ^ (-(1 / 2 : ℝ)) / L = L ^ (-(3 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one L, ← Real.rpow_add hLpos]; congr 1; norm_num
      calc 3 * (M_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) +
              (eVariationOn (ibpStep phi ampσ) (Icc r s1)).toReal) / (1 * (c * (L / 2)))
          ≤ 3 * (M_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) +
              V_1 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) / (1 * (c * (L / 2))) := by gcongr
        _ = 6 * (M_1 + V_1) * (c ^ (-(3 / 2 : ℝ)) / c) * (L ^ (-(1 / 2 : ℝ)) / L) := by ring
        _ = 6 * (M_1 + V_1) * c ^ (-(5 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by rw [hc_eq, hL_eq]
    have hc_le : c ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    exact hvdc.trans (h1.trans (by gcongr))
  rw [hibp]
  calc ‖Complex.exp (Complex.I * (phi s1 : ℂ)) * (ampσ s1 / (Complex.I * ((deriv phi s1 : ℝ) : ℂ))) -
          Complex.exp (Complex.I * (phi r : ℂ)) * (ampσ r / (Complex.I * ((deriv phi r : ℝ) : ℂ))) +
          Complex.I * ∫ x in r..s1, Complex.exp (Complex.I * (phi x : ℂ)) * ibpStep phi ampσ x‖
      ≤ ‖Complex.exp (Complex.I * (phi s1 : ℂ)) * (ampσ s1 / (Complex.I * ((deriv phi s1 : ℝ) : ℂ)))‖ +
          ‖Complex.exp (Complex.I * (phi r : ℂ)) * (ampσ r / (Complex.I * ((deriv phi r : ℝ) : ℂ)))‖ +
          ‖Complex.I * ∫ x in r..s1, Complex.exp (Complex.I * (phi x : ℂ)) * ibpStep phi ampσ x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * Cw * (3 * (Nat.factorial 15 : ℝ) * 48) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) +
          2 * Cw * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) +
          6 * (M_1 + V_1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
        refine add_le_add (add_le_add hbd_s1 hbd_r) ?_
        rw [norm_mul, Complex.norm_I, one_mul]
        exact hvdc_rem
    _ = C * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by simp only [C, C_bd]; ring

/-- info: 'FormalResearch.SignUncertainty.warp_ibp1_vdc1_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warp_ibp1_vdc1_bound

end FormalResearch.SignUncertainty

