/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.CtMDeriv
public import FormalResearch.SignUncertainty.StripAdmissTail
public import FormalResearch.Analysis.VanDerCorput
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Three-fold integration by parts and `edgePhi` bounds for `fct:cusp-edge` (F2a)

Support module for `FctCuspEdge.lean` (`CFT/sign_uncertainty/paper/constant_terms_five.tex`,
Lemma FCT.7a `fct:cusp-edge`, lines 1025–1092).

Contents:
* `contDiff_edgePhi`: `edgePhi L` is `C^∞` on `ℝ`, with global derivative bounds
  `edgePhi_iteratedDeriv_bound` (`|Φ^{(k)}(τ; L)| ≤ C_k (1 + |τ|)^{-(k-1)}` for `k ≥ 2`).
* Elementary quantitative bounds for `hankelEdgeM`, `hankelEdgeM'`, and `tau0 L` in both
  the small-`L` (`0 < L ≤ 1`) and large-`L` (`1 ≤ L`) regimes.
* `ibp3_interval` and `ibp3_Ioi`: three-fold non-stationary integration by parts for
  `∫ exp (I * φ x) * h x` under symbol bounds `|φ^{(j+1)}| ≤ K w^{-j} |φ'|` (`j = 1, 2, 3`)
  and `‖h^{(j)}‖ ≤ B w^{-j}` (`j = 0, 1, 2, 3`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctCuspEdge

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtMDeriv

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Smoothness and global derivative bounds for `edgePhi` and `hankelEdgeM` -/

lemma edgePhiDeriv2_eq_neg_g0 {τ : ℝ} (hτ : τ ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4)) :
    edgePhiDeriv2 τ = -CtMDeriv.g0 τ := by
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · have hpos' : -τ ∈ Ioo (0 : ℝ) (1 / 4) := ⟨neg_pos.mpr hneg, by linarith [hτ.1]⟩
    have hm := CtMDeriv.mPrime_eq_g0 hpos'
    rw [CtOuter.mPrime_eq_hankelEdgeM' hpos'.1] at hm
    have hodd_g0 : CtMDeriv.g0 (-τ) = -CtMDeriv.g0 τ := by
      unfold CtMDeriv.g0; simp
    have hodd_d2 : edgePhiDeriv2 (-τ) = -edgePhiDeriv2 τ := by
      unfold edgePhiDeriv2
      have hne : τ ≠ 0 := hneg.ne
      have hne' : -τ ≠ 0 := neg_ne_zero.mpr hne
      simp [Real.sinh_neg]; ring
    have heq : -edgePhiDeriv2 (-τ) = CtMDeriv.g0 (-τ) := by
      simpa [hankelEdgeM'] using hm
    linarith
  · simp [edgePhiDeriv2, CtMDeriv.g0]
  · have hm := CtMDeriv.mPrime_eq_g0 ⟨hpos, hτ.2⟩
    rw [CtOuter.mPrime_eq_hankelEdgeM' hpos] at hm
    have heq : -edgePhiDeriv2 τ = CtMDeriv.g0 τ := by
      simpa [hankelEdgeM'] using hm
    linarith

lemma edgePhiDeriv2_odd (τ : ℝ) : edgePhiDeriv2 (-τ) = -edgePhiDeriv2 τ := by
  by_cases hτ : τ = 0
  · subst hτ; simp [edgePhiDeriv2]
  · unfold edgePhiDeriv2
    simp [Real.sinh_neg]; ring

lemma contDiff_edgePhiDeriv2 : ContDiff ℝ ∞' edgePhiDeriv2 := by
  rw [contDiff_iff_contDiffAt]
  intro τ
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · have h1 : ContDiffOn ℝ ∞' (fun t : ℝ => CtOuter.mPrime (-t)) (Iio 0) := by
      have hmap : MapsTo (fun t : ℝ => -t) (Iio (0 : ℝ)) (Ioi (0 : ℝ)) := fun t ht => neg_pos.mpr ht
      exact CtMDeriv.contDiffOn_mPrime.comp contDiff_neg.contDiffOn hmap
    have h2 : ContDiffAt ℝ ∞' (fun t : ℝ => CtOuter.mPrime (-t)) τ :=
      h1.contDiffAt (isOpen_Iio.mem_nhds hneg)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hneg] with t ht
    have ht' : 0 < -t := neg_pos.mpr ht
    have hm := CtOuter.mPrime_eq_hankelEdgeM' ht'
    have heq : -edgePhiDeriv2 (-t) = CtOuter.mPrime (-t) := by simpa [hankelEdgeM'] using hm.symm
    have hodd := edgePhiDeriv2_odd t
    linarith
  · have h2 : ContDiffAt ℝ ∞' (fun t : ℝ => -CtMDeriv.g0 t) 0 :=
      CtMDeriv.contDiffOn_g0.neg.contDiffAt (isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4) by norm_num)]
      with t ht using edgePhiDeriv2_eq_neg_g0 ht
  · have h2 : ContDiffAt ℝ ∞' (fun t : ℝ => -CtOuter.mPrime t) τ :=
      CtMDeriv.contDiffOn_mPrime.neg.contDiffAt (isOpen_Ioi.mem_nhds hpos)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hpos] with t ht
    have hm := CtOuter.mPrime_eq_hankelEdgeM' ht
    have heq : -edgePhiDeriv2 t = CtOuter.mPrime t := by simpa [hankelEdgeM'] using hm.symm
    linarith

lemma contDiff_edgePhiDeriv (L : ℝ) : ContDiff ℝ ∞' (edgePhiDeriv L) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun τ => (hasDerivAt_edgePhiDeriv L τ).differentiableAt, ?_⟩
  have heq : deriv (edgePhiDeriv L) = edgePhiDeriv2 :=
    funext fun τ => (hasDerivAt_edgePhiDeriv L τ).deriv
  rw [heq]
  exact contDiff_edgePhiDeriv2

lemma contDiff_edgePhi (L : ℝ) : ContDiff ℝ ∞' (edgePhi L) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun τ => (hasDerivAt_edgePhi L τ).differentiableAt, ?_⟩
  have heq : deriv (edgePhi L) = edgePhiDeriv L :=
    funext fun τ => (hasDerivAt_edgePhi L τ).deriv
  rw [heq]
  exact contDiff_edgePhiDeriv L

lemma edgePhi_iteratedDeriv_ge_two (L : ℝ) (k : ℕ) (hk : 2 ≤ k) (τ : ℝ) :
    iteratedDeriv k (edgePhi L) τ = iteratedDeriv (k - 2) edgePhiDeriv2 τ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [iteratedDeriv_succ', show deriv (edgePhi L) = edgePhiDeriv L from
    funext fun t => (hasDerivAt_edgePhi L t).deriv]
  rw [iteratedDeriv_succ', show deriv (edgePhiDeriv L) = edgePhiDeriv2 from
    funext fun t => (hasDerivAt_edgePhiDeriv L t).deriv]

lemma edgePhi_iteratedDeriv_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L τ : ℝ,
      |iteratedDeriv k (edgePhi L) τ| ≤ C / (1 + |τ|) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨C, hC⟩ := CtMDeriv.mPrime_iter_bound j
  have hC0 : 0 ≤ C := by
    have := hC 1 one_pos
    have hpos : 0 < (1 + (1 : ℝ)) ^ (j + 1) := by positivity
    have hnn : 0 ≤ C / (1 + (1 : ℝ)) ^ (j + 1) := le_trans (abs_nonneg _) this
    by_contra hneg
    push Not at hneg
    have : C / (1 + (1 : ℝ)) ^ (j + 1) < 0 := div_neg_of_neg_of_pos hneg hpos
    linarith
  refine ⟨C, hC0, fun L τ => ?_⟩
  rw [edgePhi_iteratedDeriv_ge_two L (j + 2) (by omega) τ]
  simp only [show j + 2 - 2 = j by omega, show j + 2 - 1 = j + 1 by omega]
  have hpos_bound : ∀ t : ℝ, 0 < t → |iteratedDeriv j edgePhiDeriv2 t| ≤ C / (1 + t) ^ (j + 1) := by
    intro t ht
    have hev : edgePhiDeriv2 =ᶠ[𝓝 t] -CtOuter.mPrime := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      have hm := CtOuter.mPrime_eq_hankelEdgeM' hs
      have heq : -edgePhiDeriv2 s = CtOuter.mPrime s := by simpa [hankelEdgeM'] using hm.symm
      show edgePhiDeriv2 s = -CtOuter.mPrime s
      linarith
    rw [hev.iteratedDeriv_eq j, iteratedDeriv_neg, abs_neg]
    exact hC t ht
  have hne_bound : ∀ t : ℝ, t ≠ 0 → |iteratedDeriv j edgePhiDeriv2 t| ≤ C / (1 + |t|) ^ (j + 1) := by
    intro t ht
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have h1 := hpos_bound (-t) (neg_pos.mpr hneg)
      have hev : (fun s => edgePhiDeriv2 (-s)) = -edgePhiDeriv2 :=
        funext edgePhiDeriv2_odd
      have hcomp := iteratedDeriv_comp_neg j edgePhiDeriv2 t
      rw [hev, iteratedDeriv_neg] at hcomp
      have habs : |iteratedDeriv j edgePhiDeriv2 (-t)| = |iteratedDeriv j edgePhiDeriv2 t| := by
        have h2 : (-1 : ℝ) ^ j * iteratedDeriv j edgePhiDeriv2 (-t) =
            -iteratedDeriv j edgePhiDeriv2 t := by
          simpa [smul_eq_mul] using hcomp.symm
        have h3 := congr_arg abs h2
        simpa [abs_mul, abs_pow] using h3
      rw [← habs, abs_of_neg hneg]
      exact h1
    · rw [abs_of_pos hpos]; exact hpos_bound t hpos
  have hcont : Continuous (fun t : ℝ => |iteratedDeriv j edgePhiDeriv2 t| - C / (1 + |t|) ^ (j + 1)) := by
    have hcd : Continuous (iteratedDeriv j edgePhiDeriv2) :=
      contDiff_edgePhiDeriv2.continuous_iteratedDeriv j (by exact_mod_cast le_top)
    refine hcd.abs.sub (continuous_const.div ?_ (fun t => by positivity))
    exact (continuous_const.add continuous_abs).pow (j + 1)
  have hS : IsClosed {t : ℝ | |iteratedDeriv j edgePhiDeriv2 t| - C / (1 + |t|) ^ (j + 1) ≤ 0} :=
    isClosed_le hcont continuous_const
  have hsub : ({0}ᶜ : Set ℝ) ⊆ {t : ℝ | |iteratedDeriv j edgePhiDeriv2 t| - C / (1 + |t|) ^ (j + 1) ≤ 0} := by
    intro t ht
    show |iteratedDeriv j edgePhiDeriv2 t| - C / (1 + |t|) ^ (j + 1) ≤ 0
    linarith [hne_bound t ht]
  have hcl : closure ({0}ᶜ : Set ℝ) = Set.univ :=
    (dense_compl_singleton (0 : ℝ)).closure_eq
  have hmem : τ ∈ {t : ℝ | |iteratedDeriv j edgePhiDeriv2 t| - C / (1 + |t|) ^ (j + 1) ≤ 0} := by
    have := closure_minimal hsub hS
    rw [hcl] at this
    exact this (mem_univ τ)
  linarith [show |iteratedDeriv j edgePhiDeriv2 τ| - C / (1 + |τ|) ^ (j + 1) ≤ 0 from hmem]

lemma edgePhi_neg (L τ : ℝ) : edgePhi L (-τ) = -edgePhi L τ := by
  have hev : ∀ u : ℝ, edgePhiDeriv L (-u) = edgePhiDeriv L u := by
    intro u
    have h0 : ∀ x : ℝ, HasDerivAt (fun t => edgePhiDeriv L (-t) - edgePhiDeriv L t) 0 x := by
      intro x
      have hd1 : HasDerivAt (fun t => edgePhiDeriv L (-t)) (-edgePhiDeriv2 (-x)) x := by
        simpa [Function.comp_def] using (hasDerivAt_edgePhiDeriv L (-x)).comp x (hasDerivAt_neg x)
      refine (hd1.sub (hasDerivAt_edgePhiDeriv L x)).congr_deriv ?_
      rw [edgePhiDeriv2_odd]; ring
    have hconst := is_const_of_deriv_eq_zero (fun x => (h0 x).differentiableAt)
      (fun x => (h0 x).deriv) u 0
    simp at hconst
    linarith
  have h0 : ∀ x : ℝ, HasDerivAt (fun t => edgePhi L (-t) + edgePhi L t) 0 x := by
    intro x
    have hd1 : HasDerivAt (fun t => edgePhi L (-t)) (-edgePhiDeriv L (-x)) x := by
      simpa [Function.comp_def] using (hasDerivAt_edgePhi L (-x)).comp x (hasDerivAt_neg x)
    refine (hd1.add (hasDerivAt_edgePhi L x)).congr_deriv ?_
    rw [hev]; ring
  have hconst := is_const_of_deriv_eq_zero (fun x => (h0 x).differentiableAt)
    (fun x => (h0 x).deriv) τ 0
  have hzero : edgePhi L 0 = 0 := by simp [edgePhi]
  simp [hzero] at hconst
  linarith

/-! ### Elementary quantitative bounds for `hankelEdgeM`, `hankelEdgeM'`, and `tau0` -/

lemma hankelEdgeM_even (τ : ℝ) : hankelEdgeM (-τ) = hankelEdgeM τ := by
  unfold hankelEdgeM ceEll
  have h1 : π * -τ / 2 = -(π * τ / 2) := by ring
  rw [h1, Real.tanh_neg, neg_div_neg_eq]

lemma hankelEdgeM_le_sq (τ : ℝ) : hankelEdgeM τ ≤ π ^ 2 / 12 * τ ^ 2 := by
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · rw [← hankelEdgeM_even]
    have h := ceEll_lt_sq_div_three (show 0 < π * (-τ) / 2 by nlinarith [Real.pi_pos])
    unfold hankelEdgeM
    linarith [show (π * -τ / 2) ^ 2 / 3 = π ^ 2 / 12 * τ ^ 2 by ring]
  · simp [hankelEdgeM_zero]
  · have h := ceEll_lt_sq_div_three (show 0 < π * τ / 2 by positivity)
    unfold hankelEdgeM
    linarith [show (π * τ / 2) ^ 2 / 3 = π ^ 2 / 12 * τ ^ 2 by ring]

lemma hankelEdgeM_ge_log {τ : ℝ} (hτ : 0 < τ) : Real.log (π * τ / 2) < hankelEdgeM τ := by
  unfold hankelEdgeM ceEll
  have hx : 0 < π * τ / 2 := by positivity
  have ht0 : 0 < Real.tanh (π * τ / 2) := tanh_pos_of_pos hx
  have ht1 : Real.tanh (π * τ / 2) < 1 := Real.tanh_lt_one _
  exact Real.log_lt_log hx ((lt_div_iff₀ ht0).mpr (by nlinarith))

lemma hankelEdgeM_le_log {τ : ℝ} (hτ : 1 / 2 ≤ τ) : hankelEdgeM τ ≤ Real.log (π * τ) := by
  unfold hankelEdgeM ceEll
  have hx : 0 < π * τ / 2 := by nlinarith [Real.pi_pos]
  have ht0 : 0 < Real.tanh (π * τ / 2) := tanh_pos_of_pos hx
  have hx_ge : (1 / 2 : ℝ) ≤ π * τ / 2 := by nlinarith [Real.pi_gt_three]
  have ht_ge : (1 / 2 : ℝ) ≤ Real.tanh (π * τ / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have he : Real.exp (-(π * τ / 2)) = (Real.exp (π * τ / 2))⁻¹ := Real.exp_neg _
    have hE : 0 < Real.exp (π * τ / 2) := Real.exp_pos _
    have hE2 : 3 ≤ Real.exp (π * τ / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have h1 : (3 / 2 : ℝ) ≤ 2 * (π * τ / 2) := by nlinarith [Real.pi_gt_three]
      have h2 := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * (π * τ / 2) by positivity) 3
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
        pow_zero, pow_one, Nat.cast_one, div_one, zero_add] at h2
      nlinarith
    have hden : 0 < (Real.exp (π * τ / 2) + Real.exp (-(π * τ / 2))) / 2 := by positivity
    rw [le_div_iff₀ hden, he]
    field_simp
    nlinarith [sq_nonneg (Real.exp (π * τ / 2))]
  refine Real.log_le_log (div_pos hx ht0) ?_
  rw [div_le_iff₀ ht0]
  nlinarith

lemma hankelEdgeM'_bounds {τ : ℝ} (hτ : 0 < τ) :
    τ / (1 + τ ^ 2) ≤ hankelEdgeM' τ ∧ hankelEdgeM' τ ≤ π ^ 2 / 6 * τ ∧ hankelEdgeM' τ ≤ 1 / τ := by
  have hm := m2_bounds hτ
  have h2 := edgePhiDeriv2_abs_le hτ.ne'
  have hpos : 0 < hankelEdgeM' τ := lt_of_lt_of_le (by positivity) hm.2.1
  have habs : |edgePhiDeriv2 τ| = hankelEdgeM' τ := by
    unfold hankelEdgeM' at hpos ⊢
    rw [abs_of_neg (by linarith)]
  rw [habs] at h2
  rw [abs_of_pos hτ] at h2
  exact ⟨hm.2.1, h2.trans (min_le_left _ _), by simpa [one_div] using h2.trans (min_le_right _ _)⟩

lemma tau0_large_bounds {L : ℝ} (hL : 1 ≤ L) :
    Real.exp L / π ≤ tau0 L ∧ tau0 L ≤ 2 * Real.exp L / π := by
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < tau0 L := tau0_pos hL0
  have hm : hankelEdgeM (tau0 L) = L := ceEll_tau0 hL0
  have hupper : tau0 L ≤ 2 * Real.exp L / π := by
    have hlog := hankelEdgeM_ge_log ht0
    rw [hm] at hlog
    have h1 : π * tau0 L / 2 < Real.exp L := by
      have := Real.exp_lt_exp.mpr hlog
      rwa [Real.exp_log (by positivity)] at this
    rw [le_div_iff₀ Real.pi_pos]
    linarith
  have hge_half : (1 / 2 : ℝ) ≤ tau0 L := by
    by_contra hlt
    push Not at hlt
    have h1 := hankelEdgeM_le_sq (tau0 L)
    rw [hm] at h1
    have hpi : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith
  have hlower : Real.exp L / π ≤ tau0 L := by
    have hlog := hankelEdgeM_le_log hge_half
    rw [hm] at hlog
    have h1 : Real.exp L ≤ π * tau0 L := by
      have := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_log (by positivity)] at this
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  exact ⟨hlower, hupper⟩

lemma hankelEdgeM_diff_ge_of_slope {a b c₀ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hslope : ∀ v ∈ Ioo a b, c₀ ≤ hankelEdgeM' v) :
    c₀ * (b - a) ≤ hankelEdgeM b - hankelEdgeM a := by
  have hcont : ContinuousOn (fun v => hankelEdgeM v - c₀ * v) (Icc a b) :=
    (hankelEdgeM_continuousOn.mono fun x (hx : x ∈ Icc a b) => le_trans ha hx.1).sub
      (continuous_const.mul continuous_id).continuousOn
  have hmono : MonotoneOn (fun v => hankelEdgeM v - c₀ * v) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
      (f' := fun v => hankelEdgeM' v - c₀) (fun v hv => ?_) (fun v hv => ?_)
    · rw [interior_Icc] at hv
      have hv0 : 0 < v := lt_of_le_of_lt ha hv.1
      have hd : HasDerivAt (fun x => hankelEdgeM x - c₀ * x) (hankelEdgeM' v - c₀) v :=
        (hankelEdgeM_hasDerivAt hv0).sub (by simpa using (hasDerivAt_id v).const_mul c₀)
      exact hd.hasDerivWithinAt
    · rw [interior_Icc] at hv
      linarith [hslope v hv]
  have hval := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  linarith

lemma hankelEdgeM_diff_ge_sq {a b c₀ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hslope : ∀ v ∈ Ioo a b, c₀ * v ≤ hankelEdgeM' v) :
    c₀ / 2 * (b ^ 2 - a ^ 2) ≤ hankelEdgeM b - hankelEdgeM a := by
  have hcont : ContinuousOn (fun v => hankelEdgeM v - c₀ / 2 * v ^ 2) (Icc a b) :=
    (hankelEdgeM_continuousOn.mono fun x (hx : x ∈ Icc a b) => le_trans ha hx.1).sub
      (continuous_const.mul (continuous_pow 2)).continuousOn
  have hmono : MonotoneOn (fun v => hankelEdgeM v - c₀ / 2 * v ^ 2) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcont
      (f' := fun v => hankelEdgeM' v - c₀ * v) (fun v hv => ?_) (fun v hv => ?_)
    · rw [interior_Icc] at hv
      have hv0 : 0 < v := lt_of_le_of_lt ha hv.1
      have hd2 : HasDerivAt (fun x : ℝ => c₀ / 2 * x ^ 2) (c₀ * v) v := by
        simpa using ((hasDerivAt_pow 2 v).const_mul (c₀ / 2)).congr_deriv (by ring)
      exact ((hankelEdgeM_hasDerivAt hv0).sub hd2).hasDerivWithinAt
    · rw [interior_Icc] at hv
      linarith [hslope v hv]
  have hval := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  linarith

lemma tau0_small_bounds {L : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1) :
    Real.sqrt L ≤ tau0 L ∧ tau0 L ≤ 4 * Real.sqrt L ∧ tau0 L ≤ 2 := by
  have ht0 : 0 < tau0 L := tau0_pos hL0
  have hm : hankelEdgeM (tau0 L) = L := ceEll_tau0 hL0
  have hlow : Real.sqrt L ≤ tau0 L := by
    have h1 := hankelEdgeM_le_sq (tau0 L)
    rw [hm] at h1
    have hpi : π ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h2 : L ≤ tau0 L ^ 2 := by nlinarith [sq_nonneg (tau0 L)]
    exact (Real.sqrt_le_left ht0.le).mpr h2
  have htau_le_two : tau0 L ≤ 2 := by
    have hlog := hankelEdgeM_ge_log (show (0 : ℝ) < 2 by norm_num)
    have hgt : 1 < hankelEdgeM 2 := by
      have : (1 : ℝ) < Real.log (π * 2 / 2) := by
        rw [show π * 2 / 2 = π by ring, Real.lt_log_iff_exp_lt Real.pi_pos]
        exact lt_trans Real.exp_one_lt_d9 (by linarith [Real.pi_gt_three])
      linarith
    by_contra hcon
    push Not at hcon
    have hmono := hankelEdgeM_strictMonoOn (show (2 : ℝ) ∈ Ici 0 by norm_num)
      (show tau0 L ∈ Ici 0 from ht0.le) hcon
    linarith
  have hhigh : tau0 L ≤ 4 * Real.sqrt L := by
    have hdiff := hankelEdgeM_diff_ge_sq le_rfl ht0.le (c₀ := 1 / 5) fun v hv => by
      have h1 := (hankelEdgeM'_bounds hv.1).1
      have hv2 : v ≤ 2 := hv.2.le.trans htau_le_two
      have hden : 1 + v ^ 2 ≤ 5 := by nlinarith [hv.1]
      have hdiv : v / 5 ≤ v / (1 + v ^ 2) :=
        div_le_div_of_nonneg_left hv.1.le (by positivity) hden
      linarith
    rw [hm, hankelEdgeM_zero] at hdiff
    have hsq : tau0 L ^ 2 ≤ 16 * L := by nlinarith
    have hrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq ht0.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
      show Real.sqrt 16 = 4 by norm_num] at hrt
    exact hrt
  exact ⟨hlow, hhigh, htau_le_two⟩

lemma hankelEdgeM_diff_small_inner {L v : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hv0 : 0 ≤ v) (hv : v ≤ 3 / 4 * tau0 L) :
    1 / 32 * L ≤ L - hankelEdgeM v := by
  have ⟨hlow, _, hle2⟩ := tau0_small_bounds hL0 hL1
  have ht0 : 0 < tau0 L := tau0_pos hL0
  have hm : hankelEdgeM (tau0 L) = L := ceEll_tau0 hL0
  have hmono : hankelEdgeM v ≤ hankelEdgeM (3 / 4 * tau0 L) :=
    hankelEdgeM_strictMonoOn.monotoneOn hv0 (mem_Ici.mpr (by positivity)) hv
  have hdiff := hankelEdgeM_diff_ge_sq (a := 3 / 4 * tau0 L) (b := tau0 L) (c₀ := 1 / 5)
    (by positivity) (by linarith) fun x hx => by
    have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx.1
    have h1 := (hankelEdgeM'_bounds hx0).1
    have hx2 : x ≤ 2 := hx.2.le.trans hle2
    have hden : 1 + x ^ 2 ≤ 5 := by nlinarith
    have hdiv : x / 5 ≤ x / (1 + x ^ 2) :=
      div_le_div_of_nonneg_left hx0.le (by positivity) hden
    linarith
  rw [hm] at hdiff
  have hsq : L ≤ tau0 L ^ 2 := by
    have := Real.sq_sqrt hL0.le
    nlinarith [hlow, Real.sqrt_nonneg L]
  nlinarith

lemma hankelEdgeM_diff_small_outer {L v : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hv : 3 / 2 * tau0 L ≤ v) :
    (v ≤ 4 → 1 / 64 * v ^ 2 ≤ hankelEdgeM v - L) ∧
    (4 ≤ v → 1 / 2 ≤ hankelEdgeM v - L) ∧
    1 / 32 * L ≤ hankelEdgeM v - L := by
  have ⟨hlow, _, hle2⟩ := tau0_small_bounds hL0 hL1
  have ht0 : 0 < tau0 L := tau0_pos hL0
  have hm : hankelEdgeM (tau0 L) = L := ceEll_tau0 hL0
  have hle4 : v ≤ 4 → 1 / 64 * v ^ 2 ≤ hankelEdgeM v - L := by
    intro hv4
    have hdiff := hankelEdgeM_diff_ge_sq (a := tau0 L) (b := v) (c₀ := 1 / 17)
      ht0.le (by linarith) fun x hx => by
      have hx0 : 0 < x := lt_trans ht0 hx.1
      have h1 := (hankelEdgeM'_bounds hx0).1
      have hx4 : x ≤ 4 := hx.2.le.trans hv4
      have hden : 1 + x ^ 2 ≤ 17 := by nlinarith
      have hdiv : x / 17 ≤ x / (1 + x ^ 2) :=
        div_le_div_of_nonneg_left hx0.le (by positivity) hden
      linarith
    rw [hm] at hdiff
    have h1 : 5 / 9 * v ^ 2 ≤ v ^ 2 - tau0 L ^ 2 := by nlinarith
    nlinarith
  have hge4 : 4 ≤ v → 1 / 2 ≤ hankelEdgeM v - L := by
    intro hv4
    have hlog := hankelEdgeM_ge_log (show (0 : ℝ) < 4 by norm_num)
    have h4 : (3 / 2 : ℝ) < hankelEdgeM 4 := by
      have : (3 / 2 : ℝ) < Real.log (π * 4 / 2) := by
        rw [show π * 4 / 2 = 2 * π by ring, Real.lt_log_iff_exp_lt (by positivity)]
        have hexp : Real.exp (3 / 2 : ℝ) < 5 := by
          have h1 : Real.exp (3 / 2 : ℝ) = Real.exp 1 * Real.sqrt (Real.exp 1) := by
            rw [← Real.exp_half, ← Real.exp_add]; congr 1; norm_num
          have h2 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
          have h3 : Real.sqrt (Real.exp 1) < 1.7 := by
            rw [Real.sqrt_lt' (by norm_num)]
            linarith
          rw [h1]; nlinarith [Real.exp_pos 1]
        linarith [Real.pi_gt_three]
      linarith
    have hmono : hankelEdgeM 4 ≤ hankelEdgeM v :=
      hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.mpr (by norm_num)) (mem_Ici.mpr (by linarith)) hv4
    linarith
  refine ⟨hle4, hge4, ?_⟩
  rcases le_or_gt v 4 with hv4 | hv4
  · have h1 := hle4 hv4
    have hsq : L ≤ tau0 L ^ 2 := by
      have := Real.sq_sqrt hL0.le
      nlinarith [hlow, Real.sqrt_nonneg L]
    nlinarith
  · linarith [hge4 hv4.le]

lemma hankelEdgeM_diff_large_inner {L v : ℝ} (hL : 1 ≤ L)
    (hv0 : 0 ≤ v) (hv : v ≤ 3 / 4 * tau0 L) :
    1 / 32 ≤ L - hankelEdgeM v := by
  have ⟨hlo, _⟩ := tau0_large_bounds hL
  have ht0 : 0 < tau0 L := tau0_pos (by linarith)
  have ht_ge : (1 / 2 : ℝ) ≤ tau0 L := by
    have hexp : (2 : ℝ) ≤ Real.exp L := by
      have := Real.add_one_le_exp L; linarith
    have hpi : π < 4 := lt_trans Real.pi_lt_d2 (by norm_num)
    have : 2 / 4 ≤ Real.exp L / π := div_le_div₀ (by positivity) hexp Real.pi_pos hpi.le
    linarith
  have hm : hankelEdgeM (tau0 L) = L := ceEll_tau0 (by linarith)
  have hmono : hankelEdgeM v ≤ hankelEdgeM (3 / 4 * tau0 L) :=
    hankelEdgeM_strictMonoOn.monotoneOn hv0 (mem_Ici.mpr (by positivity)) hv
  have hdiff := hankelEdgeM_diff_ge_of_slope (a := 3 / 4 * tau0 L) (b := tau0 L)
    (c₀ := 1 / (8 * tau0 L)) (by positivity) (by linarith) fun x hx => by
    have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx.1
    have h1 := (hankelEdgeM'_bounds hx0).1
    have hden : 1 + x ^ 2 ≤ 8 * tau0 L * x := by
      have hx1 : 3 / 4 * tau0 L ≤ x := hx.1.le
      have hx2 : x ≤ tau0 L := hx.2.le
      nlinarith [ht_ge]
    have hdiv : 1 / (8 * tau0 L) ≤ x / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact hdiv.trans h1
  rw [hm] at hdiff
  have hcancel : 1 / (8 * tau0 L) * (tau0 L - 3 / 4 * tau0 L) = 1 / 32 := by
    field_simp [ht0.ne']; ring
  linarith

lemma hankelEdgeM_diff_large_outer {L v : ℝ} (hL : 1 ≤ L)
    (hv : 3 / 2 * tau0 L ≤ v) :
    1 / 12 ≤ hankelEdgeM v - L := by
  have ⟨hlo, _⟩ := tau0_large_bounds hL
  have ht0 : 0 < tau0 L := tau0_pos (by linarith)
  have ht_ge : (1 / 2 : ℝ) ≤ tau0 L := by
    have hexp : (2 : ℝ) ≤ Real.exp L := by
      have := Real.add_one_le_exp L; linarith
    have hpi : π < 4 := lt_trans Real.pi_lt_d2 (by norm_num)
    have : 2 / 4 ≤ Real.exp L / π := div_le_div₀ (by positivity) hexp Real.pi_pos hpi.le
    linarith
  have hm : hankelEdgeM (tau0 L) = L := ceEll_tau0 (by linarith)
  have hmono : hankelEdgeM (3 / 2 * tau0 L) ≤ hankelEdgeM v :=
    hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (by linarith)) hv
  have hdiff := hankelEdgeM_diff_ge_of_slope (a := tau0 L) (b := 3 / 2 * tau0 L)
    (c₀ := 1 / (6 * tau0 L)) ht0.le (by linarith) fun x hx => by
    have hx0 : 0 < x := lt_trans ht0 hx.1
    have h1 := (hankelEdgeM'_bounds hx0).1
    have hx1 : tau0 L ≤ x := hx.1.le
    have hx2 : x ≤ 3 / 2 * tau0 L := hx.2.le
    have hden : 1 + x ^ 2 ≤ 6 * tau0 L * x := by nlinarith [ht_ge]
    have hdiv : 1 / (6 * tau0 L) ≤ x / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact hdiv.trans h1
  rw [hm] at hdiff
  have hcancel : 1 / (6 * tau0 L) * (3 / 2 * tau0 L - tau0 L) = 1 / 12 := by
    field_simp [ht0.ne']; ring
  linarith

/-! ### Reusable 3-fold non-stationary integration by parts -/

/-- One-step IBP operator `L_φ(h)(x) = (h(x) / φ'(x))'` (complex-valued). -/
noncomputable def ibpStep (φ : ℝ → ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  deriv fun x => h x / ((deriv φ x : ℝ) : ℂ)

lemma contDiffOn_ibpStep {n : ℕ} {U : Set ℝ} (hU : IsOpen U) {φ : ℝ → ℝ} {h : ℝ → ℂ}
    (hφ : ContDiffOn ℝ (n + 2 : ℕ) φ U) (hh : ContDiffOn ℝ (n + 1 : ℕ) h U)
    (hφ_ne : ∀ x ∈ U, deriv φ x ≠ 0) :
    ContDiffOn ℝ n (ibpStep φ h) U := by
  have hdφ : ContDiffOn ℝ (n + 1 : ℕ) (deriv φ) U := by
    have h1 : ContDiffOn ℝ (n + 1 : ℕ) (derivWithin φ U) U :=
      hφ.derivWithin hU.uniqueDiffOn (m := (n + 1 : ℕ)) (by norm_cast)
    exact h1.congr fun x hx => (derivWithin_of_isOpen hU hx).symm
  have hdiv : ContDiffOn ℝ (n + 1 : ℕ) (fun x => h x / ((deriv φ x : ℝ) : ℂ)) U := by
    have heq : (fun x => h x / ((deriv φ x : ℝ) : ℂ)) = fun x => h x * (((deriv φ x)⁻¹ : ℝ) : ℂ) := by
      ext x; simp [div_eq_mul_inv]
    rw [heq]
    exact hh.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (hdφ.inv hφ_ne))
  have hder : ContDiffOn ℝ n (derivWithin (fun x => h x / ((deriv φ x : ℝ) : ℂ)) U) U :=
    hdiv.derivWithin hU.uniqueDiffOn (m := n) (by norm_cast)
  exact hder.congr fun x hx => (derivWithin_of_isOpen hU hx).symm

lemma ibpStep_integral {a b : ℝ} (hab : a ≤ b) {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    {φ : ℝ → ℝ} {h : ℝ → ℂ}
    (hφ : ContDiffOn ℝ 2 φ U) (hh : ContDiffOn ℝ 1 h U)
    (hφ_ne : ∀ x ∈ U, deriv φ x ≠ 0) :
    ∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * h x =
      Complex.exp (Complex.I * (φ b : ℂ)) * (h b / (Complex.I * ((deriv φ b : ℝ) : ℂ))) -
      Complex.exp (Complex.I * (φ a : ℂ)) * (h a / (Complex.I * ((deriv φ a : ℝ) : ℂ))) +
      Complex.I * ∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * ibpStep φ h x := by
  let u : ℝ → ℂ := fun x => h x / ((deriv φ x : ℝ) : ℂ)
  let v : ℝ → ℂ := fun x => Complex.exp (Complex.I * (φ x : ℂ)) / Complex.I
  have hdφ_cd : ContDiffOn ℝ 1 (deriv φ) U := by
    have h1 := hφ.derivWithin hU.uniqueDiffOn (m := 1) (by norm_num)
    exact h1.congr fun x hx => (derivWithin_of_isOpen hU hx).symm
  have hu_cd : ContDiffOn ℝ 1 u U := by
    have heq : u = fun x => h x * (((deriv φ x)⁻¹ : ℝ) : ℂ) := by
      ext x; simp [u, div_eq_mul_inv]
    rw [heq]
    exact hh.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (hdφ_cd.inv hφ_ne))
  have hu : ∀ x ∈ uIcc a b, HasDerivAt u (ibpStep φ h x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hmem : x ∈ U := hsub hx
    have hdiff : DifferentiableAt ℝ u x :=
      (hu_cd.differentiableOn one_ne_zero x hmem).differentiableAt (hU.mem_nhds hmem)
    exact hdiff.hasDerivAt
  have hv : ∀ x ∈ uIcc a b, HasDerivAt v (Complex.exp (Complex.I * (φ x : ℂ)) * ((deriv φ x : ℝ) : ℂ)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hmem : x ∈ U := hsub hx
    have hφd : HasDerivAt φ (deriv φ x) x :=
      ((hφ.differentiableOn (by norm_num) x hmem).differentiableAt (hU.mem_nhds hmem)).hasDerivAt
    have h1 : HasDerivAt (fun t => Complex.I * (φ t : ℂ)) (Complex.I * ((deriv φ x : ℝ) : ℂ)) x :=
      hφd.ofReal_comp.const_mul Complex.I
    have h2 : HasDerivAt (fun t => Complex.exp (Complex.I * (φ t : ℂ)))
        (Complex.exp (Complex.I * (φ x : ℂ)) * (Complex.I * ((deriv φ x : ℝ) : ℂ))) x :=
      h1.cexp
    refine (h2.div_const Complex.I).congr_deriv ?_
    field_simp [Complex.I_ne_zero]
  have hu'_cont : ContinuousOn (ibpStep φ h) (Icc a b) :=
    (contDiffOn_ibpStep (n := 0) hU hφ hh hφ_ne).continuousOn.mono hsub
  have hv'_cont : ContinuousOn (fun x => Complex.exp (Complex.I * (φ x : ℂ)) * ((deriv φ x : ℝ) : ℂ)) (Icc a b) := by
    have h1 : ContinuousOn (fun x => Complex.exp (Complex.I * (φ x : ℂ))) (Icc a b) :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp_continuousOn
        (hφ.continuousOn.mono hsub)
    have h2 : ContinuousOn (fun x => ((deriv φ x : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.comp_continuousOn (hdφ_cd.continuousOn.mono hsub)
    exact h1.mul h2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hu'_cont.intervalIntegrable_of_Icc hab) (hv'_cont.intervalIntegrable_of_Icc hab)
  have hlhs : ∫ x in a..b, u x * (Complex.exp (Complex.I * (φ x : ℂ)) * ((deriv φ x : ℝ) : ℂ)) =
      ∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * h x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hab] at hx
    have hne : ((deriv φ x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ_ne x (hsub hx))
    dsimp [u]; field_simp [hne]
  have hrhs : ∫ x in a..b, ibpStep φ h x * v x =
      (-Complex.I) * ∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * ibpStep φ h x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    dsimp [v]; rw [div_eq_mul_inv, inv_I]; ring
  rw [hlhs, hrhs] at hibp
  have hb_eq : u b * v b = Complex.exp (Complex.I * (φ b : ℂ)) * (h b / (Complex.I * ((deriv φ b : ℝ) : ℂ))) := by
    dsimp [u, v]; ring
  have ha_eq : u a * v a = Complex.exp (Complex.I * (φ a : ℂ)) * (h a / (Complex.I * ((deriv φ a : ℝ) : ℂ))) := by
    dsimp [u, v]; ring
  rw [hb_eq, ha_eq] at hibp
  linear_combination hibp

/-- Derivative bounds on `1 / φ'(x)` through order `3`. -/
lemma inv_deriv_bounds {U : Set ℝ} (hU : IsOpen U) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 4 φ U) {x Λ w K : ℝ} (hx : x ∈ U)
    (hΛ : 0 < Λ) (hw : 0 < w) (hK : 1 ≤ K)
    (hφ1 : Λ ≤ |deriv φ x|)
    (hφk : ∀ j ∈ ({1, 2, 3} : Finset ℕ), |iteratedDeriv (j + 1) φ x| ≤ K * w ^ (-(j : ℤ)) * |deriv φ x|) :
    ∀ m ≤ 3, |iteratedDeriv m (fun t => (deriv φ t)⁻¹) x| ≤ 13 * K ^ 3 * w ^ (-(m : ℤ)) / Λ := by
  have hp_ne : deriv φ x ≠ 0 := fun h0 => by rw [h0, abs_zero] at hφ1; linarith
  have hp_pos : 0 < |deriv φ x| := abs_pos.mpr hp_ne
  have hcd_p : ContDiffAt ℝ 3 (deriv φ) x := by
    have h1 : ContDiffOn ℝ 3 (deriv φ) U :=
      (hφ.derivWithin hU.uniqueDiffOn (m := 3) (by norm_num)).congr fun t ht => (derivWithin_of_isOpen hU ht).symm
    exact h1.contDiffAt (hU.mem_nhds hx)
  have h1 : |iteratedDeriv 1 (deriv φ) x| ≤ K * w ^ (-1 : ℤ) * |deriv φ x| := by
    have := hφk 1 (by simp)
    rwa [iteratedDeriv_succ'] at this
  have h2 : |iteratedDeriv 2 (deriv φ) x| ≤ K * w ^ (-2 : ℤ) * |deriv φ x| := by
    have := hφk 2 (by simp)
    rwa [iteratedDeriv_succ'] at this
  have h3 : |iteratedDeriv 3 (deriv φ) x| ≤ K * w ^ (-3 : ℤ) * |deriv φ x| := by
    have := hφk 3 (by simp)
    rwa [iteratedDeriv_succ'] at this
  -- Derivatives of `g(t) = (p t)⁻¹`
  set p := deriv φ
  have hp_cdU : ContDiffOn ℝ 3 p U :=
    (hφ.derivWithin hU.uniqueDiffOn (m := 3) (by norm_num)).congr fun s hs => (derivWithin_of_isOpen hU hs).symm
  have hdp_cdU : ContDiffOn ℝ 2 (deriv p) U :=
    (hp_cdU.derivWithin hU.uniqueDiffOn (m := 2) (by norm_num)).congr fun s hs => (derivWithin_of_isOpen hU hs).symm
  have hddp_cdU : ContDiffOn ℝ 1 (iteratedDeriv 2 p) U := by
    have h1 : ContDiffOn ℝ 1 (deriv (deriv p)) U :=
      (hdp_cdU.derivWithin hU.uniqueDiffOn (m := 1) (by norm_num)).congr fun s hs => (derivWithin_of_isOpen hU hs).symm
    exact h1.congr fun s _ => by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hp_ev : ∀ᶠ t in 𝓝 x, p t ≠ 0 :=
    hcd_p.continuousAt.eventually_ne hp_ne
  have hd1_ev : deriv (fun s => (p s)⁻¹) =ᶠ[𝓝 x] fun s => -deriv p s / (p s) ^ 2 := by
    filter_upwards [hp_ev, hU.mem_nhds hx] with t ht htU
    have hd : HasDerivAt p (deriv p t) t :=
      ((hp_cdU.differentiableOn (by norm_num) t htU).differentiableAt (hU.mem_nhds htU)).hasDerivAt
    exact (hd.inv ht).deriv
  have hd2_ev : iteratedDeriv 2 (fun s => (p s)⁻¹) =ᶠ[𝓝 x]
      fun s => (-iteratedDeriv 2 p s * p s + 2 * (deriv p s) ^ 2) / (p s) ^ 3 := by
    filter_upwards [hp_ev, hU.mem_nhds hx, hd1_ev.eventuallyEq_nhds] with t ht htU h1t
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1t.deriv_eq]
    have hdp1 : HasDerivAt p (deriv p t) t :=
      ((hp_cdU.differentiableOn (by norm_num) t htU).differentiableAt (hU.mem_nhds htU)).hasDerivAt
    have hdp2 : HasDerivAt (deriv p) (iteratedDeriv 2 p t) t := by
      have hd' := ((hdp_cdU.differentiableOn (by norm_num) t htU).differentiableAt (hU.mem_nhds htU)).hasDerivAt
      rwa [show deriv (deriv p) t = iteratedDeriv 2 p t by rw [iteratedDeriv_succ, iteratedDeriv_one]] at hd'
    have hnum : HasDerivAt (fun s => -deriv p s) (-iteratedDeriv 2 p t) t := hdp2.neg
    have hden : HasDerivAt (fun s => (p s) ^ 2) (2 * p t * deriv p t) t :=
      (hdp1.pow 2).congr_deriv (by simp [mul_comm])
    have hq := hnum.div hden (pow_ne_zero 2 ht)
    have hqd : deriv (fun s => -deriv p s / (p s) ^ 2) t =
        (-iteratedDeriv 2 p t * (p t) ^ 2 - -deriv p t * (2 * p t * deriv p t)) / ((p t) ^ 2) ^ 2 :=
      hq.deriv
    rw [hqd]
    field_simp [ht]
    ring
  have hd3_at : iteratedDeriv 3 (fun s => (p s)⁻¹) x =
      (-iteratedDeriv 3 p x * (p x) ^ 2 + 6 * iteratedDeriv 2 p x * deriv p x * p x -
        6 * (deriv p x) ^ 3) / (p x) ^ 4 := by
    rw [iteratedDeriv_succ, hd2_ev.deriv_eq]
    have hdp1 : HasDerivAt p (deriv p x) x :=
      ((hp_cdU.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
    have hdp2 : HasDerivAt (deriv p) (iteratedDeriv 2 p x) x := by
      have hd' := ((hdp_cdU.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
      rwa [show deriv (deriv p) x = iteratedDeriv 2 p x by rw [iteratedDeriv_succ, iteratedDeriv_one]] at hd'
    have hdp3 : HasDerivAt (iteratedDeriv 2 p) (iteratedDeriv 3 p x) x := by
      have hd' := ((hddp_cdU.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
      rwa [← iteratedDeriv_succ] at hd'
    have hnum : HasDerivAt (fun s => -iteratedDeriv 2 p s * p s + 2 * (deriv p s) ^ 2)
        ((-iteratedDeriv 3 p x * p x + -iteratedDeriv 2 p x * deriv p x) +
          2 * (2 * deriv p x * iteratedDeriv 2 p x)) x := by
      have ha := (hdp3.neg).mul hdp1
      have hb1 : HasDerivAt (fun s => (deriv p s) ^ 2) (2 * deriv p x * iteratedDeriv 2 p x) x :=
        (hdp2.pow 2).congr_deriv (by simp [mul_comm])
      exact ha.add (hb1.const_mul 2)
    have hden : HasDerivAt (fun s => (p s) ^ 3) (3 * (p x) ^ 2 * deriv p x) x :=
      (hdp1.pow 3).congr_deriv (by simp [mul_comm])
    have hq := hnum.div hden (pow_ne_zero 3 hp_ne)
    have hqd : deriv (fun s => (-iteratedDeriv 2 p s * p s + 2 * (deriv p s) ^ 2) / (p s) ^ 3) x =
        (((-iteratedDeriv 3 p x * p x + -iteratedDeriv 2 p x * deriv p x) +
          2 * (2 * deriv p x * iteratedDeriv 2 p x)) * (p x) ^ 3 -
          (-iteratedDeriv 2 p x * p x + 2 * (deriv p x) ^ 2) * (3 * (p x) ^ 2 * deriv p x)) / ((p x) ^ 3) ^ 2 :=
      hq.deriv
    rw [hqd]
    field_simp [hp_ne]
    ring
  intro m hm
  have hK1 : 1 ≤ K := hK
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hK3 : K ^ 2 ≤ K ^ 3 := by nlinarith
  have hinv_le : |p x|⁻¹ ≤ Λ⁻¹ := inv_anti₀ hΛ hφ1
  interval_cases m
  · -- m = 0
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one, abs_inv]
    calc |p x|⁻¹ ≤ Λ⁻¹ := hinv_le
      _ = 1 / Λ := (one_div Λ).symm
      _ ≤ 13 * K ^ 3 / Λ := by gcongr; nlinarith
  · -- m = 1
    rw [iteratedDeriv_one, hd1_ev.self_of_nhds, abs_div, abs_neg, abs_pow]
    have h1' : |deriv p x| ≤ K * w ^ (-1 : ℤ) * |p x| := by rwa [iteratedDeriv_one] at h1
    have hstep : |deriv p x| / |p x| ^ 2 ≤ K * w ^ (-1 : ℤ) / |p x| := by
      rw [div_le_div_iff₀ (pow_pos hp_pos 2) hp_pos]
      nlinarith
    have hstep2 : K * w ^ (-1 : ℤ) / |p x| ≤ K * w ^ (-1 : ℤ) / Λ :=
      div_le_div_of_nonneg_left (by positivity) hΛ hφ1
    calc |deriv p x| / |p x| ^ 2 ≤ K * w ^ (-1 : ℤ) / Λ := hstep.trans hstep2
      _ ≤ 13 * K ^ 3 * w ^ (-1 : ℤ) / Λ := by
          gcongr; nlinarith
  · -- m = 2
    rw [hd2_ev.self_of_nhds, abs_div, abs_pow]
    have h1' : |deriv p x| ≤ K * w ^ (-1 : ℤ) * |p x| := by rwa [iteratedDeriv_one] at h1
    have htri : |-iteratedDeriv 2 p x * p x + 2 * (deriv p x) ^ 2| ≤
        |iteratedDeriv 2 p x| * |p x| + 2 * |deriv p x| ^ 2 := by
      calc |-iteratedDeriv 2 p x * p x + 2 * (deriv p x) ^ 2|
          ≤ |-iteratedDeriv 2 p x * p x| + |2 * (deriv p x) ^ 2| := abs_add_le _ _
        _ = |iteratedDeriv 2 p x| * |p x| + 2 * |deriv p x| ^ 2 := by
            simp [abs_mul, abs_pow]
    have hsq1 : |deriv p x| ^ 2 ≤ K ^ 2 * w ^ (-2 : ℤ) * |p x| ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg _) h1'
      have hw2 : w ^ (-1 : ℤ) * w ^ (-1 : ℤ) = w ^ (-2 : ℤ) := by
        rw [← zpow_add₀ hw.ne']; norm_num
      calc |deriv p x| ^ 2 = |deriv p x| * |deriv p x| := sq _
        _ ≤ (K * w ^ (-1 : ℤ) * |p x|) * (K * w ^ (-1 : ℤ) * |p x|) := h
        _ = K ^ 2 * (w ^ (-1 : ℤ) * w ^ (-1 : ℤ)) * |p x| ^ 2 := by ring
        _ = K ^ 2 * w ^ (-2 : ℤ) * |p x| ^ 2 := by rw [hw2]
    have hnum_le : |-iteratedDeriv 2 p x * p x + 2 * (deriv p x) ^ 2| ≤
        3 * K ^ 2 * w ^ (-2 : ℤ) * |p x| ^ 2 := by
      have ha : |iteratedDeriv 2 p x| * |p x| ≤ K * w ^ (-2 : ℤ) * |p x| ^ 2 := by
        calc |iteratedDeriv 2 p x| * |p x| ≤ (K * w ^ (-2 : ℤ) * |p x|) * |p x| :=
              mul_le_mul_of_nonneg_right h2 hp_pos.le
          _ = K * w ^ (-2 : ℤ) * |p x| ^ 2 := by ring
      have hK_le : K * w ^ (-2 : ℤ) * |p x| ^ 2 ≤ K ^ 2 * w ^ (-2 : ℤ) * |p x| ^ 2 := by
        gcongr
      linarith
    calc |-iteratedDeriv 2 p x * p x + 2 * (deriv p x) ^ 2| / |p x| ^ 3
        ≤ (3 * K ^ 2 * w ^ (-2 : ℤ) * |p x| ^ 2) / |p x| ^ 3 :=
          div_le_div_of_nonneg_right hnum_le (pow_nonneg hp_pos.le 3)
      _ = 3 * K ^ 2 * w ^ (-2 : ℤ) / |p x| := by field_simp [hp_pos.ne']
      _ ≤ 3 * K ^ 2 * w ^ (-2 : ℤ) / Λ :=
          div_le_div_of_nonneg_left (by positivity) hΛ hφ1
      _ ≤ 13 * K ^ 3 * w ^ (-2 : ℤ) / Λ := by gcongr; nlinarith
  · -- m = 3
    rw [hd3_at, abs_div, abs_pow]
    have h1' : |deriv p x| ≤ K * w ^ (-1 : ℤ) * |p x| := by rwa [iteratedDeriv_one] at h1
    have htri : |-iteratedDeriv 3 p x * (p x) ^ 2 + 6 * iteratedDeriv 2 p x * deriv p x * p x -
        6 * (deriv p x) ^ 3| ≤
        |iteratedDeriv 3 p x| * |p x| ^ 2 + 6 * |iteratedDeriv 2 p x| * |deriv p x| * |p x| +
        6 * |deriv p x| ^ 3 := by
      calc |-iteratedDeriv 3 p x * (p x) ^ 2 + 6 * iteratedDeriv 2 p x * deriv p x * p x -
            6 * (deriv p x) ^ 3|
          ≤ |-iteratedDeriv 3 p x * (p x) ^ 2 + 6 * iteratedDeriv 2 p x * deriv p x * p x| +
            |6 * (deriv p x) ^ 3| := abs_sub _ _
        _ ≤ |-iteratedDeriv 3 p x * (p x) ^ 2| + |6 * iteratedDeriv 2 p x * deriv p x * p x| +
            |6 * (deriv p x) ^ 3| := add_le_add (abs_add_le _ _) le_rfl
        _ = |iteratedDeriv 3 p x| * |p x| ^ 2 + 6 * |iteratedDeriv 2 p x| * |deriv p x| * |p x| +
            6 * |deriv p x| ^ 3 := by simp [abs_mul, abs_pow]
    have hw3a : w ^ (-2 : ℤ) * w ^ (-1 : ℤ) = w ^ (-3 : ℤ) := by
      rw [← zpow_add₀ hw.ne']; norm_num
    have hw3b : (w ^ (-1 : ℤ)) ^ 3 = w ^ (-3 : ℤ) := by
      rw [← zpow_natCast, ← zpow_mul]; norm_num
    have ht1 : |iteratedDeriv 3 p x| * |p x| ^ 2 ≤ K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3 := by
      calc |iteratedDeriv 3 p x| * |p x| ^ 2
          ≤ (K * w ^ (-3 : ℤ) * |p x|) * |p x| ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        _ = K * w ^ (-3 : ℤ) * |p x| ^ 3 := by ring
        _ ≤ K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3 := by gcongr; nlinarith
    have ht2 : |iteratedDeriv 2 p x| * |deriv p x| * |p x| ≤ K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3 := by
      calc |iteratedDeriv 2 p x| * |deriv p x| * |p x|
          ≤ (K * w ^ (-2 : ℤ) * |p x|) * (K * w ^ (-1 : ℤ) * |p x|) * |p x| := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul h2 h1' (abs_nonneg _) (by positivity)) hp_pos.le
        _ = K ^ 2 * (w ^ (-2 : ℤ) * w ^ (-1 : ℤ)) * |p x| ^ 3 := by ring
        _ = K ^ 2 * w ^ (-3 : ℤ) * |p x| ^ 3 := by rw [hw3a]
        _ ≤ K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3 := by gcongr
    have ht3 : |deriv p x| ^ 3 ≤ K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3 := by
      calc |deriv p x| ^ 3 ≤ (K * w ^ (-1 : ℤ) * |p x|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1' 3
        _ = K ^ 3 * (w ^ (-1 : ℤ)) ^ 3 * |p x| ^ 3 := by ring
        _ = K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3 := by rw [hw3b]
    have hnum_le : |-iteratedDeriv 3 p x * (p x) ^ 2 + 6 * iteratedDeriv 2 p x * deriv p x * p x -
        6 * (deriv p x) ^ 3| ≤ 13 * K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3 := by
      linarith
    calc _ ≤ (13 * K ^ 3 * w ^ (-3 : ℤ) * |p x| ^ 3) / |p x| ^ 4 :=
          div_le_div_of_nonneg_right hnum_le (pow_nonneg hp_pos.le 4)
      _ = 13 * K ^ 3 * w ^ (-3 : ℤ) / |p x| := by field_simp [hp_pos.ne']
      _ ≤ 13 * K ^ 3 * w ^ (-3 : ℤ) / Λ :=
          div_le_div_of_nonneg_left (by positivity) hΛ hφ1

private lemma iteratedDeriv_ofReal_eq (n : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv n (fun t => (g t : ℂ)) x = ((iteratedDeriv n g x : ℝ) : ℂ) := by
  induction n generalizing g x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun t => (g t : ℂ)) = fun t => ((iteratedDeriv n g t : ℝ) : ℂ) :=
      funext (ih g)
    rw [hfun]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv n g) x
    · exact hd.hasDerivAt.ofReal_comp.deriv
    · have hnd : ¬ DifferentiableAt ℝ (fun t => ((iteratedDeriv n g t : ℝ) : ℂ)) x := by
        intro hcd
        exact hd (Complex.reCLM.differentiableAt.comp x hcd)
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd,
        Complex.ofReal_zero]

/-- One step of derivative bounds for `ibpStep φ h`. -/
lemma ibpStep_deriv_bound {n : ℕ} (hn : n ≤ 2) {U : Set ℝ} (hU : IsOpen U) {φ : ℝ → ℝ} {h : ℝ → ℂ}
    (hφ : ContDiffOn ℝ 4 φ U) (hh : ContDiffOn ℝ (n + 1 : ℕ) h U)
    {x Λ w K M : ℝ} (hx : x ∈ U)
    (hΛ : 0 < Λ) (hw : 0 < w) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hφ1 : Λ ≤ |deriv φ x|)
    (hφk : ∀ j ∈ ({1, 2, 3} : Finset ℕ), |iteratedDeriv (j + 1) φ x| ≤ K * w ^ (-(j : ℤ)) * |deriv φ x|)
    (hhk : ∀ j ≤ n + 1, ‖iteratedDeriv j h x‖ ≤ M * w ^ (-(j : ℤ))) :
    ∀ j ≤ n, ‖iteratedDeriv j (ibpStep φ h) x‖ ≤ (104 * K ^ 3 * M / (Λ * w)) * w ^ (-(j : ℤ)) := by
  have hinv := inv_deriv_bounds hU hφ hx hΛ hw hK hφ1 hφk
  have hdφ_cd : ContDiffAt ℝ 3 (deriv φ) x :=
    ((hφ.derivWithin hU.uniqueDiffOn (m := 3) (by norm_num)).congr
      fun t ht => (derivWithin_of_isOpen hU ht).symm).contDiffAt (hU.mem_nhds hx)
  have hinv_cd : ContDiffAt ℝ 3 (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x := by
    have hp_ne : deriv φ x ≠ 0 := fun h0 => by rw [h0, abs_zero] at hφ1; linarith
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x (hdφ_cd.inv hp_ne)
  have hh_cd : ContDiffAt ℝ (n + 1 : ℕ) h x := hh.contDiffAt (hU.mem_nhds hx)
  have heq_mul : (fun t => h t / ((deriv φ t : ℝ) : ℂ)) = h * fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ) := by
    ext t; simp [div_eq_mul_inv]
  intro j hj
  have h_le : j + 1 ≤ 3 := by omega
  have h_iter : iteratedDeriv j (ibpStep φ h) x =
      iteratedDeriv (j + 1) (h * fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x := by
    unfold ibpStep
    rw [heq_mul, ← iteratedDeriv_succ']
  rw [h_iter]
  have hleib := iteratedDeriv_mul (n := j + 1)
    (hh_cd.of_le (by exact_mod_cast (show j + 1 ≤ n + 1 by omega)))
    (hinv_cd.of_le (by exact_mod_cast h_le))
  rw [hleib]
  calc ‖∑ i ∈ Finset.range (j + 1 + 1),
        ((j + 1).choose i : ℂ) * iteratedDeriv i h x * iteratedDeriv (j + 1 - i) (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x‖
      ≤ ∑ i ∈ Finset.range (j + 1 + 1),
        ‖((j + 1).choose i : ℂ) * iteratedDeriv i h x * iteratedDeriv (j + 1 - i) (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1 + 1),
        ((j + 1).choose i : ℝ) * (13 * K ^ 3 * M / (Λ * w) * w ^ (-(j : ℤ))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_le : i ≤ j + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_assoc, norm_mul, norm_mul, Complex.norm_natCast]
        have ha : ‖iteratedDeriv i h x‖ ≤ M * w ^ (-(i : ℤ)) := hhk i (by omega)
        have hb : ‖iteratedDeriv (j + 1 - i) (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x‖ ≤
            13 * K ^ 3 * w ^ (-((j + 1 - i : ℕ) : ℤ)) / Λ := by
          have hcomp : iteratedDeriv (j + 1 - i) (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x =
              ((iteratedDeriv (j + 1 - i) (fun t => (deriv φ t)⁻¹) x : ℝ) : ℂ) :=
            iteratedDeriv_ofReal_eq (j + 1 - i) (fun t => (deriv φ t)⁻¹) x
          rw [hcomp, Complex.norm_real, Real.norm_eq_abs]
          exact hinv (j + 1 - i) (by omega)
        have hmul : ‖iteratedDeriv i h x‖ * ‖iteratedDeriv (j + 1 - i) (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x‖ ≤
            13 * K ^ 3 * M / (Λ * w) * w ^ (-(j : ℤ)) := by
          have hw_eq : w ^ (-(i : ℤ)) * w ^ (-((j + 1 - i : ℕ) : ℤ)) = w⁻¹ * w ^ (-(j : ℤ)) := by
            rw [← zpow_add₀ hw.ne', ← zpow_neg_one, ← zpow_add₀ hw.ne']
            congr 1; omega
          calc _ ≤ (M * w ^ (-(i : ℤ))) * (13 * K ^ 3 * w ^ (-((j + 1 - i : ℕ) : ℤ)) / Λ) :=
                mul_le_mul ha hb (norm_nonneg _) (by positivity)
            _ = 13 * K ^ 3 * M / Λ * (w ^ (-(i : ℤ)) * w ^ (-((j + 1 - i : ℕ) : ℤ))) := by ring
            _ = 13 * K ^ 3 * M / Λ * (w⁻¹ * w ^ (-(j : ℤ))) := by rw [hw_eq]
            _ = 13 * K ^ 3 * M / (Λ * w) * w ^ (-(j : ℤ)) := by field_simp [hΛ.ne', hw.ne']
        exact mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
    _ = (∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ)) * (13 * K ^ 3 * M / (Λ * w) * w ^ (-(j : ℤ))) := by
        rw [Finset.sum_mul]
    _ = ((2 : ℝ) ^ (j + 1)) * (13 * K ^ 3 * M / (Λ * w) * w ^ (-(j : ℤ))) := by
        have hsum : (∑ i ∈ Finset.range (j + 1 + 1), ((j + 1).choose i : ℝ)) = (2 : ℝ) ^ (j + 1) := by
          exact_mod_cast Nat.sum_range_choose (j + 1)
        rw [hsum]
    _ ≤ (8 : ℝ) * (13 * K ^ 3 * M / (Λ * w) * w ^ (-(j : ℤ))) := by
        have h2 : (2 : ℝ) ^ (j + 1) ≤ 8 := by
          calc (2 : ℝ) ^ (j + 1) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) h_le
            _ = 8 := by norm_num
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (104 * K ^ 3 * M / (Λ * w)) * w ^ (-(j : ℤ)) := by ring

/-- Three-fold IBP bound on `[a, b]` when `h` and its first two derivatives vanish at `a` and `b`. -/
theorem ibp3_interval {a b : ℝ} (hab : a ≤ b) {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    {φ : ℝ → ℝ} {h : ℝ → ℂ} {B w : ℝ → ℝ} {Λ K : ℝ}
    (hφ : ContDiffOn ℝ 4 φ U) (hh : ContDiffOn ℝ 3 h U)
    (hφ_ne : ∀ x ∈ U, deriv φ x ≠ 0)
    (hΛ : 0 < Λ) (hK : 1 ≤ K)
    (hvan_a : ∀ j ≤ 2, iteratedDeriv j h a = 0)
    (hvan_b : ∀ j ≤ 2, iteratedDeriv j h b = 0)
    (hw_pos : ∀ x ∈ Icc a b, 0 < w x)
    (hB_nn : ∀ x ∈ Icc a b, 0 ≤ B x)
    (hφ1 : ∀ x ∈ Icc a b, Λ ≤ |deriv φ x|)
    (hφk : ∀ x ∈ Icc a b, ∀ j ∈ ({1, 2, 3} : Finset ℕ),
      |iteratedDeriv (j + 1) φ x| ≤ K * (w x) ^ (-(j : ℤ)) * |deriv φ x|)
    (hhk : ∀ x ∈ Icc a b, ∀ j ≤ 3, ‖iteratedDeriv j h x‖ ≤ B x * (w x) ^ (-(j : ℤ)))
    (hBw_int : IntervalIntegrable (fun x => B x * (w x) ^ (-3 : ℤ)) volume a b) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * h x‖ ≤
      (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in a..b, B x * (w x) ^ (-3 : ℤ) := by
  let h1 := ibpStep φ h
  let h2 := ibpStep φ h1
  let h3 := ibpStep φ h2
  have hh1_cd : ContDiffOn ℝ 2 h1 U := contDiffOn_ibpStep (n := 2) hU (hφ.of_le (by norm_num)) hh hφ_ne
  have hh2_cd : ContDiffOn ℝ 1 h2 U := contDiffOn_ibpStep (n := 1) hU (hφ.of_le (by norm_num)) hh1_cd hφ_ne
  have hh3_cd : ContDiffOn ℝ 0 h3 U := contDiffOn_ibpStep (n := 0) hU (hφ.of_le (by norm_num)) hh2_cd hφ_ne
  -- Vanishing of `h1` and `h2` at `a` and `b`
  have hvan_step : ∀ {f : ℝ → ℂ} {x : ℝ} {n : ℕ}, x ∈ U → n ≤ 1 →
      ContDiffOn ℝ (n + 1 : ℕ) f U → (∀ j ≤ n + 1, iteratedDeriv j f x = 0) →
      ∀ j ≤ n, iteratedDeriv j (ibpStep φ f) x = 0 := by
    intro f x n hxU hn hf hfv j hj
    have hdφ_cd : ContDiffAt ℝ 3 (deriv φ) x :=
      ((hφ.derivWithin hU.uniqueDiffOn (m := 3) (by norm_num)).congr
        fun t ht => (derivWithin_of_isOpen hU ht).symm).contDiffAt (hU.mem_nhds hxU)
    have hinv_cd : ContDiffAt ℝ 3 (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (hdφ_cd.inv (hφ_ne x hxU))
    have heq_mul : (fun t => f t / ((deriv φ t : ℝ) : ℂ)) = f * fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ) := by
      ext t; simp [div_eq_mul_inv]
    unfold ibpStep
    rw [heq_mul, ← iteratedDeriv_succ', iteratedDeriv_mul (n := j + 1)
      ((hf.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast (show j + 1 ≤ n + 1 by omega)))
      (hinv_cd.of_le (by exact_mod_cast (show j + 1 ≤ 3 by omega)))]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_le : i ≤ j + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hfv i (by omega), mul_zero, zero_mul]
  have haU : a ∈ U := hsub (left_mem_Icc.mpr hab)
  have hbU : b ∈ U := hsub (right_mem_Icc.mpr hab)
  have hh0_a : h a = 0 := by simpa using hvan_a 0 (by omega)
  have hh0_b : h b = 0 := by simpa using hvan_b 0 (by omega)
  have hh1_a : ∀ j ≤ 1, iteratedDeriv j h1 a = 0 := hvan_step haU le_rfl (hh.of_le (by norm_num)) hvan_a
  have hh1_b : ∀ j ≤ 1, iteratedDeriv j h1 b = 0 := hvan_step hbU le_rfl (hh.of_le (by norm_num)) hvan_b
  have hh2_a : h2 a = 0 := by
    simpa using hvan_step (n := 0) haU (by omega) (hh1_cd.of_le (by norm_num)) hh1_a 0 le_rfl
  have hh2_b : h2 b = 0 := by
    simpa using hvan_step (n := 0) hbU (by omega) (hh1_cd.of_le (by norm_num)) hh1_b 0 le_rfl
  have step1 := ibpStep_integral hab hU hsub (hφ.of_le (by norm_num)) (hh.of_le (by norm_num)) hφ_ne
  have step2 := ibpStep_integral hab hU hsub (hφ.of_le (by norm_num)) (hh1_cd.of_le (by norm_num)) hφ_ne
  have step3 := ibpStep_integral hab hU hsub (hφ.of_le (by norm_num)) hh2_cd hφ_ne
  rw [hh0_a, hh0_b, zero_div, zero_div, mul_zero, mul_zero, sub_zero, zero_add] at step1
  rw [show h1 a = 0 from by simpa using hh1_a 0 (by omega),
      show h1 b = 0 from by simpa using hh1_b 0 (by omega),
      zero_div, zero_div, mul_zero, mul_zero, sub_zero, zero_add] at step2
  rw [hh2_a, hh2_b, zero_div, zero_div, mul_zero, mul_zero, sub_zero, zero_add] at step3
  rw [step1, step2, step3]
  have hnorm_I : ‖Complex.I * (Complex.I * (Complex.I *
      ∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * h3 x))‖ =
      ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖ := by
    simp [Complex.norm_I]
  rw [hnorm_I]
  have h3_bound : ∀ x ∈ Icc a b, ‖Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖ ≤
      (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * (B x * (w x) ^ (-3 : ℤ)) := by
    intro x hx
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    have hxU : x ∈ U := hsub hx
    have b1 := ibpStep_deriv_bound (n := 2) le_rfl hU hφ hh hxU hΛ (hw_pos x hx) hK (hB_nn x hx)
      (hφ1 x hx) (hφk x hx) (hhk x hx)
    have b2 := ibpStep_deriv_bound (n := 1) (by omega) hU hφ hh1_cd hxU hΛ (hw_pos x hx) hK
      (by have := hB_nn x hx; have := hw_pos x hx; positivity) (hφ1 x hx) (hφk x hx) b1
    have b3 := ibpStep_deriv_bound (n := 0) (by omega) hU hφ hh2_cd hxU hΛ (hw_pos x hx) hK
      (by have := hB_nn x hx; have := hw_pos x hx; positivity) (hφ1 x hx) (hφk x hx) b2 0 le_rfl
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at b3
    refine b3.trans (le_of_eq ?_)
    have hw0 := (hw_pos x hx).ne'
    have hΛ0 := hΛ.ne'
    rw [show (w x) ^ (-3 : ℤ) = ((w x) ^ 3)⁻¹ by rw [zpow_neg]; norm_cast,
        show Λ ^ (-3 : ℤ) = (Λ ^ 3)⁻¹ by rw [zpow_neg]; norm_cast]
    field_simp [hw0, hΛ0]
  calc ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖
      ≤ ∫ x in a..b, ‖Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in a..b, (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * (B x * (w x) ^ (-3 : ℤ)) := by
        refine intervalIntegral.integral_mono_on hab ?_ (hBw_int.const_mul _) h3_bound
        have hcont : ContinuousOn (fun x => Complex.exp (Complex.I * (φ x : ℂ)) * h3 x) (Icc a b) :=
          ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp_continuousOn
            (hφ.continuousOn.mono hsub)).mul (hh3_cd.continuousOn.mono hsub)
        exact hcont.norm.intervalIntegrable_of_Icc hab
    _ = (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in a..b, B x * (w x) ^ (-3 : ℤ) :=
        intervalIntegral.integral_const_mul _ _

/-- Three-fold IBP bound on `Ioi a` when `h` and its first two derivatives vanish at `a`,
and `B(x) w(x)^{-j} → 0` as `x → ∞` for `j ≤ 2`. -/
theorem ibp3_Ioi {a : ℝ} {U : Set ℝ} (hU : IsOpen U) (hsub : Ici a ⊆ U)
    {φ : ℝ → ℝ} {h : ℝ → ℂ} {B w : ℝ → ℝ} {Λ K : ℝ}
    (hφ : ContDiffOn ℝ 4 φ U) (hh : ContDiffOn ℝ 3 h U)
    (hφ_ne : ∀ x ∈ U, deriv φ x ≠ 0)
    (hΛ : 0 < Λ) (hK : 1 ≤ K)
    (hvan_a : ∀ j ≤ 2, iteratedDeriv j h a = 0)
    (hw_pos : ∀ x ∈ Ici a, 0 < w x)
    (hB_nn : ∀ x ∈ Ici a, 0 ≤ B x)
    (hφ1 : ∀ x ∈ Ici a, Λ ≤ |deriv φ x|)
    (hφk : ∀ x ∈ Ici a, ∀ j ∈ ({1, 2, 3} : Finset ℕ),
      |iteratedDeriv (j + 1) φ x| ≤ K * (w x) ^ (-(j : ℤ)) * |deriv φ x|)
    (hhk : ∀ x ∈ Ici a, ∀ j ≤ 3, ‖iteratedDeriv j h x‖ ≤ B x * (w x) ^ (-(j : ℤ)))
    (hint_h : IntegrableOn (fun x => Complex.exp (Complex.I * (φ x : ℂ)) * h x) (Ioi a))
    (hBw_int : IntegrableOn (fun x => B x * (w x) ^ (-3 : ℤ)) (Ioi a))
    (hlim : ∀ (j : ℕ), j ≤ 2 → Tendsto (fun x => B x * (w x) ^ (-(j : ℤ))) atTop (𝓝 0)) :
    ‖∫ x in Ioi a, Complex.exp (Complex.I * (φ x : ℂ)) * h x‖ ≤
      (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioi a, B x * (w x) ^ (-3 : ℤ) := by
  let h1 := ibpStep φ h
  let h2 := ibpStep φ h1
  let h3 := ibpStep φ h2
  have hh1_cd : ContDiffOn ℝ 2 h1 U := contDiffOn_ibpStep (n := 2) hU (hφ.of_le (by norm_num)) hh hφ_ne
  have hh2_cd : ContDiffOn ℝ 1 h2 U := contDiffOn_ibpStep (n := 1) hU (hφ.of_le (by norm_num)) hh1_cd hφ_ne
  have hh3_cd : ContDiffOn ℝ 0 h3 U := contDiffOn_ibpStep (n := 0) hU (hφ.of_le (by norm_num)) hh2_cd hφ_ne
  have hvan_step : ∀ {f : ℝ → ℂ} {x : ℝ} {n : ℕ}, x ∈ U → n ≤ 1 →
      ContDiffOn ℝ (n + 1 : ℕ) f U → (∀ j ≤ n + 1, iteratedDeriv j f x = 0) →
      ∀ j ≤ n, iteratedDeriv j (ibpStep φ f) x = 0 := by
    intro f x n hxU hn hf hfv j hj
    have hdφ_cd : ContDiffAt ℝ 3 (deriv φ) x :=
      ((hφ.derivWithin hU.uniqueDiffOn (m := 3) (by norm_num)).congr
        fun t ht => (derivWithin_of_isOpen hU ht).symm).contDiffAt (hU.mem_nhds hxU)
    have hinv_cd : ContDiffAt ℝ 3 (fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (hdφ_cd.inv (hφ_ne x hxU))
    have heq_mul : (fun t => f t / ((deriv φ t : ℝ) : ℂ)) = f * fun t => (((deriv φ t)⁻¹ : ℝ) : ℂ) := by
      ext t; simp [div_eq_mul_inv]
    unfold ibpStep
    rw [heq_mul, ← iteratedDeriv_succ', iteratedDeriv_mul (n := j + 1)
      ((hf.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast (show j + 1 ≤ n + 1 by omega)))
      (hinv_cd.of_le (by exact_mod_cast (show j + 1 ≤ 3 by omega)))]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_le : i ≤ j + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hfv i (by omega), mul_zero, zero_mul]
  have haU : a ∈ U := hsub le_rfl
  have hh0_a : h a = 0 := by simpa using hvan_a 0 (by omega)
  have hh1_a : ∀ j ≤ 1, iteratedDeriv j h1 a = 0 := hvan_step haU le_rfl (hh.of_le (by norm_num)) hvan_a
  have hh2_a : h2 a = 0 := by
    simpa using hvan_step (n := 0) haU (by omega) (hh1_cd.of_le (by norm_num)) hh1_a 0 le_rfl
  -- Pointwise bounds on `h1, h2, h3` on `Ici a`
  have hb1 : ∀ x ∈ Ici a, ∀ j ≤ 2, ‖iteratedDeriv j h1 x‖ ≤ (104 * K ^ 3 * B x / (Λ * w x)) * (w x) ^ (-(j : ℤ)) :=
    fun x hx => ibpStep_deriv_bound (n := 2) le_rfl hU hφ hh (hsub hx) hΛ (hw_pos x hx) hK (hB_nn x hx)
      (hφ1 x hx) (hφk x hx) (hhk x hx)
  have hb2 : ∀ x ∈ Ici a, ∀ j ≤ 1, ‖iteratedDeriv j h2 x‖ ≤
      (104 * K ^ 3 * (104 * K ^ 3 * B x / (Λ * w x)) / (Λ * w x)) * (w x) ^ (-(j : ℤ)) :=
    fun x hx => ibpStep_deriv_bound (n := 1) (by omega) hU hφ hh1_cd (hsub hx) hΛ (hw_pos x hx) hK
      (by have := hB_nn x hx; have := hw_pos x hx; positivity) (hφ1 x hx) (hφk x hx) (hb1 x hx)
  have hb3 : ∀ x ∈ Ici a, ‖Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖ ≤
      (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * (B x * (w x) ^ (-3 : ℤ)) := by
    intro x hx
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    have b3 := ibpStep_deriv_bound (n := 0) (by omega) hU hφ hh2_cd (hsub hx) hΛ (hw_pos x hx) hK
      (by have := hB_nn x hx; have := hw_pos x hx; positivity) (hφ1 x hx) (hφk x hx) (hb2 x hx) 0 le_rfl
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at b3
    refine b3.trans (le_of_eq ?_)
    have hw0 := (hw_pos x hx).ne'
    have hΛ0 := hΛ.ne'
    rw [show (w x) ^ (-3 : ℤ) = ((w x) ^ 3)⁻¹ by rw [zpow_neg]; norm_cast,
        show Λ ^ (-3 : ℤ) = (Λ ^ 3)⁻¹ by rw [zpow_neg]; norm_cast]
    field_simp [hw0, hΛ0]
  -- Show `‖∫ x in a..R, ...‖` converges to `‖∫ x in Ioi a, ...‖` and is bounded by `C * ∫_a^R + boundary(R)`
  have htend_lhs : Tendsto (fun R => ‖∫ x in a..R, Complex.exp (Complex.I * (φ x : ℂ)) * h x‖)
      atTop (𝓝 ‖∫ x in Ioi a, Complex.exp (Complex.I * (φ x : ℂ)) * h x‖) :=
    (intervalIntegral_tendsto_integral_Ioi a hint_h tendsto_id).norm
  have hbd_ev : ∀ᶠ R in atTop,
      ‖∫ x in a..R, Complex.exp (Complex.I * (φ x : ℂ)) * h x‖ ≤
      ‖h R‖ / Λ + ‖h1 R‖ / Λ + ‖h2 R‖ / Λ +
      (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioi a, B x * (w x) ^ (-3 : ℤ) := by
    filter_upwards [eventually_ge_atTop a] with R hR
    have hsubR : Icc a R ⊆ U := fun x hx => hsub hx.1
    have step1 := ibpStep_integral hR hU hsubR (hφ.of_le (by norm_num)) (hh.of_le (by norm_num)) hφ_ne
    have step2 := ibpStep_integral hR hU hsubR (hφ.of_le (by norm_num)) (hh1_cd.of_le (by norm_num)) hφ_ne
    have step3 := ibpStep_integral hR hU hsubR (hφ.of_le (by norm_num)) hh2_cd hφ_ne
    rw [hh0_a, zero_div, mul_zero, sub_zero] at step1
    rw [show h1 a = 0 from by simpa using hh1_a 0 (by omega), zero_div, mul_zero, sub_zero] at step2
    rw [hh2_a, zero_div, mul_zero, sub_zero] at step3
    rw [step1, step2, step3]
    have hbd_term : ∀ (f : ℝ → ℂ),
        ‖Complex.exp (Complex.I * (φ R : ℂ)) * (f R / (Complex.I * ((deriv φ R : ℝ) : ℂ)))‖ ≤ ‖f R‖ / Λ := by
      intro f
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, norm_div, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hΛ (hφ1 R hR)
    have hbd_int : ‖∫ x in a..R, Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖ ≤
        (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioi a, B x * (w x) ^ (-3 : ℤ) := by
      have hcont : ContinuousOn (fun x => Complex.exp (Complex.I * (φ x : ℂ)) * h3 x) (Icc a R) :=
        ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp_continuousOn
          (hφ.continuousOn.mono hsubR)).mul (hh3_cd.continuousOn.mono hsubR)
      calc ‖∫ x in a..R, Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖
          ≤ ∫ x in a..R, ‖Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖ :=
            intervalIntegral.norm_integral_le_integral_norm hR
        _ ≤ ∫ x in a..R, (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * (B x * (w x) ^ (-3 : ℤ)) := by
            refine intervalIntegral.integral_mono_on hR (hcont.norm.intervalIntegrable_of_Icc hR) ?_
              (fun x hx => hb3 x hx.1)
            exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
              (hBw_int.mono_set Ioc_subset_Ioi_self)).const_mul _
        _ = (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioc a R, B x * (w x) ^ (-3 : ℤ) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hR]
        _ ≤ (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioi a, B x * (w x) ^ (-3 : ℤ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact setIntegral_mono_set hBw_int (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
              mul_nonneg (hB_nn x (le_of_lt hx)) (zpow_nonneg (hw_pos x (le_of_lt hx)).le _))
              (Eventually.of_forall Ioc_subset_Ioi_self)
    calc ‖Complex.exp (Complex.I * (φ R : ℂ)) * (h R / (Complex.I * ((deriv φ R : ℝ) : ℂ))) +
          Complex.I * (Complex.exp (Complex.I * (φ R : ℂ)) * (h1 R / (Complex.I * ((deriv φ R : ℝ) : ℂ))) +
          Complex.I * (Complex.exp (Complex.I * (φ R : ℂ)) * (h2 R / (Complex.I * ((deriv φ R : ℝ) : ℂ))) +
          Complex.I * ∫ x in a..R, Complex.exp (Complex.I * (φ x : ℂ)) * h3 x))‖
        ≤ ‖Complex.exp (Complex.I * (φ R : ℂ)) * (h R / (Complex.I * ((deriv φ R : ℝ) : ℂ)))‖ +
          (‖Complex.exp (Complex.I * (φ R : ℂ)) * (h1 R / (Complex.I * ((deriv φ R : ℝ) : ℂ)))‖ +
          (‖Complex.exp (Complex.I * (φ R : ℂ)) * (h2 R / (Complex.I * ((deriv φ R : ℝ) : ℂ)))‖ +
          ‖∫ x in a..R, Complex.exp (Complex.I * (φ x : ℂ)) * h3 x‖)) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul, Complex.norm_I, one_mul]
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul, Complex.norm_I, one_mul]
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ‖h R‖ / Λ + ‖h1 R‖ / Λ + ‖h2 R‖ / Λ +
          (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioi a, B x * (w x) ^ (-3 : ℤ) := by
          linarith [hbd_term h, hbd_term h1, hbd_term h2, hbd_int]
  have htend_rhs : Tendsto (fun R => ‖h R‖ / Λ + ‖h1 R‖ / Λ + ‖h2 R‖ / Λ +
      (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioi a, B x * (w x) ^ (-3 : ℤ))
      atTop (𝓝 (0 + 0 + 0 + (104 * K ^ 3) ^ 3 * Λ ^ (-3 : ℤ) * ∫ x in Ioi a, B x * (w x) ^ (-3 : ℤ))) := by
    have ht0 : Tendsto (fun R => ‖h R‖ / Λ) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun R => by positivity) ?_
        (by simpa using (hlim 0 (by omega)).div_const Λ)
      filter_upwards [eventually_ge_atTop a] with R hR
      have := hhk R hR 0 (by omega)
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at this
      exact div_le_div_of_nonneg_right this hΛ.le
    have ht1 : Tendsto (fun R => ‖h1 R‖ / Λ) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun R => by positivity) ?_
        (by simpa using ((hlim 1 (by omega)).const_mul (104 * K ^ 3 / Λ ^ 2)))
      filter_upwards [eventually_ge_atTop a] with R hR
      have := hb1 R hR 0 (by omega)
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at this
      have hw0 := (hw_pos R hR).ne'
      have hΛ0 := hΛ.ne'
      calc ‖h1 R‖ / Λ ≤ (104 * K ^ 3 * B R / (Λ * w R)) / Λ := div_le_div_of_nonneg_right this hΛ.le
        _ = 104 * K ^ 3 / Λ ^ 2 * (B R * (w R)⁻¹) := by field_simp [hw0, hΛ0]
    have ht2 : Tendsto (fun R => ‖h2 R‖ / Λ) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun R => by positivity) ?_
        (by simpa using ((hlim 2 (by omega)).const_mul ((104 * K ^ 3) ^ 2 / Λ ^ 3)))
      filter_upwards [eventually_ge_atTop a] with R hR
      have := hb2 R hR 0 (by omega)
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at this
      have hw0 := (hw_pos R hR).ne'
      have hΛ0 := hΛ.ne'
      calc ‖h2 R‖ / Λ ≤ (104 * K ^ 3 * (104 * K ^ 3 * B R / (Λ * w R)) / (Λ * w R)) / Λ :=
            div_le_div_of_nonneg_right this hΛ.le
        _ = (104 * K ^ 3) ^ 2 / Λ ^ 3 * (B R * (w R) ^ (-2 : ℤ)) := by
            rw [show (w R) ^ (-2 : ℤ) = ((w R) ^ 2)⁻¹ by rw [zpow_neg]; norm_cast]
            field_simp [hw0, hΛ0]
    exact ((ht0.add ht1).add ht2).add tendsto_const_nhds
  simpa using le_of_tendsto_of_tendsto htend_lhs htend_rhs hbd_ev

end FormalResearch.SignUncertainty.FctCuspEdge
