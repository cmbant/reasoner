/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpLeftTailMid
public import FormalResearch.SignUncertainty.FctPhysicalBudgetConcrete

/-!
# Left-tail oscillatory error: shared VdC/splitting helpers and Mid-band bound (`fct:warp-asymp`)

Leaf helper module for `FctPhysicalPositive.lean` and `FctWarpLeftTailFar.lean`:
* `hankelEdgeM_ge_sq_sub_quartic`, `physDelta_ge`, `hankelEdgeM_two_sub_three_self`:
  sharp lower bounds on `hankelEdgeM` near `0` via `stripG_sub_le`.
* `integral_real_split_two_sides`: splits `∫_ℝ f` into `Ioc (-r) r`, `Ioi r`, and reflected `Ioi r`.
* `vdc1_Ioi_edgePhi`, `vdc1_Ioi_neg_edgePhi`: `van_der_corput_first` wrappers on `Ioi a`.
* `warpAmpLeft_deriv_L1_on_tail`: uniform `L¹` and `L^∞` bounds on `warpAmpLeft` over `Ioi r`.
* `warpLeftTailDensity_mid_bound`: `|warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-(15 / 8 : ℝ))`
  on the Mid-band `L ≤ 3 * physDelta c`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.Analysis FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctCuspEdge

namespace FormalResearch.SignUncertainty

/-! ### Quantitative `hankelEdgeM` lower bounds near `0` -/

lemma edgePhiDeriv_eq_sub_hankelEdgeM {L τ : ℝ} (hτ : 0 ≤ τ) :
    edgePhiDeriv L τ = L - hankelEdgeM τ := by
  unfold edgePhiDeriv hankelEdgeM ceEll
  split_ifs with h0
  · subst h0; simp
  · rw [abs_of_nonneg hτ, ← inv_div (π * τ / 2), Real.log_inv]; ring

lemma edgePhiDeriv_antitoneOn_nonneg (L : ℝ) : AntitoneOn (edgePhiDeriv L) (Ici 0) := by
  intro x hx y hy hxy
  rw [edgePhiDeriv_eq_sub_hankelEdgeM (mem_Ici.mp hx), edgePhiDeriv_eq_sub_hankelEdgeM (mem_Ici.mp hy)]
  exact sub_le_sub_left (hankelEdgeM_strictMonoOn.monotoneOn hx hy hxy) L

lemma hankelEdgeM_ge_sq_sub_quartic {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ14 : τ ≤ 1 / 4) :
    π ^ 2 / 12 * τ ^ 2 - 10 * τ ^ 4 ≤ hankelEdgeM τ := by
  rcases eq_or_lt_of_le hτ0 with rfl | hτpos
  · simp [hankelEdgeM_zero]
  have hz : ‖(τ : ℂ) * Complex.I‖ ≤ 1 / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos hτpos]
    exact hτ14
  have hsg := stripG_sub_le hz
  rw [stripG_imag_eq_neg_m hτpos.ne', abs_of_pos hτpos] at hsg
  have heq : (-↑(hankelEdgeM τ) : ℂ) - (↑π : ℂ) ^ 2 / 12 * ((τ : ℂ) * Complex.I) ^ 2 =
      ((π ^ 2 / 12 * τ ^ 2 - hankelEdgeM τ : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  have hnorm : ‖((τ : ℂ) * Complex.I)‖ = τ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos hτpos]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, hnorm] at hsg
  linarith [(abs_le.mp hsg).2]

lemma physDelta_eq_hankelEdgeM {c : ℝ} (_hc : 0 ≤ c) :
    FctSym.physDelta c = hankelEdgeM (c ^ (-(1 / 4 : ℝ))) := by
  unfold FctSym.physDelta hankelEdgeM uctM
  rfl

lemma physDelta_ge {c : ℝ} (hc : 32 ^ 4 ≤ c) :
    (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) ≤ FctSym.physDelta c := by
  have hcpos : 0 < c := by positivity
  set t := c ^ (-(1 / 4 : ℝ))
  have htpos : 0 < t := Real.rpow_pos_of_pos hcpos _
  have ht32 : t ≤ 1 / 32 := by
    dsimp [t]
    rw [Real.rpow_neg hcpos.le]
    have hpow : (32 : ℝ) ≤ c ^ (1 / 4 : ℝ) := by
      have h1 : (32 : ℝ) = (32 ^ 4 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (32 : ℝ) 4, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) hc (by norm_num)
    calc (c ^ (1 / 4 : ℝ))⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by positivity) hpow
      _ = 1 / 32 := by rw [← one_div]
  have hsq : t ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]; congr 1; norm_num
  have hM := hankelEdgeM_ge_sq_sub_quartic htpos.le (by linarith)
  have hpi : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have ht4 : t ^ 4 ≤ (1 / 32) ^ 2 * t ^ 2 := by
    have : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ htpos.le ht32 2) (sq_nonneg t)
  rw [physDelta_eq_hankelEdgeM hcpos.le, ← hsq]
  nlinarith

lemma hankelEdgeM_two_sub_three_self {t : ℝ} (ht0 : 0 ≤ t) (ht32 : t ≤ 1 / 32) :
    (1 / 2 : ℝ) * t ^ 2 ≤ hankelEdgeM (2 * t) - 3 * hankelEdgeM t := by
  have h2t := hankelEdgeM_ge_sq_sub_quartic (τ := 2 * t) (by linarith) (by linarith)
  have ht := hankelEdgeM_le_sq ht0
  have hpi_t : 3 / 4 * t ^ 2 ≤ π ^ 2 / 12 * t ^ 2 := by
    have hpi : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    linarith [show (9 / 12 : ℝ) = 3 / 4 by norm_num, mul_le_mul_of_nonneg_right hpi (sq_nonneg t)]
  have h4sq : π ^ 2 / 12 * (2 * t) ^ 2 = 4 * (π ^ 2 / 12 * t ^ 2) := by ring
  have ht4 : (2 * t) ^ 4 ≤ (1 / 64 : ℝ) * t ^ 2 := by
    have : (2 * t) ^ 4 = 16 * t ^ 2 * t ^ 2 := by ring
    rw [this]
    have ht2 : t ^ 2 ≤ (1 / 32 : ℝ) ^ 2 := pow_le_pow_left₀ ht0 ht32 2
    nlinarith [sq_nonneg t]
  rw [h4sq] at h2t
  calc (1 / 2 : ℝ) * t ^ 2
      ≤ (3 / 4 : ℝ) * t ^ 2 - 10 * ((1 / 64 : ℝ) * t ^ 2) := by nlinarith [sq_nonneg t]
    _ ≤ π ^ 2 / 12 * t ^ 2 - 10 * (2 * t) ^ 4 := by linarith
    _ = 4 * (π ^ 2 / 12 * t ^ 2) - 10 * (2 * t) ^ 4 - 3 * (π ^ 2 / 12 * t ^ 2) := by ring
    _ ≤ hankelEdgeM (2 * t) - 3 * hankelEdgeM t := by linarith

/-! ### Exponential decay helpers and real-line integral splitting -/

lemma integrable_pow_mul_exp_neg_pi (N : ℕ) :
    Integrable (fun τ : ℝ => (1 + |τ|) ^ N * Real.exp (-(π * |τ|))) := by
  obtain ⟨K, hK0, hK⟩ := poly_exp_le_n (N + 2)
  refine (integrable_inv_one_add_abs_sq.const_mul K).mono' ?_ (ae_of_all _ fun τ => ?_)
  · exact (((continuous_const.add continuous_abs).pow N).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)).aestronglyMeasurable
  · have hx0 : 0 ≤ |τ| := abs_nonneg τ
    have h1x : 0 < 1 + |τ| := by linarith
    have hb := hK |τ| hx0
    have hnn : 0 ≤ (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) := by positivity
    rw [Real.norm_of_nonneg hnn]
    rw [show K * (1 / (1 + |τ|) ^ 2) = K / (1 + |τ|) ^ 2 by ring, le_div_iff₀ (by positivity)]
    calc (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) * (1 + |τ|) ^ 2
        = (1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)) := by ring
      _ ≤ K := hb

lemma poly14_exp_le {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ 14 * Real.exp (-(π * x)) ≤ 3 * (Nat.factorial 15 : ℝ) := by
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
  have hexp_dec : Real.exp (1 + x) * Real.exp (-(π * x)) ≤ 3 := by
    rw [← Real.exp_add]
    have harg : 1 + x + -(π * x) ≤ 1 := by nlinarith [Real.pi_gt_three]
    have he1 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.le).trans (by norm_num)
    exact (Real.exp_le_exp.mpr harg).trans he1
  calc (1 + x) ^ 14 * Real.exp (-(π * x))
      ≤ ((Nat.factorial 15 : ℝ) * Real.exp (1 + x)) * Real.exp (-(π * x)) :=
        mul_le_mul_of_nonneg_right hexp_15 (Real.exp_pos _).le
    _ = (Nat.factorial 15 : ℝ) * (Real.exp (1 + x) * Real.exp (-(π * x))) := by ring
    _ ≤ (Nat.factorial 15 : ℝ) * 3 := mul_le_mul_of_nonneg_left hexp_dec (Nat.cast_nonneg _)
    _ = 3 * (Nat.factorial 15 : ℝ) := by ring

lemma integral_real_split_two_sides {f : ℝ → ℂ} (hf : Integrable f) {r : ℝ} (hr : 0 < r) :
    ∫ τ : ℝ, f τ =
      (∫ τ in Ioc (-r) r, f τ) + (∫ τ in Ioi r, f τ) + (∫ τ in Ioi r, f (-τ)) := by
  have h1 : ∫ τ : ℝ, f τ = (∫ τ in Iic r, f τ) + ∫ τ in Ioi r, f τ :=
    (intervalIntegral.integral_Iic_add_Ioi (b := r) hf.integrableOn hf.integrableOn).symm
  have hf_iic : IntegrableOn f (Iic r) := hf.integrableOn
  have hdisj : Disjoint (Iic (-r)) (Ioc (-r) r) := by
    rw [Set.disjoint_iff_forall_ne]
    intro x hx y hy hxy
    subst hxy
    linarith [mem_Iic.mp hx, (mem_Ioc.mp hy).1]
  have hunion : Iic (-r) ∪ Ioc (-r) r = Iic r := Iic_union_Ioc_eq_Iic (by linarith)
  have h2 : ∫ τ in Iic r, f τ = (∫ τ in Iic (-r), f τ) + ∫ τ in Ioc (-r) r, f τ := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioc
      (hf_iic.mono_set (hunion ▸ subset_union_left))
      (hf_iic.mono_set (hunion ▸ subset_union_right))
  have hneg : ∫ τ in Iic (-r), f τ = ∫ τ in Ioi r, f (-τ) :=
    (integral_comp_neg_Ioi r f).symm
  rw [h1, h2, hneg]; ring

/-! ### Reusable `van_der_corput_first` wrappers on `Ioi a` -/

lemma vdc_variation_on_Icc {amp : ℝ → ℂ} {a T V : ℝ} (haT : a ≤ T) (ha : 0 < a)
    (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hV : ∫ x in Icc a T, ‖deriv amp x‖ ≤ V) :
    BoundedVariationOn amp (Icc a T) ∧ (eVariationOn amp (Icc a T)).toReal ≤ V := by
  have hIcc : Icc a T ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hd : ∀ x ∈ Icc a T, HasDerivAt amp (deriv amp x) x := fun x hx =>
    ((hCD.contDiffAt (isOpen_Ioi.mem_nhds (hIcc hx))).differentiableAt (by norm_num)).hasDerivAt
  have hderiv_cont : ContinuousOn (deriv amp) (Ioi 0) :=
    (hCD.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
      fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm
  have hci : IntervalIntegrable (deriv amp) volume a T :=
    (hderiv_cont.mono hIcc).intervalIntegrable_of_Icc haT
  have hev := eVariationOn_le_integral_norm_deriv haT hd hci
  have hX : ∫ t in a..T, ‖deriv amp t‖ ≤ V := by
    rw [intervalIntegral.integral_of_le haT, ← integral_Icc_eq_integral_Ioc]
    exact hV
  have hX0 : 0 ≤ ∫ t in a..T, ‖deriv amp t‖ :=
    intervalIntegral.integral_nonneg haT fun t _ => norm_nonneg _
  have hV0 : 0 ≤ V := hX0.trans hX
  have hne : eVariationOn amp (Icc a T) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hev
  exact ⟨hne, ENNReal.toReal_le_of_le_ofReal hV0 (hev.trans (ENNReal.ofReal_le_ofReal hX))⟩

lemma vdc1_Ioi_edgePhi {a L c lam M_bd V_bd : ℝ} (ha : 0 < a) (hc : 0 < c) (hlam : 0 < lam)
    (_hM0 : 0 ≤ M_bd) (_hV0 : 0 ≤ V_bd) {amp : ℝ → ℂ}
    (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hInt : IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) (Ioi a))
    (hLam : ∀ x ∈ Ici a, lam ≤ |edgePhiDeriv L x|)
    (hM : ∀ x ∈ Ici a, ‖amp x‖ ≤ M_bd)
    (hV : ∀ T : ℝ, a ≤ T → ∫ x in Icc a T, ‖deriv amp x‖ ≤ V_bd) :
    ‖∫ τ in Ioi a, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
      3 * (M_bd + V_bd) / (c * lam) := by
  have htend := intervalIntegral_tendsto_integral_Ioi a hInt tendsto_id
  refine le_of_tendsto htend.norm ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  have hIcc_pos : Icc a T ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hφ : ∀ y ∈ Icc a T, HasDerivAt (edgePhi L) (edgePhiDeriv L y) y := fun y _ =>
    hasDerivAt_edgePhi L y
  have hφ'_cont : ContinuousOn (edgePhiDeriv L) (Icc a T) :=
    (contDiff_edgePhiDeriv L).continuous.continuousOn
  have hφ'_mono : MonotoneOn (edgePhiDeriv L) (Icc a T) ∨ AntitoneOn (edgePhiDeriv L) (Icc a T) :=
    Or.inr ((edgePhiDeriv_antitoneOn_nonneg L).mono fun x hx => le_trans ha.le hx.1)
  have hφ'_lb : ∀ y ∈ Icc a T, lam ≤ |edgePhiDeriv L y| := fun y hy => hLam y hy.1
  have hamp_cont : ContinuousOn amp (Icc a T) := hCD.continuousOn.mono hIcc_pos
  obtain ⟨hamp_bv, hamp_var⟩ := vdc_variation_on_Icc hT ha hCD (hV T hT)
  have hamp_bd : ∀ y ∈ Icc a T, ‖amp y‖ ≤ M_bd := fun y hy => hM y hy.1
  have hvdc := van_der_corput_first hT hc hlam hφ hφ'_cont hφ'_mono hφ'_lb hamp_cont hamp_bv hamp_bd
  have hden : 0 < c * lam := mul_pos hc hlam
  refine hvdc.trans ?_
  gcongr

lemma edgePhiDeriv_neg (L τ : ℝ) : edgePhiDeriv L (-τ) = edgePhiDeriv L τ := by
  unfold edgePhiDeriv
  simp only [abs_neg, neg_eq_zero]

lemma vdc1_Ioi_neg_edgePhi {a L c lam M_bd V_bd : ℝ} (ha : 0 < a) (hc : 0 < c) (hlam : 0 < lam)
    (_hM0 : 0 ≤ M_bd) (_hV0 : 0 ≤ V_bd) {amp : ℝ → ℂ}
    (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hInt : IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-τ) : ℂ))) (Ioi a))
    (hLam : ∀ x ∈ Ici a, lam ≤ |edgePhiDeriv L x|)
    (hM : ∀ x ∈ Ici a, ‖amp x‖ ≤ M_bd)
    (hV : ∀ T : ℝ, a ≤ T → ∫ x in Icc a T, ‖deriv amp x‖ ≤ V_bd) :
    ‖∫ τ in Ioi a, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-τ) : ℂ))‖ ≤
      3 * (M_bd + V_bd) / (c * lam) := by
  have htend := intervalIntegral_tendsto_integral_Ioi a hInt tendsto_id
  refine le_of_tendsto htend.norm ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  have hIcc_pos : Icc a T ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hφ : ∀ y ∈ Icc a T, HasDerivAt (fun x => edgePhi L (-x)) (-edgePhiDeriv L y) y := by
    intro y _
    have h1 := (hasDerivAt_edgePhi L (-y)).scomp y (hasDerivAt_neg y)
    simpa [Function.comp_def, edgePhiDeriv_neg L y] using h1
  have hφ'_cont : ContinuousOn (fun y => -edgePhiDeriv L y) (Icc a T) :=
    (contDiff_edgePhiDeriv L).continuous.neg.continuousOn
  have hφ'_mono :
      MonotoneOn (fun y => -edgePhiDeriv L y) (Icc a T) ∨
      AntitoneOn (fun y => -edgePhiDeriv L y) (Icc a T) := by
    left
    intro x hx y hy hxy
    exact neg_le_neg ((edgePhiDeriv_antitoneOn_nonneg L) (le_trans ha.le hx.1) (le_trans ha.le hy.1) hxy)
  have hφ'_lb : ∀ y ∈ Icc a T, lam ≤ |-edgePhiDeriv L y| := fun y hy => by
    rw [abs_neg]; exact hLam y hy.1
  have hamp_cont : ContinuousOn amp (Icc a T) := hCD.continuousOn.mono hIcc_pos
  obtain ⟨hamp_bv, hamp_var⟩ := vdc_variation_on_Icc hT ha hCD (hV T hT)
  have hamp_bd : ∀ y ∈ Icc a T, ‖amp y‖ ≤ M_bd := fun y hy => hM y hy.1
  have hvdc := van_der_corput_first hT hc hlam hφ hφ'_cont hφ'_mono hφ'_lb hamp_cont hamp_bv hamp_bd
  have hden : 0 < c * lam := mul_pos hc hlam
  refine hvdc.trans ?_
  gcongr

/-! ### Uniform `L^∞` and `L^1` variation bounds for `warpAmpLeft` on `Ioi a` -/

lemma warpAmpLeft_M_V_tail_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ M0 V0 c₀ : ℝ, 0 < M0 ∧ 0 < V0 ∧ 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ (a : ℝ), 0 < a →
        (∀ x ∈ Ici a, ‖warpAmpLeft h ε c ξ x‖ ≤ M0 * c⁻¹ ∧ ‖warpAmpLeft h ε c ξ (-x)‖ ≤ M0 * c⁻¹) ∧
        (∀ T : ℝ, a ≤ T →
          ∫ x in Icc a T, ‖deriv (warpAmpLeft h ε c ξ) x‖ ≤ V0 * c⁻¹ ∧
          ∫ x in Icc a T, ‖deriv (fun t => warpAmpLeft h ε c ξ (-t)) x‖ ≤ V0 * c⁻¹) := by
  obtain ⟨C, c₀, hC0, hc0, hB⟩ := warpAmpLeft_bounds hK4 h
  set I14 : ℝ := ∫ τ : ℝ, (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|))
  have hI14_int : Integrable (fun τ : ℝ => (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|))) :=
    integrable_pow_mul_exp_neg_pi 14
  have hI14_nn : 0 ≤ I14 := integral_nonneg fun τ => by positivity
  set C1 : ℝ := max C 1
  have hC1 : 0 < C1 := by positivity
  set M0 : ℝ := C1 * (3 * (Nat.factorial 15 : ℝ))
  set V0 : ℝ := C1 * (1 / 2 + I14)
  refine ⟨M0, V0, c₀, by positivity, by positivity, hc0, fun ε c ξ hε hc a ha => ?_⟩
  obtain ⟨hCD, hNear, hOuter⟩ := hB ε c ξ hε hc
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one (hc0.trans hc)
  have hCC1 : C ≤ C1 := le_max_left C 1
  have hpt_M : ∀ t : ℝ, t ≠ 0 → ‖warpAmpLeft h ε c ξ t‖ ≤ M0 * c⁻¹ := by
    intro t ht
    rcases le_or_gt |t| (1 / 16) with ht16 | ht16
    · have h0 := (hNear t ht ht16).1
      have hrp : |t| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg t) (by linarith) (by norm_num)
      have h315 : (1 : ℝ) ≤ 3 * (Nat.factorial 15 : ℝ) := by norm_num
      calc ‖warpAmpLeft h ε c ξ t‖ ≤ C * c⁻¹ * |t| ^ (1 / 2 : ℝ) := h0
        _ ≤ C1 * c⁻¹ * 1 := by gcongr
        _ ≤ C1 * c⁻¹ * (3 * (Nat.factorial 15 : ℝ)) := by gcongr
        _ = M0 * c⁻¹ := by simp only [M0]; ring
    · have h0 := (hOuter t ht16.le).1
      have hpe := poly14_exp_le (abs_nonneg t)
      calc ‖warpAmpLeft h ε c ξ t‖ ≤ C * c⁻¹ * ((1 + |t|) ^ 14 * Real.exp (-(π * |t|))) := by
            linarith [show C * c⁻¹ * (1 + |t|) ^ 14 * Real.exp (-(π * |t|)) =
              C * c⁻¹ * ((1 + |t|) ^ 14 * Real.exp (-(π * |t|))) by ring]
        _ ≤ C1 * c⁻¹ * (3 * (Nat.factorial 15 : ℝ)) := by gcongr
        _ = M0 * c⁻¹ := by simp only [M0]; ring
  have hM : ∀ x ∈ Ici a, ‖warpAmpLeft h ε c ξ x‖ ≤ M0 * c⁻¹ ∧ ‖warpAmpLeft h ε c ξ (-x)‖ ≤ M0 * c⁻¹ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx
    exact ⟨hpt_M x hxpos.ne', hpt_M (-x) (neg_ne_zero.mpr hxpos.ne')⟩
  set g_near : ℝ → ℝ := (Ioc (0 : ℝ) (1 / 16)).indicator (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
  set g_far : ℝ → ℝ := fun x => (1 + |x|) ^ 14 * Real.exp (-(π * |x|))
  have hg_near_int : Integrable g_near := by
    have hii : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 (1 / 16) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hii
    exact hii.integrable_indicator measurableSet_Ioc
  have hg_near_val : ∫ x : ℝ, g_near x = 1 / 2 := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      integral_rpow (Or.inl (by norm_num))]
    have hpow : (1 / 16 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 1 / 4 := by
      rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, show (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ 2 by norm_num,
        ← Real.rpow_natCast (1 / 4 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hpow, Real.zero_rpow (by norm_num)]
    norm_num
  have hdom_int : Integrable (fun x : ℝ => C1 * c⁻¹ * (g_near x + g_far x)) :=
    (hg_near_int.add hI14_int).const_mul (C1 * c⁻¹)
  have hdom_val : ∫ x : ℝ, C1 * c⁻¹ * (g_near x + g_far x) = V0 * c⁻¹ := by
    rw [integral_const_mul, integral_add hg_near_int hI14_int, hg_near_val]
    simp only [V0, I14, g_far]; ring
  have hderiv_neg_norm : ∀ x : ℝ, x ≠ 0 →
      ‖deriv (fun t => warpAmpLeft h ε c ξ (-t)) x‖ = ‖deriv (warpAmpLeft h ε c ξ) (-x)‖ := by
    intro x hx
    have hnx : -x ∈ {τ : ℝ | τ ≠ 0} := neg_ne_zero.mpr hx
    have h1 : HasDerivAt (warpAmpLeft h ε c ξ) (deriv (warpAmpLeft h ε c ξ) (-x)) (-x) :=
      ((hCD.contDiffAt (isOpen_ne.mem_nhds hnx)).differentiableAt (by norm_num)).hasDerivAt
    have h2 := h1.scomp x (hasDerivAt_neg x)
    change ‖deriv (warpAmpLeft h ε c ξ ∘ Neg.neg) x‖ = ‖deriv (warpAmpLeft h ε c ξ) (-x)‖
    rw [h2.deriv, norm_smul]
    simp
  have hpt_deriv : ∀ x : ℝ, 0 < x →
      ‖deriv (warpAmpLeft h ε c ξ) x‖ ≤ C1 * c⁻¹ * (g_near x + g_far x) ∧
      ‖deriv (fun t => warpAmpLeft h ε c ξ (-t)) x‖ ≤ C1 * c⁻¹ * (g_near x + g_far x) := by
    intro x hxpos
    have hgf0 : 0 ≤ g_far x := by positivity
    have hgn0 : 0 ≤ g_near x := Set.indicator_nonneg (fun _ hy => Real.rpow_nonneg (mem_Ioc.mp hy).1.le _) x
    have hbd_both : ∀ t : ℝ, |t| = x →
        ‖deriv (warpAmpLeft h ε c ξ) t‖ ≤ C1 * c⁻¹ * (g_near x + g_far x) := by
      intro t ht
      have htne : t ≠ 0 := abs_pos.mp (ht ▸ hxpos)
      rcases le_or_gt x (1 / 16) with hx16 | hx16
      · have hd1 := (hNear t htne (ht ▸ hx16)).2.1
        have hmem : x ∈ Ioc (0 : ℝ) (1 / 16) := ⟨hxpos, hx16⟩
        have hgn : g_near x = x ^ (-(1 / 2 : ℝ)) := Set.indicator_of_mem hmem _
        rw [ht] at hd1
        calc ‖deriv (warpAmpLeft h ε c ξ) t‖ ≤ C * c⁻¹ * x ^ (-(1 / 2 : ℝ)) := hd1
          _ ≤ C1 * c⁻¹ * g_near x := by rw [hgn]; gcongr
          _ ≤ C1 * c⁻¹ * (g_near x + g_far x) := by
              apply mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hgf0) (by positivity)
      · have hd1 := (hOuter t (ht ▸ hx16.le)).2.1
        rw [ht] at hd1
        have hgf_eq : g_far x = (1 + x) ^ 14 * Real.exp (-(π * x)) := by
          simp only [g_far, abs_of_pos hxpos]
        calc ‖deriv (warpAmpLeft h ε c ξ) t‖ ≤ C * c⁻¹ * g_far x := by
              rw [hgf_eq]; linarith [show C * c⁻¹ * (1 + x) ^ 14 * Real.exp (-(π * x)) =
                C * c⁻¹ * ((1 + x) ^ 14 * Real.exp (-(π * x))) by ring]
          _ ≤ C1 * c⁻¹ * g_far x := by gcongr
          _ ≤ C1 * c⁻¹ * (g_near x + g_far x) := by
              apply mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hgn0) (by positivity)
    refine ⟨hbd_both x (abs_of_pos hxpos), ?_⟩
    rw [hderiv_neg_norm x hxpos.ne']
    exact hbd_both (-x) (by rw [abs_neg, abs_of_pos hxpos])
  have hV : ∀ T : ℝ, a ≤ T →
      ∫ x in Icc a T, ‖deriv (warpAmpLeft h ε c ξ) x‖ ≤ V0 * c⁻¹ ∧
      ∫ x in Icc a T, ‖deriv (fun t => warpAmpLeft h ε c ξ (-t)) x‖ ≤ V0 * c⁻¹ := by
    intro T _
    have hIcc_pos : ∀ x ∈ Icc a T, 0 < x := fun x hx => lt_of_lt_of_le ha hx.1
    have hcd1 : ContDiffOn ℝ 1 (warpAmpLeft h ε c ξ) (Ioi 0) :=
      (hCD.of_le (by norm_num)).mono fun x hx => (mem_Ioi.mp hx).ne'
    have hcd1_neg : ContDiffOn ℝ 1 (fun t => warpAmpLeft h ε c ξ (-t)) (Ioi 0) :=
      (hCD.of_le (by norm_num)).comp contDiff_neg.contDiffOn fun x hx => neg_ne_zero.mpr (mem_Ioi.mp hx).ne'
    have hcont1 : ContinuousOn (fun x => ‖deriv (warpAmpLeft h ε c ξ) x‖) (Icc a T) := by
      have hc0' : ContinuousOn (deriv (warpAmpLeft h ε c ξ)) (Ioi 0) :=
        (hcd1.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
          fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm
      exact hc0'.norm.mono fun x hx => hIcc_pos x hx
    have hcont2 : ContinuousOn (fun x => ‖deriv (fun t => warpAmpLeft h ε c ξ (-t)) x‖) (Icc a T) := by
      have hc0' : ContinuousOn (deriv (fun t => warpAmpLeft h ε c ξ (-t))) (Ioi 0) :=
        (hcd1_neg.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
          fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm
      exact hc0'.norm.mono fun x hx => hIcc_pos x hx
    have hint1 : IntegrableOn (fun x => ‖deriv (warpAmpLeft h ε c ξ) x‖) (Icc a T) :=
      hcont1.integrableOn_Icc
    have hint2 : IntegrableOn (fun x => ‖deriv (fun t => warpAmpLeft h ε c ξ (-t)) x‖) (Icc a T) :=
      hcont2.integrableOn_Icc
    have hbound_int : ∫ x in Icc a T, C1 * c⁻¹ * (g_near x + g_far x) ≤ V0 * c⁻¹ := by
      rw [← hdom_val]
      exact setIntegral_le_integral hdom_int (Eventually.of_forall fun x => by
        have hgf0 : 0 ≤ g_far x := by positivity
        have hgn0 : 0 ≤ g_near x := Set.indicator_nonneg (fun _ hy => Real.rpow_nonneg (mem_Ioc.mp hy).1.le _) x
        positivity)
    refine ⟨?_, ?_⟩
    · refine (setIntegral_mono_on hint1 hdom_int.integrableOn measurableSet_Icc fun x hx =>
        (hpt_deriv x (hIcc_pos x hx)).1).trans hbound_int
    · refine (setIntegral_mono_on hint2 hdom_int.integrableOn measurableSet_Icc fun x hx =>
        (hpt_deriv x (hIcc_pos x hx)).2).trans hbound_int
  exact ⟨hM, hV⟩

/-! ### Mid-band left-tail bound (`L ≤ 3 * physDelta c`) -/

/-- On the Mid-band `L ≤ 3 * FctSym.physDelta c` (uniformly for all `0 < ξ` with
`Real.log (π² ξ) ≤ 3 * FctSym.physDelta c`), the left-tail density satisfies
`|warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-(15 / 8 : ℝ))`.

Ref: `fct:warp-asymp` (2) left-tail mid-band bound. -/
theorem warpLeftTailDensity_mid_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      Real.log (π ^ 2 * ξ) ≤ 3 * FctSym.physDelta c →
      |warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-(15 / 8 : ℝ)) := by
  obtain ⟨Cw, c0w, hCw0, hc0w, hW⟩ := warpAmpLeft_bounds hK4 h
  obtain ⟨M0, V0, c0MV, hM0_pos, hV0_pos, hc0MV, hMV⟩ := warpAmpLeft_M_V_tail_bounds hK4 h
  set c₀ : ℝ := max (32 ^ 4) (max c0w c0MV)
  set C_near : ℝ := (4 / 3 : ℝ) * 2 ^ (3 / 2 : ℝ) * Cw
  set C_tail : ℝ := 12 * (M0 + V0)
  set C : ℝ := |uctCAi| / (2 * π) * (C_near + C_tail)
  refine ⟨C, c₀, by positivity, le_max_left _ _, fun ε c ξ hε hc hξ hL => ?_⟩
  have hc32 : (32 : ℝ) ^ 4 ≤ c := (le_max_left _ _).trans hc
  have hcw : c0w ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcMV : c0MV ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hcpos : 0 < c := by positivity
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc32
  set L : ℝ := Real.log (π ^ 2 * ξ)
  set r : ℝ := 2 * c ^ (-(1 / 4 : ℝ))
  have hr_pos : 0 < r := by positivity
  have ht32 : c ^ (-(1 / 4 : ℝ)) ≤ 1 / 32 := by
    rw [Real.rpow_neg hcpos.le]
    have hpow : (32 : ℝ) ≤ c ^ (1 / 4 : ℝ) := by
      have h1 : (32 : ℝ) = (32 ^ 4 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (32 : ℝ) 4, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) hc32 (by norm_num)
    calc (c ^ (1 / 4 : ℝ))⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by positivity) hpow
      _ = 1 / 32 := by rw [← one_div]
  have hr16 : r ≤ 1 / 16 := by dsimp [r]; linarith
  set f_full : ℝ → ℂ := fun τ =>
    mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
        fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
        fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
        ctHG ε ((τ : ℂ) * Complex.I))
  have hf_eq : ∀ τ : ℝ, f_full τ =
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ := fun τ =>
    warpAmpLeft_eq_integrand h ε c ξ τ hξ
  obtain ⟨hW_cd, hW_near, hW_outer⟩ := hW ε c ξ hε hcw
  have hInt_full : Integrable f_full := by
    have heq : f_full = fun τ : ℝ =>
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ := by
      ext τ; exact hf_eq τ
    rw [heq]
    have hcont : ContinuousOn (fun τ : ℝ =>
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ) {τ : ℝ | τ ≠ 0} := by
      have hexp_c : Continuous (fun τ : ℝ => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) :=
        Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_edgePhi L).continuous))
      exact hexp_c.continuousOn.mul hW_cd.continuousOn
    have hae : AEStronglyMeasurable (fun τ : ℝ =>
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ) volume := by
      have hm : AEStronglyMeasurable (fun τ : ℝ =>
          Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ)
          (volume.restrict ({(0 : ℝ)}ᶜ)) :=
        hcont.aestronglyMeasurable isOpen_ne.measurableSet
      rwa [MeasureTheory.restrict_compl_singleton (0 : ℝ)] at hm
    set g_near_i : ℝ → ℝ := (Icc (-(1 / 16 : ℝ)) (1 / 16)).indicator (fun _ => Cw * c⁻¹)
    set g_far_i : ℝ → ℝ := fun τ => Cw * c⁻¹ * ((1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)))
    have hg_i : Integrable (fun τ : ℝ => g_near_i τ + g_far_i τ) := by
      have h1 : Integrable g_near_i :=
        (integrableOn_const (C := Cw * c⁻¹) (hs := measure_Icc_lt_top.ne)).integrable_indicator
          measurableSet_Icc
      have h2 : Integrable g_far_i := (integrable_pow_mul_exp_neg_pi 14).const_mul (Cw * c⁻¹)
      exact h1.add h2
    have hae0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
    refine hg_i.mono' hae ?_
    filter_upwards [hae0] with τ hτ
    rw [norm_mul, Complex.norm_exp]
    have hre : (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)).re = 0 := by
      rw [mul_assoc, Complex.I_mul_re, ← Complex.ofReal_mul, Complex.ofReal_im]; norm_num
    rw [hre, Real.exp_zero, one_mul]
    have hg1_nn : 0 ≤ g_near_i τ := Set.indicator_nonneg (fun _ _ => by positivity) τ
    have hg2_nn : 0 ≤ g_far_i τ := by positivity
    rcases le_or_gt |τ| (1 / 16) with h16 | h16
    · have hbd := (hW_near τ hτ h16).1
      have hrp1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) (by linarith) (by norm_num)
      have hmem : τ ∈ Icc (-(1 / 16 : ℝ)) (1 / 16) := abs_le.mp h16
      have hge : g_near_i τ = Cw * c⁻¹ := Set.indicator_of_mem hmem _
      calc ‖warpAmpLeft h ε c ξ τ‖ ≤ Cw * c⁻¹ * |τ| ^ (1 / 2 : ℝ) := hbd
        _ ≤ Cw * c⁻¹ * 1 := by gcongr
        _ = g_near_i τ + 0 := by rw [hge]; ring
        _ ≤ g_near_i τ + g_far_i τ := add_le_add le_rfl hg2_nn
    · have hbd := (hW_outer τ h16.le).1
      calc ‖warpAmpLeft h ε c ξ τ‖ ≤ Cw * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := hbd
        _ = 0 + g_far_i τ := by simp only [g_far_i]; ring
        _ ≤ g_near_i τ + g_far_i τ := add_le_add hg1_nn le_rfl
  have hsplit := integral_real_split_two_sides hInt_full hr_pos
  -- 1. Near-0 bound on `Ioc (-r) r`
  have h_near : ‖∫ τ in Ioc (-r) r, f_full τ‖ ≤ C_near * c ^ (-(11 / 8 : ℝ)) := by
    set g_bnd : ℝ → ℝ := fun τ => Cw * c⁻¹ * |τ| ^ (1 / 2 : ℝ)
    have hg_cont : ContinuousOn g_bnd (Icc (-r) r) :=
      (continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn
    have hg_int : IntegrableOn g_bnd (Ioc (-r) r) := hg_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hpt_near : ∀ᵐ τ ∂(volume.restrict (Ioc (-r) r)), ‖f_full τ‖ ≤ g_bnd τ := by
      have hae0 : ∀ᵐ τ : ℝ ∂(volume.restrict (Ioc (-r) r)), τ ≠ 0 := by
        rw [ae_restrict_iff' measurableSet_Ioc]
        have : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
        filter_upwards [this] with τ hτ _; exact hτ
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hae0] with τ hτmem hτne
      have hτr : |τ| ≤ r := abs_le.mpr ⟨(mem_Ioc.mp hτmem).1.le, (mem_Ioc.mp hτmem).2⟩
      rw [hf_eq τ, norm_mul, Complex.norm_exp]
      have hre : (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)).re = 0 := by
        rw [mul_assoc, Complex.I_mul_re, ← Complex.ofReal_mul, Complex.ofReal_im]; norm_num
      rw [hre, Real.exp_zero, one_mul]
      exact (hW_near τ hτne (hτr.trans hr16)).1
    have hnorm_le := norm_integral_le_of_norm_le hg_int hpt_near
    have hg_eval : ∫ τ in Ioc (-r) r, g_bnd τ = (4 / 3 : ℝ) * Cw * c⁻¹ * r ^ (3 / 2 : ℝ) := by
      rw [← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
      dsimp only [g_bnd]
      rw [intervalIntegral.integral_const_mul]
      have heven : ∫ τ in -r..r, |τ| ^ (1 / 2 : ℝ) = 2 * ∫ τ in 0..r, τ ^ (1 / 2 : ℝ) := by
        have hneg0 : ∫ τ in -r..0, |τ| ^ (1 / 2 : ℝ) = ∫ τ in 0..r, |τ| ^ (1 / 2 : ℝ) := by
          have := intervalIntegral.integral_comp_neg (fun τ : ℝ => |τ| ^ (1 / 2 : ℝ)) (a := (0 : ℝ)) (b := r)
          simpa using this.symm
        have hpos0 : ∫ τ in 0..r, |τ| ^ (1 / 2 : ℝ) = ∫ τ in 0..r, τ ^ (1 / 2 : ℝ) :=
          intervalIntegral.integral_congr fun τ hτ => by
            rw [abs_of_nonneg (uIcc_of_le hr_pos.le ▸ hτ).1]
        have hi1 : IntervalIntegrable (fun τ : ℝ => |τ| ^ (1 / 2 : ℝ)) volume (-r) 0 :=
          (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))).intervalIntegrable _ _
        have hi2 : IntervalIntegrable (fun τ : ℝ => |τ| ^ (1 / 2 : ℝ)) volume 0 r :=
          (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))).intervalIntegrable _ _
        rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hneg0, hpos0]; ring
      rw [heven, integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num)]
      norm_num; ring
    have hr32 : r ^ (3 / 2 : ℝ) = 2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 8 : ℝ)) := by
      dsimp [r]
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hcpos.le]
      congr 2; norm_num
    have hc_pow : c⁻¹ * c ^ (-(3 / 8 : ℝ)) = c ^ (-(11 / 8 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
    refine hnorm_le.trans ?_
    rw [hg_eval, hr32]
    exact (calc (4 / 3 : ℝ) * Cw * c⁻¹ * (2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 8 : ℝ)))
        = C_near * (c⁻¹ * c ^ (-(3 / 8 : ℝ))) := by simp only [C_near]; ring
      _ = C_near * c ^ (-(11 / 8 : ℝ)) := by rw [hc_pow]).le
  -- 2. Outer tails via `vdc1_Ioi_edgePhi` and `vdc1_Ioi_neg_edgePhi`
  have hLam : ∀ x ∈ Ici r, (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) ≤ |edgePhiDeriv L x| := by
    intro x hx
    have hxr : r ≤ x := hx
    have ht0 : 0 ≤ c ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hcpos.le _
    have hx0 : 0 ≤ x := le_trans hr_pos.le hxr
    have hstep1 := hankelEdgeM_two_sub_three_self ht0 ht32
    have hstep2 : hankelEdgeM r ≤ hankelEdgeM x :=
      hankelEdgeM_strictMonoOn.monotoneOn hr_pos.le hx0 hxr
    have hphys : FctSym.physDelta c = hankelEdgeM (c ^ (-(1 / 4 : ℝ))) := physDelta_eq_hankelEdgeM hcpos.le
    have hneg : edgePhiDeriv L x ≤ -(1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
      rw [edgePhiDeriv_eq_sub_hankelEdgeM hx0]
      have hsq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]; congr 1; norm_num
      linarith [show (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) ≤ hankelEdgeM r - 3 * FctSym.physDelta c by
        rw [hphys, ← hsq]; exact hstep1]
    have hle0 : edgePhiDeriv L x ≤ 0 := by
      have : 0 ≤ (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) := mul_nonneg (by norm_num) (Real.rpow_nonneg hcpos.le _)
      linarith
    rw [abs_of_nonpos hle0]
    linarith
  have hCD1_pos : ContDiffOn ℝ 1 (warpAmpLeft h ε c ξ) (Ioi 0) :=
    (hW_cd.of_le (by norm_num)).mono fun x hx => (mem_Ioi.mp hx).ne'
  have hCD1_neg : ContDiffOn ℝ 1 (fun t => warpAmpLeft h ε c ξ (-t)) (Ioi 0) :=
    (hW_cd.of_le (by norm_num)).comp contDiff_neg.contDiffOn fun x hx => neg_ne_zero.mpr (mem_Ioi.mp hx).ne'
  obtain ⟨hM_all, hV_all⟩ := hMV ε c ξ hε hcMV r hr_pos
  have hInt_pos :
      IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ τ *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) (Ioi r) := by
    have heq : (fun τ : ℝ => warpAmpLeft h ε c ξ τ *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) = f_full := by
      ext τ; rw [hf_eq τ, mul_comm]
    rw [heq]
    exact hInt_full.integrableOn
  have hInt_neg :
      IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ (-τ) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-τ) : ℂ))) (Ioi r) := by
    have heq : (fun τ : ℝ => warpAmpLeft h ε c ξ (-τ) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-τ) : ℂ))) = fun τ => f_full (-τ) := by
      ext τ; rw [hf_eq (-τ), mul_comm]
    rw [heq]
    exact (hInt_full.comp_neg).integrableOn
  have hlam_pos : 0 < (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hcpos _)
  have hvdc_pos := vdc1_Ioi_edgePhi hr_pos hcpos hlam_pos
    (by positivity) (by positivity) hCD1_pos hInt_pos hLam
    (fun x hx => (hM_all x hx).1) (fun T hT => (hV_all T hT).1)
  have hvdc_neg := vdc1_Ioi_neg_edgePhi hr_pos hcpos hlam_pos
    (by positivity) (by positivity) hCD1_neg hInt_neg hLam
    (fun x hx => (hM_all x hx).2) (fun T hT => (hV_all T hT).2)
  have hvdc_simp : 3 * (M0 * c⁻¹ + V0 * c⁻¹) / (c * ((1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)))) =
      (6 * (M0 + V0)) * c ^ (-(3 / 2 : ℝ)) := by
    have hpow : c * c ^ (-(1 / 2 : ℝ)) = c ^ (1 / 2 : ℝ) := by
      nth_rw 1 [← Real.rpow_one c]
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    have hpow2 : c⁻¹ / c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_sub hcpos]; congr 1; norm_num
    calc 3 * (M0 * c⁻¹ + V0 * c⁻¹) / (c * ((1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ))))
        = 6 * (M0 + V0) * (c⁻¹ / (c * c ^ (-(1 / 2 : ℝ)))) := by ring
      _ = 6 * (M0 + V0) * (c⁻¹ / c ^ (1 / 2 : ℝ)) := by rw [hpow]
      _ = 6 * (M0 + V0) * c ^ (-(3 / 2 : ℝ)) := by rw [hpow2]
  have hc32_le : c ^ (-(3 / 2 : ℝ)) ≤ c ^ (-(11 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hint_pos_eq : ∫ τ in Ioi r, f_full τ =
      ∫ τ in Ioi r, warpAmpLeft h ε c ξ τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun τ _ => by rw [hf_eq τ, mul_comm]
  have hint_neg_eq : ∫ τ in Ioi r, f_full (-τ) =
      ∫ τ in Ioi r, warpAmpLeft h ε c ξ (-τ) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-τ) : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun τ _ => by rw [hf_eq (-τ), mul_comm]
  have h_pos_bd : ‖∫ τ in Ioi r, f_full τ‖ ≤ (6 * (M0 + V0)) * c ^ (-(11 / 8 : ℝ)) := by
    rw [hint_pos_eq]
    exact hvdc_pos.trans (by rw [hvdc_simp]; exact mul_le_mul_of_nonneg_left hc32_le (by positivity))
  have h_neg_bd : ‖∫ τ in Ioi r, f_full (-τ)‖ ≤ (6 * (M0 + V0)) * c ^ (-(11 / 8 : ℝ)) := by
    rw [hint_neg_eq]
    exact hvdc_neg.trans (by rw [hvdc_simp]; exact mul_le_mul_of_nonneg_left hc32_le (by positivity))
  have h_full_bd : ‖∫ τ : ℝ, f_full τ‖ ≤ (C_near + C_tail) * c ^ (-(11 / 8 : ℝ)) := by
    rw [hsplit]
    calc ‖(∫ τ in Ioc (-r) r, f_full τ) + (∫ τ in Ioi r, f_full τ) + ∫ τ in Ioi r, f_full (-τ)‖
        ≤ ‖∫ τ in Ioc (-r) r, f_full τ‖ + ‖∫ τ in Ioi r, f_full τ‖ +
            ‖∫ τ in Ioi r, f_full (-τ)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C_near * c ^ (-(11 / 8 : ℝ)) + (6 * (M0 + V0)) * c ^ (-(11 / 8 : ℝ)) +
            (6 * (M0 + V0)) * c ^ (-(11 / 8 : ℝ)) :=
          add_le_add (add_le_add h_near h_pos_bd) h_neg_bd
      _ = (C_near + C_tail) * c ^ (-(11 / 8 : ℝ)) := by simp only [C_tail]; ring
  have hc_final : c ^ (-(1 / 2 : ℝ)) * c ^ (-(11 / 8 : ℝ)) = c ^ (-(15 / 8 : ℝ)) := by
    rw [← Real.rpow_add hcpos]; congr 1; norm_num
  unfold warpLeftTailDensity
  rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * π),
    abs_of_pos (Real.rpow_pos_of_pos hcpos _)]
  calc |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * |(∫ τ : ℝ, f_full τ).re|
      ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * ‖∫ τ : ℝ, f_full τ‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * ((C_near + C_tail) * c ^ (-(11 / 8 : ℝ))) :=
        mul_le_mul_of_nonneg_left h_full_bd (by positivity)
    _ = C * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(11 / 8 : ℝ))) := by simp only [C]; ring
    _ = C * c ^ (-(15 / 8 : ℝ)) := by rw [hc_final]

/-- info: 'FormalResearch.SignUncertainty.warpLeftTailDensity_mid_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpLeftTailDensity_mid_bound

end FormalResearch.SignUncertainty
