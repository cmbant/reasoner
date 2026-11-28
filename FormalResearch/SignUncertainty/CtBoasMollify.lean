/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtOuterBandCut

/-!
# Smooth mollifier and `C^{1,1}` (Lipschitz-derivative) second-difference bounds (`ct:boas` Steps 3–4)

General smooth-mollification infrastructure for the log-free proof of `ct:boas`
(`CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Steps 3–4):

* `mollBump`, `mollKernel`, `mollConv`: an even `C^∞` unit-integral bump supported in `(-1, 1)`, rescaled to
  `[-ε, ε]`; `mollConv_sub_le` gives `|ρ_ε * f - f| ≤ ½ M₂ ε²` from the second-difference bound
  `|f(x+y) - 2 f(x) + f(x-y)| ≤ M₂ y²`, and `abs_iteratedDeriv_mollConv_le` bounds `|(ρ_ε * f)^{(r)}| ≤ C_r ε^{-r}`
  for every `r : ℕ`.
* `secDiff_le_of_deriv_lip`, `deriv_lip_mul`: `C^{1,1}` calculus without weak second derivatives.

Class: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Even `C^∞` mollifier and `r`-th derivative bounds -/

noncomputable def rawUnitBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def evenUnitBump (x : ℝ) : ℝ :=
  (rawUnitBump x + rawUnitBump (-x)) / 2

lemma contDiff_evenUnitBump : ContDiff ℝ (⊤ : ℕ∞) evenUnitBump := by
  unfold evenUnitBump
  exact (rawUnitBump.contDiff.add (rawUnitBump.contDiff.comp contDiff_neg)).div_const 2

lemma evenUnitBump_nonneg (x : ℝ) : 0 ≤ evenUnitBump x := by
  unfold evenUnitBump
  have h1 : 0 ≤ rawUnitBump x := rawUnitBump.nonneg
  have h2 : 0 ≤ rawUnitBump (-x) := rawUnitBump.nonneg
  linarith

lemma evenUnitBump_neg (x : ℝ) : evenUnitBump (-x) = evenUnitBump x := by
  unfold evenUnitBump; rw [neg_neg]; ring

lemma evenUnitBump_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : evenUnitBump x = 0 := by
  have h1 : x ∉ Function.support rawUnitBump := by
    rw [rawUnitBump.support_eq]
    simpa [rawUnitBump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt] using hx
  have h2 : -x ∉ Function.support rawUnitBump := by
    rw [rawUnitBump.support_eq]
    simpa [rawUnitBump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg, not_lt] using hx
  unfold evenUnitBump
  rw [Function.notMem_support.mp h1, Function.notMem_support.mp h2]
  norm_num

lemma hasCompactSupport_evenUnitBump : HasCompactSupport evenUnitBump := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
  intro x hx
  by_contra h
  refine hx (evenUnitBump_eq_zero ?_)
  rw [Set.mem_Icc] at h
  push Not at h
  rcases le_or_gt (-1 : ℝ) x with h1 | h1
  · rw [abs_of_nonneg (by linarith [h h1])]; linarith [h h1]
  · rw [abs_of_neg (by linarith)]; linarith

lemma one_le_integral_evenUnitBump : 1 ≤ ∫ x : ℝ, evenUnitBump x := by
  have hi : Integrable evenUnitBump :=
    contDiff_evenUnitBump.continuous.integrable_of_hasCompactSupport hasCompactSupport_evenUnitBump
  have hsub : ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), evenUnitBump x ≤ ∫ x : ℝ, evenUnitBump x :=
    setIntegral_le_integral hi (ae_of_all _ evenUnitBump_nonneg)
  have hcongr : ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), evenUnitBump x = 1 := by
    have hpt : ∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), evenUnitBump x = 1 := fun x hx => by
      have ha : |x| ≤ 1 / 2 := abs_le.2 hx
      have h1 : x ∈ Metric.closedBall (0 : ℝ) rawUnitBump.rIn := by
        simpa [rawUnitBump, Real.norm_eq_abs] using ha
      have h2 : -x ∈ Metric.closedBall (0 : ℝ) rawUnitBump.rIn := by
        simpa [rawUnitBump, Real.norm_eq_abs, abs_neg] using ha
      unfold evenUnitBump
      rw [rawUnitBump.one_of_mem_closedBall h1, rawUnitBump.one_of_mem_closedBall h2]
      norm_num
    rw [setIntegral_congr_fun measurableSet_Icc hpt, setIntegral_const, smul_eq_mul,
      Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  linarith

/-- Normalized even `C^∞` unit-integral bump supported in `(-1, 1)`. -/
noncomputable def mollBump (x : ℝ) : ℝ :=
  evenUnitBump x / ∫ t : ℝ, evenUnitBump t

lemma contDiff_mollBump : ContDiff ℝ (⊤ : ℕ∞) mollBump := by
  unfold mollBump
  exact contDiff_evenUnitBump.div_const _

lemma mollBump_nonneg (x : ℝ) : 0 ≤ mollBump x :=
  div_nonneg (evenUnitBump_nonneg x) (by linarith [one_le_integral_evenUnitBump])

lemma mollBump_neg (x : ℝ) : mollBump (-x) = mollBump x := by
  unfold mollBump
  rw [evenUnitBump_neg]

lemma mollBump_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : mollBump x = 0 := by
  unfold mollBump
  rw [evenUnitBump_eq_zero hx, zero_div]

lemma integral_mollBump : ∫ x : ℝ, mollBump x = 1 := by
  unfold mollBump
  rw [integral_div]
  exact div_self (by linarith [one_le_integral_evenUnitBump])

/-- Rescaled smooth mollifier `ρ_ε(x) = ε⁻¹ ρ(x / ε)` for `ε > 0`. -/
noncomputable def mollKernel (ε x : ℝ) : ℝ :=
  ε⁻¹ * mollBump (x / ε)

lemma contDiff_mollKernel {ε : ℝ} (_hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (mollKernel ε) := by
  unfold mollKernel
  exact contDiff_const.mul (contDiff_mollBump.comp (contDiff_id.div_const ε))

lemma mollKernel_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ mollKernel ε x :=
  mul_nonneg (inv_nonneg.2 hε.le) (mollBump_nonneg _)

lemma mollKernel_neg (ε x : ℝ) : mollKernel ε (-x) = mollKernel ε x := by
  unfold mollKernel; rw [neg_div, mollBump_neg]

lemma mollKernel_eq_zero {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : ε ≤ |x|) : mollKernel ε x = 0 := by
  unfold mollKernel
  have h1 : 1 ≤ |x / ε| := by
    rw [abs_div, abs_of_pos hε, one_le_div hε]
    exact hx
  rw [mollBump_eq_zero h1, mul_zero]

lemma integrable_mollKernel {ε : ℝ} (hε : 0 < ε) : Integrable (mollKernel ε) := by
  have hc : Continuous (mollKernel ε) := (contDiff_mollKernel hε).continuous
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -ε) (b := ε)) ?_
  intro x hx
  by_contra h
  refine hx (mollKernel_eq_zero hε ?_)
  rw [Set.mem_Icc] at h
  push Not at h
  rcases le_or_gt (-ε) x with h1 | h1
  · rw [abs_of_nonneg (by linarith [h h1])]; linarith [h h1]
  · rw [abs_of_neg (by linarith)]; linarith

lemma integral_mollKernel {ε : ℝ} (hε : 0 < ε) : ∫ x : ℝ, mollKernel ε x = 1 := by
  unfold mollKernel
  rw [integral_const_mul, Measure.integral_comp_div mollBump ε, smul_eq_mul, abs_of_pos hε,
    integral_mollBump, mul_one, inv_mul_cancel₀ hε.ne']

/-- Convolution `mollConv ε f x = ∫ y, ρ_ε(x - y) f(y) dy`. -/
noncomputable def mollConv (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, mollKernel ε (x - y) * f y

lemma mollConv_eq_sub {ε : ℝ} (_hε : 0 < ε) {f : ℝ → ℝ} (x : ℝ) :
    mollConv ε f x = ∫ y : ℝ, mollKernel ε y * f (x - y) := by
  unfold mollConv
  have h1 : (fun y : ℝ => mollKernel ε (x - y) * f y) =
      fun y => (fun t => mollKernel ε t * f (x - t)) (x - y) := by
    funext y; simp
  rw [h1, integral_sub_left_eq_self (fun t => mollKernel ε t * f (x - t)) volume x]

lemma mollConv_bounds {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hfc : Continuous f)
    (h0 : ∀ y, 0 ≤ f y) (h1 : ∀ y, f y ≤ 1) (x : ℝ) :
    0 ≤ mollConv ε f x ∧ mollConv ε f x ≤ 1 := by
  have hi : Integrable (fun y => mollKernel ε y * f (x - y)) := by
    refine (integrable_mollKernel hε).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((contDiff_mollKernel hε).continuous.mul (hfc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollKernel_nonneg hε y), abs_of_nonneg (h0 _)]
      exact mul_le_of_le_one_right (mollKernel_nonneg hε y) (h1 _)
  rw [mollConv_eq_sub hε]
  constructor
  · exact integral_nonneg fun y => mul_nonneg (mollKernel_nonneg hε y) (h0 _)
  · calc ∫ y : ℝ, mollKernel ε y * f (x - y) ≤ ∫ y : ℝ, mollKernel ε y := by
          refine integral_mono hi (integrable_mollKernel hε) fun y => ?_
          exact mul_le_of_le_one_right (mollKernel_nonneg hε y) (h1 _)
      _ = 1 := integral_mollKernel hε

lemma mollConv_eq_zero_of_support {ε a b : ℝ} (hε : 0 < ε) {f : ℝ → ℝ}
    (hsupp : ∀ y, y ∉ Icc a b → f y = 0) {x : ℝ} (hx : x ∉ Ioo (a - ε) (b + ε)) :
    mollConv ε f x = 0 := by
  unfold mollConv
  refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ Icc a b
  · have hxe : ε ≤ |x - y| := by
      rw [Set.mem_Ioo] at hx; push Not at hx
      rcases le_or_gt x (a - ε) with h | h
      · rw [abs_sub_comm, abs_of_nonneg (by linarith [hy.1])]; linarith [hy.1]
      · rw [abs_of_nonneg (by linarith [hy.2, hx h])]; linarith [hy.2, hx h]
    change mollKernel ε (x - y) * f y = 0
    rw [mollKernel_eq_zero hε hxe, zero_mul]
  · change mollKernel ε (x - y) * f y = 0
    rw [hsupp y hy, mul_zero]

/-- **Second-order mollification error**: `|ρ_ε * f - f| ≤ ½ M₂ ε²` using evenness of `ρ_ε` and
`|f(x+y) - 2 f(x) + f(x-y)| ≤ M₂ y²` for `|y| ≤ ε`. -/
lemma mollConv_sub_le {ε M₂ : ℝ} (hε : 0 < ε) (hM₂ : 0 ≤ M₂) {f : ℝ → ℝ} (hfc : Continuous f)
    (hfb : ∀ y, |f y| ≤ 1) {x : ℝ}
    (hsec : ∀ y, |y| ≤ ε → |f (x + y) - 2 * f x + f (x - y)| ≤ M₂ * y ^ 2) :
    |mollConv ε f x - f x| ≤ 1 / 2 * M₂ * ε ^ 2 := by
  have hi_ker := integrable_mollKernel hε
  have hi1 : Integrable (fun y => mollKernel ε y * f (x - y)) := by
    refine hi_ker.mono' ((contDiff_mollKernel hε).continuous.mul
      (hfc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollKernel_nonneg hε y)]
    exact mul_le_of_le_one_right (mollKernel_nonneg hε y) (hfb _)
  have hi2 : Integrable (fun y => mollKernel ε y * f (x + y)) := by
    have := hi1.comp_neg
    refine this.congr (ae_of_all _ fun y => ?_)
    simp [mollKernel_neg, sub_neg_eq_add]
  have hsymm : ∫ y : ℝ, mollKernel ε y * f (x - y) = ∫ y : ℝ, mollKernel ε y * f (x + y) := by
    rw [← integral_neg_eq_self (fun y => mollKernel ε y * f (x - y))]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp [mollKernel_neg, sub_neg_eq_add]
  have hid : mollConv ε f x - f x =
      1 / 2 * ∫ y : ℝ, mollKernel ε y * (f (x + y) - 2 * f x + f (x - y)) := by
    rw [mollConv_eq_sub hε]
    have hfx : f x = ∫ y : ℝ, mollKernel ε y * f x := by
      rw [integral_mul_const, integral_mollKernel hε, one_mul]
    have hi3 : Integrable (fun y => mollKernel ε y * (2 * f x)) := hi_ker.mul_const (2 * f x)
    have h12 : Integrable (fun y => mollKernel ε y * f (x + y) - mollKernel ε y * (2 * f x)) :=
      hi2.sub hi3
    have hsum1 : (fun y => mollKernel ε y * (f (x + y) - 2 * f x + f (x - y))) =
        fun y => (mollKernel ε y * f (x + y) - mollKernel ε y * (2 * f x)) +
          mollKernel ε y * f (x - y) := funext fun y => by ring
    have e2 : ∫ y : ℝ, mollKernel ε y * (2 * f x) = 2 * f x := by
      rw [integral_mul_const, integral_mollKernel hε, one_mul]
    have e_sub : ∫ y : ℝ, (mollKernel ε y * f (x + y) - mollKernel ε y * (2 * f x)) =
        (∫ y : ℝ, mollKernel ε y * f (x + y)) - 2 * f x := by
      rw [integral_sub hi2 hi3, e2]
    have e_add : ∫ y : ℝ, ((mollKernel ε y * f (x + y) - mollKernel ε y * (2 * f x)) +
        mollKernel ε y * f (x - y)) =
        (∫ y : ℝ, (mollKernel ε y * f (x + y) - mollKernel ε y * (2 * f x))) +
          ∫ y : ℝ, mollKernel ε y * f (x - y) := integral_add h12 hi1
    rw [hsum1, e_add, e_sub, hsymm]
    ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc (1 / 2 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hpt : ∀ y, |mollKernel ε y * (f (x + y) - 2 * f x + f (x - y))| ≤
      M₂ * ε ^ 2 * mollKernel ε y := fun y => by
    by_cases hy : |y| ≤ ε
    · rw [abs_mul, abs_of_nonneg (mollKernel_nonneg hε y)]
      have hsq : y ^ 2 ≤ ε ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
      have h1 : |f (x + y) - 2 * f x + f (x - y)| ≤ M₂ * ε ^ 2 :=
        (hsec y hy).trans (mul_le_mul_of_nonneg_left hsq hM₂)
      exact (mul_le_mul_of_nonneg_left h1 (mollKernel_nonneg hε y)).trans_eq (by ring)
    · rw [not_le] at hy
      rw [mollKernel_eq_zero hε hy.le, zero_mul, abs_zero, mul_zero]
  have hint : Integrable (fun y => mollKernel ε y * (f (x + y) - 2 * f x + f (x - y))) := by
    refine ((hi2.sub (hi_ker.mul_const (2 * f x))).add hi1).congr (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [← Real.norm_eq_abs]
  calc ‖∫ y, mollKernel ε y * (f (x + y) - 2 * f x + f (x - y))‖
      ≤ ∫ y, ‖mollKernel ε y * (f (x + y) - 2 * f x + f (x - y))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, M₂ * ε ^ 2 * mollKernel ε y := integral_mono hint.norm (hi_ker.const_mul _) (fun y => by
        rw [Real.norm_eq_abs]; exact hpt y)
    _ = M₂ * ε ^ 2 := by rw [integral_const_mul, integral_mollKernel hε, mul_one]

lemma mollConv_iteratedDeriv_eq {ε a b : ℝ} (hε : 0 < ε) (hab : a ≤ b) {f : ℝ → ℝ}
    (hfc : Continuous f) (hsupp : ∀ y, y ∉ Icc a b → f y = 0) :
    (∀ n : ℕ, ContDiff ℝ n (mollConv ε f)) ∧ ∀ (r : ℕ) (x : ℝ),
      iteratedDeriv r (mollConv ε f) x = ∫ y in a..b, iteratedDeriv r (mollKernel ε) (x - y) * f y := by
  have heq : ∀ x, mollConv ε f x = ∫ y in a..b, mollKernel ε (x - y) * f y := fun x => by
    unfold mollConv
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ Icc a b
    · rw [indicator_of_mem hy]
    · dsimp only
      rw [indicator_of_notMem hy, hsupp y hy, mul_zero]
  have hderiv : ∀ (r : ℕ) (x : ℝ),
      HasDerivAt (fun z => ∫ y in a..b, iteratedDeriv r (mollKernel ε) (z - y) * f y)
        (∫ y in a..b, iteratedDeriv (r + 1) (mollKernel ε) (x - y) * f y) x := by
    intro r x
    have hc_r1 : Continuous (iteratedDeriv r (mollKernel ε)) :=
      (contDiff_mollKernel hε).continuous_iteratedDeriv r (WithTop.coe_le_coe.2 le_top)
    have hc_r2 : Continuous (iteratedDeriv (r + 1) (mollKernel ε)) :=
      (contDiff_mollKernel hε).continuous_iteratedDeriv (r + 1) (WithTop.coe_le_coe.2 le_top)
    have hcont_p : Continuous (fun p : ℝ × ℝ => iteratedDeriv (r + 1) (mollKernel ε) (p.1 - p.2) * f p.2) :=
      (hc_r2.comp (continuous_fst.sub continuous_snd)).mul (hfc.comp continuous_snd)
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (s := Icc (x - 1) (x + 1) ×ˢ Icc a b) hcont_p.continuousOn
    have hid := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun z y => iteratedDeriv r (mollKernel ε) (z - y) * f y)
      (F' := fun z y => iteratedDeriv (r + 1) (mollKernel ε) (z - y) * f y)
      (bound := fun _ => B)
      (x₀ := x) (s := Metric.ball x 1) (a := a) (b := b) (Metric.ball_mem_nhds x one_pos)
      (Eventually.of_forall fun z => (((hc_r1.comp (continuous_const.sub continuous_id)).mul
        hfc).aestronglyMeasurable).restrict)
      (((hc_r1.comp (continuous_const.sub continuous_id)).mul hfc).intervalIntegrable a b)
      (((hc_r2.comp (continuous_const.sub continuous_id)).mul hfc).aestronglyMeasurable).restrict
      (Eventually.of_forall fun y hy z hz => by
        have hz' : z ∈ Icc (x - 1) (x + 1) := by
          have := Metric.mem_ball.1 hz
          rw [Real.dist_eq, abs_lt] at this
          exact ⟨by linarith, by linarith⟩
        have hy' : y ∈ Icc a b := by
          rw [Set.uIoc_of_le hab] at hy; exact ⟨hy.1.le, hy.2⟩
        exact hB (z, y) ⟨hz', hy'⟩)
      intervalIntegrable_const
      (Eventually.of_forall fun y _ z _ => by
        have hd : HasDerivAt (iteratedDeriv r (mollKernel ε))
            (iteratedDeriv (r + 1) (mollKernel ε) (z - y)) (z - y) := by
          have := ((contDiff_mollKernel hε).differentiable_iteratedDeriv r
            (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top r)) (z - y)).hasDerivAt
          rwa [← iteratedDeriv_succ] at this
        exact ((hd.comp z ((hasDerivAt_id z).sub_const y)).congr_deriv (by ring)).mul_const (f y))
    exact hid.2
  have hcd : ∀ (n r : ℕ), ContDiff ℝ (n : ℕ∞ω) (fun z => ∫ y in a..b, iteratedDeriv r (mollKernel ε) (z - y) * f y) := by
    intro n
    induction n with
    | zero =>
      intro r
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x => (hderiv r x).continuousAt
    | succ n ih =>
      intro r
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun z => (hderiv r z).differentiableAt, ?_⟩
      simp only [WithTop.natCast_ne_top, IsEmpty.forall_iff, true_and]
      have e : deriv (fun z => ∫ y in a..b, iteratedDeriv r (mollKernel ε) (z - y) * f y) =
          fun z => ∫ y in a..b, iteratedDeriv (r + 1) (mollKernel ε) (z - y) * f y :=
        funext fun z => (hderiv r z).deriv
      rw [e]
      exact ih (r + 1)
  have heq_fn : mollConv ε f = fun z => ∫ y in a..b, mollKernel ε (z - y) * f y := funext heq
  rw [heq_fn]
  refine ⟨fun n => by simpa using hcd n 0, fun r => ?_⟩
  induction r with
  | zero => intro x; simp
  | succ r ih =>
    intro x
    rw [iteratedDeriv_succ]
    have e : iteratedDeriv r (fun w => ∫ y in a..b, mollKernel ε (w - y) * f y) =
        fun w => ∫ y in a..b, iteratedDeriv r (mollKernel ε) (w - y) * f y := funext ih
    rw [e, (hderiv r x).deriv]

lemma iteratedDeriv_mollKernel_eq {ε : ℝ} (_hε : 0 < ε) (r : ℕ) (z : ℝ) :
    iteratedDeriv r (mollKernel ε) z = ε⁻¹ * (ε⁻¹) ^ r * iteratedDeriv r mollBump (z / ε) := by
  have e : mollKernel ε = fun t => ε⁻¹ * (fun u => mollBump (ε⁻¹ * u)) t := by
    funext t; unfold mollKernel; rw [div_eq_inv_mul]
  rw [e]
  have h1 : ContDiffAt ℝ r (fun u : ℝ => mollBump (ε⁻¹ * u)) z :=
    ((contDiff_mollBump.comp (contDiff_const.mul contDiff_id)).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hsmul : (fun t => ε⁻¹ * (fun u => mollBump (ε⁻¹ * u)) t) = ε⁻¹ • fun u => mollBump (ε⁻¹ * u) := rfl
  have hcomp := congrFun (iteratedDeriv_comp_const_mul (n := r)
    (contDiff_mollBump.of_le (WithTop.coe_le_coe.2 le_top)) ε⁻¹) z
  rw [hsmul, iteratedDeriv_const_smul (n := r) h1, smul_eq_mul, hcomp, div_eq_inv_mul]
  ring

/-- **Uniform `r`-th derivative bound for `ρ_ε * f`**: `|(ρ_ε * f)^{(r)}(x)| ≤ C_r ε^{-r}`
whenever `|f| ≤ 1`, continuous, supported in `[a, b]`. -/
theorem abs_iteratedDeriv_mollConv_le (r : ℕ) : ∃ C_m : ℝ, 0 ≤ C_m ∧
    ∀ {ε a b : ℝ}, 0 < ε → a ≤ b → ∀ {f : ℝ → ℝ}, Continuous f → (∀ y, y ∉ Icc a b → f y = 0) →
      (∀ y, |f y| ≤ 1) → ∀ x : ℝ, |iteratedDeriv r (mollConv ε f) x| ≤ C_m * (ε⁻¹) ^ r := by
  have hc_b : Continuous (iteratedDeriv r mollBump) :=
    contDiff_mollBump.continuous_iteratedDeriv r (WithTop.coe_le_coe.2 le_top)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := iteratedDeriv r mollBump) (s := Icc (-1 : ℝ) 1) hc_b.continuousOn
  refine ⟨2 * max B 0, by positivity, ?_⟩
  intro ε a b hε hab f hfc hsupp hfb x
  obtain ⟨-, hform⟩ := mollConv_iteratedDeriv_eq hε hab hfc hsupp
  rw [hform r x]
  have hsupp_b : ∀ t : ℝ, 1 < |t| → iteratedDeriv r mollBump t = 0 := by
    intro t ht
    have hne : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; norm_num at ht
    have hmem : mollBump =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have ht1 : t < -1 := by rw [abs_of_neg hneg] at ht; linarith
        filter_upwards [Iio_mem_nhds ht1] with y hy
        have hy' : y < -1 := Set.mem_Iio.1 hy
        exact mollBump_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)
      · have ht1 : 1 < t := by rw [abs_of_pos hpos] at ht; exact ht
        filter_upwards [Ioi_mem_nhds ht1] with y hy
        have hy' : 1 < y := Set.mem_Ioi.1 hy
        exact mollBump_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)
    rw [hmem.iteratedDeriv_eq r]
    simp
  have hbound_b : ∀ t : ℝ, |iteratedDeriv r mollBump t| ≤ max B 0 := fun t => by
    by_cases ht : |t| ≤ 1
    · have h := hB t (abs_le.1 ht)
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left B 0)
    · rw [not_le] at ht
      rw [hsupp_b t ht, abs_zero]
      exact le_max_right B 0
  have hint_fn : ∀ y, |iteratedDeriv r (mollKernel ε) (x - y) * f y| ≤
      ((Icc (x - ε) (x + ε)).indicator (fun _ => ε⁻¹ * (ε⁻¹) ^ r * max B 0)) y := fun y => by
    rw [iteratedDeriv_mollKernel_eq hε, abs_mul]
    by_cases hy : y ∈ Icc (x - ε) (x + ε)
    · rw [indicator_of_mem hy]
      have h1 : |ε⁻¹ * (ε⁻¹) ^ r * iteratedDeriv r mollBump ((x - y) / ε)| ≤
          ε⁻¹ * (ε⁻¹) ^ r * max B 0 := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hbound_b _) (by positivity)
      calc _ ≤ |ε⁻¹ * (ε⁻¹) ^ r * iteratedDeriv r mollBump ((x - y) / ε)| * 1 :=
            mul_le_mul_of_nonneg_left (hfb y) (abs_nonneg _)
        _ ≤ _ := by linarith
    · rw [indicator_of_notMem hy]
      have hgt : 1 < |(x - y) / ε| := by
        rw [abs_div, abs_of_pos hε, one_lt_div hε]
        rw [Set.mem_Icc] at hy; push Not at hy
        rcases lt_or_ge y (x - ε) with h | h
        · rw [abs_of_nonneg (by linarith)]; linarith
        · have h2 := hy h
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      rw [hsupp_b _ hgt, mul_zero, abs_zero, zero_mul]
  rw [intervalIntegral.integral_of_le hab]
  have hintL : IntegrableOn (fun y => iteratedDeriv r (mollKernel ε) (x - y) * f y) (Ioc a b) :=
    ((((contDiff_mollKernel hε).continuous_iteratedDeriv r (WithTop.coe_le_coe.2 le_top)).comp
      (continuous_const.sub continuous_id)).mul hfc).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hintI : Integrable (fun y => (Icc (x - ε) (x + ε)).indicator (fun _ => ε⁻¹ * (ε⁻¹) ^ r * max B 0) y) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  rw [← Real.norm_eq_abs]
  calc ‖∫ y in Ioc a b, iteratedDeriv r (mollKernel ε) (x - y) * f y‖
      ≤ ∫ y in Ioc a b, ‖iteratedDeriv r (mollKernel ε) (x - y) * f y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioc a b, (Icc (x - ε) (x + ε)).indicator (fun _ => ε⁻¹ * (ε⁻¹) ^ r * max B 0) y :=
        setIntegral_mono_on hintL.norm hintI.integrableOn measurableSet_Ioc fun y _ => by
          rw [Real.norm_eq_abs]; exact hint_fn y
    _ ≤ ∫ y, (Icc (x - ε) (x + ε)).indicator (fun _ => ε⁻¹ * (ε⁻¹) ^ r * max B 0) y :=
        setIntegral_le_integral hintI (ae_of_all _ fun y => indicator_nonneg (fun _ _ => by positivity) y)
    _ = 2 * max B 0 * (ε⁻¹) ^ r := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc_of_le (by linarith)]
        have hlen : x + ε - (x - ε) = 2 * ε := by ring
        rw [hlen]
        field_simp

/-! ### `C^{1,1}` (Lipschitz-derivative) calculus for second differences -/

/-- A differentiable function `f : ℝ → ℝ` with `L`-Lipschitz derivative `f'` satisfies
`|f(x + y) - 2 f(x) + f(x - y)| ≤ L y²` for all `x, y : ℝ`. -/
lemma secDiff_le_of_deriv_lip {f f' : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hlip : ∀ x y : ℝ, |f' x - f' y| ≤ L * |x - y|) (x y : ℝ) :
    |f (x + y) - 2 * f x + f (x - y)| ≤ L * y ^ 2 := by
  have hc : Continuous f' := continuous_iff_continuousAt.2 fun u => by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / (L + 1), by positivity, fun {v} hv => ?_⟩
    rw [Real.dist_eq] at hv ⊢
    calc |f' v - f' u| ≤ L * |v - u| := hlip v u
      _ ≤ (L + 1) * |v - u| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hv (by positivity)
      _ = ε := by field_simp
  have nonneg_case : ∀ t : ℝ, 0 ≤ t → |f (x + t) - 2 * f x + f (x - t)| ≤ L * t ^ 2 := by
    intro t ht
    have hc1 : Continuous (fun s => f' (x + s)) := hc.comp (continuous_const.add continuous_id)
    have hc2 : Continuous (fun s => f' (x - s)) := hc.comp (continuous_const.sub continuous_id)
    have h1 : f (x + t) - f x = ∫ s in (0 : ℝ)..t, f' (x + s) := by
      have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => f (x + s))
        (f' := fun s => f' (x + s)) (fun s _ =>
          ((hd (x + s)).comp s ((hasDerivAt_id s).const_add x)).congr_deriv (by ring))
        (hc1.intervalIntegrable 0 t)
      rw [hid]; simp
    have h2 : f x - f (x - t) = ∫ s in (0 : ℝ)..t, f' (x - s) := by
      have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => -f (x - s))
        (f' := fun s => f' (x - s)) (fun s _ =>
          (((hd (x - s)).comp s ((hasDerivAt_id s).const_sub x)).neg).congr_deriv (by ring))
        (hc2.intervalIntegrable 0 t)
      rw [hid]; simp; ring
    have hid : f (x + t) - 2 * f x + f (x - t) = ∫ s in (0 : ℝ)..t, (f' (x + s) - f' (x - s)) := by
      rw [show f (x + t) - 2 * f x + f (x - t) = (f (x + t) - f x) - (f x - f (x - t)) by ring, h1, h2]
      exact (intervalIntegral.integral_sub (hc1.intervalIntegrable 0 t) (hc2.intervalIntegrable 0 t)).symm
    rw [hid]
    have hbd : ∀ s ∈ Icc (0 : ℝ) t, |f' (x + s) - f' (x - s)| ≤ L * (2 * s) := fun s hs => by
      refine (hlip (x + s) (x - s)).trans_eq ?_
      have : x + s - (x - s) = 2 * s := by ring
      rw [this, abs_of_nonneg (by linarith [hs.1])]
    have hint2 : ∫ s in (0 : ℝ)..t, L * (2 * s) = L * t ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hsq : ∫ s in (0 : ℝ)..t, (2 * s) = t ^ 2 := by
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => s ^ 2)
          (fun s _ => by simpa using hasDerivAt_pow 2 s)
          ((continuous_const.mul continuous_id).intervalIntegrable 0 t)
        simpa using h.trans (by simp)
      rw [hsq]
    have hint_diff : IntervalIntegrable (fun s => |f' (x + s) - f' (x - s)|) volume 0 t :=
      (hc1.sub hc2).abs.intervalIntegrable 0 t
    have hint_R : IntervalIntegrable (fun s => L * (2 * s)) volume 0 t :=
      (continuous_const.mul (continuous_const.mul continuous_id)).intervalIntegrable 0 t
    calc |∫ s in (0 : ℝ)..t, (f' (x + s) - f' (x - s))|
        ≤ ∫ s in (0 : ℝ)..t, |f' (x + s) - f' (x - s)| := by
          simpa only [Real.norm_eq_abs] using intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in (0 : ℝ)..t, L * (2 * s) :=
          intervalIntegral.integral_mono_on ht hint_diff hint_R hbd
      _ = L * t ^ 2 := hint2
  rcases le_or_gt 0 y with hy | hy
  · exact nonneg_case y hy
  · have h1 := nonneg_case (-y) (by linarith)
    have e1 : f (x + -y) - 2 * f x + f (x - -y) = f (x + y) - 2 * f x + f (x - y) := by
      rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring
    rw [e1, neg_sq] at h1
    exact h1

/-- Product rule for `C^{1,1}` bounds: if `|g| ≤ G₀, |g'| ≤ G₁, Lip(g') ≤ G₂` and `|h| ≤ H₀, |h'| ≤ H₁, Lip(h') ≤ H₂`,
then `Lip((gh)') ≤ G₂ H₀ + 2 G₁ H₁ + G₀ H₂`. -/
lemma deriv_lip_mul {g g' h h' : ℝ → ℝ} {G₀ G₁ G₂ H₀ H₁ H₂ : ℝ}
    (hgd : ∀ x, HasDerivAt g (g' x) x) (hhd : ∀ x, HasDerivAt h (h' x) x)
    (hg0 : ∀ x, |g x| ≤ G₀) (hg1 : ∀ x, |g' x| ≤ G₁) (hg2 : ∀ x y, |g' x - g' y| ≤ G₂ * |x - y|)
    (hh0 : ∀ x, |h x| ≤ H₀) (hh1 : ∀ x, |h' x| ≤ H₁) (hh2 : ∀ x y, |h' x - h' y| ≤ H₂ * |x - y|)
    (x y : ℝ) :
    |(g' x * h x + g x * h' x) - (g' y * h y + g y * h' y)| ≤
      (G₂ * H₀ + 2 * G₁ * H₁ + G₀ * H₂) * |x - y| := by
  have hG0 : 0 ≤ G₀ := (abs_nonneg _).trans (hg0 0)
  have hG1 : 0 ≤ G₁ := (abs_nonneg _).trans (hg1 0)
  have hG2 : 0 ≤ G₂ := by simpa using (abs_nonneg _).trans (hg2 0 1)
  have hH0 : 0 ≤ H₀ := (abs_nonneg _).trans (hh0 0)
  have hH1 : 0 ≤ H₁ := (abs_nonneg _).trans (hh1 0)
  have hH2 : 0 ≤ H₂ := by simpa using (abs_nonneg _).trans (hh2 0 1)
  have hglip : |g x - g y| ≤ G₁ * |x - y| := by
    have := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := g)
      (fun z _ => (hgd z).differentiableAt)
      (fun z _ => by rw [Real.norm_eq_abs, (hgd z).deriv]; exact hg1 z) (mem_univ y) (mem_univ x)
    simpa [Real.norm_eq_abs, Real.dist_eq] using this
  have hhlip : |h x - h y| ≤ H₁ * |x - y| := by
    have := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := h)
      (fun z _ => (hhd z).differentiableAt)
      (fun z _ => by rw [Real.norm_eq_abs, (hhd z).deriv]; exact hh1 z) (mem_univ y) (mem_univ x)
    simpa [Real.norm_eq_abs, Real.dist_eq] using this
  have hid : (g' x * h x + g x * h' x) - (g' y * h y + g y * h' y) =
      (g' x - g' y) * h x + g' y * (h x - h y) + (g x - g y) * h' x + g y * (h' x - h' y) := by ring
  rw [hid]
  have h1 : |(g' x - g' y) * h x| ≤ G₂ * |x - y| * H₀ := by
    rw [abs_mul]; exact mul_le_mul (hg2 x y) (hh0 x) (abs_nonneg _) (mul_nonneg hG2 (abs_nonneg _))
  have h2 : |g' y * (h x - h y)| ≤ G₁ * (H₁ * |x - y|) := by
    rw [abs_mul]; exact mul_le_mul (hg1 y) hhlip (abs_nonneg _) hG1
  have h3 : |(g x - g y) * h' x| ≤ G₁ * |x - y| * H₁ := by
    rw [abs_mul]; exact mul_le_mul hglip (hh1 x) (abs_nonneg _) (mul_nonneg hG1 (abs_nonneg _))
  have h4 : |g y * (h' x - h' y)| ≤ G₀ * (H₂ * |x - y|) := by
    rw [abs_mul]; exact mul_le_mul (hg0 y) (hh2 x y) (abs_nonneg _) hG0
  have htri1 := abs_add_le ((g' x - g' y) * h x + g' y * (h x - h y) + (g x - g y) * h' x) (g y * (h' x - h' y))
  have htri2 := abs_add_le ((g' x - g' y) * h x + g' y * (h x - h y)) ((g x - g y) * h' x)
  have htri3 := abs_add_le ((g' x - g' y) * h x) (g' y * (h x - h y))
  linarith

end FormalResearch.SignUncertainty
