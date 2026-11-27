/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingLeftC2
public import FormalResearch.SignUncertainty.FctPhiKillSymbol
public import FormalResearch.SignUncertainty.StripAdmissLift
public import FormalResearch.SignUncertainty.FctDescentRay
public import FormalResearch.CohnElkies.MellinLiftIntegrals
public import FormalResearch.CohnElkies.PieceCUniform

/-!
# Far-edge bounds for `stripG`, `phiKill`, `ctHG`, and `fctWarpA` on `τ ≥ 1/2`

Helper module for `FctSplittingPsiFar.lean`. Proves:
* `stripG_far_bound`: linear growth `‖stripG t‖ ≤ C * (1 + |t.im|)` on `{|t.re| ≤ 1, 1/2 ≤ |t.im|}`.
* `stripG_far_EJOn`, `phiKill_far_EJOn`, `ctHG_far_EJOn`, `fctWarpA_far_EJOn`: `EJOn` bounds on
  `τ ∈ [1/2, ∞)` for `A_ε(iτ)` and its factors.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real ContDiff
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-! ### `stripG` bounds and far-edge `EJOn` on `τ ≥ 1/2` -/

private lemma abs_sinh_pi_quarter_gt : (1 / 2 : ℝ) < Real.sinh (Real.pi / 4) ^ 2 := by
  have hpi : (3 / 4 : ℝ) < Real.pi / 4 := by linarith [Real.pi_gt_three]
  have he1 : (2 : ℝ) < Real.exp (3 / 4 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 4 by norm_num) 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, pow_one, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_ofNat] at hsum
    linarith
  have hexp_pos : 0 < Real.exp (3 / 4 : ℝ) := Real.exp_pos _
  have he2 : Real.exp (-(3 / 4 : ℝ)) < 1 / 2 := by
    rw [Real.exp_neg]
    exact inv_lt_of_inv_lt₀ (by positivity) (by linarith)
  have hs34 : (3 / 4 : ℝ) < Real.sinh (3 / 4 : ℝ) := by rw [Real.sinh_eq]; linarith
  have hs : (3 / 4 : ℝ) < Real.sinh (Real.pi / 4) :=
    hs34.trans_le (Real.sinh_le_sinh.mpr hpi.le)
  nlinarith

private lemma sin_add_mul_I_real (x y : ℝ) :
    Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I) =
      (Real.sin x * Real.cosh y : ℂ) + (Real.cos x * Real.sinh y : ℂ) * Complex.I := by
  rw [Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast
  ring

private lemma cos_add_mul_I_real (x y : ℝ) :
    Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I) =
      (Real.cos x * Real.cosh y : ℂ) - (Real.sin x * Real.sinh y : ℂ) * Complex.I := by
  rw [Complex.cos_add, Complex.sin_mul_I, Complex.cos_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast
  ring

private lemma normSq_sin_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)) = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [sin_add_mul_I_real, Complex.normSq_apply]
  have hc : Real.cosh y ^ 2 = Real.sinh y ^ 2 + 1 := by linarith [Real.cosh_sq_sub_sinh_sq y]
  have hs := Real.sin_sq_add_cos_sq x
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  nlinarith [hc, hs, sq_nonneg (Real.sin x), sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y)]

private lemma normSq_cos_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)) = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [cos_add_mul_I_real, Complex.normSq_apply]
  have hc : Real.cosh y ^ 2 = Real.sinh y ^ 2 + 1 := by linarith [Real.cosh_sq_sub_sinh_sq y]
  have hs := Real.sin_sq_add_cos_sq x
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
    zero_add, zero_sub]
  nlinarith [hc, hs, sq_nonneg (Real.sin x), sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y)]

private lemma tan_norm_band {t : ℂ} (ht : 1 / 2 ≤ |t.im|) :
    Complex.cos (Real.pi * t / 2) ≠ 0 ∧
      1 / 2 ≤ ‖Complex.tan (Real.pi * t / 2)‖ ∧ ‖Complex.tan (Real.pi * t / 2)‖ ≤ 2 := by
  set x : ℝ := Real.pi * t.re / 2 with hx
  set y : ℝ := Real.pi * t.im / 2 with hy
  have hz : Real.pi * t / 2 = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [x, y, mul_div_assoc]
  have hy_ge : Real.pi / 4 ≤ |y| := by
    simp only [y, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hsinh_abs : Real.sinh (Real.pi / 4) ≤ |Real.sinh y| := by
    rcases le_or_gt 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0] at hy_ge
      rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hy0)]
      exact Real.sinh_le_sinh.mpr hy_ge
    · rw [abs_of_neg hy0] at hy_ge
      rw [abs_of_neg (Real.sinh_neg_iff.mpr hy0), ← Real.sinh_neg]
      exact Real.sinh_le_sinh.mpr hy_ge
  have hsinh2 : (1 / 2 : ℝ) < Real.sinh y ^ 2 := by
    have hs0 : 0 ≤ Real.sinh (Real.pi / 4) := Real.sinh_nonneg_iff.mpr (by positivity)
    have hsq : Real.sinh (Real.pi / 4) ^ 2 ≤ Real.sinh y ^ 2 := by
      rw [← sq_abs (Real.sinh y)]
      exact pow_le_pow_left₀ hs0 hsinh_abs 2
    exact abs_sinh_pi_quarter_gt.trans_le hsq
  have hsin_sq : 0 ≤ Real.sin x ^ 2 ∧ Real.sin x ^ 2 ≤ 1 := ⟨sq_nonneg _, Real.sin_sq_le_one x⟩
  have hcos_sq : 0 ≤ Real.cos x ^ 2 ∧ Real.cos x ^ 2 ≤ 1 := ⟨sq_nonneg _, Real.cos_sq_le_one x⟩
  have hncos_sq : ‖Complex.cos (Real.pi * t / 2)‖ ^ 2 = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
    rw [hz, ← Complex.normSq_eq_norm_sq, normSq_cos_add_mul_I]
  have hnsin_sq : ‖Complex.sin (Real.pi * t / 2)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
    rw [hz, ← Complex.normSq_eq_norm_sq, normSq_sin_add_mul_I]
  have hcos_pos : 0 < ‖Complex.cos (Real.pi * t / 2)‖ ^ 2 := by linarith
  have hcos_ne : Complex.cos (Real.pi * t / 2) ≠ 0 := by
    intro h0; rw [h0, norm_zero, pow_two, mul_zero] at hcos_pos; linarith
  have htan_sq : ‖Complex.tan (Real.pi * t / 2)‖ ^ 2 =
      (Real.sin x ^ 2 + Real.sinh y ^ 2) / (Real.cos x ^ 2 + Real.sinh y ^ 2) := by
    rw [Complex.tan_eq_sin_div_cos, norm_div, div_pow, hnsin_sq, hncos_sq]
  have hlo : 1 / 4 ≤ ‖Complex.tan (Real.pi * t / 2)‖ ^ 2 := by
    rw [htan_sq, le_div_iff₀ (by linarith)]; nlinarith
  have hhi : ‖Complex.tan (Real.pi * t / 2)‖ ^ 2 ≤ 4 := by
    rw [htan_sq, div_le_iff₀ (by linarith)]; nlinarith
  refine ⟨hcos_ne, ?_, ?_⟩
  · nlinarith [norm_nonneg (Complex.tan (Real.pi * t / 2))]
  · nlinarith [norm_nonneg (Complex.tan (Real.pi * t / 2))]

lemma stripG_far_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ, |t.re| ≤ 1 → 1 / 2 ≤ |t.im| →
    ‖stripG t‖ ≤ C * (1 + |t.im|) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨2 * Real.log 2 + Real.log Real.pi + Real.pi + 1, by positivity, fun t hre him => ?_⟩
  have ht_ne : t ≠ 0 := fun h0 => by rw [h0] at him; simp at him; linarith
  have htan := tan_norm_band him
  set w : ℂ := Complex.tan (Real.pi * t / 2) / ((Real.pi : ℂ) * t / 2)
  have hSG : stripG t = Complex.log w := by unfold stripG; simp [ht_ne, w]
  have hlog_norm : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
    have hsplit : Complex.log w = (Real.log ‖w‖ : ℂ) + (Complex.arg w : ℂ) * Complex.I := rfl
    calc ‖Complex.log w‖
        ≤ ‖(Real.log ‖w‖ : ℂ)‖ + ‖(Complex.arg w : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |Real.log ‖w‖| + |Complex.arg w| := by simp
      _ ≤ |Real.log ‖w‖| + Real.pi := by linarith [Complex.abs_arg_le_pi w]
  have ht_norm_lo : (1 / 2 : ℝ) ≤ ‖t‖ := him.trans (Complex.abs_im_le_norm t)
  have ht_norm_hi : ‖t‖ ≤ 1 + |t.im| :=
    (Complex.norm_le_abs_re_add_abs_im t).trans (by linarith)
  have hpt_lo : 1 / 2 ≤ ‖(Real.pi : ℂ) * t / 2‖ := by
    have hnorm : ‖(Real.pi : ℂ) * t / 2‖ = Real.pi / 2 * ‖t‖ := by
      simp [abs_of_pos Real.pi_pos]; ring
    rw [hnorm]; nlinarith [Real.pi_gt_three]
  have hpt_hi : ‖(Real.pi : ℂ) * t / 2‖ ≤ Real.pi * (1 + |t.im|) := by
    have hnorm : ‖(Real.pi : ℂ) * t / 2‖ = Real.pi / 2 * ‖t‖ := by
      simp [abs_of_pos Real.pi_pos]; ring
    rw [hnorm]; nlinarith [Real.pi_pos]
  have hw_norm : ‖w‖ = ‖Complex.tan (Real.pi * t / 2)‖ / ‖(Real.pi : ℂ) * t / 2‖ := norm_div _ _
  have hpt_pos : 0 < ‖(Real.pi : ℂ) * t / 2‖ := by linarith
  have htan_pos : 0 < ‖Complex.tan (Real.pi * t / 2)‖ := by linarith [htan.2.1]
  have hlog_tan : |Real.log ‖Complex.tan (Real.pi * t / 2)‖| ≤ Real.log 2 := by
    rw [abs_le]
    constructor
    · rw [← Real.log_inv, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      exact Real.log_le_log (by norm_num) htan.2.1
    · exact Real.log_le_log htan_pos htan.2.2
  have hlog_pt : |Real.log ‖(Real.pi : ℂ) * t / 2‖| ≤ Real.log 2 + Real.log Real.pi + |t.im| := by
    rw [abs_le]
    constructor
    · have h1 : -Real.log 2 ≤ Real.log ‖(Real.pi : ℂ) * t / 2‖ := by
        rw [← Real.log_inv, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        exact Real.log_le_log (by positivity) hpt_lo
      have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
      linarith [abs_nonneg t.im]
    · have h1 : Real.log ‖(Real.pi : ℂ) * t / 2‖ ≤ Real.log (Real.pi * (1 + |t.im|)) :=
        Real.log_le_log hpt_pos hpt_hi
      have h2 : Real.log (Real.pi * (1 + |t.im|)) = Real.log Real.pi + Real.log (1 + |t.im|) :=
        Real.log_mul Real.pi_pos.ne' (by positivity)
      have h3 : Real.log (1 + |t.im|) ≤ |t.im| := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |t.im|)]
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
  have hlog_w : |Real.log ‖w‖| ≤ 2 * Real.log 2 + Real.log Real.pi + |t.im| := by
    rw [hw_norm, Real.log_div htan_pos.ne' hpt_pos.ne']
    calc |Real.log ‖Complex.tan (Real.pi * t / 2)‖ - Real.log ‖(Real.pi : ℂ) * t / 2‖|
        ≤ |Real.log ‖Complex.tan (Real.pi * t / 2)‖| + |Real.log ‖(Real.pi : ℂ) * t / 2‖| := abs_sub _ _
      _ ≤ _ := by linarith
  rw [hSG]
  have hge : 1 ≤ 1 + |t.im| := by linarith [abs_nonneg t.im]
  have hc1 : 0 ≤ 2 * Real.log 2 + Real.log Real.pi + Real.pi := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have := Real.log_nonneg (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
    positivity
  calc ‖Complex.log w‖
      ≤ 2 * Real.log 2 + Real.log Real.pi + Real.pi + |t.im| := by linarith
    _ ≤ (2 * Real.log 2 + Real.log Real.pi + Real.pi) * (1 + |t.im|) + 1 * (1 + |t.im|) := by
        nlinarith [abs_nonneg t.im]
    _ = (2 * Real.log 2 + Real.log Real.pi + Real.pi + 1) * (1 + |t.im|) := by ring

lemma stripG_differentiableOn :
    DifferentiableOn ℂ stripG {ζ : ℂ | |ζ.re| < 1 ∧ ζ ≠ 0} := fun _ hζ =>
  (stripG_hasDerivAt hζ.2 hζ.1).differentiableAt.differentiableWithinAt

private lemma stripG_imag_contDiffOn :
    ContDiffOn ℝ 2 (fun τ : ℝ => stripG ((τ : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} := by
  have hopen : IsOpen {ζ : ℂ | |ζ.re| < 1 ∧ ζ ≠ 0} :=
    (isOpen_lt continuous_re.abs continuous_const).inter isOpen_ne
  have hcd : ContDiffOn ℂ 2 stripG {ζ : ℂ | |ζ.re| < 1 ∧ ζ ≠ 0} :=
    stripG_differentiableOn.contDiffOn hopen
  have hlin : ContDiff ℝ 2 (fun τ : ℝ => (τ : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  refine (hcd.restrict_scalars ℝ).comp hlin.contDiffOn fun τ hτ => ?_
  simp only [mem_setOf_eq, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, abs_zero, zero_lt_one, true_and]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hτ) Complex.I_ne_zero

lemma stripG_imag_deriv_pos {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t : ℝ => stripG ((t : ℂ) * Complex.I))
      (Complex.I * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) -
        1 / ((τ : ℂ) * Complex.I))) τ := by
  have hζ0 : (τ : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hτ.ne') Complex.I_ne_zero
  have hre : |((τ : ℂ) * Complex.I).re| < 1 := by simp
  have hs := stripG_hasDerivAt hζ0 hre
  have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
  refine (hs.comp τ hl).congr_deriv ?_
  ring

private lemma abs_sinh_pi_half_gt_one : (1 : ℝ) < Real.sinh (Real.pi / 2) := by
  have h1 : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have he1 : (5 / 2 : ℝ) < Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, pow_one, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_ofNat] at hsum
    norm_num at hsum
    linarith
  have he2 : Real.exp (-1 : ℝ) < 1 / 2 := by
    rw [Real.exp_neg]
    exact inv_lt_of_inv_lt₀ (by norm_num) (by linarith)
  have hs1 : (1 : ℝ) < Real.sinh 1 := by rw [Real.sinh_eq]; linarith
  exact hs1.trans_le (Real.sinh_le_sinh.mpr h1.le)

lemma stripG_imag_deriv_far_bounds {τ : ℝ} (hτ : 1 / 2 ≤ τ) :
    ‖deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ ≤ Real.pi + 2 ∧
    ‖deriv (deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I))) τ‖ ≤ 2 * Real.pi ^ 2 + 4 := by
  have hτpos : 0 < τ := by linarith
  have hsin_eq : Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) =
      (Real.sinh (Real.pi * τ) : ℂ) * Complex.I := by
    have harg : (Real.pi : ℂ) * ((τ : ℂ) * Complex.I) = ((0 : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, sin_add_mul_I_real, Real.sin_zero, Real.cos_zero]
    simp
  have hcos_eq : Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) =
      (Real.cosh (Real.pi * τ) : ℂ) := by
    have harg : (Real.pi : ℂ) * ((τ : ℂ) * Complex.I) = ((0 : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, cos_add_mul_I_real, Real.cos_zero, Real.sin_zero]
    simp
  have hsh_gt : (1 : ℝ) < Real.sinh (Real.pi * τ) := by
    have hle : Real.pi / 2 ≤ Real.pi * τ := by nlinarith [Real.pi_pos]
    exact abs_sinh_pi_half_gt_one.trans_le (Real.sinh_le_sinh.mpr hle)
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) ≠ 0 := by
    rw [hsin_eq]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) Complex.I_ne_zero
  have hnsin : 1 < ‖Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I))‖ := by
    rw [hsin_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    exact hsh_gt
  have hd1 : ‖deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ ≤ Real.pi + 2 := by
    rw [(stripG_imag_deriv_pos hτpos).deriv, norm_mul, Complex.norm_I, one_mul]
    calc ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) -
          1 / ((τ : ℂ) * Complex.I)‖
        ≤ ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I))‖ +
          ‖1 / ((τ : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ Real.pi + 2 := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
            norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, abs_of_pos hτpos]
          have h1 : Real.pi / ‖Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I))‖ ≤ Real.pi :=
            div_le_self Real.pi_pos.le hnsin.le
          have h2 : 1 / τ ≤ 2 := by rw [div_le_iff₀ hτpos]; linarith
          linarith
  have hd2 : ‖deriv (deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I))) τ‖ ≤ 2 * Real.pi ^ 2 + 4 := by
    have hev : deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) =ᶠ[𝓝 τ]
        fun t : ℝ => Complex.I * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) -
          1 / ((t : ℂ) * Complex.I)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hτpos] with t ht
      exact (stripG_imag_deriv_pos ht).deriv
    have harg_hd : HasDerivAt (fun t : ℝ => (Real.pi : ℂ) * ((t : ℂ) * Complex.I))
        ((Real.pi : ℂ) * Complex.I) τ := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I).const_mul (Real.pi : ℂ)
      refine this.congr_deriv ?_; simp
    have hsin_hd : HasDerivAt (fun t : ℝ => Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)))
        (Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) * ((Real.pi : ℂ) * Complex.I)) τ :=
      (Complex.hasDerivAt_sin _).comp τ harg_hd
    have hdiv1 := (hasDerivAt_const τ (Real.pi : ℂ)).div hsin_hd hsin_ne
    have hτI_ne : (τ : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hτpos.ne') Complex.I_ne_zero
    have hτI_hd : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ :=
      ((hasDerivAt_id τ).ofReal_comp).mul_const Complex.I |>.congr_deriv (by simp)
    have hdiv2 := (hasDerivAt_const τ (1 : ℂ)).div hτI_hd hτI_ne
    have hcomb := (hdiv1.sub hdiv2).const_mul Complex.I
    rw [hev.deriv_eq]
    rw [show deriv (fun t : ℝ => Complex.I * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) -
        1 / ((t : ℂ) * Complex.I))) τ = _ from hcomb.deriv]
    have hd_simp :
        Complex.I * ((0 * Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) -
          (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) *
            ((Real.pi : ℂ) * Complex.I))) /
          Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) ^ 2 -
          (0 * ((τ : ℂ) * Complex.I) - 1 * Complex.I) / ((τ : ℂ) * Complex.I) ^ 2) =
        (Real.pi : ℂ) ^ 2 * Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) /
          Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) ^ 2 -
          1 / ((τ : ℂ) * Complex.I) ^ 2 := by
      ring_nf; simp [Complex.I_sq]
    rw [hd_simp]
    have hcosh_le : Real.cosh (Real.pi * τ) ≤ 1 + Real.sinh (Real.pi * τ) := by
      have hch0 : 0 ≤ Real.cosh (Real.pi * τ) := (Real.cosh_pos _).le
      have hsq : Real.cosh (Real.pi * τ) ^ 2 ≤ (1 + Real.sinh (Real.pi * τ)) ^ 2 := by
        nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi * τ)]
      nlinarith
    have hratio : Real.cosh (Real.pi * τ) / Real.sinh (Real.pi * τ) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hsh_gt]
    have hn1 : ‖(Real.pi : ℂ) ^ 2 * Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) /
        Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) ^ 2‖ ≤ 2 * Real.pi ^ 2 := by
      rw [norm_div, norm_mul, norm_pow, norm_pow, hcos_eq, hsin_eq, norm_mul]
      simp only [Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_pos (Real.cosh_pos _), abs_of_pos (by linarith : 0 < Real.sinh (Real.pi * τ))]
      calc Real.pi ^ 2 * Real.cosh (Real.pi * τ) / Real.sinh (Real.pi * τ) ^ 2
          = Real.pi ^ 2 * (Real.cosh (Real.pi * τ) / Real.sinh (Real.pi * τ) ^ 2) := by ring
        _ ≤ Real.pi ^ 2 * 2 := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = 2 * Real.pi ^ 2 := by ring
    have hn2 : ‖(1 : ℂ) / ((τ : ℂ) * Complex.I) ^ 2‖ ≤ 4 := by
      rw [norm_div, norm_one, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hτpos, div_le_iff₀ (by positivity)]
      nlinarith
    exact (norm_sub_le _ _).trans (add_le_add hn1 hn2)
  exact ⟨hd1, hd2⟩

private lemma stripG_far_EJOn : ∃ M : ℝ, 0 ≤ M ∧
    EJOn (Ici (1 / 2 : ℝ)) (fun τ : ℝ => stripG ((τ : ℂ) * Complex.I)) 0 1 0 M := by
  obtain ⟨Cg, hCg0, hCg⟩ := stripG_far_bound
  set M : ℝ := max Cg (max (Real.pi + 2) (2 * Real.pi ^ 2 + 4))
  have hM0 : 0 ≤ M := hCg0.trans (le_max_left _ _)
  refine ⟨M, hM0, hM0, stripG_imag_contDiffOn, ?_, ?_, ?_⟩
  · intro τ hτ _
    have hτ_le : 1 / 2 ≤ τ := hτ
    have hτpos : 0 < τ := by linarith
    have him : 1 / 2 ≤ |((τ : ℂ) * Complex.I).im| := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, add_zero, abs_of_pos hτpos]
      exact hτ_le
    have h0 := hCg ((τ : ℂ) * Complex.I) (by simp) him
    rw [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, abs_of_pos hτpos] at h0
    have hej0 : ejW 0 1 0 0 τ = 1 + τ := by
      simp [ejW, abs_of_pos hτpos]
    rw [hej0]
    exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · intro τ hτ _
    have hτ_le : 1 / 2 ≤ τ := hτ
    have hd1 := (stripG_imag_deriv_far_bounds hτ_le).1
    have hM1 : Real.pi + 2 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hτpos : 0 < τ := by linarith
    have hw1 : 1 ≤ ejW 0 1 0 1 τ := by
      simp only [ejW, zero_sub, Nat.cast_one, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one,
        abs_of_pos hτpos, Real.rpow_neg hτpos.le, Real.rpow_one]
      rw [show (1 + 1 : ℕ) = 2 by rfl, inv_mul_eq_div, le_div_iff₀ hτpos]
      nlinarith
    have h1 := hd1.trans hM1
    exact h1.trans (le_mul_of_one_le_right hM0 hw1)
  · intro τ hτ _
    have hτ_le : 1 / 2 ≤ τ := hτ
    have hd2 := (stripG_imag_deriv_far_bounds hτ_le).2
    have hM2 : 2 * Real.pi ^ 2 + 4 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    have hτpos : 0 < τ := by linarith
    have hw2 : 1 ≤ ejW 0 1 0 2 τ := by
      simp only [ejW, zero_sub, Nat.cast_ofNat, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one,
        abs_of_pos hτpos]
      rw [show (1 + 2 : ℕ) = 3 by rfl, show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hτpos.le, Real.rpow_natCast, inv_mul_eq_div, le_div_iff₀ (pow_pos hτpos 2)]
      nlinarith [sq_nonneg τ]
    have h2 := hd2.trans hM2
    exact h2.trans (le_mul_of_one_le_right hM0 hw2)

/-! ### `phiKill`, `ctHG`, and `fctWarpA` `EJOn` on `τ ≥ 1/2` -/

private lemma clm_deriv_one {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (L : ℂ →L[ℝ] ℝ) (t : ℝ) :
    L (deriv f t) = deriv (fun s : ℝ => L (f s)) t :=
  (L.hasFDerivAt.comp_hasDerivAt t (hf.differentiable (by norm_num) t).hasDerivAt).deriv.symm

private lemma clm_deriv_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (L : ℂ →L[ℝ] ℝ) (t : ℝ) :
    L (deriv (deriv f) t) = iteratedDeriv 2 (fun s : ℝ => L (f s)) t := by
  have hd : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ) + 1) f from hf)).2.2).differentiable (by norm_num)
  have hfn : (fun s : ℝ => L (deriv f s)) = deriv (fun s : ℝ => L (f s)) :=
    funext (clm_deriv_one hf L)
  have h1 := (L.hasFDerivAt.comp_hasDerivAt t (hd t).hasDerivAt).deriv.symm
  dsimp only [Function.comp_def] at h1
  rw [hfn] at h1
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using h1

private lemma phiKill_far_EJOn {a : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧
      EJOn (Ici (1 / 2 : ℝ)) (fun τ : ℝ => FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)) 0 0 0 M := by
  obtain ⟨C, hC0, hC⟩ := FctSym.phiKill_tsymbol
  set f : ℝ → ℂ := fun s => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)
  have hcd : ContDiff ℝ 2 f := (FctSym.contDiff_phiKill_imag ha).of_le (by norm_cast)
  set M : ℝ := 2 * max (C 0) (max (C 1) (C 2))
  have hM0 : 0 ≤ M := by have := hC0 0; positivity
  have hre_bd : ∀ z, |Complex.reCLM z| ≤ ‖z‖ := fun z => Complex.abs_re_le_norm z
  have him_bd : ∀ z, |Complex.imCLM z| ≤ ‖z‖ := fun z => Complex.abs_im_le_norm z
  refine ⟨M, hM0, hM0, hcd.contDiffOn, ?_, ?_, ?_⟩
  · intro τ hτ _
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hr := (hC a τ ha hτpos Complex.reCLM hre_bd 0).1
    have hi := (hC a τ ha hτpos Complex.imCLM him_bd 0).1
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at hr hi
    have hnorm : ‖f τ‖ ≤ |Complex.reCLM (f τ)| + |Complex.imCLM (f τ)| :=
      Complex.norm_le_abs_re_add_abs_im (f τ)
    have hmin : min 1 ((τ / a) ^ 8) ≤ 1 := min_le_left _ _
    have h1 : ‖f τ‖ ≤ 2 * C 0 := by
      dsimp only [f] at hnorm ⊢
      calc ‖FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)‖
          ≤ |Complex.reCLM (FctPhiKill.phiKill a ((τ : ℂ) * Complex.I))| +
            |Complex.imCLM (FctPhiKill.phiKill a ((τ : ℂ) * Complex.I))| := hnorm
        _ ≤ C 0 * min 1 ((τ / a) ^ 8) + C 0 * min 1 ((τ / a) ^ 8) := add_le_add hr hi
        _ ≤ C 0 * 1 + C 0 * 1 := by gcongr; exact hC0 0; exact hC0 0
        _ = 2 * C 0 := by ring
    have hC0M : 2 * C 0 ≤ M := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    simpa [ejW, f] using h1.trans hC0M
  · intro τ hτ _
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hr := (hC a τ ha hτpos Complex.reCLM hre_bd 1).1
    have hi := (hC a τ ha hτpos Complex.imCLM him_bd 1).1
    simp only [pow_one, iteratedDeriv_one] at hr hi
    rw [← clm_deriv_one hcd Complex.reCLM τ, abs_mul, abs_of_pos hτpos] at hr
    rw [← clm_deriv_one hcd Complex.imCLM τ, abs_mul, abs_of_pos hτpos] at hi
    have hr' : |Complex.reCLM (deriv f τ)| ≤ C 1 * τ⁻¹ := by
      rw [← le_div_iff₀' hτpos] at hr
      calc |Complex.reCLM (deriv f τ)| ≤ C 1 * min 1 ((τ / a) ^ 8) / τ := hr
        _ ≤ C 1 * 1 / τ := by gcongr; exact hC0 1; exact min_le_left _ _
        _ = C 1 * τ⁻¹ := by ring
    have hi' : |Complex.imCLM (deriv f τ)| ≤ C 1 * τ⁻¹ := by
      rw [← le_div_iff₀' hτpos] at hi
      calc |Complex.imCLM (deriv f τ)| ≤ C 1 * min 1 ((τ / a) ^ 8) / τ := hi
        _ ≤ C 1 * 1 / τ := by gcongr; exact hC0 1; exact min_le_left _ _
        _ = C 1 * τ⁻¹ := by ring
    have hnorm := (Complex.norm_le_abs_re_add_abs_im (deriv f τ)).trans (add_le_add hr' hi')
    have hC1M : 2 * C 1 ≤ M :=
      mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) (by norm_num)
    have hej : τ⁻¹ ≤ ejW 0 0 0 1 τ := by
      simp only [ejW, zero_sub, Nat.cast_one, zero_add, mul_zero, zero_mul, neg_zero,
        Real.exp_zero, mul_one, abs_of_pos hτpos, Real.rpow_neg hτpos.le, Real.rpow_one, pow_one]
      exact le_mul_of_one_le_right (inv_nonneg.mpr hτpos.le) (by linarith : (1 : ℝ) ≤ 1 + τ)
    calc ‖deriv f τ‖ ≤ (2 * C 1) * τ⁻¹ := by linarith
      _ ≤ M * τ⁻¹ := mul_le_mul_of_nonneg_right hC1M (inv_nonneg.mpr hτpos.le)
      _ ≤ M * ejW 0 0 0 1 τ := mul_le_mul_of_nonneg_left hej hM0
  · intro τ hτ _
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hr := (hC a τ ha hτpos Complex.reCLM hre_bd 2).1
    have hi := (hC a τ ha hτpos Complex.imCLM him_bd 2).1
    rw [← clm_deriv_two hcd Complex.reCLM τ, abs_mul, abs_of_pos (pow_pos hτpos 2)] at hr
    rw [← clm_deriv_two hcd Complex.imCLM τ, abs_mul, abs_of_pos (pow_pos hτpos 2)] at hi
    have hr' : |Complex.reCLM (deriv (deriv f) τ)| ≤ C 2 * (τ ^ 2)⁻¹ := by
      rw [← le_div_iff₀' (pow_pos hτpos 2)] at hr
      calc |Complex.reCLM (deriv (deriv f) τ)| ≤ C 2 * min 1 ((τ / a) ^ 8) / τ ^ 2 := hr
        _ ≤ C 2 * 1 / τ ^ 2 := by gcongr; exact hC0 2; exact min_le_left _ _
        _ = C 2 * (τ ^ 2)⁻¹ := by ring
    have hi' : |Complex.imCLM (deriv (deriv f) τ)| ≤ C 2 * (τ ^ 2)⁻¹ := by
      rw [← le_div_iff₀' (pow_pos hτpos 2)] at hi
      calc |Complex.imCLM (deriv (deriv f) τ)| ≤ C 2 * min 1 ((τ / a) ^ 8) / τ ^ 2 := hi
        _ ≤ C 2 * 1 / τ ^ 2 := by gcongr; exact hC0 2; exact min_le_left _ _
        _ = C 2 * (τ ^ 2)⁻¹ := by ring
    have hnorm := (Complex.norm_le_abs_re_add_abs_im (deriv (deriv f) τ)).trans (add_le_add hr' hi')
    have hC2M : 2 * C 2 ≤ M :=
      mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) (by norm_num)
    have hej : (τ ^ 2)⁻¹ ≤ ejW 0 0 0 2 τ := by
      simp only [ejW, zero_sub, Nat.cast_ofNat, zero_add, mul_zero, zero_mul, neg_zero,
        Real.exp_zero, mul_one, abs_of_pos hτpos]
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτpos.le, Real.rpow_natCast]
      exact le_mul_of_one_le_right (inv_nonneg.mpr (pow_nonneg hτpos.le 2))
        (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + τ))
    calc ‖deriv (deriv f) τ‖ ≤ (2 * C 2) * (τ ^ 2)⁻¹ := by linarith
      _ ≤ M * (τ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hC2M (inv_nonneg.mpr (pow_nonneg hτpos.le 2))
      _ ≤ M * ejW 0 0 0 2 τ := mul_le_mul_of_nonneg_left hej hM0

private lemma rpow_neg52_le_eight {τ : ℝ} (hτ : 1 / 2 ≤ τ) : τ ^ (-(5 / 2 : ℝ)) ≤ 8 := by
  have h1 : τ ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hτ (by norm_num)
  have h2 : (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  have h3 : (1 / 2 : ℝ) ^ (-3 : ℝ) = 8 := by
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  linarith

private lemma ctHG_far_EJOn (ε : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    EJOn (Ici (1 / 2 : ℝ)) (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I)) 0 10 1 M := by
  obtain ⟨Mze, hZ⟩ := ejZE ε
  have hprod : EJ (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I))
      (-(5 / 2 : ℝ)) 10 1 (4 * (4 * Mze * 9) * 9) := by
    have hp := (hZ.mul edgeR_EJ).mul edgeS_EJ
    have heq : (fun τ : ℝ =>
        uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)) *
          edgeR τ * edgeS τ) = fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I) :=
      funext fun τ => (ctHG_edge ε τ).symm
    rw [heq] at hp
    exact hp.cast (a' := -(5 / 2 : ℝ)) (b' := 1) (by norm_num) (by norm_num)
  have hM0 : 0 ≤ 4 * (4 * Mze * 9) * 9 := hprod.hM
  refine ⟨8 * (4 * (4 * Mze * 9) * 9), by positivity, by positivity, hprod.c2, ?_, ?_, ?_⟩
  · intro τ hτ hτ0
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hpow : |τ| ^ (-(5 / 2 : ℝ) - ((0 : ℕ) : ℝ)) ≤ 8 * |τ| ^ (0 - ((0 : ℕ) : ℝ)) := by
      simp only [abs_of_pos hτpos, Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      exact rpow_neg52_le_eight hτ
    have hw : ejW (-(5 / 2)) 10 1 0 τ ≤ 8 * ejW 0 10 1 0 τ := by
      unfold ejW
      calc |τ| ^ (-(5 / 2 : ℝ) - ((0 : ℕ) : ℝ)) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(Real.pi * 1 * |τ|))
          ≤ (8 * |τ| ^ (0 - ((0 : ℕ) : ℝ))) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(Real.pi * 1 * |τ|)) := by
            gcongr
        _ = 8 * ejW 0 10 1 0 τ := by unfold ejW; ring
    exact (hprod.b0 τ hτ0).trans ((mul_le_mul_of_nonneg_left hw hM0).trans_eq (by ring))
  · intro τ hτ hτ0
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hpow : |τ| ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ)) ≤ 8 * |τ| ^ (0 - ((1 : ℕ) : ℝ)) := by
      simp only [abs_of_pos hτpos, Nat.cast_one]
      rw [show -(5 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) + (-1 : ℝ) by ring, Real.rpow_add hτpos,
        show (0 : ℝ) - 1 = -1 by ring]
      exact mul_le_mul_of_nonneg_right (rpow_neg52_le_eight hτ) (Real.rpow_nonneg hτpos.le _)
    have hw : ejW (-(5 / 2)) 10 1 1 τ ≤ 8 * ejW 0 10 1 1 τ := by
      unfold ejW
      calc |τ| ^ (-(5 / 2 : ℝ) - ((1 : ℕ) : ℝ)) * (1 + |τ|) ^ (10 + 1) * Real.exp (-(Real.pi * 1 * |τ|))
          ≤ (8 * |τ| ^ (0 - ((1 : ℕ) : ℝ))) * (1 + |τ|) ^ (10 + 1) * Real.exp (-(Real.pi * 1 * |τ|)) := by
            gcongr
        _ = 8 * ejW 0 10 1 1 τ := by unfold ejW; ring
    exact (hprod.b1 τ hτ0).trans ((mul_le_mul_of_nonneg_left hw hM0).trans_eq (by ring))
  · intro τ hτ hτ0
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hpow : |τ| ^ (-(5 / 2 : ℝ) - ((2 : ℕ) : ℝ)) ≤ 8 * |τ| ^ (0 - ((2 : ℕ) : ℝ)) := by
      simp only [abs_of_pos hτpos, Nat.cast_ofNat]
      rw [show -(5 / 2 : ℝ) - 2 = -(5 / 2 : ℝ) + (-2 : ℝ) by ring, Real.rpow_add hτpos,
        show (0 : ℝ) - 2 = -2 by ring]
      exact mul_le_mul_of_nonneg_right (rpow_neg52_le_eight hτ) (Real.rpow_nonneg hτpos.le _)
    have hw : ejW (-(5 / 2)) 10 1 2 τ ≤ 8 * ejW 0 10 1 2 τ := by
      unfold ejW
      calc |τ| ^ (-(5 / 2 : ℝ) - ((2 : ℕ) : ℝ)) * (1 + |τ|) ^ (10 + 2) * Real.exp (-(Real.pi * 1 * |τ|))
          ≤ (8 * |τ| ^ (0 - ((2 : ℕ) : ℝ))) * (1 + |τ|) ^ (10 + 2) * Real.exp (-(Real.pi * 1 * |τ|)) := by
            gcongr
        _ = 8 * ejW 0 10 1 2 τ := by unfold ejW; ring
    exact (hprod.b2 τ hτ0).trans ((mul_le_mul_of_nonneg_left hw hM0).trans_eq (by ring))

lemma fctWarpA_far_EJOn {K4 ε c L1 α P : ℝ} (hc : 0 < c) (hP : 0 ≤ P)
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) (fun _ => P)) :
    ∃ M : ℝ, 0 ≤ M ∧
      EJOn (Ici (1 / 2 : ℝ)) (fun τ : ℝ => fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) 0 11 1 M := by
  obtain ⟨Mg, hMg0, hMg⟩ := stripG_far_EJOn
  have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc _
  obtain ⟨Mpk, hMpk0, hMpk⟩ := phiKill_far_EJOn ha
  obtain ⟨Mhg, hMhg0, hMhg⟩ := ctHG_far_EJOn ε
  set f1 : ℝ → ℂ := fun τ => stripG ((τ : ℂ) * Complex.I)
  set f2 : ℝ → ℂ := fun τ => (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)
  have hf2 : EJOn (Ici (1 / 2 : ℝ)) f2 0 0 0 (|L1| * Mpk) := by
    have hm := hMpk.const_mul (L1 : ℂ)
    simpa [f2, Complex.norm_real, Real.norm_eq_abs] using hm
  have hejw_le : ∀ (j : ℕ) {τ : ℝ}, τ ≠ 0 → ejW 0 0 0 j τ ≤ ejW 0 1 0 j τ := fun j τ hτ => by
    unfold ejW
    have hge : (1 + |τ|) ^ (0 + j) ≤ (1 + |τ|) ^ (1 + j) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (by omega)
    gcongr
  have hf12 : EJOn (Ici (1 / 2 : ℝ)) (fun τ => f1 τ + f2 τ) 0 1 0 (Mg + |L1| * Mpk) := by
    refine ⟨by positivity, hMg.c2.add hf2.c2, ?_, ?_, ?_⟩
    · intro τ hτ hτ0
      have h0 := (norm_add_le (f1 τ) (f2 τ)).trans (add_le_add (hMg.b0 τ hτ hτ0) (hf2.b0 τ hτ hτ0))
      have h1 : |L1| * Mpk * ejW 0 0 0 0 τ ≤ |L1| * Mpk * ejW 0 1 0 0 τ :=
        mul_le_mul_of_nonneg_left (hejw_le 0 hτ0) (by positivity)
      linarith
    · intro τ hτ hτ0
      have hnh : {t : ℝ | t ≠ 0} ∈ 𝓝 τ := isOpen_ne.mem_nhds hτ0
      have hd1 : DifferentiableAt ℝ f1 τ :=
        ((hMg.c2.differentiableOn (by norm_num)).differentiableAt hnh)
      have hd2 : DifferentiableAt ℝ f2 τ :=
        ((hf2.c2.differentiableOn (by norm_num)).differentiableAt hnh)
      have hda : deriv (fun t => f1 t + f2 t) τ = deriv f1 τ + deriv f2 τ := deriv_add hd1 hd2
      rw [hda]
      have h0 := (norm_add_le _ _).trans (add_le_add (hMg.b1 τ hτ hτ0) (hf2.b1 τ hτ hτ0))
      have h1 : |L1| * Mpk * ejW 0 0 0 1 τ ≤ |L1| * Mpk * ejW 0 1 0 1 τ :=
        mul_le_mul_of_nonneg_left (hejw_le 1 hτ0) (by positivity)
      linarith
    · intro τ hτ hτ0
      have hnh : {t : ℝ | t ≠ 0} ∈ 𝓝 τ := isOpen_ne.mem_nhds hτ0
      have hcd1 : ContDiffOn ℝ 1 (deriv f1) {t : ℝ | t ≠ 0} :=
        (contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne (n := 1) |>.mp hMg.c2).2.2
      have hcd2 : ContDiffOn ℝ 1 (deriv f2) {t : ℝ | t ≠ 0} :=
        (contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne (n := 1) |>.mp hf2.c2).2.2
      have hdd1 : DifferentiableAt ℝ (deriv f1) τ :=
        ((hcd1.differentiableOn (by norm_num)).differentiableAt hnh)
      have hdd2 : DifferentiableAt ℝ (deriv f2) τ :=
        ((hcd2.differentiableOn (by norm_num)).differentiableAt hnh)
      have hev : deriv (fun t => f1 t + f2 t) =ᶠ[𝓝 τ] fun t => deriv f1 t + deriv f2 t := by
        filter_upwards [hnh] with t ht
        have ht1 := ((hMg.c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds ht))
        have ht2 := ((hf2.c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds ht))
        exact deriv_add ht1 ht2
      have hda2 : deriv (deriv (fun t => f1 t + f2 t)) τ = deriv (deriv f1) τ + deriv (deriv f2) τ := by
        rw [hev.deriv_eq]
        exact deriv_add hdd1 hdd2
      rw [hda2]
      have h0 := (norm_add_le _ _).trans (add_le_add (hMg.b2 τ hτ hτ0) (hf2.b2 τ hτ hτ0))
      have h1 : |L1| * Mpk * ejW 0 0 0 2 τ ≤ |L1| * Mpk * ejW 0 1 0 2 τ :=
        mul_le_mul_of_nonneg_left (hejw_le 2 hτ0) (by positivity)
      linarith
  have hD_ej : EJ (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) 0 0 0 P :=
    EJ.of_env2 hEnv hP 0 (fun _ => by simp)
  have hA := (hf12.mul hD_ej.to_on).mul hMhg
  refine ⟨4 * (4 * (Mg + |L1| * Mpk) * P) * Mhg, hA.hM, ?_⟩
  simpa [fctWarpA, f1, f2] using hA.cast (a' := 0) (b' := 1) (by norm_num) (by norm_num)

end FormalResearch.SignUncertainty
