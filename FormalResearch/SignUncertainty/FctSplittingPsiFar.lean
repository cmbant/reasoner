/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingLeftC2
public import FormalResearch.SignUncertainty.FctPhiKillSymbol
public import FormalResearch.SignUncertainty.StripAdmissLift
public import FormalResearch.SignUncertainty.FctDescentRay

/-!
# Exponential decay of `Ψ_c(iτ)` and its first two derivatives on the far left edge `|τ| ≥ 1/2`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.8 (`fct:splitting`), far-edge
estimate for `Ψ_c(iτ)` (`|τ| ≥ 1/2`, `j = 0, 1, 2`).

Starting from `FctDescentStmt h` alone (horizontal strip descent at `σ = 3/8 ∈ [5/16, 7/16]`):
* Horizontal FTC (`Fubini` on `[ε₀, 3/8] × [δ, 1]`, `δ ↓ 0`, `ε₀ ↓ 0`) expresses
  `K₀(iτ) Ψ_c(iτ) = K₀(3/8 + iτ) Ψ_c(3/8 + iτ) - ∫_{0}^{3/8} K₀(r + iτ) A_ε(r + iτ) dr`
  for `τ > 0`, giving `‖Ψ_c(iτ)‖ ≤ M₀ (1 + τ)^8 exp(-π τ)` on `τ ≥ 1/2`.
* Using the ODE `Ψ_c'(iτ) = i (A_ε(iτ) - (K₀'/K₀)(iτ) Ψ_c(iτ))` from `fctPsi_hasDerivAt_pos`,
  along with `EJOn` bounds for `A_ε(iτ)` and polynomial bounds for `(K₀'/K₀)(iτ)` and its
  derivative, gives matching `(1 + |τ|)^N exp(-π |τ|)` bounds for `∂_τ Ψ_c(iτ)` and `∂_τ^2 Ψ_c(iτ)`.
* Reflection by `fctPsi_conj` extends the `j = 0, 1, 2` bounds to `τ ≤ -1/2`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

/-! ### Part 1: `stripG` bounds and far-edge `EJOn` on `τ ≥ 1/2` -/

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

private lemma normSq_sin_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)) = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  have hc := Real.cosh_sq_sub_sinh_sq y
  have hs := Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (Real.sin x), sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y)]

private lemma normSq_cos_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)) = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_mul, Complex.sub_im, Complex.mul_im, mul_one, zero_sub]
  have hc := Real.cosh_sq_sub_sinh_sq y
  have hs := Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (Real.sin x), sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y)]

private lemma tan_norm_band {t : ℂ} (ht : 1 / 2 ≤ |t.im|) :
    Complex.cos (Real.pi * t / 2) ≠ 0 ∧
      1 / 2 ≤ ‖Complex.tan (Real.pi * t / 2)‖ ∧ ‖Complex.tan (Real.pi * t / 2)‖ ≤ 2 := by
  set x : ℝ := Real.pi * t.re / 2 with hx
  set y : ℝ := Real.pi * t.im / 2 with hy
  have hz : Real.pi * t / 2 = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [x, y, mul_div_assoc]
  have hy_ge : Real.pi / 4 ≤ |y| := by
    simp only [y, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos two_pos]
    nlinarith [Real.pi_pos]
  have hsinh_abs : Real.sinh (Real.pi / 4) ≤ |Real.sinh y| := by
    rw [← Real.sinh_abs]
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
    intro h0; rw [h0, norm_zero, sq] at hcos_pos; linarith
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
      exact Real.log_le_log (by positivity) htan.2.1
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

private lemma stripG_imag_deriv_pos {τ : ℝ} (hτ : 0 < τ) :
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
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, pow_one, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_ofNat] at hsum
    linarith
  have he2 : Real.exp (-1 : ℝ) < 1 / 2 := by
    rw [Real.exp_neg]
    exact inv_lt_of_inv_lt₀ (by norm_num) (by linarith)
  have hs1 : (1 : ℝ) < Real.sinh 1 := by rw [Real.sinh_eq]; linarith
  exact hs1.trans_le (Real.sinh_le_sinh.mpr h1.le)

private lemma stripG_imag_deriv_far_bounds {τ : ℝ} (hτ : 1 / 2 ≤ τ) :
    ‖deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ ≤ Real.pi + 2 ∧
    ‖deriv (deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I))) τ‖ ≤ 2 * Real.pi ^ 2 + 4 := by
  have hτpos : 0 < τ := by linarith
  have hsin_eq : Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) =
      (Real.sinh (Real.pi * τ) : ℂ) * Complex.I := by
    have harg : (Real.pi : ℂ) * ((τ : ℂ) * Complex.I) = ((Real.pi * τ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.sin_mul_I]
  have hcos_eq : Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) =
      (Real.cosh (Real.pi * τ) : ℂ) := by
    have harg : (Real.pi : ℂ) * ((τ : ℂ) * Complex.I) = ((Real.pi * τ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.cos_mul_I]
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
    have hdiv2 := (hasDerivAt_const τ (1 : ℂ)).div
      ((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I |>.congr_deriv (by simp)) hτI_ne
    have hcomb := (hdiv1.sub hdiv2).const_mul Complex.I
    rw [hev.deriv_eq, hcomb.deriv]
    have hd_simp :
        Complex.I * ((0 * Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) -
          (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) *
            ((Real.pi : ℂ) * Complex.I))) /
          Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) ^ 2 -
          (0 * ((τ : ℂ) * Complex.I) - 1 * Complex.I) / ((τ : ℂ) * Complex.I) ^ 2) =
        (Real.pi : ℂ) ^ 2 * Complex.cos ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) /
          Complex.sin ((Real.pi : ℂ) * ((τ : ℂ) * Complex.I)) ^ 2 -
          1 / ((τ : ℂ) * Complex.I) ^ 2 := by
      ring_nf; simp [Complex.I_sq]; ring
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
      rw [norm_div, norm_mul, norm_pow, norm_pow, hcos_eq, hsin_eq, norm_mul,
        Complex.norm_real, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (Real.cosh_pos _),
        abs_of_pos (by linarith)]
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
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have h0 := hCg ((τ : ℂ) * Complex.I) (by simp) (by simp [abs_of_pos hτpos, hτ])
    simpa [ejW, abs_of_pos hτpos] using
      h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro τ hτ _
    have hd1 := (stripG_imag_deriv_far_bounds hτ).1
    have hM1 : Real.pi + 2 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hw1 : 1 ≤ ejW 0 1 0 1 τ := by
      simp only [ejW, zero_sub, zero_mul, neg_zero, Real.exp_zero, mul_one, abs_of_pos hτpos,
        Real.rpow_neg hτpos.le, Real.rpow_one]
      rw [inv_mul_eq_div, le_div_iff₀ hτpos]
      nlinarith
    have h1 := hd1.trans hM1
    simpa using h1.trans (le_mul_of_one_le_right hM0 hw1)
  · intro τ hτ _
    have hd2 := (stripG_imag_deriv_far_bounds hτ).2
    have hM2 : 2 * Real.pi ^ 2 + 4 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hw2 : 1 ≤ ejW 0 1 0 2 τ := by
      simp only [ejW, zero_sub, zero_mul, neg_zero, Real.exp_zero, mul_one, abs_of_pos hτpos]
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτpos.le,
        Real.rpow_natCast, inv_mul_eq_div, le_div_iff₀ (pow_pos hτpos 2)]
      nlinarith [sq_nonneg τ]
    have h2 := hd2.trans hM2
    simpa using h2.trans (le_mul_of_one_le_right hM0 hw2)

/-! ### Part 2: `phiKill` and `fctWarpA` `EJOn` on `τ ≥ 1/2` -/

private lemma clm_deriv_one {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (L : ℂ →L[ℝ] ℝ) (t : ℝ) :
    L (deriv f t) = deriv (fun s : ℝ => L (f s)) t :=
  (L.hasFDerivAt.comp_hasDerivAt t (hf.differentiable (by norm_num) t).hasDerivAt).deriv.symm

private lemma clm_deriv_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (L : ℂ →L[ℝ] ℝ) (t : ℝ) :
    L (deriv (deriv f) t) = iteratedDeriv 2 (fun s : ℝ => L (f s)) t := by
  have hd : Differentiable ℝ (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.differentiable le_rfl
  have hfn : (fun s : ℝ => L (deriv f s)) = deriv (fun s : ℝ => L (f s)) :=
    funext (clm_deriv_one hf L)
  have h1 := (L.hasFDerivAt.comp_hasDerivAt t (hd t).hasDerivAt).deriv.symm
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
      calc ‖f τ‖ ≤ C 0 * min 1 ((τ / a) ^ 8) + C 0 * min 1 ((τ / a) ^ 8) := by linarith
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
      simp only [ejW, zero_sub, Nat.cast_one, zero_add, zero_mul, neg_zero, Real.exp_zero, mul_one,
        abs_of_pos hτpos, Real.rpow_neg hτpos.le, Real.rpow_one, pow_one]
      exact le_mul_of_one_le_right (inv_nonneg.mpr hτpos.le) (by linarith)
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
      simp only [ejW, zero_sub, Nat.cast_ofNat, zero_add, zero_mul, neg_zero, Real.exp_zero,
        mul_one, abs_of_pos hτpos]
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτpos.le, Real.rpow_natCast]
      exact le_mul_of_one_le_right (inv_nonneg.mpr (pow_nonneg hτpos.le 2))
        (one_le_pow₀ (by linarith))
    calc ‖deriv (deriv f) τ‖ ≤ (2 * C 2) * (τ ^ 2)⁻¹ := by linarith
      _ ≤ M * (τ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hC2M (inv_nonneg.mpr (pow_nonneg hτpos.le 2))
      _ ≤ M * ejW 0 0 0 2 τ := mul_le_mul_of_nonneg_left hej hM0

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
    exact hp.cast (by norm_num) (by norm_num)
  have hM0 : 0 ≤ 4 * (4 * Mze * 9) * 9 := hprod.hM
  refine ⟨8 * (4 * (4 * Mze * 9) * 9), by positivity, by positivity, hprod.c2, ?_, ?_, ?_⟩
  · intro τ hτ hτ0
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hpow : |τ| ^ (-(5 / 2 : ℝ) - 0) ≤ 8 * |τ| ^ (0 - (0 : ℕ) : ℝ) := by
      simp only [abs_of_pos hτpos, sub_zero, Real.rpow_zero, mul_one]
      have h1 : τ ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hτ (by norm_num)
      have h2 : (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      have h3 : (1 / 2 : ℝ) ^ (-3 : ℝ) = 8 := by norm_num
      linarith
    have hw : ejW (-(5 / 2)) 10 1 0 τ ≤ 8 * ejW 0 10 1 0 τ := by
      unfold ejW
      calc |τ| ^ (-(5 / 2 : ℝ) - 0) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(Real.pi * 1 * |τ|))
          ≤ (8 * |τ| ^ (0 - (0 : ℕ) : ℝ)) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(Real.pi * 1 * |τ|)) := by
            gcongr
        _ = 8 * ejW 0 10 1 0 τ := by unfold ejW; ring
    exact (hprod.b0 τ hτ0).trans ((mul_le_mul_of_nonneg_left hw hM0).trans_eq (by ring))
  · intro τ hτ hτ0
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hpow : |τ| ^ (-(5 / 2 : ℝ) - (1 : ℕ)) ≤ 8 * |τ| ^ (0 - (1 : ℕ) : ℝ) := by
      simp only [abs_of_pos hτpos, Nat.cast_one]
      rw [show -(5 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) + (-1 : ℝ) by ring, Real.rpow_add hτpos,
        show (0 : ℝ) - 1 = -1 by ring]
      have h1 : τ ^ (-(5 / 2 : ℝ)) ≤ 8 := by
        have ha : τ ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hτ (by norm_num)
        have hb : (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
        have hc : (1 / 2 : ℝ) ^ (-3 : ℝ) = 8 := by norm_num
        linarith
      calc τ ^ (-(5 / 2 : ℝ)) * τ ^ (-1 : ℝ) ≤ 8 * τ ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hτpos.le _)
    have hw : ejW (-(5 / 2)) 10 1 1 τ ≤ 8 * ejW 0 10 1 1 τ := by
      unfold ejW
      calc |τ| ^ (-(5 / 2 : ℝ) - (1 : ℕ)) * (1 + |τ|) ^ (10 + 1) * Real.exp (-(Real.pi * 1 * |τ|))
          ≤ (8 * |τ| ^ (0 - (1 : ℕ) : ℝ)) * (1 + |τ|) ^ (10 + 1) * Real.exp (-(Real.pi * 1 * |τ|)) := by
            gcongr
        _ = 8 * ejW 0 10 1 1 τ := by unfold ejW; ring
    exact (hprod.b1 τ hτ0).trans ((mul_le_mul_of_nonneg_left hw hM0).trans_eq (by ring))
  · intro τ hτ hτ0
    have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hpow : |τ| ^ (-(5 / 2 : ℝ) - (2 : ℕ)) ≤ 8 * |τ| ^ (0 - (2 : ℕ) : ℝ) := by
      simp only [abs_of_pos hτpos, Nat.cast_ofNat]
      rw [show -(5 / 2 : ℝ) - 2 = -(5 / 2 : ℝ) + (-2 : ℝ) by ring, Real.rpow_add hτpos,
        show (0 : ℝ) - 2 = -2 by ring]
      have h1 : τ ^ (-(5 / 2 : ℝ)) ≤ 8 := by
        have ha : τ ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hτ (by norm_num)
        have hb : (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
        have hc : (1 / 2 : ℝ) ^ (-3 : ℝ) = 8 := by norm_num
        linarith
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hτpos.le _)
    have hw : ejW (-(5 / 2)) 10 1 2 τ ≤ 8 * ejW 0 10 1 2 τ := by
      unfold ejW
      calc |τ| ^ (-(5 / 2 : ℝ) - (2 : ℕ)) * (1 + |τ|) ^ (10 + 2) * Real.exp (-(Real.pi * 1 * |τ|))
          ≤ (8 * |τ| ^ (0 - (2 : ℕ) : ℝ)) * (1 + |τ|) ^ (10 + 2) * Real.exp (-(Real.pi * 1 * |τ|)) := by
            gcongr
        _ = 8 * ejW 0 10 1 2 τ := by unfold ejW; ring
    exact (hprod.b2 τ hτ0).trans ((mul_le_mul_of_nonneg_left hw hM0).trans_eq (by ring))

private lemma fctWarpA_far_EJOn {K4 ε c L1 α P : ℝ} (hc : 0 < c) (hP : 0 ≤ P)
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
      have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
      have hnh : {t : ℝ | t ≠ 0} ∈ 𝓝 τ := isOpen_ne.mem_nhds hτ0
      have hd1 : DifferentiableAt ℝ f1 τ :=
        ((hMg.c2.differentiableOn (by norm_num)).differentiableAt hnh)
      have hd2 : DifferentiableAt ℝ f2 τ :=
        ((hf2.c2.differentiableOn (by norm_num)).differentiableAt hnh)
      rw [deriv_add hd1 hd2]
      have h0 := (norm_add_le _ _).trans (add_le_add (hMg.b1 τ hτ hτ0) (hf2.b1 τ hτ hτ0))
      have h1 : |L1| * Mpk * ejW 0 0 0 1 τ ≤ |L1| * Mpk * ejW 0 1 0 1 τ :=
        mul_le_mul_of_nonneg_left (hejw_le 1 hτ0) (by positivity)
      linarith
    · intro τ hτ hτ0
      have hnh : {t : ℝ | t ≠ 0} ∈ 𝓝 τ := isOpen_ne.mem_nhds hτ0
      have hcd1 : ContDiffOn ℝ 1 (deriv f1) {t : ℝ | t ≠ 0} :=
        (contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne |>.mp hMg.c2).2
      have hcd2 : ContDiffOn ℝ 1 (deriv f2) {t : ℝ | t ≠ 0} :=
        (contDiffOn_succ_iff_deriv_of_isOpen isOpen_ne |>.mp hf2.c2).2
      have hdd1 : DifferentiableAt ℝ (deriv f1) τ :=
        ((hcd1.differentiableOn (by norm_num)).differentiableAt hnh)
      have hdd2 : DifferentiableAt ℝ (deriv f2) τ :=
        ((hcd2.differentiableOn (by norm_num)).differentiableAt hnh)
      have hev : deriv (fun t => f1 t + f2 t) =ᶠ[𝓝 τ] fun t => deriv f1 t + deriv f2 t := by
        filter_upwards [hnh] with t ht
        have ht1 := ((hMg.c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds ht))
        have ht2 := ((hf2.c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds ht))
        exact deriv_add ht1 ht2
      rw [hev.deriv_eq, deriv_add hdd1 hdd2]
      have h0 := (norm_add_le _ _).trans (add_le_add (hMg.b2 τ hτ hτ0) (hf2.b2 τ hτ hτ0))
      have h1 : |L1| * Mpk * ejW 0 0 0 2 τ ≤ |L1| * Mpk * ejW 0 1 0 2 τ :=
        mul_le_mul_of_nonneg_left (hejw_le 2 hτ0) (by positivity)
      linarith
  have hD_ej : EJ (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) 0 0 0 P :=
    EJ.of_env2 hEnv hP 0 (fun _ => by simp)
  have hA := (hf12.mul hD_ej.to_on).mul hMhg
  refine ⟨4 * (4 * (Mg + |L1| * Mpk) * P) * Mhg, hA.hM, ?_⟩
  simpa [fctWarpA, f1, f2] using hA.cast (by norm_num) (by norm_num)

/-! ### Part 3: Horizontal FTC and zero-order `Ψ_c(iτ)` bound on `τ ≥ 1/2` -/

private lemma mellinK0_mul_fctPsi_eq {K4 ε c L1 α : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ζ.re < 1) :
    mellinK0 c ζ (fctXi1 L1) * fctPsi K4 ε c L1 α ζ =
      ζ * ∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ζ) := by
  unfold fctPsi fctWarpKA
  have hne := mellinK0_ne_zero c hζ (fctXi1 L1)
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

private lemma fctPsi_horiz_ftc {K4 ε c L1 α : ℝ} (hc : 0 < c)
    (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    {τ : ℝ} (hτ : 0 < τ) :
    mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
        fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) -
      mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
        fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      ∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I) := by
  set f : ℂ → ℂ := fctWarpKA K4 ε c L1 α
  have hf_hol : DifferentiableOn ℂ f strip := fctWarpKA_differentiableOn hc hDh
  have hf_deriv_cont : ContinuousOn (deriv f) strip :=
    (hf_hol.contDiffOn isOpen_strip).continuousOn_deriv_of_isOpen isOpen_strip (by norm_num)
  let Φ : ℝ → ℝ → ℂ := fun r s =>
    f ((s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)) +
      (s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I) *
        deriv f ((s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))
  have hmem_strip : ∀ {r s : ℝ}, 0 < r → r < 1 → 0 < s → s ≤ 1 →
      (s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I) ∈ strip := fun hr0 hr1 hs0 hs1 => by
    simp only [strip, mem_setOf_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.I_im,
      mul_one, zero_add, zero_mul]
    exact ⟨mul_pos hs0 hr0, by nlinarith⟩
  have hbox : ∀ {ε₀ δ : ℝ}, 0 < ε₀ → ε₀ < 3 / 8 → 0 < δ → δ < 1 →
      ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I) -
        ∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)) =
      ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          ∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
        ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
          ∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)) := by
    intro ε₀ δ hε0 hε38 hδ0 hδ1
    have hcont_Φ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc ε₀ (3 / 8) ×ˢ Icc δ 1) := by
      have harg : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) * ((p.1 : ℂ) + (τ : ℂ) * Complex.I)) := by
        fun_prop
      have hmap : MapsTo (fun p : ℝ × ℝ => (p.2 : ℂ) * ((p.1 : ℂ) + (τ : ℂ) * Complex.I))
          (Icc ε₀ (3 / 8) ×ˢ Icc δ 1) strip := fun p hp =>
        hmem_strip (hε0.trans_le hp.1.1) (hp.1.2.trans_lt (by norm_num))
          (hδ0.trans_le hp.2.1) hp.2.2
      exact (hf_hol.continuousOn.comp harg.continuousOn hmap).add
        (harg.continuousOn.mul (hf_deriv_cont.comp harg.continuousOn hmap))
    have hInt_prod : Integrable (fun p : ℝ × ℝ => Φ p.1 p.2)
        ((volume.restrict (Ioc ε₀ (3 / 8))).prod (volume.restrict (Ioc δ 1))) := by
      have hIcc : IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc ε₀ (3 / 8) ×ˢ Icc δ 1) :=
        hcont_Φ.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hIoc := hIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      rwa [IntegrableOn, ← Measure.volume_eq_prod, ← Measure.prod_restrict] at hIoc
    have hswap : ∫ r in ε₀..(3 / 8 : ℝ), (∫ s in δ..1, Φ r s) =
        ∫ s in δ..1, (∫ r in ε₀..(3 / 8 : ℝ), Φ r s) := by
      simp only [intervalIntegral.integral_of_le hε38.le, intervalIntegral.integral_of_le hδ1.le]
      exact integral_integral_swap hInt_prod
    have hLHS_inner : ∀ r ∈ Icc ε₀ (3 / 8),
        ∫ s in δ..1, Φ r s = f ((r : ℂ) + (τ : ℂ) * Complex.I) -
          (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)) := by
      intro r hr
      have hint_s : IntervalIntegrable (Φ r) volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        exact hcont_Φ.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨hr, hs⟩
      have hderiv_s : ∀ s ∈ uIcc δ 1,
          HasDerivAt (fun t : ℝ => (t : ℂ) * f ((t : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
            (Φ r s) s := by
        intro s hs
        rw [uIcc_of_le hδ1.le] at hs
        have hms := hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt (by norm_num))
          (hδ0.trans_le hs.1) hs.2
        have hdf := (hf_hol.differentiableAt (isOpen_strip.mem_nhds hms)).hasDerivAt
        have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))
            ((r : ℂ) + (τ : ℂ) * Complex.I) s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ((r : ℂ) + (τ : ℂ) * Complex.I)
        have hcomp := (Complex.ofRealCLM.hasDerivAt (x := s)).mul (hdf.comp s harg)
        refine hcomp.congr_deriv ?_
        simp [Φ]; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_s hint_s]
      simp
    have hRHS_inner : ∀ s ∈ Icc δ 1,
        ∫ r in ε₀..(3 / 8 : ℝ), Φ r s =
          ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
              f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
            ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
              f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)) := by
      intro s hs
      have hint_r : IntervalIntegrable (fun r => Φ r s) volume ε₀ (3 / 8) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hε38.le]
        exact hcont_Φ.comp (continuousOn_id.prodMk continuousOn_const) fun r hr => ⟨hr, hs⟩
      have hderiv_r : ∀ r ∈ uIcc ε₀ (3 / 8),
          HasDerivAt (fun x : ℝ => ((x : ℂ) + (τ : ℂ) * Complex.I) *
              f ((s : ℂ) * ((x : ℂ) + (τ : ℂ) * Complex.I)))
            (Φ r s) r := by
        intro r hr
        rw [uIcc_of_le hε38.le] at hr
        have hms := hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt (by norm_num))
          (hδ0.trans_le hs.1) hs.2
        have hdf := (hf_hol.differentiableAt (isOpen_strip.mem_nhds hms)).hasDerivAt
        have hz_d : HasDerivAt (fun x : ℝ => (x : ℂ) + (τ : ℂ) * Complex.I) 1 r := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).add_const ((τ : ℂ) * Complex.I)
        have harg : HasDerivAt (fun x : ℝ => (s : ℂ) * ((x : ℂ) + (τ : ℂ) * Complex.I))
            (s : ℂ) r := by
          simpa using hz_d.const_mul (s : ℂ)
        have hcomp := hz_d.mul (hdf.comp r harg)
        refine hcomp.congr_deriv ?_
        simp [Φ]; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_r hint_r]
      norm_num
    have hL : ∫ r in ε₀..(3 / 8 : ℝ), (∫ s in δ..1, Φ r s) =
        ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I) -
          ∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)) := by
      have hc1 : IntervalIntegrable (fun r : ℝ => f ((r : ℂ) + (τ : ℂ) * Complex.I)) volume ε₀ (3 / 8) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hε38.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun r hr => ?_
        simp only [strip, mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
        exact ⟨hε0.trans_le hr.1, hr.2.trans_lt (by norm_num)⟩
      have hc2 : IntervalIntegrable (fun r : ℝ => (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
          volume ε₀ (3 / 8) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hε38.le]
        refine continuousOn_const.mul (hf_hol.continuousOn.comp (by fun_prop) fun r hr => ?_)
        exact hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt (by norm_num)) hδ0 hδ1.le
      rw [intervalIntegral.integral_congr (fun r hr => hLHS_inner r (by rwa [uIcc_of_le hε38.le] at hr))]
      exact intervalIntegral.integral_sub hc1 hc2
    have hR : ∫ s in δ..1, (∫ r in ε₀..(3 / 8 : ℝ), Φ r s) =
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)) := by
      have hc1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)))
          volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun s hs => ?_
        exact hmem_strip (by norm_num) (by norm_num) (hδ0.trans_le hs.1) hs.2
      have hc2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
          volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun s hs => ?_
        exact hmem_strip hε0 (hε38.trans (by norm_num)) (hδ0.trans_le hs.1) hs.2
      rw [intervalIntegral.integral_congr (fun s hs => hRHS_inner s (by rwa [uIcc_of_le hδ1.le] at hs))]
      rw [intervalIntegral.integral_sub (hc1.const_mul _) (hc2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hL, hswap, hR]
  -- Pass `δ → 0+` for fixed `ε₀ ∈ (0, 3/8)`
  have heps_eq : ∀ {ε₀ : ℝ}, 0 < ε₀ → ε₀ < 3 / 8 →
      ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I) =
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)) := by
    intro ε₀ hε0 hε38
    obtain ⟨r₀, M₀, hr₀, hM₀, hnear⟩ := fctWarpKA_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDb
    have hRHS_lim : Tendsto (fun δ : ℝ =>
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))) := by
      have hi1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)))
          volume 0 1 := by
        refine fctWarpKA_segment_integrable hc hDc hDb ?_ ?_ ?_
        · norm_num
        · norm_num
        · intro h0; have := congr_arg Complex.im h0; simp at this; linarith
      have hi2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
          volume 0 1 := by
        refine fctWarpKA_segment_integrable hc hDc hDb ?_ ?_ ?_
        · simpa using hε0.le
        · simp; linarith
        · intro h0; have := congr_arg Complex.im h0; simp at this; linarith
      have hc1 := (intervalIntegral.continuousOn_primitive_interval' hi1 (by simp)).continuousWithinAt
      have hc2 := (intervalIntegral.continuousOn_primitive_interval' hi2 (by simp)).continuousWithinAt
      have hnh : (Icc (0 : ℝ) 1) ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds ?_ |>.mono fun _ h => ?_
      · exact (tendsto_const_nhds.mul (hc1.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))).sub
          (tendsto_const_nhds.mul (hc2.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)))
      · exact Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
      · exact Ioo_subset_Icc_self
    have htail_lim : Tendsto (fun δ : ℝ =>
        ∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro e he
      set δ_cap : ℝ := min (1 / 2) (r₀ / (1 + τ))
      have hδ_cap : 0 < δ_cap := lt_min (by norm_num) (div_pos hr₀ (by positivity))
      set K_e : ℝ := (3 / 8) * M₀ * τ ^ (-(1 / 2 : ℝ))
      have hKe : 0 ≤ K_e := by positivity
      set δ₀ : ℝ := min δ_cap (e / (K_e + 1)) ^ 2
      have hδ0 : 0 < δ₀ := pow_pos (lt_min hδ_cap (div_pos he (by positivity))) 2
      refine ⟨min δ_cap ((e / (K_e + 1)) ^ 2), lt_min hδ_cap (pow_pos (div_pos he (by positivity)) 2),
        fun δ hδ hdist => ?_⟩
      have hδpos : 0 < δ := hδ
      rw [Real.dist_eq, sub_zero, abs_of_pos hδpos] at hdist
      have hδ_lt_cap : δ < δ_cap := hdist.trans_le (min_le_left _ _)
      have hδ1 : δ < 1 := hδ_lt_cap.trans_le ((min_le_left _ _).trans (by norm_num))
      have hδr0 : δ * (1 + τ) ≤ r₀ := by
        have hlt : δ ≤ r₀ / (1 + τ) := hδ_lt_cap.le.trans (min_le_right _ _)
        rwa [le_div_iff₀ (by positivity)] at hlt
      have hbd_int : ∀ r ∈ uIoc ε₀ (3 / 8),
          ‖(δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
            M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) := by
        intro r hr
        rw [uIoc_of_le hε38.le] at hr
        set t : ℂ := (δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)
        have ht_re0 : 0 ≤ t.re := by simp [t]; exact mul_nonneg hδpos.le (by linarith [hr.1])
        have ht_re1 : t.re < 1 := by simp [t]; nlinarith [hr.2]
        have ht_ne : t ≠ 0 := by
          intro h0; have := congr_arg Complex.im h0
          simp [t] at this; exact absurd this (mul_ne_zero hδpos.ne' hτ.ne')
        have hnr : ‖(r : ℂ) + (τ : ℂ) * Complex.I‖ ≤ 1 + τ := by
          have := Complex.norm_le_abs_re_add_abs_im ((r : ℂ) + (τ : ℂ) * Complex.I)
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
            zero_add, abs_of_pos (hε0.trans_le hr.1), abs_of_pos hτ] at this
          linarith [hr.2]
        have hnt_hi : ‖t‖ ≤ r₀ := by
          calc ‖t‖ = δ * ‖(r : ℂ) + (τ : ℂ) * Complex.I‖ := by
                simp [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
            _ ≤ δ * (1 + τ) := mul_le_mul_of_nonneg_left hnr hδpos.le
            _ ≤ r₀ := hδr0
        have hnt_lo : δ * τ ≤ ‖t‖ := by
          have := Complex.abs_im_le_norm t
          simpa [t, abs_of_pos hδpos, abs_of_pos hτ] using this
        have hpow : ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ (δ * τ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hδpos hτ) hnt_lo (by norm_num)
        have hft := hnear t ht_re0 ht_re1 ht_ne hnt_hi
        calc ‖(δ : ℂ) * f t‖ = δ * ‖f t‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
          _ ≤ δ * (M₀ * ‖t‖ ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hft hδpos.le
          _ ≤ δ * (M₀ * (δ * τ) ^ (-(1 / 2 : ℝ))) := by gcongr
          _ = M₀ * τ ^ (-(1 / 2 : ℝ)) * (δ ^ (1 : ℝ) * δ ^ (-(1 / 2 : ℝ))) := by
              rw [Real.mul_rpow hδpos.le hτ.le, Real.rpow_one]; ring
          _ = M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_add hδpos, show (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 by ring]
      have hint_norm := intervalIntegral.norm_integral_le_of_norm_le_const hbd_int
      have hlen : |((3 / 8 : ℝ) - ε₀)| ≤ 3 / 8 := by rw [abs_of_nonneg (by linarith)]; linarith
      have hsqrt : δ ^ (1 / 2 : ℝ) < e / (K_e + 1) := by
        have h1 : δ < (e / (K_e + 1)) ^ 2 := hdist.trans_le (min_le_right _ _)
        rw [← Real.sqrt_eq_rpow]
        exact (Real.sqrt_lt' (div_pos he (by positivity))).mpr h1
      rw [dist_zero_right]
      calc ‖∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))‖
          ≤ M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) * |3 / 8 - ε₀| := hint_norm
        _ ≤ K_e * δ ^ (1 / 2 : ℝ) := by
            have := mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ))
            linarith [show M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) * (3 / 8) = K_e * δ ^ (1 / 2 : ℝ) from by ring]
        _ ≤ (K_e + 1) * δ ^ (1 / 2 : ℝ) := by gcongr; linarith
        _ < (K_e + 1) * (e / (K_e + 1)) := mul_lt_mul_of_pos_left hsqrt (by positivity)
        _ = e := by field_simp
    have hLHS_lim : Tendsto (fun δ : ℝ =>
        ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I) -
          ∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
      simpa using tendsto_const_nhds.sub htail_lim
    have hev_eq : (fun δ : ℝ =>
        ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I) -
          ∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun δ : ℝ =>
          ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
              ∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
            ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
              ∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      exact hbox hε0 hε38 hδ.1 hδ.2
    exact tendsto_nhds_unique hLHS_lim (hRHS_lim.congr' hev_eq.symm)
  -- Pass `ε₀ → 0+`
  have hi_r : IntervalIntegrable (fun r : ℝ => f ((r : ℂ) + (τ : ℂ) * Complex.I)) volume 0 (3 / 8) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine (fctWarpKA_continuousOn hc hDc).comp (by fun_prop) fun r hr => ?_
    exact strip_half_mem hr.1 hr.2 hτ
  have hLHS_lim0 : Tendsto (fun ε₀ : ℝ => ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in (0 : ℝ)..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
    have hc0 := (intervalIntegral.continuousOn_primitive_interval' hi_r (by simp)).continuousWithinAt
    exact hc0.mono_left (nhdsWithin_le_nhdsWithin (by filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 8)] with x hx; exact Ioo_subset_Icc_self hx))
  have hPsi_cont : ContinuousOn (fun ε₀ : ℝ => ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
      ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) (Icc (0 : ℝ) (3 / 8)) := by
    have hcont_g := fctPsi_integral_continuousOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb
    have hmap : MapsTo (fun ε₀ : ℝ => (ε₀ : ℂ) + (τ : ℂ) * Complex.I) (Icc (0 : ℝ) (3 / 8)) psiDom :=
      fun ε₀ hε₀ => strip_half_mem hε₀.1 hε₀.2 hτ
    exact (by fun_prop : ContinuousOn (fun ε₀ : ℝ => (ε₀ : ℂ) + (τ : ℂ) * Complex.I) (Icc 0 (3 / 8))).mul
      (hcont_g.comp (by fun_prop) hmap)
  have hRHS_lim0 : Tendsto (fun ε₀ : ℝ =>
      ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
        ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
          ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
        ((τ : ℂ) * Complex.I) *
          ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I)))) := by
    have hc1 := hPsi_cont.continuousWithinAt (by simp)
    have hlim2 : Tendsto (fun ε₀ : ℝ => ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
        ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (((τ : ℂ) * Complex.I) *
          ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I)))) := by
      simpa using hc1.mono_left (nhdsWithin_le_nhdsWithin
        (by filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 8)] with x hx; exact Ioo_subset_Icc_self hx))
    exact tendsto_const_nhds.sub hlim2
  have hev0 : (fun ε₀ : ℝ => ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε₀ : ℝ =>
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 8)] with ε₀ hε₀
    exact heps_eq hε₀.1 hε₀.2
  have hfin := tendsto_nhds_unique hLHS_lim0 (hRHS_lim0.congr' hev0.symm)
  rw [mellinK0_mul_fctPsi_eq hc (by simp : ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).re < 1),
    mellinK0_mul_fctPsi_eq hc (by simp : ((τ : ℂ) * Complex.I).re < 1)]
  exact hfin.symm

private lemma mellinK0_imag_inv_le {c ξ τ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hτ : 0 ≤ τ) :
    ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖⁻¹ ≤ Real.exp (1 / (6 * c)) * (1 + τ) := by
  have hmag := (norm_mellinK0_imag_le hc hξ τ).1
  have hbin : ‖FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)‖ ≤ 1 / (6 * c) := by
    have hb := FormalResearch.Asymptotics.binetDiff_norm_le hc (by simp : ((τ : ℂ) * Complex.I).re < 1)
    simpa using hb.trans_eq (by ring)
  have hre : -(1 / (6 * c)) ≤ (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re := by
    linarith [neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hbin)]
  have hexp : Real.exp (-(1 / (6 * c))) ≤
      Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re :=
    Real.exp_le_exp.mpr hre
  have hpow : (1 + τ)⁻¹ ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
    have h4 : 1 + τ ^ 2 ≤ (1 + τ) ^ 4 := by
      have h0 := pow_nonneg hτ 3
      nlinarith [sq_nonneg τ]
    have hp1 : ((1 + τ) ^ 4) ^ (-(1 / 4 : ℝ)) ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h4 (by norm_num)
    have hpi : ((1 + τ) ^ 4) ^ (-(1 / 4 : ℝ)) = (1 + τ)⁻¹ := by
      rw [← Real.rpow_natCast (1 + τ) 4, ← Real.rpow_mul (by positivity)]
      norm_num
      exact Real.rpow_neg_one (1 + τ)
    linarith
  have hlo : (1 + τ)⁻¹ * Real.exp (-(1 / (6 * c))) ≤ ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ := by
    rw [hmag]; exact mul_le_mul hpow hexp (by positivity) (by positivity)
  have hinv := inv_anti₀ (by positivity) hlo
  rwa [mul_inv, inv_inv, ← Real.exp_neg, neg_neg, mul_comm] at hinv

private lemma fctPsi_far_zero_pos {K4 ε c L1 α B Cdesc : ℝ} (hc : 0 < c)
    (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hCD : ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Cdesc * c⁻¹ / Real.log (2 + τ)) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ ≤ M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDb 0 ⟨le_rfl, zero_le_one⟩)
  have hC0 : 0 ≤ Cdesc := by
    have hlogpos : 0 < Real.log (2 + (1 / 2 : ℝ)) := Real.log_pos (by norm_num)
    have hnn := (norm_nonneg _).trans (hCD (1 / 2) le_rfl)
    have : 0 ≤ Cdesc * c⁻¹ := (div_nonneg_iff.mp hnn).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hlogpos))
    exact nonneg_of_mul_nonneg_left this (by positivity)
  obtain ⟨Kk, hKk0, hKk⟩ := norm_mellinK0_half_strip_decay hc (fctXi1_pos L1)
  obtain ⟨Khg, hKhg0, hKhg⟩ := ctHG_far ε
  obtain ⟨Cg, hCg0, hCg⟩ := stripG_far_bound
  obtain ⟨Cpk, hCpk0, hCpk⟩ := (FctPhiKill.fct_phikill).2.2.2.2.2.1
  set a : ℝ := c ^ (-(1 / 12 : ℝ))
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  set M_right : ℝ := Kk * ((Cdesc * c⁻¹ / Real.log 2 + 1) * (B * Khg) * c⁻¹)
  set M_int : ℝ := Kk * (Cg + |L1| * Cpk) * B * Khg
  set M0 : ℝ := Real.exp (1 / (6 * c)) * (M_right + M_int)
  refine ⟨M0, by positivity, fun τ hτ => ?_⟩
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have hftc := fctPsi_horiz_ftc hc hDh hDc ⟨B, hDb⟩ hτpos
  have hmul : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
      fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
        fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) -
      ∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I) := by
    linear_combination -hftc
  -- Bound right term at `3/8 + iτ`
  have hK_38 : ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1)‖ ≤ Kk := by
    have h1 := hKk (3 / 8) τ (by norm_num) (by norm_num)
    have hp : (1 + |τ|) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by norm_num)
    exact h1.trans (mul_le_of_le_one_right hKk0 hp)
  have hmem_38 : (3 / 8 : ℂ) + (τ : ℂ) * Complex.I ∈ closedStrip := by
    simp [closedStrip]; norm_num
  have hPsi_38_eq : fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) =
      (fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) + 1) *
        (fctDcompAt K4 c α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          ctHG ε ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) * (c : ℂ)⁻¹ := by
    have hHG_ne := ctHG_ne_zero_of_band ε (by simp : 0 < ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).re)
      (by simp : ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).re < 1 / 2)
    have hD_ne := fctDcompAt_ne_zero (K4 := K4) (c := c) (α := α) ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    unfold fctFint fctPhiC
    field_simp [hc_ne, hD_ne, hHG_ne]
    ring
  have hFint_bd : ‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) + 1‖ ≤
      Cdesc * c⁻¹ / Real.log 2 + 1 := by
    have h1 := hCD τ hτ
    have hlog : Real.log 2 ≤ Real.log (2 + τ) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : Cdesc * c⁻¹ / Real.log (2 + τ) ≤ Cdesc * c⁻¹ / Real.log 2 :=
      div_le_div_of_nonneg_left (by positivity) (Real.log_pos (by norm_num)) hlog
    exact (norm_add_le _ _).trans (by simpa using add_le_add_right (h1.trans h2) 1)
  have hD_38 : ‖fctDcompAt K4 c α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ B := hDb _ hmem_38
  have hHG_38 : ‖ctHG ε ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))) := by
    simpa [abs_of_pos hτpos] using hKhg _ hmem_38 (by simp [abs_of_pos hτpos, hτ])
  have hbd_right :
      ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
          fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        M_right * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    rw [hPsi_38_eq, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    have h67 : (1 + τ) ^ 6 ≤ (1 + τ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
          (‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) + 1‖ *
            (‖fctDcompAt K4 c α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ *
              ‖ctHG ε ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖) * c⁻¹)
        ≤ Kk * ((Cdesc * c⁻¹ / Real.log 2 + 1) * (B * (Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))))) * c⁻¹) := by
          gcongr
      _ = M_right * (1 + τ) ^ 6 * Real.exp (-(Real.pi * τ)) := by simp only [M_right]; ring
      _ ≤ M_right * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by gcongr
  -- Bound horizontal integral over `0..3/8`
  have hint_pt : ∀ r ∈ uIoc (0 : ℝ) (3 / 8),
      ‖fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        M_int * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    intro r hr
    rw [uIoc_of_le (by norm_num)] at hr
    set t : ℂ := (r : ℂ) + (τ : ℂ) * Complex.I
    have ht_mem : t ∈ closedStrip := ⟨by simp; linarith [hr.1], by simp; linarith [hr.2]⟩
    have ht_K0 : ‖mellinK0 c t (fctXi1 L1)‖ ≤ Kk := by
      have h1 := hKk r τ hr.1.le (hr.2.trans (by norm_num))
      have hp : (1 + |τ|) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by norm_num)
      exact h1.trans (mul_le_of_le_one_right hKk0 hp)
    have ht_g : ‖stripG t‖ ≤ Cg * (1 + τ) := by
      simpa [t, abs_of_pos hτpos] using hCg t (by simp [abs_le]; constructor <;> linarith [hr.1, hr.2])
        (by simp [abs_of_pos hτpos, hτ])
    have ht_pk : ‖FctPhiKill.phiKill a t‖ ≤ Cpk := by
      have h1 := hCpk (a := a) (z := t) ha (by simp [t]; linarith [hr.1])
      exact h1.trans (mul_le_of_le_one_right hCpk0 (min_le_right _ _))
    have ht_fac : ‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill a t‖ ≤ (Cg + |L1| * Cpk) * (1 + τ) := by
      calc ‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill a t‖
          ≤ ‖stripG t‖ + |L1| * ‖FctPhiKill.phiKill a t‖ := by
            simpa [Complex.norm_real, Real.norm_eq_abs] using norm_add_le (stripG t) ((L1 : ℂ) * FctPhiKill.phiKill a t)
        _ ≤ Cg * (1 + τ) + |L1| * (Cpk * (1 + τ)) := by
            gcongr
            exact le_mul_of_one_le_right hCpk0 (by linarith)
        _ = (Cg + |L1| * Cpk) * (1 + τ) := by ring
    have ht_D : ‖fctDcompAt K4 c α t‖ ≤ B := hDb t ht_mem
    have ht_HG : ‖ctHG ε t‖ ≤ Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))) := by
      simpa [t, abs_of_pos hτpos] using hKhg t ht_mem (by simp [t, abs_of_pos hτpos, hτ])
    unfold fctWarpKA fctWarpA
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖mellinK0 c t (fctXi1 L1)‖ * (‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill a t‖ *
          ‖fctDcompAt K4 c α t‖ * ‖ctHG ε t‖)
        ≤ Kk * ((Cg + |L1| * Cpk) * (1 + τ) * B * (Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))))) := by
          gcongr
      _ = M_int * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by simp only [M_int]; ring
  have hbd_int :
      ‖∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        M_int * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hint_pt
    have h2 : |(3 / 8 : ℝ) - 0| ≤ 1 := by norm_num
    exact h1.trans (mul_le_of_le_one_right (by positivity) h2)
  have hK0_ne := mellinK0_ne_zero c (by simp : ((τ : ℂ) * Complex.I).re < 1) (fctXi1 L1)
  have hpsi_eq : fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹ *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) := by
    rw [← mul_assoc, inv_mul_cancel₀ hK0_ne, one_mul]
  rw [hpsi_eq, norm_mul, norm_inv, hmul]
  have hKinv := mellinK0_imag_inv_le hc (fctXi1_pos L1) hτpos.le
  have hcomb :
      ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
          fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) -
        ∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        (M_right + M_int) * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    calc ‖_‖ ≤ ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
            fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ +
          ‖∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖⁻¹ * ‖_‖
      ≤ (Real.exp (1 / (6 * c)) * (1 + τ)) * ((M_right + M_int) * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ))) := by
        gcongr
    _ = M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) := by simp only [M0]; ring

/-! ### Part 4: Logarithmic derivative of `K₀` and derivatives `j = 1, 2` on `τ ≥ 1/2` -/

private noncomputable def fctRk (c L1 : ℝ) (τ : ℝ) : ℂ :=
  1 / (2 * (1 - (τ : ℂ) * Complex.I)) +
    deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I) +
    (c : ℂ) * (stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ))

private lemma mellinK0_log_deriv_imag {c L1 : ℝ} (hc : 0 < c) (τ : ℝ) :
    deriv (fun w : ℂ => mellinK0 c w (fctXi1 L1)) ((τ : ℂ) * Complex.I) /
        mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) = fctRk c L1 τ := by
  set w : ℂ := (τ : ℂ) * Complex.I
  have hw_re0 : w.re = 0 := by simp [w]
  have hw_abs : |w.re| < 1 := by simp [hw_re0]
  have hw_lt1 : w.re < 1 := by simp [hw_re0]
  have h1_re : 0 < (1 - w).re := by simp [hw_re0]
  have hsp : 1 - w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl h1_re)
  have h1w_ne : 1 - w ≠ 0 := Complex.slitPlane_ne_zero hsp
  have hpow : HasDerivAt (fun z : ℂ => (1 - z) ^ (-(1 / 2 : ℂ)))
      ((1 / (2 * (1 - w))) * (1 - w) ^ (-(1 / 2 : ℂ))) w := by
    have h1 := ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).cpow_const hsp (c := -(1 / 2 : ℂ))
    refine h1.congr_deriv ?_
    have hsub : (1 - w) ^ (-(1 / 2 : ℂ) - 1) = (1 - w) ^ (-(1 / 2 : ℂ)) * (1 - w)⁻¹ := by
      simpa [Complex.cpow_one] using Complex.cpow_sub (1 - w) (-(1 / 2 : ℂ)) h1w_ne
    rw [hsub]
    field_simp [h1w_ne]
    ring
  have hopen_b : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hbd_at : HasDerivAt (FormalResearch.Asymptotics.binetDiff c)
      (deriv (FormalResearch.Asymptotics.binetDiff c) w) w :=
    ((FormalResearch.Asymptotics.binetDiff_differentiableOn hc).differentiableAt
      (hopen_b.mem_nhds hw_lt1)).hasDerivAt
  have hbin := hbd_at.cexp
  have hphi := ((hasDerivAt_mellinPhi_fct L1 hw_abs).const_mul (c : ℂ)).cexp
  have hmul := (hpow.mul hbin).mul hphi
  have hm_eq : (fun z : ℂ => (1 - z) ^ (-(1 / 2 : ℂ)) *
      Complex.exp (FormalResearch.Asymptotics.binetDiff c z) *
      Complex.exp ((c : ℂ) * mellinPhi z (fctXi1 L1))) =
      fun z : ℂ => mellinK0 c z (fctXi1 L1) := funext fun z => (rfl)
  rw [hm_eq] at hmul
  rw [hmul.deriv]
  have hKne := mellinK0_ne_zero c hw_lt1 (fctXi1 L1)
  have h1ne : (1 - w) ^ (-(1 / 2 : ℂ)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h1w_ne)
  have h2ne : Complex.exp (FormalResearch.Asymptotics.binetDiff c w) ≠ 0 := Complex.exp_ne_zero _
  have h3ne : Complex.exp ((c : ℂ) * mellinPhi w (fctXi1 L1)) ≠ 0 := Complex.exp_ne_zero _
  unfold fctRk mellinK0 fctRayP
  field_simp [hKne, h1ne, h2ne, h3ne]
  ring

private lemma fctRk_far_bounds {c L1 : ℝ} (hc : 0 < c) :
    ∃ Mr : ℝ, 0 ≤ Mr ∧ ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctRk c L1 τ‖ ≤ Mr * (1 + τ) ∧
      ‖deriv (fctRk c L1) τ‖ ≤ Mr := by
  obtain ⟨Cg, hCg0, hCg⟩ := stripG_far_bound
  set Mr : ℝ := 1 / 2 + 1 / (6 * c) + c * (Cg + |L1| + Real.pi + 2) + 1
  have hMr0 : 0 ≤ Mr := by positivity
  refine ⟨Mr, hMr0, fun τ hτ => ?_⟩
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have h1τ_ge : 1 ≤ ‖(1 : ℂ) - (τ : ℂ) * Complex.I‖ := by
    have hre := Complex.abs_re_le_norm (1 - (τ : ℂ) * Complex.I)
    simpa using hre
  have ht1_norm : ‖(1 : ℂ) / (2 * (1 - (τ : ℂ) * Complex.I))‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ (by linarith)]
    linarith
  have ht2_norm : ‖deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤
      1 / (12 * c) := by
    have h := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc
      (by simp : ((τ : ℂ) * Complex.I).re ≤ 0) (r := 1) le_rfl
    simpa [iteratedDeriv_one] using h
  have hsg_norm : ‖stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ)‖ ≤ (Cg + |L1|) * (1 + τ) := by
    have hsg := hCg ((τ : ℂ) * Complex.I) (by simp) (by simp [abs_of_pos hτpos, hτ])
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, abs_of_pos hτpos] at hsg
    calc ‖stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ)‖
        ≤ ‖stripG ((τ : ℂ) * Complex.I)‖ + |L1| := by
          simpa [Complex.norm_real, Real.norm_eq_abs] using norm_add_le (stripG ((τ : ℂ) * Complex.I)) (L1 : ℂ)
      _ ≤ Cg * (1 + τ) + |L1| * (1 + τ) := by
          gcongr; exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)
      _ = (Cg + |L1|) * (1 + τ) := by ring
  have hRk0 : ‖fctRk c L1 τ‖ ≤ Mr * (1 + τ) := by
    unfold fctRk
    have hb1 : ‖1 / (2 * (1 - (τ : ℂ) * Complex.I)) +
        deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤
        (1 / 2 + 1 / (12 * c)) * (1 + τ) := by
      have hsum := (norm_add_le _ _).trans (add_le_add ht1_norm ht2_norm)
      exact hsum.trans (le_mul_of_one_le_right (by positivity) (by linarith))
    have hb2 : ‖(c : ℂ) * (stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ))‖ ≤
        (c * (Cg + |L1|)) * (1 + τ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      calc c * ‖stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ)‖
          ≤ c * ((Cg + |L1|) * (1 + τ)) := mul_le_mul_of_nonneg_left hsg_norm hc.le
        _ = (c * (Cg + |L1|)) * (1 + τ) := by ring
    calc ‖_‖ ≤ (1 / 2 + 1 / (12 * c)) * (1 + τ) + (c * (Cg + |L1|)) * (1 + τ) :=
          (norm_add_le _ _).trans (add_le_add hb1 hb2)
      _ ≤ Mr * (1 + τ) := by
          gcongr
          simp only [Mr]
          have : 0 ≤ c * (Real.pi + 2) := mul_nonneg hc.le (by linarith [Real.pi_pos])
          linarith [show (1 : ℝ) / (12 * c) ≤ 1 / (6 * c) by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith]
  -- Derivative of `fctRk c L1` at `τ`
  have hd1 : HasDerivAt (fun t : ℝ => 1 / (2 * (1 - (t : ℂ) * Complex.I)))
      (Complex.I / (2 * (1 - (τ : ℂ) * Complex.I) ^ 2)) τ := by
    have hden_ne : (2 : ℂ) * (1 - (τ : ℂ) * Complex.I) ≠ 0 := by
      intro h0; rw [mul_eq_zero] at h0
      rcases h0 with h | h
      · norm_num at h
      · have := congr_arg Complex.re h; simp at this
    have hlin : HasDerivAt (fun t : ℝ => (2 : ℂ) * (1 - (t : ℂ) * Complex.I)) (-2 * Complex.I) τ := by
      have h1 := ((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I)
      have h2 := ((hasDerivAt_const τ (1 : ℂ)).sub h1).const_mul (2 : ℂ)
      refine h2.congr_deriv ?_; simp; ring
    have hd := (hasDerivAt_const τ (1 : ℂ)).div hlin hden_ne
    refine hd.congr_deriv ?_
    field_simp [hden_ne]; ring
  have hd2 : HasDerivAt (fun t : ℝ => deriv (FormalResearch.Asymptotics.binetDiff c) ((t : ℂ) * Complex.I))
      (Complex.I * iteratedDeriv 2 (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)) τ := by
    have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have hcd := (FormalResearch.Asymptotics.binetDiff_differentiableOn hc).contDiffOn hopen (n := 2)
    have hcd1 : ContDiffOn ℂ 1 (deriv (FormalResearch.Asymptotics.binetDiff c)) {z : ℂ | z.re < 1} :=
      (contDiffOn_succ_iff_deriv_of_isOpen hopen).mp hcd |>.2
    have hdiff := (hcd1.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds (by simp : ((τ : ℂ) * Complex.I).re < 1))
    have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
    refine (hdiff.hasDerivAt.comp τ hl).congr_deriv ?_
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    ring
  have hd3 : HasDerivAt (fun t : ℝ => (c : ℂ) * (stripG ((t : ℂ) * Complex.I) + (L1 : ℂ)))
      ((c : ℂ) * deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ) τ := by
    have hsg := (stripG_imag_deriv_pos hτpos)
    rw [← hsg.deriv] at hsg
    exact (hsg.add_const (L1 : ℂ)).const_mul (c : ℂ)
  have hd_tot := (hd1.add hd2).add hd3
  have hd_eq : (fun t : ℝ => 1 / (2 * (1 - (t : ℂ) * Complex.I)) +
      deriv (FormalResearch.Asymptotics.binetDiff c) ((t : ℂ) * Complex.I) +
      (c : ℂ) * (stripG ((t : ℂ) * Complex.I) + (L1 : ℂ))) = fctRk c L1 := rfl
  rw [hd_eq] at hd_tot
  have hRk1 : ‖deriv (fctRk c L1) τ‖ ≤ Mr := by
    rw [hd_tot.deriv]
    have hb1 : ‖Complex.I / (2 * (1 - (τ : ℂ) * Complex.I) ^ 2)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_I, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by simp,
        div_le_iff₀ (by have := one_le_pow₀ h1τ_ge (n := 2); positivity)]
      have : 1 ≤ ‖1 - (τ : ℂ) * Complex.I‖ ^ 2 := one_le_pow₀ h1τ_ge
      linarith
    have hb2 : ‖Complex.I * iteratedDeriv 2 (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤
        1 / (6 * c) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have h := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc
        (by simp : ((τ : ℂ) * Complex.I).re ≤ 0) (r := 2) (by norm_num)
      simpa [Nat.factorial] using h.trans_eq (by ring)
    have hb3 : ‖(c : ℂ) * deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ ≤ c * (Real.pi + 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (stripG_imag_deriv_far_bounds hτ).1 hc.le
    calc ‖_‖ ≤ ‖Complex.I / (2 * (1 - (τ : ℂ) * Complex.I) ^ 2)‖ +
          ‖Complex.I * iteratedDeriv 2 (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ +
          ‖(c : ℂ) * deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ 1 / 2 + 1 / (6 * c) + c * (Real.pi + 2) := by linarith
      _ ≤ Mr := by
          simp only [Mr]
          have : 0 ≤ c * (Cg + |L1|) := mul_nonneg hc.le (by positivity)
          linarith
  exact ⟨hRk0, hRk1⟩

private lemma fctPsi_far_pos {K4 ε c L1 α P B Cdesc : ℝ} (hc : 0 < c) (hP : 0 ≤ P)
    (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) (fun _ => P))
    (hCD : ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Cdesc * c⁻¹ / Real.log (2 + τ)) :
    ∃ (N : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ τ : ℝ, 1 / 2 ≤ τ →
      let ψ := fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)
      ‖ψ τ‖ ≤ M * (1 + τ) ^ N * Real.exp (-(Real.pi * τ)) ∧
      ‖deriv ψ τ‖ ≤ M * (1 + τ) ^ N * Real.exp (-(Real.pi * τ)) ∧
      ‖deriv (deriv ψ) τ‖ ≤ M * (1 + τ) ^ N * Real.exp (-(Real.pi * τ)) := by
  obtain ⟨M0, hM0, hpsi0⟩ := fctPsi_far_zero_pos hc hDh hDc hDb hCD
  obtain ⟨Ma, hMa, hA_ej⟩ := fctWarpA_far_EJOn (ε := ε) (L1 := L1) hc hP hEnv
  obtain ⟨Mr, hMr, hRk_bd⟩ := fctRk_far_bounds (c := c) (L1 := L1) hc
  set ψ : ℝ → ℂ := fun t => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)
  set A : ℝ → ℂ := fun t => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)
  set M1 : ℝ := Ma + Mr * M0
  set M2 : ℝ := 2 * Ma + Mr * M0 + Mr * M1
  set M : ℝ := max M0 (max M1 M2)
  refine ⟨12, M, hM0.trans (le_max_left _ _), fun τ hτ => ?_⟩
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have h1τ : 1 ≤ 1 + τ := by linarith
  have hexp_pos : 0 ≤ Real.exp (-(Real.pi * τ)) := (Real.exp_pos _).le
  have hb0_raw := hpsi0 τ hτ
  have hb0 : ‖ψ τ‖ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    have hpow : (1 + τ) ^ 8 ≤ (1 + τ) ^ 12 := pow_le_pow_right₀ h1τ (by norm_num)
    have hM : M0 ≤ M := le_max_left _ _
    calc ‖ψ τ‖ ≤ M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) := hb0_raw
      _ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by gcongr
  have hode : ∀ t : ℝ, 0 < t → deriv ψ t = Complex.I * (A t - fctRk c L1 t * ψ t) := fun t ht => by
    have h1 := (fctPsi_hasDerivAt_pos hc hDc ⟨B, hDb⟩ hEnv ht).deriv
    rwa [mellinK0_log_deriv_imag hc t] at h1
  have hA0 : ‖A τ‖ ≤ Ma * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by
    have h := hA_ej.b0 τ hτ hτpos.ne'
    simpa [ejW, abs_of_pos hτpos] using h
  have hA1 : ‖deriv A τ‖ ≤ (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    have h := hA_ej.b1 τ hτ hτpos.ne'
    simp only [ejW, zero_sub, Nat.cast_one, abs_of_pos hτpos, Real.rpow_neg hτpos.le,
      Real.rpow_one] at h
    have hτinv : τ⁻¹ ≤ 2 := by rw [inv_le_iff₀' hτpos]; linarith
    calc ‖deriv A τ‖ ≤ Ma * (τ⁻¹ * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ))) := h
      _ ≤ Ma * (2 * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ))) := by gcongr
      _ = (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by ring
  have hRk := hRk_bd τ hτ
  have hb1_raw : ‖deriv ψ τ‖ ≤ M1 * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by
    rw [hode τ hτpos, norm_mul, Complex.norm_I, one_mul]
    calc ‖A τ - fctRk c L1 τ * ψ τ‖ ≤ ‖A τ‖ + ‖fctRk c L1 τ‖ * ‖ψ τ‖ := by
          simpa [norm_mul] using norm_sub_le (A τ) (fctRk c L1 τ * ψ τ)
      _ ≤ Ma * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) +
          (Mr * (1 + τ)) * (M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ))) := by gcongr
      _ = Ma * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) +
          (Mr * M0) * (1 + τ) ^ 9 * Real.exp (-(Real.pi * τ)) := by ring
      _ ≤ Ma * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) +
          (Mr * M0) * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by
          gcongr; exact pow_le_pow_right₀ h1τ (by norm_num)
      _ = M1 * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by simp only [M1]; ring
  have hb1 : ‖deriv ψ τ‖ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    have hpow : (1 + τ) ^ 11 ≤ (1 + τ) ^ 12 := pow_le_pow_right₀ h1τ (by norm_num)
    have hM : M1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    exact hb1_raw.trans (by gcongr)
  have hderiv2 : deriv (deriv ψ) τ =
      Complex.I * (deriv A τ - (deriv (fctRk c L1) τ * ψ τ + fctRk c L1 τ * deriv ψ τ)) := by
    have hev : deriv ψ =ᶠ[𝓝 τ] fun t : ℝ => Complex.I * (A t - fctRk c L1 t * ψ t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hτpos] with t ht
      exact hode t ht
    have hdA : HasDerivAt A (deriv A τ) τ :=
      ((hA_ej.c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds hτpos.ne')).hasDerivAt
    have hdψ : HasDerivAt ψ (deriv ψ τ) τ :=
      (fctPsi_hasDerivAt_pos hc hDc ⟨B, hDb⟩ hEnv hτpos).hasDerivAt.congr_deriv
        ((fctPsi_hasDerivAt_pos hc hDc ⟨B, hDb⟩ hEnv hτpos).deriv.symm)
    have hdRk : HasDerivAt (fctRk c L1) (deriv (fctRk c L1) τ) τ := by
      have h1 : DifferentiableAt ℝ (fctRk c L1) τ := by
        have h1d : DifferentiableAt ℝ (fun t : ℝ => 1 / (2 * (1 - (t : ℂ) * Complex.I))) τ := by
          have hne : (2 : ℂ) * (1 - (τ : ℂ) * Complex.I) ≠ 0 := by
            intro h0; rw [mul_eq_zero] at h0
            rcases h0 with h | h
            · norm_num at h
            · have := congr_arg Complex.re h; simp at this
          exact (differentiableAt_const _).div (by fun_prop) hne
        have h2d : DifferentiableAt ℝ (fun t : ℝ => deriv (FormalResearch.Asymptotics.binetDiff c) ((t : ℂ) * Complex.I)) τ := by
          have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
          have hcd := (FormalResearch.Asymptotics.binetDiff_differentiableOn hc).contDiffOn hopen (n := 2)
          have hcd1 := (contDiffOn_succ_iff_deriv_of_isOpen hopen).mp hcd |>.2
          exact ((hcd1.differentiableOn (by norm_num)).differentiableAt
            (hopen.mem_nhds (by simp : ((τ : ℂ) * Complex.I).re < 1))).comp τ (by fun_prop)
        have h3d : DifferentiableAt ℝ (fun t : ℝ => (c : ℂ) * (stripG ((t : ℂ) * Complex.I) + (L1 : ℂ))) τ :=
          (((stripG_imag_deriv_pos hτpos).differentiableAt).add_const _).const_mul _
        exact (h1d.add h2d).add h3d
      exact h1d.hasDerivAt
    have hprod := hdRk.mul hdψ
    have hcomb := (hdA.sub hprod).const_mul Complex.I
    rw [hev.deriv_eq, hcomb.deriv]
  have hb2_raw : ‖deriv (deriv ψ) τ‖ ≤ M2 * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    rw [hderiv2, norm_mul, Complex.norm_I, one_mul]
    calc ‖deriv A τ - (deriv (fctRk c L1) τ * ψ τ + fctRk c L1 τ * deriv ψ τ)‖
        ≤ ‖deriv A τ‖ + (‖deriv (fctRk c L1) τ‖ * ‖ψ τ‖ + ‖fctRk c L1 τ‖ * ‖deriv ψ τ‖) := by
          simpa [norm_mul] using (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) +
          (Mr * (M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ))) +
            (Mr * (1 + τ)) * (M1 * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)))) := by gcongr
      _ = (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) +
          ((Mr * M0) * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) +
            (Mr * M1) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ))) := by ring
      _ ≤ (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) +
          ((Mr * M0) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) +
            (Mr * M1) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ))) := by
          gcongr; exact pow_le_pow_right₀ h1τ (by norm_num)
      _ = M2 * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by simp only [M2]; ring
  have hb2 : ‖deriv (deriv ψ) τ‖ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) :=
    hb2_raw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)) hexp_pos)
  exact ⟨hb0, hb1, hb2⟩

/-! ### Part 5: Reflection to `τ ≤ -1/2` and main theorem `fctPsi_far` -/

private lemma conj_reflect_derivs {ψ : ℝ → ℂ} (hconj : ∀ t : ℝ, ψ (-t) = starRingEnd ℂ (ψ t))
    (hdiff : DifferentiableOn ℝ ψ {t : ℝ | 0 < t})
    (hdiff2 : DifferentiableOn ℝ (deriv ψ) {t : ℝ | 0 < t})
    {τ : ℝ} (hτ : τ < 0) :
    ‖ψ τ‖ = ‖ψ (-τ)‖ ∧
    ‖deriv ψ τ‖ = ‖deriv ψ (-τ)‖ ∧
    ‖deriv (deriv ψ) τ‖ = ‖deriv (deriv ψ) (-τ)‖ := by
  have hpos : 0 < -τ := neg_pos.mpr hτ
  have hnh : {t : ℝ | 0 < t} ∈ 𝓝 (-τ) := isOpen_Ioi.mem_nhds hpos
  have hd1 : HasDerivAt ψ (deriv ψ (-τ)) (-τ) := (hdiff.differentiableAt hnh).hasDerivAt
  have heq : ψ = fun t : ℝ => Complex.conjCLE (ψ (-t)) := by
    funext t; simpa using (congr_arg (starRingEnd ℂ) (hconj t)).symm
  have hrefl1 : ∀ t : ℝ, t < 0 → deriv ψ t = -Complex.conjCLE (deriv ψ (-t)) := fun t ht => by
    have hpt : HasDerivAt (fun x : ℝ => Complex.conjCLE (ψ (-x)))
        (Complex.conjCLE (deriv ψ (-t) * (-1))) t := by
      have h1 := ((hdiff.differentiableAt (isOpen_Ioi.mem_nhds (neg_pos.mpr ht))).hasDerivAt).comp t
        (hasDerivAt_neg t)
      exact Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t h1
    rw [← heq] at hpt
    rw [hpt.deriv]; simp
  have hd2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) (-τ)) (-τ) := (hdiff2.differentiableAt hnh).hasDerivAt
  have hrefl2_at : deriv (deriv ψ) τ = Complex.conjCLE (deriv (deriv ψ) (-τ)) := by
    have hev : deriv ψ =ᶠ[𝓝 τ] fun t : ℝ => -Complex.conjCLE (deriv ψ (-t)) := by
      filter_upwards [isOpen_Iio.mem_nhds hτ] with t ht
      exact hrefl1 t ht
    have hpt : HasDerivAt (fun t : ℝ => -Complex.conjCLE (deriv ψ (-t)))
        (-(Complex.conjCLE (deriv (deriv ψ) (-τ) * (-1)))) τ := by
      have h1 := hd2.comp τ (hasDerivAt_neg τ)
      exact (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ h1).neg
    rw [hev.deriv_eq, hpt.deriv]; simp
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [show τ = -(-τ) by ring, hconj (-τ), Complex.norm_conj]
  · rw [hrefl1 τ hτ, norm_neg]; simpa using Complex.norm_conj (deriv ψ (-τ))
  · rw [hrefl2_at]; simpa using Complex.norm_conj (deriv (deriv ψ) (-τ))

/-- **Far left-edge decay (`fct:splitting`)**: on `|τ| ≥ 1/2`, `Ψ_c(iτ)` and its first two
derivatives decay like `(1 + |τ|)^N exp(-π |τ|)` under `FctDescentStmt h`. -/
theorem fctPsi_far {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      let ψ := fun t : ℝ => fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)
      ∃ (N : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ τ : ℝ, 1 / 2 ≤ |τ| →
        ‖ψ τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(Real.pi * |τ|)) ∧
        ‖deriv ψ τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(Real.pi * |τ|)) ∧
        ‖deriv (deriv ψ) τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(Real.pi * |τ|)) := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨Cdesc, c0Desc, hDesc⟩ := hD
  refine ⟨max (max c0D c0Desc) 1, fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' (le_max_right _ _)
  have hcpos : 0 < c := by linarith
  have hcD' := hcD ε c hε (hc.trans' ((le_max_left _ _).trans (le_max_left _ _)))
  have hcDesc' := hDesc ε c hε (hc.trans' ((le_max_right _ _).trans (le_max_left _ _)))
  obtain ⟨B, hB⟩ := hcD'.bd
  obtain ⟨P, hP, hEnv⟩ := hcD'.env
  have hCD : ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        Cdesc * c⁻¹ / Real.log (2 + τ) := fun τ hτ => by
    have h1 := hcDesc' (3 / 8) τ (by norm_num) (by norm_num)
    rwa [abs_of_pos (by linarith : 0 < τ)] at h1
  obtain ⟨N, M, hM, hpos⟩ := fctPsi_far_pos hcpos hP hcD'.hol hcD'.cont hB hEnv hCD
  refine ⟨N, M, hM, fun τ hτ => ?_⟩
  rcases le_or_gt 0 τ with hτ0 | hτneg
  · have habs : |τ| = τ := abs_of_nonneg hτ0
    simpa [habs] using hpos τ (by linarith)
  · have habs : |τ| = -τ := abs_of_neg hτneg
    have hneg_ge : 1 / 2 ≤ -τ := by linarith
    have hconj : ∀ t : ℝ, fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (((-t : ℝ) : ℂ) * Complex.I) =
        starRingEnd ℂ (fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)) := by
      intro t
      have heq : ((-t : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((t : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      rw [heq]
      exact fctPsi_conj hcD'.conj (by simp) (by simp)
    have hcd_pos : ContDiffOn ℝ 2 (fun t : ℝ =>
        fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)) {t : ℝ | 0 < t} := by
      refine contDiffOn_iff_contDiffAt.mpr fun t ht => ?_
      have hcd_left := fctPsi_contDiffOn_left (K4 := K4) (ε := ε) (c := c) (L1 := fctWarpL1 h ε c)
        (α := fctWarpAlpha h ε c) hcpos hcD'.cont ⟨B, hB⟩ hEnv
      exact hcd_left.contDiffAt (isOpen_Ioi.mem_nhds ht) |>.of_le (by norm_cast)
    have hdiff1 : DifferentiableOn ℝ (fun t : ℝ =>
        fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)) {t : ℝ | 0 < t} :=
      hcd_pos.differentiableOn (by norm_num)
    have hdiff2 : DifferentiableOn ℝ (deriv (fun t : ℝ =>
        fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I))) {t : ℝ | 0 < t} :=
      ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mp hcd_pos).2.differentiableOn (by norm_num)
    have hrefl := conj_reflect_derivs hconj hdiff1 hdiff2 hτneg
    have hp := hpos (-τ) hneg_ge
    simpa [habs, hrefl.1, hrefl.2.1, hrefl.2.2] using hp

/-- info: 'FormalResearch.SignUncertainty.fctPsi_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPsi_far

end FormalResearch.SignUncertainty
