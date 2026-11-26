module

public import FormalResearch.SignUncertainty.AiryRationalSeeds
public import FormalResearch.SignUncertainty.ShellGapOriginFloor
public import FormalResearch.Special.AiryCftQUniform
public import FormalResearch.Special.AiryGoodCircles
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Smooth Regularization and Hermite--Airy Rational Approximation (`lem:al-smooth`, `lem:al-hermite-approx`)

This module formalizes two ingredients for `thm:al-rational-density` from
`CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex`:

1. **Cauchy derivative estimates in the Airy class (`§1`):**
   * `re_cpow_three_halves_ball_abs_sub_le` and `airyEnv_ball_le`: on the disc
     `‖ζ - w‖ ≤ 2 (1 + ‖w‖)^{-1/2}`, `Re(ζ^{3/2})` varies by at most `30`, so `airyEnv ζ ≤ e^{40} airyEnv w`
     uniformly across the negative real branch cut via a first-quadrant square-root comparison;
   * `deriv_inAiryClass_bound`: if `H` is entire with `‖H z‖ ≤ C (1 + ‖z‖)^ν airyEnv z`, then
     `‖deriv H w‖ ≤ C₁ (1 + ‖w‖)^{ν + 1/2} airyEnv w`.

2. **Lemma `lem:al-smooth` (`lem_al_smooth`, `§2`):**
   For `H ∈ 𝒢` and `ε ∈ (0, 1]`, `m_ε(z) = ∫_{-1}^1 φ(t) cosh(ε t √z) dt`, `M_ε = m_ε^2`, and
   `H_ε(z) = M_ε(z) H(z + 2ε)` give `H_ε ∈ 𝒢 ∩ 𝓢(ℝ)` with locally uniform convergence on `ℂ`,
   weighted `L¹(e^{Y max(u, 0)} du)` convergence for every `Y ≥ 0`, uniform `L¹` norm bound, and
   `|ℒ_y(H_ε(· + s))| ≤ C_H e^{-s y}` (`(eq:al-shift-bound)`).

3. **Lemma `lem:al-hermite-approx` (`lem_al_hermite_approx`, `§3`):**
   For real-on-`ℝ` `F ∈ 𝒢 ∩ 𝓢(ℝ)`, the Hermite--Airy expansion `(eq:al-hermite)` holds on all of `ℂ`
   (proved without contour residue calculus by dividing `F - S` twice at each zero via `dslope`, bounding
   the entire quotient `(F - S) / Ai²` on good circles via `airyQ_mem_half` and `good_circle_exists`, and
   applying the maximum modulus principle), `∑ F'(a_n)/Ai'(a_n)² = 0`, and the partial sums `F_N ∈ ℛ_Ai^gen`
   satisfy (a)–(d).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric FormalResearch.Special
open scoped Real Nat ContDiff Uniformity

namespace FormalResearch.SignUncertainty

/-! ### Section 1: Envelope Stability on `(1 + ‖w‖)^{-1/2}` Balls and Cauchy Bounds -/

/-- First-quadrant comparison showing `|(ζ^{3/2}).re - (w^{3/2}).re| ≤ 30` whenever
`‖ζ - w‖ ≤ 2 (1 + ‖w‖)^{-1/2}`, uniformly across the branch cut `(-∞, 0]`. -/
theorem re_cpow_three_halves_ball_abs_sub_le {w ζ : ℂ}
    (hζ : ‖ζ - w‖ ≤ 2 * (1 + ‖w‖) ^ (-(1 / 2 : ℝ))) :
    |(ζ ^ (3 / 2 : ℂ)).re - (w ^ (3 / 2 : ℂ)).re| ≤ 30 := by
  have hw1_pos : 0 < 1 + ‖w‖ := by positivity
  have hr_le_two : 2 * (1 + ‖w‖) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
    have h1 : (1 + ‖w‖) ^ (-(1 / 2 : ℝ)) ≤ 1 ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith [norm_nonneg w]) (by norm_num)
    rw [Real.one_rpow] at h1
    linarith
  have hdist_le_two : ‖ζ - w‖ ≤ 2 := hζ.trans hr_le_two
  by_cases hw_small : ‖w‖ ≤ 4
  · have hζ_le : ‖ζ‖ ≤ 6 := by
      calc ‖ζ‖ = ‖(ζ - w) + w‖ := by ring_nf
        _ ≤ ‖ζ - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ 2 + 4 := add_le_add hdist_le_two hw_small
        _ = 6 := by norm_num
    have hcube_bound : ∀ z : ℂ, |(z ^ (3 / 2 : ℂ)).re| ^ 2 ≤ ‖z‖ ^ 3 := fun z => by
      rw [re_cpow_three_halves_eq_ab z, sq_abs]
      have hsq := airySqrtRe_sq_add z
      set a := airySqrtRe z
      set b := (z ^ (1 / 2 : ℂ)).im
      have hid : (a ^ 2 + b ^ 2) ^ 3 - (a ^ 3 - 3 * a * b ^ 2) ^ 2 =
          (3 * a ^ 2 * b - b ^ 3) ^ 2 := by ring
      rw [← hsq]
      nlinarith [sq_nonneg (3 * a ^ 2 * b - b ^ 3)]
    have hw_re : |(w ^ (3 / 2 : ℂ)).re| ≤ 8 := by
      have h1 : |(w ^ (3 / 2 : ℂ)).re| ^ 2 ≤ 8 ^ 2 := by
        calc |(w ^ (3 / 2 : ℂ)).re| ^ 2 ≤ ‖w‖ ^ 3 := hcube_bound w
          _ ≤ 4 ^ 3 := pow_le_pow_left₀ (norm_nonneg w) hw_small 3
          _ = 8 ^ 2 := by norm_num
      nlinarith [abs_nonneg (w ^ (3 / 2 : ℂ)).re]
    have hζ_re : |(ζ ^ (3 / 2 : ℂ)).re| ≤ 15 := by
      have h1 : |(ζ ^ (3 / 2 : ℂ)).re| ^ 2 ≤ 15 ^ 2 := by
        calc |(ζ ^ (3 / 2 : ℂ)).re| ^ 2 ≤ ‖ζ‖ ^ 3 := hcube_bound ζ
          _ ≤ 6 ^ 3 := pow_le_pow_left₀ (norm_nonneg ζ) hζ_le 3
          _ ≤ 15 ^ 2 := by norm_num
      nlinarith [abs_nonneg (ζ ^ (3 / 2 : ℂ)).re]
    calc |(ζ ^ (3 / 2 : ℂ)).re - (w ^ (3 / 2 : ℂ)).re|
        ≤ |(ζ ^ (3 / 2 : ℂ)).re| + |(w ^ (3 / 2 : ℂ)).re| := abs_sub _ _
      _ ≤ 15 + 8 := add_le_add hζ_re hw_re
      _ ≤ 30 := by norm_num
  · push Not at hw_small
    set a := airySqrtRe w
    set b := |(w ^ (1 / 2 : ℂ)).im|
    set a' := airySqrtRe ζ
    set b' := |(ζ ^ (1 / 2 : ℂ)).im|
    have ha0 : 0 ≤ a := airySqrtRe_nonneg w
    have hb0 : 0 ≤ b := abs_nonneg _
    have ha'0 : 0 ≤ a' := airySqrtRe_nonneg ζ
    have hb'0 : 0 ≤ b' := abs_nonneg _
    set q : ℂ := (a : ℂ) + (b : ℂ) * I
    set q' : ℂ := (a' : ℂ) + (b' : ℂ) * I
    have hq_norm_sq : ‖q‖ ^ 2 = ‖w‖ := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I, sq_abs]
      exact airySqrtRe_sq_add w
    have hq'_norm_sq : ‖q'‖ ^ 2 = ‖ζ‖ := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I, sq_abs]
      exact airySqrtRe_sq_add ζ
    have hq_cube_re : (q ^ 3).re = (w ^ (3 / 2 : ℂ)).re := by
      have hre : (q ^ 3).re = a ^ 3 - 3 * a * b ^ 2 := by
        simp [q, pow_three, Complex.mul_re, Complex.mul_im]
        ring
      rw [hre, sq_abs, ← re_cpow_three_halves_eq_ab w]
    have hq'_cube_re : (q' ^ 3).re = (ζ ^ (3 / 2 : ℂ)).re := by
      have hre : (q' ^ 3).re = a' ^ 3 - 3 * a' * b' ^ 2 := by
        simp [q', pow_three, Complex.mul_re, Complex.mul_im]
        ring
      rw [hre, sq_abs, ← re_cpow_three_halves_eq_ab ζ]
    have hq2_re : (q' ^ 2 - q ^ 2).re = (ζ - w).re := by
      have h1 : (q' ^ 2 - q ^ 2).re = (a' ^ 2 - b' ^ 2) - (a ^ 2 - b ^ 2) := by
        simp [q, q', sq, Complex.mul_re, Complex.mul_im]
      rw [h1, sq_abs, sq_abs, airySqrtRe_sq_sub ζ, airySqrtRe_sq_sub w, Complex.sub_re]
    have hq2_im : |(q' ^ 2 - q ^ 2).im| ≤ |(ζ - w).im| := by
      have h1 : (q' ^ 2 - q ^ 2).im = 2 * a' * b' - 2 * a * b := by
        simp [q, q', sq, Complex.mul_re, Complex.mul_im]
        ring
      have hw_im : 2 * a * b = |w.im| := by
        calc 2 * a * b = |2 * airySqrtRe w * (w ^ (1 / 2 : ℂ)).im| := by
              rw [abs_mul, abs_mul, Nat.abs_ofNat, abs_of_nonneg ha0]
          _ = |w.im| := by rw [airySqrtRe_mul_im w]
      have hζ_im : 2 * a' * b' = |ζ.im| := by
        calc 2 * a' * b' = |2 * airySqrtRe ζ * (ζ ^ (1 / 2 : ℂ)).im| := by
              rw [abs_mul, abs_mul, Nat.abs_ofNat, abs_of_nonneg ha'0]
          _ = |ζ.im| := by rw [airySqrtRe_mul_im ζ]
      rw [h1, hw_im, hζ_im, Complex.sub_im]
      exact abs_abs_sub_abs_le_abs_sub ζ.im w.im
    have hq2_norm : ‖q' ^ 2 - q ^ 2‖ ^ 2 ≤ 2 * ‖ζ - w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq, hq2_re]
      have hre_le : (ζ - w).re ^ 2 ≤ ‖ζ - w‖ ^ 2 := by
        have h := Complex.abs_re_le_norm (ζ - w)
        nlinarith [sq_abs (ζ - w).re, abs_nonneg (ζ - w).re, norm_nonneg (ζ - w)]
      have him_le : (q' ^ 2 - q ^ 2).im ^ 2 ≤ ‖ζ - w‖ ^ 2 := by
        have h := hq2_im.trans (Complex.abs_im_le_norm (ζ - w))
        nlinarith [sq_abs (q' ^ 2 - q ^ 2).im, abs_nonneg (q' ^ 2 - q ^ 2).im, norm_nonneg (ζ - w)]
      linarith
    have hq_sum_ge : ‖w‖ ≤ ‖q' + q‖ ^ 2 := by
      have h1 : ‖q' + q‖ ^ 2 = (a' + a) ^ 2 + (b' + b) ^ 2 := by
        have hsum : q' + q = ((a' + a : ℝ) : ℂ) + ((b' + b : ℝ) : ℂ) * I := by
          simp [q, q']; ring
        rw [hsum, Complex.sq_norm, Complex.normSq_add_mul_I]
      rw [h1, ← hq_norm_sq, Complex.sq_norm, Complex.normSq_add_mul_I]
      nlinarith
    have hdist_sq : ‖ζ - w‖ ^ 2 ≤ 4 / (1 + ‖w‖) := by
      calc ‖ζ - w‖ ^ 2 ≤ (2 * (1 + ‖w‖) ^ (-(1 / 2 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hζ 2
        _ = 4 * ((1 + ‖w‖) ^ (-(1 / 2 : ℝ))) ^ 2 := by ring
        _ = 4 * (1 + ‖w‖) ^ ((-1 / 2 : ℝ) * 2) := by
            rw [← Real.rpow_natCast ((1 + ‖w‖) ^ _), ← Real.rpow_mul hw1_pos.le]; norm_num
        _ = 4 / (1 + ‖w‖) := by
            rw [show (-1 / 2 : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one]; ring
    have hdiff_sq : ‖q' - q‖ ^ 2 ≤ 8 / ‖w‖ ^ 2 := by
      have hmul : ‖q' - q‖ ^ 2 * ‖w‖ ≤ 2 * ‖ζ - w‖ ^ 2 := by
        calc ‖q' - q‖ ^ 2 * ‖w‖ ≤ ‖q' - q‖ ^ 2 * ‖q' + q‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hq_sum_ge (sq_nonneg _)
          _ = ‖(q' - q) * (q' + q)‖ ^ 2 := by rw [norm_mul, mul_pow]
          _ = ‖q' ^ 2 - q ^ 2‖ ^ 2 := by ring_nf
          _ ≤ 2 * ‖ζ - w‖ ^ 2 := hq2_norm
      have hw_pos : 0 < ‖w‖ := by linarith
      rw [le_div_iff₀ (sq_pos_of_pos hw_pos)]
      have h2 : 2 * ‖ζ - w‖ ^ 2 * ‖w‖ ≤ 8 := by
        have h3 : 2 * ‖ζ - w‖ ^ 2 ≤ 8 / (1 + ‖w‖) := by
          calc 2 * ‖ζ - w‖ ^ 2 ≤ 2 * (4 / (1 + ‖w‖)) :=
                mul_le_mul_of_nonneg_left hdist_sq (by norm_num)
            _ = 8 / (1 + ‖w‖) := by ring
        calc 2 * ‖ζ - w‖ ^ 2 * ‖w‖ ≤ (8 / (1 + ‖w‖)) * ‖w‖ :=
              mul_le_mul_of_nonneg_right h3 hw_pos.le
          _ ≤ (8 / (1 + ‖w‖)) * (1 + ‖w‖) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = 8 := div_mul_cancel₀ 8 hw1_pos.ne'
      calc ‖q' - q‖ ^ 2 * ‖w‖ ^ 2 = (‖q' - q‖ ^ 2 * ‖w‖) * ‖w‖ := by ring
        _ ≤ (2 * ‖ζ - w‖ ^ 2) * ‖w‖ := mul_le_mul_of_nonneg_right hmul hw_pos.le
        _ ≤ 8 := h2
    have hdiff_le : ‖q' - q‖ ≤ 3 / ‖w‖ := by
      have hw_pos : 0 < ‖w‖ := by linarith
      have h1 : ‖q' - q‖ ^ 2 ≤ (3 / ‖w‖) ^ 2 := by
        refine hdiff_sq.trans ?_
        rw [div_pow]
        exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg ‖w‖)
      nlinarith [norm_nonneg (q' - q), div_pos (show (0 : ℝ) < 3 by norm_num) hw_pos]
    have hζ_le_2w : ‖ζ‖ ≤ 2 * ‖w‖ := by
      have htri : ‖ζ‖ ≤ ‖ζ - w‖ + ‖w‖ := by
        calc ‖ζ‖ = ‖(ζ - w) + w‖ := by ring_nf
          _ ≤ ‖ζ - w‖ + ‖w‖ := norm_add_le _ _
      linarith
    have hquad_le : ‖q' ^ 2 + q' * q + q ^ 2‖ ≤ 5 * ‖w‖ := by
      have hqq' : ‖q'‖ * ‖q‖ ≤ 2 * ‖w‖ := by
        have hsq_qq' : (‖q'‖ * ‖q‖) ^ 2 ≤ (2 * ‖w‖) ^ 2 := by
          rw [mul_pow, hq'_norm_sq, hq_norm_sq]
          nlinarith
        nlinarith [norm_nonneg q', norm_nonneg q]
      have htri1 := norm_add_le (q' ^ 2 + q' * q) (q ^ 2)
      have htri2 := norm_add_le (q' ^ 2) (q' * q)
      rw [norm_pow, hq_norm_sq] at htri1
      rw [norm_pow, norm_mul, hq'_norm_sq] at htri2
      linarith
    have hw_pos : 0 < ‖w‖ := by linarith
    rw [← hq'_cube_re, ← hq_cube_re, ← Complex.sub_re]
    calc |(q' ^ 3 - q ^ 3).re|
        ≤ ‖q' ^ 3 - q ^ 3‖ := Complex.abs_re_le_norm _
      _ = ‖(q' - q) * (q' ^ 2 + q' * q + q ^ 2)‖ := by ring_nf
      _ = ‖q' - q‖ * ‖q' ^ 2 + q' * q + q ^ 2‖ := norm_mul _ _
      _ ≤ (3 / ‖w‖) * (5 * ‖w‖) := mul_le_mul hdiff_le hquad_le (norm_nonneg _) (by positivity)
      _ = 15 := by field_simp [hw_pos.ne']; ring
      _ ≤ 30 := by norm_num

/-- Envelope stability on `(1 + ‖w‖)^{-1/2}` balls: `airyEnv ζ ≤ exp 40 * airyEnv w`. -/
theorem airyEnv_ball_le {w ζ : ℂ} (hζ : ‖ζ - w‖ ≤ 2 * (1 + ‖w‖) ^ (-(1 / 2 : ℝ))) :
    airyEnv ζ ≤ Real.exp 40 * airyEnv w := by
  unfold airyEnv
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp (re_cpow_three_halves_ball_abs_sub_le hζ)).1
  linarith

private lemma one_add_norm_rpow_ball_le (ν : ℝ) {w ζ : ℂ} (hζ : ‖ζ - w‖ ≤ 1) :
    (1 + ‖ζ‖) ^ ν ≤ 4 ^ |ν| * (1 + ‖w‖) ^ ν := by
  have hw_pos : 0 < 1 + ‖w‖ := by positivity
  have hζ_pos : 0 < 1 + ‖ζ‖ := by positivity
  have hup : 1 + ‖ζ‖ ≤ 4 * (1 + ‖w‖) := by
    have htri : ‖ζ‖ ≤ ‖ζ - w‖ + ‖w‖ := by
      calc ‖ζ‖ = ‖(ζ - w) + w‖ := by ring_nf
        _ ≤ ‖ζ - w‖ + ‖w‖ := norm_add_le _ _
    linarith [norm_nonneg w]
  have hlow : (1 + ‖w‖) / 4 ≤ 1 + ‖ζ‖ := by
    by_cases hw3 : ‖w‖ ≤ 3
    · have : (1 + ‖w‖) / 4 ≤ 1 := by linarith
      linarith [norm_nonneg ζ]
    · push Not at hw3
      have h1 : ‖w‖ - 1 ≤ ‖ζ‖ := by
        have htri : ‖w‖ ≤ ‖w - ζ‖ + ‖ζ‖ := by
          calc ‖w‖ = ‖(w - ζ) + ζ‖ := by ring_nf
            _ ≤ ‖w - ζ‖ + ‖ζ‖ := norm_add_le _ _
        rw [norm_sub_rev] at htri
        linarith
      linarith
  rcases le_or_gt 0 ν with hν | hν
  · rw [abs_of_nonneg hν, ← Real.mul_rpow (by norm_num) hw_pos.le]
    exact Real.rpow_le_rpow hζ_pos.le hup hν
  · rw [abs_of_neg hν]
    have hneg : 0 ≤ -ν := by linarith
    have h1 : (1 + ‖w‖) ^ (-ν) ≤ (4 * (1 + ‖ζ‖)) ^ (-ν) :=
      Real.rpow_le_rpow hw_pos.le (by linarith) hneg
    rw [Real.mul_rpow (by norm_num) hζ_pos.le] at h1
    have h2 : (1 + ‖ζ‖) ^ ν = ((1 + ‖ζ‖) ^ (-ν))⁻¹ := by
      rw [Real.rpow_neg hζ_pos.le, inv_inv]
    have h3 : (1 + ‖w‖) ^ ν = ((1 + ‖w‖) ^ (-ν))⁻¹ := by
      rw [Real.rpow_neg hw_pos.le, inv_inv]
    rw [h2, h3]
    have hp1 : 0 < (1 + ‖ζ‖) ^ (-ν) := Real.rpow_pos_of_pos hζ_pos _
    have hp2 : 0 < (1 + ‖w‖) ^ (-ν) := Real.rpow_pos_of_pos hw_pos _
    rw [inv_le_iff_one_le_mul₀' hp1]
    calc (1 : ℝ) = (1 + ‖w‖) ^ (-ν) * ((1 + ‖w‖) ^ (-ν))⁻¹ :=
          (mul_inv_cancel₀ hp2.ne').symm
      _ ≤ (4 ^ (-ν) * (1 + ‖ζ‖) ^ (-ν)) * ((1 + ‖w‖) ^ (-ν))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hp2.le)
      _ = (1 + ‖ζ‖) ^ (-ν) * (4 ^ (-ν) * ((1 + ‖w‖) ^ (-ν))⁻¹) := by ring

/-- Cauchy's first-derivative estimate on `(1 + ‖w‖)^{-1/2}` circles preserves polynomial-times-`airyEnv`
growth with exponent shift `+ 1 / 2`. -/
theorem deriv_inAiryClass_bound {H : ℂ → ℂ} (hH_diff : Differentiable ℂ H)
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ z : ℂ, ‖H z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z) :
    ∀ w : ℂ, ‖deriv H w‖ ≤
      (C * 4 ^ |ν| * Real.exp 40) * (1 + ‖w‖) ^ (ν + 1 / 2) * airyEnv w := by
  intro w
  have hw_pos : 0 < 1 + ‖w‖ := by positivity
  set r : ℝ := (1 + ‖w‖) ^ (-(1 / 2 : ℝ))
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hw_pos _
  have hr_le_one : r ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
    have h2 := Real.rpow_le_rpow_of_nonpos zero_lt_one h1 (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    rwa [Real.one_rpow] at h2
  set M : ℝ := C * 4 ^ |ν| * Real.exp 40 * (1 + ‖w‖) ^ ν * airyEnv w
  have hsphere : ∀ ζ ∈ sphere w r, ‖H ζ‖ ≤ M := by
    intro ζ hζ
    have hnorm : ‖ζ - w‖ = r := mem_sphere_iff_norm.mp hζ
    have h1 := hb ζ
    have h2 := one_add_norm_rpow_ball_le ν (w := w) (ζ := ζ) (by linarith)
    have h3 := airyEnv_ball_le (w := w) (ζ := ζ) (by rw [hnorm]; linarith)
    calc ‖H ζ‖ ≤ C * (1 + ‖ζ‖) ^ ν * airyEnv ζ := h1
      _ ≤ C * (4 ^ |ν| * (1 + ‖w‖) ^ ν) * (Real.exp 40 * airyEnv w) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (airyEnv_pos ζ).le ?_
          positivity
      _ = M := by dsimp [M]; ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hr_pos
    hH_diff.differentiableOn.diffContOnCl hsphere
  rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at hcauchy
  refine hcauchy.trans_eq ?_
  have hr_inv : r⁻¹ = (1 + ‖w‖) ^ (1 / 2 : ℝ) := by
    dsimp [r]
    rw [Real.rpow_neg hw_pos.le, inv_inv]
  have hrpow_add : (1 + ‖w‖) ^ ν * (1 + ‖w‖) ^ (1 / 2 : ℝ) = (1 + ‖w‖) ^ (ν + 1 / 2) :=
    (Real.rpow_add hw_pos ν (1 / 2)).symm
  rw [div_eq_mul_inv, hr_inv]
  dsimp [M]
  calc C * 4 ^ |ν| * Real.exp 40 * (1 + ‖w‖) ^ ν * airyEnv w * (1 + ‖w‖) ^ (1 / 2 : ℝ)
      = C * 4 ^ |ν| * Real.exp 40 * ((1 + ‖w‖) ^ ν * (1 + ‖w‖) ^ (1 / 2 : ℝ)) * airyEnv w := by ring
    _ = C * 4 ^ |ν| * Real.exp 40 * (1 + ‖w‖) ^ (ν + 1 / 2) * airyEnv w := by rw [hrpow_add]

/-- Iterated real derivatives of `x ↦ (F (x : ℂ)).re` equal the real parts of the complex
iterated derivatives `iteratedDeriv n F (x : ℂ)` for every entire function `F : ℂ → ℂ`. -/
lemma iteratedDeriv_re_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => (F (t : ℂ)).re) x = (iteratedDeriv n F (x : ℂ)).re := by
  have hcomp_eq : ∀ m : ℕ, ∀ t : ℝ,
      iteratedDeriv m (fun s : ℝ => F (s : ℂ)) t = iteratedDeriv m F (t : ℂ) := by
    intro m
    induction m with
    | zero => intro t; rfl
    | succ m ih =>
      intro t
      have hm_diff : Differentiable ℂ (iteratedDeriv m F) :=
        (hF.contDiff (n := (m + 1 : ℕ))).differentiable_iteratedDeriv' m
      have hd : HasDerivAt (fun s : ℝ => iteratedDeriv m F (s : ℂ))
          (iteratedDeriv (m + 1) F (t : ℂ)) t := by
        rw [iteratedDeriv_succ]
        exact (hm_diff (t : ℂ)).hasDerivAt.comp_ofReal
      rw [iteratedDeriv_succ, funext ih, hd.deriv]
  have hre_eq : ∀ m : ℕ, ∀ t : ℝ,
      iteratedDeriv m (fun s : ℝ => (F (s : ℂ)).re) t =
        (iteratedDeriv m (fun s : ℝ => F (s : ℂ)) t).re := by
    intro m
    induction m with
    | zero => intro t; rfl
    | succ m ih =>
      intro t
      have hm_diff : Differentiable ℂ (iteratedDeriv m F) :=
        (hF.contDiff (n := (m + 1 : ℕ))).differentiable_iteratedDeriv' m
      have hdC : HasDerivAt (iteratedDeriv m (fun s : ℝ => F (s : ℂ)))
          (deriv (iteratedDeriv m F) (t : ℂ)) t := by
        rw [funext (hcomp_eq m)]
        exact (hm_diff (t : ℂ)).hasDerivAt.comp_ofReal
      have hdR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdC
      rw [iteratedDeriv_succ, funext ih]
      change deriv (⇑Complex.reCLM ∘ iteratedDeriv m (fun s : ℝ => F (s : ℂ))) t = _
      rw [hdR.deriv, iteratedDeriv_succ, hdC.deriv]
      rfl
  rw [hre_eq n x, hcomp_eq n x]

/-- Real smoothness (`ContDiff ℝ (⊤ : ℕ∞)`) and continuity of `iteratedDeriv n` for
`x ↦ (F (x : ℂ)).re` when `F` is entire. -/
lemma contDiff_re_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (F (t : ℂ)).re) ∧
      ∀ n : ℕ, Continuous (iteratedDeriv n (fun t : ℝ => (F (t : ℂ)).re)) := by
  have hdiff_m : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m (fun t : ℝ => (F (t : ℂ)).re)) := by
    intro m x
    have heq : iteratedDeriv m (fun t : ℝ => (F (t : ℂ)).re) =
        fun t : ℝ => (iteratedDeriv m F (t : ℂ)).re :=
      funext (iteratedDeriv_re_of_differentiable hF m)
    rw [heq]
    have hm_diff : Differentiable ℂ (iteratedDeriv m F) :=
      (hF.contDiff (n := (m + 1 : ℕ))).differentiable_iteratedDeriv' m
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((hm_diff (x : ℂ)).hasDerivAt.comp_ofReal)).differentiableAt
  exact ⟨contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞)) fun m _ => hdiff_m m,
    fun n => (hdiff_m n).continuous⟩

/-- Closure of `InAiryClass` under positive real shifts `z ↦ z + s` (`s ≥ 0`). -/
theorem inAiryClass_shift_nonneg {G : ℂ → ℂ} (hG : InAiryClass G) {s : ℝ} (hs : 0 ≤ s) :
    InAiryClass (fun z : ℂ => G (z + (s : ℂ))) := by
  refine ⟨hG.1.comp (differentiable_id.add (differentiable_const _)), ?_, ?_, ?_⟩
  · have hfun : (fun x : ℝ => G ((x : ℂ) + (s : ℂ))) = fun x : ℝ => G ((x + s : ℝ) : ℂ) := by
      ext x; push_cast; rfl
    rw [hfun]
    exact hG.2.1.comp_add_right s
  · obtain ⟨C, ν, hC, hb⟩ := hG.2.2.1
    set K : ℝ := (1 + s) ^ |ν|
    have hK_nn : 0 ≤ K := by positivity
    refine ⟨C * K, ν, mul_nonneg hC hK_nn, fun z => ?_⟩
    have hz_pos : 0 < 1 + ‖z‖ := by positivity
    have hzs_pos : 0 < 1 + ‖z + (s : ℂ)‖ := by positivity
    have hpoly : (1 + ‖z + (s : ℂ)‖) ^ ν ≤ K * (1 + ‖z‖) ^ ν := by
      rcases le_or_gt 0 ν with hν | hν
      · have hup : 1 + ‖z + (s : ℂ)‖ ≤ (1 + s) * (1 + ‖z‖) := by
          have htri := norm_add_le z (s : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] at htri
          nlinarith [norm_nonneg z]
        dsimp [K]
        rw [abs_of_nonneg hν, ← Real.mul_rpow (by linarith) hz_pos.le]
        exact Real.rpow_le_rpow hzs_pos.le hup hν
      · have hlow : (1 + ‖z‖) / (1 + s) ≤ 1 + ‖z + (s : ℂ)‖ := by
          rw [div_le_iff₀ (by linarith)]
          have htri : ‖z‖ ≤ ‖z + (s : ℂ)‖ + s := by
            calc ‖z‖ = ‖(z + (s : ℂ)) - (s : ℂ)‖ := by ring_nf
              _ ≤ ‖z + (s : ℂ)‖ + ‖(s : ℂ)‖ := norm_sub_le _ _
              _ = ‖z + (s : ℂ)‖ + s := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
          nlinarith [norm_nonneg (z + (s : ℂ))]
        have hneg : 0 ≤ -ν := by linarith
        have h1 : (1 + ‖z‖) ^ (-ν) ≤ ((1 + s) * (1 + ‖z + (s : ℂ)‖)) ^ (-ν) :=
          Real.rpow_le_rpow hz_pos.le (by rw [div_le_iff₀ (by linarith)] at hlow; linarith) hneg
        rw [Real.mul_rpow (by linarith) hzs_pos.le] at h1
        have hp1 : 0 < (1 + ‖z + (s : ℂ)‖) ^ (-ν) := Real.rpow_pos_of_pos hzs_pos _
        have hp2 : 0 < (1 + ‖z‖) ^ (-ν) := Real.rpow_pos_of_pos hz_pos _
        have h2 : (1 + ‖z + (s : ℂ)‖) ^ ν = ((1 + ‖z + (s : ℂ)‖) ^ (-ν))⁻¹ := by
          rw [Real.rpow_neg hzs_pos.le, inv_inv]
        have h3 : (1 + ‖z‖) ^ ν = ((1 + ‖z‖) ^ (-ν))⁻¹ := by
          rw [Real.rpow_neg hz_pos.le, inv_inv]
        dsimp [K]
        rw [abs_of_neg hν, h2, h3, inv_le_iff_one_le_mul₀' hp1]
        calc (1 : ℝ) = (1 + ‖z‖) ^ (-ν) * ((1 + ‖z‖) ^ (-ν))⁻¹ := (mul_inv_cancel₀ hp2.ne').symm
          _ ≤ ((1 + s) ^ (-ν) * (1 + ‖z + (s : ℂ)‖) ^ (-ν)) * ((1 + ‖z‖) ^ (-ν))⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hp2.le)
          _ = (1 + ‖z + (s : ℂ)‖) ^ (-ν) * ((1 + s) ^ (-ν) * ((1 + ‖z‖) ^ (-ν))⁻¹) := by ring
    have henv : airyEnv (z + (s : ℂ)) ≤ airyEnv z := by
      refine (airyEnv_add_real_le z s).trans ?_
      have hexp : Real.exp (-2 * s * airySqrtRe z) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [airySqrtRe_nonneg z])
      exact mul_le_of_le_one_right (airyEnv_pos z).le hexp
    calc ‖G (z + (s : ℂ))‖
        ≤ C * (1 + ‖z + (s : ℂ)‖) ^ ν * airyEnv (z + (s : ℂ)) := hb _
      _ ≤ C * (K * (1 + ‖z‖) ^ ν) * airyEnv z :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpoly hC) henv (airyEnv_pos _).le
            (mul_nonneg hC (mul_nonneg hK_nn (by positivity)))
      _ = (C * K) * (1 + ‖z‖) ^ ν * airyEnv z := by ring
  · intro x
    dsimp only
    have hcast : (x : ℂ) + (s : ℂ) = ((x + s : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast]
    exact hG.2.2.2 (x + s)

/-- Closure of `SchwartzMap ℝ ℝ` under real translation `u ↦ S (u + s)`. -/
theorem schwartz_shift (S : SchwartzMap ℝ ℝ) (s : ℝ) :
    ∃ S_s : SchwartzMap ℝ ℝ, ∀ u : ℝ, S_s u = S (u + s) := by
  refine ⟨{
    toFun := fun u => S (u + s)
    smooth' := (S.smooth (⊤ : ℕ∞)).comp (contDiff_id.add contDiff_const)
    decay' := fun k n => ?_
  }, fun _ => rfl⟩
  choose C hC_pos hC using fun j : ℕ => S.decay j n
  refine ⟨∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * |s| ^ (k - j) * C j, fun x => ?_⟩
  rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hiter : iteratedDeriv n (fun u : ℝ => S (u + s)) x = iteratedDeriv n S (x + s) := by
    have h := congrFun (iteratedDeriv_comp_add_const n (S : ℝ → ℝ) s) x
    exact h
  rw [hiter, Real.norm_eq_abs]
  have hbin : |x| ^ k ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * |x + s| ^ j * |s| ^ (k - j) := by
    calc |x| ^ k = |(x + s) - s| ^ k := by ring_nf
      _ ≤ (|x + s| + |s|) ^ k := pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) k
      _ = ∑ j ∈ Finset.range (k + 1), |x + s| ^ j * |s| ^ (k - j) * (k.choose j : ℝ) :=
          add_pow |x + s| |s| k
      _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * |x + s| ^ j * |s| ^ (k - j) := by
          refine Finset.sum_congr rfl fun j _ => by ring
  calc |x| ^ k * |iteratedDeriv n S (x + s)|
      ≤ (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * |x + s| ^ j * |s| ^ (k - j)) *
          |iteratedDeriv n S (x + s)| :=
        mul_le_mul_of_nonneg_right hbin (abs_nonneg _)
    _ = ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * |s| ^ (k - j) * (|x + s| ^ j * |iteratedDeriv n S (x + s)|) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * |s| ^ (k - j) * C j := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := hC j (x + s)
        rwa [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h

/-! ### Section 2: Smooth Regularization in the Airy Class (`lem:al-smooth`) -/

noncomputable def airyRawBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma integral_airyRawBump_pos : 0 < ∫ s : ℝ, airyRawBump s := by
  have hcont : Continuous airyRawBump := (airyRawBump.contDiff (n := (⊤ : ℕ∞))).continuous
  have hsupp : HasCompactSupport airyRawBump := airyRawBump.hasCompactSupport
  have hint : Integrable airyRawBump := hcont.integrable_of_hasCompactSupport hsupp
  have h1 : ∀ s ∈ Icc (-1 / 4 : ℝ) (1 / 4), (1 : ℝ) ≤ airyRawBump s := by
    intro s hs
    have hmem : s ∈ closedBall (0 : ℝ) airyRawBump.rIn := by
      change |s - 0| ≤ 1 / 4
      rw [sub_zero, abs_le]
      exact ⟨by linarith [hs.1], hs.2⟩
    rw [airyRawBump.one_of_mem_closedBall hmem]
  have hsub := setIntegral_mono_on (continuousOn_const.integrableOn_Icc) hint.integrableOn
    measurableSet_Icc h1
  have hval : (∫ _ in Icc (-1 / 4 : ℝ) (1 / 4), (1 : ℝ)) = 1 / 2 := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
    norm_num
  have hle_all : (∫ s in Icc (-1 / 4 : ℝ) (1 / 4), airyRawBump s) ≤ ∫ s : ℝ, airyRawBump s :=
    setIntegral_le_integral hint (Eventually.of_forall fun s => airyRawBump.nonneg' s)
  linarith

/-- Fixed normalized even smooth bump `φ ∈ C_c^∞(-1, 1)` (`supp φ ⊆ [-1/2, 1/2]`) with `φ ≥ 0`
and `∫_{-1}^1 φ = 1`. -/
noncomputable def airySmoothPhi (t : ℝ) : ℝ :=
  airyRawBump t / ∫ s : ℝ, airyRawBump s

lemma contDiff_airySmoothPhi : ContDiff ℝ (⊤ : ℕ∞) airySmoothPhi :=
  (airyRawBump.contDiff (n := (⊤ : ℕ∞))).div_const _

lemma airySmoothPhi_even (t : ℝ) : airySmoothPhi (-t) = airySmoothPhi t := by
  unfold airySmoothPhi
  rw [airyRawBump.neg]

lemma airySmoothPhi_nonneg (t : ℝ) : 0 ≤ airySmoothPhi t :=
  div_nonneg (airyRawBump.nonneg' t) integral_airyRawBump_pos.le

lemma airySmoothPhi_eq_zero_of_le_abs {t : ℝ} (ht : 1 / 2 ≤ |t|) : airySmoothPhi t = 0 := by
  have h0 : airyRawBump t = 0 := by
    by_contra hne
    have hmem : t ∈ Function.support airyRawBump := hne
    rw [airyRawBump.support_eq] at hmem
    change |t - 0| < 1 / 2 at hmem
    rw [sub_zero] at hmem
    linarith
  unfold airySmoothPhi
  rw [h0, zero_div]

lemma iteratedDeriv_airySmoothPhi_eq_zero_of_gt {t : ℝ} (ht : 1 / 2 < |t|) (m : ℕ) :
    iteratedDeriv m airySmoothPhi t = 0 := by
  have hev : airySmoothPhi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    have hopen : IsOpen {s : ℝ | 1 / 2 < |s|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact airySmoothPhi_eq_zero_of_le_abs (le_of_lt hs)
  rw [hev.iteratedDeriv_eq]
  rcases m with _ | m <;> simp

lemma integral_airySmoothPhi_univ : (∫ t : ℝ, airySmoothPhi t) = 1 := by
  unfold airySmoothPhi
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, mul_inv_cancel₀ integral_airyRawBump_pos.ne']

lemma intervalIntegral_airySmoothPhi : (∫ t in (-1 : ℝ)..1, airySmoothPhi t) = 1 := by
  have hsupp : Function.support airySmoothPhi ⊆ Ioc (-1 : ℝ) 1 := by
    intro t ht
    by_contra hnot
    apply ht
    apply airySmoothPhi_eq_zero_of_le_abs
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hnot
    rcases hnot with h1 | h2
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have heq : (∫ t in Ioc (-1 : ℝ) 1, airySmoothPhi t) = ∫ t : ℝ, airySmoothPhi t := by
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Ioc (-1 : ℝ) 1
    · exact indicator_of_mem ht _
    · rw [indicator_of_notMem ht]
      by_contra hne
      exact ht (hsupp (Ne.symm hne))
  rw [heq, integral_airySmoothPhi_univ]

/-- The entire cosine-cosh kernel `m_ε(z) = ∫_{-1}^1 φ(t) cosh(ε t √z) dt` (`(eq:al-smooth)`). -/
noncomputable def airySmoothM (ε : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) *
    Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))

/-- The squared multiplier `M_ε(z) = m_ε(z)^2` (`(eq:al-smooth)`). -/
noncomputable def airySmoothMSq (ε : ℝ) (z : ℂ) : ℂ :=
  airySmoothM ε z ^ 2

/-- The regularized Airy-class function `H_ε(z) = M_ε(z) H(z + 2ε)` (`(eq:al-smooth)`). -/
noncomputable def airySmoothReg (H : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  airySmoothMSq ε z * H (z + ((2 * ε : ℝ) : ℂ))

/-- Power series `∑' k, w^{2k} / (2k)! * z^k` equal to `cosh(w √z)` everywhere on `ℂ`. -/
noncomputable def airyCoshSeries (w : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, (((w ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * z ^ k)

lemma cosh_mul_cpow_half_eq_series (w : ℝ) (z : ℂ) :
    Complex.cosh ((w : ℂ) * z ^ (1 / 2 : ℂ)) = airyCoshSeries w z := by
  rw [Complex.cosh_eq_tsum, airyCoshSeries]
  congr 1; ext k
  have hpow : ((w : ℂ) * z ^ (1 / 2 : ℂ)) ^ (2 * k) = (w : ℂ) ^ (2 * k) * z ^ k := by
    rw [mul_pow, pow_mul (z ^ (1 / 2 : ℂ)) 2 k, cpow_half_sq]
  rw [hpow]
  push_cast
  ring

private lemma summable_cosh_majorant (R : ℝ) :
    Summable (fun k : ℕ => R ^ (2 * k) / ((2 * k)! : ℝ)) :=
  (Real.hasSum_cosh R).summable

private lemma norm_cosh_series_term_le {w : ℝ} {z : ℂ} {W Z : ℝ}
    (hw : |w| ≤ W) (hz : ‖z‖ ≤ Z) (hW : 0 ≤ W) (hZ : 0 ≤ Z) (k : ℕ) :
    ‖(((w ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * z ^ k)‖ ≤
      (W * (Z + 1)) ^ (2 * k) / ((2 * k)! : ℝ) := by
  have hfac : |((2 * k)! : ℝ)| = ((2 * k)! : ℝ) :=
    abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos (2 * k)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, abs_div, abs_pow, hfac]
  have hZ1 : Z ^ k ≤ (Z + 1) ^ (2 * k) := by
    calc Z ^ k ≤ (Z + 1) ^ k := pow_le_pow_left₀ hZ (by linarith) k
      _ ≤ (Z + 1) ^ (2 * k) := pow_le_pow_right₀ (by linarith) (by omega)
  have hmul : |w| ^ (2 * k) * ‖z‖ ^ k ≤ (W * (Z + 1)) ^ (2 * k) := by
    calc |w| ^ (2 * k) * ‖z‖ ^ k
        ≤ W ^ (2 * k) * Z ^ k :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hw _)
            (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity) (by positivity)
      _ ≤ W ^ (2 * k) * (Z + 1) ^ (2 * k) :=
          mul_le_mul_of_nonneg_left hZ1 (pow_nonneg hW _)
      _ = (W * (Z + 1)) ^ (2 * k) := (mul_pow _ _ _).symm
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hmul (Nat.cast_nonneg _)

private lemma differentiable_airyCoshSeries (w : ℝ) :
    Differentiable ℂ (airyCoshSeries w) := by
  intro z₀
  set Z : ℝ := ‖z₀‖ + 1
  have hU : IsOpen (ball (0 : ℂ) Z) := isOpen_ball
  have hdiffOn : DifferentiableOn ℂ (airyCoshSeries w) (ball (0 : ℂ) Z) := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_cosh_majorant (|w| * (Z + 1))) ?_ hU ?_
    · intro k; fun_prop
    · intro k z hz
      exact norm_cosh_series_term_le le_rfl (mem_ball_zero_iff.mp hz).le (abs_nonneg w)
        (by positivity) k
  exact hdiffOn.differentiableAt (hU.mem_nhds (by simp [Z]))

private lemma norm_deriv_airyCoshSeries_le {w : ℝ} {z : ℂ} {W Z : ℝ}
    (hw : |w| ≤ W) (hz : ‖z‖ ≤ Z) (hW : 0 ≤ W) (hZ : 0 ≤ Z) :
    ‖deriv (airyCoshSeries w) z‖ ≤ Real.cosh (W * (Z + 2)) := by
  have hsphere : ∀ ζ ∈ sphere z 1, ‖airyCoshSeries w ζ‖ ≤ Real.cosh (W * (Z + 2)) := by
    intro ζ hζ
    have hζ_le : ‖ζ‖ ≤ Z + 1 := by
      have h1 : ‖ζ - z‖ = 1 := mem_sphere_iff_norm.mp hζ
      calc ‖ζ‖ = ‖(ζ - z) + z‖ := by ring_nf
        _ ≤ ‖ζ - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 + Z := by linarith
        _ = Z + 1 := add_comm _ _
    have hsum_maj := summable_cosh_majorant (W * ((Z + 1) + 1))
    calc ‖airyCoshSeries w ζ‖
        ≤ ∑' k : ℕ, ‖(((w ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * ζ ^ k)‖ :=
          norm_tsum_le_tsum_norm (hsum_maj.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun k => norm_cosh_series_term_le hw hζ_le hW (by linarith) k))
      _ ≤ ∑' k : ℕ, (W * ((Z + 1) + 1)) ^ (2 * k) / ((2 * k)! : ℝ) :=
          Summable.tsum_le_tsum
            (fun k => norm_cosh_series_term_le hw hζ_le hW (by linarith) k)
            (hsum_maj.of_nonneg_of_le (fun _ => norm_nonneg _)
              (fun k => norm_cosh_series_term_le hw hζ_le hW (by linarith) k))
            hsum_maj
      _ = Real.cosh (W * (Z + 2)) := by
          rw [show (Z + 1) + 1 = Z + 2 by ring, ← Real.cosh_eq_tsum]
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 zero_lt_one
    (differentiable_airyCoshSeries w).differentiableOn.diffContOnCl hsphere
  simpa using hc

private lemma continuous_uncurry_airyCoshSeries :
    Continuous (fun p : ℝ × ℂ => airyCoshSeries p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro ⟨w₀, z₀⟩
  set W : ℝ := |w₀| + 1
  set Z : ℝ := ‖z₀‖ + 1
  let U : Set (ℝ × ℂ) := ball (w₀, z₀) 1
  have hU_open : IsOpen U := isOpen_ball
  have hmem : (w₀, z₀) ∈ U := mem_ball_self zero_lt_one
  have hbd : ∀ k : ℕ, ∀ p ∈ U,
      ‖(((p.1 ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * p.2 ^ k)‖ ≤
        (W * (Z + 1)) ^ (2 * k) / ((2 * k)! : ℝ) := by
    intro k ⟨w, z⟩ hp
    have hmax : max (dist w w₀) (dist z z₀) < 1 := by simpa [U, Prod.dist_eq] using hp
    have h1 : dist w w₀ < 1 := lt_of_le_of_lt (le_max_left _ _) hmax
    have h2 : dist z z₀ < 1 := lt_of_le_of_lt (le_max_right _ _) hmax
    have hw : |w| ≤ W := by
      rw [Real.dist_eq] at h1
      calc |w| = |(w - w₀) + w₀| := by ring_nf
        _ ≤ |w - w₀| + |w₀| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; linarith
    have hz : ‖z‖ ≤ Z := by
      rw [dist_eq_norm] at h2
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ Z := by dsimp [Z]; linarith
    exact norm_cosh_series_term_le hw hz (by positivity) (by positivity) k
  have hcontOn : ContinuousOn (fun p : ℝ × ℂ => airyCoshSeries p.1 p.2) U := by
    refine (tendstoUniformlyOn_tsum (summable_cosh_majorant (W * (Z + 1))) hbd).continuousOn ?_
    refine Frequently.of_forall fun s => Continuous.continuousOn ?_
    classical
    induction s using Finset.induction_on with
    | empty => simp [continuous_const]
    | insert k s hk ih =>
      simp_rw [Finset.sum_insert hk]
      exact ((Complex.continuous_ofReal.comp ((continuous_fst.pow (2 * k)).div_const _)).mul
        (continuous_snd.pow k)).add ih
  exact hcontOn.continuousAt (hU_open.mem_nhds hmem)

lemma airySmoothM_eq_series_integral (ε : ℝ) (z : ℂ) :
    airySmoothM ε z = ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z := by
  unfold airySmoothM
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [cosh_mul_cpow_half_eq_series]

theorem differentiable_airySmoothM (ε : ℝ) : Differentiable ℂ (airySmoothM ε) := by
  have hfun : airySmoothM ε = fun z =>
      ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z :=
    funext (airySmoothM_eq_series_integral ε)
  rw [hfun]
  intro z₀
  set Z : ℝ := ‖z₀‖ + 1
  set W : ℝ := |ε|
  have hcont_phi : Continuous (fun t : ℝ => (airySmoothPhi t : ℂ)) :=
    Complex.continuous_ofReal.comp contDiff_airySmoothPhi.continuous
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hcont_phi.continuousOn
  set B : ℝ := max Mφ 0 * Real.cosh (W * (Z + 2))
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable
      (fun t : ℝ => (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    refine Eventually.of_forall fun z => ?_
    refine Continuous.aestronglyMeasurable ?_
    exact hcont_phi.mul (continuous_uncurry_airyCoshSeries.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const))
  have hF_int : IntervalIntegrable
      (fun t : ℝ => (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z₀) volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact hcont_phi.mul (continuous_uncurry_airyCoshSeries.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const))
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => (airySmoothPhi t : ℂ) * deriv (airyCoshSeries (ε * t)) z₀)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    let δ_seq : ℕ → ℂ := fun n => (((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
    have hlim : ∀ t : ℝ, Tendsto (fun n : ℕ =>
        (airySmoothPhi t : ℂ) * ((airyCoshSeries (ε * t) (z₀ + δ_seq n) -
          airyCoshSeries (ε * t) z₀) / δ_seq n)) atTop
        (𝓝 ((airySmoothPhi t : ℂ) * deriv (airyCoshSeries (ε * t)) z₀)) := by
      intro t
      refine Filter.Tendsto.const_mul _ ?_
      have hd := (differentiable_airyCoshSeries (ε * t) z₀).hasDerivAt
      have hseq : Tendsto δ_seq atTop (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
            tendsto_inv_atTop_zero.comp
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          exact ((Complex.continuous_ofReal.tendsto 0).comp hr).congr fun _ => rfl
        · rw [mem_compl_singleton_iff]
          exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (by positivity))
      have hsl := hd.tendsto_slope_zero.comp hseq
      refine hsl.congr fun n => ?_
      dsimp only [Function.comp_def]
      rw [smul_eq_mul, div_eq_inv_mul]
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => ?_) (Eventually.of_forall hlim)
    refine Continuous.aestronglyMeasurable ?_
    exact hcont_phi.mul (((continuous_uncurry_airyCoshSeries.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const)).sub
      (continuous_uncurry_airyCoshSeries.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const))).div_const _)
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ z ∈ ball z₀ 1,
      ‖(airySmoothPhi t : ℂ) * deriv (airyCoshSeries (ε * t)) z‖ ≤ B := by
    refine Eventually.of_forall fun t ht z hz => ?_
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hw : |ε * t| ≤ W := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg ε) ht_abs
    have hz_le : ‖z‖ ≤ Z := by
      have h1 : ‖z - z₀‖ < 1 := mem_ball_iff_norm.mp hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ Z := by dsimp [Z]; linarith
    have hphi_le : ‖(airySmoothPhi t : ℂ)‖ ≤ max Mφ 0 :=
      (hMφ t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _)
    rw [norm_mul]
    exact mul_le_mul hphi_le (norm_deriv_airyCoshSeries_le hw hz_le (abs_nonneg ε) (by positivity))
      (norm_nonneg _) (le_max_right _ _)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z₀ zero_lt_one) hF_meas hF_int hF'_meas h_bound
    intervalIntegrable_const
    (Eventually.of_forall fun t _ z _ =>
      ((differentiable_airyCoshSeries (ε * t) z).hasDerivAt.const_mul _))).2.differentiableAt

theorem differentiable_airySmoothMSq (ε : ℝ) : Differentiable ℂ (airySmoothMSq ε) :=
  (differentiable_airySmoothM ε).pow 2

lemma continuous_uncurry_airySmoothM :
    Continuous (fun p : ℝ × ℂ => airySmoothM p.1 p.2) := by
  have hfun : (fun p : ℝ × ℂ => airySmoothM p.1 p.2) = fun p : ℝ × ℂ =>
      ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (p.1 * t) p.2 :=
    funext fun p => airySmoothM_eq_series_integral p.1 p.2
  rw [hfun]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ (-1) 1
  exact (Complex.continuous_ofReal.comp (contDiff_airySmoothPhi.continuous.comp continuous_snd)).mul
    (continuous_uncurry_airyCoshSeries.comp
      ((continuous_fst.fst.mul continuous_snd).prodMk continuous_fst.snd))

lemma airySmoothM_zero (z : ℂ) : airySmoothM 0 z = 1 := by
  unfold airySmoothM
  have hcongr : (∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) *
      Complex.cosh (((0 * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))) =
      ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  rw [hcongr, intervalIntegral.integral_ofReal, intervalIntegral_airySmoothPhi, Complex.ofReal_one]

lemma airySmoothMSq_zero (z : ℂ) : airySmoothMSq 0 z = 1 := by
  simp [airySmoothMSq, airySmoothM_zero]

lemma airySmoothM_ofReal_im (ε u : ℝ) : (airySmoothM ε (u : ℂ)).im = 0 := by
  rw [airySmoothM_eq_series_integral]
  have hreal : ∀ t : ℝ, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) (u : ℂ) =
      ((airySmoothPhi t * ∑' k : ℕ, ((ε * t) ^ (2 * k) / (2 * k)!) * u ^ k : ℝ) : ℂ) := by
    intro t
    unfold airyCoshSeries
    rw [Complex.ofReal_mul, Complex.ofReal_tsum]
    simp
  have hc : (∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) (u : ℂ)) =
      ∫ t in (-1 : ℝ)..1,
        ((airySmoothPhi t * ∑' k : ℕ, ((ε * t) ^ (2 * k) / (2 * k)!) * u ^ k : ℝ) : ℂ) :=
    intervalIntegral.integral_congr fun t _ => hreal t
  rw [hc, intervalIntegral.integral_ofReal, Complex.ofReal_im]

lemma airySmoothMSq_ofReal_im_and_nonneg (ε u : ℝ) :
    (airySmoothMSq ε (u : ℂ)).im = 0 ∧ 0 ≤ (airySmoothMSq ε (u : ℂ)).re := by
  have him := airySmoothM_ofReal_im ε u
  have heq : airySmoothM ε (u : ℂ) = ((airySmoothM ε (u : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  unfold airySmoothMSq
  rw [heq, ← Complex.ofReal_pow]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact sq_nonneg _⟩

private lemma norm_cosh_le_exp_abs_re (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.cosh]
  have h1 : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp z
  have h2 : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by rw [Complex.norm_exp, Complex.neg_re]
  have he1 : Real.exp z.re ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (le_abs_self _)
  have he2 : Real.exp (-z.re) ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(Complex.exp z + Complex.exp (-z)) / 2‖
      = ‖Complex.exp z + Complex.exp (-z)‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
    _ ≤ (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (Real.exp z.re + Real.exp (-z.re)) / 2 := by rw [h1, h2]
    _ ≤ Real.exp |z.re| := by linarith

lemma norm_airySmoothM_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖airySmoothM ε z‖ ≤ Real.exp (ε * airySqrtRe z) := by
  unfold airySmoothM
  have hcont : Continuous (fun t : ℝ =>
      ‖(airySmoothPhi t : ℂ) * Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖) := by
    refine Continuous.norm ?_
    exact (Complex.continuous_ofReal.comp contDiff_airySmoothPhi.continuous).mul
      (Complex.continuous_cosh.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)).mul continuous_const))
  have hpt : ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖(airySmoothPhi t : ℂ) * Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖ ≤
        airySmoothPhi t * Real.exp (ε * airySqrtRe z) := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (airySmoothPhi_nonneg t)]
    refine mul_le_mul_of_nonneg_left ?_ (airySmoothPhi_nonneg t)
    refine (norm_cosh_le_exp_abs_re _).trans (Real.exp_le_exp.mpr ?_)
    have hre : (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ)).re = ε * t * airySqrtRe z := by
      simp [airySqrtRe, Complex.mul_re]
    rw [hre, abs_mul, abs_mul, abs_of_nonneg hε, abs_of_nonneg (airySqrtRe_nonneg z)]
    have ht_abs : |t| ≤ 1 := abs_le.mpr ht
    calc ε * |t| * airySqrtRe z
        ≤ ε * 1 * airySqrtRe z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_abs hε) (airySqrtRe_nonneg z)
      _ = ε * airySqrtRe z := by ring
  calc ‖∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) *
        Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖
      ≤ ∫ t in (-1 : ℝ)..1, ‖(airySmoothPhi t : ℂ) *
          Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (-1 : ℝ)..1, airySmoothPhi t * Real.exp (ε * airySqrtRe z) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hcont.intervalIntegrable _ _)
          ((contDiff_airySmoothPhi.continuous.mul continuous_const).intervalIntegrable _ _)
          hpt
    _ = (∫ t in (-1 : ℝ)..1, airySmoothPhi t) * Real.exp (ε * airySqrtRe z) :=
        intervalIntegral.integral_mul_const _ _
    _ = Real.exp (ε * airySqrtRe z) := by rw [intervalIntegral_airySmoothPhi, one_mul]

lemma norm_airySmoothMSq_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖airySmoothMSq ε z‖ ≤ Real.exp (2 * ε * airySqrtRe z) := by
  unfold airySmoothMSq
  rw [norm_pow]
  calc ‖airySmoothM ε z‖ ^ 2
      ≤ (Real.exp (ε * airySqrtRe z)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_airySmoothM_le hε z) 2
    _ = Real.exp (2 * ε * airySqrtRe z) := by
        rw [sq, ← Real.exp_add]; congr 1; ring

lemma airySqrtRe_ofReal_nonpos {u : ℝ} (hu : u ≤ 0) : airySqrtRe (u : ℂ) = 0 := by
  have h1 := airySqrtRe_sq_sub (u : ℂ)
  have h2 := airySqrtRe_mul_im (u : ℂ)
  simp only [Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  rcases mul_eq_zero.mp h2 with h0 | him0
  · linarith
  · rw [him0] at h1
    have : airySqrtRe (u : ℂ) ^ 2 ≤ 0 := by linarith
    nlinarith [sq_nonneg (airySqrtRe (u : ℂ))]

lemma norm_airySmoothMSq_neg_le_one {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    ‖airySmoothMSq ε ((-x : ℝ) : ℂ)‖ ≤ 1 := by
  refine (norm_airySmoothMSq_le hε ((-x : ℝ) : ℂ)).trans ?_
  rw [airySqrtRe_ofReal_nonpos (by linarith), mul_zero, Real.exp_zero]

/-- Two-step integration by parts on `[-1, 1]` for any `ψ ∈ C^∞` vanishing near `±1`:
`∫_{-1}^1 ψ''(t) cosh(w t) dt = w^2 ∫_{-1}^1 ψ(t) cosh(w t) dt`. -/
private lemma cosh_ibp_two {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hvan : ∀ j : ℕ, iteratedDeriv j ψ (-1) = 0 ∧ iteratedDeriv j ψ 1 = 0) (w : ℂ) :
    (∫ t in (-1 : ℝ)..1, ((iteratedDeriv 2 ψ t : ℝ) : ℂ) * Complex.cosh (w * (t : ℂ))) =
      w ^ 2 * ∫ t in (-1 : ℝ)..1, (ψ t : ℂ) * Complex.cosh (w * (t : ℂ)) := by
  have hd0 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (ψ s : ℂ)) ((deriv ψ t : ℝ) : ℂ) t := fun t =>
    ((hψ.differentiable (by simp) t).hasDerivAt).ofReal_comp
  have hd1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((deriv ψ s : ℝ) : ℂ))
      ((iteratedDeriv 2 ψ t : ℝ) : ℂ) t := fun t => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := hψ.iterate_deriv 1
    exact ((hcd1.differentiable (by simp) t).hasDerivAt).ofReal_comp
  have hcosh : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.cosh (w * (s : ℂ)))
      (w * Complex.sinh (w * (t : ℂ))) t := fun t => by
    have hc : HasDerivAt (fun z : ℂ => Complex.cosh (w * z))
        (Complex.sinh (w * (t : ℂ)) * w) (t : ℂ) :=
      (Complex.hasDerivAt_cosh (w * (t : ℂ))).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_mul w)
    exact (hc.congr_deriv (mul_comm _ _)).comp_ofReal
  have hsinh : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.sinh (w * (s : ℂ)))
      (w * Complex.cosh (w * (t : ℂ))) t := fun t => by
    have hc : HasDerivAt (fun z : ℂ => Complex.sinh (w * z))
        (Complex.cosh (w * (t : ℂ)) * w) (t : ℂ) :=
      (Complex.hasDerivAt_sinh (w * (t : ℂ))).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_mul w)
    exact (hc.congr_deriv (mul_comm _ _)).comp_ofReal
  have hcd_d1 : Continuous (deriv ψ) := (hψ.iterate_deriv 1).continuous
  have hcd_d2 : Continuous (iteratedDeriv 2 ψ) := by
    simpa [iteratedDeriv_eq_iterate] using (hψ.iterate_deriv 2).continuous
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -1) (b := 1)
    (u := fun t => Complex.cosh (w * (t : ℂ)))
    (u' := fun t => w * Complex.sinh (w * (t : ℂ)))
    (v := fun t => ((deriv ψ t : ℝ) : ℂ))
    (v' := fun t => ((iteratedDeriv 2 ψ t : ℝ) : ℂ))
    (fun t _ => hcosh t) (fun t _ => hd1 t)
    ((continuous_const.mul (Complex.continuous_sinh.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _)
    ((Complex.continuous_ofReal.comp hcd_d2).intervalIntegrable _ _)
  have hb1_1 : deriv ψ 1 = 0 := by rw [← iteratedDeriv_one]; exact (hvan 1).2
  have hb1_m1 : deriv ψ (-1) = 0 := by rw [← iteratedDeriv_one]; exact (hvan 1).1
  simp only [hb1_1, hb1_m1, Complex.ofReal_zero, mul_zero, sub_zero, zero_sub] at hibp1
  have hibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -1) (b := 1)
    (u := fun t => Complex.sinh (w * (t : ℂ)))
    (u' := fun t => w * Complex.cosh (w * (t : ℂ)))
    (v := fun t => (ψ t : ℂ))
    (v' := fun t => ((deriv ψ t : ℝ) : ℂ))
    (fun t _ => hsinh t) (fun t _ => hd0 t)
    ((continuous_const.mul (Complex.continuous_cosh.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _)
    ((Complex.continuous_ofReal.comp hcd_d1).intervalIntegrable _ _)
  have hb0_1 : ψ 1 = 0 := by rw [← iteratedDeriv_zero]; exact (hvan 0).2
  have hb0_m1 : ψ (-1) = 0 := by rw [← iteratedDeriv_zero]; exact (hvan 0).1
  simp only [hb0_1, hb0_m1, Complex.ofReal_zero, mul_zero, sub_zero, zero_sub] at hibp2
  calc (∫ t in (-1 : ℝ)..1, ((iteratedDeriv 2 ψ t : ℝ) : ℂ) * Complex.cosh (w * (t : ℂ)))
      = ∫ t in (-1 : ℝ)..1, Complex.cosh (w * (t : ℂ)) * ((iteratedDeriv 2 ψ t : ℝ) : ℂ) := by
          refine intervalIntegral.integral_congr fun t _ => mul_comm _ _
    _ = -∫ t in (-1 : ℝ)..1, w * Complex.sinh (w * (t : ℂ)) * ((deriv ψ t : ℝ) : ℂ) := hibp1
    _ = -w * ∫ t in (-1 : ℝ)..1, Complex.sinh (w * (t : ℂ)) * ((deriv ψ t : ℝ) : ℂ) := by
          simp_rw [mul_assoc]; rw [intervalIntegral.integral_const_mul, neg_mul]
    _ = -w * (-∫ t in (-1 : ℝ)..1, w * Complex.cosh (w * (t : ℂ)) * (ψ t : ℂ)) := by
          rw [hibp2]
    _ = w ^ 2 * ∫ t in (-1 : ℝ)..1, (ψ t : ℂ) * Complex.cosh (w * (t : ℂ)) := by
          have hmul : (∫ t in (-1 : ℝ)..1, w * Complex.cosh (w * (t : ℂ)) * (ψ t : ℂ)) =
              w * ∫ t in (-1 : ℝ)..1, (ψ t : ℂ) * Complex.cosh (w * (t : ℂ)) := by
            have hc : ∀ t : ℝ, w * Complex.cosh (w * (t : ℂ)) * (ψ t : ℂ) =
                w * ((ψ t : ℂ) * Complex.cosh (w * (t : ℂ))) := fun t => by ring
            simp_rw [hc]
            exact intervalIntegral.integral_const_mul _ _
          rw [hmul]; ring

private lemma iteratedDeriv_comp_iteratedDeriv (j k : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv j (iteratedDeriv k f) x = iteratedDeriv (j + k) f x := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

private lemma airySmoothM_ibp_iter (ε : ℝ) (z : ℂ) (m : ℕ) :
    (((ε : ℂ) ^ 2 * z) ^ m) * airySmoothM ε z =
      ∫ t in (-1 : ℝ)..1, ((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
        Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ)) := by
  set w : ℂ := (ε : ℂ) * z ^ (1 / 2 : ℂ)
  have hw2 : w ^ 2 = (ε : ℂ) ^ 2 * z := by
    dsimp [w]; rw [mul_pow, cpow_half_sq]
  have harg : ∀ t : ℝ, ((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ) = w * (t : ℂ) := fun t => by
    dsimp [w]; push_cast; ring
  unfold airySmoothM
  simp_rw [harg, ← hw2, ← pow_mul]
  induction m with
  | zero => simp
  | succ m ih =>
    have hcd_m : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv (2 * m) airySmoothPhi) := by
      rw [iteratedDeriv_eq_iterate]
      exact contDiff_airySmoothPhi.iterate_deriv (2 * m)
    have hstep := cosh_ibp_two (ψ := iteratedDeriv (2 * m) airySmoothPhi) hcd_m
      (fun j => by
        rw [iteratedDeriv_comp_iteratedDeriv, iteratedDeriv_comp_iteratedDeriv]
        exact ⟨iteratedDeriv_airySmoothPhi_eq_zero_of_gt (by norm_num) _,
          iteratedDeriv_airySmoothPhi_eq_zero_of_gt (by norm_num) _⟩)
      w
    have hiter : ∀ t : ℝ, iteratedDeriv 2 (iteratedDeriv (2 * m) airySmoothPhi) t =
        iteratedDeriv (2 * (m + 1)) airySmoothPhi t := fun t => by
      rw [iteratedDeriv_comp_iteratedDeriv, show 2 + 2 * m = 2 * (m + 1) by omega]
    simp_rw [hiter] at hstep
    rw [hstep, ← ih, ← mul_assoc, ← pow_add, show 2 + 2 * m = 2 * (m + 1) by omega]

/-- Uniform polynomial-decay bound on `‖airySmoothMSq ε ζ‖` on any circle `sphere (u : ℂ) r`
(`0 < r ≤ 1`) around `u ≤ -4`. -/
lemma norm_airySmoothMSq_le_on_neg_sphere {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1) (m : ℕ) :
    ∃ C_m : ℝ, 0 ≤ C_m ∧ ∀ {u r : ℝ}, u ≤ -4 → 0 < r → r ≤ 1 →
      ∀ ζ ∈ sphere (u : ℂ) r, ‖airySmoothMSq ε ζ‖ ≤ C_m * (|u|⁻¹) ^ (2 * m) := by
  have hcont_phi_m : Continuous (iteratedDeriv (2 * m) airySmoothPhi) := by
    rw [iteratedDeriv_eq_iterate]
    exact (contDiff_airySmoothPhi.iterate_deriv (2 * m)).continuous
  obtain ⟨Bφ, hBφ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hcont_phi_m.continuousOn
  set Kφ : ℝ := 2 * max Bφ 0 * Real.exp 1
  refine ⟨(Kφ * (2 / ε ^ 2) ^ m) ^ 2, sq_nonneg _, fun {u r} hu _hr0 hr1 ζ hζ => ?_⟩
  have h_abs_u : 4 ≤ |u| := by rw [abs_of_neg (by linarith)]; linarith
  have hnorm_sub : ‖ζ - (u : ℂ)‖ = r := mem_sphere_iff_norm.mp hζ
  have hζ_re : ζ.re ≤ -3 := by
    have h1 := Complex.abs_re_le_norm (ζ - (u : ℂ))
    rw [hnorm_sub, Complex.sub_re, Complex.ofReal_re] at h1
    linarith [(abs_le.mp h1).2]
  have hζ_im : |ζ.im| ≤ 1 := by
    have h1 := Complex.abs_im_le_norm (ζ - (u : ℂ))
    rw [hnorm_sub, Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
    exact h1.trans hr1
  have ha_le : airySqrtRe ζ ≤ 1 / 2 := by
    have h1 := airySqrtRe_sq_sub ζ
    have h2 := airySqrtRe_mul_im ζ
    have hb_ge : 1 ≤ |(ζ ^ (1 / 2 : ℂ)).im| := by
      have : 1 ≤ (ζ ^ (1 / 2 : ℂ)).im ^ 2 := by nlinarith [sq_nonneg (airySqrtRe ζ)]
      nlinarith [sq_abs (ζ ^ (1 / 2 : ℂ)).im, abs_nonneg (ζ ^ (1 / 2 : ℂ)).im]
    have hmul : 2 * airySqrtRe ζ * |(ζ ^ (1 / 2 : ℂ)).im| ≤ 1 := by
      calc 2 * airySqrtRe ζ * |(ζ ^ (1 / 2 : ℂ)).im|
          = |2 * airySqrtRe ζ * (ζ ^ (1 / 2 : ℂ)).im| := by
            rw [abs_mul, abs_mul, Nat.abs_ofNat, abs_of_nonneg (airySqrtRe_nonneg ζ)]
        _ = |ζ.im| := by rw [h2]
        _ ≤ 1 := hζ_im
    nlinarith [airySqrtRe_nonneg ζ]
  have hζ_norm_ge : |u| / 2 ≤ ‖ζ‖ := by
    have htri : |(u : ℂ).re| ≤ ‖ζ - (u : ℂ)‖ + ‖ζ‖ := by
      calc |(u : ℂ).re| ≤ ‖(u : ℂ)‖ := Complex.abs_re_le_norm _
        _ = ‖(u : ℂ) - ζ + ζ‖ := by ring_nf
        _ ≤ ‖(u : ℂ) - ζ‖ + ‖ζ‖ := norm_add_le _ _
        _ = ‖ζ - (u : ℂ)‖ + ‖ζ‖ := by rw [norm_sub_rev]
    rw [Complex.ofReal_re, hnorm_sub] at htri
    linarith
  have hibp := airySmoothM_ibp_iter ε ζ m
  have hint_le : ‖∫ t in (-1 : ℝ)..1, ((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
      Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖ ≤ Kφ := by
    calc ‖∫ t in (-1 : ℝ)..1, ((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
          Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖
        ≤ ∫ t in (-1 : ℝ)..1, ‖((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
            Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ _ in (-1 : ℝ)..1, max Bφ 0 * Real.exp 1 := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const
            fun t ht => ?_
          · refine Continuous.intervalIntegrable (Continuous.norm ?_) _ _
            exact (Complex.continuous_ofReal.comp hcont_phi_m).mul
              (Complex.continuous_cosh.comp ((Complex.continuous_ofReal.comp
                (continuous_const.mul continuous_id)).mul continuous_const))
          · rw [norm_mul, Complex.norm_real]
            have hphi_b : ‖iteratedDeriv (2 * m) airySmoothPhi t‖ ≤ max Bφ 0 :=
              (hBφ t ht).trans (le_max_left _ _)
            have hcosh_b : ‖Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖ ≤ Real.exp 1 := by
              refine (norm_cosh_le_exp_abs_re _).trans (Real.exp_le_exp.mpr ?_)
              have hre : (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ)).re = ε * t * airySqrtRe ζ := by
                simp [airySqrtRe, Complex.mul_re]
              rw [hre, abs_mul, abs_mul, abs_of_pos hε, abs_of_nonneg (airySqrtRe_nonneg ζ)]
              have ht_abs : |t| ≤ 1 := abs_le.mpr ht
              have hεt : ε * |t| ≤ 1 := by nlinarith [abs_nonneg t]
              nlinarith [airySqrtRe_nonneg ζ]
            exact mul_le_mul hphi_b hcosh_b (norm_nonneg _) (le_max_right _ _)
      _ = Kφ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          dsimp [Kφ]; ring
  have hM_le : ‖airySmoothM ε ζ‖ ≤ (Kφ * (2 / ε ^ 2) ^ m) * (|u|⁻¹) ^ m := by
    have h1 : ((ε ^ 2 * (|u| / 2)) ^ m) * ‖airySmoothM ε ζ‖ ≤ Kφ := by
      calc ((ε ^ 2 * (|u| / 2)) ^ m) * ‖airySmoothM ε ζ‖
          ≤ ((ε ^ 2 * ‖ζ‖) ^ m) * ‖airySmoothM ε ζ‖ :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (by positivity)
                (mul_le_mul_of_nonneg_left hζ_norm_ge (sq_nonneg ε)) m)
              (norm_nonneg _)
        _ = ‖(((ε : ℂ) ^ 2 * ζ) ^ m) * airySmoothM ε ζ‖ := by
            rw [norm_mul, norm_pow, norm_mul, norm_pow, Complex.norm_real,
              Real.norm_eq_abs, sq_abs]
        _ ≤ Kφ := by rw [hibp]; exact hint_le
    have hpos : 0 < (ε ^ 2 * (|u| / 2)) ^ m := pow_pos (by positivity) m
    have hinv : ((ε ^ 2 * (|u| / 2)) ^ m)⁻¹ = (2 / ε ^ 2) ^ m * (|u|⁻¹) ^ m := by
      rw [← inv_pow, ← mul_pow]; congr 1
      field_simp [hε.ne', (by linarith : |u| ≠ 0)]
    rw [← le_div_iff₀' hpos, div_eq_mul_inv, hinv] at h1
    exact le_trans h1 (le_of_eq (by ring))
  unfold airySmoothMSq
  rw [norm_pow]
  calc ‖airySmoothM ε ζ‖ ^ 2
      ≤ ((Kφ * (2 / ε ^ 2) ^ m) * (|u|⁻¹) ^ m) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hM_le 2
    _ = (Kφ * (2 / ε ^ 2) ^ m) ^ 2 * (|u|⁻¹) ^ (2 * m) := by
        rw [mul_pow, ← pow_mul, mul_comm m 2]

/-- Rapid decay of `M_ε(u)` and all its derivatives on `(-∞, 0]`. -/
theorem airySmoothMSq_neg_rapid_decay {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u ≤ 0 →
      |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u| ≤ C := by
  have hcont_iter := (contDiff_re_of_differentiable (differentiable_airySmoothMSq ε)).2 n
  have hcont_d : Continuous (fun u : ℝ =>
      |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u|) :=
    (continuous_abs.pow k).mul (continuous_abs.comp hcont_iter)
  obtain ⟨M_loc, hM_loc⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-4 : ℝ) 0) hcont_d.continuousOn
  obtain ⟨C_k, hCk_nn, hCk⟩ := norm_airySmoothMSq_le_on_neg_sphere hε hε1 k
  refine ⟨max (max M_loc 0) (n.factorial * C_k), by positivity, fun u hu => ?_⟩
  by_cases hu4 : -4 ≤ u
  · have h1 := hM_loc u ⟨hu4, hu⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    exact h1.trans ((le_max_left M_loc 0).trans (le_max_left _ _))
  · push Not at hu4
    have hu_abs : 4 < |u| := by rw [abs_of_neg (by linarith)]; linarith
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n zero_lt_one
      (differentiable_airySmoothMSq ε).differentiableOn.diffContOnCl
      (fun ζ hζ => hCk hu4.le zero_lt_one le_rfl ζ hζ)
    rw [one_pow, div_one] at hcauchy
    have hderiv_le : |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u| ≤
        n.factorial * (C_k * (|u|⁻¹) ^ (2 * k)) := by
      rw [iteratedDeriv_re_of_differentiable (differentiable_airySmoothMSq ε)]
      exact (Complex.abs_re_le_norm _).trans hcauchy
    have hpow_le : |u| ^ k * (|u|⁻¹) ^ (2 * k) ≤ 1 := by
      rw [show 2 * k = k + k by omega, pow_add, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ (by linarith), one_pow, one_mul]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
    calc |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u|
        ≤ |u| ^ k * (n.factorial * (C_k * (|u|⁻¹) ^ (2 * k))) :=
          mul_le_mul_of_nonneg_left hderiv_le (by positivity)
      _ = (n.factorial * C_k) * (|u| ^ k * (|u|⁻¹) ^ (2 * k)) := by ring
      _ ≤ (n.factorial * C_k) * 1 :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
      _ ≤ max (max M_loc 0) (n.factorial * C_k) := by rw [mul_one]; exact le_max_right _ _

private lemma pow_mul_exp_neg_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ N * Real.exp (-x) ≤ N.factorial := by
  have hterm : x ^ N / (N.factorial : ℝ) ≤ Real.exp x := by
    rw [Real.exp_eq_exp_ℝ]
    have hsum := NormedSpace.expSeries_div_hasSum_exp x
    have h := Summable.le_tsum hsum.summable N (fun k _ => by positivity)
    simpa [← hsum.tsum_eq] using h
  have hfac_pos : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  rw [div_le_iff₀ hfac_pos] at hterm
  calc x ^ N * Real.exp (-x)
      ≤ (Real.exp x * N.factorial) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_pos _).le
    _ = N.factorial * (Real.exp x * Real.exp (-x)) := by ring
    _ = N.factorial := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- **Lemma `lem:al-smooth`** (`ce_airy_lp_proofs.tex` lines 47–77):
smooth regularization `H_ε(z) = M_ε(z) H(z + 2ε)` inside `𝒢 ∩ 𝓢(ℝ)`. -/
theorem lem_al_smooth {H : ℂ → ℂ} (hH : InAiryClass H) :
    (∀ ε ∈ Ioc (0 : ℝ) 1,
      Differentiable ℂ (airySmoothMSq ε) ∧
      (∀ u : ℝ, (airySmoothMSq ε (u : ℂ)).im = 0 ∧ 0 ≤ (airySmoothMSq ε (u : ℂ)).re) ∧
      (∀ x : ℝ, 0 ≤ x → ‖airySmoothMSq ε ((-x : ℝ) : ℂ)‖ ≤ 1) ∧
      (∀ z : ℂ, ‖airySmoothMSq ε z‖ ≤ Real.exp (2 * ε * airySqrtRe z)) ∧
      InAiryClass (airySmoothReg H ε) ∧
      ((∀ u : ℝ, (H (u : ℂ)).im = 0) → ∀ u : ℝ, (airySmoothReg H ε (u : ℂ)).im = 0) ∧
      ∃ S_ε : SchwartzMap ℝ ℝ, ∀ u : ℝ, S_ε u = (airySmoothReg H ε (u : ℂ)).re) ∧
    TendstoLocallyUniformly (fun ε z => airySmoothReg H ε z) H (𝓝[>] 0) ∧
    (∀ Y : ℝ, 0 ≤ Y →
      Tendsto (fun ε : ℝ =>
        ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
        (𝓝[>] 0) (𝓝 0)) ∧
    ∃ C_H : ℝ, 0 ≤ C_H ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1, (∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖) ≤ C_H) ∧
      ∀ s : ℝ, 0 < s → ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ y : ℝ, 0 ≤ y →
        |airyLaplace (fun u => (airySmoothReg H ε ((u + s : ℝ) : ℂ)).re) y| ≤
          C_H * Real.exp (-s * y) := by
  obtain ⟨C₀, ν₀, hC₀_nn, hb₀⟩ := hH.2.2.1
  -- Envelope + polynomial growth bound for `airySmoothReg H ε` uniform in `ε ∈ [0, 1]`.
  set K_shift : ℝ := 3 ^ |ν₀|
  have hK_pos : 0 < K_shift := by positivity
  have hReg_diff : ∀ ε : ℝ, Differentiable ℂ (airySmoothReg H ε) := fun ε =>
    (differentiable_airySmoothMSq ε).mul (hH.1.comp (differentiable_id.add (differentiable_const _)))
  have hReg_growth : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ z : ℂ,
      ‖airySmoothReg H ε z‖ ≤ (C₀ * K_shift) * (1 + ‖z‖) ^ ν₀ * airyEnv z := by
    intro ε hε0 hε1 z
    unfold airySmoothReg
    rw [norm_mul]
    have hM := norm_airySmoothMSq_le hε0 z
    have hHz := hb₀ (z + ((2 * ε : ℝ) : ℂ))
    have henv_shift := airyEnv_add_real_le z (2 * ε)
    have hprod_env : Real.exp (2 * ε * airySqrtRe z) * airyEnv (z + ((2 * ε : ℝ) : ℂ)) ≤ airyEnv z := by
      calc Real.exp (2 * ε * airySqrtRe z) * airyEnv (z + ((2 * ε : ℝ) : ℂ))
          ≤ Real.exp (2 * ε * airySqrtRe z) *
              (airyEnv z * Real.exp (-2 * (2 * ε) * airySqrtRe z)) :=
            mul_le_mul_of_nonneg_left henv_shift (Real.exp_pos _).le
        _ = airyEnv z * Real.exp (-2 * ε * airySqrtRe z) := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
            congr 2; ring
        _ ≤ airyEnv z * 1 := mul_le_mul_of_nonneg_left
            (Real.exp_le_one_iff.mpr (by nlinarith [airySqrtRe_nonneg z])) (airyEnv_pos z).le
        _ = airyEnv z := mul_one _
    have hpoly : (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ ≤ K_shift * (1 + ‖z‖) ^ ν₀ := by
      have hz_pos : 0 < 1 + ‖z‖ := by positivity
      have hzs_pos : 0 < 1 + ‖z + ((2 * ε : ℝ) : ℂ)‖ := by positivity
      rcases le_or_gt 0 ν₀ with hν | hν
      · have hup : 1 + ‖z + ((2 * ε : ℝ) : ℂ)‖ ≤ 3 * (1 + ‖z‖) := by
          have htri := norm_add_le z ((2 * ε : ℝ) : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at htri
          nlinarith [norm_nonneg z]
        dsimp [K_shift]
        rw [abs_of_nonneg hν, ← Real.mul_rpow (by norm_num) hz_pos.le]
        exact Real.rpow_le_rpow hzs_pos.le hup hν
      · have hlow : (1 + ‖z‖) / 3 ≤ 1 + ‖z + ((2 * ε : ℝ) : ℂ)‖ := by
          by_cases hz2 : ‖z‖ ≤ 2
          · have : (1 + ‖z‖) / 3 ≤ 1 := by linarith
            linarith [norm_nonneg (z + ((2 * ε : ℝ) : ℂ))]
          · push Not at hz2
            have htri : ‖z‖ ≤ ‖z + ((2 * ε : ℝ) : ℂ)‖ + 2 * ε := by
              calc ‖z‖ = ‖(z + ((2 * ε : ℝ) : ℂ)) - ((2 * ε : ℝ) : ℂ)‖ := by ring_nf
                _ ≤ ‖z + ((2 * ε : ℝ) : ℂ)‖ + ‖((2 * ε : ℝ) : ℂ)‖ := norm_sub_le _ _
                _ = ‖z + ((2 * ε : ℝ) : ℂ)‖ + 2 * ε := by
                    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            linarith [norm_nonneg (z + ((2 * ε : ℝ) : ℂ))]
        have hneg : 0 ≤ -ν₀ := by linarith
        have h1 : (1 + ‖z‖) ^ (-ν₀) ≤ (3 * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖)) ^ (-ν₀) :=
          Real.rpow_le_rpow hz_pos.le (by linarith) hneg
        rw [Real.mul_rpow (by norm_num) hzs_pos.le] at h1
        have hp1 : 0 < (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀) := Real.rpow_pos_of_pos hzs_pos _
        have hp2 : 0 < (1 + ‖z‖) ^ (-ν₀) := Real.rpow_pos_of_pos hz_pos _
        have h2 : (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ = ((1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀))⁻¹ := by
          rw [Real.rpow_neg hzs_pos.le, inv_inv]
        have h3 : (1 + ‖z‖) ^ ν₀ = ((1 + ‖z‖) ^ (-ν₀))⁻¹ := by
          rw [Real.rpow_neg hz_pos.le, inv_inv]
        dsimp [K_shift]
        rw [abs_of_neg hν, h2, h3, inv_le_iff_one_le_mul₀' hp1]
        calc (1 : ℝ) = (1 + ‖z‖) ^ (-ν₀) * ((1 + ‖z‖) ^ (-ν₀))⁻¹ := (mul_inv_cancel₀ hp2.ne').symm
          _ ≤ (3 ^ (-ν₀) * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀)) * ((1 + ‖z‖) ^ (-ν₀))⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hp2.le)
          _ = (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀) *
                (3 ^ (-ν₀) * ((1 + ‖z‖) ^ (-ν₀))⁻¹) := by ring
    calc ‖airySmoothMSq ε z‖ * ‖H (z + ((2 * ε : ℝ) : ℂ))‖
        ≤ Real.exp (2 * ε * airySqrtRe z) *
            (C₀ * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ * airyEnv (z + ((2 * ε : ℝ) : ℂ))) :=
          mul_le_mul hM hHz (norm_nonneg _) (Real.exp_pos _).le
      _ = C₀ * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ *
            (Real.exp (2 * ε * airySqrtRe z) * airyEnv (z + ((2 * ε : ℝ) : ℂ))) := by ring
      _ ≤ C₀ * (K_shift * (1 + ‖z‖) ^ ν₀) * airyEnv z :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpoly hC₀_nn) hprod_env
            (mul_nonneg (Real.exp_pos _).le (airyEnv_pos _).le)
            (mul_nonneg hC₀_nn (mul_nonneg hK_pos.le (Real.rpow_nonneg (by positivity) _)))
      _ = (C₀ * K_shift) * (1 + ‖z‖) ^ ν₀ * airyEnv z := by ring
  -- Helper for `airyEnv (u : ℂ)` on `u ≥ 0`
  have hairyEnv_nonneg_eq : ∀ u : ℝ, 0 ≤ u →
      airyEnv (u : ℂ) = Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
    intro u hu
    unfold airyEnv
    congr 2
    have hc := (Complex.ofReal_cpow hu (3 / 2 : ℝ)).symm
    push_cast at hc
    rw [hc, Complex.ofReal_re]
  have hcontOn_airyEnv_Ici : ContinuousOn (fun u : ℝ => airyEnv (u : ℂ)) (Ici 0) := by
    refine (Continuous.continuousOn ?_).congr fun u (hu : 0 ≤ u) => hairyEnv_nonneg_eq u hu
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num)))
  -- Positive-axis integrable majorant `g_pos Y` for `‖airySmoothReg H ε (u : ℂ)‖ * e^{Y u}` on `u > 0`.
  have hpos_maj_int : ∀ Y : ℝ, 0 ≤ Y →
      IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
        airyEnv (u : ℂ) * Real.exp (Y * u)) (Ioi 0) := by
    intro Y hY
    set R₀ : ℝ := max 5 ((3 * (Y + 1)) ^ 2)
    have hR₀_ge5 : 5 ≤ R₀ := le_max_left _ _
    have hmid : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
        airyEnv (u : ℂ) * Real.exp (Y * u)) (Icc 0 R₀) := by
      refine ContinuousOn.integrableOn_Icc ?_
      refine (((continuousOn_const.mul ?_).mul ?_).mul ?_)
      · refine ContinuousOn.rpow_const (continuousOn_const.add continuous_abs.continuousOn) ?_
        intro x _; left; positivity
      · exact hcontOn_airyEnv_Ici.mono (fun x hx => hx.1)
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    have htail : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
        airyEnv (u : ℂ) * Real.exp (Y * u)) (Ioi R₀) := by
      set Np : ℕ := ⌈|ν₀|⌉₊
      have hdom : IntegrableOn (fun u : ℝ =>
          ((C₀ * K_shift) * Real.exp 1 * Np.factorial) * Real.exp (-u)) (Ioi R₀) := by
        have hexp : IntegrableOn (fun u : ℝ => Real.exp (-1 * u)) (Ioi R₀) :=
          integrableOn_exp_mul_Ioi (by norm_num) R₀
        have hexp' : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi R₀) :=
          hexp.congr_fun (fun u _ => by ring_nf) measurableSet_Ioi
        exact hexp'.const_mul ((C₀ * K_shift) * Real.exp 1 * Np.factorial)
      refine hdom.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : R₀ < u) => ?_)
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        refine (((continuousOn_const.mul ?_).mul ?_).mul ?_)
        · refine ContinuousOn.rpow_const (continuousOn_const.add continuous_abs.continuousOn) ?_
          intro x _; left; positivity
        · exact hcontOn_airyEnv_Ici.mono (fun x (hx : R₀ < x) => show 0 ≤ x by linarith)
        · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      · have hu_pos : 0 < u := by linarith
        have henv_eq := hairyEnv_nonneg_eq u hu_pos.le
        have hsqrt_ge : 3 * (Y + 1) ≤ Real.sqrt u := by
          have hsq : (3 * (Y + 1)) ^ 2 ≤ u := (le_max_right _ _).trans hu.le
          exact Real.le_sqrt_of_sq_le hsq
        have hu32 : u * Real.sqrt u = u ^ (3 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hu_pos.le (by norm_num)]
          norm_num
        have hexp_le : airyEnv (u : ℂ) * Real.exp (Y * u) ≤ Real.exp (-2 * u) := by
          rw [henv_eq, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h1 : 3 * (Y + 1) * u ≤ u ^ (3 / 2 : ℝ) := by
            rw [← hu32]; nlinarith
          nlinarith
        have hrpow_le : (1 + |u|) ^ ν₀ ≤ (1 + u) ^ Np := by
          rw [abs_of_pos hu_pos, ← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith)
            ((le_abs_self ν₀).trans (Nat.le_ceil |ν₀|))
        have hpow_exp : (1 + u) ^ Np * Real.exp (-2 * u) ≤
            Real.exp 1 * Np.factorial * Real.exp (-u) := by
          have hpe := pow_mul_exp_neg_le Np (x := 1 + u) (by positivity)
          calc (1 + u) ^ Np * Real.exp (-2 * u)
              = ((1 + u) ^ Np * Real.exp (-(1 + u))) * Real.exp (1 - u) := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
            _ ≤ Np.factorial * Real.exp (1 - u) :=
                mul_le_mul_of_nonneg_right hpe (Real.exp_pos _).le
            _ = Real.exp 1 * Np.factorial * Real.exp (-u) := by
                rw [sub_eq_add_neg, Real.exp_add]; ring
        have henv_u_nn : 0 ≤ airyEnv (u : ℂ) := (airyEnv_pos (u : ℂ)).le
        have hterm_nn : 0 ≤ (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u) :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀_nn hK_pos.le)
            (Real.rpow_nonneg (by positivity) _)) henv_u_nn) (Real.exp_pos _).le
        rw [Real.norm_eq_abs, abs_of_nonneg hterm_nn]
        calc (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)
            = (C₀ * K_shift) * ((1 + |u|) ^ ν₀ * (airyEnv (u : ℂ) * Real.exp (Y * u))) := by ring
          _ ≤ (C₀ * K_shift) * ((1 + u) ^ Np * Real.exp (-2 * u)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hrpow_le hexp_le
                  (mul_nonneg henv_u_nn (Real.exp_pos _).le) (by positivity))
                (by positivity)
          _ ≤ (C₀ * K_shift) * (Real.exp 1 * Np.factorial * Real.exp (-u)) :=
              mul_le_mul_of_nonneg_left hpow_exp (by positivity)
          _ = ((C₀ * K_shift) * Real.exp 1 * Np.factorial) * Real.exp (-u) := by ring
    have hIci : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
        airyEnv (u : ℂ) * Real.exp (Y * u)) (Ici 0) := by
      rw [← Icc_union_Ioi_eq_Ici (by positivity : (0 : ℝ) ≤ R₀)]
      exact hmid.union htail
    exact hIci.mono_set Ioi_subset_Ici_self
  -- Uniform L¹ bound `C_H` for `airySmoothReg H ε` (`ε ∈ [0, 1]`).
  obtain ⟨M_mid, hM_mid⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2 : ℝ) 2) (hH.1.continuous.comp Complex.continuous_ofReal).continuousOn
  set I_H : ℝ := ∫ v : ℝ, ‖H (v : ℂ)‖
  set I_pos0 : ℝ := ∫ u in Ioi (0 : ℝ), (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)
  set C_H : ℝ := I_H + 2 * max M_mid 0 + I_pos0
  have hI_H_nn : 0 ≤ I_H := integral_nonneg fun _ => norm_nonneg _
  have hI_pos0_nn : 0 ≤ I_pos0 := setIntegral_nonneg measurableSet_Ioi fun u _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hC₀_nn hK_pos.le) (Real.rpow_nonneg (by positivity) _))
      (airyEnv_pos (u : ℂ)).le
  have hC_H_nn : 0 ≤ C_H := by positivity
  have hReg_int_and_l1 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      Integrable (fun u : ℝ => airySmoothReg H ε (u : ℂ)) ∧
      (∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖) ≤ C_H := by
    intro ε hε0 hε1
    have hmeas : AEStronglyMeasurable (fun u : ℝ => airySmoothReg H ε (u : ℂ)) volume :=
      ((hReg_diff ε).continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
    -- Integrability and bound on `Ioi 0`
    have hint_pos : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Ioi 0) := by
      have hdom0 : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ))
          (Ioi 0) := by
        simpa [zero_mul, Real.exp_zero, mul_one] using hpos_maj_int 0 le_rfl
      refine hdom0.mono' hmeas.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
      simpa [Complex.norm_real, Real.norm_eq_abs] using hReg_growth ε hε0 hε1 (u : ℂ)
    have hbd_pos : (∫ u in Ioi (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) ≤ I_pos0 := by
      have hdom0 : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ))
          (Ioi 0) := by
        simpa [zero_mul, Real.exp_zero, mul_one] using hpos_maj_int 0 le_rfl
      refine setIntegral_mono_on hint_pos.norm hdom0 measurableSet_Ioi fun u _ => ?_
      simpa [Complex.norm_real, Real.norm_eq_abs] using hReg_growth ε hε0 hε1 (u : ℂ)
    -- Integrability and bound on `Ioc (-2) 0`
    have hint_mid : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Ioc (-2) 0) :=
      (((hReg_diff ε).continuous.comp Complex.continuous_ofReal).continuousOn.integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have hbd_mid : (∫ u in Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖) ≤ 2 * max M_mid 0 := by
      have hpt : ∀ u ∈ Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖ ≤ max M_mid 0 := by
        intro u hu
        unfold airySmoothReg
        rw [norm_mul]
        have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
          have := norm_airySmoothMSq_neg_le_one hε0 (x := -u) (by linarith [hu.2])
          simpa using this
        have hcast : (u : ℂ) + (2 * ε : ℝ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast]
        have hH1 : ‖H ((u + 2 * ε : ℝ) : ℂ)‖ ≤ max M_mid 0 :=
          (hM_mid (u + 2 * ε) ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans (le_max_left _ _)
        nlinarith [norm_nonneg (H ((u + 2 * ε : ℝ) : ℂ))]
      calc (∫ u in Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖)
          ≤ ∫ _ in Ioc (-2 : ℝ) 0, max M_mid 0 :=
            setIntegral_mono_on hint_mid.norm
              (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              measurableSet_Ioc hpt
        _ = 2 * max M_mid 0 := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
            ring
    -- Integrability and bound on `Iic (-2)`
    have hint_far : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Iic (-2)) := by
      have hdom_shift : IntegrableOn (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) (Iic (-2)) :=
        (hH.2.1.norm.comp_add_right (2 * ε)).integrableOn
      refine hdom_shift.mono' hmeas.restrict
        (ae_restrict_of_forall_mem measurableSet_Iic fun u (hu : u ≤ -2) => ?_)
      unfold airySmoothReg
      rw [norm_mul]
      have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
        have := norm_airySmoothMSq_neg_le_one hε0 (x := -u) (by linarith)
        simpa using this
      have hcast : (u : ℂ) + (2 * ε : ℝ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast]
      exact mul_le_of_le_one_left (norm_nonneg _) hM1
    have hbd_far : (∫ u in Iic (-2 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) ≤ I_H := by
      have hdom_shift : Integrable (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) :=
        hH.2.1.norm.comp_add_right (2 * ε)
      have hmono := setIntegral_mono_on hint_far.norm hdom_shift.integrableOn
        measurableSet_Iic fun u (hu : u ≤ -2) => by
          unfold airySmoothReg
          rw [norm_mul]
          have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
            have := norm_airySmoothMSq_neg_le_one hε0 (x := -u) (by linarith)
            simpa using this
          have hcast : (u : ℂ) + (2 * ε : ℝ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
          rw [hcast]
          exact mul_le_of_le_one_left (norm_nonneg _) hM1
      refine hmono.trans ?_
      calc (∫ u in Iic (-2 : ℝ), ‖H ((u + 2 * ε : ℝ) : ℂ)‖)
          ≤ ∫ u : ℝ, ‖H ((u + 2 * ε : ℝ) : ℂ)‖ :=
            setIntegral_le_integral hdom_shift (Eventually.of_forall fun _ => norm_nonneg _)
        _ = I_H := integral_add_right_eq_self (fun v : ℝ => ‖H (v : ℂ)‖) (2 * ε)
    have hint_Iic0 : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Iic 0) := by
      rw [← Iic_union_Ioc_eq_Iic (by norm_num : (-2 : ℝ) ≤ 0)]
      exact hint_far.union hint_mid
    have hint_univ : Integrable (fun u : ℝ => airySmoothReg H ε (u : ℂ)) := by
      rw [← integrableOn_univ, ← Iic_union_Ioi]
      exact hint_Iic0.union hint_pos
    refine ⟨hint_univ, ?_⟩
    have hsplit1 : (∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖) =
        (∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) +
          ∫ u in Ioi (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖ := by
      rw [← setIntegral_univ, ← Iic_union_Ioi,
        setIntegral_union (Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2)
          measurableSet_Ioi hint_Iic0.norm hint_pos.norm]
    have hsplit2 : (∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) =
        (∫ u in Iic (-2 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) +
          ∫ u in Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖ := by
      have hdisj : Disjoint (Iic (-2 : ℝ)) (Ioc (-2 : ℝ) 0) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2.1
      rw [← Iic_union_Ioc_eq_Iic (by norm_num : (-2 : ℝ) ≤ 0),
        setIntegral_union hdisj measurableSet_Ioc hint_far.norm hint_mid.norm]
    rw [hsplit1, hsplit2]
    dsimp [C_H]
    linarith
  have hReg_im_zero : ∀ ε : ℝ, ∀ u : ℝ, (airySmoothReg H ε (u : ℂ)).im = 0 := by
    intro ε u
    unfold airySmoothReg
    have hm_im := (airySmoothMSq_ofReal_im_and_nonneg ε u).1
    have hcast : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.mul_im, hm_im, hH.2.2.2 (u + 2 * ε)]
    ring
  -- Assemble all four conjuncts of `lem_al_smooth`
  refine ⟨?_, ?_, ?_, C_H, hC_H_nn, ?_, ?_⟩
  · -- Part 1: properties for each `ε ∈ (0, 1]`
    intro ε ⟨hε0, hε1⟩
    have hcl : InAiryClass (airySmoothReg H ε) :=
      ⟨hReg_diff ε, (hReg_int_and_l1 ε hε0.le hε1).1,
        ⟨C₀ * K_shift, ν₀, by positivity, hReg_growth ε hε0.le hε1⟩,
        hReg_im_zero ε⟩
    refine ⟨differentiable_airySmoothMSq ε, airySmoothMSq_ofReal_im_and_nonneg ε,
      fun x hx => norm_airySmoothMSq_neg_le_one hε0.le hx,
      norm_airySmoothMSq_le hε0.le, hcl, fun _ => hReg_im_zero ε, ?_⟩
    · -- SchwartzMap ℝ ℝ witness via Cauchy estimates on `sphere (u : ℂ) ((1 + |u|)^{-1/2})`
      obtain ⟨hsmooth_re, hcont_iter_re⟩ := contDiff_re_of_differentiable (hReg_diff ε)
      refine ⟨{
        toFun := fun u => (airySmoothReg H ε (u : ℂ)).re
        smooth' := hsmooth_re
        decay' := fun k n => ?_
      }, fun _ => rfl⟩
      have hcont_kn : Continuous (fun u : ℝ =>
          |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u|) :=
        (continuous_abs.pow k).mul (continuous_abs.comp (hcont_iter_re n))
      obtain ⟨M_box, hM_box⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (s := Icc (-5 : ℝ) 5) hcont_kn.continuousOn
      set Nν : ℕ := ⌈|ν₀|⌉₊
      set m_ord : ℕ := k + n + Nν + 1
      obtain ⟨C_m, hCm_nn, hCm⟩ := norm_airySmoothMSq_le_on_neg_sphere hε0 hε1 m_ord
      -- Left tail `u < -5`:
      set C_left : ℝ := n.factorial * C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ (n + Nν)
      -- Right tail `5 < u`:
      set N_right : ℕ := k + n + Nν
      set C_right : ℝ := n.factorial * (C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 41 * N_right.factorial
      refine ⟨max (max M_box 0) (max C_left C_right), fun u => ?_⟩
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      by_cases hu_mid : -5 ≤ u ∧ u ≤ 5
      · have h1 := hM_box u hu_mid
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
        exact h1.trans ((le_max_left M_box 0).trans (le_max_left _ _))
      · rw [not_and_or, not_le, not_le] at hu_mid
        set r_u : ℝ := (1 + |u|) ^ (-(1 / 2 : ℝ))
        have hu1_pos : 0 < 1 + |u| := by positivity
        have hru_pos : 0 < r_u := Real.rpow_pos_of_pos hu1_pos _
        have hru_le1 : r_u ≤ 1 := by
          have h1 : (1 : ℝ) ≤ 1 + |u| := by linarith [abs_nonneg u]
          have h2 := Real.rpow_le_rpow_of_nonpos zero_lt_one h1 (by norm_num : -(1 / 2 : ℝ) ≤ 0)
          rwa [Real.one_rpow] at h2
        have hru_pow_inv : (r_u ^ n)⁻¹ ≤ (1 + |u|) ^ n := by
          have hinv : r_u⁻¹ = (1 + |u|) ^ (1 / 2 : ℝ) := by
            dsimp [r_u]; rw [Real.rpow_neg hu1_pos.le, inv_inv]
          rw [← inv_pow, hinv, ← Real.rpow_natCast ((1 + |u|) ^ (1 / 2 : ℝ)),
            ← Real.rpow_mul hu1_pos.le, ← Real.rpow_natCast (1 + |u|) n]
          refine Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) ?_
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        rcases hu_mid with hu_lt | hu_gt
        · -- `u < -5`
          have hu_abs : 5 < |u| := by rw [abs_of_neg (by linarith)]; linarith
          have hsphere_neg : ∀ ζ ∈ sphere (u : ℂ) r_u,
              ‖airySmoothReg H ε ζ‖ ≤
                (C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
                  (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord)) := by
            intro ζ hζ
            have hnorm_sub : ‖ζ - (u : ℂ)‖ = r_u := mem_sphere_iff_norm.mp hζ
            have hM_s := hCm (by linarith : u ≤ -4) hru_pos hru_le1 ζ hζ
            set w_u : ℂ := ((u + 2 * ε : ℝ) : ℂ)
            have hw_eq : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = w_u := by dsimp [w_u]; push_cast; rfl
            have hsub_w : (ζ + ((2 * ε : ℝ) : ℂ)) - w_u = ζ - (u : ℂ) := by
              rw [← hw_eq]; ring
            have hrw_le : r_u ≤ 2 * (1 + ‖w_u‖) ^ (-(1 / 2 : ℝ)) := by
              have hw_le : 1 + ‖w_u‖ ≤ 1 + |u| := by
                rw [Complex.norm_real, Real.norm_eq_abs,
                  abs_of_neg (by linarith : u + 2 * ε < 0), abs_of_neg (by linarith : u < 0)]
                linarith
              have h2 : (1 + |u|) ^ (-(1 / 2 : ℝ)) ≤ (1 + ‖w_u‖) ^ (-(1 / 2 : ℝ)) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hw_le (by norm_num)
              linarith [Real.rpow_pos_of_pos (by positivity : 0 < 1 + ‖w_u‖) (-(1 / 2 : ℝ))]
            have henv_w : airyEnv w_u = 1 := by
              unfold airyEnv
              have hre0 : (w_u ^ (3 / 2 : ℂ)).re = 0 := by
                rw [re_cpow_three_halves_eq_ab w_u]
                have ha0 : airySqrtRe w_u = 0 :=
                  airySqrtRe_ofReal_nonpos (by linarith : u + 2 * ε ≤ 0)
                simp [ha0]
              simp [hre0]
            have henv_s : airyEnv (ζ + ((2 * ε : ℝ) : ℂ)) ≤ Real.exp 40 := by
              have h := airyEnv_ball_le (w := w_u) (ζ := ζ + ((2 * ε : ℝ) : ℂ))
                (by rw [hsub_w, hnorm_sub]; exact hrw_le)
              rwa [henv_w, mul_one] at h
            have hpoly_s : (1 + ‖ζ + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ ≤ 4 ^ |ν₀| * (4 * |u|) ^ Nν := by
              have h1 := one_add_norm_rpow_ball_le ν₀ (w := w_u) (ζ := ζ + ((2 * ε : ℝ) : ℂ))
                (by rw [hsub_w, hnorm_sub]; exact hru_le1)
              have hw_le : 1 + ‖w_u‖ ≤ 4 * |u| := by
                rw [Complex.norm_real, Real.norm_eq_abs,
                  abs_of_neg (by linarith : u + 2 * ε < 0)]
                linarith [abs_of_neg (by linarith : u < 0)]
              have h2 : (1 + ‖w_u‖) ^ ν₀ ≤ (4 * |u|) ^ Nν := by
                calc (1 + ‖w_u‖) ^ ν₀
                    ≤ (1 + ‖w_u‖) ^ (Nν : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg w_u])
                        ((le_abs_self ν₀).trans (Nat.le_ceil |ν₀|))
                  _ = (1 + ‖w_u‖) ^ Nν := Real.rpow_natCast _ _
                  _ ≤ (4 * |u|) ^ Nν := pow_le_pow_left₀ (by positivity) hw_le Nν
              exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
            have hH_s : ‖H (ζ + ((2 * ε : ℝ) : ℂ))‖ ≤
                C₀ * (4 ^ |ν₀| * (4 * |u|) ^ Nν) * Real.exp 40 := by
              calc ‖H (ζ + ((2 * ε : ℝ) : ℂ))‖
                  ≤ C₀ * (1 + ‖ζ + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ * airyEnv (ζ + ((2 * ε : ℝ) : ℂ)) := hb₀ _
                _ ≤ C₀ * (4 ^ |ν₀| * (4 * |u|) ^ Nν) * Real.exp 40 :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hpoly_s hC₀_nn) henv_s
                      (airyEnv_pos _).le (by positivity)
            unfold airySmoothReg
            rw [norm_mul]
            calc ‖airySmoothMSq ε ζ‖ * ‖H (ζ + ((2 * ε : ℝ) : ℂ))‖
                ≤ (C_m * (|u|⁻¹) ^ (2 * m_ord)) *
                    (C₀ * (4 ^ |ν₀| * (4 * |u|) ^ Nν) * Real.exp 40) :=
                  mul_le_mul hM_s hH_s (norm_nonneg _) (by positivity)
              _ = (C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
                    (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord)) := by
                  rw [mul_pow]; ring
          have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hru_pos
            (hReg_diff ε).differentiableOn.diffContOnCl hsphere_neg
          have hd_re : |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤
              ‖iteratedDeriv n (airySmoothReg H ε) (u : ℂ)‖ := by
            rw [iteratedDeriv_re_of_differentiable (hReg_diff ε)]
            exact Complex.abs_re_le_norm _
          have h1_plus : (1 + |u|) ^ n ≤ 4 ^ n * |u| ^ n := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) (by linarith) n
          have hpow_collapse : |u| ^ k * |u| ^ n * |u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord) ≤ 1 := by
            have htot : |u| ^ k * |u| ^ n * |u| ^ Nν = |u| ^ (k + n + Nν) := by
              rw [← pow_add, ← pow_add, add_assoc]
            rw [htot]
            have hle_m : k + n + Nν ≤ 2 * m_ord := by dsimp [m_ord]; omega
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle_m
            rw [hd, pow_add (|u|⁻¹) (k + n + Nν) d, ← mul_assoc (|u| ^ (k + n + Nν)), ← mul_pow,
              mul_inv_cancel₀ (by linarith), one_pow, one_mul]
            exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
          have hbound_u : |u| ^ k *
              |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤ C_left := by
            calc |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u|
                ≤ |u| ^ k * (n.factorial *
                    ((C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
                      (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord))) * (r_u ^ n)⁻¹) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact hd_re.trans (by rwa [div_eq_mul_inv] at hcauchy)
              _ ≤ |u| ^ k * (n.factorial *
                    ((C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
                      (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord))) * (4 ^ n * |u| ^ n)) := by
                  refine mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hru_pow_inv.trans h1_plus) (by positivity))
                    (by positivity)
              _ = C_left * (|u| ^ k * |u| ^ n * |u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord)) := by
                  dsimp [C_left]; rw [pow_add]; ring
              _ ≤ C_left * 1 := mul_le_mul_of_nonneg_left hpow_collapse (by positivity)
              _ = C_left := mul_one _
          exact hbound_u.trans ((le_max_left C_left C_right).trans (le_max_right _ _))
        · -- `5 < u`
          have hu_pos : 0 < u := by linarith
          have hsphere_pos : ∀ ζ ∈ sphere (u : ℂ) r_u,
              ‖airySmoothReg H ε ζ‖ ≤
                ((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                  (1 + u) ^ Nν * Real.exp (-u) := by
            intro ζ hζ
            have hnorm_sub : ‖ζ - (u : ℂ)‖ = r_u := mem_sphere_iff_norm.mp hζ
            have h1 := hReg_growth ε hε0.le hε1 ζ
            have hpoly_s : (1 + ‖ζ‖) ^ ν₀ ≤ 4 ^ |ν₀| * (1 + u) ^ Nν := by
              have hp1 := one_add_norm_rpow_ball_le ν₀ (w := (u : ℂ)) (ζ := ζ)
                (by rw [hnorm_sub]; exact hru_le1)
              have hnorm_u : ‖(u : ℂ)‖ = u := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
              rw [hnorm_u] at hp1
              have hp2 : (1 + u) ^ ν₀ ≤ (1 + u) ^ Nν := by
                rw [← Real.rpow_natCast]
                exact Real.rpow_le_rpow_of_exponent_le (by linarith)
                  ((le_abs_self ν₀).trans (Nat.le_ceil |ν₀|))
              exact hp1.trans (mul_le_mul_of_nonneg_left hp2 (by positivity))
            have henv_s : airyEnv ζ ≤ Real.exp 40 * Real.exp (-u) := by
              have hnorm_u : ‖(u : ℂ)‖ = |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
              have he1 := airyEnv_ball_le (w := (u : ℂ)) (ζ := ζ) (by
                rw [hnorm_sub, hnorm_u]; linarith)
              have he2 : airyEnv (u : ℂ) ≤ Real.exp (-u) := by
                rw [hairyEnv_nonneg_eq u hu_pos.le]
                apply Real.exp_le_exp.mpr
                have hu_ge1 : u ^ (1 : ℝ) ≤ u ^ (3 / 2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
                rw [Real.rpow_one] at hu_ge1
                linarith
              exact he1.trans (mul_le_mul_of_nonneg_left he2 (Real.exp_pos _).le)
            calc ‖airySmoothReg H ε ζ‖
                ≤ (C₀ * K_shift) * (1 + ‖ζ‖) ^ ν₀ * airyEnv ζ := h1
              _ ≤ (C₀ * K_shift) * (4 ^ |ν₀| * (1 + u) ^ Nν) * (Real.exp 40 * Real.exp (-u)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hpoly_s (by positivity)) henv_s
                    (airyEnv_pos _).le (by positivity)
              _ = ((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) * (1 + u) ^ Nν * Real.exp (-u) := by
                  ring
          have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hru_pos
            (hReg_diff ε).differentiableOn.diffContOnCl hsphere_pos
          have hcauchy' : ‖iteratedDeriv n (airySmoothReg H ε) (u : ℂ)‖ ≤
              n.factorial * (((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                (1 + u) ^ Nν * Real.exp (-u)) * (r_u ^ n)⁻¹ := by
            rwa [div_eq_mul_inv] at hcauchy
          have hd_re : |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤
              ‖iteratedDeriv n (airySmoothReg H ε) (u : ℂ)‖ := by
            rw [iteratedDeriv_re_of_differentiable (hReg_diff ε)]
            exact Complex.abs_re_le_norm _
          have hu_abs_eq : |u| = u := abs_of_pos hu_pos
          have hpow_exp : (1 + u) ^ N_right * Real.exp (-u) ≤ Real.exp 1 * N_right.factorial := by
            have hpe := pow_mul_exp_neg_le N_right (x := 1 + u) (by positivity)
            calc (1 + u) ^ N_right * Real.exp (-u)
                = ((1 + u) ^ N_right * Real.exp (-(1 + u))) * Real.exp 1 := by
                  rw [mul_assoc, ← Real.exp_add]; congr 2; ring
              _ ≤ N_right.factorial * Real.exp 1 :=
                  mul_le_mul_of_nonneg_right hpe (Real.exp_pos _).le
              _ = Real.exp 1 * N_right.factorial := mul_comm _ _
          have hbound_u : |u| ^ k *
              |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤ C_right := by
            rw [hu_abs_eq]
            have hru_u : (r_u ^ n)⁻¹ ≤ (1 + u) ^ n := by rwa [hu_abs_eq] at hru_pow_inv
            have huk_le : u ^ k ≤ (1 + u) ^ k := pow_le_pow_left₀ hu_pos.le (by linarith) k
            calc u ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u|
                ≤ (1 + u) ^ k * (n.factorial *
                    (((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                      (1 + u) ^ Nν * Real.exp (-u)) * (1 + u) ^ n) := by
                  refine mul_le_mul huk_le ?_ (abs_nonneg _) (by positivity)
                  exact hd_re.trans (hcauchy'.trans
                    (mul_le_mul_of_nonneg_left hru_u (by positivity)))
              _ = (n.factorial * (C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                    ((1 + u) ^ N_right * Real.exp (-u)) := by
                  dsimp [N_right]; rw [pow_add, pow_add]; ring
              _ ≤ (n.factorial * (C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                    (Real.exp 1 * N_right.factorial) :=
                  mul_le_mul_of_nonneg_left hpow_exp (by positivity)
              _ = C_right := by
                  dsimp [C_right]
                  have hexp41 : Real.exp 40 * Real.exp 1 = Real.exp 41 := by
                    rw [← Real.exp_add]; norm_num
                  rw [← hexp41]; ring
          exact hbound_u.trans ((le_max_right C_left C_right).trans (le_max_right _ _))
  · -- Part 2: `TendstoLocallyUniformly (fun ε z => airySmoothReg H ε z) H (𝓝[>] 0)`
    rw [tendstoLocallyUniformly_iff_forall_tendsto]
    intro z₀
    have hcont_reg : Continuous (fun p : ℝ × ℂ => airySmoothReg H p.1 p.2) := by
      unfold airySmoothReg airySmoothMSq
      exact (continuous_uncurry_airySmoothM.pow 2).mul
        (hH.1.continuous.comp (continuous_snd.add
          (Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst))))
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro V hV
    obtain ⟨δ, hδ, hVδ⟩ := Metric.mem_uniformity_dist.mp hV
    have hcont_dist : Continuous (fun p : ℝ × ℂ => dist (H p.2) (airySmoothReg H p.1 p.2)) :=
      (hH.1.continuous.comp continuous_snd).dist hcont_reg
    have hat0 : dist (H z₀) (airySmoothReg H 0 z₀) < δ := by
      simp [airySmoothReg, airySmoothMSq_zero, hδ]
    have hev : ∀ᶠ p : ℝ × ℂ in 𝓝 (0, z₀),
        p ∈ {q : ℝ × ℂ | dist (H q.2) (airySmoothReg H q.1 q.2) < δ} :=
      hcont_dist.continuousAt.preimage_mem_nhds (Iio_mem_nhds hat0)
    rw [nhds_prod_eq] at hev
    filter_upwards [hev.filter_mono (Filter.prod_mono_left _ nhdsWithin_le_nhds)] with p hp
    exact hVδ hp
  · -- Part 3: Weighted `L¹(e^{Y max(u, 0)} du)` convergence as `ε ↓ 0`
    intro Y hY
    have hcont_reg_R : Continuous (fun p : ℝ × ℝ => airySmoothReg H p.1 (p.2 : ℂ)) := by
      unfold airySmoothReg airySmoothMSq
      exact ((continuous_uncurry_airySmoothM.comp
        (continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd))).pow 2).mul
        (hH.1.continuous.comp ((Complex.continuous_ofReal.comp continuous_snd).add
          (Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst))))
    have hK_ge1 : 1 ≤ K_shift :=
      Real.one_le_rpow (by norm_num) (abs_nonneg ν₀)
    have h_pos_tendsto : Tendsto (fun ε : ℝ =>
        ∫ u in Ioi (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
        (𝓝[>] 0) (𝓝 0) := by
      have hdom : IntegrableOn (fun u : ℝ =>
          2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u))) (Ioi 0) :=
        (hpos_maj_int Y hY).const_mul 2
      have hconv := tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (Ioi (0 : ℝ)))
        (F := fun ε u => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
        (f := fun _ => (0 : ℝ))
        (bound := fun u =>
          2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)))
        (Eventually.of_forall fun ε => by
          refine Continuous.aestronglyMeasurable ?_
          exact ((hcont_reg_R.comp (continuous_const.prodMk continuous_id)).sub
            (hH.1.continuous.comp Complex.continuous_ofReal)).norm.mul
            (Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const))))
        (Filter.eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε =>
          ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), max_eq_left hu.le]
            have h1 : ‖airySmoothReg H ε (u : ℂ)‖ ≤
                (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
              simpa [Complex.norm_real, Real.norm_eq_abs] using
                hReg_growth ε hε.1.le hε.2 (u : ℂ)
            have h2 : ‖H (u : ℂ)‖ ≤ (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
              have hb_u : ‖H (u : ℂ)‖ ≤ C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
                simpa [Complex.norm_real, Real.norm_eq_abs] using hb₀ (u : ℂ)
              exact hb_u.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC₀_nn hK_ge1) (by positivity))
                (airyEnv_pos _).le)
            calc ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * u)
                ≤ (‖airySmoothReg H ε (u : ℂ)‖ + ‖H (u : ℂ)‖) * Real.exp (Y * u) :=
                  mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
              _ ≤ 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)) * Real.exp (Y * u) :=
                  mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
              _ = 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)) := by
                  ring)
        hdom
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => by
          have ht : Tendsto (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) (𝓝 0) (𝓝 (H (u : ℂ))) := by
            have hc_fn : Continuous (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) :=
              hcont_reg_R.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => u))
            simpa [airySmoothReg, airySmoothMSq_zero] using (hc_fn.continuousAt (x := 0)).tendsto
          have ht_sub := (ht.mono_left nhdsWithin_le_nhds).sub_const (H (u : ℂ))
          rw [sub_self] at ht_sub
          have ht_mul := ht_sub.norm.mul_const (Real.exp (Y * max u 0))
          rw [norm_zero, zero_mul] at ht_mul
          exact ht_mul)
      rw [integral_zero] at hconv
      exact hconv
    -- Negative half-line `Iic 0` (`max u 0 = 0`, `exp (Y * max u 0) = 1`)
    have h_neg_tendsto : Tendsto (fun ε : ℝ =>
        ∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
        (𝓝[>] 0) (𝓝 0) := by
      have htail_H : Tendsto (fun R : ℝ => ∫ v in Iic (-R + 2), ‖H (v : ℂ)‖) atTop (𝓝 0) := by
        have hconv := tendsto_integral_filter_of_dominated_convergence
          (l := atTop) (μ := volume)
          (F := fun (R : ℝ) (v : ℝ) => (Iic (-R + 2)).indicator (fun x => ‖H (x : ℂ)‖) v)
          (f := fun _ => (0 : ℝ))
          (bound := fun v => ‖H (v : ℂ)‖)
          (Eventually.of_forall fun R =>
            (hH.2.1.norm.aestronglyMeasurable.indicator measurableSet_Iic))
          (Eventually.of_forall fun R => Eventually.of_forall fun v => by
            by_cases hv : v ∈ Iic (-R + 2)
            · simp [indicator_of_mem hv]
            · simp [indicator_of_notMem hv])
          hH.2.1.norm
          (Eventually.of_forall fun v => by
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [Filter.eventually_gt_atTop (2 - v)] with R hR
            have hv_not : v ∉ Iic (-R + 2) := by rw [mem_Iic]; linarith
            simp [indicator_of_notMem hv_not])
        simpa [integral_indicator measurableSet_Iic] using hconv
      rw [Metric.tendsto_nhds]
      intro δ hδ
      have htail_ev := (Metric.tendsto_nhds.mp htail_H (δ / 4) (by positivity)).and
        (Filter.eventually_ge_atTop (2 : ℝ))
      obtain ⟨R, hR_int, hR_ge2⟩ := htail_ev.exists
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (setIntegral_nonneg measurableSet_Iic
        fun _ _ => norm_nonneg _)] at hR_int
      obtain ⟨M_win, hM_win⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (s := Icc (-R) 2) (hH.1.continuous.comp Complex.continuous_ofReal).continuousOn
      have hwin_tendsto : Tendsto (fun ε : ℝ =>
          ∫ u in Ioc (-R) 0, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
        have hdom_win : IntegrableOn (fun _ : ℝ => 2 * max M_win 0) (Ioc (-R) 0) :=
          continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        have hconv := tendsto_integral_filter_of_dominated_convergence
          (l := 𝓝[>] 0) (μ := volume.restrict (Ioc (-R) 0))
          (F := fun ε u => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖)
          (f := fun _ => (0 : ℝ))
          (bound := fun _ => 2 * max M_win 0)
          (Eventually.of_forall fun ε =>
            (((hcont_reg_R.comp (continuous_const.prodMk continuous_id)).sub
              (hH.1.continuous.comp Complex.continuous_ofReal)).norm).aestronglyMeasurable)
          (Filter.eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε =>
            ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => by
              rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
              have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
                have := norm_airySmoothMSq_neg_le_one hε.1.le (x := -u) (by linarith [hu.2])
                simpa using this
              have hreg_le : ‖airySmoothReg H ε (u : ℂ)‖ ≤ max M_win 0 := by
                unfold airySmoothReg
                rw [norm_mul]
                have hcast : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
                rw [hcast]
                have hh := (hM_win (u + 2 * ε) ⟨by linarith [hu.1, hε.1],
                  by linarith [hu.2, hε.2]⟩).trans (le_max_left _ _)
                nlinarith [norm_nonneg (H ((u + 2 * ε : ℝ) : ℂ))]
              have hh0 : ‖H (u : ℂ)‖ ≤ max M_win 0 :=
                (hM_win u ⟨hu.1.le, by linarith [hu.2]⟩).trans (le_max_left _ _)
              calc ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖
                  ≤ ‖airySmoothReg H ε (u : ℂ)‖ + ‖H (u : ℂ)‖ := norm_sub_le _ _
                _ ≤ 2 * max M_win 0 := by linarith)
          hdom_win
          (ae_restrict_of_forall_mem measurableSet_Ioc fun u _ => by
            have ht : Tendsto (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) (𝓝 0) (𝓝 (H (u : ℂ))) := by
              have hc_fn : Continuous (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) :=
                hcont_reg_R.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => u))
              simpa [airySmoothReg, airySmoothMSq_zero] using (hc_fn.continuousAt (x := 0)).tendsto
            have ht_sub := (ht.mono_left nhdsWithin_le_nhds).sub_const (H (u : ℂ))
            rw [sub_self] at ht_sub
            have htn := ht_sub.norm
            rw [norm_zero] at htn
            exact htn)
        rw [integral_zero] at hconv
        exact hconv
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one,
        Metric.tendsto_nhds.mp hwin_tendsto (δ / 2) (by positivity)] with ε hε hwin_lt
      rw [Real.dist_eq, sub_zero] at hwin_lt ⊢
      have hnn_int : 0 ≤ ∫ u in Iic (0 : ℝ),
          ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0) :=
        setIntegral_nonneg measurableSet_Iic fun _ _ => by positivity
      rw [abs_of_nonneg hnn_int]
      have heq_Iic : (∫ u in Iic (0 : ℝ),
          ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0)) =
          ∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ := by
        refine setIntegral_congr_fun measurableSet_Iic fun u (hu : u ≤ 0) => ?_
        rw [max_eq_right hu, mul_zero, Real.exp_zero, mul_one]
      rw [heq_Iic]
      have hint_diff : Integrable (fun u : ℝ => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) :=
        ((hReg_int_and_l1 ε hε.1.le hε.2).1.sub hH.2.1).norm
      have hsplit : (∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) =
          (∫ u in Iic (-R), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) +
            ∫ u in Ioc (-R) 0, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ := by
        have hdisj : Disjoint (Iic (-R)) (Ioc (-R) 0) :=
          Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2.1
        rw [← Iic_union_Ioc_eq_Iic (by linarith : -R ≤ 0),
          setIntegral_union hdisj measurableSet_Ioc hint_diff.integrableOn hint_diff.integrableOn]
      have hfar_lt : (∫ u in Iic (-R), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) < δ / 2 := by
        have hpt_le : ∀ u ≤ -R, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ ≤
            ‖H ((u + 2 * ε : ℝ) : ℂ)‖ + ‖H (u : ℂ)‖ := by
          intro u hu
          have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
            have := norm_airySmoothMSq_neg_le_one hε.1.le (x := -u) (by linarith)
            simpa using this
          have hcast : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
          have hmul1 : ‖airySmoothMSq ε (u : ℂ)‖ * ‖H ((u + 2 * ε : ℝ) : ℂ)‖ ≤
              ‖H ((u + 2 * ε : ℝ) : ℂ)‖ :=
            mul_le_of_le_one_left (norm_nonneg _) hM1
          unfold airySmoothReg
          rw [hcast]
          exact (norm_sub_le _ _).trans (by rw [norm_mul]; linarith)
        have hdom1 : Integrable (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) :=
          hH.2.1.norm.comp_add_right (2 * ε)
        have hmono := setIntegral_mono_on hint_diff.integrableOn
          (show IntegrableOn (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖ + ‖H (u : ℂ)‖) (Iic (-R))
            from hdom1.integrableOn.add hH.2.1.norm.integrableOn)
          measurableSet_Iic hpt_le
        rw [integral_add hdom1.integrableOn hH.2.1.norm.integrableOn] at hmono
        have hshift_eq : (∫ u in Iic (-R), ‖H ((u + 2 * ε : ℝ) : ℂ)‖) =
            ∫ v in Iic (-R + 2 * ε), ‖H (v : ℂ)‖ := by
          rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
          have hind : (Iic (-R)).indicator (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) =
              fun u : ℝ => (Iic (-R + 2 * ε)).indicator (fun v : ℝ => ‖H (v : ℂ)‖) (u + 2 * ε) := by
            ext u
            by_cases hu : u ≤ -R
            · have hv : u + 2 * ε ≤ -R + 2 * ε := by linarith
              rw [indicator_of_mem hu, indicator_of_mem hv]
            · have hv : ¬ (u + 2 * ε ≤ -R + 2 * ε) := by linarith
              rw [indicator_of_notMem hu, indicator_of_notMem hv]
          rw [hind]
          exact integral_add_right_eq_self
            (fun v : ℝ => (Iic (-R + 2 * ε)).indicator (fun x => ‖H (x : ℂ)‖) v) (2 * ε)
        have hsub1 : (∫ v in Iic (-R + 2 * ε), ‖H (v : ℂ)‖) ≤ ∫ v in Iic (-R + 2), ‖H (v : ℂ)‖ :=
          setIntegral_mono_set hH.2.1.norm.integrableOn
            (Eventually.of_forall fun _ => norm_nonneg _)
            (Eventually.of_forall fun v (hv : v ≤ -R + 2 * ε) => by
              change v ≤ -R + 2; linarith [hε.2])
        have hsub2 : (∫ u in Iic (-R), ‖H (u : ℂ)‖) ≤ ∫ v in Iic (-R + 2), ‖H (v : ℂ)‖ :=
          setIntegral_mono_set hH.2.1.norm.integrableOn
            (Eventually.of_forall fun _ => norm_nonneg _)
            (Eventually.of_forall fun v (hv : v ≤ -R) => by
              change v ≤ -R + 2; linarith)
        rw [hshift_eq] at hmono
        linarith
      have hwin_lt' : (∫ u in Ioc (-R) 0, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) < δ / 2 :=
        (le_abs_self _).trans_lt hwin_lt
      rw [hsplit]
      linarith
    -- Combine `Iic 0` and `Ioi 0`
    have hsum := h_neg_tendsto.add h_pos_tendsto
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    have hint_neg : IntegrableOn
        (fun u : ℝ => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0)) (Iic 0) := by
      refine (((hReg_int_and_l1 ε hε.1.le hε.2).1.sub hH.2.1).norm.integrableOn).congr_fun
        (fun u (hu : u ≤ 0) => ?_) measurableSet_Iic
      dsimp only [Pi.sub_apply]
      rw [max_eq_right hu, mul_zero, Real.exp_zero, mul_one]
    have hint_pos : IntegrableOn
        (fun u : ℝ => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0)) (Ioi 0) := by
      refine ((hpos_maj_int Y hY).const_mul 2).mono' ?_
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
      · refine Continuous.aestronglyMeasurable ?_ |>.restrict
        exact ((hcont_reg_R.comp (continuous_const.prodMk continuous_id)).sub
          (hH.1.continuous.comp Complex.continuous_ofReal)).norm.mul
          (Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const)))
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), max_eq_left hu.le]
        have h1 : ‖airySmoothReg H ε (u : ℂ)‖ ≤
            (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
          simpa [Complex.norm_real, Real.norm_eq_abs] using hReg_growth ε hε.1.le hε.2 (u : ℂ)
        have h2 : ‖H (u : ℂ)‖ ≤ (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
          have hb_u : ‖H (u : ℂ)‖ ≤ C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
            simpa [Complex.norm_real, Real.norm_eq_abs] using hb₀ (u : ℂ)
          exact hb_u.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC₀_nn hK_ge1) (by positivity))
            (airyEnv_pos _).le)
        calc ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * u)
            ≤ (‖airySmoothReg H ε (u : ℂ)‖ + ‖H (u : ℂ)‖) * Real.exp (Y * u) :=
              mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
          _ ≤ 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)) * Real.exp (Y * u) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
          _ = 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)) := by ring
    have hdisj0 : Disjoint (Iic (0 : ℝ)) (Ioi (0 : ℝ)) :=
      Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
    exact (setIntegral_union hdisj0 measurableSet_Ioi hint_neg hint_pos).symm.trans
      (by rw [Iic_union_Ioi, setIntegral_univ])
  · intro ε hε
    exact (hReg_int_and_l1 ε hε.1.le hε.2).2
  · -- Part 4b: `(eq:al-shift-bound)`
    intro s hs ε hε y hy
    have hcl_ε : InAiryClass (airySmoothReg H ε) :=
      ⟨hReg_diff ε, (hReg_int_and_l1 ε hε.1.le hε.2).1,
        ⟨C₀ * K_shift, ν₀, by positivity, hReg_growth ε hε.1.le hε.2⟩,
        hReg_im_zero ε⟩
    have hshift_lap : airyLaplace (fun u => (airySmoothReg H ε ((u + s : ℝ) : ℂ)).re) y =
        Real.exp (-s * y) * airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y := by
      unfold airyLaplace
      have hlin : ∀ u : ℝ, (airySmoothReg H ε ((u + s : ℝ) : ℂ)).re * Real.exp (y * u) =
          Real.exp (-s * y) *
            ((airySmoothReg H ε ((u + s : ℝ) : ℂ)).re * Real.exp (y * (u + s))) := by
        intro u
        rw [mul_comm (Real.exp (-s * y)), mul_assoc, ← Real.exp_add]
        congr 2; ring
      simp_rw [hlin]
      rw [integral_const_mul, integral_add_right_eq_self
        (fun v : ℝ => (airySmoothReg H ε (v : ℂ)).re * Real.exp (y * v)) s]
      ring
    have hub1 : airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y ≤
        ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖ :=
      airyLaplace_re_le_l1 hcl_ε hy
    have hub2 : -airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y ≤
        ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖ := by
      have hneg := airyLaplace_re_le_l1 hcl_ε.neg hy
      have heq_neg : airyLaplace (fun u => ((-airySmoothReg H ε (u : ℂ)).re)) y =
          -airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y := by
        unfold airyLaplace
        simp only [Complex.neg_re, neg_mul, integral_neg, mul_neg]
      have hnorm_neg : (∫ u : ℝ, ‖-airySmoothReg H ε (u : ℂ)‖) =
          ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖ := by simp
      rwa [heq_neg, hnorm_neg] at hneg
    have hl1_le := (hReg_int_and_l1 ε hε.1.le hε.2).2
    rw [hshift_lap, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, hub1.trans hl1_le⟩)
      (Real.exp_pos _).le

/-- info: 'FormalResearch.SignUncertainty.lem_al_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_al_smooth

/-! ### Section 3: Hermite--Airy Rational Approximation (`lem:al-hermite-approx`) -/

/-- Monotonicity of `Ai'(x)² - x Ai(x)²` gives the uniform floor `Ai'(a₁)² ≤ Ai'(a_{n+1})²`. -/
lemma airyAi'_airyZ_sq_ge_zero (n : ℕ) :
    airyAi' (airyZ 0) ^ 2 ≤ airyAi' (airyZ n) ^ 2 := by
  let E : ℝ → ℝ := fun x => airyAi' x ^ 2 - x * airyAi x ^ 2
  have hdE : ∀ x : ℝ, HasDerivAt E (-(airyAi x ^ 2)) x := fun x => by
    have hA := hasDerivAt_airyAi x
    have hB := hasDerivAt_airyAi' x
    have h1 : HasDerivAt (fun t => airyAi' t ^ 2) (2 * airyAi' x * (x * airyAi x)) x :=
      (hB.pow 2).congr_deriv (by ring)
    have h2 : HasDerivAt (fun t => t * airyAi t ^ 2)
        (1 * airyAi x ^ 2 + x * (2 * airyAi x * airyAi' x)) x :=
      (hasDerivAt_id' x).mul ((hA.pow 2).congr_deriv (by ring))
    exact (h1.sub h2).congr_deriv (by ring)
  have hanti : Antitone E := antitone_of_deriv_nonpos
    (fun x => (hdE x).differentiableAt)
    (fun x => by rw [(hdE x).deriv]; linarith [sq_nonneg (airyAi x)])
  have hle := hanti (airyZ_anti (Nat.zero_le n))
  have hz0 : airyAi (airyZ 0) = 0 := airyAi_airyZero 1
  have hzn : airyAi (airyZ n) = 0 := airyAi_airyZero (n + 1)
  dsimp [E] at hle
  rw [hz0, hzn] at hle
  linarith

/-- Because `Ai''(a_{n+1}) = a_{n+1} Ai(a_{n+1}) = 0`, the Airy cardinal `k_n(z) = Ai(z)/(z - a_{n+1})`
has zero first derivative at its own node `a_{n+1}`. -/
lemma deriv_airyCardinal_same (n : ℕ) : deriv (airyCardinal n) (airyZ n : ℂ) = 0 := by
  set a : ℂ := (airyZ n : ℂ)
  have hmul : ∀ z : ℂ, (z - a) * airyCardinal n z = airyAiC z := fun z => by
    by_cases hz : z = a
    · subst hz; simp [a, airyAiC_airyZ]
    · rw [airyCardinal_of_ne n hz, mul_div_cancel₀ _ (sub_ne_zero.mpr hz)]
  have hd1 : ∀ z : ℂ, deriv airyAiC z = airyCardinal n z + (z - a) * deriv (airyCardinal n) z := by
    intro z
    have h1 : HasDerivAt (fun w : ℂ => (w - a) * airyCardinal n w)
        (1 * airyCardinal n z + (z - a) * deriv (airyCardinal n) z) z :=
      ((hasDerivAt_id' z).sub_const a).mul ((differentiable_airyCardinal n z).hasDerivAt)
    rw [funext hmul] at h1
    have hd_eq := h1.deriv
    rwa [one_mul] at hd_eq
  have hd_card2 : DifferentiableAt ℂ (deriv (airyCardinal n)) a :=
    (((differentiable_airyCardinal n).contDiff (n := (2 : ℕ))).differentiable_iteratedDeriv' 1 a)
      |>.congr_of_eventuallyEq (Eventually.of_forall fun z => congrFun iteratedDeriv_one.symm z)
  have hd2_rhs : HasDerivAt (fun z : ℂ => airyCardinal n z + (z - a) * deriv (airyCardinal n) z)
      (2 * deriv (airyCardinal n) a) a := by
    have hp1 := (differentiable_airyCardinal n a).hasDerivAt
    have hp2 := ((hasDerivAt_id' a).sub_const a).mul hd_card2.hasDerivAt
    exact (hp1.add hp2).congr_deriv (by ring)
  have hd2_lhs : HasDerivAt (deriv airyAiC) 0 a := by
    have h := hasDerivAt_deriv_airyAiC a
    rw [show a * airyAiC a = 0 by simp [a, airyAiC_airyZ]] at h
    exact h
  rw [← funext hd1] at hd2_rhs
  have heq := hd2_rhs.unique hd2_lhs
  exact (mul_eq_zero.mp heq).resolve_left two_ne_zero

private lemma airyCardinal_at_airyZ (n m : ℕ) :
    airyCardinal n (airyZ m : ℂ) = if n = m then (airyAi' (airyZ m) : ℂ) else 0 := by
  split_ifs with hnm
  · subst hnm; exact airyCardinal_same_eq_airyAi' n
  · have hne : (airyZ m : ℂ) ≠ (airyZ n : ℂ) := fun h =>
      hnm (airyZ_injective (Complex.ofReal_injective h.symm))
    rw [airyCardinal_of_ne n hne, airyAiC_airyZ, zero_div]

private lemma airySeedG_at_airyZ (n m : ℕ) :
    airySeedG n (airyZ m : ℂ) = if n = m then ((airyAi' (airyZ m) ^ 2 : ℝ) : ℂ) else 0 := by
  unfold airySeedG
  rw [airyCardinal_at_airyZ]
  split_ifs with hnm
  · push_cast; rfl
  · simp

private lemma airySeedF_at_airyZ (n m : ℕ) : airySeedF n (airyZ m : ℂ) = 0 := by
  unfold airySeedF
  rw [airyAiC_airyZ, zero_mul]

private lemma deriv_airySeedG_at_airyZ (n m : ℕ) : deriv (airySeedG n) (airyZ m : ℂ) = 0 := by
  have hd : HasDerivAt (airySeedG n)
      (2 * airyCardinal n (airyZ m : ℂ) * deriv (airyCardinal n) (airyZ m : ℂ)) (airyZ m : ℂ) := by
    unfold airySeedG
    exact (((differentiable_airyCardinal n (airyZ m : ℂ)).hasDerivAt.pow 2).congr_deriv (by ring))
  rw [hd.deriv, airyCardinal_at_airyZ]
  split_ifs with hnm
  · subst hnm; rw [deriv_airyCardinal_same, mul_zero]
  · simp

private lemma deriv_airySeedF_at_airyZ (n m : ℕ) :
    deriv (airySeedF n) (airyZ m : ℂ) =
      if n = m then ((airyAi' (airyZ m) ^ 2 : ℝ) : ℂ) else 0 := by
  have hd : HasDerivAt (airySeedF n)
      (deriv airyAiC (airyZ m : ℂ) * airyCardinal n (airyZ m : ℂ) +
        airyAiC (airyZ m : ℂ) * deriv (airyCardinal n) (airyZ m : ℂ)) (airyZ m : ℂ) := by
    unfold airySeedF
    exact (differentiable_airyAiC (airyZ m : ℂ)).hasDerivAt.mul
      ((differentiable_airyCardinal n (airyZ m : ℂ)).hasDerivAt)
  rw [hd.deriv, airyAiC_airyZ, zero_mul, add_zero, deriv_airyAiC_ofReal, airyCardinal_at_airyZ]
  split_ifs with hnm
  · push_cast; ring
  · simp

/-- Single `n`-th Hermite--Airy term `[F(a_{n+1}) g_{n+1}(z) + F'(a_{n+1}) f_{n+1}(z)] / Ai'(a_{n+1})²`
(`(eq:al-hermite)`). -/
noncomputable def airyHermiteTerm (F : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ((((F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) * airySeedG n z) +
    ((((deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) * airySeedF n z)

/-- `N`-th partial sum `F_N` of the Hermite--Airy expansion `(eq:al-hermite)`. -/
noncomputable def airyHermitePartialSum (F : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, airyHermiteTerm F n z

/-- Rapid coefficient summability for `F ∈ 𝒢 ∩ 𝓢(ℝ)`. -/
private lemma airyHermite_coeff_summable {F : ℂ → ℂ} {S_F : SchwartzMap ℝ ℝ}
    (hSF : ∀ u : ℝ, S_F u = (F (u : ℂ)).re)
    (hderiv_SF : ∀ u : ℝ, deriv (S_F : ℝ → ℝ) u = (deriv F (u : ℂ)).re) (M : ℕ) :
    Summable (fun n : ℕ => |airyZ n| ^ M *
      (|(F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2| +
       |(deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2|)) := by
  have hAi'0_pos : 0 < airyAi' (airyZ 0) ^ 2 :=
    sq_pos_of_ne_zero (airyAi'_airyZ_ne_zero 0)
  have hcoeff_decay : ∀ K_ord : ℕ, ∃ K_M : ℝ, 0 ≤ K_M ∧
      ∀ n : ℕ, |airyZ n| ^ K_ord *
        (|(F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2| +
         |(deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2|) ≤ K_M := by
    intro K_ord
    obtain ⟨C0, hC0_pos, hC0⟩ := S_F.decay K_ord 0
    obtain ⟨C1, hC1_pos, hC1⟩ := S_F.decay K_ord 1
    refine ⟨(C0 + C1) / airyAi' (airyZ 0) ^ 2, by positivity, fun n => ?_⟩
    have h0 := hC0 (airyZ n)
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
      Real.norm_eq_abs, hSF (airyZ n)] at h0
    have h1 := hC1 (airyZ n)
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
      Real.norm_eq_abs, hderiv_SF (airyZ n)] at h1
    have hden_ge := airyAi'_airyZ_sq_ge_zero n
    have hden_pos : 0 < airyAi' (airyZ n) ^ 2 := lt_of_lt_of_le hAi'0_pos hden_ge
    rw [abs_div, abs_div, abs_of_pos hden_pos, ← add_div, ← mul_div_assoc, mul_add]
    exact div_le_div₀ (by positivity) (add_le_add h0 h1) hAi'0_pos hden_ge
  obtain ⟨K, hK_nn, hK⟩ := hcoeff_decay (M + 2)
  refine (summable_airyZ_inv_sq.mul_left K).of_nonneg_of_le (fun _ => by positivity) fun n => ?_
  have h1 := hK n
  rw [pow_add, sq_abs] at h1
  set c_n := |(F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2| +
    |(deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2|
  calc |airyZ n| ^ M * c_n
      = (|airyZ n| ^ M * (airyZ n) ^ 2 * c_n) * ((airyZ n) ^ 2)⁻¹ := by
        have hne0 : airyZ n ≠ 0 := (airyZ_neg n).ne
        field_simp [hne0]
    _ ≤ K * ((airyZ n) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

/-- Core expansion and derivative-quadrature step of `lem:al-hermite-approx`:
proves `(eq:al-hermite)` on all of `ℂ` via `dslope`-twice, good circles, and Maximum Modulus,
together with `∑ F'(a_n)/Ai'(a_n)² = 0` and local compact-ball summable majorants. -/
private lemma airyHermite_quadrature_and_expansion {F : ℂ → ℂ} (hF : InAiryClass F)
    (hF_im : ∀ u : ℝ, (F (u : ℂ)).im = 0)
    {S_F : SchwartzMap ℝ ℝ} (hSF : ∀ u : ℝ, S_F u = (F (u : ℂ)).re) :
    (∀ z : ℂ, HasSum (fun n : ℕ => airyHermiteTerm F n z) (F z)) ∧
    HasSum (fun n : ℕ => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2) 0 ∧
    (∀ R : ℝ, 1 ≤ R → ∃ u_R : ℕ → ℝ, Summable u_R ∧
      ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) R, ‖airyHermiteTerm F n z‖ ≤ u_R n) := by
  have hF_ofReal : ∀ u : ℝ, F (u : ℂ) = (S_F u : ℂ) := fun u => by
    apply Complex.ext
    · simp [hSF u]
    · simp [hF_im u]
  have hderiv_SF : ∀ u : ℝ, deriv (S_F : ℝ → ℝ) u = (deriv F (u : ℂ)).re := fun u => by
    have h1 := iteratedDeriv_re_of_differentiable hF.1 1 u
    rw [iteratedDeriv_one, iteratedDeriv_one] at h1
    have hfun : (fun t : ℝ => (F (t : ℂ)).re) = (S_F : ℝ → ℝ) := funext fun t => (hSF t).symm
    rwa [hfun] at h1
  have hderiv_F_ofReal : ∀ u : ℝ, deriv F (u : ℂ) = ((deriv (S_F : ℝ → ℝ) u : ℝ) : ℂ) := fun u => by
    have hd1 : HasDerivAt (fun t : ℝ => F (t : ℂ)) (deriv F (u : ℂ)) u :=
      (hF.1 (u : ℂ)).hasDerivAt.comp_ofReal
    have hd2 : HasDerivAt (fun t : ℝ => (S_F t : ℂ)) ((deriv (S_F : ℝ → ℝ) u : ℝ) : ℂ) u :=
      S_F.differentiableAt.hasDerivAt.ofReal_comp
    rw [funext hF_ofReal] at hd1
    exact hd1.unique hd2
  set cG : ℕ → ℝ := fun n => (F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cF : ℕ → ℝ := fun n => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cAbs : ℕ → ℝ := fun n => |cG n| + |cF n|
  have hcoeff_summable : ∀ M : ℕ, Summable (fun n : ℕ => |airyZ n| ^ M * cAbs n) :=
    airyHermite_coeff_summable hSF hderiv_SF
  -- 1. Quadrature for `deriv F`: `HasSum cF 0`
  have hcF_hasSum_zero : HasSum cF 0 := by
    obtain ⟨C₀, ν₀, hC₀_nn, hb₀⟩ := hF.2.2.1
    have hdF_diff : Differentiable ℂ (deriv F) := by
      simpa [iteratedDeriv_one] using
        (hF.1.contDiff (n := (2 : ℕ))).differentiable_iteratedDeriv' 1
    have hdF_bd := deriv_inAiryClass_bound hF.1 hC₀_nn hb₀
    obtain ⟨D0, _, hD0⟩ := S_F.decay 0 1
    obtain ⟨D2, _, hD2⟩ := S_F.decay 2 1
    have hdSF_int : Integrable (deriv (S_F : ℝ → ℝ)) := by
      have hdom : Integrable (fun x : ℝ => (D0 + D2) * (1 + x ^ 2)⁻¹) :=
        integrable_inv_one_add_sq.const_mul (D0 + D2)
      refine hdom.mono' ((S_F.smooth (⊤ : ℕ∞)).iterate_deriv 1 |>.continuous.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      have b0 := hD0 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
        Real.norm_eq_abs, pow_zero, one_mul] at b0
      have b2 := hD2 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
        Real.norm_eq_abs, sq_abs] at b2
      rw [Real.norm_eq_abs, le_mul_inv_iff₀ (by positivity)]
      nlinarith [abs_nonneg (deriv (S_F : ℝ → ℝ) x)]
    have hdF_int : Integrable (fun x : ℝ => deriv F (x : ℂ)) := by
      simp_rw [hderiv_F_ofReal]
      exact hdSF_int.ofReal
    obtain ⟨B1, hB1_pos, hB1⟩ := S_F.decay 1 0
    have hint_dSF_zero : (∫ x : ℝ, deriv (S_F : ℝ → ℝ) x) = 0 := by
      have ht_top : Tendsto (S_F : ℝ → ℝ) atTop (𝓝 0) := by
        have hinv : Tendsto (fun x : ℝ => B1 * x⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_inv_atTop_zero.const_mul B1
        refine squeeze_zero_norm' ?_ hinv
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        have hb := hB1 x
        rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
          pow_one, abs_of_pos hx] at hb
        exact (le_mul_inv_iff₀' hx).mpr (by linarith)
      have ht_bot : Tendsto (S_F : ℝ → ℝ) atBot (𝓝 0) := by
        have hinv : Tendsto (fun x : ℝ => B1 * (-x)⁻¹) atBot (𝓝 0) := by
          have h1 : Tendsto (fun y : ℝ => B1 * y⁻¹) atTop (𝓝 0) := by
            simpa using tendsto_inv_atTop_zero.const_mul B1
          exact h1.comp tendsto_neg_atBot_atTop
        refine squeeze_zero_norm' ?_ hinv
        filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
        have hb := hB1 x
        rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
          pow_one, abs_of_neg hx] at hb
        have hnx : 0 < -x := neg_pos.mpr hx
        exact (le_mul_inv_iff₀' hnx).mpr (by linarith)
      have h1 := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
        (fun x _ => S_F.differentiableAt.hasDerivAt) hdSF_int.integrableOn ht_top
      have h2 := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'
        (fun x _ => S_F.differentiableAt.hasDerivAt) hdSF_int.integrableOn ht_bot
      have hdisj0 : Disjoint (Iic (0 : ℝ)) (Ioi (0 : ℝ)) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
      rw [← setIntegral_univ, ← Iic_union_Ioi,
        setIntegral_union hdisj0 measurableSet_Ioi
          hdSF_int.integrableOn hdSF_int.integrableOn, h1, h2]
      ring
    have hq := airyQ_hasSum_unc hdF_diff hdF_int (by positivity) hdF_bd
    have hre := hq.map Complex.reCLM.toAddMonoidHom Complex.continuous_re
    change HasSum (fun n : ℕ => (deriv F (airyZ n : ℂ) / (deriv airyAiC (airyZ n : ℂ)) ^ 2).re)
      (∫ x : ℝ, deriv F (x : ℂ)).re at hre
    have hint_re : (∫ x : ℝ, deriv F (x : ℂ)).re = ∫ x : ℝ, deriv (S_F : ℝ → ℝ) x := by
      refine (integral_re hdF_int).symm.trans ?_
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact (hderiv_SF x).symm
    rw [hint_re, hint_dSF_zero] at hre
    refine hre.congr_fun fun n => ?_
    rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  -- 2. Local uniform majorant on every `closedBall (0 : ℂ) R` (`R ≥ 1`)
  have hball_maj : ∀ R : ℝ, 1 ≤ R → ∃ u_R : ℕ → ℝ, Summable u_R ∧
      ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) R, ‖airyHermiteTerm F n z‖ ≤ u_R n := by
    intro R _
    obtain ⟨M_Ai, hM_Ai⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      differentiable_airyAiC.continuous.continuousOn
    set B_Ai : ℝ := max M_Ai 0
    have hterm_cont : ∀ n : ℕ, Continuous (airyHermiteTerm F n) := fun n => by
      unfold airyHermiteTerm airySeedG airySeedF
      exact (continuous_const.mul ((differentiable_airyCardinal n).continuous.pow 2)).add
        (continuous_const.mul (differentiable_airyAiC.continuous.mul
          (differentiable_airyCardinal n).continuous))
    choose B_n hB_n using fun n : ℕ =>
      (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn (hterm_cont n).continuousOn
    let u_R : ℕ → ℝ := fun n =>
      if R + 1 ≤ -airyZ n then B_Ai ^ 2 * cAbs n else max (B_n n) 0
    have hu_sum : Summable u_R := by
      have hbase : Summable (fun n : ℕ => B_Ai ^ 2 * cAbs n) := by
        simpa [pow_zero, one_mul] using (hcoeff_summable 0).mul_left (B_Ai ^ 2)
      refine hbase.congr_cofinite ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_le_neg_airyZ (R + 1)] with n hn
      simp only [u_R, hn, ↓reduceIte]
    refine ⟨u_R, hu_sum, fun n z hz => ?_⟩
    dsimp [u_R]
    split_ifs with hn
    · have hne : z ≠ (airyZ n : ℂ) := by
        intro heq
        have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZ_neg n)] at h1
        linarith
      have hdist_ge1 : 1 ≤ ‖z - (airyZ n : ℂ)‖ := by
        have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
        have htri : ‖(airyZ n : ℂ)‖ ≤ ‖z - (airyZ n : ℂ)‖ + ‖z‖ := by
          calc ‖(airyZ n : ℂ)‖ = ‖(airyZ n : ℂ) - z + z‖ := by ring_nf
            _ ≤ ‖(airyZ n : ℂ) - z‖ + ‖z‖ := norm_add_le _ _
            _ = ‖z - (airyZ n : ℂ)‖ + ‖z‖ := by rw [norm_sub_rev]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZ_neg n)] at htri
        linarith
      have hAi_le : ‖airyAiC z‖ ≤ B_Ai := (hM_Ai z hz).trans (le_max_left _ _)
      have hcard_le : ‖airyCardinal n z‖ ≤ B_Ai := by
        rw [airyCardinal_of_ne n hne, norm_div]
        exact (div_le_self (norm_nonneg _) hdist_ge1).trans hAi_le
      have hG_le : ‖airySeedG n z‖ ≤ B_Ai ^ 2 := by
        unfold airySeedG; rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hcard_le 2
      have hF_le : ‖airySeedF n z‖ ≤ B_Ai ^ 2 := by
        unfold airySeedF; rw [norm_mul, sq]
        exact mul_le_mul hAi_le hcard_le (norm_nonneg _) (le_max_right _ _)
      unfold airyHermiteTerm
      calc ‖((cG n : ℂ) * airySeedG n z) + ((cF n : ℂ) * airySeedF n z)‖
          ≤ ‖(cG n : ℂ) * airySeedG n z‖ + ‖(cF n : ℂ) * airySeedF n z‖ := norm_add_le _ _
        _ = |cG n| * ‖airySeedG n z‖ + |cF n| * ‖airySeedF n z‖ := by
            simp [Complex.norm_real]
        _ ≤ |cG n| * B_Ai ^ 2 + |cF n| * B_Ai ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hG_le (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hF_le (abs_nonneg _))
        _ = B_Ai ^ 2 * cAbs n := by dsimp [cAbs]; ring
    · exact (hB_n n z hz).trans (le_max_left _ _)
  -- 3. Entirety and termwise derivative of `S z := ∑' n, airyHermiteTerm F n z`
  let S : ℂ → ℂ := fun z => ∑' n : ℕ, airyHermiteTerm F n z
  have hterm_diff : ∀ n : ℕ, Differentiable ℂ (airyHermiteTerm F n) := fun n => by
    unfold airyHermiteTerm airySeedG airySeedF
    exact ((differentiable_const _).mul ((differentiable_airyCardinal n).pow 2)).add
      ((differentiable_const _).mul (differentiable_airyAiC.mul (differentiable_airyCardinal n)))
  have hS_hasSum : ∀ z : ℂ, HasSum (fun n : ℕ => airyHermiteTerm F n z) (S z) := by
    intro z
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj (max ‖z‖ 1) (le_max_right _ _)
    have hz_mem : z ∈ closedBall (0 : ℂ) (max ‖z‖ 1) := by
      rw [mem_closedBall_zero_iff]; exact le_max_left _ _
    exact (Summable.of_norm_bounded hu_R fun n => hbd_R n z hz_mem).hasSum
  have hS_diff : Differentiable ℂ S := by
    intro z₀
    set R : ℝ := max (‖z₀‖ + 1) 1
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj R (le_max_right _ _)
    have hU : IsOpen (ball (0 : ℂ) R) := isOpen_ball
    have hdiffOn := differentiableOn_tsum_of_summable_norm hu_R
      (fun n => (hterm_diff n).differentiableOn) hU
      (fun n w hw => hbd_R n w (ball_subset_closedBall hw))
    have hz₀_mem : z₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith [le_max_left (‖z₀‖ + 1) 1]
    exact hdiffOn.differentiableAt (hU.mem_nhds hz₀_mem)
  have hS_deriv_hasSum : ∀ z₀ : ℂ,
      HasSum (fun n : ℕ => deriv (airyHermiteTerm F n) z₀) (deriv S z₀) := by
    intro z₀
    set R : ℝ := max (‖z₀‖ + 1) 1
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj R (le_max_right _ _)
    have hz₀_mem : z₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith [le_max_left (‖z₀‖ + 1) 1]
    exact hasSum_deriv_of_summable_norm hu_R
      (fun n => (hterm_diff n).differentiableOn) isOpen_ball
      (fun n w hw => hbd_R n w (ball_subset_closedBall hw)) hz₀_mem
  -- 4. `S` matches `F` and `deriv F` at every Airy zero `airyZ m`
  have hS_at_airyZ : ∀ m : ℕ, S (airyZ m : ℂ) = F (airyZ m : ℂ) := by
    intro m
    have hsingle : HasSum (fun n : ℕ => airyHermiteTerm F n (airyZ m : ℂ)) (F (airyZ m : ℂ)) := by
      refine (hasSum_ite_eq m (F (airyZ m : ℂ))).congr_fun fun n => ?_
      unfold airyHermiteTerm
      rw [airySeedG_at_airyZ, airySeedF_at_airyZ, mul_zero, add_zero]
      split_ifs with hnm
      · subst hnm
        have hne : airyAi' (airyZ n) ^ 2 ≠ 0 := pow_ne_zero 2 (airyAi'_airyZ_ne_zero n)
        calc (((F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) *
              ((airyAi' (airyZ n) ^ 2 : ℝ) : ℂ)
            = (((F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 * airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) :=
              (Complex.ofReal_mul _ _).symm
          _ = ((F (airyZ n : ℂ)).re : ℂ) := by rw [div_mul_cancel₀ _ hne]
          _ = F (airyZ n : ℂ) := by rw [← hSF, ← hF_ofReal]
      · simp
    exact (hS_hasSum (airyZ m : ℂ)).unique hsingle
  have hderivS_at_airyZ : ∀ m : ℕ, deriv S (airyZ m : ℂ) = deriv F (airyZ m : ℂ) := by
    intro m
    have hsingle : HasSum (fun n : ℕ => deriv (airyHermiteTerm F n) (airyZ m : ℂ))
        (deriv F (airyZ m : ℂ)) := by
      refine (hasSum_ite_eq m (deriv F (airyZ m : ℂ))).congr_fun fun n => ?_
      have hd_term : deriv (airyHermiteTerm F n) (airyZ m : ℂ) =
          (cG n : ℂ) * deriv (airySeedG n) (airyZ m : ℂ) +
            (cF n : ℂ) * deriv (airySeedF n) (airyZ m : ℂ) := by
        unfold airyHermiteTerm
        exact ((((airySeedG_inAiryClass n).1 (airyZ m : ℂ)).hasDerivAt.const_mul (cG n : ℂ)).add
          (((airySeedF_inAiryClass n).1 (airyZ m : ℂ)).hasDerivAt.const_mul (cF n : ℂ))).deriv
      rw [hd_term, deriv_airySeedG_at_airyZ, mul_zero, zero_add, deriv_airySeedF_at_airyZ]
      split_ifs with hnm
      · subst hnm
        have hne : airyAi' (airyZ n) ^ 2 ≠ 0 := pow_ne_zero 2 (airyAi'_airyZ_ne_zero n)
        dsimp [cF]
        calc (((deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) *
              ((airyAi' (airyZ n) ^ 2 : ℝ) : ℂ)
            = (((deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 *
                airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) := (Complex.ofReal_mul _ _).symm
          _ = ((deriv F (airyZ n : ℂ)).re : ℂ) := by rw [div_mul_cancel₀ _ hne]
          _ = deriv F (airyZ n : ℂ) := by rw [← hderiv_SF, ← hderiv_F_ofReal]
      · simp
    exact (hS_deriv_hasSum (airyZ m : ℂ)).unique hsingle
  -- 5. Entire quotient `Q = (F - S) / Ai²`, good circles, and Maximum Modulus
  have hS_eq_F : ∀ z : ℂ, S z = F z := by
    classical
    let Δ : ℂ → ℂ := fun z => F z - S z
    have hΔ_diff : Differentiable ℂ Δ := hF.1.sub hS_diff
    have hΔ_zero : ∀ m : ℕ, Δ (airyZ m : ℂ) = 0 := fun m =>
      sub_eq_zero.mpr (hS_at_airyZ m).symm
    have hdΔ_zero : ∀ m : ℕ, deriv Δ (airyZ m : ℂ) = 0 := fun m => by
      have hd := ((hF.1 (airyZ m : ℂ)).hasDerivAt.sub (hS_diff (airyZ m : ℂ)).hasDerivAt).deriv
      change deriv Δ (airyZ m : ℂ) = _ at hd
      rw [hd, hderivS_at_airyZ, sub_self]
    let Q : ℂ → ℂ := fun z =>
      if h : ∃ m : ℕ, z = (airyZ m : ℂ) then
        dslope (dslope Δ (airyZ h.choose : ℂ)) (airyZ h.choose : ℂ) z /
          airyCardinal h.choose z ^ 2
      else Δ z / airyAiC z ^ 2
    have hQ_local_eq : ∀ (m : ℕ) {z : ℂ}, z ≠ (airyZ m : ℂ) → airyAiC z ≠ 0 →
        dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ) z / airyCardinal m z ^ 2 =
          Δ z / airyAiC z ^ 2 := by
      intro m z hz hAi
      have hds1 : dslope Δ (airyZ m : ℂ) z = Δ z / (z - (airyZ m : ℂ)) := by
        rw [dslope_of_ne _ hz, slope_def_field, hΔ_zero m, sub_zero]
      have hds1_same : dslope Δ (airyZ m : ℂ) (airyZ m : ℂ) = 0 := by
        rw [dslope_same, hdΔ_zero m]
      have hds2 : dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ) z =
          Δ z / (z - (airyZ m : ℂ)) ^ 2 := by
        rw [dslope_of_ne _ hz, slope_def_field, hds1, hds1_same, sub_zero, div_div, sq]
      rw [hds2, airyCardinal_of_ne m hz, div_pow]
      have hsub_ne : (z - (airyZ m : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hz)
      have hAi2_ne : airyAiC z ^ 2 ≠ 0 := pow_ne_zero 2 hAi
      field_simp [hsub_ne, hAi2_ne]
    have hQ_diff : Differentiable ℂ Q := by
      intro z₀
      by_cases hAi0 : airyAiC z₀ = 0
      · obtain ⟨k, hk1, hkz⟩ := (airyAiC_eq_zero_iff z₀).mp hAi0
        set m : ℕ := k - 1
        have hz₀_eq : z₀ = (airyZ m : ℂ) := by
          rw [hkz]; congr 1; simp [airyZ, m, Nat.sub_add_cancel hk1]
        let U_m : Set ℂ := {z : ℂ | airyCardinal m z ≠ 0}
        have hUm_open : IsOpen U_m :=
          isOpen_ne_fun (differentiable_airyCardinal m).continuous continuous_const
        have hz₀_Um : z₀ ∈ U_m := by
          change airyCardinal m z₀ ≠ 0
          rw [hz₀_eq, airyCardinal_same_eq_airyAi']
          exact Complex.ofReal_ne_zero.mpr (airyAi'_airyZ_ne_zero m)
        have hds_entire : Differentiable ℂ (dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ)) := by
          have hd1 : Differentiable ℂ (dslope Δ (airyZ m : ℂ)) :=
            differentiableOn_univ.mp
              ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hΔ_diff.differentiableOn)
          exact differentiableOn_univ.mp
            ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hd1.differentiableOn)
        have hev : Q =ᶠ[𝓝 z₀] fun z =>
            dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ) z / airyCardinal m z ^ 2 := by
          filter_upwards [hUm_open.mem_nhds hz₀_Um] with z hz_Um
          change airyCardinal m z ≠ 0 at hz_Um
          by_cases hzm : z = (airyZ m : ℂ)
          · dsimp only [Q]
            split_ifs with hex
            · have hchoose : hex.choose = m :=
                airyZ_injective (Complex.ofReal_injective (hex.choose_spec.symm.trans hzm))
              rw [hchoose]
            · exact absurd ⟨m, hzm⟩ hex
          · have hno : ¬ ∃ m' : ℕ, z = (airyZ m' : ℂ) := by
              rintro ⟨m', rfl⟩
              have hm' : m' ≠ m := fun heq => hzm (heq ▸ rfl)
              have hc0 : airyCardinal m (airyZ m' : ℂ) = 0 := by
                rw [airyCardinal_at_airyZ]
                split_ifs with h1
                exact absurd h1.symm hm'
              exact hz_Um hc0
            have hAi_ne : airyAiC z ≠ 0 := by
              intro h0
              obtain ⟨k', hk'1, hk'z⟩ := (airyAiC_eq_zero_iff z).mp h0
              exact hno ⟨k' - 1, by rw [hk'z]; simp [airyZ, Nat.sub_add_cancel hk'1]⟩
            simp only [Q, hno, ↓reduceDIte]
            exact (hQ_local_eq m hzm hAi_ne).symm
        refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
        exact (hds_entire z₀).div ((differentiable_airyCardinal m z₀).pow 2)
          (pow_ne_zero 2 hz₀_Um)
      · have hopen : IsOpen {z : ℂ | airyAiC z ≠ 0} :=
          isOpen_ne_fun differentiable_airyAiC.continuous continuous_const
        have hev : Q =ᶠ[𝓝 z₀] fun z => Δ z / airyAiC z ^ 2 := by
          filter_upwards [hopen.mem_nhds hAi0] with z hz
          have hno : ¬ ∃ m : ℕ, z = (airyZ m : ℂ) := by
            rintro ⟨m, rfl⟩
            exact hz (airyAiC_airyZ m)
          simp only [Q, hno, ↓reduceDIte]
        refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
        exact (hΔ_diff z₀).div ((differentiable_airyAiC z₀).pow 2) (pow_ne_zero 2 hAi0)
    have hΔ_eq_mul : ∀ z : ℂ, Δ z = airyAiC z ^ 2 * Q z := by
      intro z
      dsimp only [Q]
      split_ifs with hex
      · obtain ⟨m, rfl⟩ := hex
        rw [hΔ_zero m, airyAiC_airyZ m, zero_pow two_ne_zero, zero_mul]
      · have hAi_ne : airyAiC z ≠ 0 := by
          intro h0
          obtain ⟨k, hk1, hkz⟩ := (airyAiC_eq_zero_iff z).mp h0
          exact hex ⟨k - 1, by rw [hkz]; simp [airyZ, Nat.sub_add_cancel hk1]⟩
        exact (mul_div_cancel₀ (Δ z) (pow_ne_zero 2 hAi_ne)).symm
    obtain ⟨C₀, ν₀, hC₀_nn, hb₀⟩ := hF.2.2.1
    have hz2F_int : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * F (x : ℂ)) := by
      obtain ⟨E2, _, hE2⟩ := S_F.decay 2 0
      obtain ⟨E4, _, hE4⟩ := S_F.decay 4 0
      have hdom : Integrable (fun x : ℝ => (E2 + E4) * (1 + x ^ 2)⁻¹) :=
        integrable_inv_one_add_sq.const_mul (E2 + E4)
      refine hdom.mono'
        (((continuous_ofReal.pow 2).mul (hF.1.continuous.comp continuous_ofReal)).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      have b2 := hE2 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
        Real.norm_eq_abs, sq_abs] at b2
      have b4 := hE4 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
        Real.norm_eq_abs, show |x| ^ 4 = x ^ 2 * x ^ 2 by rw [← sq_abs]; ring] at b4
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        hF_ofReal x, Complex.norm_real, Real.norm_eq_abs, le_mul_inv_iff₀ (by positivity)]
      nlinarith [abs_nonneg (S_F x), sq_nonneg x]
    have hz2F_growth : ∀ z : ℂ, ‖z ^ 2 * F z‖ ≤ C₀ * (1 + ‖z‖) ^ (ν₀ + 2) * airyEnv z := by
      intro z
      have hz_pos : 0 < 1 + ‖z‖ := by positivity
      have h1 : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact pow_le_pow_left₀ (norm_nonneg z) (by linarith) 2
      rw [norm_mul, norm_pow]
      calc ‖z‖ ^ 2 * ‖F z‖
          ≤ (1 + ‖z‖) ^ (2 : ℝ) * (C₀ * (1 + ‖z‖) ^ ν₀ * airyEnv z) :=
            mul_le_mul h1 (hb₀ z) (norm_nonneg _) (by positivity)
        _ = C₀ * ((1 + ‖z‖) ^ ν₀ * (1 + ‖z‖) ^ (2 : ℝ)) * airyEnv z := by ring
        _ = C₀ * (1 + ‖z‖) ^ (ν₀ + 2) * airyEnv z := by rw [← Real.rpow_add hz_pos]
    obtain ⟨C_half, hChalf_nn, hChalf⟩ := airyQ_mem_half
      ((differentiable_id.pow 2).mul hF.1) hz2F_int hC₀_nn hz2F_growth
    have hsum_good : Summable (fun n : ℕ => (2 + 80000 * |airyZ n| ^ 2) * cAbs n) := by
      have hs0 := (hcoeff_summable 0).mul_left 2
      have hs2 := (hcoeff_summable 2).mul_left 80000
      refine (hs0.add hs2).congr fun n => ?_
      simp [pow_zero]; ring
    set M_good : ℝ := ∑' n : ℕ, (2 + 80000 * |airyZ n| ^ 2) * cAbs n
    have hMgood_nn : 0 ≤ M_good := tsum_nonneg fun _ => by positivity
    have hQ_zero : ∀ z₀ : ℂ, Q z₀ = 0 := by
      intro z₀
      set K_tot : ℝ := 50 * π * C_half + M_good
      have hnorm_zero : ‖Q z₀‖ ≤ 0 := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        rw [zero_add]
        set k : ℕ := max 10 (max (⌈‖z₀‖⌉₊ + 1) (⌈K_tot / δ⌉₊ + 1))
        have hk10 : 10 ≤ k := le_max_left _ _
        obtain ⟨r, hr_lo, hr_hi, hgood⟩ := good_circle_exists k hk10
        have hr_ge10 : 10 ≤ r := by
          have : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk10
          linarith
        have hr_pos : 0 < r := by linarith
        have hz₀_in : z₀ ∈ ball (0 : ℂ) r := by
          rw [mem_ball_zero_iff]
          have hk_z : ⌈‖z₀‖⌉₊ + 1 ≤ k := (le_max_left _ _).trans (le_max_right _ _)
          have h1 : ‖z₀‖ < (k : ℝ) := by
            calc ‖z₀‖ ≤ (⌈‖z₀‖⌉₊ : ℝ) := Nat.le_ceil _
              _ < (k : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk_z)
          linarith
        have hdist_zeros : ∀ n : ℕ,
            (1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ)) ≤ |-r - airyZ n| := by
          intro n
          by_cases h1 : 1 ≤ |-r - airyZ n|
          · have hrp : (1 + r) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
              simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith)
                (by norm_num : -(1 / 2 : ℝ) ≤ 0)
            linarith
          · push Not at h1
            have hgood_neg := hgood ((-r : ℝ) : ℂ) (by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hr_pos])
            have henv_neg : airyEnv ((-r : ℝ) : ℂ) = 1 :=
              airyEnv_ofReal_neg (by linarith)
            rw [henv_neg, mul_one, airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs,
              sq_abs] at hgood_neg
            have hAi_lb : (1 / 10) * (1 + r) ^ (-(1 / 4 : ℝ)) ≤ |airyAi (-r)| := by
              have hsq : ((1 / 10) * (1 + r) ^ (-(1 / 4 : ℝ))) ^ 2 ≤ airyAi (-r) ^ 2 := by
                refine le_trans ?_ hgood_neg
                rw [mul_pow, ← Real.rpow_natCast ((1 + r) ^ _),
                  ← Real.rpow_mul (by linarith : 0 ≤ 1 + r)]
                have hpi4 : 25 * π ≤ 100 := by linarith [Real.pi_lt_four]
                have hdiv : (1 / 10 : ℝ) ^ 2 ≤ 1 / (25 * π) := by
                  rw [show (1 / 10 : ℝ) ^ 2 = 1 / 100 by norm_num]
                  exact one_div_le_one_div_of_le (by positivity) hpi4
                norm_num at *
                exact mul_le_mul_of_nonneg_right hdiv (by positivity)
              have hnn : 0 ≤ (1 / 10) * (1 + r) ^ (-(1 / 4 : ℝ)) := by positivity
              nlinarith [sq_abs (airyAi (-r)), abs_nonneg (airyAi (-r))]
            let lo : ℝ := min (-r) (airyZ n)
            let hi : ℝ := max (-r) (airyZ n)
            have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
              (s := Icc lo hi) (f := airyAi)
              (C := 10 * (1 + r) ^ (1 / 4 : ℝ))
              (fun t _ => (hasDerivAt_airyAi t).differentiableAt)
              (fun t ht => by
                rw [(hasDerivAt_airyAi t).deriv, Real.norm_eq_abs]
                have ht_neg : t ≤ 0 := by
                  have : hi ≤ 0 := max_le (by linarith) (airyZ_neg n).le
                  exact ht.2.trans this
                have ht_abs : |t| ≤ r + 1 := by
                  rw [abs_of_nonpos ht_neg]
                  have hlo_ge : -(r + 1) ≤ lo := by
                    refine le_min (by linarith) ?_
                    have h1_b := abs_le.mp h1.le
                    linarith [h1_b.1, h1_b.2]
                  linarith [ht.1]
                have hb_d := (airyAi_and_deriv_neg_bounds ht_neg).2
                refine hb_d.trans ?_
                have h16 : 1 + |t| ≤ 16 * (1 + r) := by linarith
                calc 5 * (1 + |t|) ^ (1 / 4 : ℝ)
                    ≤ 5 * (16 * (1 + r)) ^ (1 / 4 : ℝ) :=
                      mul_le_mul_of_nonneg_left
                        (Real.rpow_le_rpow (by positivity) h16 (by norm_num)) (by norm_num)
                  _ = 5 * (16 ^ (1 / 4 : ℝ) * (1 + r) ^ (1 / 4 : ℝ)) := by
                      rw [Real.mul_rpow (by norm_num) (by positivity)]
                  _ = 10 * (1 + r) ^ (1 / 4 : ℝ) := by
                      have h16_4 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
                        rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num,
                          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
                        norm_num
                      rw [h16_4]; ring)
              (convex_Icc lo hi)
              ⟨min_le_right _ _, le_max_right _ _⟩
              ⟨min_le_left _ _, le_max_left _ _⟩
            have hz_zero : airyAi (airyZ n) = 0 := airyAi_airyZero (n + 1)
            rw [hz_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
            have hprod := hAi_lb.trans hmvt
            have hrpos14 : 0 < 10 * (1 + r) ^ (1 / 4 : ℝ) := by positivity
            rw [← div_le_iff₀' hrpos14] at hprod
            have hrhs_eq : ((1 / 10 : ℝ) * (1 + r) ^ (-(1 / 4 : ℝ))) /
                (10 * (1 + r) ^ (1 / 4 : ℝ)) =
                (1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ)) := by
              rw [Real.rpow_neg (by positivity : 0 ≤ 1 + r),
                show (1 / 2 : ℝ) = 1 / 4 + 1 / 4 by norm_num,
                Real.rpow_add (by positivity : 0 < 1 + r)]
              have hp : (1 + r) ^ (1 / 4 : ℝ) ≠ 0 :=
                (Real.rpow_pos_of_pos (by positivity) _).ne'
              field_simp [hp]
              ring
            rwa [hrhs_eq] at hprod
        have hfront : ∀ ζ ∈ frontier (ball (0 : ℂ) r), ‖Q ζ‖ ≤ K_tot / r := by
          intro ζ hζ
          rw [frontier_ball (0 : ℂ) hr_pos.ne', mem_sphere_zero_iff_norm] at hζ
          have hAi_good := hgood ζ hζ
          have hAi_pos : 0 < ‖airyAiC ζ‖ ^ 2 := by
            refine lt_of_lt_of_le ?_ hAi_good
            have := airyEnv_pos ζ
            have : 0 < (1 + r) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
            positivity
          have hAi_ne : airyAiC ζ ≠ 0 := fun h0 => by simp [h0] at hAi_pos
          have hQ_eq : Q ζ = (F ζ - S ζ) / airyAiC ζ ^ 2 := by
            have hno : ¬ ∃ m : ℕ, ζ = (airyZ m : ℂ) := by
              rintro ⟨m, rfl⟩; exact hAi_ne (airyAiC_airyZ m)
            simp only [Q, hno, ↓reduceDIte]
          have hF_div : ‖F ζ / airyAiC ζ ^ 2‖ ≤ (50 * π * C_half) / r := by
            have henv_ζ_pos : 0 < airyEnv ζ := airyEnv_pos ζ
            have hz2 := hChalf ζ
            change ‖ζ ^ 2 * F ζ‖ ≤ C_half * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * airyEnv ζ at hz2
            rw [norm_mul, norm_pow, hζ] at hz2
            have hF_ub : ‖F ζ‖ ≤ C_half * (1 + r) ^ (1 / 2 : ℝ) * airyEnv ζ / r ^ 2 := by
              rw [le_div_iff₀ (sq_pos_of_pos hr_pos)]
              linarith
            rw [norm_div, norm_pow]
            calc ‖F ζ‖ / ‖airyAiC ζ‖ ^ 2
                ≤ (C_half * (1 + r) ^ (1 / 2 : ℝ) * airyEnv ζ / r ^ 2) /
                    (1 / (25 * π) * (1 + r) ^ (-(1 / 2 : ℝ)) * airyEnv ζ) := by
                  refine div_le_div₀ (by positivity) hF_ub ?_ hAi_good
                  have : 0 < (1 + r) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
                  positivity
              _ = 25 * π * C_half * ((1 + r) / r ^ 2) := by
                  have he_ne : (airyEnv ζ) ≠ 0 := (airyEnv_pos ζ).ne'
                  have hr_ne : r ^ 2 ≠ 0 := (sq_pos_of_pos hr_pos).ne'
                  have hpi_ne : π ≠ 0 := Real.pi_pos.ne'
                  have hr12 : (1 + r) ^ (1 / 2 : ℝ) / (1 + r) ^ (-(1 / 2 : ℝ)) = 1 + r := by
                    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + r), div_inv_eq_mul,
                      ← Real.rpow_add (by positivity : 0 < 1 + r)]
                    norm_num
                  calc (C_half * (1 + r) ^ (1 / 2 : ℝ) * airyEnv ζ / r ^ 2) /
                        (1 / (25 * π) * (1 + r) ^ (-(1 / 2 : ℝ)) * airyEnv ζ)
                      = 25 * π * C_half *
                          ((1 + r) ^ (1 / 2 : ℝ) / (1 + r) ^ (-(1 / 2 : ℝ))) / r ^ 2 := by
                        field_simp [he_ne, hr_ne, hpi_ne]
                    _ = 25 * π * C_half * ((1 + r) / r ^ 2) := by rw [hr12]; ring
              _ ≤ (50 * π * C_half) / r := by
                  have h1r : (1 + r) / r ^ 2 ≤ 2 / r := by
                    rw [div_le_div_iff₀ (sq_pos_of_pos hr_pos) hr_pos]
                    nlinarith
                  calc 25 * π * C_half * ((1 + r) / r ^ 2)
                      ≤ 25 * π * C_half * (2 / r) :=
                        mul_le_mul_of_nonneg_left h1r (by positivity)
                    _ = (50 * π * C_half) / r := by ring
          have hS_div : ‖S ζ / airyAiC ζ ^ 2‖ ≤ M_good / r := by
            have hdiv_sum : HasSum (fun n : ℕ => airyHermiteTerm F n ζ / airyAiC ζ ^ 2)
                (S ζ / airyAiC ζ ^ 2) := by
              simpa [div_eq_mul_inv] using (hS_hasSum ζ).mul_right ((airyAiC ζ ^ 2)⁻¹)
            have hterm_le : ∀ n : ℕ, ‖airyHermiteTerm F n ζ / airyAiC ζ ^ 2‖ ≤
                ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r := by
              intro n
              have hdist_ζ : |-r - airyZ n| ≤ ‖ζ - (airyZ n : ℂ)‖ := by
                have htri : |‖ζ‖ - ‖(airyZ n : ℂ)‖| ≤ ‖ζ - (airyZ n : ℂ)‖ :=
                  abs_norm_sub_norm_le ζ (airyZ n : ℂ)
                rw [hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZ_neg n)] at htri
                have heq_abs : |-r - airyZ n| = |r - (-airyZ n)| := by
                  rw [← abs_neg]; ring_nf
                rwa [heq_abs]
              have hd_pos : 0 < ‖ζ - (airyZ n : ℂ)‖ :=
                lt_of_lt_of_le (by positivity) ((hdist_zeros n).trans hdist_ζ)
              have hne_ζ : ζ ≠ (airyZ n : ℂ) := sub_ne_zero.mp (norm_pos_iff.mp hd_pos)
              have hsimp : airyHermiteTerm F n ζ / airyAiC ζ ^ 2 =
                  (cG n : ℂ) / (ζ - (airyZ n : ℂ)) ^ 2 +
                    (cF n : ℂ) / (ζ - (airyZ n : ℂ)) := by
                unfold airyHermiteTerm airySeedG airySeedF
                rw [airyCardinal_of_ne n hne_ζ]
                have hAi2_ne : airyAiC ζ ^ 2 ≠ 0 := pow_ne_zero 2 hAi_ne
                have hsub_ne : ζ - (airyZ n : ℂ) ≠ 0 := sub_ne_zero.mpr hne_ζ
                field_simp [hAi2_ne, hsub_ne]
                rfl
              rw [hsimp]
              have hinv_le : max (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ (‖ζ - (airyZ n : ℂ)‖)⁻¹ ≤
                  (2 + 80000 * |airyZ n| ^ 2) / r := by
                by_cases hcase : |airyZ n| ≤ r / 2
                · have hd_ge : r / 2 ≤ ‖ζ - (airyZ n : ℂ)‖ := by
                    have htri : ‖ζ‖ - ‖(airyZ n : ℂ)‖ ≤ ‖ζ - (airyZ n : ℂ)‖ :=
                      norm_sub_norm_le ζ (airyZ n : ℂ)
                    rw [hζ, Complex.norm_real, Real.norm_eq_abs] at htri
                    linarith
                  have hi1 : (‖ζ - (airyZ n : ℂ)‖)⁻¹ ≤ 2 / r := by
                    rw [← one_div, div_le_div_iff₀ hd_pos hr_pos]
                    linarith
                  have hi2 : (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ ≤ 2 / r := by
                    have hge1 : 1 ≤ ‖ζ - (airyZ n : ℂ)‖ := by linarith
                    have hsq_ge : ‖ζ - (airyZ n : ℂ)‖ ≤ ‖ζ - (airyZ n : ℂ)‖ ^ 2 := by nlinarith
                    exact (inv_anti₀ hd_pos hsq_ge).trans hi1
                  exact (max_le hi2 hi1).trans
                    (div_le_div_of_nonneg_right (by linarith [sq_nonneg |airyZ n|]) hr_pos.le)
                · push Not at hcase
                  have hd_lb := (hdist_zeros n).trans hdist_ζ
                  have h100 : (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ ≤ 10000 * (1 + r) := by
                    have hsq : ((1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ))) ^ 2 ≤
                        ‖ζ - (airyZ n : ℂ)‖ ^ 2 :=
                      pow_le_pow_left₀ (by positivity) hd_lb 2
                    have hlhs : ((1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ))) ^ 2 =
                        (10000 * (1 + r))⁻¹ := by
                      rw [mul_pow, ← Real.rpow_natCast ((1 + r) ^ _),
                        ← Real.rpow_mul (by positivity : 0 ≤ 1 + r)]
                      have hexp_eq : -(1 / 2 : ℝ) * (2 : ℕ) = -1 := by norm_num
                      rw [hexp_eq, Real.rpow_neg_one, mul_inv]
                      norm_num
                      ring
                    rw [hlhs] at hsq
                    exact (inv_le_inv₀ (sq_pos_of_pos hd_pos) (by positivity)).mpr hsq |>.trans_eq
                      (inv_inv _)
                  have h100_1 : (‖ζ - (airyZ n : ℂ)‖)⁻¹ ≤ 10000 * (1 + r) := by
                    by_cases hd1 : 1 ≤ ‖ζ - (airyZ n : ℂ)‖
                    · exact (inv_le_one_of_one_le₀ hd1).trans (by linarith)
                    · push Not at hd1
                      have hsq_le : ‖ζ - (airyZ n : ℂ)‖ ^ 2 ≤ ‖ζ - (airyZ n : ℂ)‖ := by nlinarith
                      exact (inv_anti₀ (sq_pos_of_pos hd_pos) hsq_le).trans h100
                  have hbound_r : 10000 * (1 + r) ≤ (2 + 80000 * |airyZ n| ^ 2) / r := by
                    rw [le_div_iff₀ hr_pos]
                    have hA2 : r ^ 2 < 4 * |airyZ n| ^ 2 := by nlinarith
                    nlinarith
                  exact (max_le h100 h100_1).trans hbound_r
              calc ‖(cG n : ℂ) / (ζ - (airyZ n : ℂ)) ^ 2 + (cF n : ℂ) / (ζ - (airyZ n : ℂ))‖
                  ≤ ‖(cG n : ℂ) / (ζ - (airyZ n : ℂ)) ^ 2‖ +
                      ‖(cF n : ℂ) / (ζ - (airyZ n : ℂ))‖ := norm_add_le _ _
                _ = |cG n| * (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ +
                      |cF n| * (‖ζ - (airyZ n : ℂ)‖)⁻¹ := by
                    simp [div_eq_mul_inv, Complex.norm_real]
                _ ≤ |cG n| * ((2 + 80000 * |airyZ n| ^ 2) / r) +
                      |cF n| * ((2 + 80000 * |airyZ n| ^ 2) / r) :=
                    add_le_add
                      (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hinv_le) (abs_nonneg _))
                      (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hinv_le) (abs_nonneg _))
                _ = ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r := by dsimp [cAbs]; ring
            rw [← hdiv_sum.tsum_eq]
            have hsum_r : Summable (fun n : ℕ => ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r) :=
              hsum_good.div_const r
            calc ‖∑' n : ℕ, airyHermiteTerm F n ζ / airyAiC ζ ^ 2‖
                ≤ ∑' n : ℕ, ‖airyHermiteTerm F n ζ / airyAiC ζ ^ 2‖ :=
                  norm_tsum_le_tsum_norm
                    (hsum_r.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le)
              _ ≤ ∑' n : ℕ, ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r :=
                  Summable.tsum_le_tsum hterm_le
                    (hsum_r.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le) hsum_r
              _ = M_good / r := tsum_div_const
          rw [hQ_eq, sub_div]
          calc ‖F ζ / airyAiC ζ ^ 2 - S ζ / airyAiC ζ ^ 2‖
              ≤ ‖F ζ / airyAiC ζ ^ 2‖ + ‖S ζ / airyAiC ζ ^ 2‖ := norm_sub_le _ _
            _ ≤ (50 * π * C_half) / r + M_good / r := add_le_add hF_div hS_div
            _ = K_tot / r := by dsimp [K_tot]; ring
        have hmax_mod := Complex.norm_le_of_forall_mem_frontier_norm_le
          isBounded_ball hQ_diff.differentiableOn.diffContOnCl hfront (subset_closure hz₀_in)
        refine hmax_mod.trans ?_
        have hk_K : ⌈K_tot / δ⌉₊ + 1 ≤ k := (le_max_right _ _).trans (le_max_right _ _)
        have hKr : K_tot / δ ≤ r := by
          calc K_tot / δ ≤ (⌈K_tot / δ⌉₊ : ℝ) := Nat.le_ceil _
            _ ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_succ_le hk_K)
            _ ≤ r := hr_lo
        rw [div_le_iff₀ hr_pos]
        have := (div_le_iff₀ hδ).mp hKr
        linarith
      exact norm_le_zero_iff.mp hnorm_zero
    intro z
    have h0 : Δ z = 0 := by rw [hΔ_eq_mul z, hQ_zero z, mul_zero]
    exact (sub_eq_zero.mp h0).symm
  exact ⟨fun z => hS_eq_F z ▸ hS_hasSum z, hcF_hasSum_zero, hball_maj⟩

/-- **Lemma `lem:al-hermite-approx`** (`ce_airy_lp_proofs.tex` lines 803–869):
for real-on-`ℝ` `F ∈ 𝒢 ∩ 𝓢(ℝ)`, the Hermite--Airy expansion `(eq:al-hermite)` holds on all of `ℂ`,
`∑ F'(a_n)/Ai'(a_n)² = 0`, and the partial sums `F_N ∈ ℛ_Ai^gen` satisfy (a)–(d). -/
theorem lem_al_hermite_approx {F : ℂ → ℂ} (hF : InAiryClass F)
    (hF_im : ∀ u : ℝ, (F (u : ℂ)).im = 0)
    (hF_schwartz : ∃ S_F : SchwartzMap ℝ ℝ, ∀ u : ℝ, S_F u = (F (u : ℂ)).re) :
    (∀ z : ℂ, HasSum (fun n : ℕ => airyHermiteTerm F n z) (F z)) ∧
    HasSum (fun n : ℕ => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2) 0 ∧
    (∀ N : ℕ, InGenRationalAiry (airyHermitePartialSum F N) ∧
      airyBetaInf (airyHermitePartialSum F N) =
        -∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 ∧
      airyBetaPlus (airyHermitePartialSum F N) =
        ∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2) ∧
    (∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun N z => airyHermitePartialSum F N z) F atTop K) ∧
    Tendsto (fun N : ℕ => ∫ u : ℝ, ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖)
      atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∫ u : ℝ, (airyHermitePartialSum F N (u : ℂ)).re)
      atTop (𝓝 (∫ u : ℝ, (F (u : ℂ)).re)) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, u ≤ 0 →
      (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re - (airyHermitePartialSum F N (u : ℂ)).re| < ε) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, 0 ≤ y →
      (1 + y) ^ (5 / 2 : ℝ) *
        |airyLaplace (fun u => (F (u : ℂ)).re) y -
          airyLaplace (fun u => (airyHermitePartialSum F N (u : ℂ)).re) y| < ε) ∧
    Tendsto (fun N : ℕ => airyBetaInf (airyHermitePartialSum F N)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => airyBetaPlus (airyHermitePartialSum F N)) atTop (𝓝 0) := by
  obtain ⟨S_F, hSF⟩ := hF_schwartz
  have hderiv_SF : ∀ u : ℝ, deriv (S_F : ℝ → ℝ) u = (deriv F (u : ℂ)).re := fun u => by
    have h1 := iteratedDeriv_re_of_differentiable hF.1 1 u
    rw [iteratedDeriv_one, iteratedDeriv_one] at h1
    have hfun : (fun t : ℝ => (F (t : ℂ)).re) = (S_F : ℝ → ℝ) := funext fun t => (hSF t).symm
    rwa [hfun] at h1
  obtain ⟨hF_hasSum, hcF_hasSum_zero, hball_maj⟩ :=
    airyHermite_quadrature_and_expansion hF hF_im hSF
  set cG : ℕ → ℝ := fun n => (F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cF : ℕ → ℝ := fun n => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cAbs : ℕ → ℝ := fun n => |cG n| + |cF n|
  have hcoeff_summable : ∀ M : ℕ, Summable (fun n : ℕ => |airyZ n| ^ M * cAbs n) :=
    airyHermite_coeff_summable hSF hderiv_SF
  -- Partial sums lie in `InGenRationalAiry` with exact `β_∞` and `β_+`
  have hpartial_coeffs : ∀ N : ℕ,
      InGenRationalAiry (airyHermitePartialSum F N) ∧
      airyBetaInf (airyHermitePartialSum F N) =
        -∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 ∧
      airyBetaPlus (airyHermitePartialSum F N) =
        ∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 := by
    intro N
    have hterm_c : ∀ n : ℕ, HasGenRationalAiryCoeffs (airyHermiteTerm F n) (-cF n) 0 := fun n => by
      change HasGenRationalAiryCoeffs
        (fun z => (cG n : ℂ) * airySeedG n z + (cF n : ℂ) * airySeedF n z) (-cF n) 0
      have h1 := (hasGenRationalAiryCoeffs_airySeedG n).smul (cG n)
      have h2 := (hasGenRationalAiryCoeffs_airySeedF n).smul (cF n)
      have h3 := h1.add h2
      simpa only [mul_zero, zero_add, mul_neg, mul_one] using h3
    have hsum_c := HasGenRationalAiryCoeffs.finset_sum (Finset.range N)
      (fun n => airyHermiteTerm F n) (fun n => -cF n) (fun _ => 0) (fun n _ => hterm_c n)
    have hfun : (fun z => ∑ n ∈ Finset.range N, airyHermiteTerm F n z) =
        airyHermitePartialSum F N := rfl
    rw [hfun, Finset.sum_neg_distrib, Finset.sum_const_zero] at hsum_c
    obtain ⟨_, _, hb_inf, hb_plus⟩ := hsum_c.beta_eq
    exact ⟨⟨_, _, hsum_c⟩, by dsimp [cF] at hb_inf; linarith, by dsimp [cF] at hb_plus; linarith⟩
  -- Summable majorant tails (`k + N` indexing matching `sum_add_tsum_nat_add`)
  obtain ⟨C_L, hCL_pos, hCL_bd⟩ := airySeed_l1_and_laplace_bounds
  set C_L1 : ℝ := max C_L 1
  have hCL_le_CL1 : C_L ≤ C_L1 := le_max_left _ _
  have hwL_sum : Summable (fun n : ℕ => C_L1 * (1 + |airyZ n|) * cAbs n) := by
    have hs0 := (hcoeff_summable 0).mul_left C_L1
    have hs1 := (hcoeff_summable 1).mul_left C_L1
    refine (hs0.add hs1).congr fun n => ?_
    simp [pow_zero, pow_one]; ring
  have hwNeg_sum : Summable (fun n : ℕ => 400 * |airyZ n| ^ 2 * cAbs n) := by
    simpa [mul_assoc] using (hcoeff_summable 2).mul_left 400
  have htail_zero : ∀ {w : ℕ → ℝ}, Summable w →
      Tendsto (fun N : ℕ => ∑' k : ℕ, w (k + N)) atTop (𝓝 0) := by
    intro w hw
    have h1 := hw.hasSum.tendsto_sum_nat
    have h2 : ∀ N : ℕ, ∑' k : ℕ, w (k + N) = (∑' n : ℕ, w n) - ∑ n ∈ Finset.range N, w n :=
      fun N => eq_sub_iff_add_eq'.mpr (hw.sum_add_tsum_nat_add N)
    have hsub := h1.const_sub (∑' n : ℕ, w n)
    rw [sub_self] at hsub
    exact hsub.congr fun N => (h2 N).symm
  -- Term L¹ and Laplace bounds
  have hterm_int_and_l1 : ∀ n : ℕ,
      Integrable (fun u : ℝ => airyHermiteTerm F n (u : ℂ)) ∧
      (∫ u : ℝ, ‖airyHermiteTerm F n (u : ℂ)‖) ≤ C_L1 * (1 + |airyZ n|) * cAbs n := by
    intro n
    have hint : Integrable (fun u : ℝ => airyHermiteTerm F n (u : ℂ)) := by
      unfold airyHermiteTerm
      exact ((airySeedG_inAiryClass n).2.1.const_mul _).add
        ((airySeedF_inAiryClass n).2.1.const_mul _)
    refine ⟨hint, ?_⟩
    obtain ⟨hg1, hf1, _, _⟩ := hCL_bd n
    have hpt : ∀ u : ℝ, ‖airyHermiteTerm F n (u : ℂ)‖ ≤
        |cG n| * ‖airySeedG n (u : ℂ)‖ + |cF n| * ‖airySeedF n (u : ℂ)‖ := fun u => by
      unfold airyHermiteTerm
      calc ‖(cG n : ℂ) * airySeedG n (u : ℂ) + (cF n : ℂ) * airySeedF n (u : ℂ)‖
          ≤ ‖(cG n : ℂ) * airySeedG n (u : ℂ)‖ + ‖(cF n : ℂ) * airySeedF n (u : ℂ)‖ :=
            norm_add_le _ _
        _ = |cG n| * ‖airySeedG n (u : ℂ)‖ + |cF n| * ‖airySeedF n (u : ℂ)‖ := by
            simp [Complex.norm_real]
    have hmono := integral_mono hint.norm
      (((airySeedG_inAiryClass n).2.1.norm.const_mul |cG n|).add
        ((airySeedF_inAiryClass n).2.1.norm.const_mul |cF n|)) hpt
    change (∫ x : ℝ, ‖airyHermiteTerm F n (x : ℂ)‖) ≤
      ∫ x : ℝ, |cG n| * ‖airySeedG n (x : ℂ)‖ + |cF n| * ‖airySeedF n (x : ℂ)‖ at hmono
    rw [integral_add ((airySeedG_inAiryClass n).2.1.norm.const_mul _)
      ((airySeedF_inAiryClass n).2.1.norm.const_mul _),
      integral_const_mul, integral_const_mul, hg1, mul_one] at hmono
    refine hmono.trans ?_
    have hf1' : (∫ u : ℝ, ‖airySeedF n (u : ℂ)‖) ≤ C_L1 * |airyZ n| :=
      hf1.trans (mul_le_mul_of_nonneg_right hCL_le_CL1 (abs_nonneg _))
    dsimp [cAbs]
    have hp_nn : 0 ≤ C_L1 * |airyZ n| * |cG n| := by positivity
    nlinarith [abs_nonneg (cG n), abs_nonneg (cF n), abs_nonneg (airyZ n),
      le_max_right C_L 1]
  have hFN_int : ∀ N : ℕ, Integrable (fun u : ℝ => airyHermitePartialSum F N (u : ℂ)) := by
    intro N
    induction N with
    | zero =>
      have hz : (fun u : ℝ => airyHermitePartialSum F 0 (u : ℂ)) = fun _ => 0 := by
        ext u; simp [airyHermitePartialSum]
      rw [hz]; exact integrable_zero _ _ _
    | succ N ih =>
      have hs : (fun u : ℝ => airyHermitePartialSum F (N + 1) (u : ℂ)) =
          fun u : ℝ => airyHermitePartialSum F N (u : ℂ) + airyHermiteTerm F N (u : ℂ) := by
        ext u; simp [airyHermitePartialSum, Finset.sum_range_succ]
      rw [hs]; exact ih.add (hterm_int_and_l1 N).1
  have hterm_lap_bd : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y →
      |airyLaplace (fun u => (airyHermiteTerm F n (u : ℂ)).re) y| ≤
        C_L1 * (1 + |airyZ n|) * cAbs n * (1 + y) ^ (-(5 / 2 : ℝ)) := by
    intro n y hy
    obtain ⟨_, _, hgl, hfl⟩ := hCL_bd n
    have hre : ∀ u : ℝ,
        (airyHermiteTerm F n (u : ℂ)).re * Real.exp (y * u) =
        cG n * ((airySeedG n (u : ℂ)).re * Real.exp (y * u)) +
          cF n * ((airySeedF n (u : ℂ)).re * Real.exp (y * u)) := fun u => by
      change (((cG n : ℂ) * airySeedG n (u : ℂ) + (cF n : ℂ) * airySeedF n (u : ℂ)).re) *
        Real.exp (y * u) = _
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    have hlin : airyLaplace (fun u => (airyHermiteTerm F n (u : ℂ)).re) y =
        cG n * airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y +
          cF n * airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y := by
      unfold airyLaplace
      simp_rw [hre]
      have hiG : Integrable (fun u : ℝ => (airySeedG n (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedG_inAiryClass n).integrable_exp_nonneg hy
      have hiF : Integrable (fun u : ℝ => (airySeedF n (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedF_inAiryClass n).integrable_exp_nonneg hy
      rw [integral_add (hiG.const_mul _) (hiF.const_mul _),
        integral_const_mul, integral_const_mul]
      ring
    rw [hlin]
    have hg_le := (hgl y hy).trans
      (mul_le_mul_of_nonneg_right hCL_le_CL1 (by positivity))
    have hf_le := (hfl y hy).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCL_le_CL1 (abs_nonneg _)) (by positivity))
    calc |cG n * airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y +
          cF n * airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y|
        ≤ |cG n| * |airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y| +
            |cF n| * |airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y| := by
          simpa [abs_mul] using abs_add_le
            (cG n * airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y)
            (cF n * airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y)
      _ ≤ |cG n| * (C_L1 * (1 + y) ^ (-(5 / 2 : ℝ))) +
            |cF n| * (C_L1 * |airyZ n| * (1 + y) ^ (-(5 / 2 : ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left hg_le (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hf_le (abs_nonneg _))
      _ ≤ C_L1 * (1 + |airyZ n|) * cAbs n * (1 + y) ^ (-(5 / 2 : ℝ)) := by
          dsimp [cAbs]
          have hp : 0 ≤ (1 + y) ^ (-(5 / 2 : ℝ)) := by positivity
          have hp1 : 0 ≤ C_L1 * |airyZ n| * |cG n| := by positivity
          have hp2 : 0 ≤ C_L1 * |cF n| := by positivity
          have h1 : |cG n| * C_L1 + |cF n| * (C_L1 * |airyZ n|) ≤
              C_L1 * (1 + |airyZ n|) * (|cG n| + |cF n|) := by linarith
          calc |cG n| * (C_L1 * (1 + y) ^ (-(5 / 2 : ℝ))) +
                |cF n| * (C_L1 * |airyZ n| * (1 + y) ^ (-(5 / 2 : ℝ)))
              = (|cG n| * C_L1 + |cF n| * (C_L1 * |airyZ n|)) * (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
            _ ≤ (C_L1 * (1 + |airyZ n|) * (|cG n| + |cF n|)) * (1 + y) ^ (-(5 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right h1 hp
  -- Tail representation `F z - airyHermitePartialSum F N z = ∑' k, airyHermiteTerm F (k + N) z`
  have hrem_eq : ∀ N : ℕ, ∀ z : ℂ,
      F z - airyHermitePartialSum F N z = ∑' k : ℕ, airyHermiteTerm F (k + N) z := by
    intro N z
    have hsplit := (hF_hasSum z).summable.sum_add_tsum_nat_add N
    rw [(hF_hasSum z).tsum_eq] at hsplit
    unfold airyHermitePartialSum
    exact (eq_sub_iff_add_eq'.mpr hsplit).symm
  -- L¹ convergence of `F - F_N` to `0`
  have hl1_tendsto : Tendsto (fun N : ℕ =>
      ∫ u : ℝ, ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => integral_nonneg fun _ => norm_nonneg _) (fun N => ?_)
      (htail_zero hwL_sum)
    simp_rw [hrem_eq N]
    have hfn_int : ∀ k : ℕ, Integrable (fun u : ℝ => airyHermiteTerm F (k + N) (u : ℂ)) :=
      fun k => (hterm_int_and_l1 (k + N)).1
    have hnorm_sum : Summable (fun k : ℕ => ∫ u : ℝ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      refine (hwL_sum.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun k => (hterm_int_and_l1 (k + N)).2)
    have hhas := (integral_tsum_of_summable_integral_norm
      (F := fun (k : ℕ) (u : ℝ) => ‖airyHermiteTerm F (k + N) (u : ℂ)‖)
      (fun k => (hfn_int k).norm)
      (by
        refine hnorm_sum.congr fun k => ?_
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])).symm
    have hpt_sum : ∀ u : ℝ, Summable (fun k : ℕ => ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      intro u
      obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj (max |u| 1) (le_max_right _ _)
      have hu_mem : (u : ℂ) ∈ closedBall (0 : ℂ) (max |u| 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact le_max_left _ _
      exact (hu_R.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun k => hbd_R (k + N) (u : ℂ) hu_mem)
    have htsum_norm_int : Integrable (fun u : ℝ => ∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
        (fun M => Finset.aestronglyMeasurable_sum (Finset.range M)
          fun k _ => (hfn_int k).norm.aestronglyMeasurable)
        (Eventually.of_forall fun u =>
          (hpt_sum u).hasSum.tendsto_sum_nat.congr fun M =>
            (Finset.sum_apply u (Finset.range M)
              (fun k (a : ℝ) => ‖airyHermiteTerm F (k + N) (a : ℂ)‖)).symm), ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => tsum_nonneg fun _ => norm_nonneg _)]
      have heq_ofReal : ∀ u : ℝ,
          ENNReal.ofReal (∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) =
            ∑' k : ℕ, ENNReal.ofReal ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
        fun u => ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hpt_sum u)
      simp_rw [heq_ofReal]
      rw [lintegral_tsum fun k => (hfn_int k).norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
      have hterm_lint : ∀ k : ℕ,
          (∫⁻ u : ℝ, ENNReal.ofReal ‖airyHermiteTerm F (k + N) (u : ℂ)‖) =
            ENNReal.ofReal (∫ u : ℝ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) :=
        fun k => (ofReal_integral_eq_lintegral_ofReal (hfn_int k).norm
          (Eventually.of_forall fun _ => norm_nonneg _)).symm
      simp_rw [hterm_lint]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _) hnorm_sum]
      exact ENNReal.ofReal_lt_top
    have hrem_int : Integrable (fun u : ℝ => ‖∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      have hsub_int : Integrable (fun u : ℝ => F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)) :=
        hF.2.1.sub (hFN_int N)
      simpa [hrem_eq N] using hsub_int.norm
    calc (∫ u : ℝ, ‖∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)‖)
        ≤ ∫ u : ℝ, ∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
          integral_mono hrem_int htsum_norm_int
            (fun u => norm_tsum_le_tsum_norm (hpt_sum u))
      _ = ∑' k : ℕ, ∫ u : ℝ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖ := hhas
      _ ≤ ∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N) :=
          Summable.tsum_le_tsum (fun k => (hterm_int_and_l1 (k + N)).2)
            hnorm_sum (hwL_sum.comp_injective (add_left_injective N))
  -- Assemble all 10 conjuncts
  refine ⟨hF_hasSum, hcF_hasSum_zero, hpartial_coeffs, ?_, hl1_tendsto, ?_, ?_, ?_, ?_, ?_⟩
  · -- Uniform convergence on compact `K ⊂ ℂ`
    intro K hK
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set R1 : ℝ := max R 1
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj R1 (le_max_right _ _)
    have hunif := tendstoUniformlyOn_tsum_nat hu_R
      (f := fun n z => airyHermiteTerm F n z) (s := closedBall (0 : ℂ) R1)
      (fun n z hz => hbd_R n z hz)
    have hfun : (fun z => ∑' n : ℕ, airyHermiteTerm F n z) = F :=
      funext fun z => (hF_hasSum z).tsum_eq
    rw [hfun] at hunif
    exact hunif.mono (hKR.trans (closedBall_subset_closedBall (le_max_left R 1)))
  · -- `∫ F_N → ∫ F`
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hl1_tendsto ε hε] with N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at hN
    rw [Real.dist_eq, abs_sub_comm]
    have hF_re_int : Integrable (fun u : ℝ => (F (u : ℂ)).re) := hF.2.1.re
    have hFN_re_int : Integrable (fun u : ℝ => (airyHermitePartialSum F N (u : ℂ)).re) :=
      (hFN_int N).re
    rw [← integral_sub hF_re_int hFN_re_int]
    refine (le_trans abs_integral_le_integral_abs
      (integral_mono (hF_re_int.sub hFN_re_int).abs
        (hF.2.1.sub (hFN_int N)).norm fun u => ?_)).trans_lt hN
    change |(F (u : ℂ)).re - (airyHermitePartialSum F N (u : ℂ)).re| ≤
      ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  · -- (b) Negative-axis `(1 + |u|)^{3/2} |F(u) - F_N(u)| → 0`
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp (htail_zero hwNeg_sum) ε hε] with N hN
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (tsum_nonneg fun _ => by positivity)] at hN
    intro u hu
    have hpt_norm_sum : Summable (fun k : ℕ => ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj (max |u| 1) (le_max_right _ _)
      have hu_mem : (u : ℂ) ∈ closedBall (0 : ℂ) (max |u| 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact le_max_left _ _
      exact (hu_R.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun k => hbd_R (k + N) (u : ℂ) hu_mem)
    have hterm_w : ∀ k : ℕ,
        (1 + |u|) ^ (3 / 2 : ℝ) * ‖airyHermiteTerm F (k + N) (u : ℂ)‖ ≤
          400 * |airyZ (k + N)| ^ 2 * cAbs (k + N) := by
      intro k
      set m := k + N
      obtain ⟨hwf, hwg, _, _⟩ := airySeed_neg_weighted_bounds m hu
      have hA_gt2 : 2 < |airyZ m| := two_lt_abs_airyZ m
      have hA_32_le : |airyZ m| ^ (3 / 2 : ℝ) ≤ |airyZ m| ^ 2 := by
        rw [show |airyZ m| ^ 2 = |airyZ m| ^ (2 : ℝ) by rw [Real.rpow_two]]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hnG : ‖airySeedG m (u : ℂ)‖ = (airySeedG m (u : ℂ)).re := by
        rw [airySeedG_ofReal, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _), Complex.ofReal_re]
      have hnF : ‖airySeedF m (u : ℂ)‖ = |(airySeedF m (u : ℂ)).re| := by
        rw [airySeedF_ofReal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
      have htri_m : ‖airyHermiteTerm F m (u : ℂ)‖ ≤
          |cG m| * ‖airySeedG m (u : ℂ)‖ + |cF m| * ‖airySeedF m (u : ℂ)‖ := by
        unfold airyHermiteTerm
        calc ‖(cG m : ℂ) * airySeedG m (u : ℂ) + (cF m : ℂ) * airySeedF m (u : ℂ)‖
            ≤ ‖(cG m : ℂ) * airySeedG m (u : ℂ)‖ + ‖(cF m : ℂ) * airySeedF m (u : ℂ)‖ :=
              norm_add_le _ _
          _ = |cG m| * ‖airySeedG m (u : ℂ)‖ + |cF m| * ‖airySeedF m (u : ℂ)‖ := by
              simp [Complex.norm_real]
      have hm_le : |cF m| * (240 * |airyZ m| ^ (3 / 2 : ℝ)) ≤
          |cF m| * (400 * |airyZ m| ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
      calc (1 + |u|) ^ (3 / 2 : ℝ) * ‖airyHermiteTerm F m (u : ℂ)‖
          ≤ (1 + |u|) ^ (3 / 2 : ℝ) *
              (|cG m| * ‖airySeedG m (u : ℂ)‖ + |cF m| * ‖airySeedF m (u : ℂ)‖) :=
            mul_le_mul_of_nonneg_left htri_m (by positivity)
        _ = |cG m| * ((1 + |u|) ^ (3 / 2 : ℝ) * (airySeedG m (u : ℂ)).re) +
              |cF m| * ((1 + |u|) ^ (3 / 2 : ℝ) * |(airySeedF m (u : ℂ)).re|) := by
            rw [hnG, hnF]; ring
        _ ≤ |cG m| * (400 * |airyZ m| ^ 2) + |cF m| * (240 * |airyZ m| ^ (3 / 2 : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hwg (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hwf (abs_nonneg _))
        _ ≤ |cG m| * (400 * |airyZ m| ^ 2) + |cF m| * (400 * |airyZ m| ^ 2) := by linarith
        _ = 400 * |airyZ m| ^ 2 * cAbs m := by dsimp [cAbs]; ring
    calc (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re - (airyHermitePartialSum F N (u : ℂ)).re|
        ≤ (1 + |u|) ^ (3 / 2 : ℝ) * ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖ := by
          rw [← Complex.sub_re]
          exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
      _ = (1 + |u|) ^ (3 / 2 : ℝ) * ‖∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)‖ := by
          rw [hrem_eq N]
      _ ≤ (1 + |u|) ^ (3 / 2 : ℝ) * ∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hpt_norm_sum) (by positivity)
      _ = ∑' k : ℕ, (1 + |u|) ^ (3 / 2 : ℝ) * ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
          (tsum_mul_left).symm
      _ ≤ ∑' k : ℕ, 400 * |airyZ (k + N)| ^ 2 * cAbs (k + N) :=
          Summable.tsum_le_tsum hterm_w (hpt_norm_sum.mul_left _)
            (hwNeg_sum.comp_injective (add_left_injective N))
      _ < ε := hN
  · -- (c) Twisted Laplace `(1 + y)^{5/2} |ℒ_y(F) - ℒ_y(F_N)| → 0`
    obtain ⟨C_pos, hCpos_pos, hpos_J0⟩ := exists_airyAi_sq_div_le_refJ0
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp (htail_zero hwL_sum) ε hε] with N hN
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (tsum_nonneg fun _ => by positivity)] at hN
    intro y hy
    set I_Jy : ℝ := ∫ u in Ioi (0 : ℝ), (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)
    have hJ_int_y : IntegrableOn (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) (Ioi 0) :=
      (integrable_airyRefJ0_mul_exp hy).integrableOn
    have hterm_y_int : ∀ m : ℕ,
        Integrable (fun u : ℝ => (airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)) ∧
        (∫ u : ℝ, ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) ≤
          (C_L1 * (1 + |airyZ m|) + C_pos * I_Jy) * cAbs m := by
      intro m
      have hiG : Integrable (fun u : ℝ => (airySeedG m (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedG_inAiryClass m).integrable_exp_nonneg hy
      have hiF : Integrable (fun u : ℝ => (airySeedF m (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedF_inAiryClass m).integrable_exp_nonneg hy
      have hre_eq : (fun u : ℝ => (airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)) =
          fun u : ℝ => cG m * ((airySeedG m (u : ℂ)).re * Real.exp (y * u)) +
            cF m * ((airySeedF m (u : ℂ)).re * Real.exp (y * u)) := by
        ext u
        change (((cG m : ℂ) * airySeedG m (u : ℂ) + (cF m : ℂ) * airySeedF m (u : ℂ)).re) *
          Real.exp (y * u) = _
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        ring
      have hint_m : Integrable (fun u : ℝ => (airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)) := by
        rw [hre_eq]; exact (hiG.const_mul _).add (hiF.const_mul _)
      refine ⟨hint_m, ?_⟩
      have hdisj0 : Disjoint (Iic (0 : ℝ)) (Ioi (0 : ℝ)) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
      have hsplit : (∫ u : ℝ, ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) =
          (∫ u in Iic (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) +
            ∫ u in Ioi (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖ :=
        (setIntegral_union hdisj0 measurableSet_Ioi
          hint_m.norm.integrableOn hint_m.norm.integrableOn).symm.trans
          (by rw [Iic_union_Ioi, setIntegral_univ])
      have hneg_le : (∫ u in Iic (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) ≤
          C_L1 * (1 + |airyZ m|) * cAbs m := by
        have hmono := setIntegral_mono_on hint_m.norm.integrableOn
          (hterm_int_and_l1 m).1.norm.integrableOn measurableSet_Iic fun u (hu : u ≤ 0) => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            have hexp1 : Real.exp (y * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
            calc |(airyHermiteTerm F m (u : ℂ)).re| * Real.exp (y * u)
                ≤ ‖airyHermiteTerm F m (u : ℂ)‖ * 1 :=
                  mul_le_mul (Complex.abs_re_le_norm _) hexp1 (Real.exp_pos _).le (norm_nonneg _)
              _ = ‖airyHermiteTerm F m (u : ℂ)‖ := mul_one _
        exact hmono.trans ((setIntegral_le_integral (hterm_int_and_l1 m).1.norm
          (Eventually.of_forall fun _ => norm_nonneg _)).trans (hterm_int_and_l1 m).2)
      have hpos_le : (∫ u in Ioi (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) ≤
          C_pos * I_Jy * cAbs m := by
        have hpt_pos : ∀ u ∈ Ioi (0 : ℝ),
            ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖ ≤
              (C_pos * cAbs m) * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by
          intro u (hu : 0 < u)
          have hne : u ≠ airyZ m := by linarith [airyZ_neg m]
          have hA2 : 2 < -airyZ m := by
            have := two_lt_abs_airyZ m
            rwa [abs_of_neg (airyZ_neg m)] at this
          have hden_gt : u + 2 < u - airyZ m := by linarith
          have hf_le : |(airySeedF m (u : ℂ)).re| ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
            rw [airySeedF_re_of_ne m hne, abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
            exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden_gt.le).trans
              (hpos_J0 u hu.le)
          have hg_le : |(airySeedG m (u : ℂ)).re| ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
            rw [airySeedG_re_of_ne m hne, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
            have hsq_ge : u + 2 ≤ (u - airyZ m) ^ 2 := by nlinarith
            exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hsq_ge).trans
              (hpos_J0 u hu.le)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hterm_re : |(airyHermiteTerm F m (u : ℂ)).re| ≤
              (C_pos * cAbs m) * (airyRefJ0 (u : ℂ)).re := by
            have hre_u : (airyHermiteTerm F m (u : ℂ)).re =
                cG m * (airySeedG m (u : ℂ)).re + cF m * (airySeedF m (u : ℂ)).re := by
              change (((cG m : ℂ) * airySeedG m (u : ℂ) +
                (cF m : ℂ) * airySeedF m (u : ℂ)).re) = _
              simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
                Complex.ofReal_im, zero_mul, sub_zero]
            rw [hre_u]
            calc |cG m * (airySeedG m (u : ℂ)).re + cF m * (airySeedF m (u : ℂ)).re|
                ≤ |cG m| * |(airySeedG m (u : ℂ)).re| + |cF m| * |(airySeedF m (u : ℂ)).re| := by
                  simpa [abs_mul] using abs_add_le
                    (cG m * (airySeedG m (u : ℂ)).re) (cF m * (airySeedF m (u : ℂ)).re)
              _ ≤ |cG m| * (C_pos * (airyRefJ0 (u : ℂ)).re) +
                    |cF m| * (C_pos * (airyRefJ0 (u : ℂ)).re) :=
                  add_le_add (mul_le_mul_of_nonneg_left hg_le (abs_nonneg _))
                    (mul_le_mul_of_nonneg_left hf_le (abs_nonneg _))
              _ = (C_pos * cAbs m) * (airyRefJ0 (u : ℂ)).re := by dsimp [cAbs]; ring
          calc |(airyHermiteTerm F m (u : ℂ)).re| * Real.exp (y * u)
              ≤ ((C_pos * cAbs m) * (airyRefJ0 (u : ℂ)).re) * Real.exp (y * u) :=
                mul_le_mul_of_nonneg_right hterm_re (Real.exp_pos _).le
            _ = (C_pos * cAbs m) * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ring
        have hmono := setIntegral_mono_on hint_m.norm.integrableOn
          (hJ_int_y.const_mul (C_pos * cAbs m)) measurableSet_Ioi hpt_pos
        rw [integral_const_mul] at hmono
        exact hmono.trans_eq (by dsimp [I_Jy]; ring)
      rw [hsplit]
      linarith
    have hsum_y : Summable (fun k : ℕ =>
        ∫ u : ℝ, ‖(airyHermiteTerm F (k + N) (u : ℂ)).re * Real.exp (y * u)‖) := by
      have hmaj : Summable (fun m : ℕ => (C_L1 * (1 + |airyZ m|) + C_pos * I_Jy) * cAbs m) := by
        refine (hwL_sum.add ((hcoeff_summable 0).mul_left (C_pos * I_Jy))).congr fun m => ?_
        simp [pow_zero]; ring
      exact (hmaj.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun k => (hterm_y_int (k + N)).2)
    have hhas_lap := hasSum_integral_of_summable_integral_norm
      (F := fun (k : ℕ) (u : ℝ) => (airyHermiteTerm F (k + N) (u : ℂ)).re * Real.exp (y * u))
      (fun k => (hterm_y_int (k + N)).1) hsum_y
    have hint_FN_y_all : ∀ M : ℕ,
        Integrable (fun u : ℝ => (airyHermitePartialSum F M (u : ℂ)).re * Real.exp (y * u)) := by
      intro M
      induction M with
      | zero =>
        have hz : (fun u : ℝ => (airyHermitePartialSum F 0 (u : ℂ)).re * Real.exp (y * u)) =
            fun _ => 0 := by ext u; simp [airyHermitePartialSum]
        rw [hz]; exact integrable_zero _ _ _
      | succ M ih =>
        have hs : (fun u : ℝ => (airyHermitePartialSum F (M + 1) (u : ℂ)).re * Real.exp (y * u)) =
            fun u : ℝ => (airyHermitePartialSum F M (u : ℂ)).re * Real.exp (y * u) +
              (airyHermiteTerm F M (u : ℂ)).re * Real.exp (y * u) := by
          ext u; simp [airyHermitePartialSum, Finset.sum_range_succ, add_mul]
        rw [hs]; exact ih.add (hterm_y_int M).1
    have hrem_lap : airyLaplace (fun u => (F (u : ℂ)).re) y -
        airyLaplace (fun u => (airyHermitePartialSum F N (u : ℂ)).re) y =
        ∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y := by
      have hint_F_y : Integrable (fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u)) :=
        hF.integrable_exp_nonneg hy
      have hint_FN_y := hint_FN_y_all N
      unfold airyLaplace
      rw [← mul_sub, ← integral_sub hint_F_y hint_FN_y]
      have hpt_re : ∀ u : ℝ,
          (F (u : ℂ)).re * Real.exp (y * u) -
            (airyHermitePartialSum F N (u : ℂ)).re * Real.exp (y * u) =
          ∑' k : ℕ, (airyHermiteTerm F (k + N) (u : ℂ)).re * Real.exp (y * u) := by
        intro u
        rw [← sub_mul, ← Complex.sub_re, hrem_eq N]
        have hs_c : HasSum (fun k : ℕ => airyHermiteTerm F (k + N) (u : ℂ))
            (∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)) :=
          ((hF_hasSum (u : ℂ)).summable.comp_injective (add_left_injective N)).hasSum
        have hs_re : HasSum (fun k : ℕ => (airyHermiteTerm F (k + N) (u : ℂ)).re)
            (∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)).re := by
          unfold HasSum at hs_c ⊢
          simp_rw [← Complex.re_sum]
          exact (Complex.continuous_re.tendsto _).comp hs_c
        rw [← hs_re.tsum_eq, ← tsum_mul_right]
      simp_rw [hpt_re]
      rw [← hhas_lap.tsum_eq, ← tsum_mul_left]
    rw [hrem_lap]
    have hlap_sum : Summable (fun k : ℕ =>
        |airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y|) :=
      ((hwL_sum.comp_injective (add_left_injective N)).mul_right
        ((1 + y) ^ (-(5 / 2 : ℝ)))).of_nonneg_of_le
        (fun _ => abs_nonneg _) (fun k => hterm_lap_bd (k + N) y hy)
    have hlap_tsum_le : |∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y| ≤
        (∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      calc |∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y|
          ≤ ∑' k : ℕ, |airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y| := by
            simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hlap_sum
        _ ≤ ∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N) * (1 + y) ^ (-(5 / 2 : ℝ)) :=
            Summable.tsum_le_tsum (fun k => hterm_lap_bd (k + N) y hy) hlap_sum
              ((hwL_sum.comp_injective (add_left_injective N)).mul_right _)
        _ = (∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) *
              (1 + y) ^ (-(5 / 2 : ℝ)) := tsum_mul_right
    have hy_cancel : (1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + y), add_neg_cancel, Real.rpow_zero]
    calc (1 + y) ^ (5 / 2 : ℝ) *
          |∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y|
        ≤ (1 + y) ^ (5 / 2 : ℝ) *
            ((∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) *
              (1 + y) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hlap_tsum_le (by positivity)
      _ = (∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) *
            ((1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by ring
      _ = ∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N) := by rw [hy_cancel, mul_one]
      _ < ε := hN
  · -- (d1) `airyBetaInf (F_N) → 0`
    have heq : (fun N : ℕ => airyBetaInf (airyHermitePartialSum F N)) =
        fun N : ℕ => -∑ n ∈ Finset.range N, cF n :=
      funext fun N => (hpartial_coeffs N).2.1
    rw [heq]
    simpa using hcF_hasSum_zero.tendsto_sum_nat.neg
  · -- (d2) `airyBetaPlus (F_N) → 0`
    have heq : (fun N : ℕ => airyBetaPlus (airyHermitePartialSum F N)) =
        fun N : ℕ => ∑ n ∈ Finset.range N, cF n :=
      funext fun N => (hpartial_coeffs N).2.2
    rw [heq]
    exact hcF_hasSum_zero.tendsto_sum_nat

/-- info: 'FormalResearch.SignUncertainty.lem_al_hermite_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_al_hermite_approx

end FormalResearch.SignUncertainty



