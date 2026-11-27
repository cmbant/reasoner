module

public import FormalResearch.SignUncertainty.AiryRationalSeeds
public import FormalResearch.SignUncertainty.ShellGapOriginFloor
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Envelope Stability, Cauchy Derivative Bounds, and Shift Closure in the Airy Class

Source: `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex` (used in `lem:al-smooth` and
`lem:al-hermite-approx`):
* `re_cpow_three_halves_ball_abs_sub_le` and `airyEnv_ball_le`: on the disc
  `‖ζ - w‖ ≤ 2 (1 + ‖w‖)^{-1/2}`, `Re(ζ^{3/2})` varies by at most `30`, so `airyEnv ζ ≤ e^{40} airyEnv w`
  uniformly across the negative real branch cut via a first-quadrant square-root comparison;
* `deriv_inAiryClass_bound`: Cauchy derivative bound in `InAiryClass`;
* `iteratedDeriv_re_of_differentiable`, `contDiff_re_of_differentiable`,
  `inAiryClass_shift_nonneg`, and `schwartz_shift`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric FormalResearch.Special
open scoped Real Nat ContDiff

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

lemma one_add_norm_rpow_ball_le (ν : ℝ) {w ζ : ℂ} (hζ : ‖ζ - w‖ ≤ 1) :
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


end FormalResearch.SignUncertainty
