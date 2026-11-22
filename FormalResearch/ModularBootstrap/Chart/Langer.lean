module

public import FormalResearch.ModularBootstrap.Chart.EvenAndFactorization
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Langer Comparability (Lemma S6)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, lines 455–466:
* `LangerChartSpec`: explicit upstream input `R5` (`lower_o1_two_edge.tex`, line 38;
  `remainder.tex`, lines 468–472) giving the inverse Langer chart `b_L(z)` near `z = 0` with
  `b_L(0) = ξ_*`, `b_L'(0) = -1/β`, and real values on `ℝ`, together with `langerChartSpec_nonvacuous`.
* **Lemma S6** (`vlo:S6`):
  1. `b(ζ) - ξ_* = -(π/(4√2)) ζ² (1 + O(ζ²))` with real even Taylor coefficients.
  2. `ζ_+ = κ_V c'^{-1/3} √ũ q_V(ũ c'^{-2/3})`, `κ_V = √(4√2/(πβ))`, `q_V` analytic near `0`
     with real Taylor coefficients and `q_V(0) = 1`, solving `b(ζ_+) = b_L(ũ c'^{-2/3})`.
  3. With `ũ = a'^2 e^{i(π - 2φ)}` and `ζ_+ = σ_+ + i τ_+`:
     `|ζ_+| = ρ = κ_V c'^{-1/3} a' (1 + O(c₀))` and `σ_+ = ρ sin φ (1 + O(ρ²))`.
  4. On the band (`ũ = -ṽ`, `φ = 0`): `ζ_+ = i τ₀`, `c'^{1/3} τ₀ = κ_V √ṽ (1 + O(c₀))`, `b(ζ_+) = x₀(τ₀)`.
  5. `Im b(ζ_+) = -(π/(2√2)) σ_+ τ_+ (1 + O(ρ²)) ≤ 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Chart

/-- Named upstream input for **Lemma S6** (`lower_o1_two_edge.tex`, Result R5, line 38;
`remainder.tex`, lines 468–472): analytic inverse Langer chart `b_L(z)` satisfying
`ũ(b_L(z)) = c'^{2/3} z`, with `b_L(0) = ξ_*`, `b_L'(0) = -1/β`, and real values on `ℝ`. -/
structure LangerChartSpec where
  bL : ℂ → ℂ
  rL : ℝ
  hrL_pos : 0 < rL
  hbL_an : AnalyticOnNhd ℂ bL (ball (0 : ℂ) rL)
  hbL_zero : bL 0 = (xiStar : ℂ)
  hbL_deriv : deriv bL 0 = -(1 / (betaTip : ℂ))
  hbL_real : ∀ x : ℝ, |x| < rL → (bL (x : ℂ)).im = 0

/-- Non-vacuity witness for `LangerChartSpec`. -/
theorem langerChartSpec_nonvacuous : Nonempty LangerChartSpec :=
  ⟨{
    bL := fun z => (xiStar : ℂ) - (1 / (betaTip : ℂ)) * z
    rL := 1
    hrL_pos := one_pos
    hbL_an := fun _ _ => by fun_prop
    hbL_zero := by simp
    hbL_deriv := by
      have hd : HasDerivAt (fun z : ℂ => (xiStar : ℂ) - (1 / (betaTip : ℂ)) * z)
          (-(1 / (betaTip : ℂ))) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (1 / (betaTip : ℂ))).const_sub (xiStar : ℂ)
      exact hd.deriv
    hbL_real := fun x _ => by
      rw [show (1 / (betaTip : ℂ)) = ((1 / betaTip : ℝ) : ℂ) by push_cast; rfl,
        Complex.sub_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.ofReal_im, mul_zero,
        sub_zero]
  }⟩

/-- Tip scaling constant `κ_V = √(4√2 / (π β))` (`lower_o1_two_edge.tex`, Lemma S6, line 458). -/
noncomputable def kappaV : ℝ := √(4 * √2 / (Real.pi * betaTip))

lemma kappaV_pos : 0 < kappaV := by
  unfold kappaV
  have := betaTip_pos
  positivity

lemma kappaV_sq : kappaV ^ 2 = 4 * √2 / (Real.pi * betaTip) := by
  unfold kappaV
  have := betaTip_pos
  exact Real.sq_sqrt (by positivity)

private lemma cpow_half_exp_angle {a phi : ℝ} (ha : 0 ≤ a) (hphi0 : 0 ≤ phi)
    (hphi1 : phi ≤ Real.pi / 2) :
    (((a ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ))) ^ (1 / 2 : ℂ) =
      (a : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - phi : ℝ) : ℂ)) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp
  · have hpos : 0 < a ^ 2 := sq_pos_of_pos ha_pos
    by_cases hphi_zero : phi = 0
    · subst hphi_zero
      simp only [mul_zero, sub_zero]
      rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
        Complex.exp_pi_mul_I, mul_neg_one, ← Complex.ofReal_neg]
      have harg : ((-(a ^ 2) : ℝ) : ℂ).arg = Real.pi :=
        Complex.arg_ofReal_of_neg (neg_lt_zero.mpr hpos)
      have hnorm : ‖((-(a ^ 2) : ℝ) : ℂ)‖ = a ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hpos]
      have hlog_neg : Complex.log ((-(a ^ 2) : ℝ) : ℂ) =
          (Real.log (a ^ 2) : ℂ) + (Real.pi : ℂ) * Complex.I := by
        refine Complex.ext ?_ ?_
        · rw [Complex.log_re, hnorm]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.ofReal_im, Complex.I_im]; ring
        · rw [Complex.log_im, harg]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hpos.ne'))]
      rw [hlog_neg, Real.log_pow,
        show ((2 : ℕ) : ℝ) * Real.log a = 2 * Real.log a by push_cast; rfl,
        show (((2 * Real.log a : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I) * (1 / 2 : ℂ) =
          (Real.log a : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha_pos]
    · have hphi_gt : 0 < phi := lt_of_le_of_ne hphi0 (Ne.symm hphi_zero)
      have ht_mem : Real.pi - 2 * phi ∈ Ioc (-Real.pi) Real.pi := by
        constructor <;> linarith [Real.pi_pos]
      let u : ℂ := ((a ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ))
      have hu_ne : u ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne') (Complex.exp_ne_zero _)
      have hexp_eq : Complex.exp (((2 * Real.log a : ℝ) : ℂ) +
          Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ)) = u := by
        rw [Complex.exp_add, show ((2 * Real.log a : ℝ) : ℂ) = ((Real.log (a ^ 2) : ℝ) : ℂ) by
          rw [Real.log_pow]; push_cast; ring, ← Complex.ofReal_exp, Real.exp_log hpos]
      have him_gt : -Real.pi < (((2 * Real.log a : ℝ) : ℂ) +
          Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ)).im := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, zero_mul, one_mul, zero_add]
        exact ht_mem.1
      have him_le : (((2 * Real.log a : ℝ) : ℂ) +
          Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ)).im ≤ Real.pi := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, zero_mul, one_mul, zero_add]
        exact ht_mem.2
      have hlog : Complex.log u =
          ((2 * Real.log a : ℝ) : ℂ) + Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ) := by
        rw [← hexp_eq, Complex.log_exp him_gt him_le]
      change u ^ (1 / 2 : ℂ) = _
      rw [Complex.cpow_def_of_ne_zero hu_ne, hlog,
        show (((2 * Real.log a : ℝ) : ℂ) + Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ)) * (1 / 2 : ℂ) =
          (Real.log a : ℂ) + Complex.I * ((Real.pi / 2 - phi : ℝ) : ℂ) by push_cast; ring,
        Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha_pos]

private lemma langer_sigma_tau_bounds
    {σp τp ρ ρ₀ x_q y_q n_q M_q phi : ℝ}
    (hρ_nn : 0 ≤ ρ) (hMq_nn : 0 ≤ M_q)
    (hsin_nn : 0 ≤ Real.sin phi) (hcos_nn : 0 ≤ Real.cos phi)
    (hnq_lo : (1 / 2 : ℝ) ≤ n_q) (hnq_hi : n_q ≤ 3 / 2) (hxq_lo : (1 / 2 : ℝ) ≤ x_q)
    (hsq_id : n_q ^ 2 = x_q ^ 2 + y_q ^ 2) (hx_le : x_q ≤ n_q) (hy_abs_le : |y_q| ≤ n_q)
    (hrho_eq : ρ = ρ₀ * n_q)
    (hsig_eq : σp = ρ₀ * (Real.sin phi * x_q - Real.cos phi * y_q))
    (htau_eq : τp = ρ₀ * (Real.cos phi * x_q + Real.sin phi * y_q))
    (hyq_sin_cos : |y_q| ≤ (8 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi * Real.cos phi)
    (hC2_half : (48 * M_q / kappaV ^ 2) * ρ ^ 2 ≤ 1 / 2) :
    |σp - ρ * Real.sin phi| ≤ (48 * M_q / kappaV ^ 2) * ρ ^ 2 * (ρ * Real.sin phi) ∧
    0 ≤ σp ∧ 0 ≤ τp := by
  have hdiff_id : |x_q - n_q| = y_q ^ 2 / (n_q + x_q) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx_le), eq_div_iff (by linarith [hnq_lo, hxq_lo] : n_q + x_q ≠ 0)]
    linarith [hsq_id]
  have hyq_le_two : |y_q| ≤ 2 := by linarith [hy_abs_le, hnq_hi]
  have h_sin_cos_le : Real.sin phi * Real.cos phi ≤ 1 :=
    (mul_le_mul (Real.sin_le_one phi) (Real.cos_le_one phi) hcos_nn zero_le_one).trans_eq (one_mul 1)
  have hcoeff_nn : 0 ≤ (8 * M_q / kappaV ^ 2) * ρ ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hMq_nn) (sq_nonneg kappaV)) (sq_nonneg ρ)
  have hyq_bd_simple : |y_q| ≤ (8 * M_q / kappaV ^ 2) * ρ ^ 2 := by
    calc |y_q| ≤ (8 * M_q / kappaV ^ 2) * ρ ^ 2 * (Real.sin phi * Real.cos phi) := by
          rw [← mul_assoc]; exact hyq_sin_cos
      _ ≤ (8 * M_q / kappaV ^ 2) * ρ ^ 2 * 1 := mul_le_mul_of_nonneg_left h_sin_cos_le hcoeff_nn
      _ = (8 * M_q / kappaV ^ 2) * ρ ^ 2 := mul_one _
  have hxq_nq_diff : |x_q - n_q| ≤ (16 * M_q / kappaV ^ 2) * ρ ^ 2 := by
    calc |x_q - n_q| = y_q ^ 2 / (n_q + x_q) := hdiff_id
      _ ≤ y_q ^ 2 / 1 :=
          div_le_div_of_nonneg_left (sq_nonneg y_q) zero_lt_one (by linarith [hnq_lo, hxq_lo])
      _ = |y_q| * |y_q| := by rw [div_one, ← sq_abs, sq]
      _ ≤ 2 * |y_q| := mul_le_mul_of_nonneg_right hyq_le_two (abs_nonneg y_q)
      _ ≤ 2 * ((8 * M_q / kappaV ^ 2) * ρ ^ 2) := mul_le_mul_of_nonneg_left hyq_bd_simple (by norm_num)
      _ = (16 * M_q / kappaV ^ 2) * ρ ^ 2 := by ring
  have hnq_ne : n_q ≠ 0 := by linarith [hnq_lo]
  have hnq_pos : 0 < n_q := by linarith [hnq_lo]
  have hsigma_rel : |σp - ρ * Real.sin phi| ≤ (48 * M_q / kappaV ^ 2) * ρ ^ 2 * (ρ * Real.sin phi) := by
    have hsig_id : σp - ρ * Real.sin phi =
        ρ * (Real.sin phi * ((x_q - n_q) / n_q) - Real.cos phi * (y_q / n_q)) := by
      rw [hsig_eq, hrho_eq]; field_simp [hnq_ne]; ring
    rw [hsig_id, abs_mul, abs_of_nonneg hρ_nn]
    have htri := abs_sub (Real.sin phi * ((x_q - n_q) / n_q)) (Real.cos phi * (y_q / n_q))
    have h1 : |Real.sin phi * ((x_q - n_q) / n_q)| ≤ (32 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi := by
      rw [abs_mul, abs_of_nonneg hsin_nn, abs_div, abs_of_pos hnq_pos]
      calc Real.sin phi * (|x_q - n_q| / n_q)
          ≤ Real.sin phi * ((16 * M_q / kappaV ^ 2) * ρ ^ 2 / (1 / 2)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div₀ (by positivity) hxq_nq_diff (by norm_num) hnq_lo) hsin_nn
        _ = (32 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi := by ring
    have h2 : |Real.cos phi * (y_q / n_q)| ≤ (16 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi := by
      rw [abs_mul, abs_of_nonneg hcos_nn, abs_div, abs_of_pos hnq_pos]
      have hcos1 : Real.cos phi ≤ 1 := Real.cos_le_one phi
      calc Real.cos phi * (|y_q| / n_q)
          ≤ 1 * (((8 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi * Real.cos phi) / (1 / 2)) :=
            mul_le_mul hcos1
              (div_le_div₀ (mul_nonneg (mul_nonneg hcoeff_nn hsin_nn) hcos_nn) hyq_sin_cos
                (by norm_num) hnq_lo)
              (div_nonneg (abs_nonneg y_q) hnq_pos.le) zero_le_one
        _ ≤ 1 * (((8 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi * 1) / (1 / 2)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hcoeff_nn hsin_nn)) (by norm_num))
              zero_le_one
        _ = (16 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi := by ring
    calc ρ * |Real.sin phi * ((x_q - n_q) / n_q) - Real.cos phi * (y_q / n_q)|
        ≤ ρ * ((32 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi +
            (16 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi) :=
          mul_le_mul_of_nonneg_left (htri.trans (add_le_add h1 h2)) hρ_nn
      _ = (48 * M_q / kappaV ^ 2) * ρ ^ 2 * (ρ * Real.sin phi) := by ring
  have hsigma_nn : 0 ≤ σp := by
    have h := (abs_le.mp hsigma_rel).1
    have hmult : (48 * M_q / kappaV ^ 2) * ρ ^ 2 * (ρ * Real.sin phi) ≤ (1 / 2) * (ρ * Real.sin phi) :=
      mul_le_mul_of_nonneg_right hC2_half (mul_nonneg hρ_nn hsin_nn)
    linarith [h, hmult, mul_nonneg hρ_nn hsin_nn]
  have htau_rel : |τp - ρ * Real.cos phi| ≤ (48 * M_q / kappaV ^ 2) * ρ ^ 2 * (ρ * Real.cos phi) := by
    have htau_id : τp - ρ * Real.cos phi =
        ρ * (Real.cos phi * ((x_q - n_q) / n_q) + Real.sin phi * (y_q / n_q)) := by
      rw [htau_eq, hrho_eq]; field_simp [hnq_ne]; ring
    rw [htau_id, abs_mul, abs_of_nonneg hρ_nn]
    have htri := abs_add_le (Real.cos phi * ((x_q - n_q) / n_q)) (Real.sin phi * (y_q / n_q))
    have h1 : |Real.cos phi * ((x_q - n_q) / n_q)| ≤ (32 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.cos phi := by
      rw [abs_mul, abs_of_nonneg hcos_nn, abs_div, abs_of_pos hnq_pos]
      calc Real.cos phi * (|x_q - n_q| / n_q)
          ≤ Real.cos phi * ((16 * M_q / kappaV ^ 2) * ρ ^ 2 / (1 / 2)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div₀ (by positivity) hxq_nq_diff (by norm_num) hnq_lo) hcos_nn
        _ = (32 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.cos phi := by ring
    have h2 : |Real.sin phi * (y_q / n_q)| ≤ (16 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.cos phi := by
      rw [abs_mul, abs_of_nonneg hsin_nn, abs_div, abs_of_pos hnq_pos]
      have hsin1 : Real.sin phi ≤ 1 := Real.sin_le_one phi
      calc Real.sin phi * (|y_q| / n_q)
          ≤ 1 * (((8 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi * Real.cos phi) / (1 / 2)) :=
            mul_le_mul hsin1
              (div_le_div₀ (mul_nonneg (mul_nonneg hcoeff_nn hsin_nn) hcos_nn) hyq_sin_cos
                (by norm_num) hnq_lo)
              (div_nonneg (abs_nonneg y_q) hnq_pos.le) zero_le_one
        _ ≤ 1 * (((8 * M_q / kappaV ^ 2) * ρ ^ 2 * 1 * Real.cos phi) / (1 / 2)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsin1 hcoeff_nn) hcos_nn)
                (by norm_num)) zero_le_one
        _ = (16 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.cos phi := by ring
    calc ρ * |Real.cos phi * ((x_q - n_q) / n_q) + Real.sin phi * (y_q / n_q)|
        ≤ ρ * ((32 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.cos phi +
            (16 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.cos phi) :=
          mul_le_mul_of_nonneg_left (htri.trans (add_le_add h1 h2)) hρ_nn
      _ = (48 * M_q / kappaV ^ 2) * ρ ^ 2 * (ρ * Real.cos phi) := by ring
  have htau_nn : 0 ≤ τp := by
    have h := (abs_le.mp htau_rel).1
    have hmult : (48 * M_q / kappaV ^ 2) * ρ ^ 2 * (ρ * Real.cos phi) ≤ (1 / 2) * (ρ * Real.cos phi) :=
      mul_le_mul_of_nonneg_right hC2_half (mul_nonneg hρ_nn hcos_nn)
    linarith [h, hmult, mul_nonneg hρ_nn hcos_nn]
  exact ⟨hsigma_rel, hsigma_nn, htau_nn⟩

private lemma langer_im_bound
    {R_b : ℂ → ℂ} {ζp : ℂ} {M_R ρ σp τp : ℝ}
    (hMR_nn : 0 ≤ M_R) (hσ_nn : 0 ≤ σp) (hτ_nn : 0 ≤ τp)
    (hσ_eq : σp = ζp.re) (hτ_eq : τp = ζp.im)
    (hρ_eq : ρ = ‖ζp‖) (hw_lt_half : ‖ζp ^ 2‖ ≤ rBEven / 2)
    (hRb_an : AnalyticOnNhd ℂ R_b (ball (0 : ℂ) rBEven))
    (hRb_deriv_bd : ∀ w ∈ closedBall (0 : ℂ) (rBEven / 2), ‖deriv R_b w‖ ≤ M_R * ‖w‖)
    (hRb_re_im : (R_b ((ζp ^ 2).re : ℂ)).im = 0)
    (hchartB_eq : chartB ζp = (xiStar : ℂ) + (-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * (ζp ^ 2) + R_b (ζp ^ 2))
    (hC3_half : (4 * √2 * M_R / Real.pi) * ρ ^ 2 ≤ 1 / 2) :
    |(chartB ζp).im - (-(Real.pi / (2 * √2)) * σp * τp)| ≤
      (4 * √2 * M_R / Real.pi) * ρ ^ 2 * (Real.pi / (2 * √2) * σp * τp) ∧
    (chartB ζp).im ≤ 0 := by
  set w := ζp ^ 2
  have hw_norm : ‖w‖ = ρ ^ 2 := by rw [hρ_eq]; exact norm_pow ζp 2
  have hw_re_cb : (w.re : ℂ) ∈ closedBall (0 : ℂ) (ρ ^ 2) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, ← hw_norm]
    exact Complex.abs_re_le_norm w
  have hw_cb : w ∈ closedBall (0 : ℂ) (ρ ^ 2) := by rw [mem_closedBall_zero_iff, hw_norm]
  have hcb_sub : closedBall (0 : ℂ) (ρ ^ 2) ⊆ closedBall (0 : ℂ) (rBEven / 2) :=
    closedBall_subset_closedBall (hw_norm ▸ hw_lt_half)
  have hcb_ball : closedBall (0 : ℂ) (rBEven / 2) ⊆ ball (0 : ℂ) rBEven :=
    closedBall_subset_ball (by linarith [rBEven_pos])
  have hRb_bd : ∀ z' ∈ closedBall (0 : ℂ) (ρ ^ 2), ‖deriv R_b z'‖ ≤ M_R * ρ ^ 2 := fun z' hz' =>
    (hRb_deriv_bd z' (hcb_sub hz')).trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz') hMR_nn)
  have hmvt_Rb := (convex_closedBall (0 : ℂ) (ρ ^ 2)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hRb_an x (hcb_sub.trans hcb_ball hx)).differentiableAt) hRb_bd hw_re_cb hw_cb
  have hw_im : w.im = 2 * σp * τp := by dsimp [w]; rw [sq, Complex.mul_im, hσ_eq, hτ_eq]; ring
  have hsub_w_re : ‖w - (w.re : ℂ)‖ = 2 * σp * τp := by
    rw [show w - (w.re : ℂ) = (w.im : ℂ) * Complex.I by apply Complex.ext <;> simp]
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, hw_im,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσ_nn) hτ_nn)]
  rw [hsub_w_re] at hmvt_Rb
  have hchartB_im_eq : (chartB ζp).im = -(Real.pi / (2 * √2)) * σp * τp + (R_b w).im := by
    rw [hchartB_eq, Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add,
      neg_mul, Complex.neg_im, Complex.im_ofReal_mul, hw_im]
    ring
  have hRb_im_bd : |(R_b w).im| ≤ (4 * √2 * M_R / Real.pi) * ρ ^ 2 * (Real.pi / (2 * √2) * σp * τp) := by
    have hsub_im : |(R_b w).im| = |(R_b w - R_b (w.re : ℂ)).im| := by
      have hdiff_im : (R_b w - R_b (w.re : ℂ)).im = (R_b w).im := by
        rw [Complex.sub_im, hRb_re_im, sub_zero]
      rw [hdiff_im]
    calc |(R_b w).im| = |(R_b w - R_b (w.re : ℂ)).im| := hsub_im
      _ ≤ ‖R_b w - R_b (w.re : ℂ)‖ := Complex.abs_im_le_norm _
      _ ≤ (M_R * ρ ^ 2) * (2 * σp * τp) := hmvt_Rb
      _ = (4 * √2 * M_R / Real.pi) * ρ ^ 2 * (Real.pi / (2 * √2) * σp * τp) := by
        have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
        have hsq2_ne : √2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
        field_simp [hpi_ne, hsq2_ne]; ring
  have him_nonpos : (chartB ζp).im ≤ 0 := by
    have h1 := (abs_le.mp hRb_im_bd).2
    have hcoef_nn : 0 ≤ Real.pi / (2 * √2) * σp * τp := by positivity
    have h2 : (4 * √2 * M_R / Real.pi) * ρ ^ 2 * (Real.pi / (2 * √2) * σp * τp) ≤
        (1 / 2) * (Real.pi / (2 * √2) * σp * τp) :=
      mul_le_mul_of_nonneg_right hC3_half hcoef_nn
    linarith [h1, h2, hchartB_im_eq, hcoef_nn]
  refine ⟨?_, him_nonpos⟩
  rw [hchartB_im_eq, show -(Real.pi / (2 * √2)) * σp * τp + (R_b w).im -
    (-(Real.pi / (2 * √2)) * σp * τp) = (R_b w).im by ring]
  exact hRb_im_bd

private lemma langer_edge_claim
    {q_V : ℂ → ℂ} {c₀_max r_bd M_q : ℝ}
    (hMq_nn : 0 ≤ M_q) (hc0_le_bd : c₀_max ≤ r_bd)
    (hqV_real : ∀ x : ℝ, |x| < c₀_max → (q_V (x : ℂ)).im = 0 ∧ 0 < (q_V (x : ℂ)).re)
    (hqV_diff_bd : ∀ w ∈ closedBall (0 : ℂ) r_bd, ‖q_V w - 1‖ ≤ M_q * ‖w‖) :
    ∀ c₀ ∈ Ioo (0 : ℝ) c₀_max,
      ∀ (c' v : ℝ), 0 < c' → 0 ≤ v → v * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ →
        let u : ℂ := -(v : ℂ)
        let z : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
        let ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * q_V z
        let τ₀ := ζp.im
        0 ≤ τ₀ ∧ ζp = Complex.I * (τ₀ : ℂ) ∧
        |c' ^ (1 / 3 : ℝ) * τ₀ - kappaV * √v| ≤ M_q * c₀ * (kappaV * √v) ∧
        chartB ζp = (edgeX0 τ₀ : ℂ) := by
  intro c₀ hc₀ c' v hc' hv hv_le u z ζp τ₀
  have hv_sqrt_sq : (√v) ^ 2 = v := Real.sq_sqrt hv
  have hu_eq : u = ((((√v) ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * 0 : ℝ) : ℂ))) := by
    dsimp [u]
    rw [hv_sqrt_sq, mul_zero, sub_zero, show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_pi_mul_I, mul_neg_one]
  have hu_half : u ^ (1 / 2 : ℂ) = (√v : ℂ) * Complex.I := by
    rw [hu_eq, cpow_half_exp_angle (Real.sqrt_nonneg v) (le_refl 0) (by positivity),
      sub_zero, show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hz_real_val : z = (((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ)) : ℂ) := by
    dsimp [z, u]; push_cast; ring
  have hz_abs : |-(v * c' ^ (-(2 / 3 : ℝ)))| < c₀_max := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg hv (Real.rpow_nonneg hc'.le _))]
    exact hv_le.trans_lt hc₀.2
  obtain ⟨hq_im, hq_re_pos⟩ := hqV_real _ hz_abs
  rw [← hz_real_val] at hq_im hq_re_pos
  have hq_eq_real : q_V z = ((q_V z).re : ℂ) := Complex.ext rfl hq_im
  have hmul_I_eq : (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ((√v : ℂ) * Complex.I) * ((q_V z).re : ℂ) =
      ((kappaV * c' ^ (-(1 / 3 : ℝ)) * √v * (q_V z).re : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hτ₀_val : τ₀ = kappaV * c' ^ (-(1 / 3 : ℝ)) * √v * (q_V z).re := by
    dsimp [τ₀, ζp]
    rw [hu_half, hq_eq_real, hmul_I_eq]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]
    ring
  have hzeta_eq_I : ζp = Complex.I * (τ₀ : ℂ) := by
    dsimp [ζp]
    rw [hu_half, hq_eq_real, hmul_I_eq, hτ₀_val]; ring
  have hτ₀_nn : 0 ≤ τ₀ := by
    rw [hτ₀_val]
    exact mul_nonneg (mul_nonneg (mul_nonneg kappaV_pos.le (Real.rpow_nonneg hc'.le _))
      (Real.sqrt_nonneg v)) hq_re_pos.le
  have hz_cb : z ∈ closedBall (0 : ℂ) r_bd := by
    rw [mem_closedBall_zero_iff, hz_real_val, Complex.norm_real, Real.norm_eq_abs]
    exact (hz_abs.trans_le hc0_le_bd).le
  have hq_sub1 := hqV_diff_bd z hz_cb
  have hc'_mul : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero]
  have hband_rel : |c' ^ (1 / 3 : ℝ) * τ₀ - kappaV * √v| ≤ M_q * c₀ * (kappaV * √v) := by
    have hdiff : c' ^ (1 / 3 : ℝ) * τ₀ - kappaV * √v = (kappaV * √v) * ((q_V z).re - 1) := by
      rw [hτ₀_val]
      calc c' ^ (1 / 3 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * √v * (q_V z).re) - kappaV * √v
          = kappaV * √v * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) * (q_V z).re - kappaV * √v := by ring
        _ = kappaV * √v * 1 * (q_V z).re - kappaV * √v := by rw [hc'_mul]
        _ = (kappaV * √v) * ((q_V z).re - 1) := by ring
    rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg kappaV_pos.le (Real.sqrt_nonneg v))]
    have hre_sub : |(q_V z).re - 1| ≤ ‖q_V z - 1‖ := by
      simpa [Complex.sub_re, Complex.one_re] using Complex.abs_re_le_norm (q_V z - 1)
    have hz_norm_le : ‖z‖ ≤ c₀ := by
      rw [hz_real_val, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (mul_nonneg hv (Real.rpow_nonneg hc'.le _))]
      exact hv_le
    have hle : |(q_V z).re - 1| ≤ M_q * c₀ :=
      hre_sub.trans (hq_sub1.trans (mul_le_mul_of_nonneg_left hz_norm_le hMq_nn))
    calc kappaV * √v * |(q_V z).re - 1|
        ≤ kappaV * √v * (M_q * c₀) :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg kappaV_pos.le (Real.sqrt_nonneg v))
      _ = M_q * c₀ * (kappaV * √v) := by ring
  refine ⟨hτ₀_nn, hzeta_eq_I, hband_rel, ?_⟩
  rw [hzeta_eq_I, chartB_left_edge]

/-- **Lemma S6 (`vlo:S6`, `lower_o1_two_edge.tex`, lines 455–466)**:
Langer comparability from the Langer chart `pg : LangerChartSpec`. -/
theorem lemma_S6 (pg : LangerChartSpec) :
    (∃ r_b > 0, ∃ C_b ≥ 0,
      r_b ≤ rB0 / 2 ∧
      (∀ k : ℕ, (iteratedDeriv k bEven 0).im = 0) ∧
      (∀ ζ ∈ ball (0 : ℂ) r_b,
        ‖chartB ζ - (xiStar : ℂ) - (-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * ζ ^ 2‖ ≤
          C_b * ‖ζ‖ ^ 4)) ∧
    (∃ q_V : ℂ → ℂ, ∃ c₀_max > 0, ∃ C₁ ≥ 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      AnalyticOnNhd ℂ q_V (ball (0 : ℂ) c₀_max) ∧
      q_V 0 = 1 ∧
      (∀ k : ℕ, (iteratedDeriv k q_V 0).im = 0) ∧
      (∀ x : ℝ, |x| < c₀_max → (q_V (x : ℂ)).im = 0 ∧ 0 < (q_V (x : ℂ)).re) ∧
      (∀ c₀ ∈ Ioo (0 : ℝ) c₀_max,
        ∀ (c' a' phi : ℝ), 0 < c' → 0 ≤ a' → 0 ≤ phi → phi ≤ Real.pi / 2 →
          a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ →
          let u : ℂ := ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ))
          let z : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
          let ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * q_V z
          let σp := ζp.re
          let τp := ζp.im
          let ρ := ‖ζp‖
          ζp ^ 2 = ((kappaV ^ 2 : ℝ) : ℂ) * z * q_V z ^ 2 ∧
          chartB ζp = pg.bL z ∧
          0 ≤ σp ∧ 0 ≤ τp ∧
          |ρ - kappaV * c' ^ (-(1 / 3 : ℝ)) * a'| ≤ C₁ * c₀ * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ∧
          |σp - ρ * Real.sin phi| ≤ C₂ * ρ ^ 2 * (ρ * Real.sin phi) ∧
          |(chartB ζp).im - (-(Real.pi / (2 * √2)) * σp * τp)| ≤
            C₃ * ρ ^ 2 * (Real.pi / (2 * √2) * σp * τp) ∧
          (chartB ζp).im ≤ 0) ∧
      (∀ c₀ ∈ Ioo (0 : ℝ) c₀_max,
        ∀ (c' v : ℝ), 0 < c' → 0 ≤ v → v * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ →
          let u : ℂ := -(v : ℂ)
          let z : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
          let ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * q_V z
          let τ₀ := ζp.im
          0 ≤ τ₀ ∧ ζp = Complex.I * (τ₀ : ℂ) ∧
          |c' ^ (1 / 3 : ℝ) * τ₀ - kappaV * √v| ≤ C₁ * c₀ * (kappaV * √v) ∧
          chartB ζp = (edgeX0 τ₀ : ℂ))) := by
  obtain ⟨r_b, hr_b_pos, C_b, hCb_nn, hr_b_half, _, him_bEven, h_exp⟩ :=
    chartB_even_expansion
  refine ⟨⟨r_b, hr_b_pos, C_b, hCb_nn, hr_b_half, him_bEven, fun ζ hζ => (h_exp ζ hζ).2⟩, ?_⟩
  have hbEven0_an : AnalyticAt ℂ bEven 0 := analyticOnNhd_bEven 0 (mem_ball_self rBEven_pos)
  have hbEven0_d_ne : deriv bEven 0 ≠ 0 := by
    rw [deriv_bEven_zero]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (div_pos Real.pi_pos
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))).ne')
  have hright_ev := hbEven0_an.hasStrictDerivAt.eventually_right_inverse hbEven0_d_ne
  rw [bEven_zero] at hright_ev
  have hev_left_inv := hbEven0_an.hasStrictDerivAt.eventually_left_inverse hbEven0_d_ne
  let bInv : ℂ → ℂ := hbEven0_an.hasStrictDerivAt.localInverse bEven (deriv bEven 0) 0 hbEven0_d_ne
  have hbInv_an : AnalyticAt ℂ bInv (xiStar : ℂ) := by
    simpa [bEven_zero] using hbEven0_an.analyticAt_localInverse hbEven0_d_ne
  have hbInv_zero : bInv (xiStar : ℂ) = 0 := by
    rw [← bEven_zero]
    exact hev_left_inv.self_of_nhds
  have hbInv_deriv : deriv bInv (xiStar : ℂ) = -(4 * √2 / Real.pi : ℂ) := by
    have hd_inv : HasDerivAt bInv (deriv bEven 0)⁻¹ (bEven 0) :=
      (hbEven0_an.hasStrictDerivAt.to_localInverse hbEven0_d_ne).hasDerivAt
    rw [bEven_zero] at hd_inv
    rw [hd_inv.deriv, deriv_bEven_zero]
    push_cast; field_simp [Real.pi_pos.ne']
  let Z : ℂ → ℂ := fun z => bInv (pg.bL z)
  have hZ_an : AnalyticAt ℂ Z 0 :=
    hbInv_an.comp_of_eq (pg.hbL_an 0 (mem_ball_self pg.hrL_pos)) pg.hbL_zero
  have hZ_zero : Z 0 = 0 := by dsimp [Z]; rw [pg.hbL_zero, hbInv_zero]
  have hZ_deriv : deriv Z 0 = (kappaV ^ 2 : ℂ) := by
    have hbL_d : HasDerivAt pg.bL (deriv pg.bL 0) 0 :=
      (pg.hbL_an 0 (mem_ball_self pg.hrL_pos)).differentiableAt.hasDerivAt
    have hinv_d : HasDerivAt bInv (deriv bInv (xiStar : ℂ)) (xiStar : ℂ) :=
      hbInv_an.differentiableAt.hasDerivAt
    have hcomp : HasDerivAt Z (deriv bInv (xiStar : ℂ) * deriv pg.bL 0) 0 :=
      hinv_d.comp_of_eq 0 hbL_d pg.hbL_zero.symm
    rw [hcomp.deriv, hbInv_deriv, pg.hbL_deriv]
    rw [← Complex.ofReal_pow, kappaV_sq]
    push_cast; ring
  let Q0 : ℂ → ℂ := fun z => dslope Z 0 z / ((kappaV ^ 2 : ℝ) : ℂ)
  obtain ⟨rZ, hrZ_pos, hrZ_an⟩ := hZ_an.exists_ball_analyticOnNhd
  have hQ0_an : AnalyticOnNhd ℂ Q0 (ball (0 : ℂ) rZ) := by
    have hd_slope : DifferentiableOn ℂ (dslope Z 0) (ball (0 : ℂ) rZ) :=
      (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hrZ_pos))).mpr
        hrZ_an.differentiableOn
    exact (hd_slope.analyticOnNhd isOpen_ball).div analyticOnNhd_const fun _ _ =>
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 kappaV_pos.ne')
  have hQ0_zero : Q0 0 = 1 := by
    dsimp [Q0]
    rw [dslope_same, hZ_deriv, ← Complex.ofReal_pow,
      div_self (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 kappaV_pos.ne'))]
  let q_V : ℂ → ℂ := fun z => (Q0 z) ^ (1 / 2 : ℂ)
  have hqV_zero_an : AnalyticAt ℂ q_V 0 :=
    (hQ0_an 0 (mem_ball_self hrZ_pos)).cpow analyticAt_const (by rw [hQ0_zero]; exact Complex.one_mem_slitPlane)
  obtain ⟨rq, hrq_pos, hrq_an⟩ := hqV_zero_an.exists_ball_analyticOnNhd
  have hqV_zero : q_V 0 = 1 := by simp [q_V, hQ0_zero]
  have hcont_inv : ContinuousAt bInv (xiStar : ℂ) := hbInv_an.continuousAt
  have hcont_bL : ContinuousAt pg.bL 0 := (pg.hbL_an 0 (mem_ball_self pg.hrL_pos)).continuousAt
  have hreal_bInv : ∀ᶠ w in 𝓝 (xiStar : ℂ), bInv (starRingEnd ℂ w) = starRingEnd ℂ (bInv w) := by
    have hinv_b : ∀ᶠ w in 𝓝 (xiStar : ℂ),
        bInv w ∈ ball (0 : ℂ) rBEven ∧ bInv (starRingEnd ℂ w) ∈ ball (0 : ℂ) rBEven := by
      have h1 : ∀ᶠ w in 𝓝 (xiStar : ℂ), bInv w ∈ ball (0 : ℂ) rBEven := by
        have hc := hcont_inv; rw [ContinuousAt, hbInv_zero] at hc
        exact hc (Metric.ball_mem_nhds 0 rBEven_pos)
      have h2 : ∀ᶠ w in 𝓝 (xiStar : ℂ), bInv (starRingEnd ℂ w) ∈ ball (0 : ℂ) rBEven := by
        have hc0 : ContinuousAt bInv (starRingEnd ℂ (xiStar : ℂ)) := by
          rw [Complex.conj_ofReal]; exact hcont_inv
        have hc : ContinuousAt (fun w => bInv (starRingEnd ℂ w)) (xiStar : ℂ) :=
          hc0.comp Complex.conjCLE.continuous.continuousAt
        rw [ContinuousAt, Complex.conj_ofReal, hbInv_zero] at hc
        exact hc (Metric.ball_mem_nhds 0 rBEven_pos)
      exact h1.and h2
    have hleft1 : ∀ᶠ w in 𝓝 (xiStar : ℂ),
        bInv (bEven (starRingEnd ℂ (bInv w))) = starRingEnd ℂ (bInv w) := by
      have hc : ContinuousAt (fun w => starRingEnd ℂ (bInv w)) (xiStar : ℂ) :=
        Complex.conjCLE.continuous.continuousAt.comp hcont_inv
      rw [ContinuousAt, hbInv_zero, map_zero] at hc
      exact hc hev_left_inv
    have hright_conj : ∀ᶠ w in 𝓝 (xiStar : ℂ), bEven (bInv (starRingEnd ℂ w)) = starRingEnd ℂ w := by
      have hc : Filter.Tendsto (starRingEnd ℂ) (𝓝 (xiStar : ℂ)) (𝓝 (xiStar : ℂ)) := by
        simpa [Complex.conj_ofReal] using (continuous_star.continuousAt (x := (xiStar : ℂ))).tendsto
      exact hc hright_ev
    filter_upwards [hinv_b, hleft1, hright_ev, hright_conj] with w hw hleft hw_r hw_rc
    have heq_beven : bEven (bInv (starRingEnd ℂ w)) = bEven (starRingEnd ℂ (bInv w)) := by
      rw [hw_rc, bEven_conj hw.1, hw_r]
    rw [← heq_beven, hw_rc] at hleft
    exact hleft
  obtain ⟨r_conj, hr_conj_pos, hr_conj⟩ := Metric.eventually_nhds_iff_ball.mp hreal_bInv
  have hev_all : ∀ᶠ z in 𝓝 (0 : ℂ),
      z ∈ ball (0 : ℂ) rZ ∧
      z ∈ ball (0 : ℂ) rq ∧
      z ∈ ball (0 : ℂ) pg.rL ∧
      pg.bL z ∈ ball (xiStar : ℂ) r_conj ∧
      Z z ∈ ball (0 : ℂ) rBEven ∧
      bEven (Z z) = pg.bL z ∧
      0 < (Q0 z).re ∧
      (1 / 2 : ℝ) ≤ (q_V z).re ∧
      ‖q_V z‖ ≤ 3 / 2 := by
    refine Filter.Eventually.and (Metric.ball_mem_nhds 0 hrZ_pos) ?_
    refine Filter.Eventually.and (Metric.ball_mem_nhds 0 hrq_pos) ?_
    refine Filter.Eventually.and (Metric.ball_mem_nhds 0 pg.hrL_pos) ?_
    refine Filter.Eventually.and ?_ ?_
    · rw [ContinuousAt, pg.hbL_zero] at hcont_bL
      exact hcont_bL (Metric.ball_mem_nhds (xiStar : ℂ) hr_conj_pos)
    · have hz_ball : ∀ᶠ z in 𝓝 (0 : ℂ), Z z ∈ ball (0 : ℂ) rBEven := by
        have hc := hZ_an.continuousAt; rw [ContinuousAt, hZ_zero] at hc
        exact hc (Metric.ball_mem_nhds 0 rBEven_pos)
      have hbe : ∀ᶠ z in 𝓝 (0 : ℂ), bEven (Z z) = pg.bL z := by
        have hc : ContinuousAt pg.bL 0 := (pg.hbL_an 0 (mem_ball_self pg.hrL_pos)).continuousAt
        rw [ContinuousAt, pg.hbL_zero] at hc
        exact hc hright_ev
      have hQ_pos : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < (Q0 z).re := by
        have hc : ContinuousAt (fun z => (Q0 z).re) 0 :=
          Complex.continuous_re.continuousAt.comp (hQ0_an 0 (mem_ball_self hrZ_pos)).continuousAt
        rw [ContinuousAt, show (Q0 0).re = 1 by rw [hQ0_zero, Complex.one_re]] at hc
        exact hc (Ioi_mem_nhds (by linarith))
      have hq_re : ∀ᶠ z in 𝓝 (0 : ℂ), (1 / 2 : ℝ) ≤ (q_V z).re := by
        have hc : ContinuousAt (fun z => (q_V z).re) 0 :=
          Complex.continuous_re.continuousAt.comp hqV_zero_an.continuousAt
        rw [ContinuousAt, show (q_V 0).re = 1 by rw [hqV_zero, Complex.one_re]] at hc
        exact hc (Ici_mem_nhds (by linarith))
      have hq_norm : ∀ᶠ z in 𝓝 (0 : ℂ), ‖q_V z‖ ≤ 3 / 2 := by
        have hc := hqV_zero_an.continuousAt.norm
        rw [ContinuousAt, show ‖q_V 0‖ = 1 by rw [hqV_zero, norm_one]] at hc
        exact hc (Iic_mem_nhds (by linarith))
      exact hz_ball.and (hbe.and (hQ_pos.and (hq_re.and hq_norm)))
  obtain ⟨r_ev, hr_ev_pos, hr_ev⟩ := Metric.eventually_nhds_iff_ball.mp hev_all
  let r_bd : ℝ := r_ev / 2
  have hr_bd_pos : 0 < r_bd := half_pos hr_ev_pos
  have hcl_rq : closedBall (0 : ℂ) r_bd ⊆ ball (0 : ℂ) rq := by
    intro w hw; rw [mem_closedBall_zero_iff] at hw
    exact (hr_ev _ (mem_ball_zero_iff.mpr (hw.trans_lt (by dsimp [r_bd]; linarith)))).2.1
  obtain ⟨M_q0, hM_q0⟩ := (isCompact_closedBall (0 : ℂ) r_bd).exists_bound_of_continuousOn
    (hrq_an.deriv.continuousOn.mono hcl_rq)
  let M_q : ℝ := max M_q0 0
  have hMq_nn : 0 ≤ M_q := le_max_right _ _
  have hq'_bd : ∀ w ∈ closedBall (0 : ℂ) r_bd, ‖deriv q_V w‖ ≤ M_q := fun w hw =>
    (hM_q0 w hw).trans (le_max_left _ _)
  let R_b : ℂ → ℂ := fun w => bEven w - (xiStar : ℂ) - deriv bEven 0 * w
  have hRb_an : AnalyticOnNhd ℂ R_b (ball (0 : ℂ) rBEven) := fun w hw =>
    ((analyticOnNhd_bEven w hw).sub analyticAt_const).sub (analyticAt_const.mul analyticAt_id)
  have hRb0_deriv : deriv R_b 0 = 0 := by
    have hb0 : HasDerivAt bEven (deriv bEven 0) 0 :=
      (analyticOnNhd_bEven 0 (mem_ball_self rBEven_pos)).differentiableAt.hasDerivAt
    have hd := (hb0.sub_const (xiStar : ℂ)).fun_sub ((hasDerivAt_id (0 : ℂ)).const_mul (deriv bEven 0))
    simpa [R_b] using hd.deriv
  let gR : ℂ → ℂ := dslope (deriv R_b) 0
  have hgR_an : AnalyticOnNhd ℂ gR (ball (0 : ℂ) rBEven) := by
    have hd1 : DifferentiableOn ℂ (deriv R_b) (ball (0 : ℂ) rBEven) :=
      hRb_an.deriv.differentiableOn
    have hd2 : DifferentiableOn ℂ gR (ball (0 : ℂ) rBEven) :=
      (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self rBEven_pos))).mpr hd1
    exact hd2.analyticOnNhd isOpen_ball
  obtain ⟨M_R0, hM_R0⟩ := (isCompact_closedBall (0 : ℂ) (rBEven / 2)).exists_bound_of_continuousOn
    (hgR_an.continuousOn.mono (closedBall_subset_ball (by linarith [rBEven_pos])))
  let M_R : ℝ := max M_R0 0
  have hMR_nn : 0 ≤ M_R := le_max_right _ _
  have hRb_deriv_bd : ∀ w ∈ closedBall (0 : ℂ) (rBEven / 2), ‖deriv R_b w‖ ≤ M_R * ‖w‖ := by
    intro w hw
    have hw_eq : w * gR w = deriv R_b w := by
      have h0 := sub_smul_dslope (deriv R_b) (0 : ℂ) w
      simpa [gR, hRb0_deriv, sub_zero, smul_eq_mul] using h0
    rw [← hw_eq, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hM_R0 w hw).trans (le_max_left _ _)) (norm_nonneg w)
  let C₁ : ℝ := M_q
  let C₂ : ℝ := 48 * M_q / kappaV ^ 2
  let C₃ : ℝ := 4 * √2 * M_R / Real.pi
  have hC₂_nn : 0 ≤ C₂ := by have := kappaV_pos; positivity
  have hC₃_nn : 0 ≤ C₃ := by positivity
  let c₀_max : ℝ := min r_bd
    (min ((r_b / 2) ^ 2 / (4 * kappaV ^ 2))
      (min (rBEven / (8 * kappaV ^ 2))
        (min (1 / (8 * kappaV ^ 2 * max C₂ 1))
          (1 / (8 * kappaV ^ 2 * max C₃ 1)))))
  have hc₀_pos : 0 < c₀_max := by
    dsimp [c₀_max]
    have := hr_bd_pos
    have := hr_b_pos
    have := rBEven_pos
    have := kappaV_pos
    positivity
  have hqV_real : ∀ x : ℝ, |x| < c₀_max → (q_V (x : ℂ)).im = 0 ∧ 0 < (q_V (x : ℂ)).re := by
    intro x hx
    have hx_bd : |x| < r_bd := hx.trans_le (min_le_left _ _)
    have hx_ev : (x : ℂ) ∈ ball (0 : ℂ) r_ev := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; dsimp [r_bd] at hx_bd; linarith
    have hev_x := hr_ev _ hx_ev
    have hx_bL_im : (pg.bL (x : ℂ)).im = 0 := pg.hbL_real x (by
      have := hev_x.2.2.1; rwa [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at this)
    have hZ_conj : starRingEnd ℂ (Z (x : ℂ)) = Z (x : ℂ) := by
      dsimp [Z]
      have hconj_bL : starRingEnd ℂ (pg.bL (x : ℂ)) = pg.bL (x : ℂ) := Complex.ext rfl (by simp [hx_bL_im])
      rw [← hr_conj _ hev_x.2.2.2.1, hconj_bL]
    have hZ_im : (Z (x : ℂ)).im = 0 := by
      have hneg : -(Z (x : ℂ)).im = (Z (x : ℂ)).im := by
        simpa using congrArg Complex.im hZ_conj
      linarith
    have hQ_im : (Q0 (x : ℂ)).im = 0 := by
      by_cases hx0 : x = 0
      · subst hx0; simp [hQ0_zero]
      · dsimp [Q0]
        rw [dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx0), slope_def_field, hZ_zero, sub_zero,
          sub_zero, div_div, show ((x : ℂ) * ((kappaV ^ 2 : ℝ) : ℂ)) = ((x * kappaV ^ 2 : ℝ) : ℂ) by
            push_cast; ring, Complex.div_ofReal_im, hZ_im, zero_div]
    have hQ_pos : 0 < (Q0 (x : ℂ)).re := hev_x.2.2.2.2.2.2.1
    have hQ_eq : Q0 (x : ℂ) = (((Q0 (x : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hQ_im
    have hq_eq : q_V (x : ℂ) = (√((Q0 (x : ℂ)).re) : ℂ) := by
      dsimp [q_V]; rw [hQ_eq, cpow_half_ofReal_nonneg hQ_pos.le, Complex.ofReal_re]
    rw [hq_eq, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, Real.sqrt_pos.mpr hQ_pos⟩
  have hqV_an_c0 : AnalyticOnNhd ℂ q_V (ball (0 : ℂ) c₀_max) :=
    (hrq_an.mono (ball_subset_closedBall.trans hcl_rq)).mono (ball_subset_ball (min_le_left _ _))
  have hqV_im_iter : ∀ k : ℕ, (iteratedDeriv k q_V 0).im = 0 := fun k =>
    iteratedDeriv_real_on_ball k q_V hqV_an_c0 (fun x hx => (hqV_real x hx).1) 0
      (by simpa using hc₀_pos)
  have hqV_diff_bd : ∀ w ∈ closedBall (0 : ℂ) r_bd,
      ‖q_V w - 1‖ ≤ M_q * ‖w‖ ∧
      ‖q_V w - q_V (w.re : ℂ)‖ ≤ M_q * |w.im| := by
    intro w hw
    have hre_cb : (w.re : ℂ) ∈ closedBall (0 : ℂ) r_bd := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm w).trans (mem_closedBall_zero_iff.mp hw)
    have hdiff_on : DifferentiableOn ℂ q_V (closedBall (0 : ℂ) r_bd) :=
      hrq_an.differentiableOn.mono hcl_rq
    have h_mvt0 := (convex_closedBall (0 : ℂ) r_bd).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hrq_an x (hcl_rq hx)).differentiableAt) hq'_bd (mem_closedBall_self hr_bd_pos.le) hw
    have h_mvt1 := (convex_closedBall (0 : ℂ) r_bd).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hrq_an x (hcl_rq hx)).differentiableAt) hq'_bd hre_cb hw
    rw [hqV_zero, sub_zero] at h_mvt0
    have hsub_re : ‖w - (w.re : ℂ)‖ = |w.im| := by
      rw [show w - (w.re : ℂ) = (w.im : ℂ) * Complex.I by apply Complex.ext <;> simp]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    rw [hsub_re] at h_mvt1
    exact ⟨h_mvt0, h_mvt1⟩
  refine ⟨q_V, c₀_max, hc₀_pos, C₁, hMq_nn, C₂, hC₂_nn, C₃, hC₃_nn,
    hqV_an_c0, hqV_zero, hqV_im_iter, hqV_real, ?_, ?_⟩
  · intro c₀ hc₀ c' a' phi hc' ha' hphi0 hphi1 ha_le u z ζp σp τp ρ
    have hz_norm : ‖z‖ = a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) := by
      dsimp [z, u]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (sq_nonneg a'), Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _),
        show Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ) =
          ((Real.pi - 2 * phi : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hz_le_c0 : ‖z‖ ≤ c₀ := by rw [hz_norm]; exact ha_le
    have hz_lt_c0max : ‖z‖ < c₀_max := hz_le_c0.trans_lt hc₀.2
    have hz_cb : z ∈ closedBall (0 : ℂ) r_bd := by
      rw [mem_closedBall_zero_iff]
      exact (hz_lt_c0max.trans_le (min_le_left _ _)).le
    have hz_ev : z ∈ ball (0 : ℂ) r_ev := by
      rw [mem_ball_zero_iff]
      exact (mem_closedBall_zero_iff.mp hz_cb).trans_lt (by dsimp [r_bd]; linarith)
    have hev_z := hr_ev z hz_ev
    have hc'_pow_sq : (c' ^ (-(1 / 3 : ℝ))) ^ 2 = c' ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast (c' ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc'.le]
      norm_num
    have hzeta_sq : ζp ^ 2 = ((kappaV ^ 2 : ℝ) : ℂ) * z * q_V z ^ 2 := by
      dsimp [ζp, z]
      rw [mul_pow, mul_pow, mul_pow, cpow_half_sq, ← Complex.ofReal_pow (c' ^ (-(1 / 3 : ℝ))),
        hc'_pow_sq]
      push_cast; ring
    have hZ_eq_sq : Z z = ζp ^ 2 := by
      rw [hzeta_sq]
      dsimp [Q0, q_V]
      rw [cpow_half_sq]
      have hd_slope := sub_smul_dslope Z (0 : ℂ) z
      rw [sub_zero, hZ_zero, sub_zero, smul_eq_mul] at hd_slope
      have hk_ne : ((kappaV ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 kappaV_pos.ne')
      rw [show ((kappaV ^ 2 : ℝ) : ℂ) * z * (dslope Z 0 z / ((kappaV ^ 2 : ℝ) : ℂ)) =
          (z * dslope Z 0 z) * (((kappaV ^ 2 : ℝ) : ℂ) / ((kappaV ^ 2 : ℝ) : ℂ)) by ring,
        div_self hk_ne, mul_one, hd_slope]
    have hrho_eq : ρ = kappaV * c' ^ (-(1 / 3 : ℝ)) * a' * ‖q_V z‖ := by
      dsimp [ρ, ζp, u]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg kappaV_pos.le, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _),
        cpow_half_exp_angle ha' hphi0 hphi1, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ha',
        show Complex.I * ((Real.pi / 2 - phi : ℝ) : ℂ) =
          ((Real.pi / 2 - phi : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hrho_sq_le : ρ ^ 2 ≤ 4 * kappaV ^ 2 * c₀ := by
      rw [hrho_eq]
      have hq_norm_le : ‖q_V z‖ ≤ 3 / 2 := hev_z.2.2.2.2.2.2.2.2
      have hsq_r : (kappaV * c' ^ (-(1 / 3 : ℝ)) * a' * ‖q_V z‖) ^ 2 =
          kappaV ^ 2 * (a' ^ 2 * c' ^ (-(2 / 3 : ℝ))) * ‖q_V z‖ ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, hc'_pow_sq]; ring
      rw [hsq_r]
      have h94 : ‖q_V z‖ ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
        nlinarith [norm_nonneg (q_V z)]
      have h1 : kappaV ^ 2 * (a' ^ 2 * c' ^ (-(2 / 3 : ℝ))) * ‖q_V z‖ ^ 2 ≤
          kappaV ^ 2 * c₀ * (3 / 2) ^ 2 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left ha_le (sq_nonneg _)) h94 (sq_nonneg _)
          (mul_nonneg (sq_nonneg _) hc₀.1.le)
      linarith [show kappaV ^ 2 * c₀ * (3 / 2 : ℝ) ^ 2 ≤ 4 * kappaV ^ 2 * c₀ by
        nlinarith [hc₀.1, kappaV_pos]]
    have hrho_lt_rb : ρ < r_b := by
      have hc0_rb : c₀ < (r_b / 2) ^ 2 / (4 * kappaV ^ 2) :=
        hc₀.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hk_sq : 0 < 4 * kappaV ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos kappaV_pos)
      have hrho_sq_lt : ρ ^ 2 < (r_b / 2) ^ 2 := by
        calc ρ ^ 2 ≤ 4 * kappaV ^ 2 * c₀ := hrho_sq_le
          _ < 4 * kappaV ^ 2 * ((r_b / 2) ^ 2 / (4 * kappaV ^ 2)) :=
              mul_lt_mul_of_pos_left hc0_rb hk_sq
          _ = (r_b / 2) ^ 2 := by rw [mul_div_cancel₀ _ hk_sq.ne']
      have hlt_half : ρ < r_b / 2 := by
        by_contra h
        push Not at h
        nlinarith [norm_nonneg ζp]
      linarith
    have hb_zeta_eq : chartB ζp = pg.bL z := by
      have hζ_mem : ζp ∈ ball (0 : ℂ) r_b := mem_ball_zero_iff.mpr hrho_lt_rb
      rw [(h_exp ζp hζ_mem).1, ← hZ_eq_sq]
      exact hev_z.2.2.2.2.2.1
    obtain ⟨hq_sub1, hq_sub_re⟩ := hqV_diff_bd z hz_cb
    have hrho_rel : |ρ - kappaV * c' ^ (-(1 / 3 : ℝ)) * a'| ≤
        C₁ * c₀ * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') := by
      have hdiff_eq : ρ - kappaV * c' ^ (-(1 / 3 : ℝ)) * a' =
          (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') * (‖q_V z‖ - 1) := by
        rw [hrho_eq]; ring
      have hρ₀_nn : 0 ≤ kappaV * c' ^ (-(1 / 3 : ℝ)) * a' :=
        mul_nonneg (mul_nonneg kappaV_pos.le (Real.rpow_nonneg hc'.le _)) ha'
      rw [hdiff_eq, abs_mul, abs_of_nonneg hρ₀_nn]
      have hnorm_diff : |‖q_V z‖ - 1| ≤ ‖q_V z - 1‖ := by
        simpa [norm_one] using abs_norm_sub_norm_le (q_V z) 1
      have hle : |‖q_V z‖ - 1| ≤ C₁ * c₀ :=
        hnorm_diff.trans (hq_sub1.trans (mul_le_mul_of_nonneg_left hz_le_c0 hMq_nn))
      calc kappaV * c' ^ (-(1 / 3 : ℝ)) * a' * |‖q_V z‖ - 1|
          ≤ kappaV * c' ^ (-(1 / 3 : ℝ)) * a' * (C₁ * c₀) :=
            mul_le_mul_of_nonneg_left hle hρ₀_nn
        _ = C₁ * c₀ * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') := by ring
    have hsin_nn : 0 ≤ Real.sin phi :=
      Real.sin_nonneg_of_nonneg_of_le_pi hphi0 (hphi1.trans (by linarith [Real.pi_pos]))
    have hcos_nn : 0 ≤ Real.cos phi :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hphi1⟩
    set ρ₀ := kappaV * c' ^ (-(1 / 3 : ℝ)) * a'
    set x_q := (q_V z).re
    set y_q := (q_V z).im
    set n_q := ‖q_V z‖
    have hnq_lo : (1 / 2 : ℝ) ≤ n_q := hev_z.2.2.2.2.2.2.2.1.trans (Complex.re_le_norm (q_V z))
    have hnq_hi : n_q ≤ 3 / 2 := hev_z.2.2.2.2.2.2.2.2
    have hxq_lo : (1 / 2 : ℝ) ≤ x_q := hev_z.2.2.2.2.2.2.2.1
    have hzeta_re_im : σp = ρ₀ * (Real.sin phi * x_q - Real.cos phi * y_q) ∧
        τp = ρ₀ * (Real.cos phi * x_q + Real.sin phi * y_q) := by
      have hhalf_eq : u ^ (1 / 2 : ℂ) =
          (a' : ℂ) * ((Real.sin phi : ℂ) + (Real.cos phi : ℂ) * Complex.I) := by
        dsimp [u]
        rw [cpow_half_exp_angle ha' hphi0 hphi1,
          show Complex.I * ((Real.pi / 2 - phi : ℝ) : ℂ) =
            ((Real.pi / 2 - phi : ℝ) : ℂ) * Complex.I by ring,
          Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
      have hzeta_eq : ζp = (ρ₀ : ℂ) * (((Real.sin phi : ℂ) + (Real.cos phi : ℂ) * Complex.I) * q_V z) := by
        dsimp [ζp, ρ₀]; rw [hhalf_eq]; push_cast; ring
      have hre_eq : ζp.re = ρ₀ * (Real.sin phi * x_q - Real.cos phi * y_q) := by
        rw [hzeta_eq, Complex.re_ofReal_mul, Complex.mul_re]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
          add_zero, mul_one, zero_add]
        dsimp [x_q, y_q]
      have him_eq : ζp.im = ρ₀ * (Real.cos phi * x_q + Real.sin phi * y_q) := by
        rw [hzeta_eq, Complex.im_ofReal_mul, Complex.mul_im]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
          add_zero, mul_one, zero_add]
        dsimp [x_q, y_q]; ring
      exact ⟨hre_eq, him_eq⟩
    have hz_im : |z.im| = ‖z‖ * (2 * Real.sin phi * Real.cos phi) := by
      have him_eq : z.im = a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) * Real.sin (Real.pi - 2 * phi) := by
        dsimp [z, u]
        rw [mul_comm Complex.I ((Real.pi - 2 * phi : ℝ) : ℂ),
          show ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (((Real.pi - 2 * phi : ℝ) : ℂ) * Complex.I) *
              ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
            ((a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
              Complex.exp (((Real.pi - 2 * phi : ℝ) : ℂ) * Complex.I) by
                rw [Complex.ofReal_mul, Complex.ofReal_pow]; ring,
          Complex.im_ofReal_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, mul_one, mul_zero, zero_add, add_zero]
      rw [him_eq, Real.sin_pi_sub, Real.sin_two_mul, abs_mul, hz_norm,
        abs_of_nonneg (mul_nonneg (sq_nonneg a') (Real.rpow_nonneg hc'.le _)),
        abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsin_nn) hcos_nn)]
    have hyq_bd : |y_q| ≤ M_q * ‖z‖ * (2 * Real.sin phi * Real.cos phi) := by
      have hre_cb_real : |(z.re : ℝ)| < c₀_max := (Complex.abs_re_le_norm z).trans_lt hz_lt_c0max
      have hq_re_im : (q_V (z.re : ℂ)).im = 0 := (hqV_real z.re hre_cb_real).1
      have h_sub : |y_q| = |(q_V z - q_V (z.re : ℂ)).im| := by
        have hdiff_im : (q_V z - q_V (z.re : ℂ)).im = y_q := by
          change (q_V z).im - (q_V (z.re : ℂ)).im = (q_V z).im
          rw [hq_re_im, sub_zero]
        rw [hdiff_im]
      calc |y_q| = |(q_V z - q_V (z.re : ℂ)).im| := h_sub
        _ ≤ ‖q_V z - q_V (z.re : ℂ)‖ := Complex.abs_im_le_norm _
        _ ≤ M_q * |z.im| := hq_sub_re
        _ = M_q * ‖z‖ * (2 * Real.sin phi * Real.cos phi) := by rw [hz_im]; ring
    have hz_rho_sq : ‖z‖ ≤ (4 / kappaV ^ 2) * ρ ^ 2 := by
      by_cases ha0 : a' = 0
      · subst ha0; rw [hz_norm, zero_pow two_ne_zero, zero_mul]; exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
      · have hρ_eq : ρ = ρ₀ * n_q := hrho_eq
        have hρ₀_nn : 0 ≤ ρ₀ := by
          dsimp [ρ₀]
          exact mul_nonneg (mul_nonneg kappaV_pos.le (Real.rpow_nonneg hc'.le _)) ha'
        have hρ₀_le : ρ₀ ≤ 2 * ρ := by
          calc ρ₀ = ρ₀ * 2 * (1 / 2) := by ring
            _ ≤ ρ₀ * 2 * n_q := mul_le_mul_of_nonneg_left hnq_lo (mul_nonneg hρ₀_nn (by norm_num))
            _ = 2 * (ρ₀ * n_q) := by ring
            _ = 2 * ρ := by rw [← hρ_eq]
        have hz_eq_r0 : ‖z‖ = (ρ₀ / kappaV) ^ 2 := by
          rw [hz_norm]; dsimp [ρ₀]; rw [div_pow, mul_pow, mul_pow, hc'_pow_sq]
          field_simp [kappaV_pos.ne']
        rw [hz_eq_r0]
        calc (ρ₀ / kappaV) ^ 2 = ρ₀ ^ 2 / kappaV ^ 2 := div_pow _ _ _
          _ ≤ (2 * ρ) ^ 2 / kappaV ^ 2 :=
              div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ₀_nn hρ₀_le 2) (sq_nonneg kappaV)
          _ = (4 / kappaV ^ 2) * ρ ^ 2 := by ring
    have hyq_sin_cos : |y_q| ≤ (8 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi * Real.cos phi := by
      calc |y_q| ≤ M_q * ‖z‖ * (2 * Real.sin phi * Real.cos phi) := hyq_bd
        _ ≤ M_q * ((4 / kappaV ^ 2) * ρ ^ 2) * (2 * Real.sin phi * Real.cos phi) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz_rho_sq hMq_nn)
              (mul_nonneg (mul_nonneg (by norm_num) hsin_nn) hcos_nn)
        _ = (8 * M_q / kappaV ^ 2) * ρ ^ 2 * Real.sin phi * Real.cos phi := by ring
    have hC2_half : C₂ * ρ ^ 2 ≤ 1 / 2 := by
      have hc0_c2 : c₀ < 1 / (8 * kappaV ^ 2 * max C₂ 1) :=
        hc₀.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
      have h4kc : 4 * kappaV ^ 2 * c₀ ≤ 1 / (2 * max C₂ 1) := by
        calc 4 * kappaV ^ 2 * c₀ ≤ 4 * kappaV ^ 2 * (1 / (8 * kappaV ^ 2 * max C₂ 1)) :=
              mul_le_mul_of_nonneg_left hc0_c2.le (mul_nonneg (by norm_num) (sq_nonneg kappaV))
          _ = 1 / (2 * max C₂ 1) := by
            have hk_ne : kappaV ≠ 0 := kappaV_pos.ne'
            have hm_ne : max C₂ 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_max_right C₂ 1)).ne'
            field_simp [hk_ne, hm_ne]; ring
      calc C₂ * ρ ^ 2 ≤ C₂ * (4 * kappaV ^ 2 * c₀) := mul_le_mul_of_nonneg_left hrho_sq_le hC₂_nn
        _ ≤ C₂ * (1 / (2 * max C₂ 1)) := mul_le_mul_of_nonneg_left h4kc hC₂_nn
        _ ≤ max C₂ 1 * (1 / (2 * max C₂ 1)) :=
            mul_le_mul_of_nonneg_right (le_max_left C₂ 1) (by positivity)
        _ = 1 / 2 := by
            have hm_ne : max C₂ 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_max_right C₂ 1)).ne'
            field_simp [hm_ne]
    have hsq_id : n_q ^ 2 = x_q ^ 2 + y_q ^ 2 := by
      dsimp [n_q, x_q, y_q]; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
    obtain ⟨hsigma_rel, hsigma_nn, htau_nn⟩ := langer_sigma_tau_bounds
      (norm_nonneg ζp) hMq_nn hsin_nn hcos_nn hnq_lo hnq_hi hxq_lo hsq_id
      (Complex.re_le_norm (q_V z)) (Complex.abs_im_le_norm (q_V z)) hrho_eq
      hzeta_re_im.1 hzeta_re_im.2 hyq_sin_cos hC2_half
    have hw_lt_half : ‖ζp ^ 2‖ ≤ rBEven / 2 := by
      have hc0_be : c₀ < rBEven / (8 * kappaV ^ 2) :=
        hc₀.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      rw [norm_pow]
      calc ρ ^ 2 ≤ 4 * kappaV ^ 2 * c₀ := hrho_sq_le
        _ ≤ 4 * kappaV ^ 2 * (rBEven / (8 * kappaV ^ 2)) :=
            mul_le_mul_of_nonneg_left hc0_be.le (mul_nonneg (by norm_num) (sq_nonneg kappaV))
        _ = rBEven / 2 := by field_simp [kappaV_pos.ne']; ring
    have hRb_re_im : (R_b ((ζp ^ 2).re : ℂ)).im = 0 := by
      dsimp [R_b]
      have hre_lt : |(ζp ^ 2).re| < rBEven :=
        (Complex.abs_re_le_norm (ζp ^ 2)).trans_lt (hw_lt_half.trans_lt (by linarith [rBEven_pos]))
      have h1 : (bEven ((ζp ^ 2).re : ℂ)).im = 0 := bEven_ofReal_im_zero hre_lt
      have h2 : ((xiStar : ℂ)).im = 0 := Complex.ofReal_im _
      have h3 : (deriv bEven 0 * ((ζp ^ 2).re : ℂ)).im = 0 := by
        rw [deriv_bEven_zero, neg_mul, Complex.neg_im, ← Complex.ofReal_mul,
          Complex.ofReal_im, neg_zero]
      change (bEven ((ζp ^ 2).re : ℂ)).im - ((xiStar : ℂ)).im -
        (deriv bEven 0 * ((ζp ^ 2).re : ℂ)).im = 0
      rw [h1, h2, h3, sub_zero, sub_zero]
    have hchartB_eq : chartB ζp =
        (xiStar : ℂ) + (-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * (ζp ^ 2) + R_b (ζp ^ 2) := by
      have hζ_mem : ζp ∈ ball (0 : ℂ) r_b := mem_ball_zero_iff.mpr hrho_lt_rb
      rw [(h_exp ζp hζ_mem).1]
      dsimp [R_b]
      rw [deriv_bEven_zero]
      ring
    have hC3_half : (4 * √2 * M_R / Real.pi) * ρ ^ 2 ≤ 1 / 2 := by
      have hc0_c3 : c₀ < 1 / (8 * kappaV ^ 2 * max C₃ 1) :=
        hc₀.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))
      have h4kc : 4 * kappaV ^ 2 * c₀ ≤ 1 / (2 * max C₃ 1) := by
        calc 4 * kappaV ^ 2 * c₀ ≤ 4 * kappaV ^ 2 * (1 / (8 * kappaV ^ 2 * max C₃ 1)) :=
              mul_le_mul_of_nonneg_left hc0_c3.le (mul_nonneg (by norm_num) (sq_nonneg kappaV))
          _ = 1 / (2 * max C₃ 1) := by
            have hk_ne : kappaV ≠ 0 := kappaV_pos.ne'
            have hm_ne : max C₃ 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_max_right C₃ 1)).ne'
            field_simp [hk_ne, hm_ne]; ring
      calc C₃ * ρ ^ 2 ≤ C₃ * (4 * kappaV ^ 2 * c₀) := mul_le_mul_of_nonneg_left hrho_sq_le hC₃_nn
        _ ≤ C₃ * (1 / (2 * max C₃ 1)) := mul_le_mul_of_nonneg_left h4kc hC₃_nn
        _ ≤ max C₃ 1 * (1 / (2 * max C₃ 1)) :=
            mul_le_mul_of_nonneg_right (le_max_left C₃ 1) (by positivity)
        _ = 1 / 2 := by
            have hm_ne : max C₃ 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_max_right C₃ 1)).ne'
            field_simp [hm_ne]
    obtain ⟨him_rel, him_nonpos⟩ := langer_im_bound hMR_nn hsigma_nn htau_nn rfl rfl rfl hw_lt_half
      hRb_an hRb_deriv_bd hRb_re_im hchartB_eq hC3_half
    exact ⟨hzeta_sq, hb_zeta_eq, hsigma_nn, htau_nn, hrho_rel, hsigma_rel, him_rel, him_nonpos⟩
  · exact langer_edge_claim hMq_nn (min_le_left _ _) hqV_real (fun w hw => (hqV_diff_bd w hw).1)

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_S6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S6

end FormalResearch.ModularBootstrap.Chart
