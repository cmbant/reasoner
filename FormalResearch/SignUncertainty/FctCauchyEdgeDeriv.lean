/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingWarp

/-!
# Edge derivatives of `C_σ(ζ)` and `q₁(ζ)` (`fct:splitting` (2), `(fct:Fminus-edge)`)

Uniform `C⁰`, `C¹`, `C²` estimates along vertical lines `Re ζ = σ_ζ` separated by `≥ 3/8` from the
contour `Re t = σ ∈ [3/8, 7/16]` (`fctCauchy_line_deriv_bounds`), and uniform bounds on `q₁, q₁', q₁''`
in the closed right half-plane (`fctQ1_deriv_bounds`).

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-! ### Algebraic decomposition of the splitting kernel and derivatives -/

private noncomputable def cauchyP (w : ℂ) : ℂ := (w / (w + 1)) ^ 2
private noncomputable def cauchyP1 (w : ℂ) : ℂ := 2 * w / (w + 1) ^ 3
private noncomputable def cauchyP2 (w : ℂ) : ℂ := (2 - 4 * w) / (w + 1) ^ 4

private noncomputable def cauchyQ (t w : ℂ) : ℂ := -1 + t / (t - w)
private noncomputable def cauchyQ1 (t w : ℂ) : ℂ := t / (t - w) ^ 2
private noncomputable def cauchyQ2 (t w : ℂ) : ℂ := 2 * t / (t - w) ^ 3

private lemma fctKsp_div_eq {t w : ℂ} (ht : t ≠ 0) (hw1 : w + 1 ≠ 0) (htw : t - w ≠ 0) :
    fctKsp t w / (t - w) = ((t + 1) ^ 2 / t ^ 3) * (cauchyP w * cauchyQ t w) := by
  unfold fctKsp cauchyP cauchyQ
  field_simp
  ring

private lemma hasDerivAt_cauchyP {w : ℂ} (hw1 : w + 1 ≠ 0) :
    HasDerivAt cauchyP (cauchyP1 w) w := by
  unfold cauchyP cauchyP1
  have h0 : HasDerivAt (fun z : ℂ => z / (z + 1)) (1 / (w + 1) ^ 2) w := by
    refine ((hasDerivAt_id w).div ((hasDerivAt_id w).add_const 1) hw1).congr_deriv ?_
    simp only [id_eq]; ring
  refine (h0.pow 2).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp

private lemma hasDerivAt_cauchyP1 {w : ℂ} (hw1 : w + 1 ≠ 0) :
    HasDerivAt cauchyP1 (cauchyP2 w) w := by
  unfold cauchyP1 cauchyP2
  have h1 : HasDerivAt (fun z : ℂ => 2 * z) 2 w := by
    simpa using (hasDerivAt_id w).const_mul (2 : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => (z + 1) ^ 3) (3 * (w + 1) ^ 2) w := by
    convert ((hasDerivAt_id w).add_const (1 : ℂ)).pow 3 using 1
    simp
  refine (h1.div h2 (pow_ne_zero 3 hw1)).congr_deriv ?_
  field_simp
  ring

private lemma hasDerivAt_cauchyQ (t : ℂ) {w : ℂ} (htw : t - w ≠ 0) :
    HasDerivAt (cauchyQ t) (cauchyQ1 t w) w := by
  unfold cauchyQ cauchyQ1
  have hsub : HasDerivAt (fun z : ℂ => t - z) (-1) w := by
    have := (hasDerivAt_id w).const_sub t
    simpa using this
  have hdiv : HasDerivAt (fun z : ℂ => t / (t - z)) (t / (t - w) ^ 2) w := by
    refine ((hasDerivAt_const w t).div hsub htw).congr_deriv ?_
    ring
  refine ((hasDerivAt_const w (-1 : ℂ)).add hdiv).congr_deriv ?_
  simp

private lemma hasDerivAt_cauchyQ1 (t : ℂ) {w : ℂ} (htw : t - w ≠ 0) :
    HasDerivAt (cauchyQ1 t) (cauchyQ2 t w) w := by
  unfold cauchyQ1 cauchyQ2
  have hsub : HasDerivAt (fun z : ℂ => (t - z) ^ 2) (2 * (t - w) * (-1)) w := by
    convert ((hasDerivAt_id w).const_sub t).pow 2 using 1
    simp
  refine ((hasDerivAt_const w t).div hsub (pow_ne_zero 2 htw)).congr_deriv ?_
  field_simp
  ring

/-! ### Elementary geometric bounds on a shifted ball -/

private lemma am_gm_inv_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / (a * b) ≤ 1 / a ^ 2 + 1 / b ^ 2 := by
  rw [div_le_iff₀ (mul_pos ha hb)]
  have h0 : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  field_simp
  nlinarith

private lemma line_ball_bounds {σ σζ η : ℝ} (hσ : 3 / 8 ≤ σ) (_ : σ ≤ 7 / 16)
    (hσζ0 : -1 / 4 ≤ σζ) (hσζ2 : |σζ| ≤ 2) (hsep : 3 / 8 ≤ |σζ - σ|)
    {w : ℂ} (hw : w ∈ ball ((σζ : ℂ) + (η : ℂ) * Complex.I) (1 / 8)) (y : ℝ) :
    5 / 8 ≤ ‖w + 1‖ ∧
    (1 + |η|) / 4 ≤ ‖w + 1‖ ∧
    ‖w‖ ≤ 3 * (1 + |η|) ∧
    1 / 4 ≤ ‖((σ : ℂ) + (y : ℂ) * Complex.I) - w‖ ∧
    (1 + |y - η|) / 8 ≤ ‖((σ : ℂ) + (y : ℂ) * Complex.I) - w‖ ∧
    (3 / 16 : ℝ) * (1 + |y|) ≤ ‖(σ : ℂ) + (y : ℂ) * Complex.I‖ ∧
    ‖(σ : ℂ) + (y : ℂ) * Complex.I‖ ≤ 1 + |y| ∧
    ‖((σ : ℂ) + (y : ℂ) * Complex.I) + 1‖ ≤ 2 * (1 + |y|) := by
  set w0 : ℂ := (σζ : ℂ) + (η : ℂ) * Complex.I
  set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
  have hdist : ‖w - w0‖ < 1 / 8 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hre_diff : |w.re - σζ| < 1 / 8 := by
    have : |w.re - σζ| = |(w - w0).re| := by simp [w0]
    rw [this]; exact (Complex.abs_re_le_norm _).trans_lt hdist
  have him_diff : |w.im - η| < 1 / 8 := by
    have : |w.im - η| = |(w - w0).im| := by simp [w0]
    rw [this]; exact (Complex.abs_im_le_norm _).trans_lt hdist
  have hre_abs : |w.re - σζ| ≤ 1 / 8 := hre_diff.le
  have him_abs : |w.im - η| ≤ 1 / 8 := him_diff.le
  have hwre_lo : σζ - 1 / 8 ≤ w.re := by linarith [(abs_le.mp hre_abs).1]
  have hw1_58 : 5 / 8 ≤ ‖w + 1‖ := by
    have := Complex.re_le_norm (w + 1)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  have hw1_eta : (1 + |η|) / 4 ≤ ‖w + 1‖ := by
    rcases le_or_gt |η| 1 with hη | hη
    · linarith
    · have him : (7 / 8 : ℝ) * |η| ≤ |(w + 1).im| := by
        have h1 : |η| - |w.im| ≤ |η - w.im| := abs_sub_abs_le_abs_sub η w.im
        rw [abs_sub_comm] at h1
        have h2 : |(w + 1).im| = |w.im| := by simp
        rw [h2]; linarith
      exact (by linarith : (1 + |η|) / 4 ≤ (7 / 8 : ℝ) * |η|).trans
        (him.trans (Complex.abs_im_le_norm (w + 1)))
  have hw_ub : ‖w‖ ≤ 3 * (1 + |η|) := by
    have hre1 : |w.re| ≤ 2 + 1 / 8 := by
      calc |w.re| = |(w.re - σζ) + σζ| := by ring_nf
        _ ≤ |w.re - σζ| + |σζ| := abs_add_le _ _
        _ ≤ 1 / 8 + 2 := add_le_add hre_abs hσζ2
        _ = 2 + 1 / 8 := by ring
    have him1 : |w.im| ≤ |η| + 1 / 8 := by
      calc |w.im| = |(w.im - η) + η| := by ring_nf
        _ ≤ |w.im - η| + |η| := abs_add_le _ _
        _ ≤ 1 / 8 + |η| := add_le_add him_abs le_rfl
        _ = |η| + 1 / 8 := by ring
    have hnorm := Complex.norm_le_abs_re_add_abs_im w
    linarith [abs_nonneg η]
  have htw_re : 1 / 4 ≤ |t.re - w.re| := by
    have htre : t.re = σ := by simp [t]
    rw [htre]
    have h1 := abs_sub_abs_le_abs_sub (σζ - σ) (w.re - σ)
    have hsub : |(σζ - σ) - (w.re - σ)| = |w.re - σζ| := by rw [abs_sub_comm]; ring_nf
    rw [hsub, abs_sub_comm σ w.re] at h1
    linarith [hsep, hre_abs]
  have htw_14 : 1 / 4 ≤ ‖t - w‖ := htw_re.trans (by
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (t - w))
  have htw_diff : (1 + |y - η|) / 8 ≤ ‖t - w‖ := by
    rcases le_or_gt |y - η| 1 with hyη | hyη
    · linarith
    · have him : (7 / 8 : ℝ) * |y - η| ≤ |(t - w).im| := by
        have htim : (t - w).im = y - w.im := by simp [t]
        rw [htim]
        have h1 := abs_sub_abs_le_abs_sub (y - η) (y - w.im)
        have e : (y - η) - (y - w.im) = w.im - η := by ring
        rw [e] at h1
        linarith
      exact (by linarith : (1 + |y - η|) / 8 ≤ (7 / 8 : ℝ) * |y - η|).trans
        (him.trans (Complex.abs_im_le_norm (t - w)))
  have ht_lb : (3 / 16 : ℝ) * (1 + |y|) ≤ ‖t‖ := by
    rcases le_or_gt |y| 1 with hy1 | hy1
    · have htre : |t.re| = σ := by
        simpa [t] using abs_of_nonneg (show 0 ≤ σ by linarith)
      have := htre ▸ Complex.abs_re_le_norm t
      linarith
    · have htim : |t.im| = |y| := by simp [t]
      have := htim ▸ Complex.abs_im_le_norm t
      linarith
  have ht_ub : ‖t‖ ≤ 1 + |y| := by
    have htre : |t.re| = σ := by
      simpa [t] using abs_of_nonneg (show 0 ≤ σ by linarith)
    have htim : |t.im| = |y| := by simp [t]
    have := Complex.norm_le_abs_re_add_abs_im t
    rw [htre, htim] at this
    linarith
  have ht1_ub : ‖t + 1‖ ≤ 2 * (1 + |y|) := by
    have h := norm_add_le t (1 : ℂ)
    rw [norm_one] at h
    linarith [abs_nonneg y]
  exact ⟨hw1_58, hw1_eta, hw_ub, htw_14, htw_diff, ht_lb, ht_ub, ht1_ub⟩

private lemma integrable_inv_sq_shift (η : ℝ) :
    Integrable (fun y : ℝ => 1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) :=
  integrable_inv_one_add_abs_sq.add (integrable_inv_one_add_abs_sq.comp_sub_right η)

private lemma integral_inv_sq_shift (η : ℝ) :
    ∫ y : ℝ, (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) = 2 * ∫ y : ℝ, 1 / (1 + |y|) ^ 2 := by
  rw [integral_add integrable_inv_one_add_abs_sq (integrable_inv_one_add_abs_sq.comp_sub_right η),
    integral_sub_right_eq_self (fun y : ℝ => 1 / (1 + |y|) ^ 2) η]
  ring

/-! ### Uniform Cauchy integral trace bounds (`C⁰`, `C¹`, `C²`) -/

private noncomputable def cauchyK1 (t w : ℂ) : ℂ :=
  ((t + 1) ^ 2 / t ^ 3) * (cauchyP1 w * cauchyQ t w + cauchyP w * cauchyQ1 t w)

private noncomputable def cauchyK2 (t w : ℂ) : ℂ :=
  ((t + 1) ^ 2 / t ^ 3) *
    (cauchyP2 w * cauchyQ t w + 2 * (cauchyP1 w * cauchyQ1 t w) + cauchyP w * cauchyQ2 t w)

private lemma norm_cauchyK1_le {σ σζ η : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    (hσζ0 : -1 / 4 ≤ σζ) (hσζ2 : |σζ| ≤ 2) (hsep : 3 / 8 ≤ |σζ - σ|)
    {w : ℂ} (hw : w ∈ ball ((σζ : ℂ) + (η : ℂ) * Complex.I) (1 / 8)) (y : ℝ) :
    ‖cauchyK1 ((σ : ℂ) + (y : ℂ) * Complex.I) w‖ ≤
      (10 ^ 7 : ℝ) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
  obtain ⟨_, hw1_eta, hw_ub, _, htw_diff, ht_lb, ht_ub, ht1_ub⟩ :=
    line_ball_bounds hσ hσ' hσζ0 hσζ2 hsep hw y
  set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
  have hy0 : (0 : ℝ) < 1 + |y| := by positivity
  have hyη0 : (0 : ℝ) < 1 + |y - η| := by positivity
  have hη0 : (0 : ℝ) < 1 + |η| := by positivity
  have htw_pos : (0 : ℝ) < ‖t - w‖ := by
    have : 0 < (1 + |y - η|) / 8 := by positivity
    linarith
  have ht_pref : ‖(t + 1) ^ 2 / t ^ 3‖ ≤ 600 * (1 / (1 + |y|)) := by
    rw [norm_div, norm_pow, norm_pow]
    have hnum : ‖t + 1‖ ^ 2 ≤ (2 * (1 + |y|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht1_ub 2
    have hden : ((3 / 16 : ℝ) * (1 + |y|)) ^ 3 ≤ ‖t‖ ^ 3 := pow_le_pow_left₀ (by positivity) ht_lb 3
    calc ‖t + 1‖ ^ 2 / ‖t‖ ^ 3 ≤ (2 * (1 + |y|)) ^ 2 / ((3 / 16 : ℝ) * (1 + |y|)) ^ 3 :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = (2 ^ 2 / (3 / 16 : ℝ) ^ 3) * (1 / (1 + |y|)) := by field_simp
      _ ≤ 600 * (1 / (1 + |y|)) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hP : ‖cauchyP w‖ ≤ 144 := by
    unfold cauchyP
    rw [norm_pow, norm_div]
    have h1 : ‖w‖ / ‖w + 1‖ ≤ (3 * (1 + |η|)) / ((1 + |η|) / 4) :=
      div_le_div₀ (by positivity) hw_ub (by positivity) hw1_eta
    have h2 : (3 * (1 + |η|)) / ((1 + |η|) / 4) = 12 := by field_simp; ring
    exact (pow_le_pow_left₀ (by positivity) (h1.trans h2.le) 2).trans (by norm_num)
  have hP1 : ‖cauchyP1 w‖ ≤ 384 * (1 / (1 + |η|) ^ 2) := by
    unfold cauchyP1
    rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow]
    have h1 : 2 * ‖w‖ ≤ 2 * (3 * (1 + |η|)) := by linarith
    have h2 : ((1 + |η|) / 4) ^ 3 ≤ ‖w + 1‖ ^ 3 := pow_le_pow_left₀ (by positivity) hw1_eta 3
    calc 2 * ‖w‖ / ‖w + 1‖ ^ 3 ≤ (2 * (3 * (1 + |η|))) / ((1 + |η|) / 4) ^ 3 :=
          div_le_div₀ (by positivity) h1 (by positivity) h2
      _ = 384 * (1 / (1 + |η|) ^ 2) := by field_simp; ring
  have hQ : ‖cauchyQ t w‖ ≤ 24 * ((1 + |η|) / (1 + |y - η|)) := by
    have heq : cauchyQ t w = w / (t - w) := by
      unfold cauchyQ
      have htw' : t - w ≠ 0 := norm_pos_iff.mp htw_pos
      field_simp; ring
    rw [heq, norm_div]
    calc ‖w‖ / ‖t - w‖ ≤ (3 * (1 + |η|)) / ((1 + |y - η|) / 8) :=
          div_le_div₀ (by positivity) hw_ub (by positivity) htw_diff
      _ = 24 * ((1 + |η|) / (1 + |y - η|)) := by field_simp; ring
  have hQ1 : ‖cauchyQ1 t w‖ ≤ 64 * ((1 + |y|) / (1 + |y - η|) ^ 2) := by
    unfold cauchyQ1
    rw [norm_div, norm_pow]
    have hden : ((1 + |y - η|) / 8) ^ 2 ≤ ‖t - w‖ ^ 2 := pow_le_pow_left₀ (by positivity) htw_diff 2
    calc ‖t‖ / ‖t - w‖ ^ 2 ≤ (1 + |y|) / ((1 + |y - η|) / 8) ^ 2 :=
          div_le_div₀ (by positivity) ht_ub (by positivity) hden
      _ = 64 * ((1 + |y|) / (1 + |y - η|) ^ 2) := by field_simp; ring
  have hP1Q : ‖cauchyP1 w * cauchyQ t w‖ ≤ (384 * 24) * (1 / (1 + |y - η|)) := by
    rw [norm_mul]
    calc ‖cauchyP1 w‖ * ‖cauchyQ t w‖
        ≤ (384 * (1 / (1 + |η|) ^ 2)) * (24 * ((1 + |η|) / (1 + |y - η|))) :=
          mul_le_mul hP1 hQ (norm_nonneg _) (by positivity)
      _ = (384 * 24) * (1 / ((1 + |η|) * (1 + |y - η|))) := by field_simp
      _ ≤ (384 * 24) * (1 / (1 + |y - η|)) := by
          gcongr
          calc 1 * (1 + |y - η|) ≤ (1 + |η|) * (1 + |y - η|) :=
                mul_le_mul_of_nonneg_right (by linarith [abs_nonneg η]) hyη0.le
  have ham : 1 / ((1 + |y|) * (1 + |y - η|)) ≤ 1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2 :=
    am_gm_inv_mul hy0 hyη0
  have h1y2 : 1 / (1 + |y - η|) ^ 2 ≤ 1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2 :=
    le_add_of_nonneg_left (by positivity)
  have ht1 : ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP1 w * cauchyQ t w‖ ≤
      (600 * (384 * 24)) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
    calc ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP1 w * cauchyQ t w‖
        ≤ (600 * (1 / (1 + |y|))) * ((384 * 24) * (1 / (1 + |y - η|))) :=
          mul_le_mul ht_pref hP1Q (norm_nonneg _) (by positivity)
      _ = (600 * (384 * 24)) * (1 / ((1 + |y|) * (1 + |y - η|))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ham (by positivity)
  have ht2 : ‖(t + 1) ^ 2 / t ^ 3‖ * (‖cauchyP w‖ * ‖cauchyQ1 t w‖) ≤
      (600 * (144 * 64)) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
    calc ‖(t + 1) ^ 2 / t ^ 3‖ * (‖cauchyP w‖ * ‖cauchyQ1 t w‖)
        ≤ (600 * (1 / (1 + |y|))) * (144 * (64 * ((1 + |y|) / (1 + |y - η|) ^ 2))) :=
          mul_le_mul ht_pref (mul_le_mul hP hQ1 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
      _ = (600 * (144 * 64)) * (1 / (1 + |y - η|) ^ 2) := by field_simp
      _ ≤ _ := by exact mul_le_mul_of_nonneg_left h1y2 (by positivity)
  rw [cauchyK1, norm_mul]
  have htri := mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by rw [norm_mul, norm_mul])) (norm_nonneg ((t + 1) ^ 2 / t ^ 3))
  calc ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP1 w * cauchyQ t w + cauchyP w * cauchyQ1 t w‖
      ≤ ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP1 w * cauchyQ t w‖ +
        ‖(t + 1) ^ 2 / t ^ 3‖ * (‖cauchyP w‖ * ‖cauchyQ1 t w‖) := by linarith
    _ ≤ (600 * (384 * 24) + 600 * (144 * 64)) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by linarith
    _ ≤ (10 ^ 7 : ℝ) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

private lemma norm_cauchyK2_le {σ σζ η : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    (hσζ0 : -1 / 4 ≤ σζ) (hσζ2 : |σζ| ≤ 2) (hsep : 3 / 8 ≤ |σζ - σ|)
    {w : ℂ} (hw : w ∈ ball ((σζ : ℂ) + (η : ℂ) * Complex.I) (1 / 8)) (y : ℝ) :
    ‖cauchyK2 ((σ : ℂ) + (y : ℂ) * Complex.I) w‖ ≤
      (10 ^ 9 : ℝ) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
  obtain ⟨_, hw1_eta, hw_ub, _, htw_diff, ht_lb, ht_ub, ht1_ub⟩ :=
    line_ball_bounds hσ hσ' hσζ0 hσζ2 hsep hw y
  set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
  have hy0 : (0 : ℝ) < 1 + |y| := by positivity
  have hyη0 : (0 : ℝ) < 1 + |y - η| := by positivity
  have hη0 : (0 : ℝ) < 1 + |η| := by positivity
  have htw_pos : (0 : ℝ) < ‖t - w‖ := by
    have : 0 < (1 + |y - η|) / 8 := by positivity
    linarith
  have ht_pref : ‖(t + 1) ^ 2 / t ^ 3‖ ≤ 600 * (1 / (1 + |y|)) := by
    rw [norm_div, norm_pow, norm_pow]
    have hnum : ‖t + 1‖ ^ 2 ≤ (2 * (1 + |y|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht1_ub 2
    have hden : ((3 / 16 : ℝ) * (1 + |y|)) ^ 3 ≤ ‖t‖ ^ 3 := pow_le_pow_left₀ (by positivity) ht_lb 3
    calc ‖t + 1‖ ^ 2 / ‖t‖ ^ 3 ≤ (2 * (1 + |y|)) ^ 2 / ((3 / 16 : ℝ) * (1 + |y|)) ^ 3 :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = (2 ^ 2 / (3 / 16 : ℝ) ^ 3) * (1 / (1 + |y|)) := by field_simp
      _ ≤ 600 * (1 / (1 + |y|)) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hP : ‖cauchyP w‖ ≤ 144 := by
    unfold cauchyP
    rw [norm_pow, norm_div]
    have h1 : ‖w‖ / ‖w + 1‖ ≤ (3 * (1 + |η|)) / ((1 + |η|) / 4) :=
      div_le_div₀ (by positivity) hw_ub (by positivity) hw1_eta
    have h2 : (3 * (1 + |η|)) / ((1 + |η|) / 4) = 12 := by field_simp; ring
    exact (pow_le_pow_left₀ (by positivity) (h1.trans h2.le) 2).trans (by norm_num)
  have hP1 : ‖cauchyP1 w‖ ≤ 384 * (1 / (1 + |η|) ^ 2) := by
    unfold cauchyP1
    rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow]
    have h1 : 2 * ‖w‖ ≤ 2 * (3 * (1 + |η|)) := by linarith
    have h2 : ((1 + |η|) / 4) ^ 3 ≤ ‖w + 1‖ ^ 3 := pow_le_pow_left₀ (by positivity) hw1_eta 3
    calc 2 * ‖w‖ / ‖w + 1‖ ^ 3 ≤ (2 * (3 * (1 + |η|))) / ((1 + |η|) / 4) ^ 3 :=
          div_le_div₀ (by positivity) h1 (by positivity) h2
      _ = 384 * (1 / (1 + |η|) ^ 2) := by field_simp; ring
  have hP2 : ‖cauchyP2 w‖ ≤ 3584 * (1 / (1 + |η|) ^ 3) := by
    unfold cauchyP2
    rw [norm_div, norm_pow]
    have hnum : ‖(2 : ℂ) - 4 * w‖ ≤ 14 * (1 + |η|) := by
      calc ‖(2 : ℂ) - 4 * w‖ ≤ ‖(2 : ℂ)‖ + ‖4 * w‖ := norm_sub_le _ _
        _ = 2 + 4 * ‖w‖ := by simp [Complex.norm_ofNat]
        _ ≤ 2 + 4 * (3 * (1 + |η|)) := by linarith
        _ ≤ 14 * (1 + |η|) := by linarith [abs_nonneg η]
    have hden : ((1 + |η|) / 4) ^ 4 ≤ ‖w + 1‖ ^ 4 := pow_le_pow_left₀ (by positivity) hw1_eta 4
    calc ‖(2 : ℂ) - 4 * w‖ / ‖w + 1‖ ^ 4 ≤ (14 * (1 + |η|)) / ((1 + |η|) / 4) ^ 4 :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 3584 * (1 / (1 + |η|) ^ 3) := by field_simp; ring
  have hQ : ‖cauchyQ t w‖ ≤ 24 * ((1 + |η|) / (1 + |y - η|)) := by
    have heq : cauchyQ t w = w / (t - w) := by
      unfold cauchyQ; have htw' : t - w ≠ 0 := norm_pos_iff.mp htw_pos; field_simp; ring
    rw [heq, norm_div]
    calc ‖w‖ / ‖t - w‖ ≤ (3 * (1 + |η|)) / ((1 + |y - η|) / 8) :=
          div_le_div₀ (by positivity) hw_ub (by positivity) htw_diff
      _ = 24 * ((1 + |η|) / (1 + |y - η|)) := by field_simp; ring
  have hQ1 : ‖cauchyQ1 t w‖ ≤ 64 * ((1 + |y|) / (1 + |y - η|) ^ 2) := by
    unfold cauchyQ1; rw [norm_div, norm_pow]
    have hden : ((1 + |y - η|) / 8) ^ 2 ≤ ‖t - w‖ ^ 2 := pow_le_pow_left₀ (by positivity) htw_diff 2
    calc ‖t‖ / ‖t - w‖ ^ 2 ≤ (1 + |y|) / ((1 + |y - η|) / 8) ^ 2 :=
          div_le_div₀ (by positivity) ht_ub (by positivity) hden
      _ = 64 * ((1 + |y|) / (1 + |y - η|) ^ 2) := by field_simp; ring
  have hQ2 : ‖cauchyQ2 t w‖ ≤ 1024 * ((1 + |y|) / (1 + |y - η|) ^ 2) := by
    unfold cauchyQ2; rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow]
    have h1 : 1 ≤ 1 + |y - η| := by linarith [abs_nonneg (y - η)]
    have hden1 : ((1 + |y - η|) / 8) ^ 3 ≤ ‖t - w‖ ^ 3 := pow_le_pow_left₀ (by positivity) htw_diff 3
    have hden2 : (1 + |y - η|) ^ 2 ≤ (1 + |y - η|) ^ 3 := by
      calc (1 + |y - η|) ^ 2 = (1 + |y - η|) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (1 + |y - η|) ^ 2 * (1 + |y - η|) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (1 + |y - η|) ^ 3 := by ring
    calc 2 * ‖t‖ / ‖t - w‖ ^ 3 ≤ 2 * (1 + |y|) / ((1 + |y - η|) / 8) ^ 3 :=
          div_le_div₀ (by positivity) (by linarith) (by positivity) hden1
      _ = 1024 * ((1 + |y|) / (1 + |y - η|) ^ 3) := by field_simp; ring
      _ ≤ 1024 * ((1 + |y|) / (1 + |y - η|) ^ 2) := by gcongr
  have ham : 1 / ((1 + |y|) * (1 + |y - η|)) ≤ 1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2 :=
    am_gm_inv_mul hy0 hyη0
  have h1y2 : 1 / (1 + |y - η|) ^ 2 ≤ 1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2 :=
    le_add_of_nonneg_left (by positivity)
  have hp2q : ‖cauchyP2 w * cauchyQ t w‖ ≤ (3584 * 24) * (1 / (1 + |y - η|)) := by
    rw [norm_mul]
    calc ‖cauchyP2 w‖ * ‖cauchyQ t w‖
        ≤ (3584 * (1 / (1 + |η|) ^ 3)) * (24 * ((1 + |η|) / (1 + |y - η|))) :=
          mul_le_mul hP2 hQ (norm_nonneg _) (by positivity)
      _ = (3584 * 24) * (1 / ((1 + |η|) ^ 2 * (1 + |y - η|))) := by field_simp
      _ ≤ (3584 * 24) * (1 / (1 + |y - η|)) := by
          gcongr
          have : (1 : ℝ) ≤ (1 + |η|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg η])
          calc 1 * (1 + |y - η|) ≤ (1 + |η|) ^ 2 * (1 + |y - η|) :=
                mul_le_mul_of_nonneg_right this hyη0.le
  have hp1q1 : ‖2 * (cauchyP1 w * cauchyQ1 t w)‖ ≤ (2 * 384 * 64) * ((1 + |y|) / (1 + |y - η|) ^ 2) := by
    rw [norm_mul, Complex.norm_ofNat, norm_mul]
    have hη1 : 1 / (1 + |η|) ^ 2 ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by linarith [abs_nonneg η])) (by positivity)
    calc 2 * (‖cauchyP1 w‖ * ‖cauchyQ1 t w‖)
        ≤ 2 * ((384 * 1) * (64 * ((1 + |y|) / (1 + |y - η|) ^ 2))) := by
          gcongr; linarith
      _ = (2 * 384 * 64) * ((1 + |y|) / (1 + |y - η|) ^ 2) := by ring
  have hpq2 : ‖cauchyP w * cauchyQ2 t w‖ ≤ (144 * 1024) * ((1 + |y|) / (1 + |y - η|) ^ 2) := by
    rw [norm_mul]
    exact (mul_le_mul hP hQ2 (norm_nonneg _) (by positivity)).trans (le_of_eq (by ring))
  have ht1 : ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP2 w * cauchyQ t w‖ ≤
      (600 * (3584 * 24)) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
    calc ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP2 w * cauchyQ t w‖
        ≤ (600 * (1 / (1 + |y|))) * ((3584 * 24) * (1 / (1 + |y - η|))) :=
          mul_le_mul ht_pref hp2q (norm_nonneg _) (by positivity)
      _ = (600 * (3584 * 24)) * (1 / ((1 + |y|) * (1 + |y - η|))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ham (by positivity)
  have ht2 : ‖(t + 1) ^ 2 / t ^ 3‖ * ‖2 * (cauchyP1 w * cauchyQ1 t w)‖ ≤
      (600 * (2 * 384 * 64)) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
    calc ‖(t + 1) ^ 2 / t ^ 3‖ * ‖2 * (cauchyP1 w * cauchyQ1 t w)‖
        ≤ (600 * (1 / (1 + |y|))) * ((2 * 384 * 64) * ((1 + |y|) / (1 + |y - η|) ^ 2)) :=
          mul_le_mul ht_pref hp1q1 (norm_nonneg _) (by positivity)
      _ = (600 * (2 * 384 * 64)) * (1 / (1 + |y - η|) ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1y2 (by positivity)
  have ht3 : ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP w * cauchyQ2 t w‖ ≤
      (600 * (144 * 1024)) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
    calc ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP w * cauchyQ2 t w‖
        ≤ (600 * (1 / (1 + |y|))) * ((144 * 1024) * ((1 + |y|) / (1 + |y - η|) ^ 2)) :=
          mul_le_mul ht_pref hpq2 (norm_nonneg _) (by positivity)
      _ = (600 * (144 * 1024)) * (1 / (1 + |y - η|) ^ 2) := by field_simp
      _ ≤ _ := by exact mul_le_mul_of_nonneg_left h1y2 (by positivity)
  rw [cauchyK2, norm_mul]
  have htri : ‖cauchyP2 w * cauchyQ t w + 2 * (cauchyP1 w * cauchyQ1 t w) + cauchyP w * cauchyQ2 t w‖ ≤
      ‖cauchyP2 w * cauchyQ t w‖ + ‖2 * (cauchyP1 w * cauchyQ1 t w)‖ + ‖cauchyP w * cauchyQ2 t w‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  calc ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP2 w * cauchyQ t w + 2 * (cauchyP1 w * cauchyQ1 t w) + cauchyP w * cauchyQ2 t w‖
      ≤ ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP2 w * cauchyQ t w‖ +
        ‖(t + 1) ^ 2 / t ^ 3‖ * ‖2 * (cauchyP1 w * cauchyQ1 t w)‖ +
        ‖(t + 1) ^ 2 / t ^ 3‖ * ‖cauchyP w * cauchyQ2 t w‖ := by
          have := mul_le_mul_of_nonneg_left htri (norm_nonneg _)
          linarith
    _ ≤ (600 * (3584 * 24) + 600 * (2 * 384 * 64) + 600 * (144 * 1024)) *
          (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by linarith
    _ ≤ (10 ^ 9 : ℝ) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

private lemma norm_cauchyK0_le {σ σζ η : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    (hσζ0 : -1 / 4 ≤ σζ) (hσζ2 : |σζ| ≤ 2) (hsep : 3 / 8 ≤ |σζ - σ|)
    (y : ℝ) :
    ‖fctKsp ((σ : ℂ) + (y : ℂ) * Complex.I) ((σζ : ℂ) + (η : ℂ) * Complex.I) /
        (((σ : ℂ) + (y : ℂ) * Complex.I) - ((σζ : ℂ) + (η : ℂ) * Complex.I))‖ ≤
      (10 ^ 7 : ℝ) * (1 + |η|) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
  set w : ℂ := (σζ : ℂ) + (η : ℂ) * Complex.I
  set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
  have hw : w ∈ ball w (1 / 8) := mem_ball_self (by norm_num)
  obtain ⟨_, hw1_eta, hw_ub, htw_14, htw_diff, ht_lb, _, ht1_ub⟩ :=
    line_ball_bounds hσ hσ' hσζ0 hσζ2 hsep hw y
  have hy0 : (0 : ℝ) < 1 + |y| := by positivity
  have hyη0 : (0 : ℝ) < 1 + |y - η| := by positivity
  have htw_pos : (0 : ℝ) < ‖t - w‖ := by linarith
  have ht0 : t ≠ 0 := by intro h; have := congrArg Complex.re h; simp [t] at this; linarith
  have hw1 : w + 1 ≠ 0 := by
    have : 0 < (1 + |η|) / 4 := by positivity
    exact norm_pos_iff.mp (by linarith)
  have htw : t - w ≠ 0 := norm_pos_iff.mp htw_pos
  rw [fctKsp_div_eq ht0 hw1 htw, norm_mul, norm_mul]
  have ht_pref : ‖(t + 1) ^ 2 / t ^ 3‖ ≤ 600 * (1 / (1 + |y|)) := by
    rw [norm_div, norm_pow, norm_pow]
    calc ‖t + 1‖ ^ 2 / ‖t‖ ^ 3 ≤ (2 * (1 + |y|)) ^ 2 / ((3 / 16 : ℝ) * (1 + |y|)) ^ 3 :=
          div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) ht1_ub 2) (by positivity)
            (pow_le_pow_left₀ (by positivity) ht_lb 3)
      _ = (2 ^ 2 / (3 / 16 : ℝ) ^ 3) * (1 / (1 + |y|)) := by field_simp
      _ ≤ 600 * (1 / (1 + |y|)) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hP : ‖cauchyP w‖ ≤ 144 := by
    unfold cauchyP; rw [norm_pow, norm_div]
    have h1 : ‖w‖ / ‖w + 1‖ ≤ (3 * (1 + |η|)) / ((1 + |η|) / 4) :=
      div_le_div₀ (by positivity) hw_ub (by positivity) hw1_eta
    have h2 : (3 * (1 + |η|)) / ((1 + |η|) / 4) = 12 := by field_simp; ring
    exact (pow_le_pow_left₀ (by positivity) (h1.trans h2.le) 2).trans (by norm_num)
  have hQ : ‖cauchyQ t w‖ ≤ 24 * ((1 + |η|) / (1 + |y - η|)) := by
    have heq : cauchyQ t w = w / (t - w) := by unfold cauchyQ; field_simp; ring
    rw [heq, norm_div]
    calc ‖w‖ / ‖t - w‖ ≤ (3 * (1 + |η|)) / ((1 + |y - η|) / 8) :=
          div_le_div₀ (by positivity) hw_ub (by positivity) htw_diff
      _ = 24 * ((1 + |η|) / (1 + |y - η|)) := by field_simp; ring
  have ham := am_gm_inv_mul hy0 hyη0
  have hcst : (600 * (144 * 24) : ℝ) ≤ 10 ^ 7 := by norm_num
  calc ‖(t + 1) ^ 2 / t ^ 3‖ * (‖cauchyP w‖ * ‖cauchyQ t w‖)
      ≤ (600 * (1 / (1 + |y|))) * (144 * (24 * ((1 + |η|) / (1 + |y - η|)))) :=
        mul_le_mul ht_pref (mul_le_mul hP hQ (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = (600 * (144 * 24)) * (1 + |η|) * (1 / ((1 + |y|) * (1 + |y - η|))) := by field_simp; ring
    _ ≤ (10 ^ 7 : ℝ) * (1 + |η|) * (1 / ((1 + |y|) * (1 + |y - η|))) := by gcongr
    _ ≤ (10 ^ 7 : ℝ) * (1 + |η|) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) :=
        mul_le_mul_of_nonneg_left ham (by positivity)

/-- **Uniform `C⁰`, `C¹`, `C²` Cauchy-integral bounds along `Re ζ = σ_ζ`** (`3/8 ≤ σ ≤ 7/16`, `|σ_ζ - σ| ≥ 3/8`, `-1/4 ≤ σ_ζ ≤ 2`).
Proves `|C_σ(σ_ζ + iη)| ≤ K₀ B (1 + |η|)`, `|C_σ'(σ_ζ + iη)| ≤ K₁ B`, `|C_σ''(σ_ζ + iη)| ≤ K₂ B`
with absolute constants independent of `c, η, B`. -/
theorem fctCauchy_line_deriv_bounds {σ σζ : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    (hσζ0 : -1 / 4 ≤ σζ) (hσζ2 : |σζ| ≤ 2) (hsep : 3 / 8 ≤ |σζ - σ|) :
    ∃ K0 K1 K2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧
      ∀ K4 ε c L1 α B : ℝ, 0 < c → ContinuousOn (fctDcompAt K4 c α) closedStrip → 0 ≤ B →
        (∀ y : ℝ, ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) →
        ∀ η : ℝ,
          let w0 : ℂ := (σζ : ℂ) + (η : ℂ) * Complex.I
          ‖fctCauchy K4 ε c L1 α σ w0‖ ≤ K0 * B * (1 + |η|) ∧
          ‖deriv (fctCauchy K4 ε c L1 α σ) w0‖ ≤ K1 * B ∧
          ‖deriv (deriv (fctCauchy K4 ε c L1 α σ)) w0‖ ≤ K2 * B := by
  set I2 : ℝ := ∫ y : ℝ, 1 / (1 + |y|) ^ 2
  have hI2 : 0 ≤ I2 := integral_nonneg fun _ => by positivity
  set C0 : ℝ := (10 ^ 7 : ℝ)
  set C1 : ℝ := (10 ^ 7 : ℝ)
  set C2 : ℝ := (10 ^ 9 : ℝ)
  refine ⟨1 / (2 * π) * C0 * (2 * I2), 1 / (2 * π) * C1 * (2 * I2), 1 / (2 * π) * C2 * (2 * I2),
    by positivity, by positivity, by positivity, ?_⟩
  intro K4 ε c L1 α B hc hDc hB hF η w0
  have hmF : Measurable (fun y : ℝ => fctFint K4 ε c L1 α ((σ : ℂ) + (y : ℂ) * Complex.I)) :=
    fctFint_line_measurable hc hDc (by linarith) (by linarith)
  set Φ0 : ℂ → ℝ → ℂ := fun w y => fctCauchyIntegrand K4 ε c L1 α σ w y
  set Φ1 : ℂ → ℝ → ℂ := fun w y =>
    cauchyK1 ((σ : ℂ) + (y : ℂ) * Complex.I) w * fctFint K4 ε c L1 α ((σ : ℂ) + (y : ℂ) * Complex.I)
  set Φ2 : ℂ → ℝ → ℂ := fun w y =>
    cauchyK2 ((σ : ℂ) + (y : ℂ) * Complex.I) w * fctFint K4 ε c L1 α ((σ : ℂ) + (y : ℂ) * Complex.I)
  have hm0 : ∀ w : ℂ, AEStronglyMeasurable (Φ0 w) volume := fun w =>
    (fctCauchyIntegrand_measurable hc hDc (by linarith) (by linarith) w).aestronglyMeasurable
  have hm1 : ∀ w : ℂ, AEStronglyMeasurable (Φ1 w) volume := fun w => by
    have hK1 : Measurable (fun y : ℝ => cauchyK1 ((σ : ℂ) + (y : ℂ) * Complex.I) w) := by
      unfold cauchyK1 cauchyP cauchyP1 cauchyQ cauchyQ1
      fun_prop
    exact (hK1.mul hmF).aestronglyMeasurable
  have hm2 : ∀ w : ℂ, AEStronglyMeasurable (Φ2 w) volume := fun w => by
    have hK2 : Measurable (fun y : ℝ => cauchyK2 ((σ : ℂ) + (y : ℂ) * Complex.I) w) := by
      unfold cauchyK2 cauchyP cauchyP1 cauchyP2 cauchyQ cauchyQ1 cauchyQ2
      fun_prop
    exact (hK2.mul hmF).aestronglyMeasurable
  have hball_ne : ∀ z ∈ ball w0 (1 / 8), z.re ≠ σ := by
    intro z hz heq
    have hdist : ‖z - w0‖ < 1 / 8 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hre_diff : |z.re - σζ| < 1 / 8 := by
      have : |z.re - σζ| = |(z - w0).re| := by simp [w0]
      rw [this]; exact (Complex.abs_re_le_norm _).trans_lt hdist
    have h1 := abs_sub_abs_le_abs_sub (σζ - σ) (z.re - σ)
    have hsub : |(σζ - σ) - (z.re - σ)| = |z.re - σζ| := by rw [abs_sub_comm]; ring_nf
    rw [hsub, heq, sub_self, abs_zero] at h1
    linarith [hsep, hre_diff]
  have hloc1 : ∀ w ∈ ball w0 (1 / 8), ∀ y : ℝ,
      ‖Φ1 w y‖ ≤ (C1 * B) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
    intro w hw y
    dsimp only [Φ1]
    rw [norm_mul]
    calc ‖cauchyK1 _ w‖ * ‖fctFint K4 ε c L1 α _‖
        ≤ (C1 * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2)) * B :=
          mul_le_mul (norm_cauchyK1_le hσ hσ' hσζ0 hσζ2 hsep hw y) (hF y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hloc2 : ∀ w ∈ ball w0 (1 / 8), ∀ y : ℝ,
      ‖Φ2 w y‖ ≤ (C2 * B) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
    intro w hw y
    dsimp only [Φ2]
    rw [norm_mul]
    calc ‖cauchyK2 _ w‖ * ‖fctFint K4 ε c L1 α _‖
        ≤ (C2 * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2)) * B :=
          mul_le_mul (norm_cauchyK2_le hσ hσ' hσζ0 hσζ2 hsep hw y) (hF y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h0int : ∀ w ∈ ball w0 (1 / 8), Integrable (Φ0 w) volume := fun w hw =>
    fctCauchyIntegrand_integrable hc hDc hσ hσ' (hball_ne w hw) hF
  have h1int : ∀ w ∈ ball w0 (1 / 8), Integrable (Φ1 w) volume := fun w hw =>
    ((integrable_inv_sq_shift η).const_mul (C1 * B)).mono' (hm1 w) (ae_of_all _ (hloc1 w hw))
  have hd01 : ∀ w ∈ ball w0 (1 / 8), HasDerivAt (fun z => ∫ y : ℝ, Φ0 z y) (∫ y : ℝ, Φ1 w y) w := by
    intro w hw
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume)
      (F := Φ0) (F' := Φ1) (x₀ := w) (s := ball w0 (1 / 8)) (Metric.isOpen_ball.mem_nhds hw)
      (Eventually.of_forall fun z => hm0 z)
      (h0int w hw)
      (hm1 w)
      (ae_of_all _ fun y z hz => hloc1 z hz y)
      ((integrable_inv_sq_shift η).const_mul (C1 * B))
      (ae_of_all _ fun y z hz => by
        obtain ⟨hw1_58, _, _, htw_14, _, _, _, _⟩ := line_ball_bounds hσ hσ' hσζ0 hσζ2 hsep hz y
        set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
        have ht0 : t ≠ 0 := by intro h; have := congrArg Complex.re h; simp [t] at this; linarith
        have hw1 : z + 1 ≠ 0 := norm_pos_iff.mp (by linarith)
        have htw : t - z ≠ 0 := norm_pos_iff.mp (by linarith)
        have hder : HasDerivAt (fun u => ((t + 1) ^ 2 / t ^ 3) * (cauchyP u * cauchyQ t u) *
            fctFint K4 ε c L1 α t) (Φ1 z y) z := by
          have hpq := (hasDerivAt_cauchyP hw1).mul (hasDerivAt_cauchyQ t htw)
          exact ((hpq.const_mul _).mul_const _).congr_deriv (by
            dsimp only [Φ1, cauchyK1]; rfl)
        have hevf : (fun u : ℂ => Φ0 u y) =ᶠ[𝓝 z] fun u => ((t + 1) ^ 2 / t ^ 3) * (cauchyP u * cauchyQ t u) *
            fctFint K4 ε c L1 α t := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hz] with u hu
          obtain ⟨hu1_58, _, _, htu_14, _, _, _, _⟩ := line_ball_bounds hσ hσ' hσζ0 hσζ2 hsep hu y
          have hu1 : u + 1 ≠ 0 := norm_pos_iff.mp (by linarith)
          have htu : t - u ≠ 0 := norm_pos_iff.mp (by linarith)
          dsimp only [Φ0, fctCauchyIntegrand]
          rw [mul_div_right_comm, fctKsp_div_eq ht0 hu1 htu]
        exact hder.congr_of_eventuallyEq hevf)
    exact h.2
  have hd12 : HasDerivAt (fun z => ∫ y : ℝ, Φ1 z y) (∫ y : ℝ, Φ2 w0 y) w0 := by
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume)
      (F := Φ1) (F' := Φ2) (x₀ := w0) (s := ball w0 (1 / 8))
      (Metric.isOpen_ball.mem_nhds (mem_ball_self (x := w0) (by norm_num)))
      (Eventually.of_forall fun z => hm1 z)
      (h1int w0 (mem_ball_self (x := w0) (by norm_num)))
      (hm2 w0)
      (ae_of_all _ fun y z hz => hloc2 z hz y)
      ((integrable_inv_sq_shift η).const_mul (C2 * B))
      (ae_of_all _ fun y z hz => by
        obtain ⟨hw1_58, _, _, htw_14, _, _, _, _⟩ := line_ball_bounds hσ hσ' hσζ0 hσζ2 hsep hz y
        set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
        have hw1 : z + 1 ≠ 0 := norm_pos_iff.mp (by linarith)
        have htw : t - z ≠ 0 := norm_pos_iff.mp (by linarith)
        have hpq1 : HasDerivAt (fun u => cauchyP1 u * cauchyQ t u + cauchyP u * cauchyQ1 t u)
            (cauchyP2 z * cauchyQ t z + 2 * (cauchyP1 z * cauchyQ1 t z) + cauchyP z * cauchyQ2 t z) z := by
          have ha := (hasDerivAt_cauchyP1 hw1).mul (hasDerivAt_cauchyQ t htw)
          have hb := (hasDerivAt_cauchyP hw1).mul (hasDerivAt_cauchyQ1 t htw)
          refine (ha.add hb).congr_deriv ?_
          ring
        exact ((hpq1.const_mul _).mul_const _).congr_deriv (by
          dsimp only [Φ1, Φ2, cauchyK1, cauchyK2]; rfl))
    exact h.2
  have hpref_pos : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
  have hC0_norm : ‖fctCauchy K4 ε c L1 α σ w0‖ ≤ 1 / (2 * π) * C0 * (2 * I2) * B * (1 + |η|) := by
    unfold fctCauchy
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpref_pos]
    have hint : ‖∫ y : ℝ, Φ0 w0 y‖ ≤ ∫ y : ℝ, C0 * B * (1 + |η|) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) := by
      refine norm_integral_le_of_norm_le ((integrable_inv_sq_shift η).const_mul (C0 * B * (1 + |η|)))
        (ae_of_all _ fun y => ?_)
      dsimp only [Φ0, fctCauchyIntegrand]
      rw [mul_div_right_comm, norm_mul]
      calc ‖fctKsp ((σ : ℂ) + (y : ℂ) * Complex.I) w0 / (((σ : ℂ) + (y : ℂ) * Complex.I) - w0)‖ *
            ‖fctFint K4 ε c L1 α _‖
          ≤ (C0 * (1 + |η|) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2)) * B :=
            mul_le_mul (norm_cauchyK0_le hσ hσ' hσζ0 hσζ2 hsep y) (hF y) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    rw [integral_const_mul, integral_inv_sq_shift] at hint
    calc 1 / (2 * π) * ‖∫ y : ℝ, Φ0 w0 y‖
        ≤ 1 / (2 * π) * (C0 * B * (1 + |η|) * (2 * I2)) := mul_le_mul_of_nonneg_left hint hpref_pos
      _ = _ := by ring
  have hd_eq : ∀ w ∈ ball w0 (1 / 8),
      deriv (fctCauchy K4 ε c L1 α σ) w = ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, Φ1 w y := by
    intro w hw
    have hc_eq : fctCauchy K4 ε c L1 α σ = fun z => ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, Φ0 z y := rfl
    rw [hc_eq]
    exact ((hd01 w hw).const_mul _).deriv
  have hC1_norm : ‖deriv (fctCauchy K4 ε c L1 α σ) w0‖ ≤ 1 / (2 * π) * C1 * (2 * I2) * B := by
    rw [hd_eq w0 (mem_ball_self (x := w0) (by norm_num)), norm_mul, Complex.norm_real, Real.norm_of_nonneg hpref_pos]
    have hint : ‖∫ y : ℝ, Φ1 w0 y‖ ≤ ∫ y : ℝ, (C1 * B) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) :=
      norm_integral_le_of_norm_le ((integrable_inv_sq_shift η).const_mul (C1 * B))
        (ae_of_all _ (hloc1 w0 (mem_ball_self (x := w0) (by norm_num))))
    rw [integral_const_mul, integral_inv_sq_shift] at hint
    calc 1 / (2 * π) * ‖∫ y : ℝ, Φ1 w0 y‖
        ≤ 1 / (2 * π) * (C1 * B * (2 * I2)) := mul_le_mul_of_nonneg_left hint hpref_pos
      _ = _ := by ring
  have hC2_norm : ‖deriv (deriv (fctCauchy K4 ε c L1 α σ)) w0‖ ≤ 1 / (2 * π) * C2 * (2 * I2) * B := by
    have hev : deriv (fctCauchy K4 ε c L1 α σ) =ᶠ[𝓝 w0]
        fun w => ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, Φ1 w y := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_self (x := w0) (by norm_num))] with w hw using hd_eq w hw
    rw [hev.deriv_eq, (hd12.const_mul _).deriv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpref_pos]
    have hint : ‖∫ y : ℝ, Φ2 w0 y‖ ≤ ∫ y : ℝ, (C2 * B) * (1 / (1 + |y|) ^ 2 + 1 / (1 + |y - η|) ^ 2) :=
      norm_integral_le_of_norm_le ((integrable_inv_sq_shift η).const_mul (C2 * B))
        (ae_of_all _ (hloc2 w0 (mem_ball_self (x := w0) (by norm_num))))
    rw [integral_const_mul, integral_inv_sq_shift] at hint
    calc 1 / (2 * π) * ‖∫ y : ℝ, Φ2 w0 y‖
        ≤ 1 / (2 * π) * (C2 * B * (2 * I2)) := mul_le_mul_of_nonneg_left hint hpref_pos
      _ = _ := by ring
  exact ⟨hC0_norm, hC1_norm, hC2_norm⟩

/-! ### Explicit bounds on `q₁` and its first two derivatives on `{Re ζ ≥ 0}` -/

private noncomputable def fctQ1Poly (s : ℂ) : ℂ := -16 + 80 * s - 144 * s ^ 2 + 112 * s ^ 3 - 32 * s ^ 4
private noncomputable def fctQ1Poly1 (s : ℂ) : ℂ := 80 - 288 * s + 336 * s ^ 2 - 128 * s ^ 3
private noncomputable def fctQ1Poly2 (s : ℂ) : ℂ := -288 + 672 * s - 384 * s ^ 2

private lemma fctQ1_eq_poly {ζ : ℂ} (hζ : ζ + 1 ≠ 0) :
    fctQ1 ζ = fctQ1Poly (ζ + 1)⁻¹ := by
  unfold fctQ1 fctQ1Poly
  field_simp
  ring

lemma fctQ1_differentiableOn_rhp : DifferentiableOn ℂ fctQ1 {ζ : ℂ | -1 / 2 < ζ.re} := by
  intro ζ hζ
  have h1 : ζ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    have : -1 / 2 < ζ.re := hζ
    linarith
  have hder : DifferentiableAt ℂ (fun z : ℂ => 16 * z ^ 3 * (1 - z) / (z + 1) ^ 4) ζ := by
    fun_prop (disch := exact pow_ne_zero 4 h1)
  exact hder.differentiableWithinAt

/-- `‖q₁(ζ)‖`, `‖q₁'(ζ)‖`, `‖q₁''(ζ)‖` are uniformly bounded by `4000` on `{Re ζ ≥ 0}`. -/
lemma fctQ1_deriv_bounds {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    ‖fctQ1 ζ‖ ≤ 4000 ∧ ‖deriv fctQ1 ζ‖ ≤ 4000 ∧ ‖deriv (deriv fctQ1) ζ‖ ≤ 4000 := by
  have hU : IsOpen {z : ℂ | -1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hζU : ζ ∈ {z : ℂ | -1 / 2 < z.re} := by change -1 / 2 < ζ.re; linarith
  have hne : ∀ z ∈ {z : ℂ | -1 / 2 < z.re}, z + 1 ≠ 0 := fun z hz h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    have : -1 / 2 < z.re := hz
    linarith
  have hd_eq : ∀ z ∈ {z : ℂ | -1 / 2 < z.re},
      HasDerivAt fctQ1 (fctQ1Poly1 (z + 1)⁻¹ * (-(z + 1)⁻¹ ^ 2)) z ∧
      HasDerivAt (fun w => fctQ1Poly1 (w + 1)⁻¹ * (-(w + 1)⁻¹ ^ 2))
        (fctQ1Poly2 (z + 1)⁻¹ * (z + 1)⁻¹ ^ 4 + fctQ1Poly1 (z + 1)⁻¹ * (2 * (z + 1)⁻¹ ^ 3)) z := by
    intro z hz
    have hz1 : z + 1 ≠ 0 := hne z hz
    have hs : HasDerivAt (fun w : ℂ => (w + 1)⁻¹) (-(z + 1)⁻¹ ^ 2) z := by
      have h0 : HasDerivAt (fun w : ℂ => w + 1) 1 z := (hasDerivAt_id z).add_const 1
      refine h0.inv hz1 |>.congr_deriv ?_
      field_simp
    have hp : HasDerivAt fctQ1Poly (fctQ1Poly1 (z + 1)⁻¹) (z + 1)⁻¹ := by
      unfold fctQ1Poly fctQ1Poly1
      refine (((((hasDerivAt_const _ (-16 : ℂ)).add
        ((hasDerivAt_id _).const_mul (80 : ℂ))).sub
        (((hasDerivAt_id _).pow 2).const_mul (144 : ℂ))).add
        (((hasDerivAt_id _).pow 3).const_mul (112 : ℂ))).sub
        (((hasDerivAt_id _).pow 4).const_mul (32 : ℂ))).congr_deriv ?_
      ring
    have hcomp : HasDerivAt (fun w => fctQ1Poly (w + 1)⁻¹)
        (fctQ1Poly1 (z + 1)⁻¹ * (-(z + 1)⁻¹ ^ 2)) z := by
      have := hp.scomp z hs
      simpa [Function.comp_def, smul_eq_mul, mul_comm] using this
    have hev : fctQ1 =ᶠ[𝓝 z] fun w => fctQ1Poly (w + 1)⁻¹ := by
      filter_upwards [hU.mem_nhds hz] with w hw using fctQ1_eq_poly (hne w hw)
    refine ⟨hcomp.congr_of_eventuallyEq hev, ?_⟩
    have hp1 : HasDerivAt fctQ1Poly1 (fctQ1Poly2 (z + 1)⁻¹) (z + 1)⁻¹ := by
      unfold fctQ1Poly1 fctQ1Poly2
      refine ((((hasDerivAt_const _ (80 : ℂ)).sub
        ((hasDerivAt_id _).const_mul (288 : ℂ))).add
        (((hasDerivAt_id _).pow 2).const_mul (336 : ℂ))).sub
        (((hasDerivAt_id _).pow 3).const_mul (128 : ℂ))).congr_deriv ?_
      ring
    have h1 : HasDerivAt (fun w => fctQ1Poly1 (w + 1)⁻¹)
        (fctQ1Poly2 (z + 1)⁻¹ * (-(z + 1)⁻¹ ^ 2)) z := by
      have := hp1.scomp z hs
      simpa [Function.comp_def, smul_eq_mul, mul_comm] using this
    have h2 : HasDerivAt (fun w : ℂ => -(w + 1)⁻¹ ^ 2) (-(2 * (z + 1)⁻¹ * (-(z + 1)⁻¹ ^ 2))) z := by
      convert (hs.pow 2).neg using 1
      simp
    refine (h1.mul h2).congr_deriv ?_
    ring
  have hs1 : ‖(ζ + 1)⁻¹‖ ≤ 1 := by
    have h1 : 1 ≤ ‖ζ + 1‖ := by
      have := Complex.re_le_norm (ζ + 1)
      simp only [Complex.add_re, Complex.one_re] at this
      linarith
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ h1
  have hsp : ∀ k : ℕ, ‖(ζ + 1)⁻¹‖ ^ k ≤ 1 := fun k => pow_le_one₀ (norm_nonneg _) hs1
  have hp0 : ‖fctQ1Poly (ζ + 1)⁻¹‖ ≤ 384 := by
    unfold fctQ1Poly
    set s := (ζ + 1)⁻¹
    have t := norm_sub_le (-16 + 80 * s - 144 * s ^ 2 + 112 * s ^ 3) (32 * s ^ 4)
    have t1 := norm_add_le (-16 + 80 * s - 144 * s ^ 2) (112 * s ^ 3)
    have t2 := norm_sub_le (-16 + 80 * s) (144 * s ^ 2)
    have t3 := norm_add_le (-16 : ℂ) (80 * s)
    simp only [norm_neg, norm_mul, norm_pow, Complex.norm_ofNat] at t t1 t2 t3
    have a0 := hsp 1; have a2 := hsp 2; have a3 := hsp 3; have a4 := hsp 4
    simp only [pow_one] at a0
    linarith
  have hp1 : ‖fctQ1Poly1 (ζ + 1)⁻¹‖ ≤ 832 := by
    unfold fctQ1Poly1
    set s := (ζ + 1)⁻¹
    have t1 := norm_sub_le (80 - 288 * s + 336 * s ^ 2) (128 * s ^ 3)
    have t2 := norm_add_le (80 - 288 * s) (336 * s ^ 2)
    have t3 := norm_sub_le (80 : ℂ) (288 * s)
    simp only [norm_mul, norm_pow, Complex.norm_ofNat] at t1 t2 t3
    have a1 := hsp 1; have a2 := hsp 2; have a3 := hsp 3
    simp only [pow_one] at a1
    linarith
  have hp2 : ‖fctQ1Poly2 (ζ + 1)⁻¹‖ ≤ 1344 := by
    unfold fctQ1Poly2
    set s := (ζ + 1)⁻¹
    have t1 := norm_sub_le (-288 + 672 * s) (384 * s ^ 2)
    have t2 := norm_add_le (-288 : ℂ) (672 * s)
    simp only [norm_neg, norm_mul, norm_pow, Complex.norm_ofNat] at t1 t2
    have a1 := hsp 1; have a2 := hsp 2
    simp only [pow_one] at a1
    linarith
  have hev_d : deriv fctQ1 =ᶠ[𝓝 ζ] fun w => fctQ1Poly1 (w + 1)⁻¹ * (-(w + 1)⁻¹ ^ 2) := by
    filter_upwards [hU.mem_nhds hζU] with w hw using (hd_eq w hw).1.deriv
  refine ⟨?_, ?_, ?_⟩
  · rw [fctQ1_eq_poly (hne ζ hζU)]
    linarith
  · rw [(hd_eq ζ hζU).1.deriv, norm_mul, norm_neg, norm_pow]
    calc ‖fctQ1Poly1 (ζ + 1)⁻¹‖ * ‖(ζ + 1)⁻¹‖ ^ 2 ≤ 832 * 1 := mul_le_mul hp1 (hsp 2) (by positivity) (by positivity)
      _ ≤ 4000 := by norm_num
  · rw [hev_d.deriv_eq, (hd_eq ζ hζU).2.deriv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, norm_pow]
    calc ‖fctQ1Poly2 (ζ + 1)⁻¹‖ * ‖(ζ + 1)⁻¹‖ ^ 4 + ‖fctQ1Poly1 (ζ + 1)⁻¹‖ * (2 * ‖(ζ + 1)⁻¹‖ ^ 3)
        ≤ 1344 * 1 + 832 * (2 * 1) := by gcongr; exact hsp 4; exact hsp 3
      _ ≤ 4000 := by norm_num

/-- info: 'FormalResearch.SignUncertainty.fctCauchy_line_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctCauchy_line_deriv_bounds

/-- info: 'FormalResearch.SignUncertainty.fctQ1_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctQ1_deriv_bounds

end FormalResearch.SignUncertainty
