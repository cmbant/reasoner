/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_1_Contour

/-!
# Section 5.1 (`s4:5.1`) Closed-Strip Continuous Extension `spinGcalCl`

Defines `spinKbCl`, `spinGeffCl`, and `spinGcalCl` and proves `spinGcalCl_props`:
`spinGcalCl a Φ` is continuous on the closed strip `{b : ℂ | |b.im| ≤ 1 / 2}` and agrees with
`spinGcal a Φ` on the open strip `spinStrip (1 / 2)`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable def spinKbCl (a : ℝ) (b : ℂ) (rL rR : ℝ) : ℂ :=
  ∫ d : ℝ, spinHb b d *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b + (d : ℂ))) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b - (d : ℂ)))

noncomputable def spinGeffCl (a : ℝ) (Φ : ℝ × ℝ → ℝ) (b : ℂ) : ℂ :=
  -((1 / (Real.sqrt π * spinSigma0) : ℝ) : ℂ) *
    ∫ p : ℝ × ℝ, (Φ p : ℂ) * spinKbCl a b p.1 p.2

noncomputable def spinGcalCl (a : ℝ) (Φ : ℝ × ℝ → ℝ) (b : ℂ) : ℂ :=
  ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0 : ℝ) : ℂ) *
    spinCalFacC b * spinGeffCl a Φ b

private lemma continuous_spinHb_d {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    Continuous (fun d : ℝ => spinHb b d) := by
  unfold spinHb
  have hw1_ne : ∀ d : ℝ, Complex.cosh ((b + (d : ℂ)) / 2) ≠ 0 := fun d =>
    (complex_tanh_bound_strip' (by simp [abs_div]; linarith)).1
  have hw2_ne : ∀ d : ℝ, Complex.cosh ((b - (d : ℂ)) / 2) ≠ 0 := fun d =>
    (complex_tanh_bound_strip' (by simp [abs_div]; linarith)).1
  have ht1 : Continuous (fun d : ℝ => Complex.tanh ((b + (d : ℂ)) / 2)) := by
    simp_rw [Complex.tanh_eq_sinh_div_cosh]; exact Continuous.div (by fun_prop) (by fun_prop) hw1_ne
  have ht2 : Continuous (fun d : ℝ => Complex.tanh ((b - (d : ℂ)) / 2)) := by
    simp_rw [Complex.tanh_eq_sinh_div_cosh]; exact Continuous.div (by fun_prop) (by fun_prop) hw2_ne
  exact (((continuous_const.mul ((ht1.pow 2).mul (ht2.pow 2))).div_const _).mul (by fun_prop))

private lemma norm_spinKb_integrand_le {a : ℝ} (ha0 : 0 < a) {b : ℂ} (hb : |b.im| ≤ 1 / 2)
    (rL rR d : ℝ) :
    ‖spinHb b d * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b + (d : ℂ))) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b - (d : ℂ)))‖ ≤
      (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
        Real.exp (2 * π * Real.sqrt a * (|rL| + |rR|))) * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
  have h1 := spinHb_norm_le_closed hb d
  have him1 : (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b + (d : ℂ))).im =
      4 * π * Real.sqrt a * rL * b.im := by
    simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
  have him2 : (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b - (d : ℂ))).im =
      4 * π * Real.sqrt a * rR * b.im := by
    simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
  have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b + (d : ℂ)))‖ ≤
      Real.exp (2 * π * Real.sqrt a * |rL|) := by
    calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * rL * b.im) := by
          rw [← him1]; exact norm_complex_cos_le_cosh _
      _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 2) * rL) := cosh_mul_im_le_cosh ha0 (by norm_num) hb
      _ ≤ Real.exp (2 * π * Real.sqrt a * |rL|) := by
          rw [← Real.cosh_abs, Real.cosh_eq, abs_mul,
            abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * (1 / 2)),
            show 4 * π * Real.sqrt a * (1 / 2) * |rL| = 2 * π * Real.sqrt a * |rL| by ring]
          linarith [Real.exp_le_exp.mpr (by linarith [show 0 ≤ 2 * π * Real.sqrt a * |rL| by positivity] :
            -(2 * π * Real.sqrt a * |rL|) ≤ 2 * π * Real.sqrt a * |rL|)]
  have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b - (d : ℂ)))‖ ≤
      Real.exp (2 * π * Real.sqrt a * |rR|) := by
    calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * rR * b.im) := by
          rw [← him2]; exact norm_complex_cos_le_cosh _
      _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 2) * rR) := cosh_mul_im_le_cosh ha0 (by norm_num) hb
      _ ≤ Real.exp (2 * π * Real.sqrt a * |rR|) := by
          rw [← Real.cosh_abs, Real.cosh_eq, abs_mul,
            abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * (1 / 2)),
            show 4 * π * Real.sqrt a * (1 / 2) * |rR| = 2 * π * Real.sqrt a * |rR| by ring]
          linarith [Real.exp_le_exp.mpr (by linarith [show 0 ≤ 2 * π * Real.sqrt a * |rR| by positivity] :
            -(2 * π * Real.sqrt a * |rR|) ≤ 2 * π * Real.sqrt a * |rR|)]
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  rw [norm_mul, norm_mul]
  calc ‖spinHb b d‖ * ‖Complex.cos _‖ * ‖Complex.cos _‖
      ≤ (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
            Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) *
          Real.exp (2 * π * Real.sqrt a * |rL|) * Real.exp (2 * π * Real.sqrt a * |rR|) :=
        mul_le_mul (mul_le_mul h1 hc1 (norm_nonneg _) (by positivity)) hc2 (norm_nonneg _) (by positivity)
    _ = _ := by
        rw [mul_assoc (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
            Real.exp (-(d ^ 2 / spinSigma0 ^ 2))), ← Real.exp_add]
        ring_nf

private lemma spinKbCl_continuousOn_b {a : ℝ} (ha : 2 ≤ a) (rL rR : ℝ) :
    ContinuousOn (fun b : ℂ => spinKbCl a b rL rR) {b : ℂ | |b.im| ≤ 1 / 2} := by
  have ha0 : 0 < a := by linarith
  have hgauss_int : Integrable (fun d : ℝ => Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  let C_bound : ℝ := 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
    Real.exp (2 * π * Real.sqrt a * (|rL| + |rR|))
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_of_dominated
    (F := fun (b : {b : ℂ | |b.im| ≤ 1 / 2}) (d : ℝ) =>
      spinHb b.1 d * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b.1 + (d : ℂ))) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b.1 - (d : ℂ))))
    (bound := fun d => C_bound * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)))
    (fun b => ((continuous_spinHb_d b.2).mul (by fun_prop)).mul (by fun_prop) |>.aestronglyMeasurable)
    (fun b => Eventually.of_forall fun d => norm_spinKb_integrand_le ha0 b.2 rL rR d)
    (hgauss_int.const_mul C_bound)
    (Eventually.of_forall fun d => ?_)
  have hcont_b : Continuous (fun b : {b : ℂ | |b.im| ≤ 1 / 2} => spinHb b.1 d *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b.1 + (d : ℂ))) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b.1 - (d : ℂ)))) := by
    unfold spinHb
    have h1_ne : ∀ b : {b : ℂ | |b.im| ≤ 1 / 2}, 1 + b.1 ^ 2 ≠ 0 := fun b => by
      have hb_re : 3 / 4 ≤ (1 + b.1 ^ 2).re := by
        simp only [Complex.add_re, Complex.one_re, sq, Complex.mul_re]
        nlinarith [sq_nonneg b.1.re, sq_abs b.1.im, pow_le_pow_left₀ (abs_nonneg b.1.im) b.2 2]
      exact norm_ne_zero_iff.mp (by linarith [hb_re.trans (Complex.re_le_norm _)])
    have hw1_ne : ∀ b : {b : ℂ | |b.im| ≤ 1 / 2}, Complex.cosh ((b.1 + (d : ℂ)) / 2) ≠ 0 := fun b => by
      have hb_im : |(b : ℂ).im| ≤ 1 / 2 := b.2
      have h : |((b.1 + (d : ℂ)) / 2).im| ≤ 5 / 4 := by
        simp [Complex.add_im, Complex.ofReal_im]; rw [abs_div]; norm_num; linarith [hb_im]
      exact (complex_tanh_bound_strip' h).1
    have hw2_ne : ∀ b : {b : ℂ | |b.im| ≤ 1 / 2}, Complex.cosh ((b.1 - (d : ℂ)) / 2) ≠ 0 := fun b => by
      have hb_im : |(b : ℂ).im| ≤ 1 / 2 := b.2
      have h : |((b.1 - (d : ℂ)) / 2).im| ≤ 5 / 4 := by
        simp [Complex.sub_im, Complex.ofReal_im]; rw [abs_div]; norm_num; linarith [hb_im]
      exact (complex_tanh_bound_strip' h).1
    have hd_sub : Continuous (fun b : {b : ℂ | |b.im| ≤ 1 / 2} => b.1) := continuous_subtype_val
    have ht1 : Continuous (fun b : {b : ℂ | |b.im| ≤ 1 / 2} => Complex.tanh ((b.1 + (d : ℂ)) / 2)) := by
      simp_rw [Complex.tanh_eq_sinh_div_cosh]
      exact Continuous.div (Complex.continuous_sinh.comp ((hd_sub.add continuous_const).div_const 2))
        (Complex.continuous_cosh.comp ((hd_sub.add continuous_const).div_const 2)) hw1_ne
    have ht2 : Continuous (fun b : {b : ℂ | |b.im| ≤ 1 / 2} => Complex.tanh ((b.1 - (d : ℂ)) / 2)) := by
      simp_rw [Complex.tanh_eq_sinh_div_cosh]
      exact Continuous.div (Complex.continuous_sinh.comp ((hd_sub.sub continuous_const).div_const 2))
        (Complex.continuous_cosh.comp ((hd_sub.sub continuous_const).div_const 2)) hw2_ne
    have hhb_sub : Continuous (fun b : {b : ℂ | |b.im| ≤ 1 / 2} =>
        ((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b.1 ^ 2) *
          (Complex.tanh ((b.1 + (d : ℂ)) / 2) ^ 2 * Complex.tanh ((b.1 - (d : ℂ)) / 2) ^ 2) /
          ((Real.tanh (xiStar / 2) ^ 4 : ℝ) : ℂ) *
          Complex.exp (-(((d ^ 2 / spinSigma0 ^ 2 : ℝ) : ℂ)))) :=
      (((Continuous.div continuous_const (continuous_const.add (hd_sub.pow 2)) h1_ne).mul
        ((ht1.pow 2).mul (ht2.pow 2))).div_const _).mul continuous_const
    exact (hhb_sub.mul (Complex.continuous_cos.comp
      (continuous_const.mul (hd_sub.add continuous_const)))).mul
      (Complex.continuous_cos.comp (continuous_const.mul (hd_sub.sub continuous_const)))
  exact hcont_b

private lemma spinKbCl_continuous_p {a : ℝ} (ha : 2 ≤ a) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    Continuous (fun p : ℝ × ℝ => spinKbCl a b p.1 p.2) := by
  have ha0 : 0 < a := by linarith
  have hgauss_int : Integrable (fun d : ℝ => Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  rw [continuous_iff_continuousAt]
  intro p₀
  have hmem : Metric.closedBall p₀ 1 ∈ 𝓝 p₀ := Metric.closedBall_mem_nhds p₀ zero_lt_one
  refine ContinuousOn.continuousAt ?_ hmem
  let C_loc : ℝ := 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
    Real.exp (4 * π * Real.sqrt a * (‖p₀‖ + 1))
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_of_dominated
    (F := fun (p : Metric.closedBall p₀ 1) (d : ℝ) =>
      spinHb b d * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1.1 : ℂ) * (b + (d : ℂ))) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1.2 : ℂ) * (b - (d : ℂ))))
    (bound := fun d => C_loc * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)))
    (fun p => ((continuous_spinHb_d hb).mul (by fun_prop)).mul (by fun_prop) |>.aestronglyMeasurable)
    (fun p => Eventually.of_forall fun d => ?_)
    (hgauss_int.const_mul C_loc)
    (Eventually.of_forall fun d =>
      (Continuous.mul (Continuous.mul continuous_const
        (Complex.continuous_cos.comp ((continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_fst.comp continuous_subtype_val))).mul continuous_const)))
        (Complex.continuous_cos.comp ((continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_subtype_val))).mul continuous_const))))
  have hp_norm : ‖p.1‖ ≤ ‖p₀‖ + 1 := by
    have h1 : dist p.1 p₀ ≤ 1 := Metric.mem_closedBall.mp p.2
    calc ‖p.1‖ = ‖(p.1 - p₀) + p₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖p.1 - p₀‖ + ‖p₀‖ := norm_add_le _ _
      _ = dist p.1 p₀ + ‖p₀‖ := by rw [dist_eq_norm]
      _ ≤ ‖p₀‖ + 1 := by linarith
  have h1 := norm_spinKb_integrand_le ha0 hb p.1.1 p.1.2 d
  have hp1 : |p.1.1| ≤ ‖p₀‖ + 1 := (Real.norm_eq_abs _ ▸ norm_fst_le p.1).trans hp_norm
  have hp2 : |p.1.2| ≤ ‖p₀‖ + 1 := (Real.norm_eq_abs _ ▸ norm_snd_le p.1).trans hp_norm
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  have hexp_le : Real.exp (2 * π * Real.sqrt a * (|p.1.1| + |p.1.2|)) ≤
      Real.exp (4 * π * Real.sqrt a * (‖p₀‖ + 1)) := by
    refine Real.exp_le_exp.mpr ?_
    calc 2 * π * Real.sqrt a * (|p.1.1| + |p.1.2|)
        ≤ 2 * π * Real.sqrt a * ((‖p₀‖ + 1) + (‖p₀‖ + 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) (by positivity)
      _ = 4 * π * Real.sqrt a * (‖p₀‖ + 1) := by ring
  exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le (by positivity))
    (Real.exp_pos _).le)

private lemma spinKbCl_bound {a : ℝ} (ha : 2 ≤ a) (rL rR : ℝ) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖spinKbCl a b rL rR‖ ≤
      max (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
            (∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * Real.exp (2 * π))
          (spinHbWideConst' * (∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2)))) +
        (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
          (∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * 16 * 256) *
          a ^ 2 * spinV1 a rL * spinV1 a rR := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hgauss_int : Integrable (fun d : ℝ => Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  let G₀ : ℝ := ∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2))
  have hG₀_nn : 0 ≤ G₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  let C_hb : ℝ := 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4
  have hChb_nn : 0 ≤ C_hb := by dsimp [C_hb]; positivity
  let C₁ : ℝ := C_hb * G₀ * Real.exp (2 * π)
  let C₂ : ℝ := C_hb * G₀ * 16 * 256
  let C₃ : ℝ := spinHbWideConst' * G₀
  set S : ℝ := |rL| + |rR|
  set D : ℝ := |(|rL| - |rR|)|
  have hS_nn : 0 ≤ S := by positivity
  have hKb_exp : ‖spinKbCl a b rL rR‖ ≤ C_hb * G₀ * Real.exp (2 * π * Real.sqrt a * S) := by
    unfold spinKbCl
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ d : ℝ, ‖spinHb b d * Complex.cos _ * Complex.cos _‖
        ≤ ∫ d : ℝ, (C_hb * Real.exp (2 * π * Real.sqrt a * S)) * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (hgauss_int.const_mul _)
            (Eventually.of_forall fun d => norm_spinKb_integrand_le ha0 hb rL rR d)
      _ = C_hb * G₀ * Real.exp (2 * π * Real.sqrt a * S) := by rw [integral_const_mul]; dsimp [G₀]; ring
  by_cases hS_small : S ≤ (Real.sqrt a)⁻¹
  · have h1 : ‖spinKbCl a b rL rR‖ ≤ C₁ := by
      calc ‖spinKbCl a b rL rR‖ ≤ C_hb * G₀ * Real.exp (2 * π * Real.sqrt a * S) := hKb_exp
        _ ≤ C_hb * G₀ * Real.exp (2 * π * Real.sqrt a * (Real.sqrt a)⁻¹) := by gcongr
        _ = C₁ := by dsimp [C₁]; rw [mul_assoc (2 * π), mul_inv_cancel₀ hsqa.ne', mul_one]
    have h2 : 0 ≤ C₂ * a ^ 2 * spinV1 a rL * spinV1 a rR :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (spinV1_nonneg ha rL))
        (spinV1_nonneg ha rR)
    linarith [le_max_left C₁ C₃]
  · push Not at hS_small
    by_cases hD_small : D ≤ S / 2
    · have hm1 : 1 / 4 ≤ min 1 (Real.sqrt a * |rL|) := by
        refine le_min (by norm_num) ?_
        have h1 : (Real.sqrt a)⁻¹ / 4 ≤ |rL| := by
          have hle : S - D ≤ 2 * |rL| := by
            dsimp [S, D]
            rcases le_total |rL| |rR| with h | h
            · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
            · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
          linarith
        calc 1 / 4 = Real.sqrt a * ((Real.sqrt a)⁻¹ / 4) := by field_simp [hsqa.ne']
          _ ≤ Real.sqrt a * |rL| := by gcongr
      have hm2 : 1 / 4 ≤ min 1 (Real.sqrt a * |rR|) := by
        refine le_min (by norm_num) ?_
        have h1 : (Real.sqrt a)⁻¹ / 4 ≤ |rR| := by
          have hle : S - D ≤ 2 * |rR| := by
            dsimp [S, D]
            rcases le_total |rL| |rR| with h | h
            · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
            · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
          linarith
        calc 1 / 4 = Real.sqrt a * ((Real.sqrt a)⁻¹ / 4) := by field_simp [hsqa.ne']
          _ ≤ Real.sqrt a * |rR| := by gcongr
      have hv1 := spinV1_ge_inv_four_a_exp_min_sq ha rL
      have hv2 := spinV1_ge_inv_four_a_exp_min_sq ha rR
      have hexp_le : Real.exp (2 * π * Real.sqrt a * S) ≤
          16 * 256 * a ^ 2 * spinV1 a rL * spinV1 a rR := by
        have hprod : ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |rL|) * (1 / 4 : ℝ) ^ 2) *
            ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |rR|) * (1 / 4 : ℝ) ^ 2) ≤
            spinV1 a rL * spinV1 a rR := by
          refine mul_le_mul ?_ ?_ (by positivity) (spinV1_nonneg ha rL)
          · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hm1 2) (by positivity)).trans hv1
          · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hm2 2) (by positivity)).trans hv2
        have hlhs : ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |rL|) * (1 / 4 : ℝ) ^ 2) *
            ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |rR|) * (1 / 4 : ℝ) ^ 2) =
            (16 * 256 * a ^ 2)⁻¹ * Real.exp (2 * π * Real.sqrt a * S) := by
          rw [show ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |rL|) * (1 / 4 : ℝ) ^ 2) *
              ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |rR|) * (1 / 4 : ℝ) ^ 2) =
              ((4 * a)⁻¹ * (1 / 4 : ℝ) ^ 2) ^ 2 *
                (Real.exp (2 * π * Real.sqrt a * |rL|) * Real.exp (2 * π * Real.sqrt a * |rR|)) by ring,
            ← Real.exp_add]
          rw [show 2 * π * Real.sqrt a * |rL| + 2 * π * Real.sqrt a * |rR| =
              2 * π * Real.sqrt a * S by dsimp [S]; ring]
          field_simp [ha0.ne']; ring
        rw [hlhs] at hprod
        calc Real.exp (2 * π * Real.sqrt a * S)
            = (16 * 256 * a ^ 2) * ((16 * 256 * a ^ 2)⁻¹ * Real.exp (2 * π * Real.sqrt a * S)) := by
              field_simp [ha0.ne']
          _ ≤ (16 * 256 * a ^ 2) * (spinV1 a rL * spinV1 a rR) := by gcongr
          _ = 16 * 256 * a ^ 2 * spinV1 a rL * spinV1 a rR := by ring
      have hkb2 : ‖spinKbCl a b rL rR‖ ≤ C₂ * a ^ 2 * spinV1 a rL * spinV1 a rR := by
        calc ‖spinKbCl a b rL rR‖ ≤ C_hb * G₀ * Real.exp (2 * π * Real.sqrt a * S) := hKb_exp
          _ ≤ C_hb * G₀ * (16 * 256 * a ^ 2 * spinV1 a rL * spinV1 a rR) := by gcongr
          _ = C₂ * a ^ 2 * spinV1 a rL * spinV1 a rR := by dsimp [C₂]; ring
      have hmax_nn : 0 ≤ max C₁ C₃ := le_trans (by positivity : 0 ≤ C₁) (le_max_left _ _)
      linarith
    · push Not at hD_small
      let term : ℝ → ℝ → ℂ := fun s₁ s₂ =>
        ∫ d : ℝ, spinHb b d * Complex.exp (I *
          (((4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * (s₁ * rL - s₂ * rR) : ℝ) : ℂ) * (d : ℂ)))
      have hterm_bd : ∀ (s₁ s₂ : ℝ), |s₁| = 1 → |s₂| = 1 → ‖term s₁ s₂‖ ≤ C₃ := by
        intro s₁ s₂ hs₁ hs₂
        set β : ℝ := 4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR)
        set ω : ℝ := 4 * π * Real.sqrt a * (s₁ * rL - s₂ * rR)
        set σ : ℝ := if 0 ≤ ω then 1 else -1
        have hσ : |σ| ≤ 1 := by dsimp [σ]; split_ifs <;> norm_num
        have hσω : σ * ω = |ω| := by
          dsimp [σ]; split_ifs with h
          · rw [one_mul, abs_of_nonneg h]
          · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
        have hβ_bd : |β| ≤ 4 * π * Real.sqrt a * S := by
          dsimp [β, S]
          rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a)]
          have htri : |s₁ * rL + s₂ * rR| ≤ |rL| + |rR| := by
            calc |s₁ * rL + s₂ * rR| ≤ |s₁ * rL| + |s₂ * rR| := abs_add_le _ _
              _ = |s₁| * |rL| + |s₂| * |rR| := by rw [abs_mul, abs_mul]
              _ = |rL| + |rR| := by rw [hs₁, hs₂, one_mul, one_mul]
          exact mul_le_mul_of_nonneg_left htri (by positivity)
        have hω_bd : 4 * π * Real.sqrt a * D ≤ |ω| := by
          dsimp [ω, D]
          rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a)]
          have h1 : |(|s₁ * rL| - |s₂ * rR|)| ≤ |s₁ * rL - s₂ * rR| := abs_abs_sub_abs_le_abs_sub _ _
          simp only [abs_mul, hs₁, hs₂, one_mul] at h1
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have hshift := gaussian_contour_shift' hb β ω σ hσ
        dsimp [term]; rw [hshift]
        have hbd_t : ∀ t : ℝ, ‖spinHbC' b ((t : ℂ) + (2 * σ : ℝ) * I) *
            Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I)))‖ ≤
            spinHbWideConst' * Real.exp (-(t ^ 2 / spinSigma0 ^ 2)) := by
          intro t
          have him_w : |((t : ℂ) + (2 * σ : ℝ) * I).im| ≤ 2 := by simp [abs_mul]; linarith
          have h1 := (spinHbC'_closed_strip_bound_and_diff hb).2 _ him_w
          rw [show ((t : ℂ) + (2 * σ : ℝ) * I).re = t by simp] at h1
          have him_exp : (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I))).re =
              -(β * b.im) - 2 * (σ * ω) := by
            simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]; ring
          have hexp_le1 : ‖Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I)))‖ ≤ 1 := by
            rw [Complex.norm_exp, him_exp, hσω, Real.exp_le_one_iff]
            have hA : -(β * b.im) ≤ 2 * π * Real.sqrt a * S := by
              calc -(β * b.im) ≤ |β * b.im| := neg_le_abs _
                _ = |β| * |b.im| := abs_mul _ _
                _ ≤ (4 * π * Real.sqrt a * S) * (1 / 2) :=
                    mul_le_mul hβ_bd hb (abs_nonneg _) (by positivity)
                _ = 2 * π * Real.sqrt a * S := by ring
            have hB : 8 * π * Real.sqrt a * D ≤ 2 * |ω| := by linarith
            have hC : 2 * π * Real.sqrt a * S ≤ 8 * π * Real.sqrt a * D := by
              have : S ≤ 4 * D := by linarith
              calc 2 * π * Real.sqrt a * S ≤ 2 * π * Real.sqrt a * (4 * D) := by gcongr
                _ = 8 * π * Real.sqrt a * D := by ring
            linarith
          rw [norm_mul]
          calc ‖spinHbC' b _‖ * ‖Complex.exp _‖
              ≤ (spinHbWideConst' * Real.exp (-(t ^ 2 / spinSigma0 ^ 2))) * 1 :=
                mul_le_mul h1 hexp_le1 (norm_nonneg _)
                  (mul_nonneg spinHbWideConst'_pos.le (Real.exp_pos _).le)
            _ = spinHbWideConst' * Real.exp (-(t ^ 2 / spinSigma0 ^ 2)) := mul_one _
        refine (norm_integral_le_integral_norm _).trans ?_
        calc ∫ t : ℝ, ‖spinHbC' b ((t : ℂ) + (2 * σ : ℝ) * I) * Complex.exp _‖
            ≤ ∫ t : ℝ, spinHbWideConst' * Real.exp (-(t ^ 2 / spinSigma0 ^ 2)) :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                (hgauss_int.const_mul _) (Eventually.of_forall hbd_t)
          _ = C₃ := by rw [integral_const_mul]
      have hterm_int : ∀ (s₁ s₂ : ℝ), Integrable (fun d : ℝ => spinHb b d * Complex.exp (I *
          (((4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * (s₁ * rL - s₂ * rR) : ℝ) : ℂ) * (d : ℂ)))) volume := fun s₁ s₂ => by
        refine (hgauss_int.const_mul (C_hb * Real.exp (|4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR)| / 2))).mono'
          (((continuous_spinHb_d hb).mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun d => ?_)
        have h1 : ‖spinHb b d‖ ≤ C_hb * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) :=
          spinHb_norm_le_closed hb d
        have him : (I * (((4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * (s₁ * rL - s₂ * rR) : ℝ) : ℂ) * (d : ℂ))).re =
            -(4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR) * b.im) := by
          simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        have hexp : ‖Complex.exp (I * (((4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * (s₁ * rL - s₂ * rR) : ℝ) : ℂ) * (d : ℂ)))‖ ≤
            Real.exp (|4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR)| / 2) := by
          rw [Complex.norm_exp, him, Real.exp_le_exp]
          calc -(4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR) * b.im)
              ≤ |4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR) * b.im| := neg_le_abs _
            _ = |4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR)| * |b.im| := abs_mul _ _
            _ ≤ |4 * π * Real.sqrt a * (s₁ * rL + s₂ * rR)| * (1 / 2) :=
                mul_le_mul_of_nonneg_left hb (abs_nonneg _)
            _ = _ := by ring
        rw [norm_mul]
        exact (mul_le_mul h1 hexp (norm_nonneg _)
          (mul_nonneg hChb_nn (Real.exp_pos _).le)).trans_eq (by ring)
      have hpt : ∀ d : ℝ,
          spinHb b d * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b + (d : ℂ))) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b - (d : ℂ))) =
          (1 / 4 : ℂ) * (
            spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * rL + 1 * rR) : ℝ) : ℂ) * b +
              ((4 * π * Real.sqrt a * (1 * rL - 1 * rR) : ℝ) : ℂ) * (d : ℂ))) +
            spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * rL + (-1) * rR) : ℝ) : ℂ) * b +
              ((4 * π * Real.sqrt a * (1 * rL - (-1) * rR) : ℝ) : ℂ) * (d : ℂ))) +
            spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * ((-1) * rL + 1 * rR) : ℝ) : ℂ) * b +
              ((4 * π * Real.sqrt a * ((-1) * rL - 1 * rR) : ℝ) : ℂ) * (d : ℂ))) +
            spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * ((-1) * rL + (-1) * rR) : ℝ) : ℂ) * b +
              ((4 * π * Real.sqrt a * ((-1) * rL - (-1) * rR) : ℝ) : ℂ) * (d : ℂ)))) := fun d => by
        set A : ℂ := 4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b + (d : ℂ))
        set B : ℂ := 4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b - (d : ℂ))
        have hcosA : Complex.cos A = (Complex.exp (I * A) + Complex.exp (-(I * A))) / 2 := by
          rw [Complex.cos, mul_comm A I, mul_comm (-A) I, mul_neg]
        have hcosB : Complex.cos B = (Complex.exp (I * B) + Complex.exp (-(I * B))) / 2 := by
          rw [Complex.cos, mul_comm B I, mul_comm (-B) I, mul_neg]
        have he1 : I * (((4 * π * Real.sqrt a * (1 * rL + 1 * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * (1 * rL - 1 * rR) : ℝ) : ℂ) * (d : ℂ)) = I * A + I * B := by
          dsimp [A, B]; push_cast; ring
        have he2 : I * (((4 * π * Real.sqrt a * (1 * rL + (-1) * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * (1 * rL - (-1) * rR) : ℝ) : ℂ) * (d : ℂ)) = I * A + -(I * B) := by
          dsimp [A, B]; push_cast; ring
        have he3 : I * (((4 * π * Real.sqrt a * ((-1) * rL + 1 * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * ((-1) * rL - 1 * rR) : ℝ) : ℂ) * (d : ℂ)) = -(I * A) + I * B := by
          dsimp [A, B]; push_cast; ring
        have he4 : I * (((4 * π * Real.sqrt a * ((-1) * rL + (-1) * rR) : ℝ) : ℂ) * b +
            ((4 * π * Real.sqrt a * ((-1) * rL - (-1) * rR) : ℝ) : ℂ) * (d : ℂ)) = -(I * A) + -(I * B) := by
          dsimp [A, B]; push_cast; ring
        rw [he1, he2, he3, he4, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
          hcosA, hcosB]; ring
      have hKb_eq : spinKbCl a b rL rR =
          (1 / 4 : ℂ) * (term 1 1 + term 1 (-1) + term (-1) 1 + term (-1) (-1)) := by
        have hi12 := (hterm_int 1 1).add (hterm_int 1 (-1))
        have hi123 := hi12.add (hterm_int (-1) 1)
        unfold spinKbCl; simp_rw [hpt]
        rw [integral_const_mul]
        congr 1
        exact (integral_add hi123 (hterm_int (-1) (-1))).trans
          (congrArg₂ (· + ·)
            ((integral_add hi12 (hterm_int (-1) 1)).trans
              (congrArg₂ (· + ·) (integral_add (hterm_int 1 1) (hterm_int 1 (-1))) rfl))
            rfl)
      have hKb3 : ‖spinKbCl a b rL rR‖ ≤ C₃ := by
        rw [hKb_eq, norm_mul, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
        have t1 := hterm_bd 1 1 (by norm_num) (by norm_num)
        have t2 := hterm_bd 1 (-1) (by norm_num) (by norm_num)
        have t3 := hterm_bd (-1) 1 (by norm_num) (by norm_num)
        have t4 := hterm_bd (-1) (-1) (by norm_num) (by norm_num)
        calc (1 / 4 : ℝ) * ‖term 1 1 + term 1 (-1) + term (-1) 1 + term (-1) (-1)‖
            ≤ (1 / 4 : ℝ) * (‖term 1 1‖ + ‖term 1 (-1)‖ + ‖term (-1) 1‖ + ‖term (-1) (-1)‖) := by
              gcongr
              exact (norm_add_le _ _).trans (by gcongr; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _))
          _ ≤ (1 / 4 : ℝ) * (4 * C₃) := by gcongr; linarith
          _ = C₃ := by ring
      have h2 : 0 ≤ C₂ * a ^ 2 * spinV1 a rL * spinV1 a rR :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (spinV1_nonneg ha rL))
          (spinV1_nonneg ha rR)
      linarith [le_max_right C₁ C₃]

lemma spinGcalCl_props {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    ContinuousOn (spinGcalCl ((c - 1) / 12) Φ) {b : ℂ | |b.im| ≤ 1 / 2} ∧
    (∀ b ∈ spinStrip (1 / 2), spinGcalCl ((c - 1) / 12) Φ b = spinGcal ((c - 1) / 12) Φ b) := by
  let a : ℝ := (c - 1) / 12
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  let C_13 : ℝ :=
    max (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
          (∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * Real.exp (2 * π))
        (spinHbWideConst' * (∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2))))
  let C_2 : ℝ := 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
    (∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * 16 * 256
  let bound : ℝ × ℝ → ℝ := fun p => |Φ p| * (C_13 + C_2 * a ^ 2 * spinV1 a p.1 * spinV1 a p.2)
  have hbound_int : Integrable bound volume := by
    have h1 := (hΦ.int.norm.congr (Eventually.of_forall fun p => Real.norm_eq_abs _)).const_mul C_13
    have h2 := hΦ.int_M2.const_mul (C_2 * a ^ 2)
    refine (h1.add h2).congr (Eventually.of_forall fun p => ?_)
    dsimp [bound]; ring
  have hgeff_cont : ContinuousOn (spinGeffCl a Φ) {b : ℂ | |b.im| ≤ 1 / 2} := by
    refine continuousOn_const.mul ?_
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_of_dominated
      (F := fun (b : {b : ℂ | |b.im| ≤ 1 / 2}) (p : ℝ × ℝ) => (Φ p : ℂ) * spinKbCl a b.1 p.1 p.2)
      (bound := bound)
      (fun b => ((Complex.continuous_ofReal.comp hΦ.cont).mul
        (spinKbCl_continuous_p ha b.2)).aestronglyMeasurable)
      (fun b => Eventually.of_forall fun p => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (spinKbCl_bound ha p.1 p.2 b.2) (abs_nonneg _))
      hbound_int
      (Eventually.of_forall fun p =>
        Continuous.mul continuous_const (spinKbCl_continuousOn_b ha p.1 p.2).restrict)
  have hfac_cont : Continuous (fun b : ℂ =>
      ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0 : ℝ) : ℂ) * spinCalFacC b) := by
    unfold spinCalFacC; fun_prop
  refine ⟨(hfac_cont.continuousOn.mul hgeff_cont), fun b hb => ?_⟩
  unfold spinGcalCl
  rw [spinGcal_eq_mul_spinGeff]
  congr 1
  have hb_im : |b.im| < 1 / 2 := hb
  set θ : ℝ := max (1 / 24) |b.im|
  have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hθ1 : θ < 1 / 2 := max_lt (by norm_num) hb_im
  have hint_θ := integrable_spinITheta ha hθ0 hθ1 hΦ
  have hgauss_int : Integrable (fun d : ℝ => Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  let Fjoint : ℝ × (ℝ × ℝ) → ℂ := fun q =>
    spinHb b q.1 * ((Φ q.2 : ℂ) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.1 : ℂ) * (b + (q.1 : ℂ))) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.2 : ℂ) * (b - (q.1 : ℂ))))
  let C_hb : ℝ := 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4
  have hFjoint_meas : AEStronglyMeasurable Fjoint (volume.prod volume) := by
    have hc1 := (continuous_spinHb_d hb_im.le).comp (continuous_fst : Continuous (fun q : ℝ × (ℝ × ℝ) => q.1))
    have hc2 : Continuous (fun q : ℝ × (ℝ × ℝ) => (Φ q.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (hΦ.cont.comp continuous_snd)
    have hcont : Continuous Fjoint := by fun_prop
    exact hcont.aestronglyMeasurable
  have hdom_prod : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      (C_hb * Real.exp (-(q.1 ^ 2 / spinSigma0 ^ 2))) *
        (|Φ q.2| * Real.cosh (4 * π * Real.sqrt a * θ * q.2.1) *
          Real.cosh (4 * π * Real.sqrt a * θ * q.2.2))) (volume.prod volume) :=
    (hgauss_int.const_mul C_hb).mul_prod hint_θ
  have hFjoint_int : Integrable Fjoint (volume.prod volume) := by
    refine hdom_prod.mono' hFjoint_meas (Eventually.of_forall fun q => ?_)
    have h1 := spinHb_norm_le_closed hb_im.le q.1
    have him1 : (4 * π * (Real.sqrt a : ℂ) * (q.2.1 : ℂ) * (b + (q.1 : ℂ))).im =
        4 * π * Real.sqrt a * q.2.1 * b.im := by
      simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
    have him2 : (4 * π * (Real.sqrt a : ℂ) * (q.2.2 : ℂ) * (b - (q.1 : ℂ))).im =
        4 * π * Real.sqrt a * q.2.2 * b.im := by
      simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
    have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.1 : ℂ) * (b + (q.1 : ℂ)))‖ ≤
        Real.cosh (4 * π * Real.sqrt a * θ * q.2.1) := by
      calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * q.2.1 * b.im) := by
            rw [← him1]; exact norm_complex_cos_le_cosh _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * q.2.1) :=
            cosh_mul_im_le_cosh ha0 hθ0.le (le_max_right _ _)
    have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.2 : ℂ) * (b - (q.1 : ℂ)))‖ ≤
        Real.cosh (4 * π * Real.sqrt a * θ * q.2.2) := by
      calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * q.2.2 * b.im) := by
            rw [← him2]; exact norm_complex_cos_le_cosh _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * q.2.2) :=
            cosh_mul_im_le_cosh ha0 hθ0.le (le_max_right _ _)
    dsimp [Fjoint]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul h1 (mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)) (by positivity) (by positivity)
  have hfub := integral_integral_swap (f := fun d p => Fjoint (d, p)) hFjoint_int
  unfold spinGeffCl spinGeff spinGC
  have hL : ∫ d : ℝ, spinHb b d * (-(∫ p : ℝ × ℝ, (Φ p : ℂ) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ))) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ))))) =
      -(∫ d : ℝ, ∫ p : ℝ × ℝ, Fjoint (d, p)) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun d => ?_)
    dsimp only; rw [mul_neg, ← integral_const_mul]
  have hR : ∫ p : ℝ × ℝ, (Φ p : ℂ) * spinKbCl a b p.1 p.2 =
      ∫ p : ℝ × ℝ, ∫ d : ℝ, Fjoint (d, p) := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    unfold spinKbCl; dsimp only; rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun d => ?_)
    dsimp [Fjoint]; ring
  change -((1 / (Real.sqrt π * spinSigma0) : ℝ) : ℂ) * ∫ p : ℝ × ℝ, (Φ p : ℂ) * spinKbCl a b p.1 p.2 =
    ((1 / (Real.sqrt π * spinSigma0) : ℝ) : ℂ) *
      ∫ d : ℝ, spinHb b d * (-(∫ p : ℝ × ℝ, (Φ p : ℂ) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ))) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ)))))
  rw [hR, ← hfub, hL]; ring

end FormalResearch.ModularBootstrap.Spin
