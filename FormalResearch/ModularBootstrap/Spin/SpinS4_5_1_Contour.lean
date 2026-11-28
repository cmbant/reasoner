/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS2xS23b
public import FormalResearch.ModularBootstrap.Spin.SpinS4CalAdjoint
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Section 5.1 (`s4:5.1`) Closed-Strip Contour Shift & Kernel Helpers

Provides `spinCalFacC`, `norm_spinCalFacC_le`, `spinGcal_eq_mul_spinGeff`,
`spinGcal_ofReal`, `spinGcal_neg`, `spinGcal_differentiableOn_strip`,
`spinGcal_strip_bound_exists`, and `gaussian_contour_shift'` on `{b : ℂ | |b.im| ≤ 1 / 2}`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable def spinCalFacC (b : ℂ) : ℂ :=
  Complex.exp (-((spinAlpha1 : ℂ) * (b ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) / (2 * (xiStar : ℂ))) -
    (b ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) ^ 2)

lemma spinCalFacC_neg (b : ℂ) : spinCalFacC (-b) = spinCalFacC b := by
  unfold spinCalFacC; simp [neg_sq]

noncomputable def spinCalFacStripConst : ℝ :=
  Real.exp ((|spinAlpha1 / (2 * xiStar)| + 1) ^ 2 / 4 + 1 / 4 + xiStar ^ 2)

lemma spinCalFacStripConst_pos : 0 < spinCalFacStripConst := Real.exp_pos _

lemma norm_spinCalFacC_le {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖spinCalFacC b‖ ≤ spinCalFacStripConst := by
  unfold spinCalFacC spinCalFacStripConst
  rw [Complex.norm_exp, Real.exp_le_exp]
  set z : ℂ := b ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)
  have hz_re : z.re = b.re ^ 2 - b.im ^ 2 - xiStar ^ 2 := by
    dsimp [z]; simp [sq, Complex.mul_re]
  have hz_im : z.im = 2 * b.re * b.im := by
    dsimp [z]; simp [sq, Complex.mul_im]; ring
  have hb_im_sq : b.im ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg b.im) hb 2
    rw [sq_abs] at h; linarith
  have hz_im_sq : z.im ^ 2 ≤ b.re ^ 2 := by
    rw [hz_im]; nlinarith [sq_nonneg b.re]
  have hbre_le : b.re ^ 2 ≤ |z.re| + 1 / 4 + xiStar ^ 2 := by
    linarith [le_abs_self z.re, neg_le_abs z.re, sq_nonneg b.im]
  have h1 : (-((spinAlpha1 : ℂ) * z / (2 * (xiStar : ℂ))) - z ^ 2).re =
      -(spinAlpha1 / (2 * xiStar)) * z.re - (z.re ^ 2 - z.im ^ 2) := by
    have hdiv : ((spinAlpha1 : ℂ) * z / (2 * (xiStar : ℂ))) =
        (((spinAlpha1 / (2 * xiStar) : ℝ) : ℂ) * z) := by push_cast; ring
    rw [Complex.sub_re, Complex.neg_re, hdiv, Complex.re_ofReal_mul, sq, Complex.mul_re]
    ring
  have h2 : -(spinAlpha1 / (2 * xiStar)) * z.re ≤ |spinAlpha1 / (2 * xiStar)| * |z.re| := by
    calc -(spinAlpha1 / (2 * xiStar)) * z.re ≤ |-(spinAlpha1 / (2 * xiStar)) * z.re| := le_abs_self _
      _ = |spinAlpha1 / (2 * xiStar)| * |z.re| := by rw [abs_mul, abs_neg]
  have hcomp : (|spinAlpha1 / (2 * xiStar)| + 1) * |z.re| - |z.re| ^ 2 ≤
      (|spinAlpha1 / (2 * xiStar)| + 1) ^ 2 / 4 := by
    linarith [sq_nonneg (|z.re| - (|spinAlpha1 / (2 * xiStar)| + 1) / 2)]
  rw [h1]
  linarith [sq_abs z.re]

lemma spinGcal_eq_mul_spinGeff (a : ℝ) (Φ : ℝ × ℝ → ℝ) (b : ℂ) :
    spinGcal a Φ b =
      ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0 : ℝ) : ℂ) *
        spinCalFacC b * spinGeff a Φ b := by
  unfold spinGcal spinGeff
  have hhb : ∀ d : ℝ, spinHbCal b d * spinGC a Φ (b + (d : ℂ)) (b - (d : ℂ)) =
      spinCalFacC b * (spinHb b d * spinGC a Φ (b + (d : ℂ)) (b - (d : ℂ))) := fun d => by
    unfold spinHbCal spinCalFacC; ring
  simp_rw [hhb, integral_const_mul]
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsig : (spinSigma0 : ℂ) ≠ 0 := by unfold spinSigma0; norm_num
  push_cast; field_simp [hpi, hsig]

lemma spinGcal_im_ofReal {a : ℝ} (ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (b : ℝ) :
    (spinGcal a Φ (b : ℂ)).im = 0 := by
  unfold spinGcal
  have hreal_int : ∀ d : ℝ,
      spinHbCal (b : ℂ) d * spinGC a Φ ((b : ℂ) + (d : ℂ)) ((b : ℂ) - (d : ℂ)) =
        ((spinHbCalReal b d * spinG a Φ (b + d) (b - d) : ℝ) : ℂ) := fun d => by
    have hL : (b : ℂ) + (d : ℂ) = ((b + d : ℝ) : ℂ) := by push_cast; rfl
    have hR : (b : ℂ) - (d : ℂ) = ((b - d : ℝ) : ℂ) := by push_cast; rfl
    rw [spinHbCal_ofReal, hL, hR, spinGC_ofReal_eq_spinG ha hΦ]; push_cast; ring
  simp_rw [hreal_int, ← Complex.coe_algebraMap, integral_ofReal]
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_mul, Complex.ofReal_im]

lemma spinGcal_neg {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) (b : ℂ) :
    spinGcal ((c - 1) / 12) Φ (-b) = spinGcal ((c - 1) / 12) Φ b := by
  obtain ⟨_, _, hS23⟩ := spinS23
  have heven := (hS23 hc hΦ).1 b
  rw [spinGcal_eq_mul_spinGeff, spinGcal_eq_mul_spinGeff, spinCalFacC_neg, heven]

lemma spinGcal_differentiableOn_strip {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    DifferentiableOn ℂ (spinGcal ((c - 1) / 12) Φ) (spinStrip (1 / 2)) := by
  obtain ⟨_, _, hS23⟩ := spinS23
  have hdiff := (hS23 hc hΦ).2.1
  have heq : spinGcal ((c - 1) / 12) Φ = fun b : ℂ =>
      ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0 : ℝ) : ℂ) *
        spinCalFacC b * spinGeff ((c - 1) / 12) Φ b :=
    funext (spinGcal_eq_mul_spinGeff _ _)
  rw [heq]
  have hfac_diff : Differentiable ℂ (fun b : ℂ =>
      ((4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0 : ℝ) : ℂ) * spinCalFacC b) := by
    unfold spinCalFacC; fun_prop
  exact hfac_diff.differentiableOn.mul hdiff

lemma spinGcal_strip_bound_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ {c : ℝ}, 40 ≤ c →
      ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass ((c - 1) / 12) Φ →
        ∀ b ∈ spinStrip (1 / 2), ‖spinGcal ((c - 1) / 12) Φ b‖ ≤ C * (c - 1) ^ 2 * spinM2 ((c - 1) / 12) Φ := by
  obtain ⟨C0, hC0, hS23⟩ := spinS23
  let K : ℝ := 4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0 * spinCalFacStripConst
  have hK_pos : 0 < K := by
    have hF : 0 < spinCalF xiStar := by
      unfold spinCalF; have := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_gt_three, xiStar_pos] : -4 * π * xiStar < 0); linarith
    have hs0 : 0 < spinSigma0 := by unfold spinSigma0; positivity
    have hsc := spinCalFacStripConst_pos
    positivity
  refine ⟨K * C0, mul_pos hK_pos hC0, fun {c} hc {Φ} hΦ b hb => ?_⟩
  have hgeff := (hS23 hc hΦ).2.2.1 b hb
  rw [spinGcal_eq_mul_spinGeff, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
    have hs0 : 0 ≤ spinSigma0 := by unfold spinSigma0; positivity
    positivity)]
  have h1 : ‖spinCalFacC b‖ ≤ spinCalFacStripConst := norm_spinCalFacC_le hb.le
  calc (4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0) * ‖spinCalFacC b‖ *
        ‖spinGeff ((c - 1) / 12) Φ b‖
      ≤ (4 * spinCalF xiStar ^ 2 * Real.sqrt π * spinSigma0) * spinCalFacStripConst *
          (C0 * (c - 1) ^ 2 * spinM2 ((c - 1) / 12) Φ) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by unfold spinSigma0; positivity)) hgeff
          (norm_nonneg _) (by unfold spinSigma0; have := spinCalFacStripConst_pos; positivity)
    _ = K * C0 * (c - 1) ^ 2 * spinM2 ((c - 1) / 12) Φ := by dsimp [K]; ring

lemma norm_complex_sinh_le' (w : ℂ) : ‖Complex.sinh w‖ ≤ Real.cosh w.re := by
  have hsin_eq : Complex.sinh w =
      (Real.sinh w.re * Real.cos w.im : ℝ) + (Real.cosh w.re * Real.sin w.im : ℝ) * I := by
    apply Complex.ext
    · simp [Complex.sinh, Complex.exp_re, Real.sinh_eq, Real.cos_neg, ← Complex.ofReal_cos]; ring
    · simp [Complex.sinh, Complex.exp_im, Real.cosh_eq, Real.sin_neg, ← Complex.ofReal_sin,
        ← Complex.ofReal_exp]; ring
  have hsq : ‖Complex.sinh w‖ ^ 2 ≤ Real.cosh w.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hsin_eq, Complex.normSq_add_mul_I]
    have hch : Real.cosh w.re ^ 2 - Real.sinh w.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
    have hcs : Real.cos w.im ^ 2 + Real.sin w.im ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    nlinarith [sq_nonneg (Real.sinh w.re), sq_nonneg (Real.cosh w.re)]
  exact le_of_sq_le_sq hsq (Real.cosh_pos _).le

lemma complex_tanh_bound_strip' {w : ℂ} (hw : |w.im| ≤ 5 / 4) :
    Complex.cosh w ≠ 0 ∧ ‖Complex.tanh w‖ ≤ (Real.cos (5 / 4))⁻¹ := by
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hcos_ge : Real.cos (5 / 4) ≤ Real.cos w.im := by
    rw [← Real.cos_abs w.im]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hw
  have hcos_sq : Real.cos (5 / 4) ^ 2 ≤ Real.cos w.im ^ 2 :=
    pow_le_pow_left₀ hcos_pos.le hcos_ge 2
  have hcos_eq : Complex.cosh w =
      (Real.cosh w.re * Real.cos w.im : ℝ) + (Real.sinh w.re * Real.sin w.im : ℝ) * I := by
    apply Complex.ext
    · simp [Complex.cosh, Complex.exp_re, Real.cosh_eq, Real.cos_neg, -Complex.ofReal_cos]; ring
    · simp [Complex.cosh, Complex.exp_im, Real.sinh_eq, Real.sin_neg, -Complex.ofReal_sin,
        ← Complex.ofReal_exp]; ring
  have hnorm_sq : ‖Complex.cosh w‖ ^ 2 = Real.sinh w.re ^ 2 + Real.cos w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hcos_eq, Complex.normSq_add_mul_I]
    have hch : Real.cosh w.re ^ 2 = Real.sinh w.re ^ 2 + 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq w.re]
    have hsc : Real.sin w.im ^ 2 + Real.cos w.im ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    nlinarith [sq_nonneg (Real.cos w.im), sq_nonneg (Real.sinh w.re)]
  have hch_ge : Real.cos (5 / 4) * Real.cosh w.re ≤ ‖Complex.cosh w‖ := by
    have hsq : (Real.cos (5 / 4) * Real.cosh w.re) ^ 2 ≤ ‖Complex.cosh w‖ ^ 2 := by
      have hch : Real.cosh w.re ^ 2 = Real.sinh w.re ^ 2 + 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq w.re]
      calc (Real.cos (5 / 4) * Real.cosh w.re) ^ 2
          = Real.cos (5 / 4) ^ 2 * (Real.sinh w.re ^ 2 + 1) := by rw [mul_pow, hch]
        _ = Real.cos (5 / 4) ^ 2 * Real.sinh w.re ^ 2 + Real.cos (5 / 4) ^ 2 := by ring
        _ ≤ 1 * Real.sinh w.re ^ 2 + Real.cos w.im ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_right (Real.cos_sq_le_one _) (sq_nonneg _)) hcos_sq
        _ = ‖Complex.cosh w‖ ^ 2 := by rw [one_mul, hnorm_sq]
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have hch_ne : Complex.cosh w ≠ 0 := norm_ne_zero_iff.mp (by have := Real.cosh_pos w.re; nlinarith)
  refine ⟨hch_ne, ?_⟩
  rw [Complex.tanh_eq_sinh_div_cosh, norm_div]
  calc ‖Complex.sinh w‖ / ‖Complex.cosh w‖
      ≤ Real.cosh w.re / (Real.cos (5 / 4) * Real.cosh w.re) :=
        div_le_div₀ (Real.cosh_pos _).le (norm_complex_sinh_le' w)
          (mul_pos hcos_pos (Real.cosh_pos _)) hch_ge
    _ = (Real.cos (5 / 4))⁻¹ := by field_simp [hcos_pos.ne', (Real.cosh_pos w.re).ne']

lemma spinHb_norm_le_closed {b : ℂ} (hb : |b.im| ≤ 1 / 2) (d : ℝ) :
    ‖spinHb b d‖ ≤ 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 *
      (Real.cos (5 / 4))⁻¹ ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
  have hb_re : 3 / 4 ≤ (1 + b ^ 2).re := by
    simp only [Complex.add_re, Complex.one_re, sq, Complex.mul_re]
    nlinarith [sq_nonneg b.re, sq_abs b.im, pow_le_pow_left₀ (abs_nonneg b.im) hb 2]
  have hb_norm : 3 / 4 ≤ ‖1 + b ^ 2‖ := hb_re.trans (Complex.re_le_norm _)
  have hw1 : |((b + (d : ℂ)) / 2).im| ≤ 5 / 4 := by
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im, add_zero]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hw2 : |((b - (d : ℂ)) / 2).im| ≤ 5 / 4 := by
    simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have ht1 := (complex_tanh_bound_strip' hw1).2
  have ht2 := (complex_tanh_bound_strip' hw2).2
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  have hinv : ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ ≤ (4 / 3) * (1 + xiStar ^ 2) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc (1 + xiStar ^ 2) / ‖1 + b ^ 2‖ ≤ (1 + xiStar ^ 2) / (3 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hb_norm
      _ = (4 / 3) * (1 + xiStar ^ 2) := by ring
  unfold spinHb
  rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have h1 : ‖Complex.tanh ((b + (d : ℂ)) / 2)‖ ^ 2 ≤ (Real.cos (5 / 4))⁻¹ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ht1 2
  have h2 : ‖Complex.tanh ((b - (d : ℂ)) / 2)‖ ^ 2 ≤ (Real.cos (5 / 4))⁻¹ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ht2 2
  calc ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ *
        (‖Complex.tanh ((b + (d : ℂ)) / 2)‖ ^ 2 * ‖Complex.tanh ((b - (d : ℂ)) / 2)‖ ^ 2) /
        Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2))
      ≤ ((4 / 3) * (1 + xiStar ^ 2)) * ((Real.cos (5 / 4))⁻¹ ^ 2 * (Real.cos (5 / 4))⁻¹ ^ 2) /
          Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul hinv (mul_le_mul h1 h2 (by positivity) (by positivity))
            (by positivity) (by positivity)) hxi.le) (Real.exp_pos _).le
    _ ≤ _ := by
        have h43 : (4 / 3 : ℝ) ≤ 4 := by norm_num
        have hsq4 : (Real.cos (5 / 4))⁻¹ ^ 2 * (Real.cos (5 / 4))⁻¹ ^ 2 = (Real.cos (5 / 4))⁻¹ ^ 4 := by ring
        rw [hsq4]
        calc ((4 / 3) * (1 + xiStar ^ 2)) * (Real.cos (5 / 4))⁻¹ ^ 4 /
              Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2))
            ≤ (4 * (1 + xiStar ^ 2)) * (Real.cos (5 / 4))⁻¹ ^ 4 /
                Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by gcongr
          _ = 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
                Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by ring

noncomputable def spinHbC' (b w : ℂ) : ℂ :=
  ((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2) *
    (Complex.tanh ((b + w) / 2) ^ 2 * Complex.tanh ((b - w) / 2) ^ 2) /
    ((Real.tanh (xiStar / 2) ^ 4 : ℝ) : ℂ) *
    Complex.exp (-(w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)))

lemma spinHbC'_ofReal (b : ℂ) (d : ℝ) : spinHbC' b (d : ℂ) = spinHb b d := by
  unfold spinHbC' spinHb; congr 2; push_cast; ring

noncomputable def spinHbWideConst' : ℝ :=
  (4 / 3) * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
    Real.exp (4 / spinSigma0 ^ 2)

lemma spinHbWideConst'_pos : 0 < spinHbWideConst' := by
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  unfold spinHbWideConst'; positivity

lemma spinHbC'_closed_strip_bound_and_diff {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    (∀ w : ℂ, |w.im| ≤ 2 → DifferentiableAt ℂ (spinHbC' b) w) ∧
      (∀ w : ℂ, |w.im| ≤ 2 →
        ‖spinHbC' b w‖ ≤ spinHbWideConst' * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2))) := by
  have hb_re : 3 / 4 ≤ (1 + b ^ 2).re := by
    simp only [Complex.add_re, Complex.one_re, sq, Complex.mul_re]
    nlinarith [sq_nonneg b.re, sq_abs b.im, pow_le_pow_left₀ (abs_nonneg b.im) hb 2]
  have hb_norm : 3 / 4 ≤ ‖1 + b ^ 2‖ := hb_re.trans (Complex.re_le_norm _)
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hw_im_bd : ∀ w : ℂ, |w.im| ≤ 2 →
      |((b + w) / 2).im| ≤ 5 / 4 ∧ |((b - w) / 2).im| ≤ 5 / 4 := fun w hw => by
    constructor
    · simp only [Complex.div_ofNat_im, Complex.add_im]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_add_le b.im w.im]
    · simp only [Complex.div_ofNat_im, Complex.sub_im]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_sub b.im w.im]
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨hw1, hw2⟩ := hw_im_bd w hw
    have hch1 := (complex_tanh_bound_strip' hw1).1
    have hch2 := (complex_tanh_bound_strip' hw2).1
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => Complex.tanh ((b + z) / 2)) w := by
      have hfun : (fun z : ℂ => Complex.tanh ((b + z) / 2)) =
          (fun z : ℂ => Complex.sinh ((b + z) / 2) / Complex.cosh ((b + z) / 2)) := by
        ext z; exact Complex.tanh_eq_sinh_div_cosh _
      rw [hfun]; exact DifferentiableAt.div (by fun_prop) (by fun_prop) hch1
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.tanh ((b - z) / 2)) w := by
      have hfun : (fun z : ℂ => Complex.tanh ((b - z) / 2)) =
          (fun z : ℂ => Complex.sinh ((b - z) / 2) / Complex.cosh ((b - z) / 2)) := by
        ext z; exact Complex.tanh_eq_sinh_div_cosh _
      rw [hfun]; exact DifferentiableAt.div (by fun_prop) (by fun_prop) hch2
    unfold spinHbC'
    exact (((((hd1.pow 2).mul (hd2.pow 2)).const_mul _).div_const _).mul (by fun_prop))
  · obtain ⟨hw1, hw2⟩ := hw_im_bd w hw
    have ht1 := (complex_tanh_bound_strip' hw1).2
    have ht2 := (complex_tanh_bound_strip' hw2).2
    have hinv : ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ ≤ (4 / 3) * (1 + xiStar ^ 2) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (1 + xiStar ^ 2) / ‖1 + b ^ 2‖ ≤ (1 + xiStar ^ 2) / (3 / 4) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hb_norm
        _ = (4 / 3) * (1 + xiStar ^ 2) := by ring
    have hexp_bd : ‖Complex.exp (-(w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)))‖ ≤
        Real.exp (4 / spinSigma0 ^ 2) * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := by
      rw [Complex.norm_exp, Complex.neg_re]
      have hre : (w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)).re = (w.re ^ 2 - w.im ^ 2) / spinSigma0 ^ 2 := by
        rw [Complex.div_ofReal_re, sq, Complex.mul_re]; ring
      rw [hre, ← Real.exp_add, Real.exp_le_exp]
      have him2 : w.im ^ 2 ≤ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg w.im) hw 2; rw [sq_abs] at this; linarith
      have hsig : 0 < spinSigma0 ^ 2 := by unfold spinSigma0; positivity
      rw [show 4 / spinSigma0 ^ 2 + -(w.re ^ 2 / spinSigma0 ^ 2) = -((w.re ^ 2 - 4) / spinSigma0 ^ 2) by ring]
      exact neg_le_neg (div_le_div_of_nonneg_right (by linarith) hsig.le)
    unfold spinHbC' spinHbWideConst'
    rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi]
    have h1 : ‖Complex.tanh ((b + w) / 2)‖ ^ 2 ≤ (Real.cos (5 / 4))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht1 2
    have h2 : ‖Complex.tanh ((b - w) / 2)‖ ^ 2 ≤ (Real.cos (5 / 4))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht2 2
    calc ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ *
          (‖Complex.tanh ((b + w) / 2)‖ ^ 2 * ‖Complex.tanh ((b - w) / 2)‖ ^ 2) /
          Real.tanh (xiStar / 2) ^ 4 * ‖Complex.exp (-(w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)))‖
        ≤ (4 / 3 * (1 + xiStar ^ 2)) * ((Real.cos (5 / 4))⁻¹ ^ 2 * (Real.cos (5 / 4))⁻¹ ^ 2) /
            Real.tanh (xiStar / 2) ^ 4 *
            (Real.exp (4 / spinSigma0 ^ 2) * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2))) := by
          refine mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul hinv
            (mul_le_mul h1 h2 (by positivity) (by positivity))
            (by positivity) (by positivity)) hxi.le) hexp_bd (norm_nonneg _) (by positivity)
      _ = ((4 / 3) * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
            Real.exp (4 / spinSigma0 ^ 2)) * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := by ring

lemma gaussian_contour_shift' {b : ℂ} (hb : |b.im| ≤ 1 / 2) (β ω σ : ℝ)
    (hσ : |σ| ≤ 1) :
    ∫ d : ℝ, spinHb b d * Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * (d : ℂ))) =
      ∫ t : ℝ, spinHbC' b ((t : ℂ) + (2 * σ : ℝ) * I) *
        Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I))) := by
  obtain ⟨hdiff, hbd⟩ := spinHbC'_closed_strip_bound_and_diff hb
  let f : ℂ → ℂ := fun w => spinHbC' b w * Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * w))
  have hf_diff : ∀ w : ℂ, |w.im| ≤ 2 → DifferentiableAt ℂ f w := fun w hw =>
    (hdiff w hw).mul (by fun_prop)
  have hf_bd : ∀ w : ℂ, |w.im| ≤ 2 →
      ‖f w‖ ≤ spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
        Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := fun w hw => by
    have him : (I * ((β : ℂ) * b + (ω : ℂ) * w)).re = -(β * b.im + ω * w.im) := by
      simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have hexp_bd : ‖Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * w))‖ ≤
        Real.exp (|β| / 2 + 2 * |ω|) := by
      rw [Complex.norm_exp, him, Real.exp_le_exp]
      have h1 : -(β * b.im) ≤ |β| / 2 := by
        calc -(β * b.im) ≤ |β * b.im| := neg_le_abs _
          _ = |β| * |b.im| := abs_mul _ _
          _ ≤ |β| * (1 / 2) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = |β| / 2 := by ring
      have h2 : -(ω * w.im) ≤ 2 * |ω| := by
        calc -(ω * w.im) ≤ |ω * w.im| := neg_le_abs _
          _ = |ω| * |w.im| := abs_mul _ _
          _ ≤ |ω| * 2 := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
          _ = 2 * |ω| := by ring
      linarith
    rw [norm_mul]
    calc ‖spinHbC' b w‖ * ‖Complex.exp _‖
        ≤ (spinHbWideConst' * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2))) *
            Real.exp (|β| / 2 + 2 * |ω|) :=
          mul_le_mul (hbd w hw) hexp_bd (norm_nonneg _) (by have := spinHbWideConst'_pos; positivity)
      _ = spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
            Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := by ring
  have hgauss_int : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  have hf_int0 : Integrable (fun t : ℝ => f (t : ℂ)) volume := by
    refine (hgauss_int.const_mul (spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|))).mono' ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun t : ℝ =>
        (hf_diff (t : ℂ) (by norm_num [Complex.ofReal_im])).continuousAt.comp Complex.continuous_ofReal.continuousAt).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by simpa using hf_bd (t : ℂ) (by norm_num [Complex.ofReal_im])
  have hf_int1 : Integrable (fun t : ℝ => f ((t : ℂ) + (2 * σ : ℝ) * I)) volume := by
    refine (hgauss_int.const_mul (spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|))).mono' ?_ ?_
    · refine (continuous_iff_continuousAt.mpr fun t => ?_).aestronglyMeasurable
      refine (hf_diff _ ?_).continuousAt.comp (by fun_prop)
      simp [abs_mul]; linarith
    · exact Eventually.of_forall fun t => by
        have him : |((t : ℂ) + (2 * σ : ℝ) * I).im| ≤ 2 := by simp [abs_mul]; linarith
        simpa using hf_bd _ him
  have hcauchy : ∀ R : ℕ,
      (∫ t in -(R : ℝ)..(R : ℝ), f (t : ℂ)) -
      (∫ t in -(R : ℝ)..(R : ℝ), f ((t : ℂ) + (2 * σ : ℝ) * I)) +
      I • (∫ y in (0 : ℝ)..(2 * σ), f ((R : ℂ) + (y : ℂ) * I)) -
      I • (∫ y in (0 : ℝ)..(2 * σ), f ((-(R : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
    intro R
    have hrect : DifferentiableOn ℂ f (Set.uIcc (-(R : ℝ)) (R : ℝ) ×ℂ Set.uIcc (0 : ℝ) (2 * σ)) := by
      intro w hw
      have hw_im : w.im ∈ Set.uIcc (0 : ℝ) (2 * σ) := hw.2
      have hw_le : |w.im| ≤ 2 := by
        rcases le_or_gt 0 (2 * σ) with hs | hs
        · rw [Set.uIcc_of_le hs] at hw_im
          exact abs_le.mpr ⟨by linarith [hw_im.1], by linarith [hw_im.2, abs_le.mp hσ]⟩
        · rw [Set.uIcc_of_ge hs.le] at hw_im
          exact abs_le.mpr ⟨by linarith [hw_im.1, abs_le.mp hσ], by linarith [hw_im.2]⟩
      exact (hf_diff w hw_le).differentiableWithinAt
    simpa using Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (-(R : ℝ) : ℂ) ((R : ℝ) + (2 * σ : ℝ) * I) (by simpa using hrect)
  have htend0 : Filter.Tendsto (fun R : ℕ => ∫ t in -(R : ℝ)..(R : ℝ), f (t : ℂ))
      Filter.atTop (𝓝 (∫ t : ℝ, f (t : ℂ))) :=
    (intervalIntegral_tendsto_integral hf_int0 tendsto_neg_atTop_atBot tendsto_id).comp
      tendsto_natCast_atTop_atTop
  have htend1 : Filter.Tendsto (fun R : ℕ => ∫ t in -(R : ℝ)..(R : ℝ), f ((t : ℂ) + (2 * σ : ℝ) * I))
      Filter.atTop (𝓝 (∫ t : ℝ, f ((t : ℂ) + (2 * σ : ℝ) * I))) :=
    (intervalIntegral_tendsto_integral hf_int1 tendsto_neg_atTop_atBot tendsto_id).comp
      tendsto_natCast_atTop_atTop
  have hside_tend : ∀ (s : ℝ) (hs : |s| = 1),
      Filter.Tendsto (fun R : ℕ => I • ∫ y in (0 : ℝ)..(2 * σ), f (((s * R : ℝ) : ℂ) + (y : ℂ) * I))
        Filter.atTop (𝓝 0) := by
    intro s hs
    have hnorm_le : ∀ R : ℕ, ‖I • ∫ y in (0 : ℝ)..(2 * σ), f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        2 * (spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|)) *
          Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
      intro R
      rw [norm_smul, Complex.norm_I, one_mul]
      have hbd_y : ∀ y ∈ Set.uIcc (0 : ℝ) (2 * σ),
          ‖f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
            spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
              Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
        intro y hy
        have hy_le : |y| ≤ 2 := by
          rcases le_or_gt 0 (2 * σ) with h2 | h2
          · rw [Set.uIcc_of_le h2] at hy
            exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2, abs_le.mp hσ]⟩
          · rw [Set.uIcc_of_ge h2.le] at hy
            exact abs_le.mpr ⟨by linarith [hy.1, abs_le.mp hσ], by linarith [hy.2]⟩
        have him : |(((s * R : ℝ) : ℂ) + (y : ℂ) * I).im| ≤ 2 := by simpa using hy_le
        have hre : (((s * R : ℝ) : ℂ) + (y : ℂ) * I).re ^ 2 = (R : ℝ) ^ 2 := by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im]
          calc (s * ↑R + (y * 0 - 0 * 1)) ^ 2 = s ^ 2 * (R : ℝ) ^ 2 := by ring
            _ = |s| ^ 2 * (R : ℝ) ^ 2 := by rw [sq_abs]
            _ = (R : ℝ) ^ 2 := by rw [hs, one_pow, one_mul]
        calc ‖f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖
            ≤ spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
                Real.exp (-((((s * R : ℝ) : ℂ) + (y : ℂ) * I).re ^ 2 / spinSigma0 ^ 2)) :=
              hf_bd _ him
          _ = spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
                Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by rw [hre]
      calc ‖∫ y in (0 : ℝ)..(2 * σ), f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ (spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
              Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2))) * |2 * σ - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hbd_y y (Set.uIoc_subset_uIcc hy)
        _ ≤ 2 * (spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|)) *
              Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
            have h2s : |2 * σ - 0| ≤ 2 := by rw [sub_zero, abs_mul]; norm_num; linarith
            have hC_nn : 0 ≤ spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
                Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
              have := spinHbWideConst'_pos; positivity
            calc _ ≤ (spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|) *
                  Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2))) * 2 :=
                  mul_le_mul_of_nonneg_left h2s hC_nn
              _ = _ := by ring
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hnorm_le ?_)
    have hpow_lim : Filter.Tendsto (fun R : ℕ => -((R : ℝ) ^ 2 / spinSigma0 ^ 2))
        Filter.atTop Filter.atBot := by
      have hsq : Filter.Tendsto (fun R : ℕ => (R : ℝ) ^ 2) Filter.atTop Filter.atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
      have hdiv : Filter.Tendsto (fun R : ℕ => (R : ℝ) ^ 2 * (spinSigma0 ^ 2)⁻¹)
          Filter.atTop Filter.atTop :=
        hsq.atTop_mul_const (by unfold spinSigma0; positivity)
      exact (Filter.tendsto_neg_atTop_atBot.comp hdiv).congr fun _ => by simp [div_eq_mul_inv]
    simpa using (Real.tendsto_exp_atBot.comp hpow_lim).const_mul (2 * (spinHbWideConst' * Real.exp (|β| / 2 + 2 * |ω|)))
  have hdiff_tend := (((htend0.sub htend1).add (hside_tend 1 (by norm_num))).sub
    (hside_tend (-1) (by norm_num)))
  have hzero_seq : (fun R : ℕ =>
      (∫ t in -(R : ℝ)..(R : ℝ), f (t : ℂ)) -
      (∫ t in -(R : ℝ)..(R : ℝ), f ((t : ℂ) + (2 * σ : ℝ) * I)) +
      I • (∫ y in (0 : ℝ)..(2 * σ), f (((1 * (R : ℝ) : ℝ) : ℂ) + (y : ℂ) * I)) -
      I • (∫ y in (0 : ℝ)..(2 * σ), f ((((-1 : ℝ) * (R : ℝ) : ℝ) : ℂ) + (y : ℂ) * I))) = fun _ => 0 := by
    ext R; simpa [one_mul, neg_one_mul] using hcauchy R
  rw [hzero_seq] at hdiff_tend
  have heq : (∫ t : ℝ, f (t : ℂ)) - (∫ t : ℝ, f ((t : ℂ) + (2 * σ : ℝ) * I)) + 0 - 0 = 0 :=
    tendsto_nhds_unique hdiff_tend tendsto_const_nhds
  exact sub_eq_zero.mp (by simpa [f, spinHbC'_ofReal] using heq)

end FormalResearch.ModularBootstrap.Spin
