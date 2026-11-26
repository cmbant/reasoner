module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFar
public import FormalResearch.SignUncertainty.CtDualId

/-!
# `ct:boas` Step 4 (phase-free core): Gaussian-windowed Fourier coefficient and its contour shift

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 4.  Phase-free: only `h ∈ L¹(ℝ)`,
the transform `Fh h z = ∫ h(s) e^{2πizs} ds` and a holomorphic extension `H` of `Fh h` to a horizontal strip
`0 ≤ Im z ≤ a` are used.

* `windowCoeff_gauss_eq` (convolution identity): for `g(x) = G_W(x - x₀) h(x)`,
  `ĝ(ν) = ∫_ℝ e^{-2π²W²ω² - 2πiωx₀} Fh h(ω - ν) dω`;
* `windowCoeff_gauss_shift` (contour shift): if `H` is continuous on `0 ≤ Im z ≤ a`, holomorphic inside, bounded, and
  equals `Fh h` on `ℝ`, then the same integral may be taken along `Im ω = a`:
  `ĝ(ν) = ∫_ℝ e^{-2π²W²(ω+ia)² - 2πi(ω+ia)x₀} H(ω + ia - ν) dω`;
* `windowCoeff_gauss_shift_bound`: hence `‖ĝ(ν)‖ ≤ ∫ e^{-2π²W²(ω²-a²) + 2πax₀} ‖H(ω+ia-ν)‖ dω`.

In the paper's variables `ζ = σ + iτ`, `z = icζ/(2π)` (so `Im z = cσ/(2π)`), and `H(z) = ĥ(-2πiz/c)`.
**Proved**, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtBoasWindow

/-- Convolution identity for the single Gaussian window (2π convention). -/
theorem windowCoeff_gauss_eq {h : ℝ → ℝ} (hh : Integrable h) {W : ℝ} (hW : 0 < W) (x₀ ν : ℝ) :
    ∫ x : ℝ, (gaussK W (x - x₀) : ℂ) * (h x : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * x)) =
      ∫ ω : ℝ, Complex.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2 - 2 * π * Complex.I * ω * x₀) *
        Fh h ((ω - ν : ℝ) : ℂ) := by
  set b : ℝ := 2 * π ^ 2 * W ^ 2 with hb
  have hb0 : 0 < b := by positivity
  set Φ : ℝ → ℝ → ℂ := fun x ω => Complex.exp (-b * ω ^ 2 - 2 * π * Complex.I * ω * x₀) *
      ((h x : ℂ) * Complex.exp (2 * π * Complex.I * ((ω - ν : ℝ) : ℂ) * x)) with hΦ
  have h1 : ∀ x : ℝ, (gaussK W (x - x₀) : ℂ) * (h x : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * x)) =
      ∫ ω, Φ x ω := by
    intro x
    rw [← gauss_fourier hW (x - x₀), ← integral_mul_const, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hΦ]
    have : Complex.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2 + 2 * π * Complex.I * ((x - x₀ : ℝ) : ℂ) * ω) *
        ((h x : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * x))) =
        Complex.exp (-b * ω ^ 2 - 2 * π * Complex.I * ω * x₀) *
        ((h x : ℂ) * Complex.exp (2 * π * Complex.I * ((ω - ν : ℝ) : ℂ) * x)) := by
      have e1 : Complex.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2 + 2 * π * Complex.I * ((x - x₀ : ℝ) : ℂ) * ω) =
          Complex.exp (-b * ω ^ 2 - 2 * π * Complex.I * ω * x₀) * Complex.exp (2 * π * Complex.I * ω * x) := by
        rw [← Complex.exp_add]; congr 1; push_cast; rw [hb]; push_cast; ring
      have e2 : Complex.exp (2 * π * Complex.I * ((ω - ν : ℝ) : ℂ) * x) =
          Complex.exp (2 * π * Complex.I * ω * x) * Complex.exp (-(2 * π * Complex.I * ν * x)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [e1, e2]; ring
    rw [mul_assoc]; exact this
  simp_rw [h1]
  have hint : Integrable (Function.uncurry Φ) (volume.prod volume) := by
    have hb' : Integrable (fun ω : ℝ => Real.exp (-b * ω ^ 2)) := integrable_exp_neg_mul_sq hb0
    have hg : Integrable (fun p : ℝ × ℝ => ‖h p.1‖ * Real.exp (-b * p.2 ^ 2)) (volume.prod volume) :=
      hh.norm.mul_prod hb'
    refine Integrable.mono' hg ?_ (ae_of_all _ fun p => ?_)
    · have m2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (h p.1 : ℂ)) (volume.prod volume) :=
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable).comp_fst
      have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          Complex.exp (-b * p.2 ^ 2 - 2 * π * Complex.I * p.2 * x₀)) (volume.prod volume) :=
        (by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (-b * p.2 ^ 2 - 2 * π * Complex.I * p.2 * x₀)).aestronglyMeasurable
      have m3 : AEStronglyMeasurable (fun p : ℝ × ℝ => Complex.exp (2 * π * Complex.I * ((p.2 - ν : ℝ) : ℂ) * p.1))
          (volume.prod volume) :=
        (by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (2 * π * Complex.I * ((p.2 - ν : ℝ) : ℂ) * p.1)).aestronglyMeasurable
      exact m1.mul (m2.mul m3)
    · obtain ⟨x, ω⟩ := p
      simp only [hΦ, Function.uncurry]
      rw [norm_mul, norm_mul, Complex.norm_real]
      have he : ‖Complex.exp (2 * π * Complex.I * ((ω - ν : ℝ) : ℂ) * x)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      have he2 : ‖Complex.exp (-b * ω ^ 2 - 2 * π * Complex.I * ω * x₀)‖ = Real.exp (-b * ω ^ 2) := by
        rw [Complex.norm_exp]; congr 1; simp
        left; rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
      rw [he, he2, mul_one]; ring_nf; exact le_refl _
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [hΦ]
  rw [integral_const_mul]
  unfold Fh
  have hbc : (-(b : ℂ)) = -(2 * (π : ℂ) ^ 2 * (W : ℂ) ^ 2) := by rw [hb]; push_cast; ring
  rw [hbc]


open FormalResearch.SignUncertainty.CtOuter in
/-- Contour shift for the Gaussian-windowed coefficient (phase-free).  If `H` extends `Fh h` continuously to
`0 ≤ Im z ≤ a`, holomorphically inside, and boundedly, then
`ĝ(ν) = ∫_ℝ e^{-2π²W²(ω+ia)² - 2πi(ω+ia)x₀} H(ω + ia - ν) dω`. -/
theorem windowCoeff_gauss_shift {h : ℝ → ℝ} (hh : Integrable h) {W : ℝ} (hW : 0 < W) (x₀ ν a : ℝ)
    (ha : 0 < a) {H : ℂ → ℂ} (hH0 : ∀ x : ℝ, H x = Fh h x)
    (hHc : ContinuousOn H {z : ℂ | 0 ≤ z.im ∧ z.im ≤ a})
    (hHd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im ∧ z.im < a}) {M : ℝ}
    (hM : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ a → ‖H z‖ ≤ M) :
    ∫ x : ℝ, (gaussK W (x - x₀) : ℂ) * (h x : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * x)) =
      ∫ ω : ℝ, Complex.exp (-(2 * π ^ 2 * W ^ 2) * ((ω : ℂ) + a * Complex.I) ^ 2 -
        2 * π * Complex.I * ((ω : ℂ) + a * Complex.I) * x₀) * H (((ω : ℂ) + a * Complex.I) - ν) := by
  rw [windowCoeff_gauss_eq hh hW x₀ ν]
  set b : ℝ := 2 * π ^ 2 * W ^ 2 with hb
  have hb0 : 0 < b := by positivity
  set Φ : ℂ → ℂ := fun w => Complex.exp (-b * w ^ 2 - 2 * π * Complex.I * w * x₀) * H (w - ν) with hΦ
  have hΦ0 : ∀ ω : ℝ, Complex.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2 - 2 * π * Complex.I * ω * x₀) *
      Fh h ((ω - ν : ℝ) : ℂ) = Φ (ω : ℂ) := by
    intro ω
    simp only [hΦ, hb]
    rw [← hH0]; push_cast; rfl
  simp_rw [hΦ0]
  set f : ℂ → ℂ := fun ζ => Φ (Complex.I * a * ζ) with hf
  have hmap : ∀ ζ : ℂ, (Complex.I * a * ζ).im = a * ζ.re := by intro ζ; simp
  have hsubc : ∀ ζ ∈ closedStrip, Complex.I * a * ζ - ν ∈ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ a} := by
    intro ζ hζ
    have : (Complex.I * a * ζ - ν).im = a * ζ.re := by simp [Complex.mul_im]
    simp only [mem_setOf_eq, this]
    exact ⟨by nlinarith [hζ.1], by nlinarith [hζ.2]⟩
  have hsubd : ∀ ζ ∈ strip, Complex.I * a * ζ - ν ∈ {z : ℂ | 0 < z.im ∧ z.im < a} := by
    intro ζ hζ
    have : (Complex.I * a * ζ - ν).im = a * ζ.re := by simp [Complex.mul_im]
    simp only [mem_setOf_eq, this]
    exact ⟨by nlinarith [hζ.1], by nlinarith [hζ.2]⟩
  have hc : ContinuousOn f closedStrip := by
    refine ContinuousOn.mul (by fun_prop) ?_
    exact hHc.comp (by fun_prop) hsubc
  have hd : DifferentiableOn ℂ f strip := by
    refine DifferentiableOn.mul (by fun_prop) ?_
    exact hHd.comp (by fun_prop) hsubd
  set B : ℝ → ℝ := fun y => M * Real.exp (b * a ^ 2 + 2 * π * a * |x₀|) * Real.exp (-(b * a ^ 2) * y ^ 2) with hBdef
  have hB : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B y := by
    intro x hx y
    simp only [hf, hΦ]
    rw [norm_mul]
    have hw : Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I) - ν = ((-(a * y) - ν : ℝ) : ℂ) + ((a * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    have h1 : ‖H (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I) - ν)‖ ≤ M := by
      apply hM
      · rw [hw]; simp; nlinarith [hx.1]
      · rw [hw]; simp; nlinarith [hx.2]
    have h2 : ‖Complex.exp (-b * (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I)) ^ 2 -
        2 * π * Complex.I * (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I)) * x₀)‖ ≤
        Real.exp (b * a ^ 2 + 2 * π * a * |x₀|) * Real.exp (-(b * a ^ 2) * y ^ 2) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : (-b * (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I)) ^ 2 -
        2 * π * Complex.I * (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I)) * x₀).re =
          b * a ^ 2 * x ^ 2 - b * a ^ 2 * y ^ 2 + 2 * π * a * x * x₀ := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]; ring
      rw [this]
      have hx1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      have hx2 : 2 * π * a * x * x₀ ≤ 2 * π * a * |x₀| := by
        have : x * x₀ ≤ |x₀| := by
          calc x * x₀ ≤ x * |x₀| := mul_le_mul_of_nonneg_left (le_abs_self _) hx.1
            _ ≤ 1 * |x₀| := mul_le_mul_of_nonneg_right hx.2 (abs_nonneg _)
            _ = |x₀| := one_mul _
        calc 2 * π * a * x * x₀ = (2 * π * a) * (x * x₀) := by ring
          _ ≤ (2 * π * a) * |x₀| := mul_le_mul_of_nonneg_left this (by positivity)
      nlinarith only [mul_nonneg (mul_pos hb0 (pow_pos ha 2)).le (sub_nonneg.2 hx1), hx2]
    calc ‖Complex.exp (-b * (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I)) ^ 2 -
        2 * π * Complex.I * (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I)) * x₀)‖ *
        ‖H (Complex.I * a * ((x : ℂ) + (y : ℂ) * Complex.I) - ν)‖
        ≤ (Real.exp (b * a ^ 2 + 2 * π * a * |x₀|) * Real.exp (-(b * a ^ 2) * y ^ 2)) * M :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = B y := by simp only [hBdef]; ring
  have hBint : Integrable B := by
    have := (integrable_exp_neg_mul_sq (mul_pos hb0 (pow_pos ha 2))).const_mul
      (M * Real.exp (b * a ^ 2 + 2 * π * a * |x₀|))
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [hBdef]; try ring
  have hBt : ∀ F : Filter ℝ, F ≤ cocompact ℝ → Tendsto B F (𝓝 0) := by
    intro F hF
    have h1 : Tendsto (fun y : ℝ => y ^ 2) (cocompact ℝ) atTop := by
      have := (tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))
      refine this.congr (fun y => ?_)
      simp [Real.norm_eq_abs, sq_abs]
    have h2 : Tendsto (fun y : ℝ => Real.exp (-(b * a ^ 2) * y ^ 2)) (cocompact ℝ) (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        ((tendsto_id.const_mul_atTop (mul_pos hb0 (pow_pos ha 2))).comp h1))
      refine this.congr (fun y => ?_)
      simp; try ring_nf
    have h3 := h2.const_mul (M * Real.exp (b * a ^ 2 + 2 * π * a * |x₀|))
    simp only [mul_zero] at h3
    exact (h3.mono_left hF).congr (fun y => by simp only [hBdef]; try ring)
  have hmain := CtDual.vertical_lines_eq_cts hc hd hB hBint
    (hBt atTop atTop_le_cocompact) (hBt atBot atBot_le_cocompact)
  have e0 : ∀ y : ℝ, f ((y : ℂ) * Complex.I) = Φ (((-(a * y) : ℝ)) : ℂ) := by
    intro y; simp only [hf]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e1 : ∀ y : ℝ, f (1 + (y : ℂ) * Complex.I) = Φ ((((-(a * y) : ℝ)) : ℂ) + a * Complex.I) := by
    intro y; simp only [hf]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  simp_rw [e0, e1] at hmain
  have hs : ∀ G : ℝ → ℂ, ∫ y : ℝ, G (-(a * y)) = a⁻¹ * ∫ ω : ℝ, G ω := by
    intro G
    have := Measure.integral_comp_mul_left (fun ω : ℝ => G (-ω)) a
    rw [this, integral_neg_eq_self (fun ω : ℝ => G ω) volume, abs_of_pos (inv_pos.2 ha), Complex.real_smul]
  have hl := hs (fun ω => Φ (ω : ℂ))
  have hr := hs (fun ω => Φ ((ω : ℂ) + a * Complex.I))
  rw [hl, hr] at hmain
  have hainv : ((a⁻¹ : ℝ) : ℂ) ≠ 0 := by simp [ha.ne']
  have := mul_left_cancel₀ hainv hmain
  refine this.symm.trans (integral_congr_ae (ae_of_all _ fun ω => ?_))
  simp only [hΦ, hb]; push_cast; rfl


open FormalResearch.SignUncertainty.CtOuter in
/-- Norm bound from the contour shift (`ct:boas` Step 4):
`‖ĝ(ν)‖ ≤ ∫ e^{-2π²W²(ω²-a²) + 2πa x₀} ‖H(ω + ia - ν)‖ dω`. -/
theorem windowCoeff_gauss_shift_bound {h : ℝ → ℝ} (hh : Integrable h) {W : ℝ} (hW : 0 < W) (x₀ ν a : ℝ)
    (ha : 0 < a) {H : ℂ → ℂ} (hH0 : ∀ x : ℝ, H x = Fh h x)
    (hHc : ContinuousOn H {z : ℂ | 0 ≤ z.im ∧ z.im ≤ a})
    (hHd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im ∧ z.im < a}) {M : ℝ}
    (hM : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ a → ‖H z‖ ≤ M) :
    ‖∫ x : ℝ, (gaussK W (x - x₀) : ℂ) * (h x : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * x))‖ ≤
      ∫ ω : ℝ, Real.exp (-(2 * π ^ 2 * W ^ 2) * (ω ^ 2 - a ^ 2) + 2 * π * a * x₀) *
        ‖H (((ω : ℂ) + a * Complex.I) - ν)‖ := by
  rw [windowCoeff_gauss_shift hh hW x₀ ν a ha hH0 hHc hHd hM]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae (ae_of_all _ fun ω => ?_)))
  simp only []
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [pow_two, Complex.mul_re, Complex.mul_im]

/-- info: 'FormalResearch.SignUncertainty.CtBoasWindow.windowCoeff_gauss_shift_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowCoeff_gauss_shift_bound

end FormalResearch.SignUncertainty.CtBoasWindow
