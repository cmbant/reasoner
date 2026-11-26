/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingHol
public import FormalResearch.SignUncertainty.FctSplittingResidue

/-!
# The Cauchy splitting integrals `F_±`: holomorphy and the contour shift (`fct:splitting` (2))

Paper I (`constant_terms_five.tex`), proof of `fct:splitting` (2) (`(fct:Fpm-def)`, the paragraph "shifting the contour ... residue `F_-(ζ) - F_+(ζ) = K_sp(ζ,ζ)F(ζ) = F(ζ)`").

Everything here takes as hypotheses only the data of `D_{τ₁}` (`CompData`-type: holomorphic on `S`, continuous and bounded on `S̄`), `c > 0`, and a uniform bound
`‖F(σ+iy)‖ ≤ B` on the contour lines (the consequence of the descent bound `(fct:F-38-bnd)` = `FctDescentStmt`, see `FctSplittingWarp`).

* `fctKsp_div_le_unif`: the kernel bound `|K_sp(t,ζ)/(t-ζ)| ≤ K (1+|y|)⁻²` on `Re t = σ`, uniform for `ζ` in a set with `|ζ| ≤ R`, `|ζ+1| ≥ m`, `|Re ζ - σ| ≥ δ`.
* `fctKsp_div_le_horiz`: on horizontal segments `Re t ∈ [3/8, 7/16]`, `|Im t| ≥ Y₀`: `|K_sp/(t-ζ)| ≤ K/|y|²`.
* `fctCauchy_differentiableOn`: `ζ ↦ fctCauchy σ ζ` is holomorphic on any open set of `ζ` with `Re ζ > 0`, `Re ζ ≠ σ`.
* `fctCauchy_shift`: **`F_-^{7/16}(ζ) - F_+^{3/8}(ζ) = F(ζ)` for `3/8 < Re ζ < 7/16`** (rectangle residue `rectInt_residue`, horizontal sides `→ 0`), and
  `fctCauchy_shift_left`: the two contours agree for `0 < Re ζ < 3/8` (Cauchy's theorem).

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- **Uniform kernel bound** on `Re t = σ`, `3/8 ≤ σ ≤ 7/16`: `|K_sp(t,ζ)/(t-ζ)| ≤ K/(1+|y|)²`, with `K` depending only on `σ` and on bounds `|ζ| ≤ R`,
`|ζ+1| ≥ m > 0`, `|Re ζ - σ| ≥ δ > 0`. -/
lemma fctKsp_div_le_unif {σ : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16) {R m δ : ℝ} (hR : 0 ≤ R) (hm : 0 < m) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ : ℂ, ‖ζ‖ ≤ R → m ≤ ‖ζ + 1‖ → δ ≤ |ζ.re - σ| → ∀ y : ℝ,
      ‖fctKsp ((σ : ℂ) + y * Complex.I) ζ / ((σ : ℂ) + y * Complex.I - ζ)‖ ≤ K / (1 + |y|) ^ 2 := by
  set κ0 : ℝ := δ / (2 + 2 * R) with hκ0
  have hκ0pos : 0 < κ0 := by positivity
  refine ⟨R ^ 3 * (m⁻¹) ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / κ0, by positivity, fun ζ hζR hζm hζδ y => ?_⟩
  set t : ℂ := (σ : ℂ) + y * Complex.I with ht
  have hy : 0 < 1 + |y| := by positivity
  have hd : ζ.re ≠ σ := fun h => by rw [h, sub_self, abs_zero] at hζδ; linarith
  set κ : ℝ := |ζ.re - σ| / (1 + |ζ.im| + |ζ.re - σ|) with hκ
  have hκκ0 : κ0 ≤ κ := by
    have himR : |ζ.im| ≤ R := (Complex.abs_im_le_norm ζ).trans hζR
    have hreR : |ζ.re - σ| ≤ R + 1 := by
      have : |ζ.re| ≤ R := (Complex.abs_re_le_norm ζ).trans hζR
      calc |ζ.re - σ| ≤ |ζ.re| + |σ| := abs_sub _ _
        _ ≤ R + 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ σ)]; linarith
    rw [hκ0, hκ, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg ζ.im, abs_nonneg (ζ.re - σ)]
  have hκpos : 0 < κ := hκ0pos.trans_le hκκ0
  have h1 : 3 / 16 * (1 + |y|) ≤ ‖t‖ := norm_line_ge hσ y
  have h2 : ‖t + 1‖ ≤ 2 * (1 + |y|) := norm_line_add_one_le (σ := σ) (by linarith) (by linarith) y
  have h3 : κ * (1 + |y|) ≤ ‖t - ζ‖ := norm_line_sub_ge (σ := σ) hd y
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le (by positivity) h1
  have hts : 0 < ‖t - ζ‖ := lt_of_lt_of_le (by positivity) h3
  set a := ‖ζ + 1‖⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have haR : a ≤ m⁻¹ := by rw [ha]; exact inv_anti₀ hm hζm
  have key : ‖fctKsp t ζ / (t - ζ)‖ = ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 / ‖t - ζ‖ := by
    simp only [fctKsp, norm_div, norm_pow, norm_mul, ha]; ring
  rw [key]
  have hnum : ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 ≤
      ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / (1 + |y|) := by
    have e1 : ‖t‖ ^ 3 ≥ (3 / 16) ^ 3 * (1 + |y|) ^ 3 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 3
    have e2 : ‖t + 1‖ ^ 2 ≤ 2 ^ 2 * (1 + |y|) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hy]
    have : ‖ζ‖ ^ 3 * (‖t + 1‖ ^ 2 * a ^ 2) * (1 + |y|) ≤
        ‖ζ‖ ^ 3 * (2 ^ 2 * (1 + |y|) ^ 2 * a ^ 2) * (1 + |y|) := by gcongr
    refine this.trans ?_
    have : ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) * ‖t‖ ^ 3 ≥
        ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) * ((3 / 16) ^ 3 * (1 + |y|) ^ 3) := by gcongr
    refine le_trans (le_of_eq ?_) this
    field_simp
  calc ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 / ‖t - ζ‖
      ≤ (‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / (1 + |y|)) / (κ * (1 + |y|)) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) h3
    _ = ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / κ / (1 + |y|) ^ 2 := by
        field_simp
    _ ≤ R ^ 3 * (m⁻¹) ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / κ0 / (1 + |y|) ^ 2 := by
        have hn3 : ‖ζ‖ ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hζR 3
        have ha2 : a ^ 2 ≤ (m⁻¹) ^ 2 := pow_le_pow_left₀ ha0 haR 2
        gcongr

/-- **Horizontal kernel bound**: for `Re t = x ∈ [3/8, 7/16]` and `|Im t| = |y| ≥ Y₀`, `|K_sp(t,ζ)/(t-ζ)| ≤ K/y²`. -/
lemma fctKsp_div_le_horiz (ζ : ℂ) :
    ∃ K Y0 : ℝ, 0 ≤ K ∧ 1 ≤ Y0 ∧ ∀ x y : ℝ, 3 / 8 ≤ x → x ≤ 7 / 16 → Y0 ≤ |y| →
      ‖fctKsp ((x : ℂ) + y * Complex.I) ζ / ((x : ℂ) + y * Complex.I - ζ)‖ ≤ K / y ^ 2 := by
  refine ⟨18 * ‖ζ‖ ^ 3 * (‖ζ + 1‖⁻¹) ^ 2, 2 * |ζ.im| + 1, by positivity, by linarith [abs_nonneg ζ.im], fun x y hx hx' hy => ?_⟩
  set t : ℂ := (x : ℂ) + y * Complex.I with ht
  have hy1 : 1 ≤ |y| := by linarith [abs_nonneg ζ.im]
  have hypos : 0 < |y| := by linarith
  have h1 : |y| ≤ ‖t‖ := by simpa [ht] using Complex.abs_im_le_norm t
  have h2 : ‖t + 1‖ ≤ 3 * |y| := by
    have : t + 1 = ((x + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by rw [ht]; push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x + 1)]
    linarith
  have h3 : |y| / 2 ≤ ‖t - ζ‖ := by
    have := Complex.abs_im_le_norm (t - ζ)
    have him : (t - ζ).im = y - ζ.im := by simp [ht]
    rw [him] at this
    have h4 : |y| - |ζ.im| ≤ |y - ζ.im| := by
      have := abs_sub_abs_le_abs_sub y ζ.im; linarith
    linarith
  have htpos : 0 < ‖t‖ := hypos.trans_le h1
  have hts : 0 < ‖t - ζ‖ := by linarith
  set a := ‖ζ + 1‖⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have key : ‖fctKsp t ζ / (t - ζ)‖ = ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 / ‖t - ζ‖ := by
    simp only [fctKsp, norm_div, norm_pow, norm_mul, ha]; ring
  rw [key]
  have e1 : |y| ^ 3 ≤ ‖t‖ ^ 3 := pow_le_pow_left₀ hypos.le h1 3
  have e2 : ‖t + 1‖ ^ 2 ≤ (3 * |y|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hnum : ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 ≤ ‖ζ‖ ^ 3 / |y| ^ 3 * ((3 * |y|) * a) ^ 2 := by
    rw [mul_pow, mul_pow]
    gcongr
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  calc ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 / ‖t - ζ‖
      ≤ (‖ζ‖ ^ 3 / |y| ^ 3 * ((3 * |y|) * a) ^ 2) / (|y| / 2) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) h3
    _ = 18 * ‖ζ‖ ^ 3 * a ^ 2 / y ^ 2 := by rw [hy2]; field_simp; ring

/-- **Measurability of the Cauchy integrand in `y`** (`0 < σ < 1`, any `ζ`). -/
lemma fctCauchyIntegrand_measurable {K4 ε c L1 α σ : ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip) (hσ0 : 0 < σ) (hσ1 : σ < 1) (ζ : ℂ) :
    Measurable (fctCauchyIntegrand K4 ε c L1 α σ ζ) := by
  have hFm := fctFint_line_measurable (ε := ε) (L1 := L1) (α := α) hc hDc hσ0 hσ1
  unfold fctCauchyIntegrand fctKsp
  exact ((((by fun_prop : Measurable fun y : ℝ => (ζ / ((σ : ℂ) + y * Complex.I)) ^ 3).mul
    (by fun_prop : Measurable fun y : ℝ => (((σ : ℂ) + y * Complex.I + 1) / (ζ + 1)) ^ 2)).mul hFm).div
    (by fun_prop : Measurable fun y : ℝ => (σ : ℂ) + y * Complex.I - ζ))

/-- **Holomorphy of the Cauchy integral `ζ ↦ fctCauchy σ ζ`** in `ζ`, on any open set with `Re ζ > 0` and `Re ζ ≠ σ` (`3/8 ≤ σ ≤ 7/16`),
when `‖F(σ+iy)‖ ≤ B` on the contour (`(fct:Fpm-def)`: `F_±` holomorphic).  Parameter integral with the dominating function `K B (1+|y|)⁻²`. -/
theorem fctCauchy_differentiableOn {K4 ε c L1 α σ B : ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip) (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    (hF : ∀ y : ℝ, ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B)
    {U : Set ℂ} (hU : IsOpen U) (hUσ : ∀ w ∈ U, 0 < w.re ∧ w.re ≠ σ) :
    DifferentiableOn ℂ (fctCauchy K4 ε c L1 α σ) U := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF 0)
  unfold fctCauchy
  refine DifferentiableOn.const_mul ?_ _
  refine differentiableOn_integral_param (μ := volume) (Φ := fun w y => fctCauchyIntegrand K4 ε c L1 α σ w y) hU
    (fun w _ => (fctCauchyIntegrand_measurable hc hDc (by linarith) (by linarith) w).aestronglyMeasurable) ?_ ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    intro w hw
    have hre := hUσ w hw
    set t : ℂ := (σ : ℂ) + y * Complex.I with ht
    have htre : t.re = σ := by simp [ht]
    have ht0 : t ≠ 0 := fun h => by rw [h] at htre; simp at htre; linarith
    have hw1 : w + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hre.1]
    have htw : t - w ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [Complex.sub_re, htre] at this; simp at this; exact hre.2 (by linarith)
    unfold fctCauchyIntegrand fctKsp
    have : DifferentiableAt ℂ (fun w : ℂ => (w / t) ^ 3 * ((t + 1) / (w + 1)) ^ 2 * fctFint K4 ε c L1 α t / (t - w)) w := by
      refine DifferentiableAt.div ?_ (by fun_prop) htw
      refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) (differentiableAt_const _)
      · fun_prop (disch := exact ht0)
      · have h5 : DifferentiableAt ℂ (fun w : ℂ => (t + 1) / (w + 1)) w :=
          (differentiableAt_const _).div (by fun_prop) hw1
        exact h5.fun_pow 2
    exact this.differentiableWithinAt
  · intro w0 hw0
    obtain ⟨hre0, hne0⟩ := hUσ w0 hw0
    set δ0 : ℝ := |w0.re - σ| with hδ0
    have hδ0pos : 0 < δ0 := abs_pos.mpr (sub_ne_zero.mpr hne0)
    set r : ℝ := min (min 1 (δ0 / 2)) (w0.re / 2) with hr
    have hrpos : 0 < r := lt_min (lt_min one_pos (by positivity)) (by positivity)
    obtain ⟨K, hK0, hK⟩ := fctKsp_div_le_unif hσ hσ' (R := ‖w0‖ + 1) (m := 1) (δ := δ0 / 2) (by positivity) one_pos (by positivity)
    refine ⟨r, hrpos, fun y => K / (1 + |y|) ^ 2 * B, (integrable_inv_one_add_abs_sq.const_mul (K * B)).congr
      (Filter.Eventually.of_forall fun y => by ring), Filter.Eventually.of_forall fun y w hw => ?_⟩
    have hwd : ‖w - w0‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
    have hr2 : r ≤ δ0 / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hr3 : r ≤ w0.re / 2 := min_le_right _ _
    have hwre : |w.re - w0.re| ≤ ‖w - w0‖ := by simpa using Complex.abs_re_le_norm (w - w0)
    have h1 : ‖w‖ ≤ ‖w0‖ + 1 := by
      calc ‖w‖ = ‖w0 + (w - w0)‖ := by ring_nf
        _ ≤ ‖w0‖ + ‖w - w0‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have h2 : 1 ≤ ‖w + 1‖ := by
      have hwre' : w0.re / 2 ≤ w.re := by
        have := (abs_le.mp (hwre.trans hwd.le)).1; linarith
      have := Complex.re_le_norm (w + 1)
      simp only [Complex.add_re, Complex.one_re] at this
      linarith
    have h3 : δ0 / 2 ≤ |w.re - σ| := by
      have := abs_sub_abs_le_abs_sub (w0.re - σ) (w.re - σ)
      have h5 : |(w0.re - σ) - (w.re - σ)| = |w.re - w0.re| := by rw [abs_sub_comm]; ring_nf
      rw [h5] at this
      linarith
    have hk := hK w h1 h2 h3 y
    unfold fctCauchyIntegrand
    rw [mul_div_right_comm, norm_mul]
    exact mul_le_mul hk (hF y) (norm_nonneg _) (by positivity)

/-- The horizontal sides of the rectangle contribute `→ 0` (`F` bounded by `B`, kernel `O(y⁻²)`). -/
lemma horiz_tendsto {K4 ε c L1 α B : ℝ} (ζ : ℂ) {yf : ℝ → ℝ} (hyf : Tendsto (fun Y => |yf Y|) atTop atTop)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) :
    Tendsto (fun Y => ∫ x : ℝ in (3 / 8 : ℝ)..(7 / 16 : ℝ),
      fctKsp ((x : ℂ) + (yf Y : ℝ) * Complex.I) ζ * fctFint K4 ε c L1 α ((x : ℂ) + (yf Y : ℝ) * Complex.I) /
        ((x : ℂ) + (yf Y : ℝ) * Complex.I - ζ)) atTop (𝓝 0) := by
  obtain ⟨K, Y0, hK0, hY0, hK⟩ := fctKsp_div_le_horiz ζ
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF (3 / 8) 0 le_rfl (by norm_num))
  have hlim : Tendsto (fun Y => K * B / (yf Y) ^ 2 * (1 / 16)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y => (yf Y) ^ 2) atTop atTop := by
      have := (tendsto_pow_atTop (n := 2) (by norm_num)).comp hyf
      refine this.congr fun Y => ?_
      simp [sq_abs]
    have := (tendsto_const_nhds (x := K * B)).div_atTop h1
    simpa using this.mul_const (1 / 16 : ℝ)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hyf.eventually_ge_atTop Y0] with Y hY
  have hy2 : 0 < (yf Y) ^ 2 := by
    have : 0 < |yf Y| := by linarith
    have := pow_pos this 2
    rwa [sq_abs] at this
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * B / (yf Y) ^ 2) fun x hx => ?_).trans ?_
  · rw [Set.uIoc_of_le (by norm_num)] at hx
    set t : ℂ := (x : ℂ) + (yf Y : ℝ) * Complex.I
    rw [mul_div_right_comm, norm_mul]
    calc _ ≤ K / (yf Y) ^ 2 * B :=
          mul_le_mul (hK x (yf Y) hx.1.le hx.2 hY) (hF x (yf Y) hx.1.le hx.2) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [abs_of_nonneg (by norm_num)]
    apply le_of_eq; norm_num

/-- **The rectangle integral computes `F_-^{7/16} - F_+^{3/8}`**: if the boundary integrals of `K_sp F/(t-ζ)` over `[3/8, 7/16] × [-Y, Y]` are eventually `V`, then
`V = 2πi (fctCauchy (7/16) ζ - fctCauchy (3/8) ζ)` (`Re ζ ∉ {3/8, 7/16}`; the sides `Re t = σ` give `i ∫ = 2πi · C_σ`, the horizontal sides tend to `0`). -/
theorem fctCauchy_rect_limit {K4 ε c L1 α B : ℝ} (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B)
    {ζ : ℂ} (hζ7 : ζ.re ≠ 7 / 16) (hζ3 : ζ.re ≠ 3 / 8) {V : ℂ}
    (hV : ∀ᶠ Y : ℝ in atTop,
      rectInt (fun t => fctKsp t ζ * fctFint K4 ε c L1 α t / (t - ζ)) (3 / 8) (7 / 16) (-Y) Y = V) :
    V = 2 * π * Complex.I * (fctCauchy K4 ε c L1 α (7 / 16) ζ - fctCauchy K4 ε c L1 α (3 / 8) ζ) := by
  have hI7 := fctCauchyIntegrand_integrable (K4 := K4) (ε := ε) (L1 := L1) (α := α) (σ := 7 / 16) hc hDc
    (by norm_num) le_rfl hζ7 (fun y => hF _ y (by norm_num) le_rfl)
  have hI3 := fctCauchyIntegrand_integrable (K4 := K4) (ε := ε) (L1 := L1) (α := α) (σ := 3 / 8) hc hDc
    le_rfl (by norm_num) hζ3 (fun y => hF _ y le_rfl (by norm_num))
  have hR := intervalIntegral_tendsto_integral hI7 tendsto_neg_atTop_atBot tendsto_id
  have hL := intervalIntegral_tendsto_integral hI3 tendsto_neg_atTop_atBot tendsto_id
  have habs : Tendsto (fun Y : ℝ => |Y|) atTop atTop :=
    (tendsto_id (α := ℝ)).congr' (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with Y hY; simp [abs_of_nonneg hY])
  have hbot := horiz_tendsto (K4 := K4) (ε := ε) (L1 := L1) (α := α) (B := B) ζ (yf := fun Y => -Y)
    (by simpa [abs_neg] using habs) hF
  have htop := horiz_tendsto (K4 := K4) (ε := ε) (L1 := L1) (α := α) (B := B) ζ (yf := fun Y => Y) habs hF
  have hlim : Tendsto (fun Y : ℝ => rectInt (fun t => fctKsp t ζ * fctFint K4 ε c L1 α t / (t - ζ)) (3 / 8) (7 / 16) (-Y) Y)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α (7 / 16) ζ y) -
        Complex.I * (∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α (3 / 8) ζ y))) := by
    unfold rectInt
    exact ((hbot.sub htop).add (tendsto_const_nhds.mul hR)).sub (tendsto_const_nhds.mul hL)
  have hV' : Tendsto (fun Y : ℝ => rectInt (fun t => fctKsp t ζ * fctFint K4 ε c L1 α t / (t - ζ)) (3 / 8) (7 / 16) (-Y) Y)
      atTop (𝓝 V) := tendsto_const_nhds.congr' (hV.mono fun Y h => h.symm)
  rw [tendsto_nhds_unique hV' hlim]
  unfold fctCauchy
  have h2π : (2 * π : ℂ) * (((1 / (2 * π) : ℝ) : ℂ)) = 1 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast; field_simp
  linear_combination (-(Complex.I * (∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α (7 / 16) ζ y) -
    Complex.I * (∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α (3 / 8) ζ y))) * h2π


lemma fctKsp_diag {ζ : ℂ} (h0 : ζ ≠ 0) (h1 : ζ + 1 ≠ 0) : fctKsp ζ ζ = 1 := by
  unfold fctKsp
  rw [div_self h0, div_self h1]; norm_num

lemma fctKsp_differentiableOn (ζ : ℂ) : DifferentiableOn ℂ (fun t : ℂ => fctKsp t ζ) {t : ℂ | 0 < t.re} := by
  intro t ht
  have ht0 : t ≠ 0 := fun h => by rw [h] at ht; simp at ht
  unfold fctKsp
  refine DifferentiableAt.differentiableWithinAt ?_
  fun_prop (disch := exact ht0)

/-- The rectangle `[3/8, 7/16] × [-Y, Y]` lies in the band `0 < Re < 1/2`. -/
lemma rectSet_band_subset (Y : ℝ) : rectSet (3 / 8) (7 / 16) (-Y) Y ⊆ {t : ℂ | 0 < t.re ∧ t.re < 1 / 2} := by
  intro t ht
  have := ht.1
  rw [Set.uIcc_of_le (by norm_num)] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **The contour shift** (`fct:splitting` (2)): for `3/8 < Re ζ < 7/16`,
`F_-^{7/16}(ζ) - F_+^{3/8}(ζ) = K_sp(ζ,ζ) F(ζ) = F(ζ)` (rectangle residue; `F` holomorphic on the band, horizontal sides `→ 0`). -/
theorem fctCauchy_shift {K4 ε c L1 α B : ℝ} (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B)
    {ζ : ℂ} (h0 : 3 / 8 < ζ.re) (h1 : ζ.re < 7 / 16) :
    fctCauchy K4 ε c L1 α (7 / 16) ζ - fctCauchy K4 ε c L1 α (3 / 8) ζ = fctFint K4 ε c L1 α ζ := by
  have hζ0 : ζ ≠ 0 := fun h => by rw [h] at h0; simp at h0; linarith
  have hζ1 : ζ + 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hband : IsOpen {t : ℂ | 0 < t.re ∧ t.re < 1 / 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hhol : DifferentiableOn ℂ (fun t : ℂ => fctKsp t ζ * fctFint K4 ε c L1 α t) {t : ℂ | 0 < t.re ∧ t.re < 1 / 2} :=
    ((fctKsp_differentiableOn ζ).mono (fun t (ht : t ∈ {t : ℂ | 0 < t.re ∧ t.re < 1 / 2}) => ht.1)).mul (fctFint_differentiableOn_band hc hDh hDc hDb)
  have hres : ∀ᶠ Y : ℝ in atTop, rectInt (fun t => fctKsp t ζ * fctFint K4 ε c L1 α t / (t - ζ)) (3 / 8) (7 / 16) (-Y) Y =
      2 * π * Complex.I * fctFint K4 ε c L1 α ζ := by
    filter_upwards [eventually_gt_atTop |ζ.im|] with Y hY
    have hy := abs_lt.mp hY
    have := rectInt_residue (h := fun t : ℂ => fctKsp t ζ * fctFint K4 ε c L1 α t) (ζ := ζ) hband hhol
      (rectSet_band_subset Y) h0 h1 (by linarith) (by linarith)
    rw [this, fctKsp_diag hζ0 hζ1, one_mul]
  have := fctCauchy_rect_limit hc hDc hF (by linarith) (by linarith) hres
  have h2π : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [this]
  exact (mul_left_cancel₀ h2π this).symm

/-- **The two contours agree to the left of `Re t = 3/8`**: for `0 < Re ζ < 3/8`, `F_-^{7/16}(ζ) = F_-^{3/8}(ζ)` (Cauchy's theorem on the rectangle). -/
theorem fctCauchy_shift_left {K4 ε c L1 α B : ℝ} (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B)
    {ζ : ℂ} (h1 : ζ.re < 3 / 8) :
    fctCauchy K4 ε c L1 α (7 / 16) ζ = fctCauchy K4 ε c L1 α (3 / 8) ζ := by
  have hhol : DifferentiableOn ℂ (fun t : ℂ => fctKsp t ζ * fctFint K4 ε c L1 α t) {t : ℂ | 0 < t.re ∧ t.re < 1 / 2} :=
    ((fctKsp_differentiableOn ζ).mono (fun t (ht : t ∈ {t : ℂ | 0 < t.re ∧ t.re < 1 / 2}) => ht.1)).mul (fctFint_differentiableOn_band hc hDh hDc hDb)
  have hres : ∀ᶠ Y : ℝ in atTop, rectInt (fun t => fctKsp t ζ * fctFint K4 ε c L1 α t / (t - ζ)) (3 / 8) (7 / 16) (-Y) Y = 0 :=
    Filter.Eventually.of_forall fun Y => by
      refine rectInt_eq_zero_of_not_mem (h := fun t : ℂ => fctKsp t ζ * fctFint K4 ε c L1 α t) hhol
        (rectSet_band_subset Y) fun hζ => ?_
      have := hζ.1
      rw [Set.uIcc_of_le (by norm_num)] at this
      linarith [this.1]
  have := fctCauchy_rect_limit hc hDc hF (by linarith) (by linarith) hres
  have h2π : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [this]
  have h3 := mul_eq_zero.mp this.symm
  rcases h3 with h3 | h3
  · exact absurd h3 h2π
  · exact sub_eq_zero.mp h3


/-- info: 'FormalResearch.SignUncertainty.fctCauchy_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctCauchy_differentiableOn

/-- info: 'FormalResearch.SignUncertainty.fctCauchy_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctCauchy_shift

/-- info: 'FormalResearch.SignUncertainty.fctCauchy_shift_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctCauchy_shift_left

end FormalResearch.SignUncertainty
