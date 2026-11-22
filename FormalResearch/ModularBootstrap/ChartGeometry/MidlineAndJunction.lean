module

public import FormalResearch.ModularBootstrap.ChartGeometry.HalfStripAsymptotics
public import FormalResearch.ModularBootstrap.Chart.ExponentAndSaddle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Midline Geometry, Tail Decay, and Strip-Junction Estimates (§J7)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J7 (lines 635–646 and 727–735).

Proves:
* Exact midline parameterization on `ζ = 1/2 + iτ` (`τ ≥ 0`):
  - `π b(1/2 + iτ) = X(τ) - i Y(τ)` with `X(τ) > 0`, `0 < Y(τ) < π/4` for `τ > 0`, and exact
    closed-form identities `cosh(2 X(τ)) = exp(π τ)`, `cos(2 Y(τ)) = exp(-π τ)`.
  - `ω(1/2 + iτ) = -i (2π/3) ‖b(1/2 + iτ)‖²` for `τ ≥ 0` (and `+i (2π/3) ‖b(1/2 + iτ)‖²` for
    `τ ≤ 0`), so `τ ↦ Im ω(1/2 + iτ)` decreases strictly from `+∞` to `-∞`, with
    `Re ω(1/2 + iτ) = 0`.
  - `(deriv chartOmega (1/2 + iτ)).im = 0` and `(deriv chartOmega (1/2 + iτ)).re < 0` for all
    `τ ≥ 0`.
  - Tail lower bound `‖ω(1/2 + iτ)‖ ≥ c τ²` for `τ ∈ ℝ`.
* Midline decay of the reference exponent `Φ*(ζ) = Φ_V(ζ; ξ_*)` (`vlo:J10escape`, `vlo:Dp`):
  - `d/dτ Re Φ*(1/2 + iτ) = -2 arg(b(1/2 + iτ)) · d/dτ Im ω(1/2 + iτ) < 0` for `τ > 0`,
    tending to `-π/3` as `τ → +∞`.
  - Exponential-tail linear upper bound `Re Φ*(1/2 ± iτ) ≤ -d₀ - d₁ (τ - T₀)` for sufficiently
    large `T₀` and `τ ≥ T₀`, plus the real-`b` perturbation identity.
* Junction `x_L` at height `-T₀` (`lower_o1_two_edge.tex`, §J7, lines 727–735, used by Lemma `Z'`):
  - Unique `x_L ∈ (0, 1/2)` solving `Re ω(x_L - i T₀) = μ_b` for `μ_b` near `μ*`, with
    `1/2 - x_L = O(T₀⁻¹)`, `Im ω(x_L - i T₀) > 0`, and `Re Φ*(x - i T₀) ≤ -κ T₀` on `[x_L, 1/2]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ChartGeometry

open FormalResearch.ModularBootstrap.Chart

/-! ### Section 1: Exact midline identities for `b`, `q`, `ω` -/

/-- Real part of `π b(1/2 + iτ)` on the upper midline. -/
noncomputable def midlineX (τ : ℝ) : ℝ :=
  Real.pi * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re

/-- Negated imaginary part of `π b(1/2 + iτ)` on the upper midline. -/
noncomputable def midlineY (τ : ℝ) : ℝ :=
  -Real.pi * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im

lemma midlineX_zero : midlineX 0 = 0 := by
  unfold midlineX
  have hB2 : chartB (2⁻¹ : ℂ) = 0 := by simpa using chartB_half
  simp [hB2]

lemma midlineY_zero : midlineY 0 = 0 := by
  unfold midlineY
  have hB2 : chartB (2⁻¹ : ℂ) = 0 := by simpa using chartB_half
  simp [hB2]

lemma midlineX_pos {τ : ℝ} (hτ : 0 < τ) : 0 < midlineX τ := by
  unfold midlineX
  have hne : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp at this; exact hτ.ne' this
  exact mul_pos Real.pi_pos (re_chartB_pos (by norm_num) (by norm_num) hne)

lemma midlineX_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ midlineX τ := by
  rcases eq_or_lt_of_le hτ with rfl | hpos
  · rw [midlineX_zero]
  · exact (midlineX_pos hpos).le

private lemma sinh_pi_chartB_midline_sq {τ : ℝ} :
    Complex.sinh ((Real.pi : ℂ) * chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))) ^ 2 =
      -Complex.I * (Real.sinh (Real.pi * τ) : ℂ) := by
  rw [sinh_pi_chartB, cpow_half_sq]
  rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
      ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * Complex.I by
    apply Complex.ext <;> simp; ring]
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero,
    zero_mul, zero_sub, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one,
    one_mul, ← Complex.ofReal_sinh]
  ring

private lemma midline_s_eq {τ : ℝ} (hτ : 0 < τ) :
    let ζ : ℂ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
    let s : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
    0 < s.re ∧ s.im = -s.re ∧ 2 * s.re ^ 2 = Real.sinh (Real.pi * τ) := by
  intro ζ s
  have hne : ζ ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp [ζ] at this; exact hτ.ne' this
  have hcos_eq : Complex.cos ((Real.pi : ℂ) * ζ) = -Complex.I * (Real.sinh (Real.pi * τ) : ℂ) := by
    rw [show (Real.pi : ℂ) * ζ = ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp [ζ]; ring]
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero,
      zero_mul, zero_sub, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one,
      one_mul, ← Complex.ofReal_sinh]
    ring
  have hs_re : 0 < s.re :=
    cpow_half_re_pos (cos_pi_mem_slitPlane (by simp [ζ]) (by simp [ζ]) hne)
  have hs2 : s ^ 2 = -Complex.I * ((Real.sinh (Real.pi * τ) : ℝ) : ℂ) := by
    dsimp [s]; rw [cpow_half_sq, hcos_eq]
  have hs2_re : s.re ^ 2 - s.im ^ 2 = 0 := by
    have := congrArg Complex.re hs2
    rw [sq, Complex.mul_re, Complex.mul_re] at this
    simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, neg_zero, mul_zero, sub_zero] at this
    nlinarith [this]
  have hs2_im : 2 * s.re * s.im = -Real.sinh (Real.pi * τ) := by
    have := congrArg Complex.im hs2
    rw [sq, Complex.mul_im, Complex.mul_im] at this
    simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_mul, one_mul, zero_mul] at this
    linarith [this]
  have hsh_pos : 0 < Real.sinh (Real.pi * τ) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hτ)
  have hs_im_neg : s.im < 0 := by nlinarith
  have hs_im_eq : s.im = -s.re := by
    have hmul : (s.re - s.im) * (s.re + s.im) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h1 | h2
    · linarith
    · linarith
  refine ⟨hs_re, hs_im_eq, ?_⟩
  rw [hs_im_eq] at hs2_im
  linarith

lemma midlineY_bounds {τ : ℝ} (hτ : 0 < τ) : 0 < midlineY τ ∧ midlineY τ < Real.pi / 4 := by
  set ζ : ℂ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
  set s : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  obtain ⟨hs_re, hs_im_eq, _⟩ := midline_s_eq hτ
  have hs_im_neg : s.im < 0 := by linarith
  have hsh_pos : 0 < Real.sinh (Real.pi * τ) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hτ)
  have hs2_eq : s ^ 2 + 1 = 1 - Complex.I * (Real.sinh (Real.pi * τ) : ℂ) := by
    have hcos_eq : Complex.cos ((Real.pi : ℂ) * ζ) = -Complex.I * (Real.sinh (Real.pi * τ) : ℂ) := by
      rw [show (Real.pi : ℂ) * ζ = ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp [ζ]; ring]
      rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero,
        zero_mul, zero_sub, ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one,
        one_mul, ← Complex.ofReal_sinh]
      ring
    dsimp [s]; rw [cpow_half_sq, hcos_eq]; ring
  set r : ℂ := (s ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hr_slit : s ^ 2 + 1 ∈ Complex.slitPlane := by
    rw [hs2_eq, Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    linarith
  have hr_re : 0 < r.re := cpow_half_re_pos hr_slit
  have hr_im : r.im < 0 := by
    have hr2 : r ^ 2 = s ^ 2 + 1 := cpow_half_sq _
    have him2 : 2 * r.re * r.im = -Real.sinh (Real.pi * τ) := by
      have := congrArg Complex.im hr2
      rw [sq, Complex.mul_im, hs2_eq] at this
      simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_sub] at this
      linarith
    nlinarith
  set u : ℂ := s + r
  have hu_re : 0 < u.re := by simp [u]; linarith
  have hu_im : u.im < 0 := by simp [u]; linarith
  have hu_arg_lt : -Real.pi / 2 < u.arg ∧ u.arg < 0 := by
    have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu_re)
    have hlt := abs_lt.mp harg
    have hu_ne : u ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hu_re; exact lt_irrefl 0 hu_re
    have hsin : Real.sin u.arg < 0 := by
      rw [Complex.sin_arg]; exact div_neg_of_neg_of_pos hu_im (norm_pos_iff.mpr hu_ne)
    have hneg : u.arg < 0 := by
      by_contra hge
      push Not at hge
      have := Real.sin_nonneg_of_nonneg_of_le_pi hge (by linarith [hlt.2])
      linarith
    exact ⟨by linarith [hlt.1], hneg⟩
  have hpb : (Real.pi : ℂ) * chartB ζ = arsinhC s := by
    unfold chartB
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    rw [mul_inv_cancel_left₀ hpi]
  have hY_eq : midlineY τ = -u.arg := by
    unfold midlineY
    have him : ((Real.pi : ℂ) * chartB ζ).im = Real.pi * (chartB ζ).im := by
      rw [Complex.im_ofReal_mul]
    have hneg_eq : -Real.pi * (chartB ζ).im = -((Real.pi : ℂ) * chartB ζ).im := by
      rw [him]; ring
    change -Real.pi * (chartB ζ).im = -u.arg
    rw [hneg_eq, hpb]
    unfold arsinhC
    change -(Complex.log u).im = -u.arg
    rw [Complex.log_im]
  have hY_pos : 0 < midlineY τ := by linarith
  have hY_lt_half : midlineY τ < Real.pi / 2 := by linarith
  have hpb_eq : (Real.pi : ℂ) * chartB ζ = (midlineX τ : ℂ) - Complex.I * (midlineY τ : ℂ) := by
    apply Complex.ext
    · simp [midlineX, ζ]
    · simp [midlineY, ζ]
  have hsinh_eq : Complex.sinh ((midlineX τ : ℂ) - Complex.I * (midlineY τ : ℂ)) = s := by
    rw [← hpb_eq, hpb, sinh_arsinhC]
  have hsinh_re : Real.sinh (midlineX τ) * Real.cos (midlineY τ) = s.re := by
    have h1 := congrArg Complex.re hsinh_eq
    rw [sub_eq_add_neg, show -(Complex.I * (midlineY τ : ℂ)) = ((-midlineY τ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I] at h1
    rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg] at h1
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using h1
  have hsinh_im : -(Real.cosh (midlineX τ) * Real.sin (midlineY τ)) = s.im := by
    have h1 := congrArg Complex.im hsinh_eq
    rw [sub_eq_add_neg, show -(Complex.I * (midlineY τ : ℂ)) = ((-midlineY τ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I] at h1
    rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.sin_neg] at h1
    simpa only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one, zero_add,
      Complex.ofReal_neg, Complex.neg_re, mul_neg] using h1
  have h_id : Real.sinh (midlineX τ) * Real.cos (midlineY τ) =
      Real.cosh (midlineX τ) * Real.sin (midlineY τ) := by linarith
  have hX_pos := midlineX_pos hτ
  have hsh_lt_ch : Real.sinh (midlineX τ) < Real.cosh (midlineX τ) := by
    rw [Real.sinh_eq, Real.cosh_eq]
    have hexp : 0 < Real.exp (-midlineX τ) := Real.exp_pos _
    linarith
  have hcos_pos : 0 < Real.cos (midlineY τ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hY_lt_half⟩
  have hsin_pos : 0 < Real.sin (midlineY τ) :=
    Real.sin_pos_of_pos_of_lt_pi hY_pos (by linarith [Real.pi_pos])
  have hsin_lt_cos : Real.sin (midlineY τ) < Real.cos (midlineY τ) := by
    nlinarith [Real.sinh_pos_iff.mpr hX_pos]
  have hcos2_pos : 0 < Real.cos (2 * midlineY τ) := by
    rw [Real.cos_two_mul]
    have hsc := Real.sin_sq_add_cos_sq (midlineY τ)
    nlinarith
  have h2Y_lt : 2 * midlineY τ < Real.pi / 2 := by
    by_contra hge
    push Not at hge
    have hle := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith) hge
    rw [Real.cos_pi_div_two] at hle
    linarith
  exact ⟨hY_pos, by linarith⟩

lemma midline_cosh_cos_eq {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.cosh (2 * midlineX τ) = Real.exp (Real.pi * τ) ∧
      Real.cos (2 * midlineY τ) = Real.exp (-Real.pi * τ) := by
  rcases eq_or_lt_of_le hτ with rfl | hpos
  · simp [midlineX_zero, midlineY_zero]
  set ζ : ℂ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
  set s : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  obtain ⟨hs_re, hs_im_eq, hs2⟩ := midline_s_eq hpos
  have hpb_eq : (Real.pi : ℂ) * chartB ζ = (midlineX τ : ℂ) - Complex.I * (midlineY τ : ℂ) := by
    apply Complex.ext
    · simp [midlineX, ζ]
    · simp [midlineY, ζ]
  have hsinh_eq : Complex.sinh ((midlineX τ : ℂ) - Complex.I * (midlineY τ : ℂ)) = s := by
    rw [← hpb_eq, sinh_pi_chartB]
  have hsinh_re : Real.sinh (midlineX τ) * Real.cos (midlineY τ) = s.re := by
    have h1 := congrArg Complex.re hsinh_eq
    rw [sub_eq_add_neg, show -(Complex.I * (midlineY τ : ℂ)) = ((-midlineY τ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I] at h1
    rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg] at h1
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using h1
  have hsinh_im : Real.cosh (midlineX τ) * Real.sin (midlineY τ) = s.re := by
    have h1 := congrArg Complex.im hsinh_eq
    rw [sub_eq_add_neg, show -(Complex.I * (midlineY τ : ℂ)) = ((-midlineY τ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I] at h1
    rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.sin_neg] at h1
    have h1' : -(Real.cosh (midlineX τ) * Real.sin (midlineY τ)) = s.im := by
      simpa only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one, zero_add,
        Complex.ofReal_neg, Complex.neg_re, mul_neg] using h1
    linarith [hs_im_eq]
  have hprod_cos : Real.cosh (2 * midlineX τ) * Real.cos (2 * midlineY τ) = 1 := by
    have hc1 := Real.cosh_two_mul (midlineX τ)
    have hc2 := Real.cos_two_mul (midlineY τ)
    have hsc := Real.sin_sq_add_cos_sq (midlineY τ)
    have hhc := Real.cosh_sq_sub_sinh_sq (midlineX τ)
    have hsq_eq : Real.sinh (midlineX τ) ^ 2 * Real.cos (midlineY τ) ^ 2 =
        Real.cosh (midlineX τ) ^ 2 * Real.sin (midlineY τ) ^ 2 := by
      nlinarith
    have hc1' : Real.cosh (2 * midlineX τ) = 2 * Real.sinh (midlineX τ) ^ 2 + 1 := by
      linear_combination hc1 + hhc
    have hc2' : Real.cos (2 * midlineY τ) = 1 - 2 * Real.sin (midlineY τ) ^ 2 := by
      linear_combination hc2 + 2 * hsc
    calc Real.cosh (2 * midlineX τ) * Real.cos (2 * midlineY τ)
        = (2 * Real.sinh (midlineX τ) ^ 2 + 1) * (1 - 2 * Real.sin (midlineY τ) ^ 2) := by
          rw [hc1', hc2']
      _ = 1 + 2 * (Real.sinh (midlineX τ) ^ 2 * (1 - Real.sin (midlineY τ) ^ 2) -
            (Real.sinh (midlineX τ) ^ 2 + 1) * Real.sin (midlineY τ) ^ 2) := by ring
      _ = 1 + 2 * (Real.sinh (midlineX τ) ^ 2 * Real.cos (midlineY τ) ^ 2 -
            Real.cosh (midlineX τ) ^ 2 * Real.sin (midlineY τ) ^ 2) := by
          have : 1 - Real.sin (midlineY τ) ^ 2 = Real.cos (midlineY τ) ^ 2 := by linarith
          have : Real.sinh (midlineX τ) ^ 2 + 1 = Real.cosh (midlineX τ) ^ 2 := by linarith
          rw [‹1 - Real.sin (midlineY τ) ^ 2 = _›, ‹Real.sinh (midlineX τ) ^ 2 + 1 = _›]
      _ = 1 := by linarith
  have hprod_sin : Real.sinh (2 * midlineX τ) * Real.sin (2 * midlineY τ) =
      2 * Real.sinh (Real.pi * τ) := by
    rw [Real.sinh_two_mul, Real.sin_two_mul]
    nlinarith
  set u := Real.cosh (2 * midlineX τ)
  have hu_ge1 : 1 ≤ u := Real.one_le_cosh _
  have hu_pos : 0 < u := Real.cosh_pos _
  have hcos2_eq : Real.cos (2 * midlineY τ) = 1 / u :=
    eq_one_div_of_mul_eq_one_right hprod_cos
  have h_diff_sq : (u - 1 / u) ^ 2 = (2 * Real.sinh (Real.pi * τ)) ^ 2 := by
    have hsh2 : Real.sinh (2 * midlineX τ) ^ 2 = u ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (2 * midlineX τ)]
    have hsn2 : Real.sin (2 * midlineY τ) ^ 2 = 1 - (1 / u) ^ 2 := by
      rw [← hcos2_eq]; linarith [Real.sin_sq_add_cos_sq (2 * midlineY τ)]
    calc (u - 1 / u) ^ 2
        = (u ^ 2 - 1) * (1 - (1 / u) ^ 2) := by field_simp [hu_pos.ne']
      _ = Real.sinh (2 * midlineX τ) ^ 2 * Real.sin (2 * midlineY τ) ^ 2 := by rw [hsh2, hsn2]
      _ = (Real.sinh (2 * midlineX τ) * Real.sin (2 * midlineY τ)) ^ 2 := by ring
      _ = (2 * Real.sinh (Real.pi * τ)) ^ 2 := by rw [hprod_sin]
  have h_diff_nn : 0 ≤ u - 1 / u := by
    have : 1 / u ≤ 1 := div_le_one_of_le₀ hu_ge1 hu_pos.le
    linarith
  have h_sh_nn : 0 ≤ 2 * Real.sinh (Real.pi * τ) := by
    have := Real.sinh_nonneg_iff.mpr (by positivity [Real.pi_pos] : 0 ≤ Real.pi * τ)
    linarith
  have h_diff_eq : u - 1 / u = 2 * Real.sinh (Real.pi * τ) := by
    nlinarith
  set e := Real.exp (Real.pi * τ)
  have he_pos : 0 < e := Real.exp_pos _
  have he_diff : e - 1 / e = 2 * Real.sinh (Real.pi * τ) := by
    dsimp [e]; rw [Real.sinh_eq, Real.exp_neg, ← one_div]; ring
  have hu_eq_e : u = e := by
    have h1 : (u - e) * (u * e + 1) = (u * e) * ((u - 1 / u) - (e - 1 / e)) := by
      field_simp [hu_pos.ne', he_pos.ne']; ring
    rw [h_diff_eq, he_diff, sub_self, mul_zero] at h1
    have h2 : 0 < u * e + 1 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h2.ne')
  refine ⟨hu_eq_e, ?_⟩
  rw [hcos2_eq, hu_eq_e, one_div, ← Real.exp_neg, show -(Real.pi * τ) = -Real.pi * τ by ring]

lemma midlineX_strictMonoOn : StrictMonoOn midlineX (Ici 0) := by
  intro a ha b hb hab
  have h1 := (midline_cosh_cos_eq ha).1
  have h2 := (midline_cosh_cos_eq hb).1
  have hexp : Real.exp (Real.pi * a) < Real.exp (Real.pi * b) :=
    Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  rw [← h1, ← h2] at hexp
  by_contra hle
  push Not at hle
  have hcosh : Real.cosh (2 * midlineX b) ≤ Real.cosh (2 * midlineX a) := Real.cosh_le_cosh.mpr (by
    rw [abs_of_nonneg (mul_nonneg two_pos.le (midlineX_nonneg hb)),
      abs_of_nonneg (mul_nonneg two_pos.le (midlineX_nonneg ha))]
    linarith)
  linarith

lemma midlineY_strictMonoOn : StrictMonoOn midlineY (Ici 0) := by
  intro a ha b hb hab
  have h1 := (midline_cosh_cos_eq ha).2
  have h2 := (midline_cosh_cos_eq hb).2
  have hexp : Real.exp (-Real.pi * b) < Real.exp (-Real.pi * a) :=
    Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  rw [← h1, ← h2] at hexp
  have hb_nn : 0 ≤ 2 * midlineY b := by
    have hb_pos : 0 < b := lt_of_le_of_lt (mem_Ici.mp ha) hab
    linarith [(midlineY_bounds hb_pos).1]
  have ha_lt : 2 * midlineY a ≤ Real.pi := by
    rcases eq_or_lt_of_le (mem_Ici.mp ha) with rfl | ha_pos
    · rw [midlineY_zero, mul_zero]; exact Real.pi_pos.le
    · linarith [(midlineY_bounds ha_pos).2, Real.pi_pos]
  by_contra hle
  push Not at hle
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hb_nn ha_lt (by linarith)
  linarith

lemma chartOmega_midline_nonneg {τ : ℝ} (hτ : 0 ≤ τ) :
    chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
      -Complex.I * ((2 * Real.pi / 3 * (‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hτ with rfl | hpos
  · have h12 : (1 / 2 : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = 1 / 2 := by simp
    rw [h12, chartOmega_half, chartB_half]
    simp
  set ζ : ℂ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
  have hre : ζ.re ≤ 1 / 2 := by simp [ζ]
  have hq : chartQ ζ = -Complex.I * starRingEnd ℂ (chartB ζ) := by
    have hne : ζ ≠ 1 / 2 := fun h => by have := congrArg Complex.im h; simp [ζ] at this; exact hpos.ne' this
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hs_eq := midline_s_eq hpos
    set s := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
    have hsin_eq : Complex.sin ((Real.pi : ℂ) * chartQ ζ) =
        Complex.sin ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))) := by
      rw [sin_pi_chartQ ζ]
      have hz2 : (Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ)) =
          -(starRingEnd ℂ ((Real.pi : ℂ) * chartB ζ) * Complex.I) := by
        rw [map_mul, Complex.conj_ofReal]; ring
      rw [hz2, Complex.sin_neg, Complex.sin_mul_I, Complex.sinh_conj, sinh_pi_chartB ζ]
      apply Complex.ext
      · simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]; linarith [hs_eq.2.1]
      · simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]; linarith [hs_eq.2.1]
    have hq_Ioo := re_chartQ_Ioo (by simp [ζ]) (by simp [ζ]) hne
    have hY := midlineY_bounds hpos
    have hz2_re : 0 < ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).re ∧
        ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).re < Real.pi / 2 := by
      have hre_val : ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).re = midlineY τ := by
        unfold midlineY
        rw [show (Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ)) =
            -Complex.I * ((Real.pi : ℂ) * starRingEnd ℂ (chartB ζ)) by ring]
        simp [Complex.mul_re, Complex.conj_im, ζ]
      rw [hre_val]; exact ⟨hY.1, by linarith [hY.2, Real.pi_pos]⟩
    have hz1_re : 0 < ((Real.pi : ℂ) * chartQ ζ).re ∧
        ((Real.pi : ℂ) * chartQ ζ).re < Real.pi := by
      rw [Complex.re_ofReal_mul]
      exact ⟨mul_pos Real.pi_pos hq_Ioo.1, by nlinarith [Real.pi_pos, hq_Ioo.2]⟩
    have hz2_im : ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).im < 0 := by
      have him_val : ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).im = -midlineX τ := by
        unfold midlineX
        rw [show (Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ)) =
            -Complex.I * ((Real.pi : ℂ) * starRingEnd ℂ (chartB ζ)) by ring]
        simp [Complex.mul_im, Complex.conj_re, ζ]
      rw [him_val]; linarith [midlineX_pos hpos]
    have hq_im_neg : ((Real.pi : ℂ) * chartQ ζ).im < 0 := by
      unfold chartQ arccosC
      rw [mul_inv_cancel_left₀ hpi]
      set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)
      set u := Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)
      have h1z : 1 - Z ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := by
        have hc := Complex.cos_two_mul ((Real.pi : ℂ) * ζ / 2)
        have hsq := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * ζ / 2)
        rw [show 2 * ((Real.pi : ℂ) * ζ / 2) = (Real.pi : ℂ) * ζ by ring] at hc
        have hsin2 : 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 =
            1 - Complex.cos ((Real.pi : ℂ) * ζ) := by linear_combination 2 * hsq + hc
        have h2 : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
        dsimp [Z]; rw [mul_pow, h2, hsin2]; ring
      have hZ_eq : Z = (Real.cosh (Real.pi * τ / 2) : ℂ) + Complex.I * (Real.sinh (Real.pi * τ / 2) : ℂ) := by
        dsimp [Z]
        rw [show (Real.pi : ℂ) * ζ / 2 = ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * τ / 2 : ℝ) : ℂ) * Complex.I by
          apply Complex.ext <;> simp [ζ]; ring,
          Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
          Real.sin_pi_div_four, Real.cos_pi_div_four]
        have hsq : √2 * (√2 / 2) = 1 := by
          rw [mul_div_assoc', Real.mul_self_sqrt (by norm_num)]; norm_num
        have hsq_c : (√2 : ℂ) * ((√2 / 2 : ℝ) : ℂ) = 1 := by rw [← Complex.ofReal_mul, hsq, Complex.ofReal_one]
        calc (√2 : ℂ) * (((√2 / 2 : ℝ) : ℂ) * (Real.cosh (Real.pi * τ / 2) : ℂ) +
              ((√2 / 2 : ℝ) : ℂ) * ((Real.sinh (Real.pi * τ / 2) : ℂ) * Complex.I))
            = ((√2 : ℂ) * ((√2 / 2 : ℝ) : ℂ)) * (Real.cosh (Real.pi * τ / 2) : ℂ) +
                ((√2 : ℂ) * ((√2 / 2 : ℝ) : ℂ)) * (Real.sinh (Real.pi * τ / 2) : ℂ) * Complex.I := by ring
          _ = _ := by rw [hsq_c]; ring
      have hu_norm : 1 < ‖u‖ := by
        have hIs : Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) = Complex.I * s := by dsimp [s]; rw [h1z]
        have hIs_re : 0 < (Complex.I * s).re := by simp; linarith [hs_eq.1, hs_eq.2.1]
        have hZ_re : 1 ≤ Z.re := by
          rw [hZ_eq]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
          exact Real.one_le_cosh _
        have hu_re : 1 < u.re := by
          have : u.re = Z.re + (Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)).re := Complex.add_re _ _
          rw [hIs] at this; linarith
        exact hu_re.trans_le (Complex.re_le_norm u)
      have hlog_re : 0 < (Complex.log u).re := by rw [Complex.log_re]; exact Real.log_pos hu_norm
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
      linarith
    obtain ⟨k, hk⟩ := Complex.sin_eq_sin_iff.mp hsin_eq
    rcases hk with hk1 | hk2
    · have hre_eq : ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).re =
          2 * (k : ℝ) * Real.pi + ((Real.pi : ℂ) * chartQ ζ).re := by
        have h := congrArg Complex.re hk1
        simpa using h
      have hk_abs : |(k : ℝ)| < 1 / 2 := by
        have hlt : |2 * (k : ℝ) * Real.pi| < Real.pi := by
          rw [show 2 * (k : ℝ) * Real.pi =
              ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).re -
                ((Real.pi : ℂ) * chartQ ζ).re by linarith, abs_lt]
          exact ⟨by linarith [hz1_re.2, hz2_re.1], by linarith [hz1_re.1, hz2_re.2]⟩
        rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos Real.pi_pos] at hlt
        nlinarith [Real.pi_pos]
      have hk0 : k = 0 := by
        by_contra hne0
        have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hne0
        linarith
      rw [hk0, Int.cast_zero, mul_zero, zero_mul, zero_add] at hk1
      exact mul_left_cancel₀ hpi hk1.symm
    · have him_eq : ((Real.pi : ℂ) * (-Complex.I * starRingEnd ℂ (chartB ζ))).im =
          -((Real.pi : ℂ) * chartQ ζ).im := by
        have h := congrArg Complex.im hk2
        simpa using h
      linarith [hq_im_neg, hz2_im]
  unfold chartOmega chartOmegaHalf
  simp only [hre, ↓reduceIte]
  rw [hq]
  have hprod : chartB ζ * (-Complex.I * starRingEnd ℂ (chartB ζ)) =
      -Complex.I * ((‖chartB ζ‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm (-Complex.I), ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [mul_assoc, hprod]
  push_cast; ring

lemma chartOmega_midline_nonpos {τ : ℝ} (hτ : τ ≤ 0) :
    chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
      Complex.I * ((2 * Real.pi / 3 * (‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2) : ℝ) : ℂ) := by
  have hconj_ζ : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) =
      starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  have h0 : 0 ≤ ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)).re := by simp
  have h1 : ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)).re ≤ 1 := by simp; norm_num
  have h12 : ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)).re ≤ 1 / 2 := by simp
  have hne : (1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ) ≠ 1 / 2 ↔ τ ≠ 0 := by
    constructor
    · intro h ht; apply h; subst ht; simp
    · intro ht h; apply ht; have := congrArg Complex.im h; simp at this; linarith
  rcases eq_or_lt_of_le hτ with rfl | hneg
  · have h12' : (1 / 2 : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = 1 / 2 := by simp
    rw [h12', chartOmega_half, chartB_half]
    simp
  · have hpos : 0 < -τ := neg_pos.mpr hneg
    have hb_conj : chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
        starRingEnd ℂ (chartB ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ))) := by
      rw [hconj_ζ, chartB_conj h0 h12 ((hne.mpr hneg.ne))]
    rw [hb_conj, Complex.norm_conj, hconj_ζ, chartOmega_conj h0 h1,
      chartOmega_midline_nonneg hpos.le, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring

lemma im_chartOmega_midline_strictAnti :
    StrictAnti (fun τ : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im) := by
  have hnorm_strictMono : StrictMonoOn (fun τ : ℝ => ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2) (Ici 0) := by
    intro a ha b hb hab
    have hsq_eq : ∀ t : ℝ, ‖chartB ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 =
        (midlineX t ^ 2 + midlineY t ^ 2) / Real.pi ^ 2 := by
      intro t
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      unfold midlineX midlineY
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp [hpi]
    dsimp only
    rw [hsq_eq a, hsq_eq b]
    have hX_lt := midlineX_strictMonoOn ha hb hab
    have hY_lt := midlineY_strictMonoOn ha hb hab
    have hXa : 0 ≤ midlineX a := midlineX_nonneg ha
    have hYa : 0 ≤ midlineY a := by
      rcases eq_or_lt_of_le (mem_Ici.mp ha) with rfl | hpos
      · rw [midlineY_zero]
      · exact (midlineY_bounds hpos).1.le
    have hX2 : midlineX a ^ 2 < midlineX b ^ 2 := by nlinarith
    have hY2 : midlineY a ^ 2 < midlineY b ^ 2 := by nlinarith
    exact div_lt_div_of_pos_right (by linarith) (sq_pos_of_pos Real.pi_pos)
  have hval_nonneg : ∀ {τ : ℝ}, 0 ≤ τ →
      (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im =
        -(2 * Real.pi / 3) * ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2 := by
    intro τ hτ
    rw [chartOmega_midline_nonneg hτ]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    ring
  have hval_nonpos : ∀ {τ : ℝ}, τ ≤ 0 →
      (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im =
        (2 * Real.pi / 3) * ‖chartB ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ))‖ ^ 2 := by
    intro τ hτ
    rw [chartOmega_midline_nonpos hτ]
    have hconj : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) =
        starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp
    rcases eq_or_lt_of_le hτ with rfl | hneg
    · simp only [neg_zero, Complex.ofReal_zero, mul_zero, add_zero]
      simp [Complex.mul_im, sq]
    · have hne : (1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ) ≠ 1 / 2 := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      rw [hconj, chartB_conj (by simp) (by simp) hne, Complex.norm_conj]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, one_mul]
      ring
  intro a b hab
  dsimp only
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [hval_nonneg ha, hval_nonneg hb]
    have hlt := hnorm_strictMono ha hb hab
    nlinarith [Real.pi_pos]
  · linarith
  · have h1 : (chartOmega ((1 / 2 : ℂ) + Complex.I * (b : ℂ))).im ≤ 0 := by
      rw [hval_nonneg hb]
      have hpos : 0 ≤ (2 * Real.pi / 3) * ‖chartB ((1 / 2 : ℂ) + Complex.I * (b : ℂ))‖ ^ 2 :=
        mul_nonneg (by positivity [Real.pi_pos]) (sq_nonneg _)
      linarith
    have h2 : 0 < (chartOmega ((1 / 2 : ℂ) + Complex.I * (a : ℂ))).im := by
      rw [hval_nonpos ha.le]
      have hpos : 0 < -a := neg_pos.mpr ha
      have hxb := midlineX_pos hpos
      have hnorm_pos : 0 < ‖chartB ((1 / 2 : ℂ) + Complex.I * ((-a : ℝ) : ℂ))‖ := by
        refine norm_pos_iff.mpr fun h0 => ?_
        have hre : (chartB ((1 / 2 : ℂ) + Complex.I * ((-a : ℝ) : ℂ))).re = 0 := by
          rw [h0, Complex.zero_re]
        unfold midlineX at hxb
        nlinarith [Real.pi_pos]
      positivity [Real.pi_pos]
    linarith
  · rw [hval_nonpos ha.le, hval_nonpos hb.le]
    have hlt := hnorm_strictMono (by linarith : 0 ≤ -b) (by linarith : 0 ≤ -a) (by linarith)
    nlinarith [Real.pi_pos]

lemma tendsto_im_chartOmega_midline_atTop :
    Tendsto (fun τ : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im) atTop atBot := by
  have hle : ∀ᶠ (τ : ℝ) in atTop,
      (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im ≤ -(Real.pi / 6) * τ ^ 2 := by
    filter_upwards [Ici_mem_atTop (2 : ℝ)] with τ hτ
    rw [mem_Ici] at hτ
    have hX_lb : Real.pi * τ / 2 ≤ midlineX τ := by
      have hcosh := (midline_cosh_cos_eq (by linarith : 0 ≤ τ)).1
      have hcosh_le : Real.cosh (Real.pi * τ) ≤ Real.cosh (2 * midlineX τ) := by
        rw [hcosh, Real.cosh_eq]
        have h1 : Real.exp (-(Real.pi * τ)) ≤ Real.exp (Real.pi * τ) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
        linarith
      rw [Real.cosh_le_cosh, abs_of_nonneg (by nlinarith [Real.pi_pos]),
        abs_of_nonneg (by linarith [midlineX_nonneg (by linarith : 0 ≤ τ)])] at hcosh_le
      linarith
    have hnorm_lb : (τ / 2) ^ 2 ≤ ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2 := by
      have hre : τ / 2 ≤ (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
        unfold midlineX at hX_lb
        have hpi := Real.pi_pos
        nlinarith
      have h1 : (τ / 2) ^ 2 ≤ (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re ^ 2 := by
        nlinarith
      have h2 : (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re ^ 2 ≤
          ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        linarith [sq_nonneg (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im]
      linarith
    rw [chartOmega_midline_nonneg (by linarith)]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    nlinarith [Real.pi_pos]
  refine tendsto_atBot_mono' atTop hle ?_
  have hsq : Tendsto (fun τ : ℝ => τ ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  exact Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -(Real.pi / 6) < 0) hsq

lemma tendsto_im_chartOmega_midline_atBot :
    Tendsto (fun τ : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im) atBot atTop := by
  have heq : (fun τ : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im) =
      (fun τ : ℝ => -(chartOmega ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ))).im) := by
    ext τ
    have hconj : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) =
        starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp
    rw [hconj, chartOmega_conj (by simp) (by simp; norm_num)]
    simp
  rw [heq]
  exact tendsto_neg_atTop_iff.mpr (tendsto_im_chartOmega_midline_atTop.comp tendsto_neg_atBot_atTop)

lemma deriv_chartOmega_midline_real_neg {τ : ℝ} (hτ : 0 ≤ τ) :
    (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im = 0 ∧
      (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re < 0 := by
  refine ⟨im_deriv_chartOmega_midline_zero τ, ?_⟩
  rcases eq_or_lt_of_le hτ with rfl | hpos
  · have hev : chartOmega =ᶠ[𝓝 (1 / 2 : ℂ)] midpointOmega := by
      filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) rMid_pos] with w hw
      exact chartOmega_eq_midpointOmega_of_mem_rMid hw
    have hmid_val : deriv midpointOmega (1 / 2 : ℂ) = -(2 / 3 : ℂ) := by
      have hcos_d : HasDerivAt (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z))
          (-Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) * (Real.pi : ℂ)) (1 / 2 : ℂ) := by
        have hlin : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) (1 / 2 : ℂ) := by
          simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (Real.pi : ℂ)
        exact ((Complex.hasDerivAt_cos _).comp (1 / 2 : ℂ) hlin).congr_deriv (by ring)
      have hcos0 : Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) = 0 := by
        rw [show (Real.pi : ℂ) * (1 / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
      have hsin1 : Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) = 1 := by
        rw [show (Real.pi : ℂ) * (1 / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
      have hA_an : AnalyticAt ℂ midpointA 0 := analyticOnNhd_midpointA 0 (mem_ball_self one_pos)
      have hA1 : AnalyticAt ℂ (fun z => midpointA (Complex.cos ((Real.pi : ℂ) * z))) (1 / 2 : ℂ) :=
        (hA_an.comp_of_eq (by fun_prop) hcos0)
      have hA2 : AnalyticAt ℂ (fun z => midpointA (-Complex.cos ((Real.pi : ℂ) * z))) (1 / 2 : ℂ) :=
        (hA_an.comp_of_eq (by fun_prop) (by rw [hcos0, neg_zero]))
      have hprod : HasDerivAt (fun z => (2 * (Real.pi : ℂ) / 3) * Complex.cos ((Real.pi : ℂ) * z) *
          (midpointA (Complex.cos ((Real.pi : ℂ) * z)) * midpointA (-Complex.cos ((Real.pi : ℂ) * z))))
          ((2 * (Real.pi : ℂ) / 3) * (-Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) * (Real.pi : ℂ)) *
            (midpointA 0 * midpointA 0)) (1 / 2 : ℂ) := by
        have hm := (hcos_d.const_mul (2 * (Real.pi : ℂ) / 3)).fun_mul
          (hA1.differentiableAt.hasDerivAt.fun_mul hA2.differentiableAt.hasDerivAt)
        have hcos0' : Complex.cos ((Real.pi : ℂ) * 2⁻¹) = 0 := by simpa using hcos0
        simpa [hcos0'] using hm
      have heq_m : midpointOmega = fun z => (2 * (Real.pi : ℂ) / 3) * Complex.cos ((Real.pi : ℂ) * z) *
          (midpointA (Complex.cos ((Real.pi : ℂ) * z)) * midpointA (-Complex.cos ((Real.pi : ℂ) * z))) := by
        ext z; unfold midpointOmega; ring
      rw [heq_m, hprod.deriv, hsin1, midpointA_zero]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      push_cast; field_simp [hpi]
    have h0 : (1 / 2 : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = 1 / 2 := by simp
    rw [h0, hev.deriv_eq, hmid_val]
    norm_num
  · have hne : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) ≠ 1 / 2 := fun h => by
      have := congrArg Complex.im h; simp at this; exact hpos.ne' this
    have hB_an : AnalyticAt ℂ chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) :=
      analyticAt_chartB (by norm_num) (by norm_num) hne
    have hline : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) Complex.I τ := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul Complex.I).const_add (1 / 2 : ℂ)
    have hB_line : DifferentiableAt ℝ (chartB ∘ fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) τ :=
      (hB_an.differentiableAt.restrictScalars ℝ).comp τ hline.differentiableAt
    have hX_diff : DifferentiableAt ℝ midlineX τ := by
      unfold midlineX
      exact (Complex.reCLM.differentiableAt.comp τ hB_line).const_mul Real.pi
    have hY_diff : DifferentiableAt ℝ midlineY τ := by
      unfold midlineY
      exact (Complex.imCLM.differentiableAt.comp τ hB_line).const_mul (-Real.pi)
    have hX_pos : 0 < midlineX τ := midlineX_pos hpos
    have hY_bds := midlineY_bounds hpos
    have hX_deriv_pos : 0 < deriv midlineX τ := by
      have hev : (fun t : ℝ => Real.cosh (2 * midlineX t)) =ᶠ[𝓝 τ] (fun t : ℝ => Real.exp (Real.pi * t)) := by
        filter_upwards [eventually_gt_nhds hpos] with t ht
        exact (midline_cosh_cos_eq ht.le).1
      have hd1 : HasDerivAt (fun t : ℝ => Real.cosh (2 * midlineX t))
          (Real.sinh (2 * midlineX τ) * (2 * deriv midlineX τ)) τ :=
        (Real.hasDerivAt_cosh _).comp τ (hX_diff.hasDerivAt.const_mul 2)
      have hd2 : HasDerivAt (fun t : ℝ => Real.exp (Real.pi * t))
          (Real.exp (Real.pi * τ) * Real.pi) τ := by
        have hmul : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi τ := by
          simpa using (hasDerivAt_id τ).const_mul Real.pi
        exact (Real.hasDerivAt_exp _).comp τ hmul
      have hu := (hd1.congr_of_eventuallyEq hev.symm).unique hd2
      have hsh_pos : 0 < Real.sinh (2 * midlineX τ) := Real.sinh_pos_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (Real.pi * τ), Real.pi_pos]
    have hY_deriv_pos : 0 < deriv midlineY τ := by
      have hev : (fun t : ℝ => Real.cos (2 * midlineY t)) =ᶠ[𝓝 τ] (fun t : ℝ => Real.exp (-Real.pi * t)) := by
        filter_upwards [eventually_gt_nhds hpos] with t ht
        exact (midline_cosh_cos_eq ht.le).2
      have hd1 : HasDerivAt (fun t : ℝ => Real.cos (2 * midlineY t))
          (-Real.sin (2 * midlineY τ) * (2 * deriv midlineY τ)) τ :=
        (Real.hasDerivAt_cos _).comp τ (hY_diff.hasDerivAt.const_mul 2)
      have hd2 : HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * t))
          (Real.exp (-Real.pi * τ) * (-Real.pi)) τ := by
        have hmul : HasDerivAt (fun t : ℝ => -Real.pi * t) (-Real.pi) τ := by
          simpa using (hasDerivAt_id τ).const_mul (-Real.pi)
        exact (Real.hasDerivAt_exp _).comp τ hmul
      have hu := (hd1.congr_of_eventuallyEq hev.symm).unique hd2
      have hsn_pos : 0 < Real.sin (2 * midlineY τ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hY_bds.1]) (by linarith [hY_bds.2])
      nlinarith [Real.exp_pos (-Real.pi * τ), Real.pi_pos]
    have hOm_re_eq : (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re =
        deriv (fun t : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).im) τ := by
      have hd_om := (analyticAt_chartOmega (ζ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ))
        (by simp) (by simp; norm_num)).differentiableAt.hasDerivAt
      have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ (hd_om.scomp τ hline)
      simpa [Function.comp_def, Complex.mul_im] using hcomp.deriv.symm
    have hev_im : (fun t : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).im) =ᶠ[𝓝 τ]
        (fun t : ℝ => -(2 / (3 * Real.pi)) * (midlineX t ^ 2 + midlineY t ^ 2)) := by
      filter_upwards [eventually_gt_nhds hpos] with t ht
      rw [chartOmega_midline_nonneg ht.le]
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero]
      have hsq : ‖chartB ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 =
          (midlineX t ^ 2 + midlineY t ^ 2) / Real.pi ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        unfold midlineX midlineY
        have hpi := Real.pi_pos.ne'
        field_simp [hpi]
      rw [hsq]
      have hpi := Real.pi_pos.ne'
      field_simp [hpi]
      ring
    have hd_sq : HasDerivAt (fun t : ℝ => -(2 / (3 * Real.pi)) * (midlineX t ^ 2 + midlineY t ^ 2))
        (-(2 / (3 * Real.pi)) * (2 * midlineX τ * deriv midlineX τ + 2 * midlineY τ * deriv midlineY τ)) τ :=
      (((hX_diff.hasDerivAt.pow 2).add (hY_diff.hasDerivAt.pow 2)).const_mul _).congr_deriv
        (by ring)
    rw [hOm_re_eq, hev_im.deriv_eq, hd_sq.deriv]
    have hsum_pos : 0 < 2 * midlineX τ * deriv midlineX τ + 2 * midlineY τ * deriv midlineY τ := by
      nlinarith [hX_pos, hY_bds.1, hX_deriv_pos, hY_deriv_pos]
    have hcoeff : 0 < 2 / (3 * Real.pi) := by positivity [Real.pi_pos]
    nlinarith

lemma norm_chartOmega_midline_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, c * τ ^ 2 ≤ ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ := by
  refine ⟨Real.pi / 6, by positivity [Real.pi_pos], fun τ => ?_⟩
  wlog hτ : 0 ≤ τ
  · push Not at hτ
    have hconj : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) =
        starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp
    rw [hconj, chartOmega_conj (by simp) (by simp; norm_num), Complex.norm_conj]
    simpa [neg_sq] using this (-τ) (by linarith)
  have hX_lb : Real.pi * τ / 2 ≤ midlineX τ := by
    have hcosh := (midline_cosh_cos_eq hτ).1
    have hcosh_le : Real.cosh (Real.pi * τ) ≤ Real.cosh (2 * midlineX τ) := by
      rw [hcosh, Real.cosh_eq]
      have h1 : Real.exp (-(Real.pi * τ)) ≤ Real.exp (Real.pi * τ) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      linarith
    rw [Real.cosh_le_cosh, abs_of_nonneg (by nlinarith [Real.pi_pos]),
      abs_of_nonneg (by linarith [midlineX_nonneg hτ])] at hcosh_le
    linarith
  have hnorm_lb : (τ / 2) ^ 2 ≤ ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2 := by
    have hre : τ / 2 ≤ (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
      unfold midlineX at hX_lb; nlinarith [Real.pi_pos]
    have h1 : (τ / 2) ^ 2 ≤ (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re ^ 2 := by nlinarith
    have h2 : (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re ^ 2 ≤
        ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      linarith [sq_nonneg (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im]
    linarith
  rw [chartOmega_midline_nonneg hτ, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity [Real.pi_pos])]
  nlinarith [Real.pi_pos]

/-! ### Section 2: Midline decay of `Re Φ*(1/2 + iτ)` (`§J7`, `vlo:J10escape`, `vlo:Dp`) -/

private lemma hasDerivAt_re_chartPhiV_midline {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t : ℝ => (chartPhiV ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) (xiStar : ℂ)).re)
      (-2 * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg *
        (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) τ := by
  have hne : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp at this; exact hτ.ne' this
  have hd_S5 := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.2
    ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (by norm_num) (by norm_num) hne
  -- Actually `chartPhiV (·) xiStar` is analytic at `1/2 + I * τ` since `1/2 + I * τ ∈ stripOpen`!
  -- Wait: let's compose `HasDerivWithinAt` on `{0 ≤ w.re ∧ w.re ≤ 1/2}` with `t ↦ 1/2 + I * t`:
  have hline : HasDerivWithinAt (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) Complex.I
      (univ : Set ℝ) τ :=
    (((Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul Complex.I).const_add (1 / 2 : ℂ) |>.congr_deriv
      (by simp [Complex.ofRealCLM_apply])).hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) (univ : Set ℝ)
      {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} := fun t _ => ⟨by norm_num, by norm_num⟩
  have hcomp := (hd_S5.comp τ hline hmaps).hasDerivAt Filter.univ_mem
  have hre_d := Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hcomp
  refine hre_d.congr_deriv ?_
  set b := chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))
  have hb_re : 0 < b.re := re_chartB_pos (by norm_num) (by norm_num) hne
  have hb_ne : b ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
  have hlog_im : (Complex.log (b / (xiStar : ℂ))).im = b.arg := by
    rw [Complex.log_im, show b / (xiStar : ℂ) = (((xiStar⁻¹ : ℝ) : ℂ)) * b by
      push_cast; ring, Complex.arg_real_mul _ (inv_pos.mpr xiStar_pos)]
  have hom_im : (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im = 0 :=
    im_deriv_chartOmega_midline_zero τ
  simp only [Complex.reCLM_apply]
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
  have h1 : (2 * Complex.log (b / (xiStar : ℂ)) *
      deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im =
      2 * b.arg * (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
    rw [Complex.mul_im, Complex.mul_im, hlog_im, hom_im]
    simp
  rw [h1]; ring

lemma deriv_re_chartPhiV_midline_neg {τ : ℝ} (hτ : 0 < τ) :
    -2 * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg *
      (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re < 0 := by
  set b := chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))
  have hb_re : 0 < b.re := by
    have hX := midlineX_pos hτ; unfold midlineX at hX; nlinarith [Real.pi_pos]
  have hb_im : b.im < 0 := by
    have hY := (midlineY_bounds hτ).1
    unfold midlineY at hY
    nlinarith [Real.pi_pos]
  have hb_ne : b ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
  have harg_neg : b.arg < 0 := by
    have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb_re))
    have hsin : Real.sin b.arg < 0 := by
      rw [Complex.sin_arg]; exact div_neg_of_neg_of_pos hb_im (norm_pos_iff.mpr hb_ne)
    by_contra hge
    push Not at hge
    have := Real.sin_nonneg_of_nonneg_of_le_pi hge (by linarith [harg.2])
    linarith
  have hom_neg : (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re < 0 :=
    (deriv_chartOmega_midline_real_neg hτ.le).2
  nlinarith

lemma re_chartPhiV_midline_strictAnti :
    StrictAntiOn (fun τ : ℝ => (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re) (Ici 0) := by
  have hcont : ContinuousOn
      (fun τ : ℝ => (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re) (Ici 0) := by
    intro τ hτ
    rcases eq_or_lt_of_le (mem_Ici.mp hτ) with rfl | hpos
    · have hstrip := continuousWithinAt_chartPhiV_half (xiStar : ℂ)
      have hmaps : MapsTo (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) (Ici 0) stripClosed :=
        fun t _ => ⟨by norm_num, by norm_num⟩
      have hcont_l : Continuous (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
      have hcomp := hstrip.comp_of_eq (hcont_l.continuousWithinAt (s := Ici 0) (x := 0)) hmaps (by simp)
      exact Complex.continuous_re.continuousAt.comp_continuousWithinAt hcomp
    · exact (hasDerivAt_re_chartPhiV_midline hpos).continuousAt.continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) hcont ?_
  intro τ hτ
  rw [interior_Ici] at hτ
  rw [(hasDerivAt_re_chartPhiV_midline hτ).deriv]
  exact deriv_re_chartPhiV_midline_neg hτ

lemma tendsto_deriv_re_chartPhiV_midline :
    Tendsto (fun τ : ℝ => -2 * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg *
        (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re)
      atTop (𝓝 (-(Real.pi / 3))) := by
  -- Use chartB_large_height and deriv_chartOmega_large_height at x = 1/2
  obtain ⟨C, hC, hdom⟩ := deriv_chartOmega_large_height
  have hB_lim : Tendsto (fun τ : ℝ => τ * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg)
      atTop (𝓝 (-(1 / 2 : ℝ))) := by
    have h_ev : ∀ᶠ (τ : ℝ) in atTop,
        |(chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re - chartBTau τ| ≤
          (12 / Real.pi) * Real.exp (-Real.pi * τ) ∧
        |(chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im - (-(1 / 4 : ℝ))| ≤
          (12 / Real.pi) * Real.exp (-Real.pi * τ) := by
      filter_upwards [Ici_mem_atTop (2 : ℝ)] with τ hτ
      have hest := chartB_large_height (x := 1 / 2) (by norm_num) le_rfl hτ
      have h12 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (τ : ℂ)) = (1 / 2 : ℂ) + Complex.I * (τ : ℂ) := by
        push_cast; rfl
      rw [h12] at hest
      have hre := (Complex.abs_re_le_norm _).trans hest
      have him := (Complex.abs_im_le_norm _).trans hest
      refine ⟨by simpa [Complex.sub_re] using hre, by
        convert him using 2
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, mul_zero, zero_sub]
        norm_num⟩
    have hre_div : Tendsto (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re / τ)
        atTop (𝓝 (1 / 2 : ℝ)) := by
      have h1 : Tendsto (fun τ : ℝ => chartBTau τ / τ) atTop (𝓝 (1 / 2 : ℝ)) := by
        have heq : (fun τ : ℝ => chartBTau τ / τ) =ᶠ[atTop]
            (fun τ : ℝ => 1 / 2 + (Real.log 2 / (2 * Real.pi)) / τ) := by
          filter_upwards [Ioi_mem_atTop (0 : ℝ)] with τ hτ
          unfold chartBTau; field_simp [hτ.ne']
        refine Tendsto.congr' heq.symm ?_
        simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add
          ((tendsto_const_nhds (x := Real.log 2 / (2 * Real.pi))).div_atTop tendsto_id)
      have hdiff : Tendsto (fun τ : ℝ => ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re - chartBTau τ) / τ)
          atTop (𝓝 0) := by
        have hbd : ∀ᶠ (τ : ℝ) in atTop,
            |((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re - chartBTau τ) / τ| ≤
              ((12 / Real.pi) * 1) / τ := by
          filter_upwards [h_ev, Ici_mem_atTop (2 : ℝ)] with τ h1 h2
          rw [mem_Ici] at h2
          rw [abs_div, abs_of_pos (by linarith : 0 < τ)]
          have hexp1 : Real.exp (-Real.pi * τ) ≤ 1 :=
            Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr Real.pi_pos.le) (by linarith [h2]))
          calc |(chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re - chartBTau τ| / τ
              ≤ ((12 / Real.pi) * Real.exp (-Real.pi * τ)) / τ := by gcongr; exact h1.1
            _ ≤ ((12 / Real.pi) * 1) / τ := by
                have hpi0 : 0 ≤ 12 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
                have hτ0 : 0 ≤ τ := by linarith
                gcongr
        rw [tendsto_zero_iff_abs_tendsto_zero]
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          ((tendsto_const_nhds (x := (12 / Real.pi) * 1)).div_atTop tendsto_id)
          (Eventually.of_forall fun _ => abs_nonneg _) hbd
      have hsum : (fun τ : ℝ => chartBTau τ / τ +
          ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re - chartBTau τ) / τ) =
          (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re / τ) := by
        ext τ; ring
      exact (Tendsto.congr (fun τ => congrFun hsum τ) (by simpa using h1.add hdiff))
    have him_lim : Tendsto (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im)
        atTop (𝓝 (-(1 / 4 : ℝ))) := by
      have hdiff : Tendsto (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im - (-(1 / 4 : ℝ)))
          atTop (𝓝 0) := by
        have hbd : ∀ᶠ (τ : ℝ) in atTop,
            |(chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im - (-(1 / 4 : ℝ))| ≤
              (12 / Real.pi) * Real.exp (-Real.pi * τ) := by
          filter_upwards [h_ev] with τ h1; exact h1.2
        rw [tendsto_zero_iff_abs_tendsto_zero]
        have hexp0 : Tendsto (fun τ : ℝ => (12 / Real.pi) * Real.exp (-Real.pi * τ)) atTop (𝓝 0) := by
          simpa using tendsto_const_nhds.mul
            (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos)))
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp0
          (Eventually.of_forall fun _ => abs_nonneg _) hbd
      simpa using hdiff.add_const (-(1 / 4 : ℝ))
    have hratio : Tendsto (fun τ : ℝ => τ * ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
        (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re)) atTop (𝓝 (-(1 / 2 : ℝ))) := by
      have heq : (fun τ : ℝ => τ * ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re)) =ᶠ[atTop]
          (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re / τ)) := by
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with τ hτ
        field_simp [hτ.ne']
      refine Tendsto.congr' heq.symm ?_
      have hdiv_r := him_lim.div hre_div (by norm_num)
      convert hdiv_r using 1
      norm_num
    have hratio0 : Tendsto (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
        (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) atTop (𝓝 0) := by
      have heq : (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) =ᶠ[atTop]
          (fun τ : ℝ => (τ * ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re)) / τ) := by
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with τ hτ
        field_simp [hτ.ne']
      refine Tendsto.congr' heq.symm ?_
      simpa using hratio.div_atTop tendsto_id
    have harctan_div : Tendsto (fun u : ℝ => Real.arctan u / u) (𝓝[≠] 0) (𝓝 1) := by
      have hd := Real.hasDerivAt_arctan (0 : ℝ)
      rw [hasDerivAt_iff_tendsto_slope] at hd
      have hd1 : Tendsto (slope Real.arctan 0) (𝓝[≠] 0) (𝓝 1) := by
        simpa [sq] using hd
      refine hd1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
      simp [slope_def_field, Real.arctan_zero]
    have h_ev_ne : ∀ᶠ (τ : ℝ) in atTop,
        (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
          (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re ≠ 0 := by
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with τ hτ
      rw [mem_Ioi] at hτ
      have hre : 0 < (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
        have hX := midlineX_pos hτ; unfold midlineX at hX; nlinarith [Real.pi_pos]
      have him : (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im < 0 := by
        have hY := (midlineY_bounds hτ).1; unfold midlineY at hY; nlinarith [Real.pi_pos]
      exact div_ne_zero him.ne hre.ne'
    have h_tend_within : Tendsto (fun τ : ℝ => (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
        (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hratio0 h_ev_ne
    have h_arc_rat : Tendsto (fun τ : ℝ => Real.arctan ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
        (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) /
        ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
        (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re)) atTop (𝓝 1) :=
      harctan_div.comp h_tend_within
    have h_arg_eq : (fun τ : ℝ => τ * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg) =ᶠ[atTop]
        (fun τ : ℝ =>
          (Real.arctan ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) /
            ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re)) *
          (τ * ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re))) := by
      filter_upwards [h_ev_ne, Ioi_mem_atTop (0 : ℝ)] with τ hne hτ
      rw [mem_Ioi] at hτ
      have hre : 0 < (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
        have hX := midlineX_pos hτ; unfold midlineX at hX; nlinarith [Real.pi_pos]
      have hb_ne : chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) ≠ 0 := fun h0 => by
        rw [h0, Complex.zero_re] at hre; exact lt_irrefl 0 hre
      have harg_eq : (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg =
          Real.arctan ((chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) := by
        have hlt := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
        have hnorm_ne : ‖chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≠ 0 :=
          norm_ne_zero_iff.mpr hb_ne
        have htan : Real.tan (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg =
            (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
              (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
          rw [Real.tan_eq_sin_div_cos, Complex.sin_arg, Complex.cos_arg hb_ne]
          exact div_div_div_cancel_right₀ hnorm_ne _ _
        rw [← htan, Real.arctan_tan hlt.1 hlt.2]
      rw [harg_eq]
      set q := (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im /
        (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re
      rw [show (Real.arctan q / q) * (τ * q) = τ * ((Real.arctan q / q) * q) by ring,
        div_mul_cancel₀ _ hne]
    refine Tendsto.congr' h_arg_eq.symm ?_
    simpa using h_arc_rat.mul hratio
  have hOm_lim : Tendsto (fun τ : ℝ => (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re / τ)
      atTop (𝓝 (-(Real.pi / 3))) := by
    have h_ev : ∀ᶠ (τ : ℝ) in atTop,
        |(deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re + (2 * Real.pi / 3) * chartBTau τ| ≤
          C * (1 + τ) * Real.exp (-Real.pi * τ) := by
      filter_upwards [Ici_mem_atTop (2 : ℝ)] with τ hτ
      have hL := hdom (x := 1 / 2) (by norm_num) le_rfl hτ
      have h12 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (τ : ℂ)) = (1 / 2 : ℂ) + Complex.I * (τ : ℂ) := by
        push_cast; rfl
      rw [h12] at hL
      have hre := (Complex.abs_re_le_norm _).trans hL
      simpa [Complex.sub_re] using hre
    have h1 : Tendsto (fun τ : ℝ => -((2 * Real.pi / 3) * chartBTau τ) / τ) atTop (𝓝 (-(Real.pi / 3))) := by
      have heq : (fun τ : ℝ => -((2 * Real.pi / 3) * chartBTau τ) / τ) =ᶠ[atTop]
          (fun τ : ℝ => -(Real.pi / 3) - (Real.log 2 / 3) / τ) := by
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with τ hτ
        unfold chartBTau; field_simp [hτ.ne', Real.pi_pos.ne']; ring
      refine Tendsto.congr' heq.symm ?_
      simpa using (tendsto_const_nhds (x := -(Real.pi / 3))).sub
        ((tendsto_const_nhds (x := Real.log 2 / 3)).div_atTop tendsto_id)
    have hdiff : Tendsto (fun τ : ℝ =>
        ((deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re + (2 * Real.pi / 3) * chartBTau τ) / τ)
        atTop (𝓝 0) := by
      have hbd : ∀ᶠ (τ : ℝ) in atTop,
          |((deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re + (2 * Real.pi / 3) * chartBTau τ) / τ| ≤
            C * (1 + τ) * Real.exp (-Real.pi * τ) := by
        filter_upwards [h_ev, Ici_mem_atTop (2 : ℝ)] with τ h1 h2
        rw [mem_Ici] at h2
        rw [abs_div, abs_of_pos (by linarith : 0 < τ)]
        exact (div_le_self (abs_nonneg _) (by linarith : 1 ≤ τ)).trans h1
      have hexp0 : Tendsto (fun τ : ℝ => C * (1 + τ) * Real.exp (-Real.pi * τ)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun τ : ℝ => (1 + τ) * Real.exp (-Real.pi * τ)) atTop (𝓝 0) := by
          have h_u : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
            simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
          have h_pi : Tendsto (fun τ : ℝ => Real.pi * (1 + τ)) atTop atTop :=
            (tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop Real.pi_pos
          have hcomp := h_u.comp h_pi
          have heq : (fun τ : ℝ => (1 + τ) * Real.exp (-Real.pi * τ)) =
              (fun τ : ℝ => (Real.exp Real.pi / Real.pi) *
                ((Real.pi * (1 + τ)) * Real.exp (-(Real.pi * (1 + τ))))) := by
            ext τ
            rw [show -(Real.pi * (1 + τ)) = -Real.pi + (-Real.pi * τ) by ring, Real.exp_add,
              Real.exp_neg]
            field_simp [Real.pi_pos.ne', (Real.exp_pos Real.pi).ne']
          rw [heq]
          simpa using tendsto_const_nhds.mul hcomp
        simpa [mul_assoc] using tendsto_const_nhds.mul hlin
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp0
        (Eventually.of_forall fun _ => abs_nonneg _) hbd
    have hsum : (fun τ : ℝ => -((2 * Real.pi / 3) * chartBTau τ) / τ +
        ((deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re + (2 * Real.pi / 3) * chartBTau τ) / τ) =
        (fun τ : ℝ => (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re / τ) := by
      ext τ; ring
    exact Tendsto.congr (fun τ => congrFun hsum τ) (by simpa using h1.add hdiff)
  have heq : (fun τ : ℝ => -2 * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg *
        (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re) =ᶠ[atTop]
      (fun τ : ℝ => -2 * (τ * (chartB ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).arg) *
        ((deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re / τ)) := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with τ hτ
    field_simp [hτ.ne']
  refine Tendsto.congr' heq.symm ?_
  have hprod := ((tendsto_const_nhds (x := (-2 : ℝ))).mul hB_lim).mul hOm_lim
  rw [show (-2 : ℝ) * (-(1 / 2 : ℝ)) * (-(Real.pi / 3)) = -(Real.pi / 3) by ring] at hprod
  exact hprod

lemma re_chartPhiV_midline_tail_bound :
    ∃ T_min > (3 : ℝ), ∀ T₀ ≥ T_min, ∃ d₀ d₁ : ℝ, 0 < d₀ ∧ 0 < d₁ ∧
      ∀ τ ≥ T₀,
        (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re ≤
          -d₀ - d₁ * (τ - T₀) := by
  have hlim := tendsto_deriv_re_chartPhiV_midline
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨T₁, hT₁⟩ := hlim (Real.pi / 6) (by positivity [Real.pi_pos])
  let T₂ := max T₁ 3
  let H₂ := (chartPhiV ((1 / 2 : ℂ) + Complex.I * (T₂ : ℂ)) (xiStar : ℂ)).re
  let T_min := max (2 * T₂ + (12 / Real.pi) * |H₂| + 1) 4
  have hT_min_gt : 3 < T_min := by linarith [le_max_right (2 * T₂ + (12 / Real.pi) * |H₂| + 1) 4]
  have h_slope : ∀ t ≥ T₂,
      -2 * (chartB ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).arg *
        (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re ≤ -(Real.pi / 6) := by
    intro t ht
    have h1 := hT₁ t (le_trans (le_max_left T₁ 3) ht)
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.2]
  have h_drop : ∀ a b : ℝ, T₂ ≤ a → a ≤ b →
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (b : ℂ)) (xiStar : ℂ)).re ≤
        (chartPhiV ((1 / 2 : ℂ) + Complex.I * (a : ℂ)) (xiStar : ℂ)).re -
          (Real.pi / 6) * (b - a) := by
    intro a b ha hab
    have hT2_pos : 0 < T₂ := by linarith [le_max_right T₁ 3]
    let g : ℝ → ℝ := fun t =>
      -(chartPhiV ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) (xiStar : ℂ)).re - (Real.pi / 6) * t
    have hg_mono : MonotoneOn g (Icc a b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
      · intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le hT2_pos ha) ht.1
        exact ((hasDerivAt_re_chartPhiV_midline ht_pos).neg.sub
          (((hasDerivAt_id t).const_mul (Real.pi / 6)).congr_deriv
            (mul_one _))).continuousAt.continuousWithinAt
      · intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le hT2_pos ha) (interior_subset ht).1
        exact ((hasDerivAt_re_chartPhiV_midline ht_pos).neg.sub
          (((hasDerivAt_id t).const_mul (Real.pi / 6)).congr_deriv
            (mul_one _))).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht_mem := interior_subset ht
        have ht_pos : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le hT2_pos ha) ht_mem.1
        have hd : HasDerivAt g
            (-(-2 * (chartB ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).arg *
              (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re) - Real.pi / 6) t :=
          ((hasDerivAt_re_chartPhiV_midline ht_pos).neg.sub
            (((hasDerivAt_id t).const_mul (Real.pi / 6)).congr_deriv (mul_one (Real.pi / 6)))).congr_deriv
            rfl
        rw [hd.deriv]
        have hs := h_slope t (le_trans ha ht_mem.1)
        linarith
    have hdiff := hg_mono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    dsimp [g] at hdiff
    linarith
  refine ⟨T_min, hT_min_gt, fun T₀ hT₀ => ?_⟩
  have hT2_le_T0 : T₂ ≤ T₀ := by
    have h1 : 2 * T₂ + (12 / Real.pi) * |H₂| + 1 ≤ T_min := le_max_left _ _
    have h2 : 0 ≤ (12 / Real.pi) * |H₂| := by positivity [Real.pi_pos]
    have h3 : 0 < T₂ := by linarith [le_max_right T₁ 3]
    linarith
  have hT0_bound : (chartPhiV ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)) (xiStar : ℂ)).re ≤
      -(Real.pi / 12) * T₀ := by
    have hdrop := h_drop T₂ T₀ le_rfl hT2_le_T0
    have h1 : 2 * T₂ + (12 / Real.pi) * |H₂| + 1 ≤ T₀ := le_trans (le_max_left _ _) hT₀
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hmult : |H₂| ≤ (Real.pi / 12) * (T₀ - 2 * T₂) := by
      have h1' : (12 / Real.pi) * |H₂| ≤ T₀ - 2 * T₂ := by linarith
      calc |H₂| = (Real.pi / 12) * ((12 / Real.pi) * |H₂|) := by
            field_simp [hpi_pos.ne']
        _ ≤ (Real.pi / 12) * (T₀ - 2 * T₂) := by gcongr
    have hH2 : H₂ ≤ |H₂| := le_abs_self H₂
    have hmain : H₂ - (Real.pi / 6) * (T₀ - T₂) ≤ -(Real.pi / 12) * T₀ := by
      nlinarith
    exact hdrop.trans hmain
  refine ⟨(Real.pi / 12) * T₀, Real.pi / 6,
    mul_pos (by positivity [Real.pi_pos]) (by linarith),
    by positivity [Real.pi_pos], fun τ hτ => ?_⟩
  have hdrop2 := h_drop T₀ τ hT2_le_T0 hτ
  linarith

lemma re_chartPhiV_midline_linear_bound :
    ∃ T_min > (3 : ℝ), ∃ κ > (0 : ℝ), ∀ τ ≥ T_min,
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re ≤ -κ * τ := by
  obtain ⟨T_min, hT_min, htail⟩ := re_chartPhiV_midline_tail_bound
  obtain ⟨d₀, d₁, hd₀, hd₁, hbd⟩ := htail T_min le_rfl
  refine ⟨T_min, hT_min, min (d₀ / T_min) d₁, lt_min (div_pos hd₀ (by linarith)) hd₁, fun τ hτ => ?_⟩
  have h1 := hbd τ hτ
  have hc1 : min (d₀ / T_min) d₁ ≤ d₀ / T_min := min_le_left _ _
  have hc2 : min (d₀ / T_min) d₁ ≤ d₁ := min_le_right _ _
  have hT_pos : 0 < T_min := by linarith
  have hterm1 : min (d₀ / T_min) d₁ * T_min ≤ d₀ := by
    calc min (d₀ / T_min) d₁ * T_min ≤ (d₀ / T_min) * T_min := by gcongr
      _ = d₀ := div_mul_cancel₀ d₀ hT_pos.ne'
  have hterm2 : min (d₀ / T_min) d₁ * (τ - T_min) ≤ d₁ * (τ - T_min) := by
    exact mul_le_mul_of_nonneg_right hc2 (by linarith)
  linarith

lemma chartPhiV_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1)
    (hω : 0 ≤ (chartOmega ζ).re) {b : ℝ} (hb : 0 < b) :
    chartPhiV (starRingEnd ℂ ζ) (b : ℂ) = starRingEnd ℂ (chartPhiV ζ (b : ℂ)) := by
  unfold chartPhiV tipL ComplexBessel.stirlingJ
  rw [map_add, map_add, chartUpsilon_conj h0 h1, chartOmega_conj h0 h1]
  have htip : (2 * (Real.pi : ℂ) / 3) * (b : ℂ) =
      starRingEnd ℂ ((2 * (Real.pi : ℂ) / 3) * (b : ℂ)) := by
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal]
  congr 1
  · congr 1
    set ω := chartOmega ζ
    rw [map_mul, map_sub]
    congr 1
    have hb_log : Complex.log (b : ℂ) = (Real.log b : ℂ) := (Complex.ofReal_log hb.le).symm
    rw [hb_log]
    have h2b : starRingEnd ℂ (2 * (Real.log b : ℂ)) = 2 * (Real.log b : ℂ) := by
      simp only [map_mul, map_ofNat, Complex.conj_ofReal]
    rw [h2b]
    congr 1
    by_cases hω0 : ω = 0
    · simp [hω0]
    · set c : ℝ := 3 / (2 * Real.pi * Real.exp 1)
      have hc_pos : 0 < c := by positivity [Real.pi_pos, Real.exp_pos 1]
      have hc_re : 0 ≤ (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))).re := by
        rw [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) = (c : ℂ) * ω by
          dsimp [c]; push_cast; ring, Complex.re_ofReal_mul]
        exact mul_nonneg hc_pos.le hω
      have h_ne : 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) ≠ 0 := by
        rw [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) = (c : ℂ) * ω by
          dsimp [c]; push_cast; ring]
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc_pos.ne') hω0
      have harg : (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))).arg ≠ Real.pi := by
        intro hpi
        have hre_neg : (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))).re < 0 := by
          have hcos := Complex.cos_arg h_ne
          rw [hpi, Real.cos_pi] at hcos
          have hnorm_pos : 0 < ‖3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))‖ :=
            norm_pos_iff.mpr h_ne
          have hre_eq : (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))).re =
              -‖3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))‖ := by
            rw [eq_div_iff hnorm_pos.ne'] at hcos; linarith
          linarith
        linarith
      have hconj_div : 3 * starRingEnd ℂ ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) =
          starRingEnd ℂ (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) := by
        simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal]
      rw [hconj_div, Complex.log_conj _ harg]
  · simp only [map_mul, Complex.conj_ofReal]

lemma re_chartPhiV_midline_even (τ : ℝ) {b : ℝ} (hb : 0 < b) :
    (chartPhiV ((1 / 2 : ℂ) - Complex.I * (τ : ℂ)) (b : ℂ)).re =
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b : ℂ)).re := by
  have hconj : (1 / 2 : ℂ) - Complex.I * (τ : ℂ) =
      starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) := by
    apply Complex.ext <;> simp
  have hω_re : (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re = 0 := by
    have hle : ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)).re ≤ 1 / 2 := by simp
    unfold chartOmega
    simp only [hle, ↓reduceIte]
    by_cases ht : τ = 0
    · subst ht
      have hB2 : chartB (2⁻¹ : ℂ) = 0 := by simpa using chartB_half
      simp [chartOmegaHalf, hB2]
    · exact chartOmegaHalf_midline_re_zero ht
  rw [hconj, chartPhiV_conj (by norm_num) (by norm_num) (by rw [hω_re]) hb, Complex.conj_re]

lemma re_chartPhiV_midline_real_b (τ : ℝ) {b : ℝ} (hb : 0 < b) :
    (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b : ℂ)).re =
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re +
        (tipL (b : ℂ) - tipL (xiStar : ℂ)).re := by
  have hω_re : (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re = 0 := by
    have hle : ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)).re ≤ 1 / 2 := by simp
    unfold chartOmega
    simp only [hle, ↓reduceIte]
    by_cases ht : τ = 0
    · subst ht
      have hB2 : chartB (2⁻¹ : ℂ) = 0 := by simpa using chartB_half
      simp [chartOmegaHalf, hB2]
    · exact chartOmegaHalf_midline_re_zero ht
  unfold chartPhiV ComplexBessel.stirlingJ
  have hb_log : Complex.log (b : ℂ) = (Real.log b : ℂ) := (Complex.ofReal_log hb.le).symm
  have hx_log : Complex.log (xiStar : ℂ) = (Real.log xiStar : ℂ) :=
    (Complex.ofReal_log xiStar_pos.le).symm
  have hdiff : (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) *
      (Complex.log (3 * chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) /
        (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) - 2 * Complex.log (b : ℂ))).re =
      (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) *
        (Complex.log (3 * chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) /
          (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) - 2 * Complex.log (xiStar : ℂ))).re := by
    rw [hb_log, hx_log]
    simp only [Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, sub_zero, hω_re]
  simp only [Complex.add_re, Complex.sub_re]
  linarith

/-! ### Section 3: Junction `x_L` at height `-T₀` (`§J7`, lines 727–735) -/

private lemma exp_neg_pi_tau_le' {τ : ℝ} (hτ : 2 ≤ τ) :
    Real.exp (-Real.pi * τ) ≤ 1 / 400 := by
  have h1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h3 : (20 : ℝ) < Real.exp 3 := by
    calc (20 : ℝ) < (2.718 : ℝ) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := by gcongr
      _ = Real.exp (((3 : ℕ) : ℝ) * 1) := (Real.exp_nat_mul 1 3).symm
      _ = Real.exp 3 := by norm_num
  have hpi : (20 : ℝ) < Real.exp Real.pi :=
    lt_of_lt_of_le h3 (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))
  have h2 : (400 : ℝ) < Real.exp (2 * Real.pi) := by
    have he : Real.exp (2 * Real.pi) = (Real.exp Real.pi) ^ 2 := by
      simpa using Real.exp_nat_mul Real.pi 2
    rw [he]; nlinarith only [hpi]
  have h4 : (400 : ℝ) ≤ Real.exp (Real.pi * τ) :=
    h2.le.trans (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ]))
  rw [show -Real.pi * τ = -(Real.pi * τ) by ring, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h4

/-- Large-height formula for `ω(x + iτ)` on `0 ≤ x ≤ 1/2`, `τ ≥ 2` (`§J7`, eq. `vlo:large`). -/
lemma chartOmega_large_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 2 ≤ τ →
      ‖chartOmega ((x : ℂ) + Complex.I * (τ : ℂ)) -
          (((2 * Real.pi / 3 * chartBTau τ * (1 / 2 - x) : ℝ) : ℂ) -
            Complex.I * ((2 * Real.pi / 3 * (chartBTau τ ^ 2 + x * (1 - x) / 4) : ℝ) : ℂ))‖ ≤
        C * (1 + τ) * Real.exp (-Real.pi * τ) := by
  refine ⟨100, by norm_num, fun {x τ} hx0 hx1 hτ => ?_⟩
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  set b0 : ℂ := (chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)
  set q0 : ℂ := (((1 - x) / 2 : ℝ) : ℂ) - Complex.I * (chartBTau τ : ℂ)
  set eb := chartB ζ - b0
  set eq := chartQ ζ - q0
  have heb := chartB_large_height hx0 hx1 hτ
  have heq := chartQ_large_height hx0 hx1 hτ
  have hBtau_le : chartBTau τ ≤ 1 + τ := by
    unfold chartBTau
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hdiv : Real.log 2 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity [Real.pi_pos])]; linarith [Real.pi_gt_three]
    linarith
  have hBtau_nn : 0 ≤ chartBTau τ := by
    unfold chartBTau; positivity [Real.pi_pos, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hb0_norm : ‖b0‖ ≤ 2 * (1 + τ) := by
    dsimp [b0]
    have hx_le : ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]; linarith
    have hBn : ‖(chartBTau τ : ℂ)‖ = chartBTau τ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
    calc ‖(chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)‖
        ≤ ‖(chartBTau τ : ℂ)‖ + ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ (1 + τ) + 1 := by linarith
      _ ≤ 2 * (1 + τ) := by linarith
  have hq0_norm : ‖q0‖ ≤ 2 * (1 + τ) := by
    dsimp [q0]
    have hx_le : ‖(((1 - x) / 2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have hBn : ‖Complex.I * (chartBTau τ : ℂ)‖ = chartBTau τ := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
    calc ‖(((1 - x) / 2 : ℝ) : ℂ) - Complex.I * (chartBTau τ : ℂ)‖
        ≤ ‖(((1 - x) / 2 : ℝ) : ℂ)‖ + ‖Complex.I * (chartBTau τ : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + τ) := by linarith
      _ ≤ 2 * (1 + τ) := by linarith
  have hlead : (2 * (Real.pi : ℂ) / 3) * b0 * q0 =
      ((2 * Real.pi / 3 * chartBTau τ * (1 / 2 - x) : ℝ) : ℂ) -
        Complex.I * ((2 * Real.pi / 3 * (chartBTau τ ^ 2 + x * (1 - x) / 4) : ℝ) : ℂ) := by
    dsimp [b0, q0]
    apply Complex.ext
    · simp [sq]; ring
    · simp [sq]; ring
  have hOm_eq : chartOmega ζ = (2 * (Real.pi : ℂ) / 3) * chartB ζ * chartQ ζ := by
    unfold chartOmega chartOmegaHalf
    have hre : ζ.re ≤ 1 / 2 := by simp [ζ]; linarith
    simp only [hre, ↓reduceIte]
  have hsplit : chartOmega ζ -
      (((2 * Real.pi / 3 * chartBTau τ * (1 / 2 - x) : ℝ) : ℂ) -
        Complex.I * ((2 * Real.pi / 3 * (chartBTau τ ^ 2 + x * (1 - x) / 4) : ℝ) : ℂ)) =
      (2 * (Real.pi : ℂ) / 3) * (eb * q0 + b0 * eq + eb * eq) := by
    rw [hOm_eq, ← hlead]
    have hb_eq : chartB ζ = b0 + eb := by dsimp [eb]; ring
    have hq_eq : chartQ ζ = q0 + eq := by dsimp [eq]; ring
    rw [hb_eq, hq_eq]
    ring
  rw [hsplit, norm_mul, show ‖2 * (Real.pi : ℂ) / 3‖ = 2 * Real.pi / 3 by
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_ofNat]]
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le' hτ
  have h12 : 12 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith
  have h2 : 2 / Real.pi ≤ 1 := by rw [div_le_iff₀ Real.pi_pos]; linarith
  have heb4 : ‖eb‖ ≤ 4 * Real.exp (-Real.pi * τ) := heb.trans (by gcongr)
  have heq1 : ‖eq‖ ≤ Real.exp (-Real.pi * τ) := by
    have : ‖eq‖ ≤ (2 / Real.pi) * Real.exp (-Real.pi * τ) := by
      simpa [ζ, q0, eq] using heq
    exact this.trans (by nlinarith [Real.exp_pos (-Real.pi * τ)])
  have h1t : 1 ≤ 1 + τ := by linarith
  have h_e : 0 < Real.exp (-Real.pi * τ) := Real.exp_pos _
  have hp1 : ‖eb * q0‖ ≤ 8 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]; calc ‖eb‖ * ‖q0‖ ≤ (4 * Real.exp (-Real.pi * τ)) * (2 * (1 + τ)) := by gcongr
      _ = 8 * (1 + τ) * Real.exp (-Real.pi * τ) := by ring
  have hp2 : ‖b0 * eq‖ ≤ 2 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]; calc ‖b0‖ * ‖eq‖ ≤ (2 * (1 + τ)) * Real.exp (-Real.pi * τ) := by gcongr
      _ = 2 * (1 + τ) * Real.exp (-Real.pi * τ) := by ring
  have hp3 : ‖eb * eq‖ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]
    have h4 : ‖eb‖ ≤ 4 / 400 := heb4.trans (by linarith)
    calc ‖eb‖ * ‖eq‖
        ≤ (4 / 400) * Real.exp (-Real.pi * τ) := mul_le_mul h4 heq1 (norm_nonneg _) (by norm_num)
      _ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith [h_e, h1t]
  have hsum : ‖eb * q0 + b0 * eq + eb * eq‖ ≤ 11 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    have htri := norm_add_le (eb * q0 + b0 * eq) (eb * eq)
    have htri2 := norm_add_le (eb * q0) (b0 * eq)
    linarith
  calc (2 * Real.pi / 3) * ‖eb * q0 + b0 * eq + eb * eq‖
      ≤ (2 * 4 / 3) * (11 * (1 + τ) * Real.exp (-Real.pi * τ)) := by gcongr
    _ ≤ 100 * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith

private lemma junction_phi_line_bound
    {T₀ κ_mid x_L x : ℝ} (hT2 : 2 ≤ T₀) (hT4 : 4 ≤ T₀)
    (hBtau_lb : T₀ / 2 ≤ chartBTau T₀) (hBtau_ub : chartBTau T₀ ≤ T₀)
    (hOm'_large : ∀ {y : ℝ}, 0 ≤ y → y ≤ 1 / 2 →
      ‖deriv chartOmega ((y : ℂ) + Complex.I * (T₀ : ℂ)) -
        (-((2 * Real.pi / 3 * chartBTau T₀ : ℝ) : ℂ) -
          ((Real.pi / 3 * (1 / 2 - y) : ℝ) : ℂ) * Complex.I)‖ ≤ 1)
    (hxL0 : 0 ≤ x_L) (hxL_width : 1 / 2 - x_L ≤ (12 * muStar / Real.pi) / T₀)
    (hx : x ∈ Icc x_L (1 / 2))
    (hmid_val : (chartPhiV ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) (xiStar : ℂ)).re ≤ -κ_mid * T₀)
    (hlog_bd : (96 * muStar / Real.pi) * (Real.log (2 * T₀ / xiStar) + Real.pi) ≤ (κ_mid / 2) * T₀) :
    (chartPhiV ((x : ℂ) - Complex.I * (T₀ : ℂ)) (xiStar : ℂ)).re ≤ -(κ_mid / 2) * T₀ := by
  let Φ_re : ℝ → ℝ := fun s => (chartPhiV ((s : ℂ) - Complex.I * (T₀ : ℂ)) (xiStar : ℂ)).re
  have h_deriv_within : ∀ t ∈ Icc x (1 / 2),
      HasDerivWithinAt Φ_re
        (2 * Complex.log (chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ)) *
          deriv chartOmega ((t : ℂ) - Complex.I * (T₀ : ℂ))).re (Icc x (1 / 2)) t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hxL0 (le_trans hx.1 ht.1)
    have ht1 : t ≤ (1 / 2 : ℝ) := ht.2
    have hne : (t : ℂ) - Complex.I * (T₀ : ℂ) ≠ 1 / 2 := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hd_S5 := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.2
      ((t : ℂ) - Complex.I * (T₀ : ℂ)) (by simp; exact ht0) (by simp; linarith [ht1]) hne
    have hline : HasDerivWithinAt (fun s : ℝ => (s : ℂ) - Complex.I * (T₀ : ℂ)) 1
        (Icc x (1 / 2)) t :=
      ((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (Complex.I * (T₀ : ℂ))).hasDerivWithinAt
    have hmaps : MapsTo (fun s : ℝ => (s : ℂ) - Complex.I * (T₀ : ℂ)) (Icc x (1 / 2))
        {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} := fun s hs => by
      refine ⟨by simp; linarith [hxL0, hx.1, hs.1], by simp; linarith [hs.2]⟩
    have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hd_S5.comp t hline hmaps)
    simpa [Φ_re, Function.comp_def] using hcomp
  have hxi_lt1 : xiStar < 1 := by
    have hsh : Real.sinh (Real.pi * xiStar) < Real.sinh Real.pi := by
      rw [sinh_pi_mul_xiStar]
      have h1 : (2.71 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have h3 : (10 : ℝ) < Real.exp 3 := by
        calc (10 : ℝ) < (2.71 : ℝ) ^ 3 := by norm_num
          _ < (Real.exp 1) ^ 3 := by gcongr
          _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
      have hpi_e : 10 < Real.exp Real.pi := lt_of_lt_of_le h3 (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))
      have hneg : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
      rw [Real.sinh_eq]; linarith
    rw [Real.sinh_lt_sinh] at hsh
    exact (mul_lt_mul_iff_right₀ Real.pi_pos).mp (by simpa using hsh)
  have hlog_nn : 0 ≤ Real.log (2 * T₀ / xiStar) + Real.pi := by
    have : 1 ≤ 2 * T₀ / xiStar := by rw [le_div_iff₀ xiStar_pos]; linarith
    linarith [Real.log_nonneg this, Real.pi_pos]
  have h_deriv_bd : ∀ t ∈ Ico x (1 / 2),
      ‖(2 * Complex.log (chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ)) *
        deriv chartOmega ((t : ℂ) - Complex.I * (T₀ : ℂ))).re‖ ≤
        8 * T₀ * (Real.log (2 * T₀ / xiStar) + Real.pi) := by
    intro t ht
    refine (Real.norm_eq_abs _).le.trans ((Complex.abs_re_le_norm _).trans ?_)
    have ht0 : 0 ≤ t := le_trans hxL0 (le_trans hx.1 ht.1)
    have ht1 : t ≤ (1 / 2 : ℝ) := ht.2.le
    have hconj_eq : (t : ℂ) - Complex.I * (T₀ : ℂ) =
        starRingEnd ℂ ((t : ℂ) + Complex.I * (T₀ : ℂ)) := by apply Complex.ext <;> simp
    have hne_p : (t : ℂ) + Complex.I * (T₀ : ℂ) ≠ 1 / 2 := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hB_conj : chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) =
        starRingEnd ℂ (chartB ((t : ℂ) + Complex.I * (T₀ : ℂ))) := by
      rw [hconj_eq]
      exact chartB_conj (by simp; exact ht0) (by simp; norm_num at ht1 ⊢; exact ht1) hne_p
    have hB_est := chartB_large_height ht0 ht1 hT2
    have hpi3 := Real.pi_gt_three
    have h12 : 12 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith
    have hexp_le : Real.exp (-Real.pi * T₀) ≤ 1 / 400 := exp_neg_pi_tau_le' hT2
    have hB_err : ‖chartB ((t : ℂ) + Complex.I * (T₀ : ℂ)) -
        ((chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ))‖ ≤ 1 / 2 := by
      have : (12 / Real.pi) * Real.exp (-Real.pi * T₀) ≤ 4 * (1 / 400) := by gcongr
      exact hB_est.trans (by linarith)
    have hB0_lb : chartBTau T₀ ≤ ‖(chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ)‖ := by
      have hre : ((chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ)).re = chartBTau T₀ := by simp
      nth_rw 1 [← hre]; exact Complex.re_le_norm _
    have hB0_ub : ‖(chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ)‖ ≤ chartBTau T₀ + 1 / 2 := by
      have hx_le : ‖Complex.I * ((t / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]; linarith
      have hBn : ‖(chartBTau T₀ : ℂ)‖ = chartBTau T₀ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      calc ‖(chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ)‖
          ≤ ‖(chartBTau T₀ : ℂ)‖ + ‖Complex.I * ((t / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ chartBTau T₀ + 1 / 2 := by linarith
    have hB_norm_lb : T₀ / 4 ≤ ‖chartB ((t : ℂ) - Complex.I * (T₀ : ℂ))‖ := by
      rw [hB_conj, Complex.norm_conj]
      have htri := norm_sub_norm_le ((chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ))
        (-((chartB ((t : ℂ) + Complex.I * (T₀ : ℂ))) -
          ((chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ))))
      rw [sub_neg_eq_add, norm_neg, add_sub_cancel] at htri
      linarith
    have hB_norm_ub : ‖chartB ((t : ℂ) - Complex.I * (T₀ : ℂ))‖ ≤ 2 * T₀ := by
      rw [hB_conj, Complex.norm_conj]
      have htri := norm_add_le ((chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ))
        ((chartB ((t : ℂ) + Complex.I * (T₀ : ℂ))) -
          ((chartBTau T₀ : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ)))
      rw [add_sub_cancel] at htri
      linarith
    have hrat_lb : 1 ≤ ‖chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ)‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le,
        le_div_iff₀ xiStar_pos]
      linarith
    have hrat_ub : ‖chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ)‖ ≤ 2 * T₀ / xiStar := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le]
      exact div_le_div_of_nonneg_right hB_norm_ub xiStar_pos.le
    have hlog_bd' : ‖Complex.log (chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ))‖ ≤
        Real.log (2 * T₀ / xiStar) + Real.pi := by
      have hnorm_le := Complex.norm_le_abs_re_add_abs_im
        (Complex.log (chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ)))
      rw [Complex.log_re, Complex.log_im] at hnorm_le
      have hlog_nn' : 0 ≤ Real.log ‖chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ)‖ :=
        Real.log_nonneg hrat_lb
      rw [abs_of_nonneg hlog_nn'] at hnorm_le
      have hlog_le : Real.log ‖chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ)‖ ≤
          Real.log (2 * T₀ / xiStar) :=
        Real.log_le_log (by linarith) hrat_ub
      linarith [Complex.abs_arg_le_pi (chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ))]
    have hom'_bd : ‖deriv chartOmega ((t : ℂ) - Complex.I * (T₀ : ℂ))‖ ≤ 4 * T₀ := by
      have hconj_d : deriv chartOmega ((t : ℂ) - Complex.I * (T₀ : ℂ)) =
          starRingEnd ℂ (deriv chartOmega ((t : ℂ) + Complex.I * (T₀ : ℂ))) := by
        rw [hconj_eq]; exact deriv_chartOmega_conj' (by simp; exact ht0) (by simp; linarith)
      rw [hconj_d, Complex.norm_conj]
      have hL := hOm'_large ht0 ht1
      have hlead_ub : ‖-((2 * Real.pi / 3 * chartBTau T₀ : ℝ) : ℂ) -
          ((Real.pi / 3 * (1 / 2 - t) : ℝ) : ℂ) * Complex.I‖ ≤ 3 * T₀ + 1 := by
        have hpi4 := Real.pi_lt_four
        have h1 : ‖-((2 * Real.pi / 3 * chartBTau T₀ : ℝ) : ℂ)‖ ≤ 3 * T₀ := by
          rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (by positivity [Real.pi_pos]), abs_of_nonneg (by linarith)]
          have : 2 * Real.pi / 3 ≤ 3 := by linarith
          exact mul_le_mul this hBtau_ub (by linarith) (by norm_num)
        have h2' : ‖((Real.pi / 3 * (1 / 2 - t) : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (by positivity [Real.pi_pos]), abs_of_nonneg (by linarith)]
          calc (Real.pi / 3) * (1 / 2 - t) ≤ (Real.pi / 3) * (1 / 2) := by gcongr; linarith
            _ ≤ 1 := by linarith [hpi4]
        have htri := norm_sub_le (-((2 * Real.pi / 3 * chartBTau T₀ : ℝ) : ℂ))
          (((Real.pi / 3 * (1 / 2 - t) : ℝ) : ℂ) * Complex.I)
        linarith
      have htri := norm_add_le (-((2 * Real.pi / 3 * chartBTau T₀ : ℝ) : ℂ) -
          ((Real.pi / 3 * (1 / 2 - t) : ℝ) : ℂ) * Complex.I)
        (deriv chartOmega ((t : ℂ) + Complex.I * (T₀ : ℂ)) -
          (-((2 * Real.pi / 3 * chartBTau T₀ : ℝ) : ℂ) -
            ((Real.pi / 3 * (1 / 2 - t) : ℝ) : ℂ) * Complex.I))
      rw [add_sub_cancel] at htri
      linarith
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖Complex.log (chartB ((t : ℂ) - Complex.I * (T₀ : ℂ)) / (xiStar : ℂ))‖ *
          ‖deriv chartOmega ((t : ℂ) - Complex.I * (T₀ : ℂ))‖
        ≤ 2 * (Real.log (2 * T₀ / xiStar) + Real.pi) * (4 * T₀) := by gcongr
      _ = 8 * T₀ * (Real.log (2 * T₀ / xiStar) + Real.pi) := by ring
  have hmvt_x := norm_image_sub_le_of_norm_deriv_le_segment' h_deriv_within h_deriv_bd
    (1 / 2 : ℝ) ⟨hx.2, le_rfl⟩
  have hre_diff : Φ_re x - Φ_re (1 / 2) ≤
      (1 / 2 - x) * (8 * T₀ * (Real.log (2 * T₀ / xiStar) + Real.pi)) := by
    have h1 : Φ_re x - Φ_re (1 / 2) ≤ ‖Φ_re (1 / 2) - Φ_re x‖ := by
      rw [Real.norm_eq_abs, ← abs_neg, neg_sub]
      exact le_abs_self _
    linarith [hmvt_x]
  have hwidth_x : 1 / 2 - x ≤ (12 * muStar / Real.pi) / T₀ := by linarith [hx.1]
  have hprod_le : (1 / 2 - x) * (8 * T₀ * (Real.log (2 * T₀ / xiStar) + Real.pi)) ≤
      (96 * muStar / Real.pi) * (Real.log (2 * T₀ / xiStar) + Real.pi) := by
    have hT0_ne : T₀ ≠ 0 := by linarith
    calc (1 / 2 - x) * (8 * T₀ * (Real.log (2 * T₀ / xiStar) + Real.pi))
        ≤ ((12 * muStar / Real.pi) / T₀) * (8 * T₀ * (Real.log (2 * T₀ / xiStar) + Real.pi)) := by
          gcongr
      _ = (96 * muStar / Real.pi) * (Real.log (2 * T₀ / xiStar) + Real.pi) := by
          field_simp [hT0_ne]; ring
  have h12 : (((1 / 2 : ℝ) : ℂ) - Complex.I * (T₀ : ℂ)) =
      (1 / 2 : ℂ) - Complex.I * (T₀ : ℂ) := by push_cast; rfl
  dsimp [Φ_re] at hre_diff
  rw [h12] at hre_diff
  linarith

/-- **Junction `x_L` at height `-T₀`** (`lower_o1_two_edge.tex`, §J7, lines 727–735):
for all sufficiently large `T₀` and every `μ_b ∈ [μ*/2, 2 μ*]`, there is a unique `x_L ∈ (0, 1/2)`
with `Re ω(x_L - i T₀) = μ_b`, satisfying `1/2 - x_L ≤ C_L / T₀`,
`Im ω(x_L - i T₀) ≥ c_L T₀^2 > 0`, and `Re Φ*(x - i T₀) ≤ -κ T₀` uniformly for `x ∈ [x_L, 1/2]`. -/
theorem existsUnique_junction_xL :
    ∃ T_min > (3 : ℝ), ∃ C_L > (0 : ℝ), ∃ c_L > (0 : ℝ), ∃ κ > (0 : ℝ),
      ∀ T₀ ≥ T_min, ∀ μ_b ∈ Icc (muStar / 2) (2 * muStar),
        ∃! x_L : ℝ, x_L ∈ Ioo (0 : ℝ) (1 / 2) ∧
          (chartOmega ((x_L : ℂ) - Complex.I * (T₀ : ℂ))).re = μ_b ∧
          1 / 2 - x_L ≤ C_L / T₀ ∧
          c_L * T₀ ^ 2 ≤ (chartOmega ((x_L : ℂ) - Complex.I * (T₀ : ℂ))).im ∧
          (∀ x ∈ Icc x_L (1 / 2),
            (chartPhiV ((x : ℂ) - Complex.I * (T₀ : ℂ)) (xiStar : ℂ)).re ≤ -κ * T₀) := by
  obtain ⟨C₁, hC₁, hOm_large⟩ := chartOmega_large_height
  obtain ⟨C₂, hC₂, hOm'_large⟩ := deriv_chartOmega_large_height
  obtain ⟨T_mid, hT_mid, κ_mid, hκ_mid, hmid_lin⟩ := re_chartPhiV_midline_linear_bound
  have hexp_tend : Tendsto (fun T : ℝ => (1 + T) * Real.exp (-Real.pi * T)) atTop (𝓝 0) := by
    have h_u : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
      simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h_pi : Tendsto (fun T : ℝ => Real.pi * (1 + T)) atTop atTop :=
      (tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop Real.pi_pos
    have hcomp := h_u.comp h_pi
    have heq : (fun T : ℝ => (1 + T) * Real.exp (-Real.pi * T)) =
        (fun T : ℝ => (Real.exp Real.pi / Real.pi) *
          ((Real.pi * (1 + T)) * Real.exp (-(Real.pi * (1 + T))))) := by
      ext T
      rw [show -(Real.pi * (1 + T)) = -Real.pi + (-Real.pi * T) by ring, Real.exp_add, Real.exp_neg]
      field_simp [Real.pi_pos.ne', (Real.exp_pos Real.pi).ne']
    rw [heq]; simpa using tendsto_const_nhds.mul hcomp
  have hlog_tend : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hev_small1 : ∀ᶠ (T : ℝ) in atTop, C₁ * (1 + T) * Real.exp (-Real.pi * T) ≤ 1 :=
    ((by simpa using hexp_tend.const_mul C₁ :
      Tendsto (fun T : ℝ => C₁ * ((1 + T) * Real.exp (-Real.pi * T))) atTop (𝓝 0)).eventually
      (Iio_mem_nhds one_pos)).mono fun T hT => by
      have : C₁ * ((1 + T) * Real.exp (-Real.pi * T)) ≤ 1 := le_of_lt hT
      linarith
  have hev_small2 : ∀ᶠ (T : ℝ) in atTop, C₂ * (1 + T) * Real.exp (-Real.pi * T) ≤ 1 :=
    ((by simpa using hexp_tend.const_mul C₂ :
      Tendsto (fun T : ℝ => C₂ * ((1 + T) * Real.exp (-Real.pi * T))) atTop (𝓝 0)).eventually
      (Iio_mem_nhds one_pos)).mono fun T hT => by
      have : C₂ * ((1 + T) * Real.exp (-Real.pi * T)) ≤ 1 := le_of_lt hT
      linarith
  have hev_log : ∀ᶠ (T : ℝ) in atTop,
      (96 * muStar / Real.pi) * (Real.log (2 * T / xiStar) + Real.pi) ≤ (κ_mid / 2) * T := by
    have hdiv0 : Tendsto (fun T : ℝ =>
        ((96 * muStar / Real.pi) * (Real.log (2 * T / xiStar) + Real.pi)) / T) atTop (𝓝 0) := by
      have heq : (fun T : ℝ =>
          ((96 * muStar / Real.pi) * (Real.log (2 * T / xiStar) + Real.pi)) / T) =ᶠ[atTop]
          (fun T : ℝ =>
          (96 * muStar / Real.pi) * (Real.log T / T + (Real.log (2 / xiStar) + Real.pi) / T)) := by
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T hT
        rw [show 2 * T / xiStar = (2 / xiStar) * T by ring,
          Real.log_mul (by positivity [xiStar_pos]) hT.ne']
        ring
      refine Tendsto.congr' heq.symm ?_
      have h0 := hlog_tend.add
        ((tendsto_const_nhds (x := Real.log (2 / xiStar) + Real.pi)).div_atTop tendsto_id)
      simpa using tendsto_const_nhds.mul h0
    filter_upwards [hdiv0.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < κ_mid / 2)),
      Ioi_mem_atTop (0 : ℝ)] with T h1 hT
    have h1le : ((96 * muStar / Real.pi) * (Real.log (2 * T / xiStar) + Real.pi)) / T ≤ κ_mid / 2 :=
      le_of_lt (by simpa using h1)
    rwa [div_le_iff₀ hT] at h1le
  have hev_mu : ∀ᶠ (T : ℝ) in atTop, 2 * muStar + 2 ≤ (Real.pi / 6) * T :=
    (eventually_ge_atTop ((2 * muStar + 2) / (Real.pi / 6))).mono fun T hT => by
      rw [div_le_iff₀ (by positivity [Real.pi_pos])] at hT; linarith
  have h_all : ∀ᶠ (T : ℝ) in atTop,
      T_mid ≤ T ∧ 4 ≤ T ∧
      2 * muStar + 2 ≤ (Real.pi / 6) * T ∧
      C₁ * (1 + T) * Real.exp (-Real.pi * T) ≤ 1 ∧
      C₂ * (1 + T) * Real.exp (-Real.pi * T) ≤ 1 ∧
      (96 * muStar / Real.pi) * (Real.log (2 * T / xiStar) + Real.pi) ≤ (κ_mid / 2) * T :=
    (eventually_ge_atTop T_mid).and ((eventually_ge_atTop 4).and
      (hev_mu.and (hev_small1.and (hev_small2.and hev_log))))
  obtain ⟨T_min₀, hT_min₀⟩ := eventually_atTop.mp h_all
  let T_min := max T_min₀ 4
  refine ⟨T_min, by linarith [le_max_right T_min₀ 4], 12 * muStar / Real.pi, by positivity [muStar_pos, Real.pi_pos],
    Real.pi / 12, by positivity [Real.pi_pos], κ_mid / 2, by positivity,
    fun T₀ hT₀ μ_b hμ => ?_⟩
  obtain ⟨hT_mid_le, hT4, hT_mu, hC1_bd, hC2_bd, hlog_bd⟩ := hT_min₀ T₀ (le_trans (le_max_left _ _) hT₀)
  have hT2 : 2 ≤ T₀ := by linarith
  have hBtau_lb : T₀ / 2 ≤ chartBTau T₀ := by
    unfold chartBTau
    have : 0 ≤ Real.log 2 / (2 * Real.pi) :=
      div_nonneg (Real.log_nonneg (by norm_num)) (by positivity [Real.pi_pos])
    linarith
  have hBtau_ub : chartBTau T₀ ≤ T₀ := by
    unfold chartBTau
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hdiv : Real.log 2 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity [Real.pi_pos])]; linarith [Real.pi_gt_three]
    linarith
  let g : ℝ → ℝ := fun x => (chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ))).re
  have hg_deriv : ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      HasDerivAt g (deriv chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ))).re x := by
    intro x hx
    have hx1 : ((x : ℂ) - Complex.I * (T₀ : ℂ)).re ≤ 1 := by simp; linarith [hx.2]
    have hx0 : 0 ≤ ((x : ℂ) - Complex.I * (T₀ : ℂ)).re := by simp; exact hx.1
    have hd := (analyticAt_chartOmega hx0 hx1).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun t : ℝ => (t : ℂ) - Complex.I * (T₀ : ℂ)) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const (Complex.I * (T₀ : ℂ))
    simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd.comp x hline)
  have hg_cont : ContinuousOn g (Icc 0 (1 / 2)) := fun x hx =>
    (hg_deriv x hx).continuousAt.continuousWithinAt
  have hg_slope : ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      (deriv chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ))).re ≤ -(Real.pi / 6) * T₀ := by
    intro x hx
    have hconj_eq : (x : ℂ) - Complex.I * (T₀ : ℂ) =
        starRingEnd ℂ ((x : ℂ) + Complex.I * (T₀ : ℂ)) := by apply Complex.ext <;> simp
    have hconj_d : deriv chartOmega ((x : ℂ) - Complex.I * (T₀ : ℂ)) =
        starRingEnd ℂ (deriv chartOmega ((x : ℂ) + Complex.I * (T₀ : ℂ))) := by
      rw [hconj_eq]; exact deriv_chartOmega_conj' (by simp; exact hx.1) (by simp; linarith [hx.2])
    rw [hconj_d, Complex.conj_re]
    have hL := hOm'_large hx.1 hx.2 hT2
    have hre := (Complex.abs_re_le_norm _).trans hL
    have hre_sub : |(deriv chartOmega ((x : ℂ) + Complex.I * (T₀ : ℂ))).re +
        (2 * Real.pi / 3) * chartBTau T₀| ≤ C₂ * (1 + T₀) * Real.exp (-Real.pi * T₀) := by
      simpa [Complex.sub_re] using hre
    have h1 := (abs_le.mp hre_sub).2
    have hpi3 := Real.pi_gt_three
    nlinarith
  have hg_anti : StrictAntiOn g (Icc 0 (1 / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 (1 / 2)) hg_cont fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hg_deriv x ⟨hx.1.le, hx.2.le⟩).deriv]
    have hneg : -(Real.pi / 6) * T₀ < 0 := by nlinarith [Real.pi_pos]
    exact (hg_slope x ⟨hx.1.le, hx.2.le⟩).trans_lt hneg
  have hg_half : g (1 / 2) = 0 := by
    dsimp [g]
    have h12 : (((1 / 2 : ℝ) : ℂ) - Complex.I * (T₀ : ℂ)) =
        (1 / 2 : ℂ) + Complex.I * ((-T₀ : ℝ) : ℂ) := by push_cast; ring
    rw [h12, chartOmega_midline_nonpos (by linarith)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, sub_zero, mul_zero]
  have hg_zero : μ_b < g 0 := by
    have hL := hOm_large (x := 0) le_rfl (by norm_num) hT2
    have hconj_eq : ((0 : ℝ) : ℂ) - Complex.I * (T₀ : ℂ) =
        starRingEnd ℂ (((0 : ℝ) : ℂ) + Complex.I * (T₀ : ℂ)) := by apply Complex.ext <;> simp
    have hOm_conj : chartOmega (((0 : ℝ) : ℂ) - Complex.I * (T₀ : ℂ)) =
        starRingEnd ℂ (chartOmega (((0 : ℝ) : ℂ) + Complex.I * (T₀ : ℂ))) := by
      rw [hconj_eq]; exact chartOmega_conj (by simp) (by simp)
    have hre_sub : |g 0 - (2 * Real.pi / 3) * chartBTau T₀ * (1 / 2)| ≤
        C₁ * (1 + T₀) * Real.exp (-Real.pi * T₀) := by
      simp only [g, Complex.ofReal_zero, zero_add] at hOm_conj ⊢
      rw [hOm_conj, Complex.conj_re]
      have hre := (Complex.abs_re_le_norm _).trans hL
      convert hre using 2
      simp only [Complex.ofReal_zero, zero_add, Complex.sub_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
        sub_zero, sq]
    have h1 := (abs_le.mp hre_sub).1
    have h2 : 2 * muStar < (Real.pi / 3) * chartBTau T₀ - 1 := by
      have hpi3 := Real.pi_gt_three
      nlinarith [hμ.2]
    linarith [hμ.2]
  have hivt : μ_b ∈ g '' Icc 0 (1 / 2) := by
    have hsub := intermediate_value_Icc' (a := (0 : ℝ)) (b := 1 / 2) (by norm_num) hg_cont
    exact hsub ⟨by rw [hg_half]; linarith [muStar_pos, hμ.1], hg_zero.le⟩
  obtain ⟨x_L, hxL_mem, hxL_eq⟩ := hivt
  have hxL_ne0 : x_L ≠ 0 := by
    intro h0; rw [h0] at hxL_eq; linarith
  have hxL_ne_half : x_L ≠ 1 / 2 := by
    intro h12; rw [h12, hg_half] at hxL_eq; linarith [muStar_pos, hμ.1]
  have hxL_ioo : x_L ∈ Ioo (0 : ℝ) (1 / 2) :=
    ⟨lt_of_le_of_ne hxL_mem.1 (Ne.symm hxL_ne0), lt_of_le_of_ne hxL_mem.2 hxL_ne_half⟩
  have hxL_width : 1 / 2 - x_L ≤ (12 * muStar / Real.pi) / T₀ := by
    let hfun : ℝ → ℝ := fun x => g x + (Real.pi / 6) * T₀ * x
    have hh_anti : AntitoneOn hfun (Icc x_L (1 / 2)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc x_L (1 / 2)) ?_ ?_ ?_
      · exact hg_cont.mono (Icc_subset_Icc hxL_mem.1 le_rfl) |>.add (by fun_prop)
      · intro x hx
        exact ((hg_deriv x (Icc_subset_Icc hxL_mem.1 le_rfl (interior_subset hx))).add
          (((hasDerivAt_id x).const_mul ((Real.pi / 6) * T₀)).congr_deriv
            (mul_one _))).differentiableAt.differentiableWithinAt
      · intro x hx
        have hxm := Icc_subset_Icc hxL_mem.1 le_rfl (interior_subset hx)
        have hd := (hg_deriv x hxm).add
          (((hasDerivAt_id x).const_mul ((Real.pi / 6) * T₀)).congr_deriv (mul_one _))
        rw [show hfun = g + fun y => (Real.pi / 6) * T₀ * id y by rfl, hd.deriv]
        linarith [hg_slope x hxm]
    have hdiff := hh_anti ⟨le_rfl, hxL_mem.2⟩ ⟨hxL_mem.2, le_rfl⟩ hxL_mem.2
    dsimp [hfun] at hdiff
    rw [hg_half, hxL_eq] at hdiff
    have hpos_den : 0 < (Real.pi / 6) * T₀ := by positivity [Real.pi_pos]
    rw [le_div_iff₀ (by linarith)]
    have hmul : (1 / 2 - x_L) * ((Real.pi / 6) * T₀) ≤ 2 * muStar := by linarith [hμ.2]
    have hpi := Real.pi_pos
    calc (1 / 2 - x_L) * T₀ = (6 / Real.pi) * ((1 / 2 - x_L) * ((Real.pi / 6) * T₀)) := by
          field_simp [hpi.ne']
      _ ≤ (6 / Real.pi) * (2 * muStar) := by gcongr
      _ = 12 * muStar / Real.pi := by ring
  have hxL_im : (Real.pi / 12) * T₀ ^ 2 ≤
      (chartOmega ((x_L : ℂ) - Complex.I * (T₀ : ℂ))).im := by
    have hconj_eq : (x_L : ℂ) - Complex.I * (T₀ : ℂ) =
        starRingEnd ℂ ((x_L : ℂ) + Complex.I * (T₀ : ℂ)) := by apply Complex.ext <;> simp
    have hOm_conj : chartOmega ((x_L : ℂ) - Complex.I * (T₀ : ℂ)) =
        starRingEnd ℂ (chartOmega ((x_L : ℂ) + Complex.I * (T₀ : ℂ))) := by
      rw [hconj_eq]; exact chartOmega_conj (by simp; exact hxL_mem.1) (by simp; linarith [hxL_mem.2])
    have hL := hOm_large hxL_mem.1 hxL_mem.2 hT2
    have him_sub : |(chartOmega ((x_L : ℂ) - Complex.I * (T₀ : ℂ))).im -
        (2 * Real.pi / 3) * (chartBTau T₀ ^ 2 + x_L * (1 - x_L) / 4)| ≤
        C₁ * (1 + T₀) * Real.exp (-Real.pi * T₀) := by
      rw [hOm_conj, Complex.conj_im, ← neg_sub, abs_neg]
      have him := (Complex.abs_im_le_norm _).trans hL
      convert him using 2
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_zero, zero_sub]
      ring
    have h1 := (abs_le.mp him_sub).1
    have hxx : 0 ≤ x_L * (1 - x_L) / 4 := by nlinarith [hxL_mem.1, hxL_mem.2]
    have hsq : T₀ ^ 2 / 4 ≤ chartBTau T₀ ^ 2 := by nlinarith
    have hpi3 := Real.pi_gt_three
    nlinarith
  have hPhi_bd : ∀ x ∈ Icc x_L (1 / 2),
      (chartPhiV ((x : ℂ) - Complex.I * (T₀ : ℂ)) (xiStar : ℂ)).re ≤ -(κ_mid / 2) * T₀ := by
    have hmid_val : (chartPhiV ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ)) (xiStar : ℂ)).re ≤
        -κ_mid * T₀ := by
      rw [re_chartPhiV_midline_even T₀ xiStar_pos]
      exact hmid_lin T₀ hT_mid_le
    intro x hx
    exact junction_phi_line_bound hT2 hT4 hBtau_lb hBtau_ub
      (fun {y} hy0 hy1 => (hOm'_large hy0 hy1 hT2).trans hC2_bd)
      hxL_mem.1 hxL_width hx hmid_val hlog_bd
  refine ⟨x_L, ⟨hxL_ioo, hxL_eq, hxL_width, hxL_im, hPhi_bd⟩, fun y hy => ?_⟩
  exact hg_anti.injOn ⟨hy.1.1.le, hy.1.2.le⟩ hxL_mem (hy.2.1.trans hxL_eq.symm)

/-- **§J7 Asymptotic & Strip Bounds Bundle** (`lower_o1_two_edge.tex`, §J7, eq. `vlo:large` and lines 618, 630–634):
collects the large-height asymptotics for `b, q, ω'`, global strip bounds for `log(b/q), ω, ω', Υ`,
and zero characterization `ω(ζ) = 0 ↔ ζ = 1/2`. -/
theorem lemma_J7_asymptotics :
    ((∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 2 ≤ τ →
      ‖chartB ((x : ℂ) + Complex.I * (τ : ℂ)) -
          ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))‖ ≤
        (12 / Real.pi) * Real.exp (-Real.pi * τ)) ∧
     (∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 2 ≤ τ →
      ‖chartQ ((x : ℂ) + Complex.I * (τ : ℂ)) -
          (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖ ≤
        (2 / Real.pi) * Real.exp (-Real.pi * τ))) ∧
    (∃ C > (0 : ℝ), ∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 2 ≤ τ →
      ‖deriv chartOmega ((x : ℂ) + Complex.I * (τ : ℂ)) -
          (-((2 * Real.pi / 3 * chartBTau τ : ℝ) : ℂ) -
            ((Real.pi / 3 * (1 / 2 - x) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (1 + τ) * Real.exp (-Real.pi * τ)) ∧
    (∃ C > (0 : ℝ), ∀ ζ ∈ stripClosed, ‖chartLogBQ ζ‖ ≤ C) ∧
    (∃ C > (0 : ℝ), ∀ ζ ∈ stripClosed, ‖chartOmega ζ‖ ≤ C * (1 + ζ.im ^ 2)) ∧
    (∃ C > (0 : ℝ), ∀ ζ ∈ stripClosed, ‖deriv chartOmega ζ‖ ≤ C * (1 + |ζ.im|)) ∧
    (∃ C > (0 : ℝ), ∀ ζ ∈ stripClosed, ‖chartUpsilon ζ‖ ≤ C * (1 + ζ.im ^ 2)) ∧
    (∀ {ζ : ℂ}, ζ ∈ stripClosed → (chartOmega ζ = 0 ↔ ζ = 1 / 2)) :=
  ⟨⟨chartB_large_height, chartQ_large_height⟩,
   deriv_chartOmega_large_height,
   chartLogBQ_bounded,
   chartOmega_strip_bound,
   deriv_chartOmega_strip_bound,
   chartUpsilon_strip_bound,
   fun hζ => chartOmega_eq_zero_iff hζ⟩

/-- **§J7 Midline Geometry & Tail Decay Bundle** (`lower_o1_two_edge.tex`, §J7, lines 635–646):
exact `cosh(2X) = e^{πτ}` / `cos(2Y) = e^{-πτ}` midline formulas, strict monotonicity of `Im ω(1/2 + iτ)`,
quadratic lower bound `‖ω(1/2 + iτ)‖ ≥ c τ²`, and linear decay of `Re Φ*(1/2 ± iτ)`. -/
theorem lemma_J7_midline :
    (∀ {τ : ℝ}, 0 ≤ τ →
      Real.cosh (2 * midlineX τ) = Real.exp (Real.pi * τ) ∧
      Real.cos (2 * midlineY τ) = Real.exp (-Real.pi * τ)) ∧
    StrictAnti (fun τ : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im) ∧
    (∀ {τ : ℝ}, 0 ≤ τ →
      (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im = 0 ∧
      (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re < 0) ∧
    (∃ c > (0 : ℝ), ∀ τ : ℝ, c * τ ^ 2 ≤ ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖) ∧
    StrictAntiOn (fun τ : ℝ => (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re) (Ici 0) ∧
    (∃ T_min > (3 : ℝ), ∀ T₀ ≥ T_min, ∃ d₀ d₁ : ℝ, 0 < d₀ ∧ 0 < d₁ ∧
      ∀ τ ≥ T₀,
        (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re ≤ -d₀ - d₁ * (τ - T₀)) :=
  ⟨midline_cosh_cos_eq,
   im_chartOmega_midline_strictAnti,
   deriv_chartOmega_midline_real_neg,
   norm_chartOmega_midline_ge,
   re_chartPhiV_midline_strictAnti,
   re_chartPhiV_midline_tail_bound⟩

/-- **§J7 Junction `x_L` at Height `-T₀`** (`lower_o1_two_edge.tex`, §J7, lines 727–735). -/
abbrev lemma_J7_junction := @existsUnique_junction_xL

/-- info: 'FormalResearch.ModularBootstrap.ChartGeometry.lemma_J7_asymptotics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ChartGeometry.lemma_J7_asymptotics

/-- info: 'FormalResearch.ModularBootstrap.ChartGeometry.lemma_J7_midline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ChartGeometry.lemma_J7_midline

/-- info: 'FormalResearch.ModularBootstrap.ChartGeometry.existsUnique_junction_xL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ChartGeometry.existsUnique_junction_xL

end FormalResearch.ModularBootstrap.ChartGeometry