module

public import FormalResearch.Special.AiryEnvelopeSector

/-!
# `Ai` and `Ai'` on `ℂ`: envelope in root coordinates, all sectors

For `w` with `Re w ≥ 0` (so `z = w²` runs over `ℂ`, `z^{3/2} = w³`):

* `airy_sq_envelope`: `‖Ai(w²)‖ (1 + |w|²)^{1/4} ≤ 3 exp(-(2/3) Re w³)`;
* `airy_deriv_sq_envelope`: `‖Ai'(w²)‖ ≤ 5 (1 + |w|²)^{1/4} exp(-(2/3) Re w³)`.

Proof: `|w| ≤ 1` by the free-parameter bound with `c = 1`; `|w| ≥ 1` and `Re w ≥ |w|/2` (`|arg z| ≤ 2π/3`)
by `c = Re w` (`airy_sectorA`); and `|w| ≥ 1`, `Re w < |w|/2` (`2π/3 < |arg z| ≤ π`) by the rotation identity
`Ai(z) = -ω Ai(ωz) - ω² Ai(ω²z)` and its derivative: the two rotated arguments are squares of
`u₁, u₂` in the good sector with `Re u₁³, Re u₂³ = ± Re w³`, and `Re w³ ≤ 0` in this sector, so the
`exp(+(2/3) Re w³)` term is dominated by `exp(-(2/3) Re w³)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma exp_two_le : Real.exp 2 ≤ 7.39 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ ≤ 7.39 := by nlinarith

lemma sqrt_pi_bounds : 1.77 ≤ √π ∧ √π ≤ 2 := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_four
  have h0 : 0 ≤ √π := Real.sqrt_nonneg _
  have hsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  constructor <;> nlinarith

lemma airy_small_param {w : ℂ} (hw : ‖w‖ ≤ 1) :
    airyParamExp 1 (w ^ 2) ≤ 4 / 3 ∧ |(w ^ 2).im| ≤ 1 := by
  have hn : (w ^ 2).re ^ 2 + (w ^ 2).im ^ 2 ≤ 1 := by
    rw [← sq_norm_eq, norm_pow]
    have h0 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    nlinarith [sq_nonneg ‖w‖]
  have hx : -1 ≤ (w ^ 2).re := by nlinarith [sq_nonneg (w ^ 2).im]
  refine ⟨?_, ?_⟩
  · unfold airyParamExp
    nlinarith [mul_nonneg (by linarith : 0 ≤ (w ^ 2).re + 1) (by linarith : 0 ≤ (w ^ 2).re + 3)]
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (w ^ 2).re]

lemma re_cube_le_one {w : ℂ} (hw : ‖w‖ ≤ 1) : (w ^ 3).re ≤ 1 := by
  have := Complex.re_le_norm (w ^ 3)
  rw [norm_pow] at this
  have h0 := norm_nonneg w
  nlinarith [mul_nonneg h0 h0]

lemma rpow_quarter_le {w : ℂ} (hw : ‖w‖ ≤ 1) : (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) ≤ 6 / 5 := by
  have h4 := rpow_quarter_pow_four (t := ‖w‖ ^ 2) (by positivity)
  set q := (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  by_contra h
  rw [not_le] at h
  have h2 := pow_lt_pow_left₀ h (by norm_num) (four_ne_zero)
  nlinarith [norm_nonneg w]

lemma one_le_rpow_quarter (t : ℝ) (ht : 0 ≤ t) : 1 ≤ (1 + t) ^ (1 / 4 : ℝ) :=
  Real.one_le_rpow (by linarith) (by norm_num)

/-- `|w| ≤ 1`: constant `3`. -/
lemma airy_small {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖airyAiC (w ^ 2)‖ * (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) ≤ 3 * Real.exp (-(2 / 3) * (w ^ 3).re) := by
  obtain ⟨hP, -⟩ := airy_small_param hw
  have hb := airy_norm_le_free_param one_pos (w ^ 2)
  have hq := rpow_quarter_le hw
  have hq0 : 0 < (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  set q := (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ)
  have hexp : Real.exp (airyParamExp 1 (w ^ 2)) ≤ Real.exp (2 : ℝ) * Real.exp (-(2 / 3)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hR : Real.exp (-(2 / 3)) ≤ Real.exp (-(2 / 3) * (w ^ 3).re) :=
    Real.exp_le_exp.mpr (by nlinarith [re_cube_le_one hw])
  obtain ⟨hs1, hs2⟩ := sqrt_pi_bounds
  have hsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hE2 := exp_two_le
  have hepos := Real.exp_pos (-(2 / 3) : ℝ)
  have hπ : 0 < π := Real.pi_pos
  rw [div_one] at hb
  have h1 : ‖airyAiC (w ^ 2)‖ * q ≤
      1 / (2 * π) * (Real.exp 2 * Real.exp (-(2 / 3)) * √π) * (6 / 5) := by
    calc ‖airyAiC (w ^ 2)‖ * q ≤ 1 / (2 * π) * (Real.exp (airyParamExp 1 (w ^ 2)) * √π) * q :=
          mul_le_mul_of_nonneg_right hb hq0.le
      _ ≤ 1 / (2 * π) * (Real.exp 2 * Real.exp (-(2 / 3)) * √π) * (6 / 5) := by
          gcongr
  have h2 : 1 / (2 * π) * (Real.exp 2 * Real.exp (-(2 / 3)) * √π) * (6 / 5) ≤
      3 * Real.exp (-(2 / 3)) := by
    have : 1 / (2 * π) * √π = 1 / (2 * √π) := by
      have hr : 0 < √π := by linarith
      rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      nlinarith [hsq]
    calc 1 / (2 * π) * (Real.exp 2 * Real.exp (-(2 / 3)) * √π) * (6 / 5)
        = (Real.exp 2 * (6 / 5) * (1 / (2 * √π))) * Real.exp (-(2 / 3)) := by
          rw [← this]; ring
      _ ≤ 3 * Real.exp (-(2 / 3)) := by
          refine mul_le_mul_of_nonneg_right ?_ hepos.le
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith
  calc ‖airyAiC (w ^ 2)‖ * q ≤ 3 * Real.exp (-(2 / 3)) := h1.trans h2
    _ ≤ 3 * Real.exp (-(2 / 3) * (w ^ 3).re) := by gcongr


lemma le_of_sq_le_sq' {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hxy
  rw [not_le] at hxy
  nlinarith

lemma re_airyOmega_mul (w : ℂ) : (airyOmega * w).re = (-w.re - √3 * w.im) / 2 := by
  simp [airyOmega, Complex.mul_re]; ring

lemma re_airyOmega_sq_mul (w : ℂ) : (airyOmega ^ 2 * w).re = (-w.re + √3 * w.im) / 2 := by
  rw [airyOmega_sq_eq]; simp [Complex.mul_re]; ring

lemma sector_ineq {a b N s : ℝ} (hs : s * s = 3) (hs0 : 0 < s) (ha0 : 0 ≤ a) (hb : 0 ≤ b)
    (hab : s * a ≤ b) (hN : N ^ 2 = a ^ 2 + b ^ 2) :
    N / 2 ≤ (-a + s * b) / 2 ∧ N / 2 ≤ (a + s * b) / 2 := by
  constructor
  · have h1 : N ≤ s * b - a :=
      le_of_sq_le_sq' (by nlinarith) (by nlinarith [mul_nonneg hb (sub_nonneg.mpr hab)])
    linarith
  · have h1 : N ≤ a + s * b :=
      le_of_sq_le_sq' (by nlinarith) (by nlinarith [mul_nonneg hb ha0, mul_nonneg hb hb, mul_nonneg (mul_nonneg hb ha0) hs0.le])
    linarith

/-- In the sector `Re w < |w|/2` (`|arg z| > 2π/3`), the squares `ωz`, `ω²z` of `z = w²` are squares of two
points `u₁, u₂` with `|u_i| = |w|`, `Re u_i ≥ |w|/2` (the good sector) and `Re u_i³ = ± Re w³`; also
`Re w³ ≤ 0`. -/
lemma airy_sectorB_roots {w : ℂ} (ha0 : 0 ≤ w.re) (ha : w.re < ‖w‖ / 2) :
    ∃ u₁ u₂ : ℂ, ‖u₁‖ = ‖w‖ ∧ ‖w‖ / 2 ≤ u₁.re ∧ u₁ ^ 2 = airyOmega * w ^ 2 ∧
      ‖u₂‖ = ‖w‖ ∧ ‖w‖ / 2 ≤ u₂.re ∧ u₂ ^ 2 = airyOmega ^ 2 * w ^ 2 ∧
      (((u₁ ^ 3).re = (w ^ 3).re ∧ (u₂ ^ 3).re = -(w ^ 3).re) ∨
        ((u₁ ^ 3).re = -(w ^ 3).re ∧ (u₂ ^ 3).re = (w ^ 3).re)) ∧ (w ^ 3).re ≤ 0 := by
  have hN := sq_norm_eq w
  have hN0 := norm_nonneg w
  set a := w.re with hadef
  set b := w.im with hbdef
  set N := ‖w‖ with hNdef
  have hs := sqrt3_sq
  have hs0 : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hb2 : 3 * a ^ 2 < b ^ 2 := by nlinarith
  have hab : √3 * a ≤ |b| := by
    by_contra h
    rw [not_le] at h
    have : |b| ^ 2 < (√3 * a) ^ 2 := pow_lt_pow_left₀ h (abs_nonneg b) two_ne_zero
    rw [sq_abs] at this
    nlinarith
  have hR : (w ^ 3).re ≤ 0 := by
    rw [re_cube]
    nlinarith [mul_nonneg ha0 (sq_nonneg a)]
  have hω3 : airyOmega ^ 3 = 1 := airyOmega_cube
  have hω6 := airyOmega_pow_six
  have hω4 := airyOmega_pow_four
  rcases le_or_gt 0 b with hb | hb
  · refine ⟨airyOmega ^ 2 * w, -(airyOmega * w), ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR⟩
    · rw [norm_mul, norm_airyOmega_sq, one_mul]
    · rw [re_airyOmega_sq_mul]
      rw [abs_of_nonneg hb] at hab
      exact (sector_ineq hs hs0 ha0 hb hab hN).1
    · rw [mul_pow, ← pow_mul, hω4]
    · rw [norm_neg, norm_mul, norm_airyOmega, one_mul]
    · rw [Complex.neg_re, re_airyOmega_mul]
      rw [abs_of_nonneg hb] at hab
      have := (sector_ineq hs hs0 ha0 hb hab hN).2
      linarith
    · rw [neg_sq, mul_pow]
    · left
      constructor
      · rw [show (airyOmega ^ 2 * w) ^ 3 = airyOmega ^ 6 * w ^ 3 by ring, hω6, one_mul]
      · rw [show (-(airyOmega * w)) ^ 3 = -(airyOmega ^ 3 * w ^ 3) by ring, hω3, one_mul,
          Complex.neg_re]
  · refine ⟨-(airyOmega ^ 2 * w), airyOmega * w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR⟩
    · rw [norm_neg, norm_mul, norm_airyOmega_sq, one_mul]
    · rw [Complex.neg_re, re_airyOmega_sq_mul]
      rw [abs_of_neg hb] at hab
      have := (sector_ineq hs hs0 ha0 (by linarith : 0 ≤ -b) hab (by rw [hN]; ring)).2
      linarith
    · rw [neg_sq, mul_pow, ← pow_mul, hω4]
    · rw [norm_mul, norm_airyOmega, one_mul]
    · rw [re_airyOmega_mul]
      rw [abs_of_neg hb] at hab
      have := (sector_ineq hs hs0 ha0 (by linarith : 0 ≤ -b) hab (by rw [hN]; ring)).1
      linarith
    · rw [mul_pow]
    · right
      constructor
      · rw [show (-(airyOmega ^ 2 * w)) ^ 3 = -(airyOmega ^ 6 * w ^ 3) by ring, hω6, one_mul,
          Complex.neg_re]
      · rw [mul_pow, hω3, one_mul]

end FormalResearch.Special
