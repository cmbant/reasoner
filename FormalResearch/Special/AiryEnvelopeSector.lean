module

public import FormalResearch.Special.AiryEnvelopeParam
public import FormalResearch.Special.AiryRotation

/-!
# `Ai` on `ℂ`: the envelope bound in root coordinates

Every `z ∈ ℂ` is `w²` with `Re w ≥ 0` (`w` the principal square root), and then `z^{3/2} = w³`.  In the
coordinate `w` the free-parameter bound of `AiryEnvelopeParam` with the choice `c = Re w` is *exactly*
the envelope: the exponent `c³/3 - c Re z + (Im z)²/(4c)` equals `-(2/3) Re w³`
(`airyParamExp_sq`), which gives

`‖Ai(w²)‖ ≤ (1/(2√(π Re w))) exp(-(2/3) Re w³)`  for `Re w > 0`   (`airy_sq_norm_le_sqrt`).

The factor `(Re w)^{-1/2}` is `≲ |w|^{-1/2} = |z|^{-1/4}` in the sector `Re w ≥ |w|/2`, i.e. `|arg z| ≤ 2π/3`.
Near the negative axis (`|arg z| > 2π/3`) the rotation identity `Ai(z) = -ω Ai(ωz) - ω² Ai(ω²z)` moves both
terms back into the good sector, with `(ωz)^{3/2} = z^{3/2}` and `(ω²z)^{3/2} = -z^{3/2}`
(`airy_sq_envelope`: `‖Ai(w²)‖ (1+|w|²)^{1/4} ≤ 3 exp(-(2/3) Re w³)` for all `Re w ≥ 0`).
The same is done for `Ai'` (`airy_deriv_sq_envelope`, constant `5`, factor `(1+|w|²)^{-1/4}`).
The translation to principal powers `z^{3/2}` is in `AiryEnvelope`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

section Algebra

lemma sqrt3_sq : √(3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma airyOmega_sq_eq : airyOmega ^ 2 = ⟨-1 / 2, -(√3 / 2)⟩ := by
  apply Complex.ext <;> simp [airyOmega, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt3_sq]

lemma norm_airyOmega : ‖airyOmega‖ = 1 := by
  rw [airyOmega_eq_exp]
  have : (2 * π * I / 3 : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_airyOmega_sq : ‖airyOmega ^ 2‖ = 1 := by
  rw [norm_pow, norm_airyOmega, one_pow]

lemma airyOmega_pow_four : airyOmega ^ 4 = airyOmega := by
  rw [show 4 = 3 + 1 by norm_num, pow_add, airyOmega_cube, one_mul, pow_one]

lemma airyOmega_pow_six : airyOmega ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, airyOmega_cube, one_pow]

lemma sq_norm_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma re_sq (w : ℂ) : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
  simp [pow_two, Complex.mul_re]

lemma im_sq (w : ℂ) : (w ^ 2).im = 2 * w.re * w.im := by
  simp [pow_two, Complex.mul_im]; ring

lemma re_cube (w : ℂ) : (w ^ 3).re = w.re ^ 3 - 3 * w.re * w.im ^ 2 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring

lemma rpow_quarter_pow_four {t : ℝ} (ht : 0 ≤ t) : ((1 + t) ^ (1 / 4 : ℝ)) ^ 4 = 1 + t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num

end Algebra

lemma airyParamExp_sq {w : ℂ} (hw : 0 < w.re) :
    airyParamExp w.re (w ^ 2) = -(2 / 3) * (w ^ 3).re := by
  unfold airyParamExp
  rw [re_sq, im_sq, re_cube]
  field_simp
  ring

/-- `‖Ai(w²)‖ ≤ (1/(2π)) √(π/Re w) exp(-(2/3) Re w³)` for `Re w > 0`: the free-parameter bound with
`c = Re w`. -/
theorem airy_sq_norm_le_sqrt {w : ℂ} (hw : 0 < w.re) :
    ‖airyAiC (w ^ 2)‖ ≤ 1 / (2 * π) * (Real.exp (-(2 / 3) * (w ^ 3).re) * √(π / w.re)) := by
  have := airy_norm_le_free_param hw (w ^ 2)
  rwa [airyParamExp_sq hw] at this

/-- `‖Ai'(w²)‖ ≤ (1/(2π)) exp(-(2/3) Re w³) ((Re w + |Im w|) √(π/Re w) + 1/Re w)` for `Re w > 0`. -/
theorem airy_deriv_sq_norm_le_sqrt {w : ℂ} (hw : 0 < w.re) :
    ‖deriv airyAiC (w ^ 2)‖ ≤ 1 / (2 * π) * (Real.exp (-(2 / 3) * (w ^ 3).re) *
      ((w.re + |w.im|) * √(π / w.re) + 1 / w.re)) := by
  have := airy_deriv_norm_le_free_param hw (w ^ 2)
  rw [airyParamExp_sq hw, im_sq] at this
  have h : |2 * w.re * w.im| / (2 * w.re) = |w.im| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * w.re)]
    field_simp
  rwa [h] at this

/-- Sector `Re w ≥ |w|/2`, `|w| ≥ 1`: constant `1/2`. -/
lemma airy_sectorA {w : ℂ} (h1 : 1 ≤ ‖w‖) (ha : ‖w‖ / 2 ≤ w.re) :
    ‖airyAiC (w ^ 2)‖ * (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) ≤ 1 / 2 * Real.exp (-(2 / 3) * (w ^ 3).re) := by
  have hapos : 0 < w.re := by linarith
  set a := w.re with hadef
  set q := (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hq4 : q ^ 4 = 1 + ‖w‖ ^ 2 := rpow_quarter_pow_four (by positivity)
  have hq4' : q ^ 4 ≤ 8 * a ^ 2 := by
    rw [hq4]; nlinarith
  have hπ : 3 < π := Real.pi_gt_three
  have hq2 : q ^ 2 ≤ π * a := by
    by_contra h
    rw [not_le] at h
    have h2 := pow_lt_pow_left₀ h (by positivity) (two_ne_zero)
    have h3 : (q ^ 2) ^ 2 = q ^ 4 := by ring
    have h4 : 0 < a ^ 2 := by positivity
    have h5 : (9 : ℝ) < π ^ 2 := by nlinarith
    have h6 := mul_lt_mul_of_pos_right h5 h4
    have h7 : (π * a) ^ 2 = π ^ 2 * a ^ 2 := by ring
    nlinarith
  have hmain : √(π / a) * q ≤ π := by
    have h0 : 0 ≤ √(π / a) * q := by positivity
    have hsq : (√(π / a) * q) ^ 2 = π / a * q ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have : π / a * q ^ 2 ≤ π ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hapos]; nlinarith
    nlinarith
  have hb := airy_sq_norm_le_sqrt hapos
  calc ‖airyAiC (w ^ 2)‖ * q
      ≤ 1 / (2 * π) * (Real.exp (-(2 / 3) * (w ^ 3).re) * √(π / a)) * q :=
        mul_le_mul_of_nonneg_right hb hq0.le
    _ = 1 / (2 * π) * Real.exp (-(2 / 3) * (w ^ 3).re) * (√(π / a) * q) := by ring
    _ ≤ 1 / (2 * π) * Real.exp (-(2 / 3) * (w ^ 3).re) * π :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 1 / 2 * Real.exp (-(2 / 3) * (w ^ 3).re) := by field_simp

end FormalResearch.Special
