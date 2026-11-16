module

public import FormalResearch.Special.AiryEnvelopeRot

/-!
# `Ai` and `Ai'` on `ℂ`: the envelope theorem in root coordinates

`airy_sq_envelope` and `airy_deriv_sq_envelope`: for all `w` with `Re w ≥ 0`,

* `‖Ai(w²)‖ ≤ 3 (1 + |w|²)^{-1/4} exp(-(2/3) Re w³)`,
* `‖Ai'(w²)‖ ≤ 5 (1 + |w|²)^{1/4} exp(-(2/3) Re w³)`.

See `AiryEnvelopeRot` for the case split and `AiryEnvelope` for the statement in terms of `z = w²` and
the principal power `z^{3/2} = w³`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma airy_rot_norm_le (z : ℂ) :
    ‖airyAiC z‖ ≤ ‖airyAiC (airyOmega * z)‖ + ‖airyAiC (airyOmega ^ 2 * z)‖ := by
  have hrot := airyAiC_rotation z
  have : airyAiC z = -(airyOmega * airyAiC (airyOmega * z) +
      airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z)) := by linear_combination hrot
  rw [this, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_airyOmega, norm_airyOmega_sq, one_mul, one_mul]

/-- The derivative of the rotation identity. -/
lemma airyAiC_rotation_deriv (z : ℂ) :
    deriv airyAiC z + airyOmega ^ 2 * deriv airyAiC (airyOmega * z) +
      airyOmega ^ 4 * deriv airyAiC (airyOmega ^ 2 * z) = 0 := by
  have hf : (fun z : ℂ => airyAiC z + airyOmega * airyAiC (airyOmega * z) +
      airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z)) = fun _ => 0 := funext airyAiC_rotation
  have h0 : HasDerivAt airyAiC (deriv airyAiC z) z :=
    differentiable_airyAiC.differentiableAt.hasDerivAt
  have h1 := ((isAirySol_airyAiC_rot (a := airyOmega) airyOmega_cube z).1).const_mul airyOmega
  have h2 := ((isAirySol_airyAiC_rot (a := airyOmega ^ 2) (by
      rw [← pow_mul, mul_comm, pow_mul, airyOmega_cube, one_pow]) z).1).const_mul (airyOmega ^ 2)
  have hsum := (h0.add h1).add h2
  have hc : HasDerivAt (fun _ : ℂ => (0 : ℂ)) 0 z := hasDerivAt_const z 0
  rw [← hf] at hc
  have := hc.unique hsum
  rw [this]
  ring

lemma airy_rot_deriv_norm_le (z : ℂ) :
    ‖deriv airyAiC z‖ ≤ ‖deriv airyAiC (airyOmega * z)‖ + ‖deriv airyAiC (airyOmega ^ 2 * z)‖ := by
  have hrot := airyAiC_rotation_deriv z
  have : deriv airyAiC z = -(airyOmega ^ 2 * deriv airyAiC (airyOmega * z) +
      airyOmega ^ 4 * deriv airyAiC (airyOmega ^ 2 * z)) := by linear_combination hrot
  rw [this, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_airyOmega_sq, norm_pow, norm_airyOmega, one_pow, one_mul, one_mul]

private lemma exp_le_of_nonpos_aux {R : ℝ} (hR : R ≤ 0) :
    Real.exp (-(2 / 3) * (-R)) ≤ Real.exp (-(2 / 3) * R) :=
  Real.exp_le_exp.mpr (by linarith)

/-- **Envelope for `Ai` in root coordinates**: for `Re w ≥ 0`,
`‖Ai(w²)‖ (1 + |w|²)^{1/4} ≤ 3 exp(-(2/3) Re w³)`. -/
theorem airy_sq_envelope {w : ℂ} (hw : 0 ≤ w.re) :
    ‖airyAiC (w ^ 2)‖ * (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) ≤ 3 * Real.exp (-(2 / 3) * (w ^ 3).re) := by
  have hE := Real.exp_pos (-(2 / 3) * (w ^ 3).re)
  by_cases h1 : ‖w‖ ≤ 1
  · exact airy_small h1
  rw [not_le] at h1
  by_cases hA : ‖w‖ / 2 ≤ w.re
  · exact (airy_sectorA h1.le hA).trans (by linarith)
  rw [not_le] at hA
  obtain ⟨u₁, u₂, hn1, hr1, hs1, hn2, hr2, hs2, hcube, hR⟩ := airy_sectorB_roots hw hA
  have e1 := airy_sectorA (w := u₁) (by rw [hn1]; exact h1.le) (by rw [hn1]; exact hr1)
  have e2 := airy_sectorA (w := u₂) (by rw [hn2]; exact h1.le) (by rw [hn2]; exact hr2)
  rw [hs1, hn1] at e1
  rw [hs2, hn2] at e2
  have hq0 : 0 < (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hz := airy_rot_norm_le (w ^ 2)
  have hle : ‖airyAiC (w ^ 2)‖ * (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) ≤
      1 / 2 * Real.exp (-(2 / 3) * (u₁ ^ 3).re) + 1 / 2 * Real.exp (-(2 / 3) * (u₂ ^ 3).re) := by
    have := mul_le_mul_of_nonneg_right hz hq0.le
    linarith
  rcases hcube with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · rw [c1, c2] at hle
    have := exp_le_of_nonpos_aux hR
    linarith
  · rw [c1, c2] at hle
    have := exp_le_of_nonpos_aux hR
    linarith

/-- Derivative, sector `Re w ≥ |w|/2`, `|w| ≥ 1`: constant `3/2`. -/
lemma airy_deriv_sectorA {w : ℂ} (h1 : 1 ≤ ‖w‖) (ha : ‖w‖ / 2 ≤ w.re) :
    ‖deriv airyAiC (w ^ 2)‖ ≤
      3 / 2 * (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (w ^ 3).re) := by
  have hapos : 0 < w.re := by linarith
  have hN := sq_norm_eq w
  have hN0 := norm_nonneg w
  set a := w.re with hadef
  set b := w.im with hbdef
  set N := ‖w‖ with hNdef
  set q := (1 + N ^ 2) ^ (1 / 4 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hq4 : q ^ 4 = 1 + N ^ 2 := rpow_quarter_pow_four (by positivity)
  have hq2 : N ≤ q ^ 2 := le_of_sq_le_sq' (by positivity) (by nlinarith)
  have hq1 : 1 ≤ q := by
    by_contra h; rw [not_le] at h
    have := pow_lt_one₀ hq0.le h (four_ne_zero)
    nlinarith
  have hπ := Real.pi_gt_d2
  have hπ' := Real.pi_lt_d2
  have hb := airy_deriv_sq_norm_le_sqrt hapos
  have hX : (a + |b|) * √(π / a) ≤ 6 * q := by
    refine le_of_sq_le_sq' (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), ← mul_div_assoc, div_le_iff₀ hapos]
    have h2 : (a + |b|) ^ 2 ≤ 2 * N ^ 2 := by nlinarith [sq_abs b, sq_nonneg (a - |b|)]
    have h3 : N * q ^ 2 ≤ q ^ 2 * q ^ 2 := by nlinarith [sq_nonneg q]
    have h4 : (a + |b|) ^ 2 * π ≤ 2 * N ^ 2 * π := mul_le_mul_of_nonneg_right h2 (by positivity)
    have h5 : N ^ 2 ≤ N * q ^ 2 := by nlinarith
    nlinarith [mul_pos hq0 hq0, mul_nonneg hN0 (sq_nonneg q)]
  have hY : 1 / a ≤ 2 * q := by
    rw [div_le_iff₀ hapos]; nlinarith
  have hbr : (a + |b|) * √(π / a) + 1 / a ≤ 8 * q := by linarith
  calc ‖deriv airyAiC (w ^ 2)‖
      ≤ 1 / (2 * π) * (Real.exp (-(2 / 3) * (w ^ 3).re) *
        ((a + |b|) * √(π / a) + 1 / a)) := hb
    _ ≤ 1 / (2 * π) * (Real.exp (-(2 / 3) * (w ^ 3).re) * (8 * q)) := by gcongr
    _ = (4 / π) * q * Real.exp (-(2 / 3) * (w ^ 3).re) := by field_simp; ring
    _ ≤ 3 / 2 * q * Real.exp (-(2 / 3) * (w ^ 3).re) := by
        have : 4 / π ≤ 3 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        gcongr

/-- Derivative, `|w| ≤ 1`: constant `5`. -/
lemma airy_deriv_small {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖deriv airyAiC (w ^ 2)‖ ≤
      5 * (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (w ^ 3).re) := by
  obtain ⟨hP, hy⟩ := airy_small_param hw
  have hb := airy_deriv_norm_le_free_param one_pos (w ^ 2)
  have hq1 := one_le_rpow_quarter (‖w‖ ^ 2) (by positivity)
  set q := (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ)
  have hexp : Real.exp (airyParamExp 1 (w ^ 2)) ≤ Real.exp (2 : ℝ) * Real.exp (-(2 / 3)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hR : Real.exp (-(2 / 3)) ≤ Real.exp (-(2 / 3) * (w ^ 3).re) :=
    Real.exp_le_exp.mpr (by nlinarith [re_cube_le_one hw])
  obtain ⟨hs1, hs2⟩ := sqrt_pi_bounds
  have hE2 := exp_two_le
  have hepos := Real.exp_pos (-(2 / 3) : ℝ)
  have hπ := Real.pi_gt_d2
  have hbr : (1 + |(w ^ 2).im| / (2 * 1)) * √(π / 1) + 1 / 1 ≤ 4 := by
    rw [div_one]; nlinarith [abs_nonneg (w ^ 2).im]
  have hbr0 : 0 ≤ (1 + |(w ^ 2).im| / (2 * 1)) * √(π / 1) + 1 / 1 := by positivity
  calc ‖deriv airyAiC (w ^ 2)‖
      ≤ 1 / (2 * π) * (Real.exp (airyParamExp 1 (w ^ 2)) *
          ((1 + |(w ^ 2).im| / (2 * 1)) * √(π / 1) + 1 / 1)) := by
        simpa using hb
    _ ≤ 1 / (2 * π) * ((Real.exp 2 * Real.exp (-(2 / 3))) * 4) := by gcongr
    _ = (2 / π * Real.exp 2) * Real.exp (-(2 / 3)) := by field_simp; ring
    _ ≤ 5 * Real.exp (-(2 / 3)) := by
        refine mul_le_mul_of_nonneg_right ?_ hepos.le
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
    _ ≤ 5 * 1 * Real.exp (-(2 / 3) * (w ^ 3).re) := by nlinarith
    _ ≤ 5 * q * Real.exp (-(2 / 3) * (w ^ 3).re) := by gcongr

/-- **Envelope for `Ai'` in root coordinates**: for `Re w ≥ 0`,
`‖Ai'(w²)‖ ≤ 5 (1 + |w|²)^{1/4} exp(-(2/3) Re w³)`. -/
theorem airy_deriv_sq_envelope {w : ℂ} (hw : 0 ≤ w.re) :
    ‖deriv airyAiC (w ^ 2)‖ ≤
      5 * (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (w ^ 3).re) := by
  have hE := Real.exp_pos (-(2 / 3) * (w ^ 3).re)
  have hq0 : 0 < (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  by_cases h1 : ‖w‖ ≤ 1
  · exact airy_deriv_small h1
  rw [not_le] at h1
  by_cases hA : ‖w‖ / 2 ≤ w.re
  · refine (airy_deriv_sectorA h1.le hA).trans ?_
    have := mul_pos hq0 hE
    nlinarith
  rw [not_le] at hA
  obtain ⟨u₁, u₂, hn1, hr1, hs1, hn2, hr2, hs2, hcube, hR⟩ := airy_sectorB_roots hw hA
  have e1 := airy_deriv_sectorA (w := u₁) (by rw [hn1]; exact h1.le) (by rw [hn1]; exact hr1)
  have e2 := airy_deriv_sectorA (w := u₂) (by rw [hn2]; exact h1.le) (by rw [hn2]; exact hr2)
  rw [hs1, hn1] at e1
  rw [hs2, hn2] at e2
  have hz := airy_rot_deriv_norm_le (w ^ 2)
  set q := (1 + ‖w‖ ^ 2) ^ (1 / 4 : ℝ)
  have hle : ‖deriv airyAiC (w ^ 2)‖ ≤
      3 / 2 * q * Real.exp (-(2 / 3) * (u₁ ^ 3).re) +
        3 / 2 * q * Real.exp (-(2 / 3) * (u₂ ^ 3).re) := by linarith
  have hqE := mul_pos hq0 hE
  rcases hcube with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · rw [c1, c2] at hle
    have := exp_le_of_nonpos_aux hR
    nlinarith [mul_le_mul_of_nonneg_left this hq0.le]
  · rw [c1, c2] at hle
    have := exp_le_of_nonpos_aux hR
    nlinarith [mul_le_mul_of_nonneg_left this hq0.le]

end FormalResearch.Special
