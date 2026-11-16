module

public import FormalResearch.Special.AiryZeroSecondOrderSaddle

/-!
# `Ai(-r²)` on the negative axis to relative order `r^{-9}`: the `u₂`-corrected modulus-phase form

Specialising `norm_airyAiC_sq_fourth_le` (`AiryZeroSecondOrderSaddle`) to `w = r e^{iπ/6}` (so `w³ = i r³`, `w⁶ = -r⁶`,
`ρ = Re w ≥ (5/6) r`) and using the rotation identity `Ai + iBi = (1 + √3 i) Ai(ω² ·)` exactly as in `AiryAsymChi`, one
gets for every `r > 0`, with `φ = (2/3) r³ - π/4`, `a = 1 - 385/(4608 r⁶)`, `t = 5/(48 r³)`:

* `airySO_chi_neg_sq`: `‖Ai(-r²) + i Bi(-r²) - (√π √r)^{-1} e^{-iφ} (a + i t)‖ ≤ (1/2)/(√r r⁹)`;
* **`airySO_Ai_neg_sq`** (the real part, DLMF 9.7.9 to `u₂`, with the `u₃` term replaced by an explicit remainder):
  `|Ai(-r²) - (√π √r)^{-1} (a cos φ + t sin φ)| ≤ (1/2)/(√r r⁹)`;
  `airySO_Bi_neg_sq` is the imaginary part (`b cos φ - a sin φ`).

In terms of `ξ = (2/3) r³`: `a = 1 - u₂/ξ²`, `u₂ = 385/10368`, `t = u₁/ξ`, `u₁ = 5/72`, and the remainder is `O(ξ^{-3})`
*without* the `u₃`-term being resolved: the point is that the `ξ^{-2}` term is real, so the imaginary part `t` of the
amplitude is correct to `O(ξ^{-3})`.  This is what makes the zeros of `Ai` computable to `O(ξ^{-3})` in phase (the
`u₂` term multiplies `cos φ`, which is `O(ξ^{-1})` at a zero).

Numerical check (mpmath, 30 digits, 596 points `r ∈ [0.5, 60]`, and `r = 100, 300`): `√r r⁹ |Ai(-r²) - main| ≤ 0.0724`
(the sup is attained for large `r` and equals `u₃ (3/2)³/√π = 0.0723...`, `u₃ = 85085/2239488`; the proved constant is `1/2`); and
at the zeros `a_n` (`n ≤ 400` and `n = 1000, 3000`) `|a cos φ + t sin φ| r⁹ / (√π/2) ≤ 0.145`, the quantity bounded in
`airyZero_phase_second`.

Proved here: everything stated.  **Not formalised:** `Ai'`, `Bi'` to this order; the `u₃` coefficient itself.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The leading terms of `2 e^{iπ/3} Ai(w²)` at `w = r e^{iπ/6}` with an arbitrary correction factor `Q`. -/
lemma airySO_chi_lead {r : ℝ} (hr : 0 < r) (Q : ℂ) :
    (1 + (√3 : ℝ) * I) * ((1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * negW r ^ 3) *
        ((π / negW r) ^ (1 / 2 : ℂ) * Q)) =
      ((1 / (√π * √r) : ℝ) : ℂ) * cexp (((-(2 / 3 * r ^ 3 - π / 4) : ℝ) : ℂ) * I) * Q := by
  rw [exp_negW_cube, sqrt_pi_div_negW hr, one_add_sqrt3_I]
  have hE : cexp (((π / 3 : ℝ) : ℂ) * I) * cexp (((-(2 / 3 * r ^ 3) : ℝ) : ℂ) * I) *
      cexp (((-(π / 12) : ℝ) : ℂ) * I) = cexp (((-(2 / 3 * r ^ 3 - π / 4) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [← hE]
  generalize cexp (((π / 3 : ℝ) : ℂ) * I) = E1
  generalize cexp (((-(2 / 3 * r ^ 3) : ℝ) : ℂ) * I) = E2
  generalize cexp (((-(π / 12) : ℝ) : ℂ) * I) = E3
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [Real.sqrt_div Real.pi_pos.le]
  have hπ' : (π : ℂ) = (√π : ℂ) * (√π : ℂ) := by exact_mod_cast hπ.symm
  have hT' : (√π : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hs' : (√r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  rw [hπ']
  field_simp

/-- At `w = r e^{iπ/6}`: `1 - 5/(48 w³) + 385/(4608 w⁶) = a + i t`. -/
lemma airySO_poly_negW {r : ℝ} (hr : 0 < r) :
    1 - 5 / (48 * negW r ^ 3) + 385 / (4608 * negW r ^ 6) =
      ((1 - 385 / (4608 * r ^ 6) : ℝ) : ℂ) + ((5 / (48 * r ^ 3) : ℝ) : ℂ) * I := by
  have h6 : negW r ^ 6 = (negW r ^ 3) ^ 2 := by ring
  rw [h6, negW_cube]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

lemma airySO_err_le {r ρ : ℝ} (hr : 0 < r) (hρ : 5 / 6 * r ≤ ρ) :
    2 * (1 / (2 * π) * (34459425 / 268738560 * (√(π / ρ) / ρ ^ 9))) ≤ 1 / 2 * (1 / (√r * r ^ 9)) := by
  have h9 := sqrt_div_pow_le hr hρ 9
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hm : 0 < √r * r ^ 9 := by positivity
  have hT := sqrtpi_ge
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hT0 : 0 < √π := by linarith
  calc 2 * (1 / (2 * π) * (34459425 / 268738560 * (√(π / ρ) / ρ ^ 9)))
      ≤ 2 * (1 / (2 * π) * (34459425 / 268738560 * (10 / 9 * (6 / 5) ^ 9 * √π / (√r * r ^ 9)))) := by gcongr
    _ = (34459425 / 268738560 * (10 / 9) * (6 / 5) ^ 9 / √π) * (1 / (√r * r ^ 9)) := by
        generalize √π = T at hπ hT0
        rw [← hπ]
        field_simp
    _ ≤ 1 / 2 * (1 / (√r * r ^ 9)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hT0]
        nlinarith

/-- **`χ = Ai + iBi` on the negative axis to `O(r^{-9})` in the variable `r = √y`**: for `r > 0`, with `φ = (2/3) r³ - π/4`,
`‖Ai(-r²) + i Bi(-r²) - (√π √r)^{-1} e^{-iφ} (a + i t)‖ ≤ (1/2)/(√r r⁹)`, `a = 1 - 385/(4608 r⁶)`, `t = 5/(48 r³)`. -/
theorem airySO_chi_neg_sq {r : ℝ} (hr : 0 < r) :
    ‖((airyAi (-(r ^ 2)) : ℝ) : ℂ) + I * ((airyBi (-(r ^ 2)) : ℝ) : ℂ) -
        ((1 / (√π * √r) : ℝ) : ℂ) * cexp (((-(2 / 3 * r ^ 3 - π / 4) : ℝ) : ℂ) * I) *
          (((1 - 385 / (4608 * r ^ 6) : ℝ) : ℂ) + ((5 / (48 * r ^ 3) : ℝ) : ℂ) * I)‖ ≤
      1 / 2 * (1 / (√r * r ^ 9)) := by
  have hw : 0 < (negW r).re := by rw [re_negW]; positivity
  have h := norm_airyAiC_sq_fourth_le hw
  rw [norm_exp_negW_cube, mul_one, re_negW r] at h
  have hχ : ((airyAi (-(r ^ 2)) : ℝ) : ℂ) + I * ((airyBi (-(r ^ 2)) : ℝ) : ℂ) =
      (1 + (√3 : ℝ) * I) * airyAiC (negW r ^ 2) := by
    have := airyAiC_add_I_mul_airyBiC ((-(r ^ 2) : ℝ) : ℂ)
    rw [airyAiC_ofReal, airyBiC_ofReal, ← negW_sq] at this
    exact this
  rw [← airySO_poly_negW hr, ← airySO_chi_lead hr, hχ, ← mul_sub, norm_mul, norm_one_add_sqrt3_I]
  have h5 := airySO_err_le hr (five_six_le_re_negW r hr)
  have h' : ‖airyAiC (negW r ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * negW r ^ 3) *
      ((π / negW r) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * negW r ^ 3) + 385 / (4608 * negW r ^ 6)))‖ ≤
      1 / (2 * π) * (34459425 / 268738560 * (√(π / (negW r).re) / (negW r).re ^ 9)) := by
    simpa [re_negW] using h
  calc 2 * ‖_‖ ≤ 2 * (1 / (2 * π) * (34459425 / 268738560 * (√(π / (negW r).re) / (negW r).re ^ 9))) := by
        gcongr
    _ ≤ _ := h5

lemma airySO_re_chi (c a t φ : ℝ) :
    ((c : ℂ) * cexp (((-φ : ℝ) : ℂ) * I) * ((a : ℂ) + (t : ℂ) * I)).re =
      c * (a * Real.cos φ + t * Real.sin φ) := by
  have h1 := Complex.exp_ofReal_mul_I_re (-φ)
  have h2 := Complex.exp_ofReal_mul_I_im (-φ)
  rw [Real.cos_neg] at h1
  rw [Real.sin_neg] at h2
  generalize cexp (((-φ : ℝ) : ℂ) * I) = E at h1 h2
  simp [Complex.mul_re, Complex.mul_im, h1, h2]
  ring

lemma airySO_im_chi (c a t φ : ℝ) :
    ((c : ℂ) * cexp (((-φ : ℝ) : ℂ) * I) * ((a : ℂ) + (t : ℂ) * I)).im =
      c * (t * Real.cos φ - a * Real.sin φ) := by
  have h1 := Complex.exp_ofReal_mul_I_re (-φ)
  have h2 := Complex.exp_ofReal_mul_I_im (-φ)
  rw [Real.cos_neg] at h1
  rw [Real.sin_neg] at h2
  generalize cexp (((-φ : ℝ) : ℂ) * I) = E at h1 h2
  simp [Complex.mul_re, Complex.mul_im, h1, h2]
  ring

/-- **DLMF 9.7.9 to the `u₂` term, imaginary part exact to `O(ξ^{-3})`**, in `r = √y`: with `φ = (2/3) r³ - π/4`,
`|Ai(-r²) - (√π √r)^{-1} (a cos φ + t sin φ)| ≤ (1/2)/(√r r⁹)`, `a = 1 - 385/(4608 r⁶)`, `t = 5/(48 r³)`. -/
theorem airySO_Ai_neg_sq {r : ℝ} (hr : 0 < r) :
    |airyAi (-(r ^ 2)) - 1 / (√π * √r) * ((1 - 385 / (4608 * r ^ 6)) * Real.cos (2 / 3 * r ^ 3 - π / 4) +
        5 / (48 * r ^ 3) * Real.sin (2 / 3 * r ^ 3 - π / 4))| ≤ 1 / 2 * (1 / (√r * r ^ 9)) := by
  refine le_trans ?_ (airySO_chi_neg_sq hr)
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, airySO_re_chi]
  simp

/-- The imaginary part: `|Bi(-r²) - (√π √r)^{-1} (t cos φ - a sin φ)| ≤ (1/2)/(√r r⁹)`. -/
theorem airySO_Bi_neg_sq {r : ℝ} (hr : 0 < r) :
    |airyBi (-(r ^ 2)) - 1 / (√π * √r) * (5 / (48 * r ^ 3) * Real.cos (2 / 3 * r ^ 3 - π / 4) -
        (1 - 385 / (4608 * r ^ 6)) * Real.sin (2 / 3 * r ^ 3 - π / 4))| ≤ 1 / 2 * (1 / (√r * r ^ 9)) := by
  refine le_trans ?_ (airySO_chi_neg_sq hr)
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  rw [Complex.sub_im, airySO_im_chi]
  simp

/-- info: 'FormalResearch.Special.airySO_chi_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airySO_chi_neg_sq

/-- info: 'FormalResearch.Special.airySO_Ai_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airySO_Ai_neg_sq

/-- info: 'FormalResearch.Special.airySO_Bi_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airySO_Bi_neg_sq

end FormalResearch.Special
