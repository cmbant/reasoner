module

public import FormalResearch.Special.AiryZeroSecondOrderChi
public import FormalResearch.Special.AiryZeroThirdSaddle

/-!
# `Ai(-r²)` on the negative axis to relative order `r^{-15}`

Specialising `norm_airyAiC_sq_fifth_le` (`AiryZeroThirdSaddle`, the saddle expansion with the terms `u_1, …, u_4`) to
`w = r e^{iπ/6}` (`w³ = i r³`, `w⁶ = -r⁶`, `w⁹ = -i r⁹`, `w^{12} = r^{12}`, `ρ = Re w ≥ (5/6) r`) and rotating as in
`AiryZeroSecondOrderChi`: for every `r > 0`, with `φ = (2/3) r³ - π/4`,
`a = 1 - 385/(4608 r⁶) + 37182145/(127401984 r^{12})` and `t = 5/(48 r³) - 85085/(663552 r⁹)`:

* `airyT3_chi_neg_sq`: `‖Ai(-r²) + i Bi(-r²) - (√π √r)^{-1} e^{-iφ} (a + i t)‖ ≤ 10/(√r r^{15})`;
* **`airyT3_Ai_neg_sq`**: `|Ai(-r²) - (√π √r)^{-1} (a cos φ + t sin φ)| ≤ 10/(√r r^{15})` (DLMF 9.7.9 to `u₄`, `u_5`-sized
  remainder); `airyT3_Bi_neg_sq` the imaginary part.

Numerical check (mpmath, 120 digits, `r ∈ [0.67, 33]` and `r = 40, 80`): `√r r^{15} |Ai(-r²) - main| ≤ 0.51`; the proved
constant `10` follows from `(5391411025/6115295232)(10/9)(6/5)^{15}/√π ≤ 9.4`.

Proved here: everything stated.  **Not formalised:** `Ai'`, `Bi'` to this order.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- At `w = r e^{iπ/6}`: the `N = 5` polynomial equals `a + i t`. -/
lemma airyT3_poly_negW {r : ℝ} (hr : 0 < r) :
    1 - 5 / (48 * negW r ^ 3) + 385 / (4608 * negW r ^ 6) - 85085 / (663552 * negW r ^ 9) +
        37182145 / (127401984 * negW r ^ 12) =
      ((1 - 385 / (4608 * r ^ 6) + 37182145 / (127401984 * r ^ 12) : ℝ) : ℂ) +
        ((5 / (48 * r ^ 3) - 85085 / (663552 * r ^ 9) : ℝ) : ℂ) * I := by
  have h6 : negW r ^ 6 = (negW r ^ 3) ^ 2 := by ring
  have h9 : negW r ^ 9 = (negW r ^ 3) ^ 3 := by ring
  have h12 : negW r ^ 12 = (negW r ^ 3) ^ 4 := by ring
  rw [h6, h9, h12, negW_cube]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hI3 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
  have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  have hI5 : I ^ 5 = I := by rw [pow_succ, hI4]; ring
  have hI0 : I ≠ 0 := Complex.I_ne_zero
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq, hI3, hI4, hI5]
  ring

lemma airyT3_err_le {r ρ : ℝ} (hr : 0 < r) (hρ : 5 / 6 * r ≤ ρ) :
    2 * (1 / (2 * π) * (5391411025 / 6115295232 * (√(π / ρ) / ρ ^ 15))) ≤ 10 * (1 / (√r * r ^ 15)) := by
  have h9 := sqrt_div_pow_le hr hρ 15
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hm : 0 < √r * r ^ 15 := by positivity
  have hT := sqrtpi_ge
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hT0 : 0 < √π := by linarith
  calc 2 * (1 / (2 * π) * (5391411025 / 6115295232 * (√(π / ρ) / ρ ^ 15)))
      ≤ 2 * (1 / (2 * π) * (5391411025 / 6115295232 * (10 / 9 * (6 / 5) ^ 15 * √π / (√r * r ^ 15)))) := by gcongr
    _ = (5391411025 / 6115295232 * (10 / 9) * (6 / 5) ^ 15 / √π) * (1 / (√r * r ^ 15)) := by
        generalize √π = T at hπ hT0
        rw [← hπ]
        field_simp
    _ ≤ 10 * (1 / (√r * r ^ 15)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ hT0]
        nlinarith

/-- **`χ = Ai + iBi` on the negative axis to `O(r^{-15})`**. -/
theorem airyT3_chi_neg_sq {r : ℝ} (hr : 0 < r) :
    ‖((airyAi (-(r ^ 2)) : ℝ) : ℂ) + I * ((airyBi (-(r ^ 2)) : ℝ) : ℂ) -
        ((1 / (√π * √r) : ℝ) : ℂ) * cexp (((-(2 / 3 * r ^ 3 - π / 4) : ℝ) : ℂ) * I) *
          (((1 - 385 / (4608 * r ^ 6) + 37182145 / (127401984 * r ^ 12) : ℝ) : ℂ) +
            ((5 / (48 * r ^ 3) - 85085 / (663552 * r ^ 9) : ℝ) : ℂ) * I)‖ ≤
      10 * (1 / (√r * r ^ 15)) := by
  have hw : 0 < (negW r).re := by rw [re_negW]; positivity
  have h := norm_airyAiC_sq_fifth_le hw
  rw [norm_exp_negW_cube, mul_one, re_negW r] at h
  have hχ : ((airyAi (-(r ^ 2)) : ℝ) : ℂ) + I * ((airyBi (-(r ^ 2)) : ℝ) : ℂ) =
      (1 + (√3 : ℝ) * I) * airyAiC (negW r ^ 2) := by
    have := airyAiC_add_I_mul_airyBiC ((-(r ^ 2) : ℝ) : ℂ)
    rw [airyAiC_ofReal, airyBiC_ofReal, ← negW_sq] at this
    exact this
  rw [← airyT3_poly_negW hr, ← airySO_chi_lead hr, hχ, ← mul_sub, norm_mul, norm_one_add_sqrt3_I]
  have h5 := airyT3_err_le hr (five_six_le_re_negW r hr)
  have h' : ‖airyAiC (negW r ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * negW r ^ 3) *
      ((π / negW r) ^ (1 / 2 : ℂ) * (1 - 5 / (48 * negW r ^ 3) + 385 / (4608 * negW r ^ 6) -
        85085 / (663552 * negW r ^ 9) + 37182145 / (127401984 * negW r ^ 12)))‖ ≤
      1 / (2 * π) * (5391411025 / 6115295232 * (√(π / (negW r).re) / (negW r).re ^ 15)) := by
    simpa [re_negW] using h
  calc 2 * ‖_‖ ≤ 2 * (1 / (2 * π) * (5391411025 / 6115295232 * (√(π / (negW r).re) / (negW r).re ^ 15))) := by
        gcongr
    _ ≤ _ := h5

/-- **DLMF 9.7.9 to `u₄`**, in `r = √y`: `|Ai(-r²) - (√π √r)^{-1} (a cos φ + t sin φ)| ≤ 10/(√r r^{15})`. -/
theorem airyT3_Ai_neg_sq {r : ℝ} (hr : 0 < r) :
    |airyAi (-(r ^ 2)) - 1 / (√π * √r) *
        ((1 - 385 / (4608 * r ^ 6) + 37182145 / (127401984 * r ^ 12)) * Real.cos (2 / 3 * r ^ 3 - π / 4) +
        (5 / (48 * r ^ 3) - 85085 / (663552 * r ^ 9)) * Real.sin (2 / 3 * r ^ 3 - π / 4))| ≤
      10 * (1 / (√r * r ^ 15)) := by
  refine le_trans ?_ (airyT3_chi_neg_sq hr)
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, airySO_re_chi]
  simp

/-- The imaginary part. -/
theorem airyT3_Bi_neg_sq {r : ℝ} (hr : 0 < r) :
    |airyBi (-(r ^ 2)) - 1 / (√π * √r) *
        ((5 / (48 * r ^ 3) - 85085 / (663552 * r ^ 9)) * Real.cos (2 / 3 * r ^ 3 - π / 4) -
        (1 - 385 / (4608 * r ^ 6) + 37182145 / (127401984 * r ^ 12)) * Real.sin (2 / 3 * r ^ 3 - π / 4))| ≤
      10 * (1 / (√r * r ^ 15)) := by
  refine le_trans ?_ (airyT3_chi_neg_sq hr)
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  rw [Complex.sub_im, airySO_im_chi]
  simp

/-- info: 'FormalResearch.Special.airyT3_chi_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_chi_neg_sq

/-- info: 'FormalResearch.Special.airyT3_Ai_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_Ai_neg_sq

/-- info: 'FormalResearch.Special.airyT3_Bi_neg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyT3_Bi_neg_sq

end FormalResearch.Special
