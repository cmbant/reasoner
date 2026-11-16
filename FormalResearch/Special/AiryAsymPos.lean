module

public import FormalResearch.Special.AiryAsymReal

/-!
# Sharp asymptotics of `Ai` and `Ai'` on the positive axis

For `x > 0`, with `ξ = (2/3) x^{3/2}` and `P(x) = (1/(2√π)) x^{-1/4} e^{-ξ}`:

* `airyAi_sub_leading_le`: `|Ai(x) - P(x)| ≤ (5/48) x^{-3/2} P(x)` (from the two-sided bounds of `AiryPositive`,
  `AiryBound`; the same constant as the saddle-point estimate of `AiryAsymSaddle` at `w = √x`);
* `airyAi'_add_leading_le`: `|Ai'(x) + (1/(2√π)) x^{1/4} e^{-ξ}| ≤ (17/(96√π)) x^{-5/4} e^{-ξ}`, i.e. relative error
  `(17/48) x^{-3/2}`; the case `w = √x` of `norm_deriv_airyAiC_sq_add_le`.

Both hold for every `x > 0`.  Not formalised: further terms of the expansion; `Bi` on the positive axis.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `Ai(x) = P(x) (1 + O(x^{-3/2}))` on the positive axis, with `5/48`. -/
theorem airyAi_sub_leading_le {x : ℝ} (hx : 0 < x) :
    |airyAi x - 1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))| ≤
      5 / 48 / x ^ (3 / 2 : ℝ) *
        (1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) := by
  have hlow := airyAi_lower_bound hx
  have hup := (le_abs_self _).trans (airyAi_abs_le hx)
  set P := 1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) with hP
  rw [abs_le]
  constructor <;> nlinarith

lemma ofReal_cpow_half {a : ℝ} (ha : 0 ≤ a) : ((a : ℂ)) ^ (1 / 2 : ℂ) = ((√a : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]
  push_cast
  rfl

/-- In the variable `r = √x`: `|Ai'(r²) + √r e^{-(2/3)r³}/(2√π)| ≤ (17/(96√π)) e^{-(2/3)r³}/(√r r²)`. -/
theorem airyAi'_sq_add_leading_le {r : ℝ} (hr : 0 < r) :
    |airyAi' (r ^ 2) + √r * Real.exp (-(2 / 3) * r ^ 3) / (2 * √π)| ≤
      17 / (96 * √π) * Real.exp (-(2 / 3) * r ^ 3) / (√r * r ^ 2) := by
  have hw : 0 < ((r : ℂ)).re := by simpa using hr
  have h := norm_deriv_airyAiC_sq_add_le hw
  have e1 : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : cexp (-(2 / 3) * (r : ℂ) ^ 3) = ((Real.exp (-(2 / 3) * r ^ 3) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  have e3 : ((π : ℂ) / (r : ℂ)) ^ (1 / 2 : ℂ) = ((√(π / r) : ℝ) : ℂ) := by
    have : (π : ℂ) / (r : ℂ) = ((π / r : ℝ) : ℂ) := by push_cast; rfl
    rw [this]; exact ofReal_cpow_half (by positivity)
  rw [e1, deriv_airyAiC_ofReal, e2, e3] at h
  simp only [Complex.ofReal_re] at h
  have hE := Real.exp_pos (-(2 / 3) * r ^ 3)
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hsr : √r * √r = r := Real.mul_self_sqrt hr.le
  have lhs : ((airyAi' (r ^ 2) : ℝ) : ℂ) + 1 / (2 * (π : ℂ)) * ((Real.exp (-(2 / 3) * r ^ 3) : ℝ) : ℂ) *
      ((r : ℂ) * ((√(π / r) : ℝ) : ℂ)) =
      ((airyAi' (r ^ 2) + √r * Real.exp (-(2 / 3) * r ^ 3) / (2 * √π) : ℝ) : ℂ) := by
    have : √(π / r) = √π / √r := Real.sqrt_div Real.pi_pos.le r
    rw [this]
    push_cast
    have hT' : (√π : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have hs' : (√r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hπ' : (π : ℂ) = (√π : ℂ) * (√π : ℂ) := by exact_mod_cast hπ.symm
    have hr' : (r : ℂ) = (√r : ℂ) * (√r : ℂ) := by exact_mod_cast hsr.symm
    rw [hπ', hr']
    field_simp
  rw [lhs] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE, abs_of_pos hr] at h
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_div Real.pi_pos.le]
  have hπ'' : π = √π * √π := hπ.symm
  generalize √π = T at hπ'' hT ⊢
  generalize √r = u at hsr hs ⊢
  rw [hπ'']
  subst hsr
  field_simp
  ring

/-- **`Ai'` on the positive axis**: for `x > 0`,
`|Ai'(x) + (1/(2√π)) x^{1/4} e^{-(2/3)x^{3/2}}| ≤ (17/(96√π)) x^{-5/4} e^{-(2/3)x^{3/2}}`. -/
theorem airyAi'_add_leading_le {x : ℝ} (hx : 0 < x) :
    |airyAi' x + 1 / (2 * √π) * x ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))| ≤
      17 / (96 * √π) * x ^ (-(5 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) := by
  have hr : 0 < √x := Real.sqrt_pos.mpr hx
  have h := airyAi'_sq_add_leading_le hr
  rw [Real.sq_sqrt hx.le] at h
  have hs : 0 < √(√x) := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [rpow_neg_five_quarter hx, ← sqrt_sqrt_eq_rpow hx, ← sqrt_cube_eq_rpow hx]
  rw [Real.sq_sqrt hx.le]
  convert h using 2
  · field_simp
  · field_simp

/-- info: 'FormalResearch.Special.airyAi_sub_leading_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_sub_leading_le

/-- info: 'FormalResearch.Special.airyAi'_add_leading_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_add_leading_le

end FormalResearch.Special
