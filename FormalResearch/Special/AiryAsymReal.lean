module

public import FormalResearch.Special.AiryAsymNeg
public import FormalResearch.Special.AiryKernelOpFormula

/-!
# Oscillatory asymptotics of `Ai`, `Ai'`, `Bi` on the negative axis: statements in `y = -x`, and consequences

Rewrites the `r = √y` statements of `AiryAsymNeg` with the real powers of `y`.  For every `y > 0`, with
`ξ = (2/3) y^{3/2}`:

* `airyAi_neg_asymptotic`   `|Ai(-y) - π^{-1/2} y^{-1/4} cos(ξ - π/4)| ≤ (1/8) y^{-7/4}`,
* `airyAi'_neg_asymptotic`  `|Ai'(-y) - π^{-1/2} y^{1/4} sin(ξ - π/4)| ≤ (2/5) y^{-5/4}`,
* `airyBi_neg_asymptotic`   `|Bi(-y) + π^{-1/2} y^{-1/4} sin(ξ - π/4)| ≤ (1/8) y^{-7/4}`.

Consequences for `y ≥ 1` (relative error `O(y^{-3/2})`):

* `airyAi_sq_add_airyBi_sq_neg`: `|Ai(-y)² + Bi(-y)² - 1/(π √y)| ≤ (2/5) y^{-2}`;
* `airyKer_diag_neg`: `|K(-y,-y) - √y/π| ≤ y^{-1}`, where `K(x,x) = Ai'(x)² - x Ai(x)²` is the Airy kernel
  on the diagonal (the density `√y/π` of the Airy point process at `-y`).

Constants are those of the proof and are not optimal.  Not formalised: the full asymptotic series,
`Bi'` on the negative axis.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma rpow_neg_quarter {y : ℝ} (hy : 0 < y) : y ^ (-(1 / 4) : ℝ) = 1 / √(√y) := by
  rw [Real.rpow_neg hy.le, sqrt_sqrt_eq_rpow hy]; simp

lemma rpow_neg_seven_quarter {y : ℝ} (hy : 0 < y) :
    y ^ (-(7 / 4) : ℝ) = 1 / (√(√y) * (√y) ^ 3) := by
  rw [Real.rpow_neg hy.le, sqrt_sqrt_eq_rpow hy, sqrt_cube_eq_rpow hy, ← Real.rpow_add hy]
  norm_num

lemma rpow_neg_five_quarter {y : ℝ} (hy : 0 < y) :
    y ^ (-(5 / 4) : ℝ) = 1 / (√(√y) * (√y) ^ 2) := by
  rw [Real.rpow_neg hy.le, sqrt_sqrt_eq_rpow hy, Real.sq_sqrt hy.le]
  have : y ^ (5 / 4 : ℝ) = y ^ (1 / 4 : ℝ) * y := by
    conv_lhs => rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.rpow_add hy, Real.rpow_one]
  rw [this]; simp

/-- **DLMF 9.7.9 with explicit remainder**: for every `y > 0`,
`|Ai(-y) - π^{-1/2} y^{-1/4} cos((2/3) y^{3/2} - π/4)| ≤ (1/8) y^{-7/4}`. -/
theorem airyAi_neg_asymptotic {y : ℝ} (hy : 0 < y) :
    |airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
      1 / 8 * y ^ (-(7 / 4) : ℝ) := by
  have hr : 0 < √y := Real.sqrt_pos.mpr hy
  have h := airyAi_neg_sq_asymptotic hr
  rw [Real.sq_sqrt hy.le] at h
  have hs : 0 < √(√y) := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have e1 : 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) =
      Real.cos (2 / 3 * (√y) ^ 3 - π / 4) / (√π * √(√y)) := by
    rw [rpow_neg_quarter hy, ← sqrt_cube_eq_rpow hy]
    field_simp
  rw [e1, rpow_neg_seven_quarter hy]
  convert h using 2
  field_simp

/-- **DLMF 9.7.10 with explicit remainder**: for every `y > 0`,
`|Ai'(-y) - π^{-1/2} y^{1/4} sin((2/3) y^{3/2} - π/4)| ≤ (2/5) y^{-5/4}`. -/
theorem airyAi'_neg_asymptotic {y : ℝ} (hy : 0 < y) :
    |airyAi' (-y) - 1 / √π * y ^ (1 / 4 : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
      2 / 5 * y ^ (-(5 / 4) : ℝ) := by
  have hr : 0 < √y := Real.sqrt_pos.mpr hy
  have h := airyAi'_neg_sq_asymptotic hr
  rw [Real.sq_sqrt hy.le] at h
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have e1 : 1 / √π * y ^ (1 / 4 : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) =
      √(√y) * Real.sin (2 / 3 * (√y) ^ 3 - π / 4) / √π := by
    rw [← sqrt_sqrt_eq_rpow hy, ← sqrt_cube_eq_rpow hy]
    field_simp
  rw [e1, rpow_neg_five_quarter hy, Real.sq_sqrt hy.le]
  convert h using 2
  have hs : 0 < √(√y) := Real.sqrt_pos.mpr hr
  field_simp

/-- **DLMF 9.7.11 with explicit remainder**: for every `y > 0`,
`|Bi(-y) + π^{-1/2} y^{-1/4} sin((2/3) y^{3/2} - π/4)| ≤ (1/8) y^{-7/4}`
(the leading term is `π^{-1/2} y^{-1/4} cos((2/3) y^{3/2} + π/4)`). -/
theorem airyBi_neg_asymptotic {y : ℝ} (hy : 0 < y) :
    |airyBi (-y) + 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
      1 / 8 * y ^ (-(7 / 4) : ℝ) := by
  have hr : 0 < √y := Real.sqrt_pos.mpr hy
  have h := airyBi_neg_sq_asymptotic hr
  rw [Real.sq_sqrt hy.le] at h
  have hs : 0 < √(√y) := Real.sqrt_pos.mpr hr
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have e1 : 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4) =
      Real.sin (2 / 3 * (√y) ^ 3 - π / 4) / (√π * √(√y)) := by
    rw [rpow_neg_quarter hy, ← sqrt_cube_eq_rpow hy]
    field_simp
  rw [e1, rpow_neg_seven_quarter hy]
  convert h using 2
  field_simp

/-! ### Consequences: amplitude and kernel diagonal -/

lemma abs_sq_sub_sq_le {A a e M : ℝ} (h : |A - a| ≤ e) (ha : |a| ≤ M) :
    |A ^ 2 - a ^ 2| ≤ e * (2 * M + e) := by
  have e1 : A ^ 2 - a ^ 2 = (A - a) * (A + a) := by ring
  have h2 : |A + a| ≤ 2 * M + e := by
    have : A + a = (A - a) + 2 * a := by ring
    rw [this]
    calc |(A - a) + 2 * a| ≤ |A - a| + |2 * a| := abs_add_le _ _
      _ ≤ e + 2 * M := by rw [abs_mul, abs_two]; linarith
      _ = 2 * M + e := by ring
  rw [e1, abs_mul]
  exact mul_le_mul h h2 (abs_nonneg _) ((abs_nonneg _).trans h)

lemma amp_num {r s T : ℝ} (hr : 1 ≤ r) (hs : 0 < s) (hsr : s * s = r) (hT : 8 / 5 ≤ T) :
    1 / (8 * (s * r ^ 3)) * (2 * (1 / (T * s)) + 1 / (8 * (s * r ^ 3))) +
      1 / (8 * (s * r ^ 3)) * (2 * (1 / (T * s)) + 1 / (8 * (s * r ^ 3))) ≤ 2 / 5 / r ^ 4 := by
  have hr0 : 0 < r := by linarith
  have hT0 : 0 < T := by linarith
  have h4 : 0 < r ^ 4 := by positivity
  have e : 1 / (8 * (s * r ^ 3)) * (2 * (1 / (T * s)) + 1 / (8 * (s * r ^ 3))) +
      1 / (8 * (s * r ^ 3)) * (2 * (1 / (T * s)) + 1 / (8 * (s * r ^ 3))) =
      1 / (2 * T * r ^ 4) + 1 / (32 * r ^ 7) := by
    subst hsr
    field_simp
    ring
  rw [e]
  have h1 : 1 / (2 * T * r ^ 4) ≤ 5 / 16 / r ^ 4 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hr0 4]
  have h2 : 1 / (32 * r ^ 7) ≤ 1 / (32 * r ^ 4) :=
    one_div_le_one_div_of_le (by positivity)
      (by nlinarith [pow_le_pow_right₀ hr (by norm_num : 4 ≤ 7), pow_pos hr0 4])
  have h3 : 5 / 16 / r ^ 4 + 1 / (32 * r ^ 4) = 11 / 32 / r ^ 4 := by field_simp; norm_num
  have h5 : 11 / 32 / r ^ 4 ≤ 2 / 5 / r ^ 4 := div_le_div_of_nonneg_right (by norm_num) h4.le
  linarith

/-- **Amplitude**: for `r ≥ 1`, `|Ai(-r²)² + Bi(-r²)² - 1/(π r)| ≤ (2/5)/r⁴`. -/
theorem airyAi_sq_add_airyBi_sq_neg_sq {r : ℝ} (hr : 1 ≤ r) :
    |airyAi (-(r ^ 2)) ^ 2 + airyBi (-(r ^ 2)) ^ 2 - 1 / (π * r)| ≤ 2 / 5 / r ^ 4 := by
  have hr0 : 0 < r := by linarith
  have h1 := airyAi_neg_sq_asymptotic hr0
  have h2 := airyBi_neg_sq_asymptotic hr0
  have hT := sqrtpi_ge
  have hsr : √r * √r = r := Real.mul_self_sqrt hr0.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr0
  set φ := 2 / 3 * r ^ 3 - π / 4 with hφ
  have hM : 0 < √π * √r := by positivity
  have hc : |Real.cos φ / (√π * √r)| ≤ 1 / (√π * √r) := by
    rw [abs_div, abs_of_pos hM]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hM.le
  have hs' : |-Real.sin φ / (√π * √r)| ≤ 1 / (√π * √r) := by
    rw [abs_div, abs_of_pos hM, abs_neg]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hM.le
  have h2' : |airyBi (-(r ^ 2)) - (-Real.sin φ / (√π * √r))| ≤ 1 / (8 * (√r * r ^ 3)) := by
    rw [neg_div, sub_neg_eq_add]; exact h2
  have hA := abs_sq_sub_sq_le h1 hc
  have hB := abs_sq_sub_sq_le h2' hs'
  have hden : (√π * √r) ^ 2 = π * r := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hr0.le]
  have hsum : (Real.cos φ / (√π * √r)) ^ 2 + (-Real.sin φ / (√π * √r)) ^ 2 = 1 / (π * r) := by
    rw [div_pow, div_pow, neg_sq, ← add_div, Real.cos_sq_add_sin_sq, hden]
  have key : airyAi (-(r ^ 2)) ^ 2 + airyBi (-(r ^ 2)) ^ 2 - 1 / (π * r) =
      (airyAi (-(r ^ 2)) ^ 2 - (Real.cos φ / (√π * √r)) ^ 2) +
        (airyBi (-(r ^ 2)) ^ 2 - (-Real.sin φ / (√π * √r)) ^ 2) := by
    linear_combination hsum
  rw [key]
  refine (abs_add_le _ _).trans ((add_le_add hA hB).trans ?_)
  have := amp_num hr hs hsr hT
  convert this using 3

/-- **Amplitude**, `y ≥ 1`: `|Ai(-y)² + Bi(-y)² - 1/(π √y)| ≤ (2/5) y^{-2}`
(so `Ai² + Bi² = (1/(π√y)) (1 + O(y^{-3/2}))`, the squared Olver modulus `M²(-y)`). -/
theorem airyAi_sq_add_airyBi_sq_neg {y : ℝ} (hy : 1 ≤ y) :
    |airyAi (-y) ^ 2 + airyBi (-y) ^ 2 - 1 / (π * √y)| ≤ 2 / 5 / y ^ 2 := by
  have hr : 1 ≤ √y := by rw [Real.one_le_sqrt]; exact hy
  have h := airyAi_sq_add_airyBi_sq_neg_sq hr
  rw [Real.sq_sqrt (by linarith)] at h
  have e : (√y) ^ 4 = y ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
  rwa [e] at h

lemma diag_num {r s T : ℝ} (hr : 1 ≤ r) (hs : 0 < s) (hsr : s * s = r) (hT : 8 / 5 ≤ T) :
    2 / (5 * (s * r ^ 2)) * (2 * (s / T) + 2 / (5 * (s * r ^ 2))) +
      r ^ 2 * (1 / (8 * (s * r ^ 3)) * (2 * (1 / (T * s)) + 1 / (8 * (s * r ^ 3)))) ≤ 1 / r ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hT0 : 0 < T := by linarith
  have h2 : 0 < r ^ 2 := by positivity
  have e : 2 / (5 * (s * r ^ 2)) * (2 * (s / T) + 2 / (5 * (s * r ^ 2))) +
      r ^ 2 * (1 / (8 * (s * r ^ 3)) * (2 * (1 / (T * s)) + 1 / (8 * (s * r ^ 3)))) =
      21 / (20 * T * r ^ 2) + 281 / 1600 / r ^ 5 := by
    subst hsr
    field_simp
    ring
  rw [e]
  have h1 : 21 / (20 * T * r ^ 2) ≤ 21 / 32 / r ^ 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hr0 2]
  have h3 : 281 / 1600 / r ^ 5 ≤ 281 / 1600 / r ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) h2
      (pow_le_pow_right₀ hr (by norm_num : 2 ≤ 5))
  have h4 : 21 / 32 / r ^ 2 + 281 / 1600 / r ^ 2 ≤ 1 / r ^ 2 := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) h2.le
  linarith

/-- **Airy kernel on the diagonal at `-r²`**, `r ≥ 1`: `|K(-r²,-r²) - r/π| ≤ 1/r²`,
where `K(x,x) = Ai'(x)² - x Ai(x)²`. -/
theorem airyKer_diag_neg_sq {r : ℝ} (hr : 1 ≤ r) :
    |airyKer (-(r ^ 2)) (-(r ^ 2)) - r / π| ≤ 1 / r ^ 2 := by
  have hr0 : 0 < r := by linarith
  have h1 := airyAi_neg_sq_asymptotic hr0
  have h3 := airyAi'_neg_sq_asymptotic hr0
  have hT := sqrtpi_ge
  have hsr : √r * √r = r := Real.mul_self_sqrt hr0.le
  have hs : 0 < √r := Real.sqrt_pos.mpr hr0
  have hT0 : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  set φ := 2 / 3 * r ^ 3 - π / 4 with hφ
  have hM : 0 < √π * √r := by positivity
  have hc : |Real.cos φ / (√π * √r)| ≤ 1 / (√π * √r) := by
    rw [abs_div, abs_of_pos hM]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hM.le
  have hs1 : |√r * Real.sin φ / √π| ≤ √r / √π := by
    rw [abs_div, abs_of_pos hT0, abs_mul, abs_of_pos hs]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right hs.le (Real.abs_sin_le_one _)) hT0.le
  have hA := abs_sq_sub_sq_le h1 hc
  have hA' := abs_sq_sub_sq_le h3 hs1
  have hsum : (√r * Real.sin φ / √π) ^ 2 + r ^ 2 * (Real.cos φ / (√π * √r)) ^ 2 = r / π := by
    have hπ : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
    have hr2 : √r ^ 2 = r := Real.sq_sqrt hr0.le
    have hcs := Real.sin_sq_add_cos_sq φ
    simp only [div_pow, mul_pow, hπ, hr2]
    rw [show Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 by linarith]
    field_simp
    ring
  have key : airyKer (-(r ^ 2)) (-(r ^ 2)) - r / π =
      (airyAi' (-(r ^ 2)) ^ 2 - (√r * Real.sin φ / √π) ^ 2) +
        r ^ 2 * (airyAi (-(r ^ 2)) ^ 2 - (Real.cos φ / (√π * √r)) ^ 2) := by
    rw [airyKer_self]
    linear_combination hsum
  rw [key]
  have hB : |r ^ 2 * (airyAi (-(r ^ 2)) ^ 2 - (Real.cos φ / (√π * √r)) ^ 2)| ≤
      r ^ 2 * (1 / (8 * (√r * r ^ 3)) * (2 * (1 / (√π * √r)) + 1 / (8 * (√r * r ^ 3)))) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  refine (abs_add_le _ _).trans ((add_le_add hA' hB).trans ?_)
  exact diag_num hr hs hsr hT

/-- **Airy kernel on the diagonal at `-y`**, `y ≥ 1`: `|K(-y,-y) - √y/π| ≤ 1/y`, i.e.
`K(-y,-y) = (√y/π)(1 + O(y^{-3/2}))`. -/
theorem airyKer_diag_neg {y : ℝ} (hy : 1 ≤ y) :
    |airyKer (-y) (-y) - √y / π| ≤ 1 / y := by
  have hr : 1 ≤ √y := by rw [Real.one_le_sqrt]; exact hy
  have h := airyKer_diag_neg_sq hr
  rwa [Real.sq_sqrt (by linarith)] at h

/-- info: 'FormalResearch.Special.airyAi_neg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_neg_asymptotic

/-- info: 'FormalResearch.Special.airyAi'_neg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_neg_asymptotic

/-- info: 'FormalResearch.Special.airyBi_neg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_neg_asymptotic

/-- info: 'FormalResearch.Special.airyAi_sq_add_airyBi_sq_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_sq_add_airyBi_sq_neg

/-- info: 'FormalResearch.Special.airyKer_diag_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_diag_neg

end FormalResearch.Special
