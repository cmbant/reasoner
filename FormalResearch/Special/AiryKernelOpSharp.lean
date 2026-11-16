module

public import FormalResearch.Special.AiryKernelOpBounds
public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryEnvelopeReal

/-!
# Sharp exponents for the Airy kernel on the diagonal (W1)

The complex envelope (`AiryEnvelope`: `|Ai z| ≤ 3(1+|z|)^{-1/4}`, `|Ai' z| ≤ 5(1+|z|)^{1/4}` on the
negative real axis, where `Re z^{3/2} = 0`) gives the sharp exponents that
`AiryKernelOpBounds` could only prove with exponents `1` and `2`:

* `abs_airyAi_le_of_nonpos`, `abs_airyAi'_le_of_nonpos`: `|Ai x| ≤ 3(1+|x|)^{-1/4}`,
  `|Ai' x| ≤ 5(1+|x|)^{1/4}` for `x ≤ 0`.
* `airyKer_diag_le_sqrt`: `K(x,x) ≤ 34 (1 + x_-)^{1/2}` for all real `x`.
* `airyN_le_sharp`, `airyR_le_sharp`: `N_Ai(u) = ∫_u^∞ K(s,s)ds ≤ 28 (1+u_-)^{3/2}` and
  `∫_u^∞ Ai'² ≤ 22 (1+u_-)^{3/2}`.

These are the bounds `K(s,s) ≤ C(1+s_-)^{1/2}` and `∫_u^∞ Ai'² ≤ C(1+u_-)^{3/2}` used in the W1 edge notes
(`Weyl/free_fermion/notes/edge_crossover.tex`), with explicit constants.

The leading asymptotics `K(-y,-y) = √y/π + O(1/y)` (`y ≥ 1`) are `airyKer_diag_neg` in `AiryAsymReal`.
Not formalised: the matching lower bounds for all `x`.
-/

@[expose] public section

namespace FormalResearch.Special

open Real MeasureTheory Set

/-- `|Ai x| ≤ 3 (1+|x|)^{-1/4}` for `x ≤ 0`. -/
theorem abs_airyAi_le_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    |airyAi x| ≤ 3 * (1 + |x|) ^ (-(1 / 4) : ℝ) := by
  have h := airyAiC_envelope (x : ℂ)
  rw [norm_airyAiC_ofReal, re_ofReal_cpow_three_halves, Complex.norm_real, Real.norm_eq_abs] at h
  rw [max_eq_right hx, Real.zero_rpow (by norm_num)] at h
  simpa using h

/-- `|Ai' x| ≤ 5 (1+|x|)^{1/4}` for `x ≤ 0`. -/
theorem abs_airyAi'_le_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    |airyAi' x| ≤ 5 * (1 + |x|) ^ (1 / 4 : ℝ) := by
  have h := airyAiC_deriv_envelope (x : ℂ)
  rw [norm_deriv_airyAiC_ofReal, re_ofReal_cpow_three_halves, Complex.norm_real,
    Real.norm_eq_abs] at h
  rw [max_eq_right hx, Real.zero_rpow (by norm_num)] at h
  simpa using h

/-- Polynomial form of the two bounds with `s = (1+y)^{1/4}`, `y = -x ≥ 0`. -/
lemma airy_neg_poly {y : ℝ} (hy : 0 ≤ y) :
    ∃ s : ℝ, 0 < s ∧ s ^ 4 = 1 + y ∧ s ^ 2 = (1 + y) ^ (1 / 2 : ℝ) ∧ s ^ 6 = (1 + y) ^ (3 / 2 : ℝ) ∧
      |airyAi (-y)| * s ≤ 3 ∧ |airyAi' (-y)| ≤ 5 * s := by
  have h1 : 0 < 1 + y := by linarith
  set s : ℝ := (1 + y) ^ (1 / 4 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos h1 _
  have hpow : ∀ n : ℕ, s ^ n = (1 + y) ^ ((n : ℝ) / 4) := by
    intro n
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul h1.le]
    congr 1; ring
  have habs : |(-y)| = y := by rw [abs_neg, abs_of_nonneg hy]
  have hA := abs_airyAi_le_of_nonpos (x := -y) (by linarith)
  have hB := abs_airyAi'_le_of_nonpos (x := -y) (by linarith)
  rw [habs] at hA hB
  refine ⟨s, hs0, ?_, ?_, ?_, ?_, hB⟩
  · rw [hpow 4]; norm_num
  · rw [hpow 2]; norm_num
  · rw [hpow 6]; norm_num
  · have hinv : (1 + y) ^ (-(1 / 4) : ℝ) = 1 / s := by
      rw [Real.rpow_neg h1.le, inv_eq_one_div]
    rw [hinv] at hA
    calc |airyAi (-y)| * s ≤ 3 * (1 / s) * s := by gcongr
      _ = 3 := by field_simp
  
/-- `K(x,x) ≤ 34 (1+x_-)^{1/2}` for `x ≤ 0` (`x_- = -x`). -/
lemma airyKer_diag_le_sqrt_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    airyKer x x ≤ 34 * (1 + (-x)) ^ (1 / 2 : ℝ) := by
  obtain ⟨s, hs, hs4, hs2, -, hA, hB⟩ := airy_neg_poly (y := -x) (by linarith)
  rw [neg_neg] at hA hB
  rw [← hs2, airyKer_self]
  set a := airyAi x
  set b := airyAi' x
  have hy : 0 ≤ -x := by linarith
  have ha2 : a ^ 2 * s ^ 2 ≤ 9 := by
    have : (|a| * s) ^ 2 ≤ 3 ^ 2 := by gcongr
    rw [mul_pow, sq_abs] at this; linarith
  have hb2 : b ^ 2 ≤ 25 * s ^ 2 := by
    have : |b| ^ 2 ≤ (5 * s) ^ 2 := by gcongr
    rw [sq_abs] at this; nlinarith
  have hy4 : -x ≤ s ^ 4 := by linarith
  have h1 : (-x) * a ^ 2 ≤ 9 * s ^ 2 := by
    calc (-x) * a ^ 2 ≤ s ^ 4 * a ^ 2 := by gcongr
      _ = s ^ 2 * (a ^ 2 * s ^ 2) := by ring
      _ ≤ s ^ 2 * 9 := by gcongr
      _ = 9 * s ^ 2 := by ring
  nlinarith [h1, hb2]

/-- `K(x,x) ≤ 34 (1+x_-)^{1/2}` for all real `x`. -/
theorem airyKer_diag_le_sqrt (x : ℝ) :
    airyKer x x ≤ 34 * (1 + max (-x) 0) ^ (1 / 2 : ℝ) := by
  by_cases hx : x ≤ 0
  · rw [max_eq_left (by linarith)]; exact airyKer_diag_le_sqrt_of_nonpos hx
  · have h0 := airyKer_diag_le_sqrt_of_nonpos (x := 0) le_rfl
    have hanti : airyKer x x ≤ airyKer 0 0 := antitone_airyKer_diag (by linarith [not_le.mp hx])
    rw [max_eq_right (by linarith [not_le.mp hx])]
    simp only [add_zero, Real.one_rpow, mul_one, neg_zero] at h0 ⊢
    linarith

/-- `N_Ai(u) ≤ 28 (1+u_-)^{3/2}` for `u ≤ 0`. -/
lemma airyN_le_sharp_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    airyN u ≤ 28 * (1 + (-u)) ^ (3 / 2 : ℝ) := by
  obtain ⟨s, hs, hs4, -, hs6, hA, hB⟩ := airy_neg_poly (y := -u) (by linarith)
  rw [neg_neg] at hA hB
  rw [← hs6]
  unfold airyN
  set a := airyAi u
  set b := airyAi' u
  have hy : 0 ≤ -u := by linarith
  have ha2 : a ^ 2 * s ^ 2 ≤ 9 := by
    have : (|a| * s) ^ 2 ≤ 3 ^ 2 := by gcongr
    rw [mul_pow, sq_abs] at this; linarith
  have hb2 : b ^ 2 ≤ 25 * s ^ 2 := by
    have : |b| ^ 2 ≤ (5 * s) ^ 2 := by gcongr
    rw [sq_abs] at this; nlinarith
  have hab : |a * b| ≤ 15 := by
    rw [abs_mul]
    have : |a| * s ≤ 3 := hA
    calc |a| * |b| ≤ |a| * (5 * s) := by gcongr
      _ = 5 * (|a| * s) := by ring
      _ ≤ 5 * 3 := by gcongr
      _ = 15 := by norm_num
  have hy4 : -u ≤ s ^ 4 := by linarith
  have hs1 : 1 ≤ s ^ 4 := by linarith
  have h1 : (-u) * a ^ 2 ≤ 9 * s ^ 2 := by
    calc (-u) * a ^ 2 ≤ s ^ 4 * a ^ 2 := by gcongr
      _ = s ^ 2 * (a ^ 2 * s ^ 2) := by ring
      _ ≤ s ^ 2 * 9 := by gcongr
      _ = 9 * s ^ 2 := by ring
  have h2 : (-u) * ((-u) * a ^ 2) ≤ (-u) * (9 * s ^ 2) := by gcongr
  have h3 : (-u) * (9 * s ^ 2) ≤ 9 * s ^ 6 := by nlinarith
  have h4 : (-u) * b ^ 2 ≤ 25 * s ^ 6 := by nlinarith [mul_le_mul_of_nonneg_left hb2 hy]
  have hs6' : 1 ≤ s ^ 6 := by nlinarith [pow_pos hs 2]
  have : -(a * b) ≤ 15 := by linarith [neg_abs_le (a * b), abs_le.mp hab]
  nlinarith

/-- `∫_u^∞ Ai'² ≤ 22 (1+u_-)^{3/2}` for `u ≤ 0` in the closed form `airyR`. -/
lemma airyR_le_sharp_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    airyR u ≤ 22 * (1 + (-u)) ^ (3 / 2 : ℝ) := by
  obtain ⟨s, hs, hs4, -, hs6, hA, hB⟩ := airy_neg_poly (y := -u) (by linarith)
  rw [neg_neg] at hA hB
  rw [← hs6]
  unfold airyR
  set a := airyAi u
  set b := airyAi' u
  have hy : 0 ≤ -u := by linarith
  have ha2 : a ^ 2 * s ^ 2 ≤ 9 := by
    have : (|a| * s) ^ 2 ≤ 3 ^ 2 := by gcongr
    rw [mul_pow, sq_abs] at this; linarith
  have hb2 : b ^ 2 ≤ 25 * s ^ 2 := by
    have : |b| ^ 2 ≤ (5 * s) ^ 2 := by gcongr
    rw [sq_abs] at this; nlinarith
  have hab : |a * b| ≤ 15 := by
    rw [abs_mul]
    have : |a| * s ≤ 3 := hA
    calc |a| * |b| ≤ |a| * (5 * s) := by gcongr
      _ = 5 * (|a| * s) := by ring
      _ ≤ 5 * 3 := by gcongr
      _ = 15 := by norm_num
  have hy4 : -u ≤ s ^ 4 := by linarith
  have hs1 : 1 ≤ s ^ 4 := by linarith
  have h1 : (-u) * a ^ 2 ≤ 9 * s ^ 2 := by
    calc (-u) * a ^ 2 ≤ s ^ 4 * a ^ 2 := by gcongr
      _ = s ^ 2 * (a ^ 2 * s ^ 2) := by ring
      _ ≤ s ^ 2 * 9 := by gcongr
      _ = 9 * s ^ 2 := by ring
  have h2 : (-u) * ((-u) * a ^ 2) ≤ (-u) * (9 * s ^ 2) := by gcongr
  have h3 : (-u) * (9 * s ^ 2) ≤ 9 * s ^ 6 := by nlinarith
  have h4 : (-u) * b ^ 2 ≤ 25 * s ^ 6 := by nlinarith [mul_le_mul_of_nonneg_left hb2 hy]
  have hs6' : 1 ≤ s ^ 6 := by nlinarith [pow_pos hs 2]
  have : -(a * b) ≤ 15 := by linarith [neg_abs_le (a * b), abs_le.mp hab]
  nlinarith

/-- `N_Ai(u) = ∫_u^∞ K(s,s)ds ≤ 28 (1+u_-)^{3/2}` for all real `u`. -/
theorem airyN_le_sharp (u : ℝ) : airyN u ≤ 28 * (1 + max (-u) 0) ^ (3 / 2 : ℝ) := by
  by_cases hu : u ≤ 0
  · rw [max_eq_left (by linarith)]; exact airyN_le_sharp_of_nonpos hu
  · have h0 := airyN_le_sharp_of_nonpos (u := 0) le_rfl
    have hmono : airyN u ≤ airyN 0 := by
      rw [← integral_Ioi_airyKer_diag, ← integral_Ioi_airyKer_diag]
      exact setIntegral_mono_set (integrableOn_Ioi_airyKer_diag 0)
        (Filter.Eventually.of_forall fun s => airyKer_diag_nonneg s)
        (Filter.Eventually.of_forall (Ioi_subset_Ioi (le_of_lt (not_le.mp hu))))
    rw [max_eq_right (by linarith [not_le.mp hu])]
    simp only [add_zero, Real.one_rpow, mul_one, neg_zero] at h0 ⊢
    linarith

/-- `∫_u^∞ Ai'² ≤ 22 (1+u_-)^{3/2}` for all real `u`. -/
theorem integral_Ioi_airyAi'_sq_le_sharp (u : ℝ) :
    ∫ s in Ioi u, airyAi' s ^ 2 ≤ 22 * (1 + max (-u) 0) ^ (3 / 2 : ℝ) := by
  rw [integral_Ioi_airyAi'_sq]
  by_cases hu : u ≤ 0
  · rw [max_eq_left (by linarith)]; exact airyR_le_sharp_of_nonpos hu
  · have h0 := airyR_le_sharp_of_nonpos (u := 0) le_rfl
    have hmono : airyR u ≤ airyR 0 := by
      rw [← integral_Ioi_airyAi'_sq, ← integral_Ioi_airyAi'_sq]
      exact setIntegral_mono_set (integrableOn_Ioi_airyAi'_sq 0)
        (Filter.Eventually.of_forall fun s => sq_nonneg _)
        (Filter.Eventually.of_forall (Ioi_subset_Ioi (le_of_lt (not_le.mp hu))))
    rw [max_eq_right (by linarith [not_le.mp hu])]
    simp only [add_zero, Real.one_rpow, mul_one, neg_zero] at h0 ⊢
    linarith

/-- info: 'FormalResearch.Special.airyKer_diag_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_diag_le_sqrt

/-- info: 'FormalResearch.Special.airyN_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyN_le_sharp

/-- info: 'FormalResearch.Special.integral_Ioi_airyAi'_sq_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_Ioi_airyAi'_sq_le_sharp

end FormalResearch.Special
