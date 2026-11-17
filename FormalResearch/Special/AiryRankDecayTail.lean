module

public import FormalResearch.Special.AiryEnvelopeReal

/-!
# Exponential majorants for `Ai²` on the real axis

**Proved**, from the envelope `airyAiC_norm_sq_le` (E1) on the real axis: for `x ∈ ℝ`

* `airyAi_sq_le_env`: `Ai(x)² ≤ 9 exp(-(4/3) (x₊)^{3/2})`;
* `airyAi_sq_le_exp`: `Ai(x)² ≤ 9 e⁴ e^{-x}` for **all** real `x`;
* `airyAi_sq_le_tail`: `Ai(x)² ≤ 9 e^{-x} exp(-(2/3) y^{3/2})` whenever `4 ≤ y ≤ x`.

The product form `e^{-x}` (rather than `e^{-(4/3)x^{3/2}}`) is what makes the double integrals of
`AiryRankDecay` split into products of one-dimensional integrals.  The constants `9`, `4`, `2/3` are not optimal
(`sup Ai² ≈ 0.287` on `ℝ` by an mpmath scan, and `(4/3)x^{3/2} ≥ x + (2/3) y^{3/2}` uses only `√x ≥ 2`).
-/

@[expose] public section

open Complex Set

namespace FormalResearch.Special

lemma airyAi_sq_le_env (x : ℝ) :
    airyAi x ^ 2 ≤ 9 * Real.exp (-(4 / 3) * (max x 0) ^ (3 / 2 : ℝ)) := by
  have h := airyAiC_norm_sq_le (x : ℂ)
  rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have e : airyEnv (x : ℂ) = Real.exp (-(4 / 3) * (max x 0) ^ (3 / 2 : ℝ)) := by
    unfold airyEnv; rw [re_ofReal_cpow_three_halves]
  rw [e] at h
  refine h.trans ?_
  have h1 : (1 + ‖(x : ℂ)‖) ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (x : ℂ)]) (by norm_num)
  have h2 := Real.exp_pos (-(4 / 3) * (max x 0) ^ (3 / 2 : ℝ))
  nlinarith

lemma two_mul_le_rpow_three_halves {x : ℝ} (hx : 4 ≤ x) : 2 * x ≤ x ^ (3 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have : x ^ (3 / 2 : ℝ) = x * √x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [this]
  have : 2 ≤ √x := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  nlinarith

lemma airyAi_sq_le_tail {x y : ℝ} (hy : 4 ≤ y) (hxy : y ≤ x) :
    airyAi x ^ 2 ≤ 9 * Real.exp (-x) * Real.exp (-(2 / 3) * y ^ (3 / 2 : ℝ)) := by
  refine (airyAi_sq_le_env x).trans ?_
  have hx : 4 ≤ x := hy.trans hxy
  rw [max_eq_left (by linarith)]
  have h1 := two_mul_le_rpow_three_halves hx
  have h2 : y ^ (3 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by linarith) hxy (by norm_num)
  have : Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) ≤
      Real.exp (-x) * Real.exp (-(2 / 3) * y ^ (3 / 2 : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  nlinarith

lemma airyAi_sq_le_exp (x : ℝ) : airyAi x ^ 2 ≤ 9 * Real.exp 4 * Real.exp (-x) := by
  refine (airyAi_sq_le_env x).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  have : -(4 / 3) * (max x 0) ^ (3 / 2 : ℝ) ≤ 4 + -x := by
    rcases le_or_gt x 4 with h | h
    · have : 0 ≤ (max x 0) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (le_max_right _ _) _
      nlinarith
    · rw [max_eq_left (by linarith)]
      have := two_mul_le_rpow_three_halves h.le
      nlinarith
  have := Real.exp_le_exp.2 this
  nlinarith

/-- info: 'FormalResearch.Special.airyAi_sq_le_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_sq_le_tail

/-- info: 'FormalResearch.Special.airyAi_sq_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_sq_le_exp

end FormalResearch.Special
