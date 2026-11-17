module

public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.AiryKernelOpBounds
public import FormalResearch.Special.AiryCftWeights
public import FormalResearch.Special.AiryEnvelopeReal

/-!
# Real bounds for `Ai`, `Ai'` on the negative axis (input to Theorem 4.7)

* `at47_airyAiC_deriv_norm_sq_le`: `‖Ai'(z)‖² ≤ 25 (1+|z|)^{1/2} e(z)` on `ℂ` (square of the proved envelope (E1')).
* `at47_neg_bounds`: for `s ≥ 1`, `√s · Ai(-s)² ≤ 9` and `Ai'(-s)² ≤ 38 √s`.
* `at47_ker_neg_lower`: for `s ≥ 4`, `K(-s,-s) ≥ √s/(2π)` (from `airyKer_diag_neg`).

All proved.
-/

@[expose] public section

open Complex
open scoped Real

namespace FormalResearch.Special

theorem at47_airyAiC_deriv_norm_sq_le (z : ℂ) :
    ‖deriv airyAiC z‖ ^ 2 ≤ 25 * (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z := by
  have h := airyAiC_deriv_envelope z
  have h0 := norm_nonneg (deriv airyAiC z)
  have h1 := pow_le_pow_left₀ h0 h 2
  refine h1.trans (le_of_eq ?_)
  have e1 : ((1 + ‖z‖) ^ (1 / 4 : ℝ)) ^ 2 = (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have e2 : (Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2 = airyEnv z := by
    rw [airyEnv, ← Real.exp_nat_mul]; norm_num; ring_nf
  calc (5 * (1 + ‖z‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2
      = 25 * ((1 + ‖z‖) ^ (1 / 4 : ℝ)) ^ 2 * (Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2 := by ring
    _ = _ := by rw [e1, e2]

theorem at47_neg_bounds {s : ℝ} (hs : 1 ≤ s) :
    √s * airyAi (-s) ^ 2 ≤ 9 ∧ airyAi' (-s) ^ 2 ≤ 38 * √s := by
  have hs0 : 0 < s := by linarith
  have hn : ‖((-s : ℝ) : ℂ)‖ = s := by simp [abs_of_pos hs0]
  have hE : airyEnv ((-s : ℝ) : ℂ) = 1 := airyEnv_ofReal_neg (by linarith)
  have hsq : 0 < √s := Real.sqrt_pos.mpr hs0
  constructor
  · have h := airyAiC_norm_sq_le ((-s : ℝ) : ℂ)
    rw [hn, hE, mul_one, norm_airyAiC_ofReal, sq_abs] at h
    have h2 : (1 + s) ^ (-(1 / 2) : ℝ) ≤ 1 / √s := by
      rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow, one_div]
      exact inv_anti₀ hsq (Real.sqrt_le_sqrt (by linarith))
    calc √s * airyAi (-s) ^ 2 ≤ √s * (9 * (1 / √s)) := by
          gcongr; exact h.trans (by gcongr)
      _ = 9 := by field_simp
  · have h := at47_airyAiC_deriv_norm_sq_le ((-s : ℝ) : ℂ)
    rw [hn, hE, mul_one, norm_deriv_airyAiC_ofReal, sq_abs] at h
    have h2 : (1 + s) ^ (1 / 2 : ℝ) ≤ √2 * √s := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have h3 : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [h3, h2, h, hsq]

theorem at47_ker_neg_lower {s : ℝ} (hs : 4 ≤ s) : √s / (2 * π) ≤ airyKer (-s) (-s) := by
  have h := airyKer_diag_neg (y := s) (by linarith)
  have hs0 : 0 < s := by linarith
  have hpi := Real.pi_pos
  have h1 := (abs_le.mp h).1
  have hsq : √s * √s = s := Real.mul_self_sqrt hs0.le
  have hsq2 : 2 ≤ √s := by
    rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hs
  have hp : π < 4 := Real.pi_lt_four
  -- 1/s ≤ √s/(2π)
  have h3 : 1 / s ≤ √s / (2 * π) := by
    rw [div_le_div_iff₀ hs0 (by positivity)]
    nlinarith [mul_pos (by linarith : (0:ℝ) < √s) (by linarith : (0:ℝ) < √s)]
  have : √s / π - √s / (2 * π) = √s / (2 * π) := by field_simp; ring
  linarith

/-- info: 'FormalResearch.Special.at47_neg_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_neg_bounds

/-- info: 'FormalResearch.Special.at47_ker_neg_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_ker_neg_lower

end FormalResearch.Special
