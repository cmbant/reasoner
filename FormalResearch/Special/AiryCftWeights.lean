module

public import FormalResearch.Special.AiryCftMittagLeffler
public import FormalResearch.Special.AiryCftDefect

/-!
# Weights `1/Ai'(a_n)²` and the summability of `Σ f(a_n)/Ai'(a_n)²`

Inputs for `AiryCftQuadrature` (Corollary D1).  All proved:

* `airyEnv_ofReal_neg`: `e(x) = exp(-(4/3) Re x^{3/2}) = 1` for real `x < 0` (the principal `x^{3/2}` is purely imaginary
  there); `airyEnv_ofReal_le_one`: `e(x) ≤ 1` for every real `x`;
* `airyZero_inv_deriv_sq_le`: `1/Ai'(a_n)² ≤ 36 π² (1 + |a_n|)^{-1/2}` (from `Bi(a_n) = -1/(π Ai'(a_n))` and
  `‖Bi - iAi‖² ≤ 36 (1+|u|)^{-1/2}/e(u)` at `u = a_n`, where `e = 1`);
* `airy_summable_weighted`: if `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` with `ν < -1` then `Σ_n f(a_n)/Ai'(a_n)²` converges absolutely
  (`|a_n| ≥ 2.5 n^{2/3}`, exponent `(2/3)(ν - 1/2) < -1`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `e(x) = 1` for negative real `x`. -/
lemma airyEnv_ofReal_neg {a : ℝ} (ha : a < 0) : airyEnv (a : ℂ) = 1 := by
  unfold airyEnv
  have hy : ((a : ℂ) ^ (1 / 2 : ℂ)).re = 0 := by
    have h1 := airySqrtRe_sq_sub (a : ℂ)
    have h2 := airySqrtRe_mul_im (a : ℂ)
    simp only [Complex.ofReal_re, Complex.ofReal_im] at h1 h2
    unfold airySqrtRe at h1 h2
    set x := ((a : ℂ) ^ (1 / 2 : ℂ)).re
    set y := ((a : ℂ) ^ (1 / 2 : ℂ)).im
    rcases mul_eq_zero.mp h2 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact h
    · rw [h] at h1; nlinarith [sq_nonneg x]
  rw [← cpow_half_cube, show (((a : ℂ) ^ (1 / 2 : ℂ)) ^ 3).re = 0 by
    rw [re_cube, hy]; ring]
  simp

/-- `e(x) ≤ 1` for every real `x`. -/
lemma airyEnv_ofReal_le_one (x : ℝ) : airyEnv (x : ℂ) ≤ 1 := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [airyEnv_ofReal_neg hx]
  · unfold airyEnv
    have : ((x : ℂ) ^ (3 / 2 : ℂ)).re = x ^ (3 / 2 : ℝ) := by
      have := Complex.ofReal_cpow hx (3 / 2 : ℝ)
      rw [show (((3 / 2 : ℝ)) : ℂ) = (3 / 2 : ℂ) by push_cast; ring] at this
      rw [← this, Complex.ofReal_re]
    rw [this]
    refine Real.exp_le_one_iff.mpr ?_
    have := Real.rpow_nonneg hx (3 / 2 : ℝ)
    nlinarith

/-- `1/Ai'(a_n)² ≤ 36 π² (1 + |a_n|)^{-1/2}`. -/
lemma airyZero_inv_deriv_sq_le (n : ℕ) :
    ‖((deriv airyAiC (airyZero n : ℂ)) ^ 2)⁻¹‖ ≤ 36 * π ^ 2 * (1 + (-airyZero n)) ^ (-(1 / 2) : ℝ) := by
  have hD := airyZero_deriv_ne_zero n
  have hBi := cftDef_airyBiC_at_zero n
  have hb := norm_airyBiC_sub_I_mul_sq_le (u := (airyZero n : ℂ)) (by simp)
  rw [airyAiC_ofReal, airyAi_airyZero, Complex.ofReal_zero, mul_zero, sub_zero,
    airyEnv_ofReal_neg (airyZero_neg n), div_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (airyZero_neg n), hBi, norm_neg, norm_div, norm_one, norm_mul] at hb
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hDn : 0 < ‖deriv airyAiC (airyZero n : ℂ)‖ := norm_pos_iff.mpr hD
  have hpn : ‖(π : ℂ)‖ = π := by simp [abs_of_pos hpi]
  rw [hpn] at hb
  rw [norm_inv, norm_pow]
  set p := (1 + (-airyZero n)) ^ (-(1 / 2) : ℝ)
  have hp : 0 < p := Real.rpow_pos_of_pos (by linarith [airyZero_neg n]) _
  set d := ‖deriv airyAiC (airyZero n : ℂ)‖
  have h1 : (1 / (π * d)) ^ 2 ≤ 36 * p := hb
  rw [div_pow, one_pow, mul_pow] at h1
  rw [div_le_iff₀ (by positivity)] at h1
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  nlinarith [h1]

/-- **Summability of the Gauss-type weights.** If `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` with `ν < -1`, then
`Σ_n f(a_n)/Ai'(a_n)²` converges absolutely. -/
theorem airy_summable_weighted {f : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C) (hν : ν < -1)
    (hf : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    Summable (fun n : ℕ => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2) := by
  set q : ℝ := ν - 1 / 2 with hq
  have hq0 : q < 0 := by rw [hq]; linarith
  have hg : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (2 / 3 * q)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by rw [hq]; linarith))
  refine Summable.of_norm_bounded_eventually (hg.mul_left (36 * π ^ 2 * C * 2.5 ^ q)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  set a : ℝ := airyZero (n + 1)
  have ha0 : a < 0 := airyZero_neg _
  have hab := (airyZero_abs_bounds (n := n + 1) (by omega)).1
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [norm_div, norm_pow]
  have hf1 := hf (a : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha0, airyEnv_ofReal_neg ha0, mul_one] at hf1
  have hw := airyZero_inv_deriv_sq_le (n + 1)
  rw [norm_inv, norm_pow] at hw
  have e1 : (1 + -a) ^ ν * (1 + -a) ^ (-(1 / 2) : ℝ) = (1 + -a) ^ q := by
    rw [hq, ← Real.rpow_add (by linarith)]; ring_nf
  have hpos : 0 < 1 + -a := by linarith
  -- (1 + |a|)^q ≤ (2.5 (n+1)^{2/3})^q
  have h2 : (1 + -a) ^ q ≤ (2.5 * ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) ^ q := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hq0.le
    linarith
  have h3 : (2.5 * ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) ^ q = 2.5 ^ q * ((n + 1 : ℕ) : ℝ) ^ (2 / 3 * q) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]
  have hd : 0 < ‖deriv airyAiC (airyZero (n + 1) : ℂ)‖ := norm_pos_iff.mpr (airyZero_deriv_ne_zero _)
  have hdd : (‖deriv airyAiC (airyZero (n + 1) : ℂ)‖ ^ 2)⁻¹ ≤ 36 * π ^ 2 * (1 + -a) ^ (-(1 / 2) : ℝ) := hw
  rw [div_eq_mul_inv]
  calc ‖f (a : ℂ)‖ * (‖deriv airyAiC (airyZero (n + 1) : ℂ)‖ ^ 2)⁻¹
      ≤ (C * (1 + -a) ^ ν) * (36 * π ^ 2 * (1 + -a) ^ (-(1 / 2) : ℝ)) := by
        gcongr
    _ = 36 * π ^ 2 * C * (1 + -a) ^ q := by rw [← e1]; ring
    _ ≤ 36 * π ^ 2 * C * (2.5 ^ q * ((n + 1 : ℕ) : ℝ) ^ (2 / 3 * q)) := by rw [← h3]; gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.Special.airyEnv_ofReal_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyEnv_ofReal_neg

/-- info: 'FormalResearch.Special.airy_summable_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_summable_weighted

end FormalResearch.Special
