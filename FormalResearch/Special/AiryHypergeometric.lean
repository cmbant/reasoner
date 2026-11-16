module

public import FormalResearch.Special.AiryTaylor
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# The Airy Taylor series as `0F1`

Mathlib has the *regularized* hypergeometric function `Complex.regularizedHGFun a b`
(`Σ_n  (∏ (a_i)_n) / (n! ∏ Γ(b_j + n)) z^n`), and no ordinary `0F1`; the ordinary `0F1(; b; w)` is
`Γ(b) · regularizedHGFun 0 {b} w`.  With the two entire series `F, G` of `AiryTaylor`
(`Ai = Ai(0) F + Ai'(0) G`) this file proves (DLMF 9.4.1–9.4.2: `f(z) = 0F1(; 2/3; z³/9)`,
`g(z) = z · 0F1(; 4/3; z³/9)`, up to the normalisation `f(0) = 1`):

* `airyTaylorF_eq_hyp`: `F(z) = Γ(2/3) · regularizedHGFun 0 {2/3} (z³/9)`  (`= 0F1(; 2/3; z³/9)`);
* `airyTaylorG_eq_hyp`: `G(z) = z · Γ(4/3) · regularizedHGFun 0 {4/3} (z³/9)`  (`= z · 0F1(; 4/3; z³/9)`);
* `airyAiC_eq_hyp`: with the exact values of `AiryValues`,
  `Ai(z) = 3^{-2/3} rHG_{2/3}(z³/9) - 3^{-4/3} z rHG_{4/3}(z³/9)`, `rHG_b = regularizedHGFun 0 {b}`
  (the classical `Ai(z) = c₁ f(z) - c₂ g(z)` with `c₁ = Ai(0) = 3^{-2/3}/Γ(2/3)`,
  `c₂ = -Ai'(0) = 3^{-1/3}/Γ(1/3)`; `Γ(4/3) = Γ(1/3)/3`).  Checked with mpmath (30 digits) at
  `z = 0.7, -2.3, 1+2i`: agreement to `10^{-31}`.

The coefficient identities used: `(3j)! = A_j B_j 3^j j!`, `Γ(2/3 + j) = Γ(2/3) B_j / 3^j`,
`Γ(4/3 + j) = Γ(4/3) A_{j+1}/(3^j A_1)` with `A_j = ∏_{i<j}(3i+1)`, `B_j = ∏_{i<j}(3i+2)`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real Nat

namespace FormalResearch.Special

lemma airyCoefA_succ (j : ℕ) : airyCoefA (j + 1) = airyCoefA j * (3 * j + 1) := by
  simp [airyCoefA, Finset.prod_range_succ]

lemma airyCoefB_succ (j : ℕ) : airyCoefB (j + 1) = airyCoefB j * (3 * j + 2) := by
  simp [airyCoefB, Finset.prod_range_succ]

lemma airyCoefA_pos (j : ℕ) : 0 < airyCoefA j := by
  induction j with
  | zero => simp [airyCoefA]
  | succ j ih => rw [airyCoefA_succ]; positivity

lemma airyCoefB_pos (j : ℕ) : 0 < airyCoefB j := by
  induction j with
  | zero => simp [airyCoefB]
  | succ j ih => rw [airyCoefB_succ]; positivity

lemma airyFactorial_three_mul (j : ℕ) :
    (((3 * j)! : ℕ) : ℂ) = (airyCoefA j : ℂ) * airyCoefB j * 3 ^ j * (j ! : ℂ) := by
  induction j with
  | zero => simp [airyCoefA, airyCoefB]
  | succ j ih =>
    have e : (3 * (j + 1))! = (3 * j + 3) * ((3 * j + 2) * ((3 * j + 1) * (3 * j)!)) := by
      rw [show 3 * (j + 1) = 3 * j + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ]
    rw [e, Nat.factorial_succ j]
    push_cast
    rw [ih, airyCoefA_succ, airyCoefB_succ]
    push_cast
    ring

lemma gamma_two_thirds_add (j : ℕ) :
    Complex.Gamma (2 / 3 + j) = Complex.Gamma (2 / 3) * (airyCoefB j : ℂ) / 3 ^ j := by
  induction j with
  | zero => simp [airyCoefB]
  | succ j ih =>
    have h : (2 / 3 + ((j + 1 : ℕ) : ℂ)) = (2 / 3 + j) + 1 := by push_cast; ring
    rw [h, Complex.Gamma_add_one _ (by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith), ih, airyCoefB_succ]
    push_cast
    ring

lemma gamma_four_thirds_add (j : ℕ) :
    Complex.Gamma (4 / 3 + j) = Complex.Gamma (4 / 3) * (airyCoefA (j + 1) : ℂ) / 3 ^ j := by
  induction j with
  | zero => simp [airyCoefA]
  | succ j ih =>
    have h : (4 / 3 + ((j + 1 : ℕ) : ℂ)) = (4 / 3 + j) + 1 := by push_cast; ring
    rw [h, Complex.Gamma_add_one _ (by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith), ih, airyCoefA_succ (j + 1)]
    push_cast
    ring

lemma gamma_ne_zero_two_thirds : Complex.Gamma (2 / 3) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by norm_num)

lemma gamma_ne_zero_four_thirds : Complex.Gamma (4 / 3) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by norm_num)

lemma regularizedHGFun_zero_singleton (b z : ℂ) :
    Complex.regularizedHGFun 0 {b} z =
      ∑' n : ℕ, (1 / ((n ! : ℂ) * Complex.Gamma (b + n))) * z ^ n := by
  unfold Complex.regularizedHGFun Complex.regularizedHGFunSeries
  rw [show (FormalMultilinearSeries.ofScalars ℂ (Complex.regularizedHGFunCoeff 0 {b})).sum z =
    FormalMultilinearSeries.ofScalarsSum (Complex.regularizedHGFunCoeff 0 {b}) z from rfl,
    FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp [Complex.regularizedHGFunCoeff]

/-- **`F(z) = 0F1(; 2/3; z³/9)`**, with `0F1(; b; w) = Γ(b) · regularizedHGFun 0 {b} w`. -/
theorem airyTaylorF_eq_hyp (z : ℂ) :
    airyTaylorF z = Complex.Gamma (2 / 3) * Complex.regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) := by
  rw [regularizedHGFun_zero_singleton, ← tsum_mul_left, airyTaylorF]
  refine tsum_congr fun j => ?_
  rw [gamma_two_thirds_add, airyFactorial_three_mul, pow_mul, div_pow]
  have hA : (airyCoefA j : ℂ) ≠ 0 := by exact_mod_cast (airyCoefA_pos j).ne'
  have hB : (airyCoefB j : ℂ) ≠ 0 := by exact_mod_cast (airyCoefB_pos j).ne'
  have hg := gamma_ne_zero_two_thirds
  have hf : (j ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have h9 : (9 : ℂ) ^ j = 3 ^ j * 3 ^ j := by rw [← mul_pow]; norm_num
  rw [h9]
  field_simp

/-- **`G(z) = z · 0F1(; 4/3; z³/9)`**. -/
theorem airyTaylorG_eq_hyp (z : ℂ) :
    airyTaylorG z = z * (Complex.Gamma (4 / 3) * Complex.regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) := by
  rw [regularizedHGFun_zero_singleton, ← tsum_mul_left, ← tsum_mul_left, airyTaylorG]
  refine tsum_congr fun j => ?_
  rw [gamma_four_thirds_add, Nat.factorial_succ (3 * j), Nat.cast_mul, airyFactorial_three_mul,
    airyCoefA_succ, pow_succ, pow_mul, div_pow]
  have hA : (airyCoefA j : ℂ) ≠ 0 := by exact_mod_cast (airyCoefA_pos j).ne'
  have hB : (airyCoefB j : ℂ) ≠ 0 := by exact_mod_cast (airyCoefB_pos j).ne'
  have hg := gamma_ne_zero_four_thirds
  have hf : (j ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have h9 : (9 : ℂ) ^ j = 3 ^ j * 3 ^ j := by rw [← mul_pow]; norm_num
  have h31 : (3 * (j : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < 3 * (j : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  rw [h9]
  push_cast
  field_simp

/-- **`Ai(z) = 3^{-2/3} · rHG_{2/3}(z³/9) - 3^{-4/3} · z · rHG_{4/3}(z³/9)`**, with
`rHG_b = Complex.regularizedHGFun 0 {b}` (DLMF 9.4.1–9.4.3 for Mathlib's regularized `0F1`). -/
theorem airyAiC_eq_hyp (z : ℂ) :
    airyAiC z = (((3 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * Complex.regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) -
      (((3 : ℝ) ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * (z * Complex.regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) := by
  rw [airyAiC_eq_explicit, airyTaylorF_eq_hyp, airyTaylorG_eq_hyp]
  have g23 : (Complex.Gamma (2 / 3) : ℂ) = ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
    have := Complex.Gamma_ofReal (2 / 3 : ℝ)
    simpa using this
  have g13 : (Complex.Gamma (1 / 3) : ℂ) = ((Real.Gamma (1 / 3) : ℝ) : ℂ) := by
    have := Complex.Gamma_ofReal (1 / 3 : ℝ)
    simpa using this
  have g43 : Complex.Gamma (4 / 3) = Complex.Gamma (1 / 3) / 3 := by
    have := Complex.Gamma_add_one (1 / 3 : ℂ) (by norm_num)
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, this]; ring
  have hr23 : Real.Gamma (2 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hr13 : Real.Gamma (1 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have e43 : ((3 : ℝ) ^ (-(4 / 3 : ℝ))) = (3 : ℝ) ^ (-(1 / 3 : ℝ)) / 3 := by
    rw [show (-(4 / 3 : ℝ)) = -(1 / 3) + (-1) by norm_num, Real.rpow_add (by norm_num), Real.rpow_neg_one]
    ring
  rw [e43, g43, g13, g23]
  push_cast
  have h1 : (Real.Gamma (2 / 3) : ℂ) ≠ 0 := by exact_mod_cast hr23
  have h2 : (Real.Gamma (1 / 3) : ℂ) ≠ 0 := by exact_mod_cast hr13
  field_simp

/-- info: 'FormalResearch.Special.airyTaylorF_eq_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyTaylorF_eq_hyp

/-- info: 'FormalResearch.Special.airyTaylorG_eq_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyTaylorG_eq_hyp

/-- info: 'FormalResearch.Special.airyAiC_eq_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_eq_hyp

end FormalResearch.Special
