module

public import FormalResearch.FourQubitEntropy.RenyiFullSHJensen

/-!
# Small-head dual: numerical bounds for the binary entropy and `A_q`

Paper E, `lem:fqe-small-head-dual`.  `binH_le_of_exp` turns a rational lower bound `S'` of
`u^q + (1-u)^q` and a Taylor bound of the exponential into `binH ≤ τ`; `bqA_ge_of_binH` converts it
into `a ≤ A_q(u)`.  Also `A_q ≥ 0` near zero.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Finset

theorem binH_le_of_exp {u S' y τ : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hS0 : 0 < S')
    (hS : S' ≤ (1 - u) ^ qS + u ^ qS) (hy0 : 0 ≤ y)
    (hy : y ≤ (qS - 1) * τ * (693147 / 1000000))
    (hnum : 1 ≤ S' * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 / 720)) :
    binH qBQ u ≤ τ := by
  have hq := qS_gt_one
  have hr : 0 < qS - 1 := by linarith
  have hL := log_two_pos'
  have hLb := log2_bounds.1
  have hτ : 0 ≤ τ := by
    by_contra h
    push Not at h
    nlinarith [mul_neg_of_pos_of_neg hr h]
  have hrL : 0 < (qS - 1) * Real.log 2 := mul_pos hr hL
  have hb := binH_mul_eq hu0 hu1
  have hexp : (∑ i ∈ range 7, y ^ i / (i.factorial : ℝ)) ≤ Real.exp y := Real.sum_le_exp_of_nonneg hy0 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hexp
  norm_num at hexp
  have hyL : y ≤ (qS - 1) * Real.log 2 * τ := by nlinarith
  have hexp2 : Real.exp y ≤ Real.exp ((qS - 1) * Real.log 2 * τ) := Real.exp_le_exp.2 hyL
  have hS1 : 0 < (1 - u) ^ qS + u ^ qS := lt_of_lt_of_le hS0 hS
  have hT : 1 ≤ ((1 - u) ^ qS + u ^ qS) * Real.exp ((qS - 1) * Real.log 2 * τ) := by
    have h1 : S' * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 / 720) ≤
        ((1 - u) ^ qS + u ^ qS) * Real.exp ((qS - 1) * Real.log 2 * τ) := by
      have hT0 : 0 ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 / 720 := by positivity
      have := mul_le_mul hS (hexp.trans hexp2) hT0 hS1.le
      linarith
    linarith
  have hlog : 0 ≤ Real.log (((1 - u) ^ qS + u ^ qS) * Real.exp ((qS - 1) * Real.log 2 * τ)) :=
    Real.log_nonneg hT
  rw [Real.log_mul hS1.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  by_contra h
  push Not at h
  have := mul_lt_mul_of_pos_right h hrL
  linarith

/-- From `binH ≤ τ` to `a ≤ A_q(u)`: `τ = 4u(1-u) - a u(1-u)(1-2u)²`. -/
theorem bqA_ge_of_binH {u a : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (h : binH qBQ u ≤ 4 * u * (1 - u) - a * (u * (1 - u) * (1 - 2 * u) ^ 2)) : a ≤ bqA u := by
  have hd : 0 < u * (1 - u) * (1 - 2 * u) ^ 2 := by
    have : 0 < 1 - 2 * u := by linarith
    have : 0 < 1 - u := by linarith
    positivity
  unfold bqA
  rw [le_div_iff₀ hd]
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
