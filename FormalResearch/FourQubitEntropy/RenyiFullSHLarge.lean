import FormalResearch.FourQubitEntropy.RenyiFullSHLargeCells
import FormalResearch.FourQubitEntropy.RenyiFullSHTail

/-!
# Small-head dual: the large tail `1/4 ≤ u ≤ 1/2`

Paper E, `lem:fqe-small-head-dual`, "Large tail": near-uniform moment bound (Taylor, as in `nu_entropy_bound`)
and the polynomial certificate `shG ≥ 0`.  Writing `x = p - 1/4`, `y = Σ(λ_i - 1/4)³`, `v = y/x`, the entropy bound is
`2 - H_q ≥ x (35/8 - (9/5) v - (159/100) x)` for `0 < x ≤ 3/32`, `0 ≤ v ≤ 9/50`.  The paper's concavity-in-`x`
and tangent-square argument is replaced here by a single Bernstein cell on the whole rectangle.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Finset

set_option maxHeartbeats 8000000 in
theorem sh_large_entropy {l : Fin 4 → ℝ} (hl : IsProb4 l) (hx0 : 0 < pur l - 1 / 4)
    (hx1 : pur l - 1 / 4 ≤ 3 / 32) (hy0 : 0 ≤ cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4))
    (hy1 : cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) ≤ 9 / 50 * (pur l - 1 / 4)) :
    (pur l - 1 / 4) * (35 / 8 - 9 / 5 * ((cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4)) / (pur l - 1 / 4)) -
      159 / 100 * (pur l - 1 / 4)) ≤ 2 - renyiSpec qS l := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = pur l - 1 / 4 := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, y = cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) := ⟨_, rfl⟩
  rw [← hydef] at hy0 hy1 ⊢
  rw [← hxdef] at hx0 hx1 hy1 ⊢
  have hw := w_sums hl.2
  rw [← hydef, ← hxdef] at hw
  obtain ⟨hw2, hw3⟩ := hw
  have hN := nu_taylor_sum hl
  rw [hw2, hw3] at hN
  obtain ⟨S4, hS4def⟩ : ∃ S, S = ∑ i, (l i - 1 / 4) ^ 4 := ⟨_, rfl⟩
  rw [← hS4def] at hN
  have hsum0 : (l 0 - 1 / 4) + (l 1 - 1 / 4) + (l 2 - 1 / 4) + (l 3 - 1 / 4) = 0 := by
    have := hl.2; simp only [Fin.sum_univ_four] at this; linarith
  have hS := sum_w4_ge hsum0
  have hS' : x * S4 ≥ x ^ 3 / 4 + y ^ 2 := by
    have e2 : x = (l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2 := by
      rw [← hw2]; simp [Fin.sum_univ_four]
    have e3 : y = (l 0 - 1 / 4) ^ 3 + (l 1 - 1 / 4) ^ 3 + (l 2 - 1 / 4) ^ 3 + (l 3 - 1 / 4) ^ 3 := by
      rw [← hw3]; simp [Fin.sum_univ_four]
    have e4 : S4 = (l 0 - 1 / 4) ^ 4 + (l 1 - 1 / 4) ^ 4 + (l 2 - 1 / 4) ^ 4 + (l 3 - 1 / 4) ^ 4 := by
      rw [hS4def]; simp [Fin.sum_univ_four]
    rw [e2, e3, e4] at *
    exact hS
  obtain ⟨v, hv⟩ : ∃ v, v = y / x := ⟨_, rfl⟩
  rw [← hv]
  have hyv : y = x * v := by rw [hv]; field_simp
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hv1 : v ≤ 9 / 50 := by rw [hv, div_le_iff₀ hx0]; linarith
  have hS4v : S4 ≥ x ^ 2 / 4 + x * v ^ 2 := by
    have : x * S4 ≥ x * (x ^ 2 / 4 + x * v ^ 2) := by
      rw [hyv] at hS'; nlinarith [hS']
    exact le_of_mul_le_mul_left this hx0
  have hC := nuC_pos
  obtain ⟨z, hzdef⟩ : ∃ z, z = x * ((nuA qS + nuB qS * v + nuC qS * v ^ 2) +
      x * (nuC qS / 4 + nuT qS * v)) := ⟨_, rfl⟩
  have hNz : 1 + z ≤ (4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS := by
    have hC4 := mul_le_mul_of_nonneg_left hS4v hC.le
    have e1 : 1 + z = 1 + nuA qS * x + nuB qS * (x * v) + nuC qS * (x ^ 2 / 4 + x * v ^ 2) +
        nuT qS * x * (x * v) := by rw [hzdef]; ring
    rw [hyv] at hN
    linarith [hN, hC4, e1]
  have hV : 3 / 2 ≤ nuA qS + nuB qS * v + nuC qS * v ^ 2 := by
    unfold nuA nuB nuC qS; nlinarith [sq_nonneg v]
  have hW : -(3 / 50) ≤ nuC qS / 4 + nuT qS * v := by
    unfold nuT nuC qS; nlinarith
  have hVW : 0 ≤ (nuA qS + nuB qS * v + nuC qS * v ^ 2) + x * (nuC qS / 4 + nuT qS * v) := by
    nlinarith [mul_nonneg hx0.le (show 0 ≤ nuC qS / 4 + nuT qS * v + 3 / 50 by linarith)]
  have hz0 : 0 ≤ z := by rw [hzdef]; positivity
  have hZq : 0 < ∑ i, l i ^ qS := sum_rpow_pos hl.1 hl.2
  have hNpos : 0 < (4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS := by positivity
  have hlogN : Real.log (1 + z) ≤ Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) :=
    Real.log_le_log (by linarith) hNz
  have hl4 := log_ge_taylor4 hz0
  have hG := shG_nonneg hx0.le hx1 hv0 hv1
  have hKz : x * shG x v = (z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4) -
      (587 / 1000 * (693148 / 10 ^ 6)) * (x * (35 / 8 - 9 / 5 * v - 159 / 100 * x)) := by
    rw [hzdef]; simp only [shG, nuA, nuB, nuC, nuT, qS]; ring
  have hLge : (587 / 1000 * (693148 / 10 ^ 6)) * (x * (35 / 8 - 9 / 5 * v - 159 / 100 * x)) ≤
      Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) := by
    have := mul_nonneg hx0.le hG
    linarith
  have hL2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hLlt : Real.log 2 < 693148 / 10 ^ 6 := by
    have := log2_bounds.2; norm_num at this ⊢; linarith
  have hlogNeq : Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) =
      (qS - 1) * Real.log 2 * (2 - renyiSpec qS l) := by
    rw [Real.log_mul (by positivity) hZq.ne', Real.log_rpow (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    unfold renyiSpec Real.logb
    have h1 : (1 - qS) ≠ 0 := by unfold qS; norm_num
    field_simp
    push_cast
    ring
  rw [hlogNeq] at hLge
  have hK : 0 ≤ 35 / 8 - 9 / 5 * v - 159 / 100 * x := by nlinarith
  have hr : 0 < qS - 1 := by unfold qS; norm_num
  have hxK : 0 ≤ x * (35 / 8 - 9 / 5 * v - 159 / 100 * x) := mul_nonneg hx0.le hK
  have step : (qS - 1) * Real.log 2 * (x * (35 / 8 - 9 / 5 * v - 159 / 100 * x)) ≤
      (qS - 1) * Real.log 2 * (2 - renyiSpec qS l) := by
    refine le_trans ?_ hLge
    have e : (587 / 1000 : ℝ) = qS - 1 := by unfold qS; norm_num
    rw [e]
    have := mul_le_mul_of_nonneg_left hLlt.le (mul_nonneg hr.le hxK)
    nlinarith [this]
  have hpos : 0 < (qS - 1) * Real.log 2 := mul_pos hr hL2
  exact le_of_mul_le_mul_left step hpos

end FormalResearch.FourQubitEntropy.RenyiFull
