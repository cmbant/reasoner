module

public import FormalResearch.Special.AiryMomentLimit
public import FormalResearch.Special.AiryZeroSecondOrder

/-!
# The Airy linear moment (`cts:airy-sum-zero`), phase-free

For `κ = (3π/2)^{2/3}` and `K ≥ 1`:
`|Σ_{k=1}^K |a_k|/κ - ∫_0^{K+1/4} u^{2/3} du| ≤ C K^{-1/3}` (**proved**, `airyZero_linear_moment`), i.e.
`Σ_{k ≤ K} |a_k|/κ - ∫_{1/4}^{K+1/2} (a - 1/4)^{2/3} da = O(K^{-1/3})` in the variable `a = u + 1/4`.

Inputs: the Hadamard sum rule `airyAi_sq_series_real`, its two-term asymptotics `airy_zero_sum_asymp` (the three-term
asymptotics of `Ai'/Ai` by the Riccati barrier of `Asymptotics.RiccatiBarrier`), the zero asymptotics
`airyZero_delta_exists` (DLMF 9.9.6 with the `n^{-4/3}` remainder), and `AiryMomentLimit`.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.Special

open FormalResearch.Special.AiryMoment

/-- `κ = (3π/2)^{2/3}` satisfies `κ³ = (3π/2)²`. -/
lemma kappa_cube : ((3 * π / 2) ^ (2 / 3 : ℝ)) ^ 3 = (3 * π / 2) ^ 2 := by
  have h : 0 ≤ 3 * π / 2 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

/-- **The Airy linear moment** (in the variable `u = a - 1/4`). -/
theorem airyZero_linear_moment :
    ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K →
      |(∑ k ∈ Finset.Icc 1 K, |airyZero k|) / (3 * π / 2) ^ (2 / 3 : ℝ) -
          ∫ u in (0 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ)| ≤ C * (K : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hκ : 0 < (3 * π / 2) ^ (2 / 3 : ℝ) := by have := Real.pi_pos; positivity
  obtain ⟨Cη, hCη⟩ := airyZero_delta_exists
  have hη : ∀ n : ℕ, |-airyZero (n + 1) - (3 * π / 2) ^ (2 / 3 : ℝ) * cc n ^ (2 / 3 : ℝ)| ≤
      Cη * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) := by
    intro n
    have h := hCη (n + 1) (by omega)
    have e1 : airyZeroT (n + 1) ^ (2 / 3 : ℝ) = (3 * π / 2) ^ (2 / 3 : ℝ) * cc n ^ (2 / 3 : ℝ) := by
      unfold airyZeroT cc
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      push_cast; ring
    rw [e1] at h
    have e2 : -airyZero (n + 1) - (3 * π / 2) ^ (2 / 3 : ℝ) * cc n ^ (2 / 3 : ℝ) =
        -(airyZero (n + 1) + (3 * π / 2) ^ (2 / 3 : ℝ) * cc n ^ (2 / 3 : ℝ)) := by ring
    rw [e2, abs_neg]
    simpa using h
  obtain ⟨C, hC⟩ := moment_finite (m := fun n => -airyZero (n + 1)) (E := fun x => (airyAi' x / airyAi x) ^ 2 - x)
    hκ kappa_cube (fun n => neg_nonneg.mpr (airyZero_nonpos _)) hη
    (fun x hx => (airy_zero_sum_asymp hx).1) (fun x hx => (airy_zero_sum_asymp hx).2)
  refine ⟨C, fun K hK => ?_⟩
  have h := hC K hK
  have hr : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, |airyZero k| = ∑ n ∈ Finset.range N, |airyZero (n + 1)| := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  have e : ∑ k ∈ Finset.Icc 1 K, |airyZero k| = ∑ n ∈ Finset.range K, -airyZero (n + 1) := by
    rw [hr K]
    exact Finset.sum_congr rfl (fun n _ => abs_of_nonpos (airyZero_nonpos _))
  rw [e]
  exact h

/-- info: 'FormalResearch.Special.airyZero_linear_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyZero_linear_moment

end FormalResearch.Special
