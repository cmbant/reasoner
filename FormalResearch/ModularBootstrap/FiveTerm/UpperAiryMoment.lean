module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperMainInputs
public import FormalResearch.Special.AiryZeroLinearMoment

/-!
# `cts:tip-shared` (a): the Airy linear moment

`airyLinearMoment : AiryLinearMoment` (**proved, unconditional**): with `κ_comb = (3π/2)^{2/3}`,
`2 Σ_{k ≤ K} |a_k|/κ_comb - 2 ∫_{1/4}^{K+1/2} (a - 1/4)^{2/3} da = O(K^{-1/3})`.  This is the content of
`Special.AiryZeroLinearMoment` (`airyZero_linear_moment`) in the variable `a = u + 1/4`; the proof there is the
Hadamard sum rule with its two-term asymptotics (Riccati barrier for the three-term asymptotics of `Ai'/Ai`) and the
zero asymptotics of `AiryZeroSecondOrder`.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special

/-- **`cts:tip-shared` (a), the Airy linear moment** (`cts:airy-sum-zero`). -/
theorem airyLinearMoment : AiryLinearMoment := by
  obtain ⟨C, hC⟩ := airyZero_linear_moment
  refine ⟨2 * C, fun K hK => ?_⟩
  have h := hC K hK
  have e1 : ∫ a in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), (a - 1 / 4) ^ (2 / 3 : ℝ) =
      ∫ u in (0 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ) := by
    rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ (2 / 3 : ℝ)) (1 / 4 : ℝ)]
    norm_num
    ring_nf
  have e2 : 2 * ∑ k ∈ Finset.Icc 1 K, |airyZero k| / kappaComb =
      2 * ((∑ k ∈ Finset.Icc 1 K, |airyZero k|) / (3 * π / 2) ^ (2 / 3 : ℝ)) := by
    rw [Finset.sum_div]; rfl
  rw [e1, e2]
  have : 2 * ((∑ k ∈ Finset.Icc 1 K, |airyZero k|) / (3 * π / 2) ^ (2 / 3 : ℝ)) -
      2 * ∫ u in (0 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ) =
      2 * ((∑ k ∈ Finset.Icc 1 K, |airyZero k|) / (3 * π / 2) ^ (2 / 3 : ℝ) -
        ∫ u in (0 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ)) := by ring
  rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc _ ≤ 2 * (C * (K : ℝ) ^ (-(1 / 3) : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2 * C * (K : ℝ) ^ (-(1 / 3) : ℝ) := by ring

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyLinearMoment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyLinearMoment

end FormalResearch.ModularBootstrap.FiveTerm
