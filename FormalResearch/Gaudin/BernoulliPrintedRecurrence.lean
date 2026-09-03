import Mathlib
import FormalResearch.Gaudin.BernoulliInverseRecurrence

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- Exact reindexing `s=n-p` from the normalized triangular recurrence to the
form printed in the Bernoulli--Chebyshev handoff. -/
theorem bernoulli_inverse_printed_recurrence {j n : Nat} (t : Nat → ℚ)
    (hj : 1 ≤ j) (hn : 1 ≤ n)
    (hconv : bernoulliInverseConvolution j n t = 0) :
    t n =
      -∑ s ∈ Finset.Icc 1 n,
        ((Nat.choose (j + n - 1) (2 * s) : ℚ) /
          ((2 * s + 1 : Nat) : ℚ)) * t (n - s) := by
  rw [bernoulli_inverse_normalized_recurrence t hj hn hconv]
  apply congrArg Neg.neg
  refine Finset.sum_bij (fun p hp => n - p) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_Icc]
    have hp' := Finset.mem_range.mp hp
    omega
  · intro p₁ hp₁ p₂ hp₂ hEq
    have hp₁' := Finset.mem_range.mp hp₁
    have hp₂' := Finset.mem_range.mp hp₂
    omega
  · intro s hs
    rw [Finset.mem_Icc] at hs
    refine ⟨n - s, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro p hp
    have hp' := Finset.mem_range.mp hp
    have hback : n - (n - p) = p := by omega
    simp [hback]

end FormalResearch.Gaudin
