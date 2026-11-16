module

public import Mathlib

/-!
# Mercator series for finite products

For a finite family `y i` with `|y i| < 1`, the logarithm of `∏ (1 - y i)` is a convergent power
series in the power sums of the `y i` (Mercator's series summed over the family):

  `∑_{i∈s} log (1 - y i) = - ∑_{n ≥ 1} (∑_{i∈s} (y i)^n) / n`   (`hasSum_log_one_sub_finset`).

Used in `FormalResearch.Racah.P2CtLogSeries` for the central factorial products.
-/

@[expose] public section

namespace FormalResearch.Asymptotics

open Finset

/-- **Mercator series for a finite family.**  If `|y i| < 1` for `i ∈ s`, the series
`n ↦ -(∑_{i∈s} (y i)^(n+1)) / (n+1)` has sum `∑_{i∈s} log (1 - y i)`. -/
theorem hasSum_log_one_sub_finset {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (hy : ∀ i ∈ s, |y i| < 1) :
    HasSum (fun n : ℕ => -((∑ i ∈ s, y i ^ (n + 1)) / ((n : ℝ) + 1)))
      (∑ i ∈ s, Real.log (1 - y i)) := by
  have h : HasSum (fun n : ℕ => ∑ i ∈ s, y i ^ (n + 1) / ((n : ℝ) + 1))
      (∑ i ∈ s, -Real.log (1 - y i)) :=
    hasSum_sum fun i hi => Real.hasSum_pow_div_log_of_abs_lt_one (hy i hi)
  have h2 := h.neg
  rw [← sum_neg_distrib] at h2
  simpa [sum_div, sum_neg_distrib] using h2

end FormalResearch.Asymptotics
