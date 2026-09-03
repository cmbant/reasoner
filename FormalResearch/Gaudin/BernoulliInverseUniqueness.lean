import Mathlib
import FormalResearch.Gaudin.BernoulliInverseRecurrence

namespace FormalResearch.Gaudin

/-- The Bernoulli--Chebyshev inverse-column convolution equations determine
every finite coefficient prefix uniquely.  Thus the triangular recurrence is
not merely a way to generate candidate coefficients: it is forced by the
matrix inverse equations. -/
theorem bernoulli_inverse_prefix_unique
    {j N : Nat} (t u : Nat → ℚ) (hj : 1 ≤ j)
    (ht0 : bernoulliInverseConvolution j 0 t = 1)
    (hu0 : bernoulliInverseConvolution j 0 u = 1)
    (ht : ∀ n, 1 ≤ n → n ≤ N → bernoulliInverseConvolution j n t = 0)
    (hu : ∀ n, 1 ≤ n → n ≤ N → bernoulliInverseConvolution j n u = 0) :
    ∀ n, n ≤ N → t n = u n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnN
      by_cases hn0 : n = 0
      · subst n
        rw [bernoulli_inverse_initial t hj ht0,
          bernoulli_inverse_initial u hj hu0]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        rw [bernoulli_inverse_raw_recurrence t hj hn1 (ht n hn1 hnN),
          bernoulli_inverse_raw_recurrence u hj hn1 (hu n hn1 hnN)]
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        have hpn : p < n := Finset.mem_range.mp hp
        rw [ih p hpn (by omega)]

/-- Infinite uniqueness form: a normalized inverse column satisfying all
Bernoulli--Chebyshev convolution equations is unique. -/
theorem bernoulli_inverse_unique
    {j : Nat} (t u : Nat → ℚ) (hj : 1 ≤ j)
    (ht0 : bernoulliInverseConvolution j 0 t = 1)
    (hu0 : bernoulliInverseConvolution j 0 u = 1)
    (ht : ∀ n, 1 ≤ n → bernoulliInverseConvolution j n t = 0)
    (hu : ∀ n, 1 ≤ n → bernoulliInverseConvolution j n u = 0) :
    t = u := by
  funext n
  exact bernoulli_inverse_prefix_unique t u hj ht0 hu0
    (N := n)
    (fun m hm hmN => ht m hm)
    (fun m hm hmN => hu m hm)
    n le_rfl

end FormalResearch.Gaudin
