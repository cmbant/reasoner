module

public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumLimit
public import FormalResearch.ModularBootstrap.Upper.Window.Quadrature
public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxTail

/-!
# The node tail of the approximating designs (Theorem 2.5, Step 1)

For `ν > K` the node value of the design `negDesign α K n η q` is a bounded multiple of the weight
`Π_ν(0)` of the `f = 1` design `D(N, η, 0)` of `ut:V`: `nodeC D ν = G_ν · Π_ν(0)` with `|G_ν| ≤ M`, `M` independent
of `ν`, `n ≥ K` and `η ∈ (0, 1/4]`.  Hence by Lemma E (`ut:E`, `lemma_E`) the tail `Σ_{ν > K}` of the node sum is
`O(η² + N^{-1/3})`.  The estimate is the case `s = clarkNode α`, `p = z₁ - η` of `IdealApprox.tail_sum_bound`
(arbitrary sites `s_k`, `K ≥ 2`, first zero `p` in a bounded set).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap.Upper.Window

/-- **The node tail of the designs is `O(η² + N^{-1/3})`** (`ut:E`): for `n ≥ K`, `N = n + 2 ≥ N₀`,
`0 < η ≤ 1/4`, `|Σ_{ν > K} Re nodeC D ν| ≤ M (η² + N^{-1/3})`. -/
theorem tail_sum_bound (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (q : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n : ℕ, K ≤ n → N₀ ≤ n + 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
      |∑' m : ℕ, (nodeC (clarkNode α 1 - η) q (siteSeq α K n) (widthSeq n η) (K + 1 + m)).re| ≤
        M * (η ^ 2 + ((n + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨M, hM0, N₀, hM⟩ := IdealApprox.tail_sum_bound (clarkNode α) (by omega : 2 ≤ K) q
    (|airyZero 1 - clarkNode α 1| + 1 / 4)
  refine ⟨M, hM0, N₀, fun n hn hN η hη hη1 => hM n hn hN η _ hη hη1 ?_⟩
  have h1 : airyZero 1 - (clarkNode α 1 - η) = (airyZero 1 - clarkNode α 1) + η := by ring
  rw [h1]
  calc |(airyZero 1 - clarkNode α 1) + η| ≤ |airyZero 1 - clarkNode α 1| + |η| := abs_add_le _ _
    _ ≤ |airyZero 1 - clarkNode α 1| + 1 / 4 := by rw [abs_of_pos hη]; linarith

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum.tail_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_sum_bound

end FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum
