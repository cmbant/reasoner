module

public import FormalResearch.FourQubitEntropy.RenyiFullSHLargeTail
public import FormalResearch.FourQubitEntropy.RenyiFullRD

/-!
# `lem:fqe-small-head-dual`: proved

Paper E, `renyi_small_head_dual.tex`.  At `q = q_s = 1587/1000` and `θ = (aL, bL, gL) = (397/100, 3/20, 159/100)`,
every ordered spectrum `(a, b, c, c)` with `a ≤ 1/2` has `Λ_θ ≤ 8023/4800`.

With `u = 2c`, `δ = a - b` the chart is `((1-u+δ)/2, (1-u-δ)/2, u/2, u/2)`, `0 ≤ δ ≤ min(u, 1-2u)`, `0 ≤ u ≤ 1/2`;
the small tail `u ≤ 1/4` is `sh_small_tail` (head/tail Jensen, `D_q` bound, `A_q` staircase, quartic bounds) and the
large tail `u ≥ 1/4` is `sh_large_tail` (near-uniform moment bound and one Bernstein cell).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

/-- **`lem:fqe-small-head-dual`.** -/
theorem smallHeadDual : SmallHeadDual := by
  intro a b c hc hcb hba ha hs
  have hl : (![a, b, c, c] : Fin 4 → ℝ) =
      ![(1 - 2 * c + (a - b)) / 2, (1 - 2 * c - (a - b)) / 2, 2 * c / 2, 2 * c / 2] := by
    ext i; fin_cases i <;> simp <;> linarith
  rw [hl]
  have hu0 : 0 ≤ 2 * c := by linarith
  have hδ0 : 0 ≤ a - b := by linarith
  have hδu : a - b ≤ 2 * c := by linarith
  have hδ2 : a - b ≤ 1 - 2 * (2 * c) := by linarith
  rcases le_total (2 * c) (1 / 4) with h | h
  · exact sh_small_tail hu0 h hδ0 hδu
  · exact sh_large_tail h (by linarith) hδ0 hδu hδ2

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.smallHeadDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smallHeadDual

end FormalResearch.FourQubitEntropy.RenyiFull
