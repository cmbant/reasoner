import FormalResearch.FourQubitEntropy.SpinFlipTradeoffOddGeneral
import FormalResearch.FourQubitEntropy.SpinFlipOddGHZ

/-!
# The GHZ state attains the odd-`n` tradeoff bound; weight values

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200),
`thm:odd-spinflip-tradeoff`: "The bound is attained by the GHZ state for every odd `n`", and the listed
weight values.

* `ghz_odd_tradeoff_eq`: for every `n = 2m+1 ≥ 5`, `π_m(GHZ_n) + (n-3)/2 · O(GHZ_n) = 1/2`
  (from `odd_tradeoff_eq_iff` and `A_ghz_odd`);
* `Omean_ghz`: `O(GHZ_n) = 0`, hence `purMean_ghz`: `π_m(GHZ_n) = 1/2`;
* `oddW_five`, `oddW_seven_one`, `oddW_seven_three`, `oddW_nine_*`: the displayed weights
  `1/5`, `3/28`, `3/140`, `31/576, 67/5376, 29/8064, 1/2304`.

Claim class: **proved**.
-/

open Finset
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {m : ℕ}

theorem Omean_ghz (hm : 1 ≤ m) : Omean (ghz (2 * m + 1)) = 0 := by
  rw [Omean_eq (by omega)]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjn : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
  by_cases ho : Odd j
  · rcases hjn.lt_or_eq with h | h
    · rw [A_ghz_odd (by omega) ho h, mul_zero]
    · subst h
      simp
  · simp [ho]

/-- `thm:odd-spinflip-tradeoff`: the GHZ state attains the bound, for every odd `n = 2m + 1 ≥ 5`. -/
theorem ghz_odd_tradeoff_eq (hm : 2 ≤ m) :
    purMean (ghz (2 * m + 1)) m + ((((2 * m + 1 : ℕ) : ℝ) - 3) / 2) * Omean (ghz (2 * m + 1)) = 1 / 2 := by
  rw [odd_tradeoff_eq_iff hm _ (nsq_ghz (by omega))]
  intro j hj ho _
  exact A_ghz_odd (by omega) ho (mem_range.mp hj)

/-- The mean `m`-qubit marginal purity of GHZ is `1/2`. -/
theorem purMean_ghz (hm : 2 ≤ m) : purMean (ghz (2 * m + 1)) m = 1 / 2 := by
  have h := ghz_odd_tradeoff_eq hm
  rw [Omean_ghz (by omega), mul_zero, add_zero] at h
  exact h

theorem oddW_five : oddW 2 1 = 1 / 5 := by
  norm_num [oddW, oddNum, Nat.choose]

theorem oddW_seven_one : oddW 3 1 = 3 / 28 := by
  norm_num [oddW, oddNum, Nat.choose]

theorem oddW_seven_three : oddW 3 3 = 3 / 140 := by
  norm_num [oddW, oddNum, Nat.choose]

theorem oddW_nine_one : oddW 4 1 = 31 / 576 := by
  norm_num [oddW, oddNum, Nat.choose]

theorem oddW_nine_three : oddW 4 3 = 67 / 5376 := by
  norm_num [oddW, oddNum, Nat.choose]

theorem oddW_nine_five : oddW 4 5 = 29 / 8064 := by
  norm_num [oddW, oddNum, Nat.choose]

theorem oddW_nine_seven : oddW 4 7 = 1 / 2304 := by
  norm_num [oddW, oddNum, Nat.choose]

end FormalResearch.FourQubitEntropy.SpinFlip
