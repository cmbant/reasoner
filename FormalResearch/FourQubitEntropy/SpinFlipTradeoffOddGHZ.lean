module

public import FormalResearch.FourQubitEntropy.SpinFlipTradeoffOddGeneral
public import FormalResearch.NQubit.Pauli.GHZ

/-!
# `O(GHZ_n) = 0` for odd `n`

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200),
`thm:odd-spinflip-tradeoff`: the GHZ state attains the bound (`ghz_odd_tradeoff_sharp_eq` in
`SpinFlipTradeoffOddSharp.lean`).  `Omean_ghz` is `O(GHZ_n) = 0`.

Claim class: **proved**.
-/

@[expose] public section


open Finset
open FormalResearch.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

open FormalResearch.NQubit.Pauli FormalResearch.NQubit.Reduced FormalResearch.NQubit.TimeReversal

variable {m : ℕ}

theorem Omean_ghz (hm : 1 ≤ m) : Omean (ghz (2 * m + 1)) = 0 := by
  rw [Omean_eq (by omega)]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjn : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
  by_cases ho : Odd j
  · rcases hjn.lt_or_eq with h | h
    · rw [weightEnum_ghz_odd (by omega) ho h, mul_zero]
    · subst h
      simp
  · simp [ho]

end FormalResearch.FourQubitEntropy.SpinFlip
