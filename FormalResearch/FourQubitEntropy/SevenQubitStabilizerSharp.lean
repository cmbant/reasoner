module

public import FormalResearch.FourQubitEntropy.SevenQubitStabilizer
public import FormalResearch.FourQubitEntropy.SevenQubitStab7
public import FormalResearch.NQubit.Graph.MeanPurity
public import FormalResearch.NQubit.Graph.Stabilizer

/-!
# Seven-qubit stabilizer states: the minimum of `π₃` is exactly `19/140` (`prop:stab7`, sharpness)

`QI/multiqubit_entanglement/seven_qubit_entanglement/icosahedral_state.tex`, `prop:stab7`: every seven-qubit
stabilizer state has `π₃ ≥ 19/140` (`SevenQubitStabilizer.stab7`), and this is attained.

The attaining state is the normalised graph state of the Fano/wheel graph `witnessGraph = 0x00cf17` of
`SevenQubitStab7` (GS-4).  Here the graph is given by its seven neighbourhood bitmasks `adjW`
(`adjW_spec`: they are the adjacency of `SevenQubitStab7.adj witnessGraph`), the cut-rank sum
`Σ_{|S| = 3} 2^{3 - rk_2 Γ[S,S^c]} = 38` is kernel-checked on the library's `graphCutRankBits`
(`rankSumW`), and `meanRdmPurity_graphStateNorm` turns it into `π₃ = 38 / (2³ · 35) = 19/140`
(`meanPurity_graphW`).  The graph state is a stabilizer state by `Graph/Stabilizer`
(`graphStateNorm_isStabilizerState`), so `19/140` is attained, and `stab7` bounds every stabilizer state from below:

* `stab7_sharp`: `IsLeast {π₃ ψ : ψ a seven-qubit stabilizer state} (19/140)`.

Claim class: proved; the finite check `rankSumW` is an exact kernel certificate (`decide +kernel`).
-/

@[expose] public section

open scoped BigOperators
open FormalResearch.NQubit FormalResearch.NQubit.Shadow FormalResearch.NQubit.Reduced
  FormalResearch.NQubit.TimeReversal
  FormalResearch.NQubit.Graph

namespace FormalResearch.FourQubitEntropy.SevenQubitStabilizer

/-- Neighbourhood bitmasks (bit `j` of row `i` set iff `i ~ j`) of the witness graph `0x00cf17`. -/
def adjW : Fin 7 → ℕ := fun i => ([46, 113, 73, 21, 10, 3, 6] : List ℕ).getD i.1 0

/-- The bitmasks are the adjacency of `witnessGraph` in the `21`-bit lexicographic edge encoding of
`SevenQubitStab7`. -/
theorem adjW_spec : ∀ i j : Fin 7,
    (adjW i).testBit j = SevenQubitStab7.adj SevenQubitStab7.witnessGraph i j := by
  decide +kernel

theorem adjW_symm : ∀ i j : Fin 7, (adjW i).testBit j = (adjW j).testBit i := by
  decide +kernel

theorem adjW_irrefl : ∀ i : Fin 7, (adjW i).testBit i = false := by
  decide +kernel

/-- `Σ_{|S| = 3} 2^{3 - rk_2 Γ[S,S^c]} = 38` for the witness graph (kernel certificate). -/
theorem rankSumW : ∑ S ∈ ((Finset.univ : Finset (Fin 7)).powersetCard 3),
    2 ^ (3 - graphCutRankBits adjW S) = 38 := by
  decide +kernel

/-- The witness graph state has `π₃ = 19/140`. -/
theorem meanPurity_graphW : meanPurity (graphStateNorm (adjGraph adjW)) 3 = 19 / 140 := by
  rw [← meanRdmPurity_eq_meanPurity,
    meanRdmPurity_graphStateNorm adjW adjW_symm 3 38 (by norm_num) rankSumW]
  norm_num [Nat.choose]

/-- The witness graph state is a seven-qubit stabilizer state. -/
theorem isStabilizerState_graphW : IsStabilizerState (graphStateNorm (adjGraph adjW)) :=
  graphStateNorm_isStabilizerState _ (fun i j => adjW_symm i j) fun i => adjW_irrefl i

/-- **`prop:stab7`, sharp form**: the minimum of `π₃` over seven-qubit stabilizer states is exactly `19/140`. -/
theorem stab7_sharp :
    IsLeast {x : ℝ | ∃ ψ : Ψ 7, IsStabilizerState ψ ∧ meanPurity ψ 3 = x} (19 / 140) :=
  ⟨⟨_, isStabilizerState_graphW, meanPurity_graphW⟩, fun _ ⟨ψ, hψ, hx⟩ => hx ▸ stab7 ψ hψ⟩

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitStabilizer.stab7_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stab7_sharp

end FormalResearch.FourQubitEntropy.SevenQubitStabilizer
