module

public import FormalResearch.NQubit.Graph.CutRankBitmask

/-!
# Mean balanced purity of a graph state from a cut-rank sum

`meanRdmPurity_graphStateNorm`: for the normalised graph state `graphStateNorm (adjGraph adj)`, if the finite sum
`Σ_{|S| = k} 2^{k - rk_2 Γ[S,S^c]}` (with `graphCutRankBits`) equals `N`, then
`meanRdmPurity _ k = N / (2^k C(n,k))`.  (`rk_2 Γ[S,S^c] ≤ |S| = k` always: `graphCutRankBits_le`.)
-/

@[expose] public section


open scoped BigOperators
open FormalResearch.NQubit.Pauli
open FormalResearch.NQubit.Reduced
open FormalResearch.NQubit.TimeReversal

namespace FormalResearch.NQubit.Graph

variable {n : ℕ}

theorem graphCutRankBits_le (adj : Fin n → ℕ) (S : Finset (Fin n)) : graphCutRankBits adj S ≤ S.card := by
  rw [← graphCutRank_eq_bits]
  have := Matrix.rank_le_card_height (cutMat (adjGraph adj) S)
  show (cutMat (adjGraph adj) S).rank ≤ S.card
  simpa using this

theorem meanRdmPurity_graphStateNorm (adj : Fin n → ℕ) (hsym : ∀ i j : Fin n, (adj i).testBit j = (adj j).testBit i)
    (k N : ℕ) (hk : k ≤ n)
    (h : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, 2 ^ (k - graphCutRankBits adj S) = N) :
    meanRdmPurity (graphStateNorm (adjGraph adj)) k = (N : ℝ) / (2 ^ k * (Nat.choose n k : ℝ)) := by
  rw [meanRdmPurity_eq_meanPurity]
  unfold meanPurity cutPuritySum cutPuritySumOn
  have hC : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      cutPurity (graphStateNorm (adjGraph adj)) S = ((2 : ℝ) ^ (k - graphCutRankBits adj S)) / 2 ^ k := by
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have hle : graphCutRankBits adj S ≤ k := hcard ▸ graphCutRankBits_le adj S
    rw [purity_gsn (adjGraph adj) (fun i j => hsym i j) S, graphCutRank_eq_bits]
    rw [eq_div_iff h2]
    have h3 : (2 : ℝ) ^ k = 2 ^ (k - graphCutRankBits adj S) * 2 ^ graphCutRankBits adj S := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [h3, one_div, inv_pow]
    have h4 : (2 : ℝ) ^ graphCutRankBits adj S ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, div_div]
  congr 1
  exact_mod_cast h

end FormalResearch.NQubit.Graph
