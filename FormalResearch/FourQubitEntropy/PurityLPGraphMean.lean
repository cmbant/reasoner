module

public import FormalResearch.FourQubitEntropy.PurityLPCutRank
public import FormalResearch.FourQubitEntropy.PurityLPCert

/-!
# Mean balanced purity of a graph state from a kernel-checked rank sum

`piMean_gsn`: for the normalised graph state `gsn (adjGraph adj)`, if the finite sum
`Σ_{|S| = k} 2^{k - rk_2 Γ[S,S^c]}` (evaluated by `decide +kernel` with the bitmask elimination `cutRankN`)
equals `N`, then `π_k = N / (2^k C(n,k))`.  (`rk_2 Γ[S,S^c] ≤ |S| = k` always.)
Source: `even_qubit_purity_minima.tex`, `thm:lptable`(2), `thm:fourteenfifteen`, `thm:sixteenseventeen`,
`balanced_purity_18.tex` `thm:eighteen`.
-/

@[expose] public section


open scoped BigOperators
open FormalResearch.NQubit

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

theorem cutRankN_le (adj : Fin n → ℕ) (S : Finset (Fin n)) : cutRankN adj S ≤ S.card := by
  rw [← cutRank_eq]
  have := Matrix.rank_le_card_height (cutMat (adjGraph adj) S)
  show (cutMat (adjGraph adj) S).rank ≤ S.card
  simpa using this

theorem piMean_gsn (adj : Fin n → ℕ) (hsym : ∀ i j : Fin n, (adj i).testBit j = (adj j).testBit i)
    (k N : ℕ) (hk : k ≤ n)
    (h : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, 2 ^ (k - cutRankN adj S) = N) :
    piMean (gsn (adjGraph adj)) k = (N : ℝ) / (2 ^ k * (Nat.choose n k : ℝ)) := by
  rw [piMean_eq_purMean]
  unfold purMean Pur PurU
  have hC : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      purity (gsn (adjGraph adj)) S = ((2 : ℝ) ^ (k - cutRankN adj S)) / 2 ^ k := by
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have hle : cutRankN adj S ≤ k := hcard ▸ cutRankN_le adj S
    rw [purity_gsn (adjGraph adj) (fun i j => hsym i j) S, cutRank_eq]
    rw [eq_div_iff h2]
    have h3 : (2 : ℝ) ^ k = 2 ^ (k - cutRankN adj S) * 2 ^ cutRankN adj S := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [h3, one_div, inv_pow]
    have h4 : (2 : ℝ) ^ cutRankN adj S ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, div_div]
  congr 1
  exact_mod_cast h

end FormalResearch.FourQubitEntropy.PurityLP
