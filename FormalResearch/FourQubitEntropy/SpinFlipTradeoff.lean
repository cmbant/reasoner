module

public import FormalResearch.FourQubitEntropy.SpinFlipOmega

/-!
# The four-qubit purity--time-reversal identity and its stability corollary

Source: `QI/multiqubit_entanglement/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200),
`thm:purity-spinflip-tradeoff` at `n = 4` (the identity `π_2 = 1/3 + (W_1 + τ_4)/6` with `W_1 = A_1`) and
`cor:spinflip-rigidity` at `n = 4`.  The entries `n = 8, 10, 14, 16, 20` rest on Rains' shadow inequalities
and rational certificates (`ST-1--ST-6`) and are *not* formalised here.  Claim class: **proved**.
-/

@[expose] public section


open FormalResearch.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

open FormalResearch.NQubit.Pauli FormalResearch.NQubit.Reduced FormalResearch.NQubit.TimeReversal

theorem tradeoff_four (ψ : Ψ 4) (hψ : nsq ψ = 1) :
    cutPuritySum ψ 2 / 6 = 1 / 3 + (weightEnum ψ 1 + tau ψ) / 6 := by
  have hsum := sum_weightEnum ψ
  have hsgn := sum_signed_weightEnum ψ
  have hA0 := weightEnum_zero ψ
  have hE1 := cutPuritySum_eq ψ 1
  have hE2 := cutPuritySum_eq ψ 2
  have hE3 := cutPuritySum_eq ψ 3
  have hC1 := cutPuritySum_compl ψ 1 (by norm_num)
  rw [hψ] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hsum hsgn hA0 hE1 hE2 hE3 hC1 ⊢
  linear_combination (1/2) * hA0 + (-1/96) * hsum + (1/96) * hsgn + (1/12) * hE1 + (1/24) * hE2 + (-1/48) * hE3 + (-1/6) * hC1


/-- `thm:purity-spinflip-tradeoff` at `n = 4`: `π_2 ≥ 1/3 + τ_4/6`. -/
theorem tradeoff_four_ge (ψ : Ψ 4) (hψ : nsq ψ = 1) :
    1 / 3 + tau ψ / 6 ≤ cutPuritySum ψ 2 / 6 := by
  rw [tradeoff_four ψ hψ]
  have := weightEnum_nonneg ψ 1
  linarith

/-- `cor:spinflip-rigidity` at `n = 4`: `π_2(ψ) ≤ 1/3 + δ` forces `τ_4(ψ) ≤ 6 δ`
(`c_4 = 1/6`); in particular a minimiser (`π_2 = 1/3`) has `τ_4 = 0`. -/
theorem tradeoff_four_stability (ψ : Ψ 4) (hψ : nsq ψ = 1) (δ : ℝ) (h : cutPuritySum ψ 2 / 6 ≤ 1 / 3 + δ) :
    tau ψ ≤ 6 * δ := by
  have := tradeoff_four_ge ψ hψ
  linarith

end FormalResearch.FourQubitEntropy.SpinFlip
