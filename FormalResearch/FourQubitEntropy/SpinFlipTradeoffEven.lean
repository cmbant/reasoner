import FormalResearch.FourQubitEntropy.SpinFlipTradeoffEvenCert
import FormalResearch.FourQubitEntropy.SpinFlipTradeoffEvenGraphA
import FormalResearch.FourQubitEntropy.SpinFlipTradeoffEvenGraph16
import FormalResearch.FourQubitEntropy.SpinFlipTradeoffEvenGraph20

/-!
# The even-`n` purity--spin-flip tradeoff (`thm:purity-spinflip-tradeoff`, ST-2--ST-6)

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex`, `thm:purity-spinflip-tradeoff` and
`cor:spinflip-rigidity`, for `n ∈ {8, 10, 14, 16, 20}` (the entry `n = 4` is `SpinFlip.tradeoff_four_ge` /
`purity_tradeoff`).  Every normalised pure `n`-qubit state satisfies

  `π_{n/2}(ψ) ≥ L_n + c_n τ_n(ψ)`,      `π_{n/2} = piMean ψ (n/2)`, `τ_n = tau ψ = |⟨ψ, Θψ⟩|² = |ψᵀ ε^{⊗n} ψ|²`,

with `(n : L_n, c_n) = 8 : 3/35, 1/70; 10 : 1/21, 1/168; 14 : 331/27456, 5/6864; 16 : 1/156, 1/1716;
20 : 1193/739024, 103/1478048`.

* `purity_spinflip_tradeoff_even` : the inequality (the dual certificates are `tradeoffBound<n>` in
  `SpinFlipTradeoffEvenCert.lean`: the exact linear identity `eq:tradeoff-dual` in the Pauli weight enumerator `A_j` and the
  shadow enumerator `S_i`, checked by `decide +kernel`, then `lp_tradeoff`);
* `purity_spinflip_tradeoff_even_sharp` : the sharpness clause, for one explicit graph state per `n` all of whose vertices have
  odd degree (`tau_gsn_eq_one` is the general `τ_n = 1` statement; `piMean_graphT<n>` the kernel-checked purities
  `π_{n/2} = L_n + c_n`);
* `purity_spinflip_tradeoff_even_coeff_optimal` : `c_n` is the largest coefficient compatible with `L_n`;
* `purity_spinflip_tradeoff_even_stability` : `cor:spinflip-rigidity`;
* `tau_eq_normSq_bilinear` : `τ_n = |Σ_{x,y} ψ_x ε^{⊗n}_{xy} ψ_y|²` (so `τ_n = |ψᵀσ_y^{⊗n}ψ|²`, as `ε = iσ_y`).

Claim class: proved (exact-rational certificates and exact finite computations checked in the kernel).
-/

open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

/-- The table `L_n` of `thm:purity-spinflip-tradeoff` (`n ∈ {8, 10, 14, 16, 20}`; `0` elsewhere). -/
def tradeoffL (n : ℕ) : ℚ :=
  match n with
  | 8 => 3 / 35
  | 10 => 1 / 21
  | 14 => 331 / 27456
  | 16 => 1 / 156
  | 20 => 1193 / 739024
  | _ => 0

/-- The table `c_n` of `thm:purity-spinflip-tradeoff` (`n ∈ {8, 10, 14, 16, 20}`; `0` elsewhere). -/
def tradeoffC (n : ℕ) : ℚ :=
  match n with
  | 8 => 1 / 70
  | 10 => 1 / 168
  | 14 => 5 / 6864
  | 16 => 1 / 1716
  | 20 => 103 / 1478048
  | _ => 0

/-- The sizes `n` treated here. -/
def TradeoffEvenSize (n : ℕ) : Prop := n = 8 ∨ n = 10 ∨ n = 14 ∨ n = 16 ∨ n = 20

theorem tradeoffC_pos {n : ℕ} (hn : TradeoffEvenSize n) : 0 < tradeoffC n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num [tradeoffC]

/-- **`thm:purity-spinflip-tradeoff`** (even `n ∈ {8, 10, 14, 16, 20}`): every normalised pure `n`-qubit state has
`π_{n/2}(ψ) ≥ L_n + c_n τ_n(ψ)`. -/
theorem purity_spinflip_tradeoff_even {n : ℕ} (hn : TradeoffEvenSize n) (ψ : Ψ n) (hψ : nsq ψ = 1) :
    (tradeoffL n : ℝ) + (tradeoffC n : ℝ) * tau ψ ≤ piMean ψ (n / 2) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · simpa [tradeoffL, tradeoffC] using tradeoffBound8 ψ hψ
  · simpa [tradeoffL, tradeoffC] using tradeoffBound10 ψ hψ
  · simpa [tradeoffL, tradeoffC] using tradeoffBound14 ψ hψ
  · simpa [tradeoffL, tradeoffC] using tradeoffBound16 ψ hψ
  · simpa [tradeoffL, tradeoffC] using tradeoffBound20 ψ hψ

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.purity_spinflip_tradeoff_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms purity_spinflip_tradeoff_even

/-- **Sharpness clause of `thm:purity-spinflip-tradeoff`**: for each `n ∈ {8, 10, 14, 16, 20}` there is a graph state (all
vertices of odd degree) with `τ_n = 1` and `π_{n/2} = L_n + c_n`. -/
theorem purity_spinflip_tradeoff_even_sharp {n : ℕ} (hn : TradeoffEvenSize n) :
    ∃ ψ : Ψ n, nsq ψ = 1 ∧ tau ψ = 1 ∧ piMean ψ (n / 2) = (tradeoffL n : ℝ) + (tradeoffC n : ℝ) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · refine ⟨gsn (adjGraph adjT8), nsq_gsn _, tau_gsn_eq_one _ adjT8_symm adjT8_irrefl adjT8_odd, ?_⟩
    rw [show (8 : ℕ) / 2 = 4 from rfl, piMean_graphT8]; norm_num [tradeoffL, tradeoffC]
  · refine ⟨gsn (adjGraph adjT10), nsq_gsn _, tau_gsn_eq_one _ adjT10_symm adjT10_irrefl adjT10_odd, ?_⟩
    rw [show (10 : ℕ) / 2 = 5 from rfl, piMean_graphT10]; norm_num [tradeoffL, tradeoffC]
  · refine ⟨gsn (adjGraph adjT14), nsq_gsn _, tau_gsn_eq_one _ adjT14_symm adjT14_irrefl adjT14_odd, ?_⟩
    rw [show (14 : ℕ) / 2 = 7 from rfl, piMean_graphT14]; norm_num [tradeoffL, tradeoffC]
  · refine ⟨gsn (adjGraph adjT16), nsq_gsn _, tau_gsn_eq_one _ adjT16_symm adjT16_irrefl adjT16_odd, ?_⟩
    rw [show (16 : ℕ) / 2 = 8 from rfl, piMean_graphT16]; norm_num [tradeoffL, tradeoffC]
  · refine ⟨gsn (adjGraph adjT20), nsq_gsn _, tau_gsn_eq_one _ adjT20_symm adjT20_irrefl adjT20_odd, ?_⟩
    rw [show (20 : ℕ) / 2 = 10 from rfl, piMean_graphT20]; norm_num [tradeoffL, tradeoffC]

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.purity_spinflip_tradeoff_even_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms purity_spinflip_tradeoff_even_sharp

/-- **`c_n` is the largest coefficient compatible with the constant `L_n`**: if
`π_{n/2} ≥ L_n + c τ_n` on all unit states, then `c ≤ c_n`. -/
theorem purity_spinflip_tradeoff_even_coeff_optimal {n : ℕ} (hn : TradeoffEvenSize n) (c : ℝ)
    (h : ∀ ψ : Ψ n, nsq ψ = 1 → (tradeoffL n : ℝ) + c * tau ψ ≤ piMean ψ (n / 2)) :
    c ≤ (tradeoffC n : ℝ) := by
  obtain ⟨ψ, hψ, hτ, hπ⟩ := purity_spinflip_tradeoff_even_sharp hn
  have := h ψ hψ
  rw [hτ, hπ] at this
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.purity_spinflip_tradeoff_even_coeff_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms purity_spinflip_tradeoff_even_coeff_optimal

/-- **`cor:spinflip-rigidity`** (all five sizes): `π_{n/2}(ψ) ≤ L_n + δ` forces `τ_n(ψ) ≤ δ / c_n`; in particular
`π_{n/2}(ψ) = L_n` forces `τ_n(ψ) = 0`, i.e. `⟨ψ, Θψ⟩ = 0`. -/
theorem purity_spinflip_tradeoff_even_stability {n : ℕ} (hn : TradeoffEvenSize n) (ψ : Ψ n) (hψ : nsq ψ = 1)
    (δ : ℝ) (h : piMean ψ (n / 2) ≤ (tradeoffL n : ℝ) + δ) : tau ψ ≤ δ / (tradeoffC n : ℝ) := by
  have hc : (0 : ℝ) < (tradeoffC n : ℝ) := by exact_mod_cast tradeoffC_pos hn
  have := purity_spinflip_tradeoff_even hn ψ hψ
  rw [le_div_iff₀ hc]
  nlinarith

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.purity_spinflip_tradeoff_even_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms purity_spinflip_tradeoff_even_stability

/-- `π_{n/2}(ψ) = L_n` forces `⟨ψ, Θψ⟩ = 0` (the `δ = 0` case of `cor:spinflip-rigidity`). -/
theorem purity_spinflip_tradeoff_even_minimiser {n : ℕ} (hn : TradeoffEvenSize n) (ψ : Ψ n) (hψ : nsq ψ = 1)
    (h : piMean ψ (n / 2) = (tradeoffL n : ℝ)) : ip ψ (Θ ψ) = 0 := by
  have h1 := purity_spinflip_tradeoff_even_stability hn ψ hψ 0 (by rw [h]; simp)
  have h2 : tau ψ = 0 := le_antisymm (by simpa using h1) (tau_nonneg ψ)
  unfold tau at h2
  exact Complex.normSq_eq_zero.mp h2

/-- `τ_n = |ψᵀ ε^{⊗n} ψ|²` with `ψᵀ ε^{⊗n} ψ = Σ_{x,y} ψ_x (Π_i ε_{x_i y_i}) ψ_y`; as `ε = iσ_y` this is
`|ψᵀ σ_y^{⊗n} ψ|²`, the `τ_n` of `thm:purity-spinflip-tradeoff`. -/
theorem tau_eq_normSq_bilinear {n : ℕ} (ψ : Ψ n) :
    tau ψ = Complex.normSq (∑ x, ∑ y, ψ x * (∏ i, eps (x i) (y i)) * ψ y) := by
  unfold tau
  rw [← Complex.normSq_conj]
  congr 1
  unfold ip Θ
  simp only [map_sum, map_mul, map_prod, Complex.conj_conj, conj_eps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end FormalResearch.FourQubitEntropy.PurityLP
