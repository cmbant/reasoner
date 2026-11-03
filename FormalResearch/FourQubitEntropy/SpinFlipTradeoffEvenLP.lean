module

public import FormalResearch.FourQubitEntropy.PurityLPCert

/-!
# The Rains-LP step with the time-reversal term (`eq:tradeoff-dual`)

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex`, proof of
`thm:purity-spinflip-tradeoff` (certificates ST-1--ST-6).

A *tradeoff certificate* for `n` is `(L, c, es, ys)`: rational `L`, `c`, multipliers `es = [(s, e_s)]`
(`s ≤ n`, `e_s ∈ ℚ`) and `ys = [(i, y_i)]` (`y_i ≥ 0`).  Its residual is the linear form `w` in the Pauli weight
distribution `A` of the exact coefficientwise identity

`a_{n/2} - L A_0 - c 2^{-n} Σ_j (-1)^j A_j = Σ_s e_s (a_s - a_{n-s}) + Σ_i y_i S_i + Σ_j w_j A_j`,

`wCoefT` computes `w_j` in `ℚ` from the true coefficient functions `aQ` (`eq:as`) and `shQ` (shadow coefficients);
`lpCheckT` is the decidable test `y_i ≥ 0 ∧ w_j ≥ 0`.

* `lp_tradeoff`: if `lpCheckT n L c es ys = true` then **for every unit vector `ψ` of `n` qubits
  `L + c τ_n(ψ) ≤ π_{n/2}(ψ)`**, using `A_0 = 1`, `A_j ≥ 0`, `Σ_j (-1)^j A_j = 2^n τ_n` (`sum_signed_A`),
  `a_s = a_{n-s}` (`purMean_compl`) and the shadow inequalities (`shadow_nonneg`).  Claim class: proved.
-/

@[expose] public section


open scoped BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

/-- Residual coefficient with the time-reversal term: `wCoef - c (-1)^j / 2^n`. -/
def wCoefT (n : ℕ) (L c : ℚ) (es ys : List (ℕ × ℚ)) (j : ℕ) : ℚ :=
  wCoef n L es ys j - c * ((-1 : ℚ) ^ j / 2 ^ n)

/-- The decidable check of a tradeoff certificate. -/
def lpCheckT (n : ℕ) (L c : ℚ) (es ys : List (ℕ × ℚ)) : Bool :=
  es.all (fun p => decide (p.1 ≤ n)) && ys.all (fun p => decide (0 ≤ p.2)) &&
    (List.range (n + 1)).all fun j => decide (0 ≤ wCoefT n L c es ys j)

theorem lin_wCoefT (n : ℕ) (A : ℕ → ℝ) (L c : ℚ) (es ys : List (ℕ × ℚ)) :
    lin n A (wCoefT n L c es ys)
      = lin n A (wCoef n L es ys)
        - (c : ℝ) / 2 ^ n * ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * A j := by
  unfold wCoefT
  rw [lin_sub, Finset.mul_sum]
  congr 1
  unfold lin
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- **The LP step with the time-reversal term** (`eq:tradeoff-dual`): a passing tradeoff certificate gives
`L + c τ_n(ψ) ≤ π_{n/2}(ψ)` for every unit `n`-qubit vector. -/
theorem lp_tradeoff (n : ℕ) (L c : ℚ) (es ys : List (ℕ × ℚ)) (h : lpCheckT n L c es ys = true)
    (ψ : Ψ n) (hψ : nsq ψ = 1) : (L : ℝ) + (c : ℝ) * tau ψ ≤ purMean ψ (n / 2) := by
  simp only [lpCheckT, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨hes, hys⟩, hw⟩ := h
  set A' : ℕ → ℝ := fun j => A ψ j with hA'
  have hk : n / 2 ≤ n := Nat.div_le_self n 2
  have hlin : ∀ s, s ≤ n → lin n A' (aQ n s) = purMean ψ s := fun s hs =>
    (purMean_eq_lin ψ hs).symm
  have hw' : 0 ≤ lin n A' (wCoefT n L c es ys) := by
    unfold lin
    refine Finset.sum_nonneg fun j hj => mul_nonneg ?_ (A_nonneg ψ j)
    exact_mod_cast hw j (Finset.mem_range.mp hj)
  rw [lin_wCoefT, lin_wCoef] at hw'
  have hes0 : (es.map fun p => (p.2 : ℝ) * (lin n A' (aQ n p.1) - lin n A' (aQ n (n - p.1)))).sum
      = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hp1 := hes p hp
    rw [hlin p.1 hp1, hlin (n - p.1) (Nat.sub_le _ _), purMean_compl ψ hp1]
    ring
  have hys0 : 0 ≤ (ys.map fun p => (p.2 : ℝ) * lin n A' (shQ n p.1)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have : lin n A' (shQ n p.1) = shadowCoeff ψ p.1 := by
      rw [shadowCoeff_eq_lin]; rfl
    rw [this]
    exact mul_nonneg (by exact_mod_cast hys p hp) (shadow_nonneg ψ p.1)
  have hsgn : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * A' j = (2 : ℝ) ^ n * tau ψ :=
    sum_signed_A ψ
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hcτ : (c : ℝ) / 2 ^ n * ((2 : ℝ) ^ n * tau ψ) = c * tau ψ := by
    field_simp
  rw [hes0, hlin (n / 2) hk, hsgn, hcτ] at hw'
  have hA0 : A' 0 = 1 := A_zero ψ hψ
  rw [hA0] at hw'
  linarith

end FormalResearch.FourQubitEntropy.PurityLP
