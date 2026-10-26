import FormalResearch.FourQubitEntropy.Checks

/-!
# The `n = 4` purity--time-reversal tradeoff, and the three Bell pairings

Remark `rem:fqe-spinflip-tradeoff` at `n = 4`: with `π₂ = P/3` the mean purity of the balanced
marginals and `τ = |ψᵀ σ_y^{⊗4} ψ|²`, every unit state has `π₂ ≥ 1/3 + τ/6`. The coefficient `1/6` is the
largest possible, attained by a product of two Bell pairs (`τ = 1`). The same product states for the
other two pairings of the qubits are zeros of `F` (Theorem `thm:fqe-moment`).
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

/-- `π₂ = 1/3 + (W₁ + τ)/6` for unit states. -/
theorem meanPurity_eq (ψ : Psi) (hn : normSqPsi ψ = 1) :
    purity ψ / 3 = 1 / 3 + (blochSq ψ + Complex.normSq (spinFlipForm ψ)) / 6 := by
  have h := purity_identity_exact ψ
  rw [hn] at h
  linarith

/-- The `n = 4` tradeoff: `π₂ ≥ 1/3 + τ/6`. -/
theorem purity_tradeoff (ψ : Psi) (hn : normSqPsi ψ = 1) :
    1 / 3 + Complex.normSq (spinFlipForm ψ) / 6 ≤ purity ψ / 3 := by
  have := blochSq_nonneg ψ
  rw [meanPurity_eq ψ hn]
  linarith

/-- `τ = 1` for the product of two Bell pairs, which has `π₂ = 1/2 = 1/3 + 1/6`. -/
theorem bell2_tau : Complex.normSq (spinFlipForm bell2) = 1 := by
  obtain ⟨h1, h2, -, h4⟩ := bell2_vals
  have := purity_identity_exact bell2
  rw [h1, h2, h4] at this
  linarith

/-- The coefficient `1/6` cannot be improved. -/
theorem purity_tradeoff_coeff_optimal (c : ℝ)
    (h : ∀ ψ : Psi, normSqPsi ψ = 1 →
      1 / 3 + c * Complex.normSq (spinFlipForm ψ) ≤ purity ψ / 3) : c ≤ 1 / 6 := by
  have := h bell2 bell2_vals.1
  rw [bell2_tau, bell2_vals.2.1] at this
  linarith

/-! ### The three pairings -/

/-- Product of two Bell pairs on the pairing `13|24`. -/
noncomputable def bell13 : Psi := fun a b c d => if a = c ∧ b = d then 1 / 2 else 0
/-- Product of two Bell pairs on the pairing `14|23`. -/
noncomputable def bell14 : Psi := fun a b c d => if a = d ∧ b = c then 1 / 2 else 0

theorem bell13_vals : normSqPsi bell13 = 1 ∧ purity bell13 = 3 / 2 ∧ cubicMoment bell13 = 9 / 8 ∧
    blochSq bell13 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> eval_state bell13

theorem bell14_vals : normSqPsi bell14 = 1 ∧ purity bell14 = 3 / 2 ∧ cubicMoment bell14 = 9 / 8 ∧
    blochSq bell14 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> eval_state bell14

theorem bell13_F : sexticF bell13 = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := bell13_vals
  unfold sexticF; rw [h1, h2, h3]; norm_num

theorem bell14_F : sexticF bell14 = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := bell14_vals
  unfold sexticF; rw [h1, h2, h3]; norm_num

end FormalResearch.FourQubitEntropy
