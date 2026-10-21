import FormalResearch.FourQubitEntropy.ClassifyMain
import FormalResearch.FourQubitEntropy.EqualityConverse

/-!
# The equality case of the four-qubit entropy bound

For a unit vector `ψ`, the mean entropy of the three marginals containing qubit `1` equals
`1 + ½ log₂ 3` exactly when `ψ` is a local-unitary image of `M₄` or of `conj M₄`.
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

/-- `P = 1` for a unit vector forces `W₁ = 0` and `ψᵀ ε^{⊗4} ψ = 0`. -/
theorem purity_one_forces (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1) :
    blochSq ψ = 0 ∧ spinFlipForm ψ = 0 := by
  have hd := purityDefect_zero ψ ψ.conj
  obtain ⟨τ, hτ, e⟩ : NonnegReal (spinFlipForm ψ * spinFlipForm ψ.conj) := by
    rw [spinFlipForm_conj]; exact NonnegReal.mul_conj _
  simp only [purityDefect, toAdd_complex, toMul_complex, toSub_complex, lit_complex] at hd
  rw [W1gen_eq, normG_eq, e, tr2_marg12, tr2_marg13, tr2_marg14,
    trace_sq_real (red12_herm ψ), trace_sq_real (red13_herm ψ), trace_sq_real (red14_herm ψ)] at hd
  have hc : (((2 * purity ψ - 2 * normSqPsi ψ ^ 2 - blochSq ψ - τ : ℝ)) : ℂ) = 0 := by
    unfold purity
    push_cast at hd ⊢
    linear_combination hd
  have h0 : (2 * purity ψ - 2 * normSqPsi ψ ^ 2 - blochSq ψ - τ : ℝ) = 0 := by exact_mod_cast hc
  have hW := blochSq_nonneg ψ
  rw [hn, hP] at h0
  have hW0 : blochSq ψ = 0 := by linarith
  have hτ0 : τ = 0 := by linarith
  refine ⟨hW0, ?_⟩
  rw [spinFlipForm_conj, hτ0] at e
  simp only [Complex.ofReal_zero] at e
  rcases mul_eq_zero.mp e with h | h
  · exact h
  · simpa using h

/-- **Equality case.** A unit vector attains the maximal mean entropy `1 + ½ log₂ 3` if and only if
it is a local-unitary image of `M₄` or of `conj M₄`. -/
theorem meanEntropy_eq_max_iff (ψ : Psi) (hn : normSqPsi ψ = 1) :
    meanEntropy ψ = 1 + Real.log 3 / (2 * Real.log 2) ↔
      LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  constructor
  · intro heq
    obtain ⟨hP, e12, -, -⟩ := equality_conditions ψ hn heq
    obtain ⟨hW, hτ⟩ := purity_one_forces ψ hn hP
    rcases classify ψ hn hW (quadratic_of_eigenvalues (red12_herm ψ) e12) hτ with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact meanEntropy_of_LU M4_unit M4_cutQuadratics h
    · exact meanEntropy_of_LU (by rw [normSqPsi_conj]; exact M4_unit) M4_cutQuadratics.conj h

end FormalResearch.FourQubitEntropy
