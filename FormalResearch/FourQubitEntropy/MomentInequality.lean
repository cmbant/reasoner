import FormalResearch.FourQubitEntropy.Bridge

/-!
# The sharp sextic moment inequality for four qubits

For every `ψ ∈ (ℂ²)^{⊗4}`, with `n = ‖ψ‖²`, `P = Σ_j tr R_{1j}²`, `T = Σ_j tr R_{1j}³` and
`W₁ = Σ_i |r_i|²` the squared unnormalised Bloch vectors,
`F = 17 n P - 12 T - 12 n³ ≥ (15/32) n W₁ ≥ 0`.

The proof is the identity `1152 F = 540 n W₁ + 3 Σ_i 36 ‖R_i‖²` (`sexticDefect_zero`), where
`R_i` is the residual tensor of the swap derivation: the `R_i` are sums of squared norms, hence
nonnegative.

Trust: the polynomial identity `sexticDefect_check` in `Identity.lean` is decided by
`native_decide`, so it rests on the Lean compiler as well as the kernel.
-/

open scoped ComplexConjugate
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- `1152 F = 540 n W₁ + 3 Σ_i 36 ‖R_i‖²` with the four residual norms nonnegative. -/
theorem sextic_identity (ψ : Psi) :
    ∃ r : ℝ, 0 ≤ r ∧
      1152 * sexticF ψ = 540 * (normSqPsi ψ * blochSq ψ) + 3 * r := by
  have hd := sexticDefect_zero ψ ψ.conj
  obtain ⟨r0, h0, e0⟩ := resNorm0_nonneg ψ
  obtain ⟨r1, h1, e1⟩ := resNorm0_nonneg (siteSwap 1 ψ)
  obtain ⟨r2, h2, e2⟩ := resNorm0_nonneg (siteSwap 2 ψ)
  obtain ⟨r3, h3, e3⟩ := resNorm0_nonneg (siteSwap 3 ψ)
  refine ⟨r0 + r1 + r2 + r3, by positivity, ?_⟩
  simp only [sexticDefect, defectG, siteSwap_conj, toAdd_complex, toMul_complex, toSub_complex,
    lit_complex] at hd
  rw [Fgen_eq, W1gen_eq, normG_eq, e0, e1, e2, e3] at hd
  have hr : (1152 * sexticF ψ - 540 * (normSqPsi ψ * blochSq ψ) - 3 * (r0 + r1 + r2 + r3) : ℝ)
      = 0 := by
    exact_mod_cast hd
  linarith

theorem blochSq_nonneg (ψ : Psi) : 0 ≤ blochSq ψ := by
  unfold blochSq
  positivity

theorem normSqPsi_nonneg (ψ : Psi) : 0 ≤ normSqPsi ψ := by
  unfold normSqPsi
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- **Sharp sextic moment inequality**: `F ≥ (15/32) n W₁`. -/
theorem sexticF_ge (ψ : Psi) : 15 / 32 * (normSqPsi ψ * blochSq ψ) ≤ sexticF ψ := by
  obtain ⟨r, hr, h⟩ := sextic_identity ψ
  linarith

/-- `F ≥ 0`. -/
theorem sexticF_nonneg (ψ : Psi) : 0 ≤ sexticF ψ :=
  le_trans (by have := normSqPsi_nonneg ψ; have := blochSq_nonneg ψ; positivity) (sexticF_ge ψ)

end FormalResearch.FourQubitEntropy
