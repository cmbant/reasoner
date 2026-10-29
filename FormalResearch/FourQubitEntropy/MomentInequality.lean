import FormalResearch.FourQubitEntropy.Bridge

/-!
# The sharp sextic moment inequality for four qubits

For every `ψ ∈ (ℂ²)^{⊗4}`, with `n = ‖ψ‖²`, `P = Σ_j tr R_{1j}²`, `T = Σ_j tr R_{1j}³` and
`W₁ = Σ_i |r_i|²` the squared unnormalised Bloch vectors,
`F = 17 n P - 12 T - 12 n³ ≥ (3/4) n W₁ ≥ 0`, and `3/4` is the best constant (`sexticF_ge_sharp`
in `Checks.lean`: every product state has `F = 3`, `n = 1`, `W₁ = 4`).
This is `thm:fqe-moment`. The paper's `thm:fqe-general-envelope` (not formalized) is stronger for
unit states with spin-flip overlap `τ > 0`: `F ≥ (3/4 + 7τ/(8(1+√τ))) W₁ + τ - τ^{3/2}`. It reduces to
`F ≥ (3/4) W₁` at `τ = 0`, so the constant `3/4` is still optimal for the `τ`-free bound proved here.

The proof is the identity
`8F = 6 n W₁ + 3 Σᵢ ‖Vᵢ - 8Uᵢ‖² + 12 Σ_{i<j} ‖(Rᵢ^{(i)} - Rⱼ^{(j)}) z‖²` (`sexticDefect_zero`).
Here `Uᵢ = Sᵢ ∏_{j≠i} Lⱼ w` and `Vᵢ = Sᵢ ∏_{j≠i} (Lⱼ + Mⱼ) w` for `w = z ⊗ z ⊗ z̃`, `Sᵢ` the
symmetriser of the three copies at qubit `i`, and `Rᵢ^{(i)}` the unnormalised one-qubit marginal
acting on qubit `i` of `z`. The two sums are sums of squared norms, hence nonnegative.

Trust: the polynomial identity `sexticDefect_check` in `Identity.lean` is checked by the kernel alone
(`decide +kernel`; no `native_decide`), so everything here uses only `propext`, `Classical.choice` and
`Quot.sound`. Building `Identity.lean` and its `IdentityCert*.lean` pieces needs about 9 GB of RAM per file;
see the *Machine requirements* paragraph of `Identity.lean`.
-/

open scoped ComplexConjugate
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- `96 F = 72 n W₁ + r + 144 s` with `r = Σᵢ 36 ‖Vᵢ - 8Uᵢ‖²` and
`s = Σ_{i<j} ‖(Rᵢ^{(i)} - Rⱼ^{(j)}) z‖²` nonnegative; that is `8F = 6 n W₁ + 3 Σᵢ ‖Vᵢ - 8Uᵢ‖²
+ 12 Σ_{i<j} ‖…‖²`. -/
theorem sextic_identity (ψ : Psi) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧
      96 * sexticF ψ = 72 * (normSqPsi ψ * blochSq ψ) + r + 144 * s := by
  have hd := sexticDefect_zero ψ ψ.conj
  obtain ⟨r0, h0, e0⟩ := resNorm0_nonneg ψ
  obtain ⟨r1, h1, e1⟩ := resNorm0_nonneg (siteSwap 1 ψ)
  obtain ⟨r2, h2, e2⟩ := resNorm0_nonneg (siteSwap 2 ψ)
  obtain ⟨r3, h3, e3⟩ := resNorm0_nonneg (siteSwap 3 ψ)
  obtain ⟨s, hs, es⟩ := pairSum_nonneg ψ
  refine ⟨r0 + r1 + r2 + r3, s, by positivity, hs, ?_⟩
  simp only [sexticDefect, defectG, siteSwap_conj, toAdd_complex, toMul_complex, toSub_complex,
    lit_complex] at hd
  rw [Fgen_eq, W1gen_eq, normG_eq, e0, e1, e2, e3, es] at hd
  have hr : (96 * sexticF ψ - 72 * (normSqPsi ψ * blochSq ψ) - (r0 + r1 + r2 + r3) - 144 * s : ℝ)
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

/-- **Sharp sextic moment inequality** (`thm:fqe-moment`): `F ≥ (3/4) n W₁`. This is the `τ`-free
bound; for unit states the paper's `thm:fqe-general-envelope` (not formalized) adds `τ - τ^{3/2}` and
`7τ W₁/(8(1+√τ))` to the right-hand side. -/
theorem sexticF_ge (ψ : Psi) : 3 / 4 * (normSqPsi ψ * blochSq ψ) ≤ sexticF ψ := by
  obtain ⟨r, s, hr, hs, h⟩ := sextic_identity ψ
  linarith

/-- `F ≥ 0`. -/
theorem sexticF_nonneg (ψ : Psi) : 0 ≤ sexticF ψ :=
  le_trans (by have := normSqPsi_nonneg ψ; have := blochSq_nonneg ψ; positivity) (sexticF_ge ψ)

end FormalResearch.FourQubitEntropy
