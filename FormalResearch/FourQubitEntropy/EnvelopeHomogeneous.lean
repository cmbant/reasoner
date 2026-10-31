import FormalResearch.FourQubitEntropy.GeneralEnvelope

/-!
# `thm:fqe-general-envelope`, the homogeneous form (GE) for every nonzero vector

`general_envelope_homog` (`eq:fqe-general-envelope` of `sextic_identity.tex`): for `ψ ≠ 0`, with
`N = ‖ψ‖²`, `s = ψᵀ ε^{⊗4} ψ`,
`F - (3/4) N W₁ - N |s|² + |s|³ ≥ 7|s|²/(8(N + |s|)) W₁`. Proved by scaling the unit-state theorem
`general_envelope_unit` (`GeneralEnvelope.lean`) by `(√N)⁻¹`, using the homogeneity of `F` (degree 6), `N`
(degree 2), `W₁` (degree 4) and `s` (degree 2).
-/

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy

theorem general_envelope_homog_aux (ψ : Psi) (hN : 0 < normSqPsi ψ) :
    3 / 4 * normSqPsi ψ * blochSq ψ
      + 7 * Complex.normSq (spinFlipForm ψ) /
          (8 * (normSqPsi ψ + Real.sqrt (Complex.normSq (spinFlipForm ψ)))) * blochSq ψ
      + normSqPsi ψ * Complex.normSq (spinFlipForm ψ)
      - Real.sqrt (Complex.normSq (spinFlipForm ψ)) ^ 3 ≤ sexticF ψ := by
  set N := normSqPsi ψ with hNdef
  set τ := Complex.normSq (spinFlipForm ψ) with hτdef
  set σ := Real.sqrt τ with hσ
  have hτ0 : 0 ≤ τ := Complex.normSq_nonneg _
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = τ := Real.sq_sqrt hτ0
  set c := (Real.sqrt N)⁻¹ with hc
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hc0 : 0 < c := inv_pos.2 hsN
  have hc2 : c ^ 2 * N = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt hN.le]; field_simp
  have h1 : normSqPsi (c • ψ) = 1 := by rw [normSqPsi_smulR]; exact hc2
  have key := general_envelope_unit (c • ψ) h1
  have hF : sexticF (c • ψ) = c ^ 6 * sexticF ψ := sexticF_smul c ψ
  have hW : blochSq (c • ψ) = c ^ 4 * blochSq ψ := blochSq_smul c ψ
  have hs : Complex.normSq (spinFlipForm (c • ψ)) = c ^ 4 * τ := by
    rw [real_smul_eq, spinFlipForm_smulC, map_mul, map_pow, Complex.normSq_ofReal]
    rw [hτdef]; ring
  have hsq : Real.sqrt (c ^ 4 * τ) = c ^ 2 * σ := by
    rw [show c ^ 4 * τ = (c ^ 2) ^ 2 * τ by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hF, hW, hs, hsq] at key
  have hNs : 0 < N + σ := by positivity
  have hden : 0 < 1 + c ^ 2 * σ := by positivity
  have hNc : N = 1 / c ^ 2 := by field_simp; linarith
  have e1 : c ^ 6 * (3 / 4 * N * blochSq ψ + 7 * τ / (8 * (N + σ)) * blochSq ψ + N * τ - σ ^ 3)
      = (3 / 4 + 7 * (c ^ 4 * τ) / (8 * (1 + c ^ 2 * σ))) * (c ^ 4 * blochSq ψ) + c ^ 4 * τ
        - c ^ 4 * τ * (c ^ 2 * σ) := by
    rw [hNc]
    have hc0' : c ≠ 0 := hc0.ne'
    have : (1 : ℝ) / c ^ 2 + σ = (1 + c ^ 2 * σ) / c ^ 2 := by field_simp
    rw [this, ← hσ2]
    field_simp
  have : c ^ 6 * (3 / 4 * N * blochSq ψ + 7 * τ / (8 * (N + σ)) * blochSq ψ + N * τ - σ ^ 3)
      ≤ c ^ 6 * sexticF ψ := by rw [e1]; exact key
  exact le_of_mul_le_mul_left this (by positivity)


/-- **`thm:fqe-general-envelope`, homogeneous form (GE), every nonzero vector** (`eq:fqe-general-envelope`):
with `N = ‖ψ‖²`, `s = ψᵀ ε^{⊗4} ψ` and `|s|² = normSq s`,
`F - (3/4) N W₁ - N |s|² + |s|³ ≥ 7|s|²/(8(N + |s|)) W₁`. -/
theorem general_envelope_homog (ψ : Psi) (hψ : ψ ≠ 0) :
    7 * Complex.normSq (spinFlipForm ψ) /
        (8 * (normSqPsi ψ + Real.sqrt (Complex.normSq (spinFlipForm ψ)))) * blochSq ψ
      ≤ sexticF ψ - 3 / 4 * normSqPsi ψ * blochSq ψ - normSqPsi ψ * Complex.normSq (spinFlipForm ψ)
        + Real.sqrt (Complex.normSq (spinFlipForm ψ)) ^ 3 := by
  have hN : 0 < normSqPsi ψ := by
    rcases lt_or_eq_of_le (normSqPsi_nonneg ψ) with h | h
    · exact h
    · exact absurd (psi_zero_of_normSqPsi_zero h.symm) hψ
  have := general_envelope_homog_aux ψ hN
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.general_envelope_homog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms general_envelope_homog

end FormalResearch.FourQubitEntropy
