import FormalResearch.FourQubitEntropy.EnvelopeProductZero

/-!
# `thm:fqe-general-envelope`: the equality classification

Paper: `ResearchNotes/QI/four_qubit_entropy/sextic_identity.tex`, `thm:fqe-general-envelope`
("Equality in `F ≥ (3/4) W₁ + τ - τ^{3/2}` holds exactly on fully product states and on the critical
equality family of Proposition `prop:fqe-critical-envelope`, including its HS endpoint at `τ = 0` and
Bell-pair-product endpoint at `τ = 1`").

**Headline** `envelope_equality_iff`: for unit `ψ`,
`F ψ = (3/4) W₁ + τ - τ √τ ↔ IsProduct ψ ∨ CritEqFamily ψ`, no further hypotheses.

* `IsProduct ψ` (`EnvelopeProduct.lean`): `ψ = α ⊗ β ⊗ γ ⊗ δ`.
* `CritEqFamily ψ` (`EnvelopeCriticalClass.lean`): `∃ v`, `‖v‖ = 1`, `ψ` is a local-unitary image
  (`LUEquiv`) of `G(v)`, and `CritForm √τ (critTheta v)`, i.e. the Bloch correlation matrix
  `Θ_{αβ} = ⟨φ|σ_α ⊗ σ_β|φ⟩`, `φ = Σ_k v_k m_k`, of the critical normal vector equals
  `O (κ I + (1-κ) s sᵀ)` with `O` one of the twelve signed cyclic permutation matrices whose three signs
  have product `-1` and `s ∈ {±1}³/√3` — exactly the paper's description. (`critical_envelope_eq_iff_vector`
  shows the condition holds for *every* unit normal vector `v` of an equality state, not only for some.)

Proof structure (the paper's): equality forces `W₁ = 0` unless `τ = 0` (`general_envelope_unit`); critical
case: the permanent classification (`EnvelopeCriticalClass.lean`, `EnvelopePermClass.lean`); `τ = 0`,
`W₁ > 0`: product states (`H_zero_product`, `EnvelopeProductZero.lean`); conversely product states
(`product_values`) and the family attain equality.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

open FormalResearch.FourQubitEntropy.PaperECritical

open FormalResearch.FourQubitEntropy.PaperECritical

/-- **`thm:fqe-general-envelope`, complete equality** (`sextic_identity.tex`): for a unit four-qubit
state `ψ` with `τ = |ψᵀ ε^{⊗4} ψ|²`,
`F = (3/4) W₁ + τ - τ^{3/2}` (equality in the weak form of the general envelope) holds **iff** `ψ` is fully
product or lies in the critical equality family of `prop:fqe-critical-envelope`: `ψ ≃ G(v)` for a unit
critical normal vector `v` whose Bloch correlation matrix is
`Θ = O (κ I + (1-κ) s sᵀ)`, `κ = √τ`, `O` a signed cyclic permutation matrix with sign product `-1`,
`s ∈ {±1}³/√3` (`CritEqFamily`). The family includes its HS endpoint `τ = 0` and its Bell-pair-product
endpoint `τ = 1` (`critEqFamily_endpoints`). -/
theorem envelope_equality_iff (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    sexticF ψ = 3 / 4 * blochSq ψ + Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ↔ IsProduct ψ ∨ CritEqFamily ψ := by
  constructor
  · intro h
    have hG := general_envelope_unit ψ hψ
    have hW0 := blochSq_nonneg ψ
    have hτ0 := Complex.normSq_nonneg (spinFlipForm ψ)
    set τ := Complex.normSq (spinFlipForm ψ) with hτdef
    have hc : 0 ≤ 7 * τ / (8 * (1 + Real.sqrt τ)) := by positivity
    rw [h] at hG
    have hcW : 7 * τ / (8 * (1 + Real.sqrt τ)) * blochSq ψ ≤ 0 := by linarith
    rcases eq_or_lt_of_le hW0 with hW | hW
    · right
      refine (critical_envelope_eq_iff ψ hψ hW.symm).1 ?_
      rw [h, ← hW]; ring
    · left
      have hc0 : 7 * τ / (8 * (1 + Real.sqrt τ)) = 0 := by
        by_contra hne
        have := mul_pos (lt_of_le_of_ne hc (Ne.symm hne)) hW
        linarith
      have hτ : τ = 0 := by
        have h8 : 0 < 8 * (1 + Real.sqrt τ) := by positivity
        have : 7 * τ = 0 := by
          rcases div_eq_zero_iff.1 hc0 with h1 | h1
          · exact h1
          · exact absurd h1 h8.ne'
        linarith
      have hs : spinFlipForm ψ = 0 := Complex.normSq_eq_zero.1 hτ
      apply H_zero_product ψ hψ hs _ hW
      rw [h, hτ]; simp
  · rintro (hP | hF)
    · obtain ⟨hF3, hW4, hs⟩ := product_values hP
      rw [hψ] at hF3 hW4
      rw [hs]; simp; rw [hF3, hW4]; norm_num
    · have hW : blochSq ψ = 0 := by
        obtain ⟨v, -, hv, -⟩ := hF
        exact blochSq_zero_of_LU_Gv v ψ hv
      have := (critical_envelope_eq_iff ψ hψ hW).2 hF
      rw [hW]; linarith


/-- The equality family quantifies over *every* unit normal vector: for a critical unit state and any
unit `v` with `ψ ≃ G(v)`, equality in `(CE)` holds iff `Θ(v) = O(κ I + (1-κ) s sᵀ)`. -/
theorem critical_envelope_eq_iff_vector {ψ : Psi} {v : Fin 2 × Fin 2 → ℂ} (hψ : normSqPsi ψ = 1)
    (hv : LUEquiv (Gv v) ψ) :
    sexticF ψ = Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ↔ CritForm (Real.sqrt (Complex.normSq (spinFlipForm ψ))) (critTheta v) := by
  obtain ⟨hn, hF, hτ⟩ := LU_Gv_data hψ hv
  rw [hτ, hF]
  exact critical_unit_iff v hn

/-- The family contains states of every `τ ∈ [0, 1]` ("such states exist for every `τ`"). -/
theorem critEqFamily_exists (κ : ℝ) (h0 : 0 ≤ κ) (h1 : κ ≤ 1) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ Complex.normSq (spinFlipForm ψ) = κ ^ 2 ∧ CritEqFamily ψ := by
  obtain ⟨ψ, hψ, hW, hs, hF⟩ := critical_envelope_attained κ h0 h1
  exact ⟨ψ, hψ, hs, (critical_envelope_eq_iff ψ hψ hW).1 hF⟩

/-- The endpoints of the family: at `τ = 0` (HS) and `τ = 1` (Bell-pair products) the equality states are
zeros of `F`, i.e. the five orbits of `prop:fqe-moment-zeros`. -/
theorem critEqFamily_endpoints {ψ : Psi} (hψ : normSqPsi ψ = 1) (hf : CritEqFamily ψ)
    (hτ : Complex.normSq (spinFlipForm ψ) = 0 ∨ Complex.normSq (spinFlipForm ψ) = 1) :
    ZeroOrbit ψ := by
  have hW : blochSq ψ = 0 := by
    obtain ⟨v, -, hv, -⟩ := hf
    exact blochSq_zero_of_LU_Gv v ψ hv
  have hF := (critical_envelope_eq_iff ψ hψ hW).2 hf
  refine (moment_zeros ψ hψ).1 ?_
  rw [hF]
  rcases hτ with h | h <;> rw [h] <;> simp

/-- info: 'FormalResearch.FourQubitEntropy.envelope_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms envelope_equality_iff

end FormalResearch.FourQubitEntropy
