import FormalResearch.FourQubitEntropy.EnvelopeTheta

/-!
# `prop:fqe-critical-envelope` in full: closed form and equality classification

Paper: `ResearchNotes/QI/four_qubit_entropy/sextic_identity.tex`, `prop:fqe-critical-envelope` (the
critical envelope `F = 1/2 + 7τ/4 + 9 perm Θ/4 ≥ τ - τ^{3/2}`, its equality family
`Θ = O(κ I + (1-κ) s sᵀ)`, and the moment form on the critical locus).

Objects: `critTheta v` (`EnvelopeTheta.lean`) is the Bloch correlation matrix `Θ_{αβ} = ⟨φ|σ_α ⊗ σ_β|φ⟩`
of `φ = Σ_k v_k m_k`, for a critical normal vector `v` (`ψ ≃ G(v)`, `‖v‖ = 1`); `CritForm κ Θ` says
`Θ = O (κ I + (1-κ) s sᵀ)` with `O` one of the twelve signed cyclic permutation matrices with sign
product `-1` and `s ∈ {±1}³/√3` (`EnvelopePermClass.lean`).

* `critical_closed_form`: `F ψ = 1/2 + (7/4) τ + (9/4) perm Θ` for every unit `ψ` with `ψ ≃ G(v)`.
* `critical_envelope_perm`: `F ≥ τ - τ^{3/2}` for such `ψ`, proved from the closed form and the permanent bound
  `perm Θ ≥ -(2 + 3κ² + 4κ³)/9` (the paper's proof; `critical_envelope` in `GeneralEnvelope.lean` is the
  independent proof from the general envelope).
* `critical_unit_iff`: for a unit normal vector `v`, `F(G(v)) = τ - τ^{3/2}` iff `CritForm √τ (critTheta v)`.
* `CritEqFamily ψ`: the critical equality family: `ψ ≃ G(v)` for a unit `v` with `CritForm κ Θ(v)`, `κ = |s(ψ)|`.
* `critical_envelope_eq_iff`: for critical unit `ψ`, equality in `(CE)` iff `CritEqFamily ψ`
  (including the HS endpoint `τ = 0` and the Bell-pair-product endpoint `τ = 1`).
* `critical_purity` (`P = 1 + τ/2`), `critical_moment_envelope` (the moment form of `(CE)`),
  `critical_moment_envelope_attained` (attained for every `P ∈ [1, 3/2]`).
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

open FormalResearch.FourQubitEntropy.PaperECritical

theorem normSq_det_unitary {u : Op1} (hu : uᴴ * u = 1) : Complex.normSq u.det = 1 := by
  have h := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have : ((Complex.normSq u.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast this

theorem normSq_spinFlip_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) :
    Complex.normSq (spinFlipForm ψ) = Complex.normSq (spinFlipForm φ) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  rw [spinFlip_localApply]
  simp only [map_mul]
  rw [normSq_det_unitary ha, normSq_det_unitary hb, normSq_det_unitary hc, normSq_det_unitary hd]
  ring

theorem blochSq_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) : blochSq ψ = blochSq φ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hψ⟩ := h
  have h1 := purity_identity_exact ψ
  have h2 := purity_identity_exact φ
  have hP : purity ψ = purity φ := by rw [← hψ]; exact purity_localApply ha hb hc hd φ
  have hn : normSqPsi ψ = normSqPsi φ := normSqPsi_LUEquiv ⟨a, b, c, d, ha, hb, hc, hd, hψ⟩
  have ht := normSq_spinFlip_LUEquiv (⟨a, b, c, d, ha, hb, hc, hd, hψ⟩ : LUEquiv φ ψ)
  rw [hP, hn, ht] at h1
  linarith

/-- The critical equality family of `prop:fqe-critical-envelope`: `ψ` is local-unitarily equivalent to
`G(v)` for a unit critical normal vector `v` whose Bloch correlation matrix is
`Θ = O (κ I + (1-κ) s sᵀ)`, `κ = |ψᵀ ε^{⊗4} ψ|`, `O` a signed cyclic permutation matrix with sign
product `-1`, `s ∈ {±1}³/√3`. -/
def CritEqFamily (ψ : Psi) : Prop :=
  ∃ v : Fin 2 × Fin 2 → ℂ, nV v = 1 ∧ LUEquiv (Gv v) ψ ∧
    CritForm (Real.sqrt (Complex.normSq (spinFlipForm ψ))) (critTheta v)

theorem tauV_eq_normSq (v : Fin 2 × Fin 2 → ℂ) : tauV v = Complex.normSq (spinFlipForm (Gv v)) := by
  rw [spinFlipForm_Gv]; rfl

theorem nV_eq (v : Fin 2 × Fin 2 → ℂ) : nV v = normSqPsi (Gv v) := (Gv_n v).symm

/-- `prop:fqe-critical-envelope`, equality, at the level of the normal vector. -/
theorem critical_unit_iff (v : Fin 2 × Fin 2 → ℂ) (hv : nV v = 1) :
    sexticF (Gv v) = tauV v - tauV v * Real.sqrt (tauV v) ↔
      CritForm (Real.sqrt (tauV v)) (critTheta v) := by
  have hb := critBloch_dot v
  have hτ0 : 0 ≤ tauV v := Complex.normSq_nonneg _
  have hdot : 0 ≤ critBloch v ⬝ᵥ critBloch v := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [mul_self_nonneg (critBloch v 0), mul_self_nonneg (critBloch v 1),
      mul_self_nonneg (critBloch v 2)]
  rw [hv] at hb
  have hτ1 : tauV v ≤ 1 := by nlinarith
  set κ := Real.sqrt (tauV v) with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = tauV v := Real.sq_sqrt hτ0
  have hκ1 : κ ≤ 1 := by nlinarith
  have hF := sexticF_Gv_perm v
  rw [hv] at hF
  obtain ⟨-, hcls⟩ := perm_class (critTheta v) (critBloch v) κ hκ0 hκ1
    (by rw [critTheta_gram, hκ2]) (by rw [hb, hκ2]; ring)
    (by rw [critTheta_det, hv, hκ2]; ring)
  rw [← hcls]
  rw [hF]
  unfold pmax
  rw [← hκ2]
  constructor <;> intro h <;> nlinarith [h]


/-- Data of a unit normal vector `v` of a critical unit `ψ`: `ψ` and `G(v)` have the same `n, F, τ`. -/
theorem LU_Gv_data {ψ : Psi} {v : Fin 2 × Fin 2 → ℂ} (hψ : normSqPsi ψ = 1)
    (hv : LUEquiv (Gv v) ψ) :
    nV v = 1 ∧ sexticF ψ = sexticF (Gv v) ∧ Complex.normSq (spinFlipForm ψ) = tauV v := by
  refine ⟨?_, sexticF_LUEquiv hv, ?_⟩
  · rw [nV_eq, ← normSqPsi_LUEquiv hv, hψ]
  · rw [tauV_eq_normSq]; exact normSq_spinFlip_LUEquiv hv

/-- **`prop:fqe-critical-envelope`, equality (up to local unitaries).** For a critical unit state
(`W₁ = 0`), equality in `F ≥ τ - τ^{3/2}` holds iff `ψ` is in the critical equality family, i.e. iff its
critical normal vector has `Θ = O(κ I + (1-κ) s sᵀ)`. -/
theorem critical_envelope_eq_iff (ψ : Psi) (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    sexticF ψ = Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ↔ CritEqFamily ψ := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := critical_LU_Gv ψ hW
    obtain ⟨hn, hF, hτ⟩ := LU_Gv_data hψ hv
    refine ⟨v, hn, hv, ?_⟩
    rw [hτ] at h ⊢
    exact (critical_unit_iff v hn).1 (by rw [← hF]; exact h)
  · rintro ⟨v, hn, hv, hform⟩
    obtain ⟨-, hF, hτ⟩ := LU_Gv_data hψ hv
    rw [hτ] at hform ⊢
    rw [hF]
    exact (critical_unit_iff v hn).2 hform

/-- The closed form of `eq:fqe-critical-envelope`: for a unit `ψ` with unit normal vector `v`
(`ψ ≃ G(v)`), `F = 1/2 + (7/4) τ + (9/4) perm Θ`. -/
theorem critical_closed_form {ψ : Psi} {v : Fin 2 × Fin 2 → ℂ} (hψ : normSqPsi ψ = 1)
    (hv : LUEquiv (Gv v) ψ) :
    sexticF ψ = 1 / 2 + 7 / 4 * Complex.normSq (spinFlipForm ψ) + 9 / 4 * perm3 (critTheta v) := by
  obtain ⟨hn, hF, hτ⟩ := LU_Gv_data hψ hv
  rw [hF, sexticF_Gv_perm, hn, hτ]
  ring

/-- `(CE)` via the permanent: `F ≥ τ - τ^{3/2}` for critical unit `ψ`, from the closed form and
`perm Θ ≥ -(2 + 3κ² + 4κ³)/9`. (An independent proof of `critical_envelope`.) -/
theorem critical_envelope_perm {ψ : Psi} {v : Fin 2 × Fin 2 → ℂ} (hψ : normSqPsi ψ = 1)
    (hv : LUEquiv (Gv v) ψ) :
    Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ≤ sexticF ψ := by
  obtain ⟨hn, hF, hτ⟩ := LU_Gv_data hψ hv
  have hb := critBloch_dot v
  have hτ0 : 0 ≤ tauV v := Complex.normSq_nonneg _
  have hdot : 0 ≤ critBloch v ⬝ᵥ critBloch v := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [mul_self_nonneg (critBloch v 0), mul_self_nonneg (critBloch v 1),
      mul_self_nonneg (critBloch v 2)]
  rw [hn] at hb
  have hτ1 : tauV v ≤ 1 := by nlinarith
  set κ := Real.sqrt (tauV v) with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = tauV v := Real.sq_sqrt hτ0
  have hκ1 : κ ≤ 1 := by nlinarith
  obtain ⟨hge, -⟩ := perm_class (critTheta v) (critBloch v) κ hκ0 hκ1
    (by rw [critTheta_gram, hκ2]) (by rw [hb, hκ2]; ring)
    (by rw [critTheta_det, hn, hκ2]; ring)
  have hF' := critical_closed_form hψ hv
  rw [hτ] at hF' ⊢
  unfold pmax at hge
  rw [← hκ, hF', ← hκ2]
  nlinarith [hge]

/-- For a critical unit state, `P = 1 + τ/2` (`prop:fqe-critical-envelope`). -/
theorem critical_purity (ψ : Psi) (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    purity ψ = 1 + Complex.normSq (spinFlipForm ψ) / 2 := by
  have := purity_identity_exact ψ
  rw [hψ, hW] at this
  linarith

/-- The moment form of `(CE)`: for critical unit `ψ`, with `x = 2 (P - 1)`,
`T ≤ 5/12 + (17/12)(P - 1) - (x - x^{3/2})/12`. -/
theorem critical_moment_envelope (ψ : Psi) (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    cubicMoment ψ ≤ 5 / 12 + 17 / 12 * (purity ψ - 1)
      - (2 * (purity ψ - 1) - 2 * (purity ψ - 1) * Real.sqrt (2 * (purity ψ - 1))) / 12 := by
  have hP := critical_purity ψ hψ hW
  have hce := critical_envelope ψ hψ hW
  have hx : 2 * (purity ψ - 1) = Complex.normSq (spinFlipForm ψ) := by rw [hP]; ring
  rw [hx]
  unfold sexticF at hce
  rw [hψ] at hce
  have : purity ψ - 1 = Complex.normSq (spinFlipForm ψ) / 2 := by rw [hP]; ring
  rw [this]
  nlinarith [hce]

/-- The envelope of the critical moment region is attained for every `P ∈ [1, 3/2]`. -/
theorem critical_moment_envelope_attained (P : ℝ) (h1 : 1 ≤ P) (h2 : P ≤ 3 / 2) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ blochSq ψ = 0 ∧ purity ψ = P ∧
      cubicMoment ψ = 5 / 12 + 17 / 12 * (P - 1)
        - (2 * (P - 1) - 2 * (P - 1) * Real.sqrt (2 * (P - 1))) / 12 := by
  have hx0 : 0 ≤ 2 * (P - 1) := by linarith
  have hκ0 : 0 ≤ Real.sqrt (2 * (P - 1)) := Real.sqrt_nonneg _
  have hκ2 : Real.sqrt (2 * (P - 1)) ^ 2 = 2 * (P - 1) := Real.sq_sqrt hx0
  have hκ1 : Real.sqrt (2 * (P - 1)) ≤ 1 := by nlinarith
  obtain ⟨ψ, hψ, hW, hs, hF⟩ := critical_envelope_attained _ hκ0 hκ1
  rw [hκ2] at hs
  have hP := critical_purity ψ hψ hW
  rw [hs] at hP
  have hPP : purity ψ = P := by linarith
  refine ⟨ψ, hψ, hW, hPP, ?_⟩
  unfold sexticF at hF
  rw [hψ, hPP, hs] at hF
  nlinarith [hF]

/-- info: 'FormalResearch.FourQubitEntropy.critical_envelope_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms critical_envelope_eq_iff

/-- info: 'FormalResearch.FourQubitEntropy.critical_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms critical_closed_form

end FormalResearch.FourQubitEntropy
