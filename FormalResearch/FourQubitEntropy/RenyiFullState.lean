import FormalResearch.FourQubitEntropy.RenyiFullEnvelope

/-!
# The Rényi envelope for pure four-qubit states, `q > 1`

Paper E, `cor:fqe-renyi-gw` for `q > 1`.

`QuadraticVarianceBound` is `thm:fqe-quadratic-variance` (QK): for every unit pure four-qubit state,
`F² + (9/2)(P - 1) ≥ 6 V_P`.  It is an exact-rational certificate of the paper (80 squared covariant
norms, QG) that is **not** formalised; it enters as an explicit hypothesis, never as an axiom.

* `relaxTriple_of_state`: under (QK) the three cut spectra of a unit vector form a triple of the
  classical relaxation (`P ≥ 1` and `F ≥ 0` are formalised: `purity_ge`, `sexticF_nonneg`).
* `meanRenyi_envelope`: from `ClassicalRelaxation` and `QuadraticVarianceBound`, for every unit `ψ`
  and every `q > 1`, `meanRenyi q ψ ≤ max {hsRenyi q, 5/3}`, with the spectral equality clauses.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **(QK), `thm:fqe-quadratic-variance`**: `F² + (9/2)(P-1) ≥ 6 V_P` for every unit pure four-qubit
state (an exact-rational certificate in the paper; hypothesis here). -/
def QuadraticVarianceBound : Prop :=
  ∀ ψ : Psi, normSqPsi ψ = 1 →
    6 * ((cutPurity12 ψ - purity ψ / 3) ^ 2 + (cutPurity13 ψ - purity ψ / 3) ^ 2
        + (cutPurity14 ψ - purity ψ / 3) ^ 2) ≤ sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1)

theorem pur_spec4 (l : Fin 2 × Fin 2 → ℝ) : pur (spec4 l) = ∑ i, l i ^ 2 := by
  unfold pur spec4
  have := Equiv.sum_comp cutEquiv.symm (fun i => l i ^ 2)
  simp only [Function.comp_apply]; rw [this]

theorem cub_spec4 (l : Fin 2 × Fin 2 → ℝ) : cub (spec4 l) = ∑ i, l i ^ 3 := by
  unfold cub spec4
  have := Equiv.sum_comp cutEquiv.symm (fun i => l i ^ 3)
  simp only [Function.comp_apply]; rw [this]

theorem cubicMoment_eq_eigen (ψ : Psi) :
    cubicMoment ψ = ∑ i, (red12_herm ψ).eigenvalues i ^ 3 + ∑ i, (red13_herm ψ).eigenvalues i ^ 3
      + ∑ i, (red14_herm ψ).eigenvalues i ^ 3 := by
  rw [sum_eigenvalues_pow (red12_herm ψ) 3, sum_eigenvalues_pow (red13_herm ψ) 3,
    sum_eigenvalues_pow (red14_herm ψ) 3]
  unfold cubicMoment
  simp only [pow_succ, pow_zero, one_mul]

/-- The three cut spectra of a unit vector. -/
noncomputable def cutSpec₂ (ψ : Psi) : Fin 4 → ℝ := spec4 (red12_herm ψ).eigenvalues
noncomputable def cutSpec₃ (ψ : Psi) : Fin 4 → ℝ := spec4 (red13_herm ψ).eigenvalues
noncomputable def cutSpec₄ (ψ : Psi) : Fin 4 → ℝ := spec4 (red14_herm ψ).eigenvalues

theorem Pm_cutSpec (ψ : Psi) : Pm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) = purity ψ := by
  unfold Pm cutSpec₂ cutSpec₃ cutSpec₄
  rw [pur_spec4, pur_spec4, pur_spec4, purity_eq_sum_sq]

theorem Tm_cutSpec (ψ : Psi) : Tm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) = cubicMoment ψ := by
  unfold Tm cutSpec₂ cutSpec₃ cutSpec₄
  rw [cub_spec4, cub_spec4, cub_spec4, cubicMoment_eq_eigen]

theorem Fm_cutSpec (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    Fm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) = sexticF ψ := by
  unfold Fm
  rw [Pm_cutSpec, Tm_cutSpec]
  unfold sexticF
  rw [hψ]; ring

/-- Under (QK), the three cut spectra of a unit vector form a triple of the classical relaxation. -/
theorem relaxTriple_of_state (hQK : QuadraticVarianceBound) {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    RelaxTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  have hP := purity_ge ψ
  rw [hψ] at hP
  have hF := sexticF_nonneg ψ
  refine ⟨isProb4_spec4 (isProb12 hψ), isProb4_spec4 (isProb13 hψ), isProb4_spec4 (isProb14 hψ),
    ?_, ?_, ?_⟩
  · rw [Pm_cutSpec]; linarith
  · rw [Fm_cutSpec ψ hψ]; exact hF
  · unfold QKTriple Vm
    rw [Fm_cutSpec ψ hψ, Pm_cutSpec]
    have h := hQK ψ hψ
    have e2 : pur (cutSpec₂ ψ) = cutPurity12 ψ := by unfold cutSpec₂ cutPurity12; rw [pur_spec4]
    have e3 : pur (cutSpec₃ ψ) = cutPurity13 ψ := by unfold cutSpec₃ cutPurity13; rw [pur_spec4]
    have e4 : pur (cutSpec₄ ψ) = cutPurity14 ψ := by unfold cutSpec₄ cutPurity14; rw [pur_spec4]
    rw [e2, e3, e4]
    exact h

theorem meanRenyi_eq_Em (ψ : Psi) (q : ℝ) :
    meanRenyi q ψ = Em q (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  unfold meanRenyi Em renyiE cutSpec₂ cutSpec₃ cutSpec₄
  rw [renyiCut_eq_renyiSpec, renyiCut_eq_renyiSpec, renyiCut_eq_renyiSpec, renyiSpec_spec4,
    renyiSpec_spec4, renyiSpec_spec4]

/-- **`cor:fqe-renyi-gw`, `q > 1`, for pure four-qubit states** (from `ClassicalRelaxation` and
`QuadraticVarianceBound`): `E_q(ψ) ≤ max {h_q, 5/3}`, with equality clauses on the cut spectra. -/
theorem meanRenyi_envelope (hCl : ClassicalRelaxation) (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) := by
  have h := envelope_triple hCl (relaxTriple_of_state hQK hψ) hq
  rw [← meanRenyi_eq_Em, hsq_eq] at h
  exact h

end FormalResearch.FourQubitEntropy.RenyiFull
