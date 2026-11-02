import FormalResearch.FourQubitEntropy.QVEqualityCritical
import FormalResearch.FourQubitEntropy.RenyiFullHeadlineQV
import FormalResearch.FourQubitEntropy.PaperEGenJointPurity

/-!
# `prop:fqe-critical-variance` for states, and equality in (QK) at `P = 1`

Paper E, `renyi_compatibility.tex` (`prop:fqe-critical-variance`, (RF)) and `quadratic_variance_certificate.tex`
(`thm:fqe-quadratic-variance`, the equality analysis at `P = 1`).  For a unit pure four-qubit state `ψ` we write
`VP ψ = Σ_j (p_j - P/3)²` (the paper's `V_P`, over the three cut purities `p_j`).

* `critical_rf`: `P = 1` gives `s ∈ [0,1]` with `s⁴ = 24 V_P` and `F ≥ (3/2)s² - s³` (RF);
* `critical_qk_equality`: `P = 1` and `F² = 6 V_P` force HS or cluster cut spectra.
-/

namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

/-- The paper's `V_P = Σ_{j=2}^4 (p_j - P/3)²` of a four-qubit state. -/
noncomputable def VP (ψ : Psi) : ℝ :=
  (cutPurity12 ψ - purity ψ / 3) ^ 2 + (cutPurity13 ψ - purity ψ / 3) ^ 2 +
    (cutPurity14 ψ - purity ψ / 3) ^ 2

theorem SpecEquiv.pur_eq {l l' : Fin 4 → ℝ} (h : SpecEquiv l l') : RenyiFull.pur l = RenyiFull.pur l' := by
  obtain ⟨e, he⟩ := h
  unfold RenyiFull.pur; simp_rw [he]; exact Equiv.sum_comp e (fun j => l' j ^ 2)

theorem SpecEquiv.cub_eq {l l' : Fin 4 → ℝ} (h : SpecEquiv l l') : RenyiFull.cub l = RenyiFull.cub l' := by
  obtain ⟨e, he⟩ := h
  unfold RenyiFull.cub; simp_rw [he]; exact Equiv.sum_comp e (fun j => l' j ^ 3)

theorem Pm_equiv {a b c a' b' c' : Fin 4 → ℝ} (h1 : SpecEquiv a a') (h2 : SpecEquiv b b')
    (h3 : SpecEquiv c c') : RenyiFull.Pm a b c = RenyiFull.Pm a' b' c' := by
  unfold RenyiFull.Pm; rw [h1.pur_eq, h2.pur_eq, h3.pur_eq]

theorem Fm_equiv {a b c a' b' c' : Fin 4 → ℝ} (h1 : SpecEquiv a a') (h2 : SpecEquiv b b')
    (h3 : SpecEquiv c c') : RenyiFull.Fm a b c = RenyiFull.Fm a' b' c' := by
  unfold RenyiFull.Fm RenyiFull.Tm; rw [Pm_equiv h1 h2 h3, h1.cub_eq, h2.cub_eq, h3.cub_eq]

theorem Vm_equiv {a b c a' b' c' : Fin 4 → ℝ} (h1 : SpecEquiv a a') (h2 : SpecEquiv b b')
    (h3 : SpecEquiv c c') : RenyiFull.Vm a b c = RenyiFull.Vm a' b' c' := by
  unfold RenyiFull.Vm; rw [Pm_equiv h1 h2 h3, h1.pur_eq, h2.pur_eq, h3.pur_eq]

theorem VP_eq_Vm (ψ : Psi) : VP ψ = RenyiFull.Vm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  have e2 : pur (cutSpec₂ ψ) = cutPurity12 ψ := by unfold cutSpec₂ cutPurity12; rw [pur_spec4]
  have e3 : pur (cutSpec₃ ψ) = cutPurity13 ψ := by unfold cutSpec₃ cutPurity13; rw [pur_spec4]
  have e4 : pur (cutSpec₄ ψ) = cutPurity14 ψ := by unfold cutSpec₄ cutPurity14; rw [pur_spec4]
  unfold VP RenyiFull.Vm
  rw [Pm_cutSpec, e2, e3, e4]

/-- **`prop:fqe-critical-variance`, (RF)** (proved under `P = 1`): with `s = (24 V_P)^{1/4}`,
`0 ≤ s ≤ 1` and `F ≥ (3/2) s² - s³`. -/
theorem critical_rf (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ s ^ 4 = 24 * VP ψ ∧ 3 / 2 * s ^ 2 - s ^ 3 ≤ sexticF ψ := by
  obtain ⟨m, n, hm, hn', e2, e3, e4⟩ := critical_cut_data ψ hn hP
  obtain ⟨s, hs0, hs1, -, hV, -, hRF⟩ := core_triple m n hm hn'
  refine ⟨s, hs0, hs1, ?_, ?_⟩
  · rw [VP_eq_Vm, Vm_equiv e2 e3 e4, hV]
  · rw [← Fm_cutSpec ψ hn, Fm_equiv e2 e3 e4]; exact hRF

/-- (RF) with the explicit `s = (24 V_P)^{1/4}`. -/
theorem critical_rf' (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1) :
    Real.sqrt (Real.sqrt (24 * VP ψ)) ≤ 1 ∧
      3 / 2 * Real.sqrt (Real.sqrt (24 * VP ψ)) ^ 2 - Real.sqrt (Real.sqrt (24 * VP ψ)) ^ 3 ≤ sexticF ψ := by
  obtain ⟨s, hs0, hs1, hs4, hF⟩ := critical_rf ψ hn hP
  have : Real.sqrt (Real.sqrt (24 * VP ψ)) = s := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.sqrt_sq hs0]
  rw [this]; exact ⟨hs1, hF⟩

/-- **Equality in (QK) at `P = 1`**: `F² = 6 V_P` (the case `P = 1` of equality in (QK)) forces HS or cluster
cut spectra. -/
theorem critical_qk_equality (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hEq : sexticF ψ ^ 2 = 6 * VP ψ) :
    IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  obtain ⟨m, n, hm, hn', e2, e3, e4⟩ := critical_cut_data ψ hn hP
  have hEq' : RenyiFull.Fm (spc0 m n) (spc1 m n) (spc2 m n) ^ 2 = 6 * RenyiFull.Vm (spc0 m n) (spc1 m n) (spc2 m n) := by
    rw [← Fm_equiv e2 e3 e4, ← Vm_equiv e2 e3 e4, Fm_cutSpec ψ hn, ← VP_eq_Vm]; exact hEq
  rcases core_equality m n hm hn' hEq' with ⟨h2, h3, h4⟩ | h
  · exact Or.inl ⟨e2.isHsPerm h2, e3.isHsPerm h3, e4.isHsPerm h4⟩
  · right
    rcases h with ⟨t2, f3, f4⟩ | ⟨f2, t3, f4⟩ | ⟨f2, f3, t4⟩
    · exact Or.inl ⟨e2.uniformTwo t2, e3.uniformFour f3, e4.uniformFour f4⟩
    · exact Or.inr (Or.inl ⟨e2.uniformFour f2, e3.uniformTwo t3, e4.uniformFour f4⟩)
    · exact Or.inr (Or.inr ⟨e2.uniformFour f2, e3.uniformFour f3, e4.uniformTwo t4⟩)

end FormalResearch.FourQubitEntropy.QVEquality
