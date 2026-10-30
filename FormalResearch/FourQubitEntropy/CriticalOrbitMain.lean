import FormalResearch.FourQubitEntropy.CriticalOrbitPhi

/-!
# Sharp critical-orbit stability: `thm:fqe-critical-orbit-sharp`

For a critical unit state `ψ` (`blochSq ψ = 0`), with `Φ`, `d² = dist2` of `CriticalOrbitPhi.lean`,
`Q = sexticQ`:

* `critical_fidelity`: `Q ≥ max{1 - Φ, 3/2 - 2Φ}` (`eq:fqe-critical-fidelity`);
* `critical_distance`: `Q ≥ ((2+√2)/4) d²` (`eq:fqe-critical-distance`);
* `critical_entropy_fidelity`, `critical_entropy_distance`: the entropy bounds
  (`eq:fqe-critical-entropy`), through the existing `entropy_gap_critical`.

The only input not proved here is the all-state comparison `Q ≥ 1 - Φ`
(`thm:fqe-global-overlap`), taken as the hypothesis `hglob` and used only when `Φ ≥ 1/2`; the
branch `Φ ≤ 1/2` is proved by `Q_lower` (the analytic argument of `critical_orbit_stability.tex`).
-/

set_option linter.unusedSimpArgs false

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- A critical unit state is `G(v)` up to local unitaries, with `v` a unit vector. -/
theorem critical_normal_vector {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    ∃ v : V, LUEquiv (Gv v) ψ ∧ Nv v = 1 ∧ sexticQ ψ = Qv v := by
  obtain ⟨v, hv⟩ := (critical_iff_LU_Gv ψ).mp hW
  refine ⟨v, hv, ?_, ?_⟩
  · have := normSqPsi_LUEquiv hv
    rw [Gv_n] at this
    simpa [Nv] using this.symm.trans hψ
  · rw [sexticQ_LUEquiv hv, sexticQ_Gv]

/-- `Φ ≥ 1/4` for a critical unit state (the 32 overlaps sum to `8`). -/
theorem Phi_ge_quarter {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    1 / 4 ≤ Phi ψ := by
  obtain ⟨v, hv, hN, -⟩ := critical_normal_vector hψ hW
  have hsum := sum_qH v
  rw [hN] at hsum
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin 32)))
    (f := fun _ => (1 / 4 : ℝ)) (g := fun a => qH a v) Finset.univ_nonempty
    (by simp [hsum]; norm_num)
  exact ha.trans (qH_le_Phi hv hψ a)

/-- `eq:fqe-critical-fidelity`: `Q ≥ max{1 - Φ, 3/2 - 2Φ}`, from the global comparison
`hglob : Φ ≥ 1/2 → Q ≥ 1 - Φ` (`thm:fqe-global-overlap`, used only when `Φ ≥ 1/2`). -/
theorem critical_fidelity {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) ≤ sexticQ ψ := by
  obtain ⟨v, hv, hN, hQ⟩ := critical_normal_vector hψ hW
  by_cases h : Phi ψ ≤ 1 / 2
  · have := Q_lower v hN (qH_le_Phi hv hψ) h
    rw [hQ]
    exact max_le (by linarith) this
  · have h := not_le.mp h
    have := hglob h.le
    exact max_le this (by linarith)

/-- `eq:fqe-critical-distance`: `Q ≥ ((2+√2)/4) d²`. -/
theorem critical_distance {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    (2 + Real.sqrt 2) / 4 * dist2 ψ ≤ sexticQ ψ := by
  have hF := critical_fidelity hψ hW hglob
  have h1 := Phi_ge_quarter hψ hW
  have h2 := Phi_le_one hψ
  set x := Real.sqrt (Phi ψ) with hx
  have hx2 : x ^ 2 = Phi ψ := Real.sq_sqrt (by linarith)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx1 : x ≤ 1 := by nlinarith
  have hxh : 1 / 2 ≤ x := by nlinarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : Real.sqrt 2 < 3 / 2 := by nlinarith
  unfold dist2
  rw [← hx]
  rcases le_total (Real.sqrt 2 / 2) x with hxs | hxs
  · have hQ1 : 1 - x ^ 2 ≤ sexticQ ψ := by rw [hx2]; exact (le_max_left _ _).trans hF
    nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hxs)]
  · have hQ2 : 3 / 2 - 2 * x ^ 2 ≤ sexticQ ψ := by rw [hx2]; exact (le_max_right _ _).trans hF
    have : 0 ≤ (Real.sqrt 2 / 2 - x) * (x - (2 - Real.sqrt 2) / 4) :=
      mul_nonneg (sub_nonneg.2 hxs) (by nlinarith)
    nlinarith

/-- `eq:fqe-critical-entropy`, fidelity form: `δ ≥ k (max{1-Φ, 3/2-2Φ} + 5τ/2)`. -/
theorem critical_entropy_fidelity {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    (Real.log 3 - 1) / (2 * Real.log 2) *
        (max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ meanEntropy M4 - meanEntropy ψ := by
  have h := entropy_gap_critical ψ hψ hW
  have hk := entropy_coeff_pos
  have : (Real.log 3 - 1) / (2 * Real.log 2) *
        (max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ (Real.log 3 - 1) / (2 * Real.log 2) *
        (sexticQ ψ + 5 / 2 * Complex.normSq (spinFlipForm ψ)) :=
    mul_le_mul_of_nonneg_left (by linarith [critical_fidelity hψ hW hglob]) hk.le
  linarith

/-- `eq:fqe-critical-entropy`, distance form: `δ ≥ k (((2+√2)/4) d² + 5τ/2)`. -/
theorem critical_entropy_distance {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    (Real.log 3 - 1) / (2 * Real.log 2) *
        ((2 + Real.sqrt 2) / 4 * dist2 ψ + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ meanEntropy M4 - meanEntropy ψ :=
  entropy_gap_critical_distance ψ hψ hW (critical_distance hψ hW hglob)

end FormalResearch.FourQubitEntropy.CO
