import FormalResearch.FourQubitEntropy.Stability

/-!
# Further short corollaries of the moment inequality

* `e3_sum_le`: the third elementary symmetric functions of the cut spectra satisfy
  `Σ_j e₃(ρ_{1j}) = (6 - P - F)/36 ≤ (6-P)/36 - 15 W₁/1152 ≤ 5/36`
  (`cor:fqe-e3`, replica_sectors.tex; the equality case is only proved in the direction
  "`M₄`-orbits attain `5/36`": the converse needs the classification of `P = 1, F = 0`).
* `moment_line_slope_optimal`: the slope `17/12` of the moment line is the least possible
  (`thm:fqe-moment`, entropy_maximum.tex).
* `swap23_M4`: the transposition of qubits `2, 3` maps `M₄` to `ω · conj M₄`
  (`rem:fqe-single-orbit`, entropy_maximum.tex).
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- Newton's identity for four numbers indexed by `Fin 2 × Fin 2`. -/
theorem e3_newton (l : Fin 2 × Fin 2 → ℝ) :
    ∑ s ∈ (Finset.univ : Finset (Fin 2 × Fin 2)).powersetCard 3, ∏ i ∈ s, l i
      = ((∑ i, l i) ^ 3 - 3 * (∑ i, l i) * (∑ i, l i ^ 2) + 2 * ∑ i, l i ^ 3) / 6 := by
  have : (Finset.univ : Finset (Fin 2 × Fin 2)).powersetCard 3
      = {{(0,0),(0,1),(1,0)}, {(0,0),(0,1),(1,1)}, {(0,0),(1,0),(1,1)}, {(0,1),(1,0),(1,1)}} := by
    decide
  rw [this]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp (config := {decide := true}) [Finset.prod_insert, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The third elementary symmetric function `e₃` of the spectrum of a Hermitian `R`. -/
noncomputable def cutE3 {R : Mat4} (hR : R.IsHermitian) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin 2 × Fin 2)).powersetCard 3, ∏ i ∈ s, hR.eigenvalues i

theorem cutE3_eq {R : Mat4} (hR : R.IsHermitian) (htr : (Matrix.trace R).re = 1) :
    cutE3 hR = (1 - 3 * (Matrix.trace (R * R)).re + 2 * (Matrix.trace (R * R * R)).re) / 6 := by
  unfold cutE3
  rw [e3_newton]
  have e3 : ∑ i, hR.eigenvalues i ^ 3 = (Matrix.trace (R * R * R)).re := by
    rw [sum_eigenvalues_pow hR 3, pow_succ, pow_two]
  have e2 : ∑ i, hR.eigenvalues i ^ 2 = (Matrix.trace (R * R)).re := by
    rw [sum_eigenvalues_pow hR 2, pow_two]
  have e1 : ∑ i, hR.eigenvalues i = 1 := by rw [sum_eigenvalues_eq_trace, htr]
  rw [e3, e2, e1]
  ring

/-- `Σ_{j=2}^4 e₃(ρ_{1j}) = (6 - P - F)/36` for a unit vector (identity (RS) of the paper). -/
theorem e3_sum_eq (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    cutE3 (red12_herm ψ) + cutE3 (red13_herm ψ) + cutE3 (red14_herm ψ)
      = (6 - purity ψ - sexticF ψ) / 36 := by
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  rw [cutE3_eq _ t12, cutE3_eq _ t13, cutE3_eq _ t14]
  unfold sexticF purity cubicMoment
  rw [hψ]
  ring

/-- **Third elementary symmetric functions** (`cor:fqe-e3`):
`Σ_j e₃(ρ_{1j}) ≤ (6 - P)/36 - 15 W₁/1152 ≤ 5/36`. -/
theorem e3_sum_le (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    cutE3 (red12_herm ψ) + cutE3 (red13_herm ψ) + cutE3 (red14_herm ψ)
        ≤ (6 - purity ψ) / 36 - 15 * blochSq ψ / 1152 ∧
      (6 - purity ψ) / 36 - 15 * blochSq ψ / 1152 ≤ 5 / 36 := by
  have h := e3_sum_eq ψ hψ
  have hF := sexticF_ge ψ
  rw [hψ] at hF
  have hP := purity_ge ψ
  rw [hψ] at hP
  have hW := blochSq_nonneg ψ
  constructor <;> nlinarith

/-- The vectors of the two `M₄` orbits attain `Σ_j e₃(ρ_{1j}) = 5/36`. -/
theorem e3_sum_of_cutQuadratics {ψ : Psi} (hψ : normSqPsi ψ = 1) (hq : CutQuadratics ψ) :
    cutE3 (red12_herm ψ) + cutE3 (red13_herm ψ) + cutE3 (red14_herm ψ) = 5 / 36 := by
  have t12 : Matrix.trace (red12 ψ) = 1 := by rw [trace_red12, hψ]; simp
  have t13 : Matrix.trace (red13 ψ) = 1 := by rw [trace_red13, hψ]; simp
  have t14 : Matrix.trace (red14 ψ) = 1 := by rw [trace_red14, hψ]; simp
  obtain ⟨a12, b12⟩ := quad_traces hq.q12 t12
  obtain ⟨a13, b13⟩ := quad_traces hq.q13 t13
  obtain ⟨a14, b14⟩ := quad_traces hq.q14 t14
  rw [cutE3_eq _ (by rw [t12]; simp), cutE3_eq _ (by rw [t13]; simp),
    cutE3_eq _ (by rw [t14]; simp), a12, a13, a14, b12, b13, b14]
  norm_num

theorem e3_sum_M4 :
    cutE3 (red12_herm M4) + cutE3 (red13_herm M4) + cutE3 (red14_herm M4) = 5 / 36 :=
  e3_sum_of_cutQuadratics M4_unit M4_cutQuadratics

/-- **Optimality of the slope `17/12`** (`thm:fqe-moment`): if
`T ≤ 5/12 + κ (P - 1)` for all unit vectors, then `κ ≥ 17/12` (the product of two Bell pairs
has `(P, T) = (3/2, 9/8)`). -/
theorem moment_line_slope_optimal (κ : ℝ)
    (h : ∀ ψ : Psi, normSqPsi ψ = 1 → cubicMoment ψ ≤ 5 / 12 + κ * (purity ψ - 1)) :
    17 / 12 ≤ κ := by
  obtain ⟨h1, h2, h3, -⟩ := bell2_vals
  have := h bell2 h1
  rw [h2, h3] at this
  linarith

/-- **Single orbit** (`rem:fqe-single-orbit`): the transposition of qubits `2, 3` sends
`M₄` to `ω · conj M₄`. -/
theorem swap23_M4 : swap23 M4 = fun a b c d => omega * Psi.conj M4 a b c d := by
  funext a b c d
  have hω : omega * conj omega = 1 := omega_mul_conj
  have hω2 : omega * omega = conj omega := omega_sq
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [swap23, M4, Psi.conj] <;>
    first | done | ring1 | linear_combination (-(((Real.sqrt 6 : ℝ) : ℂ))⁻¹) * hω |
      linear_combination (-(((Real.sqrt 6 : ℝ) : ℂ))⁻¹) * hω2

/-- info: 'FormalResearch.FourQubitEntropy.e3_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms e3_sum_le

/-- info: 'FormalResearch.FourQubitEntropy.e3_sum_M4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms e3_sum_M4

/-- info: 'FormalResearch.FourQubitEntropy.moment_line_slope_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms moment_line_slope_optimal

/-- info: 'FormalResearch.FourQubitEntropy.swap23_M4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swap23_M4

end FormalResearch.FourQubitEntropy
