import FormalResearch.FourQubitEntropy.PaperEGoSliceGen

/-!
# `thm:fqe-global-overlap`, layer (a): existence of a closest-point frame

`exists_frame`: for every unit `ψ` there is a unit `φ` and `h ≥ 0` with `IsFrame φ h` (that is, `Z_* =
G(η₀)` is a closest point of `𝓜` to `φ`, at real height `h`), `Q(φ) = Q(ψ)` and `Φ(ψ) = h²`.

Proof: `Phi_attained` gives a closest point `χ₀ ∈ 𝓜`; it lies in the LU class of `Z_*` or of `conj Z_* =
G(η₇)` (`exists_same_class`); in the second case replace `ψ` by `conj ψ` (`Q`, `Φ` conjugation invariant:
`sexticQ_conj`, `Phi_conj`); apply the LU map taking `χ₀` to `Z_*` (`ip_localApply`), and a global phase.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-! ### Complex conjugation -/

theorem red12_conj (ψ : Psi) : red12 (Psi.conj ψ) = (red12 ψ).map (starRingEnd ℂ) := by
  ext i j
  simp [red12, Psi.conj, map_sum, map_mul, mul_comm]

theorem red13_conj (ψ : Psi) : red13 (Psi.conj ψ) = (red13 ψ).map (starRingEnd ℂ) := by
  ext i j
  simp [red13, Psi.conj, map_sum, map_mul, mul_comm]

theorem red14_conj (ψ : Psi) : red14 (Psi.conj ψ) = (red14 ψ).map (starRingEnd ℂ) := by
  ext i j
  simp [red14, Psi.conj, map_sum, map_mul, mul_comm]

theorem trace_sq_map_conj (A : Mat4) :
    Matrix.trace (A.map (starRingEnd ℂ) * A.map (starRingEnd ℂ)) =
      (starRingEnd ℂ) (Matrix.trace (A * A)) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]

theorem trace_cube_map_conj (A : Mat4) :
    Matrix.trace (A.map (starRingEnd ℂ) * A.map (starRingEnd ℂ) * A.map (starRingEnd ℂ)) =
      (starRingEnd ℂ) (Matrix.trace (A * A * A)) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]

theorem purity_conj (ψ : Psi) : purity (Psi.conj ψ) = purity ψ := by
  unfold purity
  rw [red12_conj, red13_conj, red14_conj, trace_sq_map_conj, trace_sq_map_conj,
    trace_sq_map_conj, Complex.conj_re, Complex.conj_re, Complex.conj_re]

theorem cubicMoment_conj (ψ : Psi) : cubicMoment (Psi.conj ψ) = cubicMoment ψ := by
  unfold cubicMoment
  rw [red12_conj, red13_conj, red14_conj, trace_cube_map_conj, trace_cube_map_conj,
    trace_cube_map_conj, Complex.conj_re, Complex.conj_re, Complex.conj_re]

theorem sexticQ_conj (ψ : Psi) : sexticQ (Psi.conj ψ) = sexticQ ψ := by
  rw [sexticQ_eq, sexticQ_eq, normSqPsi_conj, purity_conj, cubicMoment_conj]

theorem ip_conj_conj (a b : Psi) : ip (Psi.conj a) (Psi.conj b) = (starRingEnd ℂ) (ip a b) := by
  simp [ip, vecOf, Psi.conj, map_sum, map_mul]

theorem InOrbit_conj {χ : Psi} (h : InOrbit χ) : InOrbit (Psi.conj χ) := by
  rcases h with h | h
  · exact Or.inr (luEquiv_conj h)
  · refine Or.inl ?_
    have := luEquiv_conj h
    rwa [FormalResearch.FourQubitEntropy.CO.Psi.conj_conj] at this

theorem Phi_conj_ge {ψ : Psi} (hψ : normSqPsi ψ = 1) : Phi ψ ≤ Phi (Psi.conj ψ) := by
  obtain ⟨χ, hχM, hχ, -⟩ := Phi_attained hψ
  have hχo := inOrbit_of_inM hχM
  have := le_Phi (by rw [normSqPsi_conj, hψ] : normSqPsi (Psi.conj ψ) = 1) (InOrbit_conj hχo)
  rw [ip_conj_conj, Complex.normSq_conj] at this
  linarith

theorem Phi_conj {ψ : Psi} (hψ : normSqPsi ψ = 1) : Phi (Psi.conj ψ) = Phi ψ := by
  refine le_antisymm ?_ (Phi_conj_ge hψ)
  have := Phi_conj_ge (ψ := Psi.conj ψ) (by rw [normSqPsi_conj, hψ])
  rwa [FormalResearch.FourQubitEntropy.CO.Psi.conj_conj] at this

/-! ### `conj Z_* = G(η₇)` -/

theorem conj_etaC_zero (j : Fin 4) : (starRingEnd ℂ) (etaC 0 j) = etaC 7 j := by
  rw [etaC_seven]
  by_cases hj : j = 0
  · subst hj
    rw [etaC0_0', Complex.conj_ofReal]
    simp [sgn4]
  · rw [etaC0_pos j hj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    simp [sgn4, hj]

theorem conj_Zs : Psi.conj (Gv (etaV 0)) = Gv (etaV 7) := by
  rw [conj_Gv]
  congr 1
  funext k
  exact conj_etaC_zero (pairIdx k)

theorem conj_Zb : Psi.conj (Gv (etaV 7)) = Gv (etaV 0) := by
  rw [← conj_Zs, FormalResearch.FourQubitEntropy.CO.Psi.conj_conj]

/-- A point of `𝓜` lies in the LU class of `Z_*` or of `conj Z_*`. -/
theorem exists_same_class {χ₀ : Psi} (h : InOrbit χ₀) :
    LUEquiv (Gv (etaV 0)) χ₀ ∨ LUEquiv (Gv (etaV 7)) χ₀ := by
  have hz := orbit_etaV 0
  rcases hz with hz | hz <;> rcases h with h | h
  · exact Or.inl (hz.symm.trans h)
  · right
    have := luEquiv_conj hz
    rw [conj_Zs] at this
    exact this.symm.trans h
  · right
    have := luEquiv_conj hz
    rw [FormalResearch.FourQubitEntropy.CO.Psi.conj_conj, conj_Zs] at this
    exact this.symm.trans h
  · exact Or.inl (hz.symm.trans h)

/-! ### From a closest point in the class of `Z_*` to a frame -/

theorem exists_phase_full (t : ℂ) : ∃ θ : ℝ, Complex.exp (θ * Complex.I) * t = (‖t‖ : ℂ) := by
  refine ⟨-Complex.arg t, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I t
  conv_lhs => rw [← h]
  rw [mul_left_comm, ← Complex.exp_add]
  push_cast
  simp

theorem LUEquiv_phase (θ : ℝ) (ψ : Psi) : LUEquiv ψ (Complex.exp (θ * Complex.I) • ψ) := by
  refine ⟨Complex.exp (θ * Complex.I) • 1, 1, 1, 1, ?_, by simp, by simp, by simp, ?_⟩
  · exact phase_unitary θ ⟨by simp, by simp⟩
  · rw [localApply_smul_a, localApply_one]

theorem frame_of_max {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (hmax : Complex.normSq (ip (Gv (etaV 0)) ψ) = Phi ψ) :
    ∃ (φ : Psi) (h : ℝ), IsFrame φ h ∧ LUEquiv ψ φ ∧ Phi ψ = h ^ 2 := by
  obtain ⟨θ, hθ⟩ := exists_phase_full (ip (Gv (etaV 0)) ψ)
  have hL := LUEquiv_phase θ ψ
  set φ := Complex.exp (θ * Complex.I) • ψ with hφ
  have hφn : normSqPsi φ = 1 := by rw [normSqPsi_LUEquiv hL, hψ]
  have hΦ : Phi φ = Phi ψ := Phi_LUEquiv hL hψ
  have hh : Phi ψ = ‖ip (Gv (etaV 0)) ψ‖ ^ 2 := by
    rw [← hmax, Complex.normSq_eq_norm_sq]
  refine ⟨φ, ‖ip (Gv (etaV 0)) ψ‖, ⟨hφn, norm_nonneg _, ?_, ?_⟩, hL, hh⟩
  · rw [hφ, ip_smul_right, hθ]
  · intro χ hχ
    have := le_Phi hφn hχ
    rw [ip_comm χ φ, Complex.normSq_conj]
    linarith

theorem step1 {ψ χ₀ : Psi} (hmax : Complex.normSq (ip ψ χ₀) = Phi ψ)
    (hL : LUEquiv (Gv (etaV 0)) χ₀) :
    ∃ ψ' : Psi, LUEquiv ψ ψ' ∧ Complex.normSq (ip (Gv (etaV 0)) ψ') = Phi ψ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hZ⟩ := hL.symm
  refine ⟨localApply a b c d ψ, ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩, ?_⟩
  rw [← hZ, ip_localApply ha hb hc hd, ip_comm, Complex.normSq_conj]
  exact hmax

theorem exists_frame_of_class {ψ : Psi} (hψ : normSqPsi ψ = 1) {χ₀ : Psi}
    (hmax : Complex.normSq (ip ψ χ₀) = Phi ψ) (hL : LUEquiv (Gv (etaV 0)) χ₀) :
    ∃ (φ : Psi) (h : ℝ), IsFrame φ h ∧ LUEquiv ψ φ ∧ Phi ψ = h ^ 2 := by
  obtain ⟨ψ', hLU, hmax'⟩ := step1 hmax hL
  have hψ' : normSqPsi ψ' = 1 := by rw [normSqPsi_LUEquiv hLU, hψ]
  have hΦ : Phi ψ' = Phi ψ := Phi_LUEquiv hLU hψ
  obtain ⟨φ, h, hf, hLU', hh⟩ := frame_of_max hψ' (by rw [hmax', hΦ])
  exact ⟨φ, h, hf, hLU.trans hLU', by rw [← hΦ]; exact hh⟩

/-- **Layer (a).** Every unit state has a closest-point frame, with the same `Q` and `Φ`. -/
theorem exists_frame {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    ∃ (φ : Psi) (h : ℝ), IsFrame φ h ∧ sexticQ φ = sexticQ ψ ∧ Phi ψ = h ^ 2 := by
  obtain ⟨χ₀, hχ₀M, hmax, -⟩ := Phi_attained hψ
  have hχ₀ := inOrbit_of_inM hχ₀M
  rcases exists_same_class hχ₀ with hL | hL
  · obtain ⟨φ, h, hf, hLU, hh⟩ := exists_frame_of_class hψ hmax hL
    exact ⟨φ, h, hf, sexticQ_LUEquiv hLU, hh⟩
  · have hLc := luEquiv_conj hL
    rw [conj_Zb] at hLc
    have hψc : normSqPsi (Psi.conj ψ) = 1 := by rw [normSqPsi_conj, hψ]
    have hmaxc : Complex.normSq (ip (Psi.conj ψ) (Psi.conj χ₀)) = Phi (Psi.conj ψ) := by
      rw [ip_conj_conj, Complex.normSq_conj, hmax, Phi_conj hψ]
    obtain ⟨φ, h, hf, hLU, hh⟩ := exists_frame_of_class hψc hmaxc hLc
    refine ⟨φ, h, hf, ?_, by rw [← Phi_conj hψ]; exact hh⟩
    rw [sexticQ_LUEquiv hLU, sexticQ_conj]

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.exists_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_frame

end

end FormalResearch.FourQubitEntropy.GO
