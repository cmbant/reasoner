import FormalResearch.FourQubitEntropy.ColumnSide

/-!
# Normalising both cut factors to the singlet
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

/-- Local unitaries on qubits `1` and `3` bringing both top vectors to the singlet. -/
theorem normalize_both (ψ : Psi) (hn : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hq : (red12 ψ - (1 / 6 : ℂ) • 1) * (red12 ψ - (1 / 2 : ℂ) • 1) = 0) :
    ∃ a1 a2 : Op1, a1ᴴ * a1 = 1 ∧ a2ᴴ * a2 = 1 ∧
      red12 (localApply a1ᴴ 1 a2ᴴ 1 ψ) = Gs ∧
      (zmat (localApply a1ᴴ 1 a2ᴴ 1 ψ))ᴴ * zmat (localApply a1ᴴ 1 a2ᴴ 1 ψ) = Gs := by
  -- rows
  obtain ⟨a1, ha1, hrow⟩ := normalize_rows ψ hq (by rw [trace_red12, hn]; simp)
    (fun a a' => by rw [rhoSite0_eq, rhoSite_half ψ hn hW])
  -- columns
  have hqc : (red12 (swapHalves ψ) - (1 / 6 : ℂ) • 1) * (red12 (swapHalves ψ) - (1 / 2 : ℂ) • 1) = 0 := by
    rw [red12_swapHalves]
    have h1 : (zmat ψ * (zmat ψ)ᴴ - (1 / 6 : ℂ) • 1) * (zmat ψ * (zmat ψ)ᴴ - (1 / 2 : ℂ) • 1) = 0 := by
      rw [← red12_zmat]; exact hq
    exact quadratic_map_star (quadratic_gram h1)
  obtain ⟨a2, ha2, hcol⟩ := normalize_rows (swapHalves ψ) hqc
    (by rw [trace_red12, normSqPsi_swapHalves, hn]; simp)
    (fun a a' => by rw [rhoSite2_eq, rhoSite_half ψ hn hW])
  have hK1 : (kron a1ᴴ 1)ᴴ * kron a1ᴴ 1 = 1 := by
    have : (a1ᴴ)ᴴ * a1ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp ha1
    exact kron_unitary this (by simp)
  have hK2 : (kron a2ᴴ 1)ᴴ * kron a2ᴴ 1 = 1 := by
    have : (a2ᴴ)ᴴ * a2ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp ha2
    exact kron_unitary this (by simp)
  refine ⟨a1, a2, ha1, ha2, ?_, ?_⟩
  · show red12 (colLU (kron a2ᴴ 1) (rowLU (kron a1ᴴ 1) ψ)) = Gs
    rw [red12_colLU _ hK2, hrow]
  · -- the Gram matrix only sees the column operator
    have hz : zmat (localApply a1ᴴ 1 a2ᴴ 1 ψ) = zmat (rowLU (kron a1ᴴ 1) (colLU (kron a2ᴴ 1) ψ)) := by
      show zmat (colLU (kron a2ᴴ 1) (rowLU (kron a1ᴴ 1) ψ)) = _
      rw [zmat_colLU, zmat_rowLU, zmat_rowLU, zmat_colLU, Matrix.mul_assoc]
    rw [hz, gram_rowLU hK1]
    have h2 : red12 (swapHalves (colLU (kron a2ᴴ 1) ψ)) = Gs := by
      rw [colLU_swapHalves]; exact hcol
    rw [red12_swapHalves] at h2
    have h3 := congrArg (fun M : Mat4 => M.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_map] at h3
    have : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := by funext z; simp
    rw [this, Matrix.map_id, Gs_map_star] at h3
    exact h3

end FormalResearch.FourQubitEntropy
