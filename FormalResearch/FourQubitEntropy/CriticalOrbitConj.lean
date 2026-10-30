import FormalResearch.FourQubitEntropy.CriticalOrbitPhi

/-!
# Critical-orbit stability: complex conjugation

`conj G(v) = G(conj v)` (the magic basis is real up to the signs `(1,-1,1,-1)`), `conj` maps local
unitary equivalences to local unitary equivalences, and `conj η_0 = η_7` for the representatives
`η_0 = (1/√2, i/√6, i/√6, i/√6)`, `η_7 = (1/√2, -i/√6, -i/√6, -i/√6)`.  Hence both `M₄` and
`conj M₄` are local-unitary images of some `G(η)`, `η ∈ 𝓗` (`exists_M4_conj`).
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

theorem Psi.conj_conj (ψ : Psi) : Psi.conj (Psi.conj ψ) = ψ := by
  funext a b c d; simp [Psi.conj]

/-- The signs relating `conj B` and `B`. -/
def sgnB : Fin 2 × Fin 2 → ℂ
  | (0, 0) => 1
  | (0, 1) => -1
  | (1, 0) => 1
  | (1, 1) => -1

theorem magicB_conj : magicB.map (starRingEnd ℂ) = magicB * Matrix.diagonal sgnB := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [magicB, Matrix.mul_apply, Matrix.diagonal_apply, sgnB, rt_conj, Fintype.sum_prod_type,
    Fin.sum_univ_two]

theorem conj_Gv (v : V) : Psi.conj (Gv v) = Gv (fun k => (starRingEnd ℂ) (v k)) := by
  have h : zmat (Psi.conj (Gv v)) = (zmat (Gv v)).map (starRingEnd ℂ) := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩; rfl
  have h2 : (zmat (Gv v)).map (starRingEnd ℂ) =
      magicB * Matrix.diagonal (fun k => (starRingEnd ℂ) (v k)) * magicBᵀ := by
    rw [zmat_Gv, Matrix.map_mul, Matrix.map_mul, magicB_conj]
    have hT : (magicB.map (starRingEnd ℂ))ᵀ = (magicB * Matrix.diagonal sgnB)ᵀ := by rw [magicB_conj]
    have e1 : (magicBᵀ).map (starRingEnd ℂ) = (magicB.map (starRingEnd ℂ))ᵀ := by
      ext i j; simp
    have e2 : (Matrix.diagonal v).map (starRingEnd ℂ) =
        Matrix.diagonal (fun k => (starRingEnd ℂ) (v k)) := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [e1, hT, e2, Matrix.transpose_mul, Matrix.diagonal_transpose]
    have : Matrix.diagonal sgnB * Matrix.diagonal (fun k => (starRingEnd ℂ) (v k)) *
        Matrix.diagonal sgnB = Matrix.diagonal (fun k => (starRingEnd ℂ) (v k)) := by
      simp only [Matrix.diagonal_mul_diagonal]
      congr 1; funext ⟨i1, i2⟩
      fin_cases i1 <;> fin_cases i2 <;> simp [sgnB]
    calc _ = magicB * (Matrix.diagonal sgnB * Matrix.diagonal (fun k => (starRingEnd ℂ) (v k)) *
          Matrix.diagonal sgnB) * magicBᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [this]
  have := h.trans h2
  unfold Gv
  rw [← zmat_ofZmat (magicB * Matrix.diagonal (fun k => (starRingEnd ℂ) (v k)) * magicBᵀ), ← this]
  rfl

theorem conj_localApply (a b c d : Op1) (φ : Psi) :
    Psi.conj (localApply a b c d φ) =
      localApply (a.map (starRingEnd ℂ)) (b.map (starRingEnd ℂ)) (c.map (starRingEnd ℂ))
        (d.map (starRingEnd ℂ)) (Psi.conj φ) := by
  funext p q r s
  simp only [Psi.conj, localApply_apply, map_sum, map_mul, Matrix.map_apply]

theorem unitary_map_conj {a : Op1} (ha : aᴴ * a = 1) :
    (a.map (starRingEnd ℂ))ᴴ * a.map (starRingEnd ℂ) = 1 := by
  have h := congrArg Matrix.transpose ha
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h
  have e : (a.map (starRingEnd ℂ))ᴴ = aᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  have e2 : aᴴᵀ = a.map (starRingEnd ℂ) := by ext i j; simp [Matrix.conjTranspose_apply]
  rw [e, ← e2]; exact h

theorem luEquiv_conj {φ ψ : Psi} (h : LUEquiv φ ψ) : LUEquiv (Psi.conj φ) (Psi.conj ψ) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact ⟨_, _, _, _, unitary_map_conj ha, unitary_map_conj hb, unitary_map_conj hc,
    unitary_map_conj hd, (conj_localApply a b c d φ).symm⟩

theorem conj_etaV_zero : (fun k => (starRingEnd ℂ) (etaV 0 k)) = etaV 7 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  funext ⟨i1, i2⟩
  fin_cases i1 <;> fin_cases i2 <;>
    simp [etaV, etaC, pairIdx, idxI, epsOf, Complex.conj_ofReal] <;> ring

theorem conj_etaV_seven : (fun k => (starRingEnd ℂ) (etaV 7 k)) = etaV 0 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  funext ⟨i1, i2⟩
  fin_cases i1 <;> fin_cases i2 <;>
    simp [etaV, etaC, pairIdx, idxI, epsOf, Complex.conj_ofReal] <;> ring

/-- Both `M₄` and `conj M₄` are local unitary images of some `G(η)`, `η ∈ 𝓗`. -/
theorem exists_M4_conj :
    (∃ p, LUEquiv M4 (Gv (etaV p))) ∧ (∃ q, LUEquiv (Psi.conj M4) (Gv (etaV q))) := by
  rcases orbit_etaV 0 with h | h
  · refine ⟨⟨0, h⟩, ⟨7, ?_⟩⟩
    have := luEquiv_conj h
    rwa [conj_Gv, conj_etaV_zero] at this
  · refine ⟨⟨7, ?_⟩, ⟨0, h⟩⟩
    have := luEquiv_conj h
    rwa [Psi.conj_conj, conj_Gv, conj_etaV_zero] at this

end FormalResearch.FourQubitEntropy.CO
