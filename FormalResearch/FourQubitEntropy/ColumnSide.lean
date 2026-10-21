import FormalResearch.FourQubitEntropy.NormalizeRows

/-!
# The column side: exchanging the two halves of a vector
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

/-- Exchange qubits `(1,2)` with `(3,4)`. -/
def swapHalves (ψ : Psi) : Psi := fun a b c d => ψ c d a b

theorem zmat_swapHalves (ψ : Psi) : zmat (swapHalves ψ) = (zmat ψ)ᵀ := by
  ext ⟨a, b⟩ ⟨c, d⟩; rfl

theorem colLU_swapHalves (K : Mat4) (ψ : Psi) : swapHalves (colLU K ψ) = rowLU K (swapHalves ψ) := by
  rw [← ofZmat_zmat (swapHalves (colLU K ψ)), ← ofZmat_zmat (rowLU K (swapHalves ψ))]
  rw [zmat_swapHalves, zmat_colLU, zmat_rowLU, zmat_swapHalves, Matrix.transpose_mul]
  simp

theorem normSqPsi_swapHalves (ψ : Psi) : normSqPsi (swapHalves ψ) = normSqPsi ψ := by
  unfold normSqPsi swapHalves
  simp only [Fin.sum_univ_two]
  ring

theorem red12_swapHalves (ψ : Psi) :
    red12 (swapHalves ψ) = ((zmat ψ)ᴴ * zmat ψ).map (starRingEnd ℂ) := by
  rw [red12_zmat, zmat_swapHalves, transpose_conjTranspose]
  exact transpose_mul_map_conj (zmat ψ) |>.symm ▸ rfl

/-- A cut matrix with the quadratic property has a Gram matrix with the same property. -/
theorem quadratic_gram {Z : Mat4}
    (hq : (Z * Zᴴ - (1 / 6 : ℂ) • 1) * (Z * Zᴴ - (1 / 2 : ℂ) • 1) = 0) :
    (Zᴴ * Z - (1 / 6 : ℂ) • 1) * (Zᴴ * Z - (1 / 2 : ℂ) • 1) = 0 := by
  have hA2 : Z * Zᴴ * (Z * Zᴴ) = (2 / 3 : ℂ) • (Z * Zᴴ) - (1 / 12 : ℂ) • 1 := by
    set A := Z * Zᴴ with hA
    have e : (A - (1 / 6 : ℂ) • 1) * (A - (1 / 2 : ℂ) • 1)
        = A * A - (2 / 3 : ℂ) • A + (1 / 12 : ℂ) • 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.one_mul, smul_smul]
      module
    rw [e] at hq
    calc A * A = (A * A - (2 / 3 : ℂ) • A + (1 / 12 : ℂ) • 1) + ((2 / 3 : ℂ) • A - (1 / 12 : ℂ) • 1) := by
          abel
      _ = _ := by rw [hq, zero_add]
  -- `Z` is invertible
  set A := Z * Zᴴ with hA
  set Zi : Mat4 := Zᴴ * ((12 * (2 / 3) : ℂ) • 1 - (12 : ℂ) • A) with hZi
  have hAN : A * ((12 * (2 / 3) : ℂ) • 1 - (12 : ℂ) • A) = 1 := by
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    rw [hA2]
    module
  have hZZi : Z * Zi = 1 := by
    rw [hZi, ← Matrix.mul_assoc, ← hA, hAN]
  have hZiZ : Zi * Z = 1 := mul_eq_one_comm.mp hZZi
  have hB : Zᴴ * Z * (Zi * Ziᴴ) = 1 := by
    calc Zᴴ * Z * (Zi * Ziᴴ) = Zᴴ * (Z * Zi) * Ziᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hZZi, Matrix.mul_one]
        have := congrArg Matrix.conjTranspose hZiZ
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] at this
        exact this
  have hB' : Zi * Ziᴴ * (Zᴴ * Z) = 1 := mul_eq_one_comm.mp hB
  set B := Zᴴ * Z with hBdef
  have hB3 : B * B * B = (2 / 3 : ℂ) • (B * B) - (1 / 12 : ℂ) • B := by
    have : B * B * B = Zᴴ * (A * A) * Z := by
      rw [hBdef, hA]; simp only [Matrix.mul_assoc]
    rw [this, hA2]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, hBdef, hA, Matrix.mul_assoc]
  have e : (B - (1 / 6 : ℂ) • 1) * (B - (1 / 2 : ℂ) • 1)
      = B * B - (2 / 3 : ℂ) • B + (1 / 12 : ℂ) • 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.one_mul, smul_smul]
    module
  rw [e]
  have hq0 : B * (B * B - (2 / 3 : ℂ) • B + (1 / 12 : ℂ) • 1) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hB3]
    module
  calc B * B - (2 / 3 : ℂ) • B + (1 / 12 : ℂ) • 1
      = (Zi * Ziᴴ * B) * (B * B - (2 / 3 : ℂ) • B + (1 / 12 : ℂ) • 1) := by rw [hB', Matrix.one_mul]
    _ = Zi * Ziᴴ * (B * (B * B - (2 / 3 : ℂ) • B + (1 / 12 : ℂ) • 1)) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hq0, Matrix.mul_zero]

theorem gram_rowLU {K : Mat4} (hK : Kᴴ * K = 1) (ψ : Psi) :
    (zmat (rowLU K ψ))ᴴ * zmat (rowLU K ψ) = (zmat ψ)ᴴ * zmat ψ := by
  rw [zmat_rowLU, Matrix.conjTranspose_mul]
  calc (zmat ψ)ᴴ * Kᴴ * (K * zmat ψ) = (zmat ψ)ᴴ * (Kᴴ * K) * zmat ψ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hK, Matrix.mul_one]

theorem rhoSite0_eq (ψ : Psi) (a a' : Fin 2) :
    ∑ b, red12 ψ (a, b) (a', b) = rhoSite 0 ψ a a' := by
  simp [red12, rhoSite, rho0, siteSwap, sum2, Psi.conj, Fin.sum_univ_two]

theorem rhoSite2_eq (ψ : Psi) (a a' : Fin 2) :
    ∑ b, red12 (swapHalves ψ) (a, b) (a', b) = rhoSite 2 ψ a a' := by
  simp [red12, rhoSite, rho0, siteSwap, sum2, swapHalves, Psi.conj, Fin.sum_univ_two]
  ring

theorem Gs_map_star : Gs.map (starRingEnd ℂ) = Gs := by
  ext i j
  have hsv : ∀ p, (starRingEnd ℂ) (sv p) = sv p := by
    intro p
    obtain ⟨a, b⟩ := p
    rw [sv_apply]; simp [map_mul, rt_conj]
    fin_cases a <;> fin_cases b <;> simp [eps2]
  simp [Gs, projVec, Matrix.one_apply, hsv, map_ofNat]
  by_cases h : i = j <;> simp [h]
  exact map_ofNat _ 6

end FormalResearch.FourQubitEntropy
