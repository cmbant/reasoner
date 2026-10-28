import FormalResearch.FourQubitEntropy.MagicCoord
import FormalResearch.FourQubitEntropy.LocalUnitary
import FormalResearch.FourQubitEntropy.Rotations
open scoped ComplexConjugate Matrix Kronecker
namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

theorem actOn_zero (σ : Op1) (ψ : Psi) : actOn 0 σ ψ = ofZmat (kron σ 1 * zmat ψ) := by
  funext a b c d
  simp [actOn, ofZmat, zmat, kron, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.one_apply]
theorem actOn_one (σ : Op1) (ψ : Psi) : actOn 1 σ ψ = ofZmat (kron 1 σ * zmat ψ) := by
  funext a b c d
  simp [actOn, ofZmat, zmat, kron, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.one_apply]
theorem actOn_two (σ : Op1) (ψ : Psi) : actOn 2 σ ψ = ofZmat (zmat ψ * (kron σ 1)ᵀ) := by
  funext a b c d
  simp [actOn, ofZmat, zmat, kron, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.one_apply]
  ring
theorem actOn_three (σ : Op1) (ψ : Psi) : actOn 3 σ ψ = ofZmat (zmat ψ * (kron 1 σ)ᵀ) := by
  funext a b c d
  simp [actOn, ofZmat, zmat, kron, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.one_apply]
  ring

theorem expectation_eq_trace (i : Fin 4) (σ : Op1) (ψ : Psi) :
    expectation i σ ψ = Matrix.trace ((zmat ψ)ᴴ * zmat (actOn i σ ψ)) := by
  simp [expectation, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, zmat,
    Fintype.sum_prod_type]
  ring



theorem left_formula (K : Mat4) (A : RMat4) (hK : magicBᴴ * K * magicB = Complex.I • A.map Complex.ofReal)
    (ψ : Psi) :
    Matrix.trace ((zmat ψ)ᴴ * (K * zmat ψ)) =
      Complex.I * ∑ j, ∑ k, (A j k : ℂ) * (magicCoord (zmat ψ) * (magicCoord (zmat ψ))ᴴ) k j := by
  set X := magicCoord (zmat ψ) with hXdef
  have hZ : zmat ψ = magicB * X * magicBᵀ := zmat_eq_coord (zmat ψ)
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := mul_eq_one_comm.mp magicBbar_mul
  have e1 : (zmat ψ)ᴴ * (K * zmat ψ) =
      magicB.map (starRingEnd ℂ) * (Xᴴ * (magicBᴴ * K * magicB) * X * magicBᵀ) := by
    conv_lhs => rw [hZ]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, transpose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rfl
  rw [e1, Matrix.trace_mul_comm]
  have e2 : (Xᴴ * (magicBᴴ * K * magicB) * X * magicBᵀ) * magicB.map (starRingEnd ℂ) =
      Xᴴ * (magicBᴴ * K * magicB) * X := by
    rw [Matrix.mul_assoc _ magicBᵀ, hBB, Matrix.mul_one]
  rw [e2, hK, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring


theorem right_formula (K : Mat4) (A : RMat4) (hK : magicBᴴ * K * magicB = Complex.I • A.map Complex.ofReal)
    (ψ : Psi) :
    Matrix.trace ((zmat ψ)ᴴ * (zmat ψ * Kᵀ)) =
      Complex.I * ∑ j, ∑ k, (A j k : ℂ) * ((magicCoord (zmat ψ))ᴴ * magicCoord (zmat ψ)) j k := by
  set X := magicCoord (zmat ψ) with hXdef
  have hZ : zmat ψ = magicB * X * magicBᵀ := zmat_eq_coord (zmat ψ)
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := mul_eq_one_comm.mp magicBbar_mul
  have hU : magicBᴴ * magicB = 1 := magicB_unitary
  have e1 : (zmat ψ)ᴴ * (zmat ψ * Kᵀ) =
      magicB.map (starRingEnd ℂ) * (Xᴴ * X * (magicBᵀ * Kᵀ)) := by
    conv_lhs => rw [hZ]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, transpose_conjTranspose]
    calc _ = magicB.map star * (Xᴴ * (magicBᴴ * magicB) * X * (magicBᵀ * Kᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]; rfl
  rw [e1, Matrix.trace_mul_comm]
  have e2 : (Xᴴ * X * (magicBᵀ * Kᵀ)) * magicB.map (starRingEnd ℂ) =
      Xᴴ * X * (magicBᴴ * K * magicB)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    have : (magicBᴴ)ᵀ = magicB.map (starRingEnd ℂ) := by ext i j; simp [Matrix.conjTranspose_apply]
    rw [this]
    simp only [Matrix.mul_assoc]
  rw [e2, hK, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring


/-- Real matrix unit. -/
def Eu (i j : Fin 2 × Fin 2) : RMat4 := Matrix.of fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

/-- `Bᴴ (σX 1) B` is `i` times a real antisymmetric matrix. -/
def A_x1 : RMat4 := Eu (0,0) (0,1) - Eu (0,1) (0,0) - Eu (1,0) (1,1) + Eu (1,1) (1,0)

set_option maxHeartbeats 4000000 in
theorem L_x1 : magicBᴴ * kron pauliX 1 * magicB = Complex.I • A_x1.map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, pauliX, A_x1, Eu,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj, Matrix.one_apply] <;>
  first | ring_nf | skip
  all_goals (try simp only [Complex.I_sq, hI3, hrt2])
  all_goals (try ring_nf)

/-- `Bᴴ (1 σX) B` is `i` times a real antisymmetric matrix. -/
def A_x2 : RMat4 := Eu (0,0) (0,1) - Eu (0,1) (0,0) + Eu (1,0) (1,1) - Eu (1,1) (1,0)

set_option maxHeartbeats 4000000 in
theorem L_x2 : magicBᴴ * kron 1 pauliX * magicB = Complex.I • A_x2.map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, pauliX, A_x2, Eu,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj, Matrix.one_apply] <;>
  first | ring_nf | skip
  all_goals (try simp only [Complex.I_sq, hI3, hrt2])
  all_goals (try ring_nf)

/-- `Bᴴ (σY 1) B` is `i` times a real antisymmetric matrix. -/
def A_y1 : RMat4 := Eu (0,0) (1,0) + Eu (0,1) (1,1) - Eu (1,0) (0,0) - Eu (1,1) (0,1)

set_option maxHeartbeats 4000000 in
theorem L_y1 : magicBᴴ * kron pauliY 1 * magicB = Complex.I • A_y1.map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, pauliY, A_y1, Eu,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj, Matrix.one_apply] <;>
  first | ring_nf | skip
  all_goals (try simp only [Complex.I_sq, hI3, hrt2])
  all_goals (try ring_nf)

/-- `Bᴴ (1 σY) B` is `i` times a real antisymmetric matrix. -/
def A_y2 : RMat4 := -Eu (0,0) (1,0) + Eu (0,1) (1,1) + Eu (1,0) (0,0) - Eu (1,1) (0,1)

set_option maxHeartbeats 4000000 in
theorem L_y2 : magicBᴴ * kron 1 pauliY * magicB = Complex.I • A_y2.map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, pauliY, A_y2, Eu,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj, Matrix.one_apply] <;>
  first | ring_nf | skip
  all_goals (try simp only [Complex.I_sq, hI3, hrt2])
  all_goals (try ring_nf)

/-- `Bᴴ (σZ 1) B` is `i` times a real antisymmetric matrix. -/
def A_z1 : RMat4 := Eu (0,0) (1,1) - Eu (0,1) (1,0) + Eu (1,0) (0,1) - Eu (1,1) (0,0)

set_option maxHeartbeats 4000000 in
theorem L_z1 : magicBᴴ * kron pauliZ 1 * magicB = Complex.I • A_z1.map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, pauliZ, A_z1, Eu,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj, Matrix.one_apply] <;>
  first | ring_nf | skip
  all_goals (try simp only [Complex.I_sq, hI3, hrt2])
  all_goals (try ring_nf)

/-- `Bᴴ (1 σZ) B` is `i` times a real antisymmetric matrix. -/
def A_z2 : RMat4 := Eu (0,0) (1,1) + Eu (0,1) (1,0) - Eu (1,0) (0,1) - Eu (1,1) (0,0)

set_option maxHeartbeats 4000000 in
theorem L_z2 : magicBᴴ * kron 1 pauliZ * magicB = Complex.I • A_z2.map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, pauliZ, A_z2, Eu,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj, Matrix.one_apply] <;>
  first | ring_nf | skip
  all_goals (try simp only [Complex.I_sq, hI3, hrt2])
  all_goals (try ring_nf)

end FormalResearch.FourQubitEntropy.PaperECritical
