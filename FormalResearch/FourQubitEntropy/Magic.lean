import FormalResearch.FourQubitEntropy.EqualityConverse

/-!
# The magic basis

`B` has the magic basis `m₁ … m₄` of two qubits as columns, indexed by pairs (the column `(1,0)` is the
singlet). Coordinates of a cut matrix are `X = Bᴴ Z B̄`, so `Z = B X Bᵀ`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

/-- `1/√2`. -/
noncomputable def rt : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem rt_mul_rt : rt * rt = 1 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold rt
  rw [← Complex.ofReal_mul, ← mul_inv, h]; push_cast; ring

theorem rt_conj : (starRingEnd ℂ) rt = rt := Complex.conj_ofReal _

/-- The magic basis as columns: `m₁ = (|00⟩+|11⟩)/√2`, `m₂ = i(|01⟩+|10⟩)/√2`,
`m₃ = (|01⟩-|10⟩)/√2`, `m₄ = i(|00⟩-|11⟩)/√2`; the columns are indexed `(0,0),(0,1),(1,0),(1,1)`. -/
noncomputable def magicB : Mat4 := Matrix.of fun p j =>
  match p, j with
  | (0, 0), (0, 0) => rt
  | (1, 1), (0, 0) => rt
  | (0, 1), (0, 1) => Complex.I * rt
  | (1, 0), (0, 1) => Complex.I * rt
  | (0, 1), (1, 0) => rt
  | (1, 0), (1, 0) => -rt
  | (0, 0), (1, 1) => Complex.I * rt
  | (1, 1), (1, 1) => -(Complex.I * rt)
  | _, _ => 0

/-- Magic-basis coordinates of a cut matrix. -/
noncomputable def magicCoord (Z : Mat4) : Mat4 := magicBᴴ * Z * magicB.map (starRingEnd ℂ)

theorem magicB_unitary : magicBᴴ * magicB = 1 := by
  have h := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact h
  have hrt4 : rt ^ 4 = 1 / 4 := by rw [show rt ^ 4 = (rt ^ 2) ^ 2 by ring, hrt2]; norm_num
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, Fintype.sum_prod_type,
    Fin.sum_univ_two, rt_conj, Complex.I_mul_I] <;>
  first
    | linear_combination h
    | linear_combination 2 * h
    | linear_combination (-2) * h
    | linear_combination 4 * h + (-2 * rt ^ 2) * hI
    | linear_combination (-4) * h + (2 * rt ^ 2) * hI
    | linear_combination 2 * h + (-rt ^ 2) * hI
    | linear_combination 2 * h + (rt ^ 2) * hI
    | (ring_nf; simp only [Complex.I_sq, hrt2, hrt4]; ring_nf)

theorem magicB_unitary' : magicB * magicBᴴ = 1 := mul_eq_one_comm.mp magicB_unitary

/-- `B̄ Bᵀ = 1`. -/
theorem magicBbar_mul : magicB.map (starRingEnd ℂ) * magicBᵀ = 1 :=
  mul_eq_one_comm.mp (unitary_transpose_mul magicB_unitary)

/-- The matrix `ε ⊗ ε` of the spin flip on two qubits. -/
def eps2 : Op1 := !![0, 1; -1, 0]

def E4 : Mat4 := kron eps2 eps2

theorem E4_transpose : E4ᵀ = E4 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [E4, kron, eps2, Matrix.kroneckerMap_apply]

set_option maxHeartbeats 4000000 in
theorem magicB_E4 : magicBᵀ * E4 * magicB = 1 := by
  have h := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact h
  have hrt4 : rt ^ 4 = 1 / 4 := by rw [show rt ^ 4 = (rt ^ 2) ^ 2 by ring, hrt2]; norm_num
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Matrix.mul_apply, Matrix.transpose_apply, magicB, E4, kron, eps2, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply] <;>
  first
    | linear_combination h
    | linear_combination 2 * h
    | linear_combination (-2) * h
    | (ring_nf; simp only [Complex.I_sq, hrt2, hrt4]; ring_nf)

end FormalResearch.FourQubitEntropy
