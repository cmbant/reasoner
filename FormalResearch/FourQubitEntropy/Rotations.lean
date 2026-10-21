import FormalResearch.FourQubitEntropy.BlockStructure

/-!
# Rotations of the magic basis by local unitaries

For `c ∈ SU(2)`, `c ⊗ c` fixes the singlet `m₃` and acts on `m₁, m₂, m₄` as a rotation. The
rotations about the three axes are the coordinate rotations in the planes `(m₁,m₂)`, `(m₂,m₄)`,
`(m₁,m₄)`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

abbrev RMat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- Real rotation in the plane `(m₁, m₂)` with cosine `p` and sine `q`. -/
def rotX (p q : ℝ) : RMat4 := Matrix.of fun i j =>
  match i, j with
  | (0, 0), (0, 0) => p
  | (0, 0), (0, 1) => q
  | (0, 1), (0, 0) => -q
  | (0, 1), (0, 1) => p
  | (1, 0), (1, 0) => 1
  | (1, 1), (1, 1) => 1
  | _, _ => 0

/-- Real rotation in the plane `(m₂, m₄)` with cosine `p` and sine `q`. -/
def rotY (p q : ℝ) : RMat4 := Matrix.of fun i j =>
  match i, j with
  | (0, 0), (0, 0) => 1
  | (0, 1), (0, 1) => p
  | (0, 1), (1, 1) => q
  | (1, 1), (0, 1) => -q
  | (1, 1), (1, 1) => p
  | (1, 0), (1, 0) => 1
  | _, _ => 0

/-- The SU(2) element `a - i b σ_x`. -/
noncomputable def cx (a b : ℝ) : Op1 := !![(a : ℂ), -(Complex.I * b); -(Complex.I * b), (a : ℂ)]

/-- The SU(2) element `a - i b σ_y`. -/
noncomputable def cy (a b : ℝ) : Op1 := !![(a : ℂ), -(b : ℂ); (b : ℂ), (a : ℂ)]

theorem cx_unitary {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : (cx a b)ᴴ * cx a b = 1 := by
  have h' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [cx, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply,
    Complex.conj_ofReal] <;>
  first | linear_combination h' | linear_combination h' + (-(b : ℂ) ^ 2) * hI | ring_nf

theorem cy_unitary {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : (cy a b)ᴴ * cy a b = 1 := by
  have h' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [cy, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply,
    Complex.conj_ofReal] <;>
  first | linear_combination h' | ring_nf

set_option maxHeartbeats 4000000 in
theorem magic_cx {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    magicBᴴ * kron (cx a b) (cx a b) * magicB = (rotX (a ^ 2 - b ^ 2) (2 * a * b)).map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hrt4 : rt ^ 4 = 1 / 4 := by rw [show rt ^ 4 = (rt ^ 2) ^ 2 by ring, hrt2]; norm_num
  have h' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hI4 : Complex.I ^ 4 = 1 := by rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, hI]; norm_num
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, cx, rotX,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj,
    Complex.conj_ofReal] <;>
  all_goals (try ring_nf)
  all_goals (try simp only [Complex.I_sq, hI4, hrt2, hrt4])
  all_goals (try ring_nf)
  all_goals (try linear_combination h')

set_option maxHeartbeats 4000000 in
theorem magic_cy {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    magicBᴴ * kron (cy a b) (cy a b) * magicB = (rotY (a ^ 2 - b ^ 2) (2 * a * b)).map Complex.ofReal := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have hrt4 : rt ^ 4 = 1 / 4 := by rw [show rt ^ 4 = (rt ^ 2) ^ 2 by ring, hrt2]; norm_num
  have h' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hI4 : Complex.I ^ 4 = 1 := by rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, hI]; norm_num
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, magicB, kron, cy, rotY,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj]
  all_goals (try ring_nf)
  all_goals (try simp only [Complex.I_sq, hI4, hrt2, hrt4])
  all_goals (try ring_nf)
  all_goals (try linear_combination h')

end FormalResearch.FourQubitEntropy
