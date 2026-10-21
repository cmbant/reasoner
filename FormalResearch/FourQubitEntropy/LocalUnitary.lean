import FormalResearch.FourQubitEntropy.EqualityReduction

/-!
# Local unitaries on a four-qubit vector

A vector `ψ` is viewed as the `4×4` matrix `Z = zmat ψ`, with rows indexed by qubits `1,2` and
columns by qubits `3,4`. A local unitary `a ⊗ b ⊗ c ⊗ d` acts as `Z ↦ (a ⊗ b) Z (c ⊗ d)ᵀ`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

/-- One-qubit operators. -/
abbrev Op1 := Matrix (Fin 2) (Fin 2) ℂ

/-- The matrix of a vector across the cut `12|34`. -/
def zmat (ψ : Psi) : Mat4 := Matrix.of fun i j => ψ i.1 i.2 j.1 j.2

/-- The vector with a given cut matrix. -/
def ofZmat (Z : Mat4) : Psi := fun a b c d => Z (a, b) (c, d)

@[simp] theorem zmat_ofZmat (Z : Mat4) : zmat (ofZmat Z) = Z := by
  ext ⟨a, b⟩ ⟨c, d⟩; rfl

@[simp] theorem ofZmat_zmat (ψ : Psi) : ofZmat (zmat ψ) = ψ := rfl

/-- Two-qubit operator from two one-qubit operators. -/
def kron (a b : Op1) : Mat4 := a ⊗ₖ b

/-- A local operator on qubits `1,2`. -/
def rowLU (K : Mat4) (ψ : Psi) : Psi := ofZmat (K * zmat ψ)

/-- A local operator on qubits `3,4`. -/
def colLU (K : Mat4) (ψ : Psi) : Psi := ofZmat (zmat ψ * Kᵀ)

theorem zmat_rowLU (K : Mat4) (ψ : Psi) : zmat (rowLU K ψ) = K * zmat ψ := by
  simp [rowLU]

theorem zmat_colLU (K : Mat4) (ψ : Psi) : zmat (colLU K ψ) = zmat ψ * Kᵀ := by
  simp [colLU]

theorem red12_zmat (ψ : Psi) : red12 ψ = zmat ψ * (zmat ψ)ᴴ := red12_eq ψ

theorem red12_rowLU (K : Mat4) (ψ : Psi) : red12 (rowLU K ψ) = K * red12 ψ * Kᴴ := by
  rw [red12_zmat, red12_zmat, zmat_rowLU, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem transpose_conjTranspose (K : Mat4) : (Kᵀ)ᴴ = K.map star := by
  ext i j; simp [Matrix.conjTranspose_apply]

theorem unitary_transpose_mul {K : Mat4} (hK : Kᴴ * K = 1) : Kᵀ * K.map star = 1 := by
  have := congrArg Matrix.transpose hK
  rw [Matrix.transpose_mul, Matrix.transpose_one] at this
  convert this using 2
  ext i j; simp [Matrix.conjTranspose_apply]

theorem red12_colLU (K : Mat4) (hK : Kᴴ * K = 1) (ψ : Psi) : red12 (colLU K ψ) = red12 ψ := by
  rw [red12_zmat, red12_zmat, zmat_colLU, Matrix.conjTranspose_mul, transpose_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Kᵀ, unitary_transpose_mul hK, Matrix.one_mul]

/-! ### The full local action -/

/-- The local operator `a ⊗ b ⊗ c ⊗ d`. -/
def localApply (a b c d : Op1) (ψ : Psi) : Psi :=
  colLU (kron c d) (rowLU (kron a b) ψ)

theorem zmat_localApply (a b c d : Op1) (ψ : Psi) :
    zmat (localApply a b c d ψ) = kron a b * zmat ψ * (kron c d)ᵀ := by
  simp [localApply, zmat_colLU, zmat_rowLU]

/-- `φ` is obtained from `ψ` by a local unitary. -/
def LUEquiv (ψ φ : Psi) : Prop :=
  ∃ a b c d : Op1, aᴴ * a = 1 ∧ bᴴ * b = 1 ∧ cᴴ * c = 1 ∧ dᴴ * d = 1 ∧
    localApply a b c d ψ = φ

theorem kron_unitary {a b : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) :
    (kron a b)ᴴ * kron a b = 1 := by
  unfold kron
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ha, hb]
  exact Matrix.one_kronecker_one

theorem kron_mul (a b a' b' : Op1) : kron a b * kron a' b' = kron (a * a') (b * b') := by
  unfold kron; rw [← Matrix.mul_kronecker_mul]

theorem kron_one : kron 1 1 = 1 := Matrix.one_kronecker_one

theorem localApply_one (ψ : Psi) : localApply 1 1 1 1 ψ = ψ := by
  rw [← ofZmat_zmat (localApply 1 1 1 1 ψ), zmat_localApply, kron_one]
  simp

theorem localApply_comp (a b c d a' b' c' d' : Op1) (ψ : Psi) :
    localApply a b c d (localApply a' b' c' d' ψ) = localApply (a * a') (b * b') (c * c') (d * d') ψ := by
  rw [← ofZmat_zmat (localApply a b c d _), ← ofZmat_zmat (localApply (a * a') _ _ _ _)]
  rw [zmat_localApply, zmat_localApply, zmat_localApply, ← kron_mul, ← kron_mul]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem LUEquiv.symm {ψ φ : Psi} (h : LUEquiv ψ φ) : LUEquiv φ ψ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  refine ⟨aᴴ, bᴴ, cᴴ, dᴴ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using mul_eq_one_comm.mp ha
  · simpa using mul_eq_one_comm.mp hb
  · simpa using mul_eq_one_comm.mp hc
  · simpa using mul_eq_one_comm.mp hd
  · rw [localApply_comp, ha, hb, hc, hd]
    exact localApply_one ψ

/-! ### Permuting qubits -/

/-- Exchange qubits `2` and `3`. -/
def swap23 (ψ : Psi) : Psi := fun a b c d => ψ a c b d

/-- Exchange qubits `2` and `4`. -/
def swap24 (ψ : Psi) : Psi := fun a b c d => ψ a d c b

theorem localApply_apply (a b c d : Op1) (ψ : Psi) (p q r s : Fin 2) :
    localApply a b c d ψ p q r s =
      ∑ p', ∑ q', ∑ r', ∑ s', a p p' * b q q' * c r r' * d s s' * ψ p' q' r' s' := by
  rw [show localApply a b c d ψ p q r s = (zmat (localApply a b c d ψ)) (p, q) (r, s) from rfl,
    zmat_localApply]
  simp only [Matrix.mul_apply, kron, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, zmat, Matrix.of_apply]
  simp only [Fin.sum_univ_two]
  ring

theorem swap23_localApply (a b c d : Op1) (ψ : Psi) :
    swap23 (localApply a c b d ψ) = localApply a b c d (swap23 ψ) := by
  funext p q r s
  simp only [swap23, localApply_apply, Fin.sum_univ_two]
  ring

theorem swap24_localApply (a b c d : Op1) (ψ : Psi) :
    swap24 (localApply a d c b ψ) = localApply a b c d (swap24 ψ) := by
  funext p q r s
  simp only [swap24, localApply_apply, Fin.sum_univ_two]
  ring

theorem red13_eq_swap (ψ : Psi) : red13 ψ = red12 (swap23 ψ) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp [red13, red12, swap23, Fin.sum_univ_two]
  try ring

theorem red14_eq_swap (ψ : Psi) : red14 ψ = red12 (swap24 ψ) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp [red14, red12, swap24, Fin.sum_univ_two]
  try ring

end FormalResearch.FourQubitEntropy
