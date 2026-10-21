import FormalResearch.FourQubitEntropy.Purity

/-!
# Spectral facts for the reduced matrices

For a Hermitian matrix with eigenvalues `λᵢ`, `tr A^k = Σ λᵢ^k`; and the reduced matrices of a
vector are positive semidefinite Gram matrices.
-/

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy

section PowerTrace

/-- The unitary of eigenvectors as a plain matrix. -/
noncomputable def eigU {A : Mat4} (hA : A.IsHermitian) : Mat4 :=
  ((hA.eigenvectorUnitary : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) : Mat4)

theorem conj_pow (U D A : Mat4) (hA : A = U * D * star U) (h1 : star U * U = 1)
    (h0 : U * star U = 1) (k : ℕ) : A ^ k = U * D ^ k * star U := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    rw [pow_succ, ih, hA]
    calc U * D ^ k * star U * (U * D * star U) = U * D ^ k * (star U * U) * D * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * D ^ (k + 1) * star U := by
          rw [h1, Matrix.mul_one, pow_succ, Matrix.mul_assoc U, Matrix.mul_assoc]

variable {A : Mat4} (hA : A.IsHermitian)

theorem trace_pow_eq (k : ℕ) :
    Matrix.trace (A ^ k) = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ k := by
  have h1 : star (eigU hA) * eigU hA = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h0 : eigU hA * star (eigU hA) = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = eigU hA * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (eigU hA) := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  rw [conj_pow _ _ A hspec h1 h0 k, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1,
    Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

end PowerTrace

end FormalResearch.FourQubitEntropy
