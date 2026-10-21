import FormalResearch.FourQubitEntropy.Magic
import FormalResearch.FourQubitEntropy.Purity

/-!
# Magic-basis coordinates of a vector
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

set_option maxHeartbeats 4000000 in
theorem spinFlip_eq_trace (ψ : Psi) :
    spinFlipForm ψ = Matrix.trace ((zmat ψ)ᵀ * E4 * zmat ψ * E4ᵀ) := by
  simp [spinFlipForm, sum4, sum2, lit, zmat, E4, kron, eps2, sgn, Matrix.trace, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.transpose_apply,
    RingOps.ofInt, RingOps.add, RingOps.mul]
  ring

theorem zmat_eq_coord (Z : Mat4) : Z = magicB * magicCoord Z * magicBᵀ := by
  unfold magicCoord
  calc Z = (magicB * magicBᴴ) * Z * (magicB.map (starRingEnd ℂ) * magicBᵀ) := by
        rw [magicB_unitary', magicBbar_mul]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

theorem trace_aux {n : Type} [Fintype n] [DecidableEq n] (B X E : Matrix n n ℂ) (hE : Eᵀ = E)
    (h : Bᵀ * E * B = 1) :
    Matrix.trace ((B * X * Bᵀ)ᵀ * E * (B * X * Bᵀ) * Eᵀ) = Matrix.trace (Xᵀ * X) := by
  rw [hE]
  have e : (B * X * Bᵀ)ᵀ * E * (B * X * Bᵀ) * E = B * (Xᵀ * X) * (Bᵀ * E) := by
    calc (B * X * Bᵀ)ᵀ * E * (B * X * Bᵀ) * E
        = B * Xᵀ * (Bᵀ * E * B) * X * (Bᵀ * E) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = B * (Xᵀ * X) * (Bᵀ * E) := by rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem trace_coord (Z : Mat4) :
    Matrix.trace (Zᵀ * E4 * Z * E4ᵀ) = Matrix.trace ((magicCoord Z)ᵀ * magicCoord Z) := by
  have hZ := zmat_eq_coord Z
  have := trace_aux magicB (magicCoord Z) E4 E4_transpose magicB_E4
  rw [← hZ] at this
  exact this

theorem spinFlip_coord (ψ : Psi) :
    spinFlipForm ψ = Matrix.trace ((magicCoord (zmat ψ))ᵀ * magicCoord (zmat ψ)) := by
  rw [spinFlip_eq_trace, trace_coord]

/-- `X Xᴴ = Bᴴ (Z Zᴴ) B`. -/
theorem coord_mul_conjTranspose (Z : Mat4) :
    magicCoord Z * (magicCoord Z)ᴴ = magicBᴴ * (Z * Zᴴ) * magicB := by
  unfold magicCoord
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h : (magicB.map (starRingEnd ℂ))ᴴ = magicBᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [h, Matrix.conjTranspose_conjTranspose]
  calc magicBᴴ * Z * magicB.map (starRingEnd ℂ) * (magicBᵀ * (Zᴴ * magicB))
      = magicBᴴ * Z * (magicB.map (starRingEnd ℂ) * magicBᵀ) * Zᴴ * magicB := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [magicBbar_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- `Xᴴ X = Bᵀ (Zᴴ Z) B̄`. -/
theorem coord_conjTranspose_mul (Z : Mat4) :
    (magicCoord Z)ᴴ * magicCoord Z = magicBᵀ * (Zᴴ * Z) * magicB.map (starRingEnd ℂ) := by
  unfold magicCoord
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h : (magicB.map (starRingEnd ℂ))ᴴ = magicBᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [h, Matrix.conjTranspose_conjTranspose]
  calc magicBᵀ * (Zᴴ * magicB) * (magicBᴴ * Z * magicB.map (starRingEnd ℂ))
      = magicBᵀ * Zᴴ * (magicB * magicBᴴ) * Z * magicB.map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [magicB_unitary']; simp only [Matrix.mul_one, Matrix.mul_assoc]

end FormalResearch.FourQubitEntropy
