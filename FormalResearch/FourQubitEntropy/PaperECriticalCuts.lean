import FormalResearch.FourQubitEntropy.PaperECriticalNormalForm

/-!
# The three cut matrices of `G(v)`

For `G(v)` with `zmat = B diag(v) Bᵀ`, the cut `13|24` (resp. `14|23`) has the same magic-basis form
`B diag(w₊) Bᵀ` (resp. `B diag(w₋) Bᵀ`) with `w₊ = H₊ v`, `w₋ = H₋ v` for the two Hadamard-type sign
matrices of `sextic_identity.tex` (`prop:fqe-moment-zeros`). Consequently the three cut spectra are
`|v|²`, `|H₊ v|²`, `|H₋ v|²`. Proved, no hypotheses, no `native_decide`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- `H₊ v`, the magic coordinates of `G(v)` across the cut `13|24`. -/
noncomputable def wp (v : Fin 2 × Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ
  | (0, 0) => (v (0, 0) - v (0, 1) + v (1, 0) - v (1, 1)) / 2
  | (0, 1) => (-v (0, 0) + v (0, 1) + v (1, 0) - v (1, 1)) / 2
  | (1, 0) => (v (0, 0) + v (0, 1) + v (1, 0) + v (1, 1)) / 2
  | (1, 1) => (-v (0, 0) - v (0, 1) + v (1, 0) + v (1, 1)) / 2

/-- `H₋ v`, the magic coordinates of `G(v)` across the cut `14|23`. -/
noncomputable def wm (v : Fin 2 × Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ
  | (0, 0) => (v (0, 0) - v (0, 1) - v (1, 0) - v (1, 1)) / 2
  | (0, 1) => (-v (0, 0) + v (0, 1) - v (1, 0) - v (1, 1)) / 2
  | (1, 0) => (-v (0, 0) - v (0, 1) + v (1, 0) - v (1, 1)) / 2
  | (1, 1) => (-v (0, 0) - v (0, 1) - v (1, 0) + v (1, 1)) / 2

set_option maxHeartbeats 4000000 in
theorem zmat_swap23_Gv (v : Fin 2 × Fin 2 → ℂ) :
    zmat (swap23 (Gv v)) = magicB * Matrix.diagonal (wp v) * magicBᵀ := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact rt_mul_rt
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [zmat, swap23, Gv, ofZmat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    magicB, wp, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
  ring_nf <;> simp only [Complex.I_sq, hrt2] <;> ring_nf


set_option maxHeartbeats 4000000 in
theorem zmat_swap24_Gv (v : Fin 2 × Fin 2 → ℂ) :
    zmat (swap24 (Gv v)) = magicB * Matrix.diagonal (wm v) * magicBᵀ := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact rt_mul_rt
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [zmat, swap24, Gv, ofZmat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    magicB, wm, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
  ring_nf <;> simp only [Complex.I_sq, hrt2] <;> ring_nf


/-! ### Spectral moments of a cut in magic form -/

theorem trace_magic_conj (X : Mat4) : Matrix.trace (magicB * X * magicBᴴ) = Matrix.trace X := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, magicB_unitary, Matrix.one_mul]

/-- If `zmat φ = B diag(w) Bᵀ` then `red12 φ = B diag(|w|²) Bᴴ`. -/
theorem red12_of_diag (φ : Psi) (w : Fin 2 × Fin 2 → ℂ)
    (h : zmat φ = magicB * Matrix.diagonal w * magicBᵀ) :
    red12 φ = magicB * Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) * magicBᴴ := by
  rw [red12_zmat, h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, transpose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  have e : Matrix.diagonal w * magicBᴴ = Matrix.diagonal w * magicBᴴ := rfl
  calc magicB * Matrix.diagonal w * magicBᵀ *
        (magicB.map star * (Matrix.diagonal (star w) * magicBᴴ))
      = magicB * Matrix.diagonal w * (magicBᵀ * magicB.map (starRingEnd ℂ)) *
        (Matrix.diagonal (star w) * magicBᴴ) := by simp only [Matrix.mul_assoc]; rfl
    _ = _ := by
        rw [hBB, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal w),
          Matrix.diagonal_mul_diagonal, ← Matrix.mul_assoc magicB]
        rfl

theorem red12_pow_two (φ : Psi) (w : Fin 2 × Fin 2 → ℂ)
    (h : zmat φ = magicB * Matrix.diagonal w * magicBᵀ) :
    (Matrix.trace (red12 φ * red12 φ)).re = ∑ k, Complex.normSq (w k) ^ 2 := by
  rw [red12_of_diag φ w h]
  have : magicB * Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) * magicBᴴ *
      (magicB * Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) * magicBᴴ) =
      magicB * (Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) *
        Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k))) * magicBᴴ := by
    calc _ = magicB * Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) * (magicBᴴ * magicB) *
          Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) * magicBᴴ := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [magicB_unitary, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [this, trace_magic_conj, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj]
  rw [← Complex.ofReal_mul, Complex.ofReal_re, pow_two]

theorem red12_pow_three (φ : Psi) (w : Fin 2 × Fin 2 → ℂ)
    (h : zmat φ = magicB * Matrix.diagonal w * magicBᵀ) :
    (Matrix.trace (red12 φ * red12 φ * red12 φ)).re = ∑ k, Complex.normSq (w k) ^ 3 := by
  rw [red12_of_diag φ w h]
  set D := Matrix.diagonal (fun k => w k * (starRingEnd ℂ) (w k)) with hD
  have : magicB * D * magicBᴴ * (magicB * D * magicBᴴ) * (magicB * D * magicBᴴ) =
      magicB * (D * D * D) * magicBᴴ := by
    calc _ = magicB * D * (magicBᴴ * magicB) * D * (magicBᴴ * magicB) * D * magicBᴴ := by
            simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [magicB_unitary]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, trace_magic_conj, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : w k * (starRingEnd ℂ) (w k) * (w k * (starRingEnd ℂ) (w k)) * (w k * (starRingEnd ℂ) (w k)) =
      ((Complex.normSq (w k) ^ 3 : ℝ) : ℂ) := by
    rw [Complex.mul_conj]; push_cast; ring
  rw [this, Complex.ofReal_re]

theorem normSqPsi_of_diag (φ : Psi) (w : Fin 2 × Fin 2 → ℂ)
    (h : zmat φ = magicB * Matrix.diagonal w * magicBᵀ) :
    normSqPsi φ = ∑ k, Complex.normSq (w k) := by
  have h1 : normSqPsi φ = (Matrix.trace (red12 φ)).re := by
    unfold normSqPsi
    simp only [Matrix.trace, Matrix.diag_apply, red12, Matrix.of_apply, Complex.re_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.mul_conj]; simp
  rw [h1, red12_of_diag φ w h, trace_magic_conj, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj]; simp

end FormalResearch.FourQubitEntropy.PaperECritical
