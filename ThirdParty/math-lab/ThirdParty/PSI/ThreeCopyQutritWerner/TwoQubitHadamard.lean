module

public import ThreeCopyQutritWerner.TwoQubitPolygon
public import ThreeCopyQutritWerner.TwoQubitProductVectors

@[expose] public section


/-! Literal four-column mixing for the two-qubit PPT route. A Gram factor
whose spin congruence has nonnegative polygon weights gives a finite product
ensemble in the existing separability predicate. The spectral construction of
that Gram factor remains a separate obligation. -/
noncomputable section
open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

def twoQubitHadamard : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

theorem twoQubitHadamard_square (i j : Fin 4) :
    twoQubitHadamard i j ^ 2 = (1 / 4 : ℂ) := by
  fin_cases i <;> fin_cases j <;> norm_num [twoQubitHadamard]

theorem twoQubitHadamard_unitary : twoQubitHadamard * twoQubitHadamardᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoQubitHadamard, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, map_ofNat]

def twoQubitPhaseMix (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal p * twoQubitHadamard

theorem twoQubitPhaseMix_unitary (p : Fin 4 → ℂ)
    (hp : ∀ i, Complex.normSq (p i) = 1) :
    twoQubitPhaseMix p * (twoQubitPhaseMix p)ᴴ = 1 := by
  have hd : Matrix.diagonal p * (Matrix.diagonal p)ᴴ = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        Complex.star_def, Complex.mul_conj, hp]
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij]
  calc
    twoQubitPhaseMix p * (twoQubitPhaseMix p)ᴴ =
        Matrix.diagonal p * (twoQubitHadamard * twoQubitHadamardᴴ) *
          (Matrix.diagonal p)ᴴ := by
      simp only [twoQubitPhaseMix, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [twoQubitHadamard_unitary]; simpa using hd

theorem twoQubitPhaseMix_spin_diagonal_zero (p : Fin 4 → ℂ) (a : Fin 4 → ℝ)
    (hs : ∑ i, (a i : ℂ) * (p i) ^ 2 = 0) (k : Fin 4) :
    ((twoQubitPhaseMix p)ᵀ * Matrix.diagonal (fun i => (a i : ℂ)) *
      twoQubitPhaseMix p) k k = 0 := by
  have he (i j : Fin 4) : twoQubitPhaseMix p i j =
      p i * twoQubitHadamard i j := Matrix.diagonal_mul p twoQubitHadamard i j
  calc
    ((twoQubitPhaseMix p)ᵀ * Matrix.diagonal (fun i => (a i : ℂ)) *
        twoQubitPhaseMix p) k k =
        ∑ i, (p i * twoQubitHadamard i k) *
          ((a i : ℂ) * (p i * twoQubitHadamard i k)) := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.transpose_apply, Matrix.diagonal_mul, he]
    _ = (1 / 4 : ℂ) * ∑ i, (a i : ℂ) * (p i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      linear_combination (a i : ℂ) * (p i) ^ 2 * twoQubitHadamard_square i k
    _ = 0 := by rw [hs, mul_zero]

/-- The factor is an actual four-column complex matrix on the literal
bipartite indices. Its spin diagonal and polygon inequalities suffice to
construct a finite product ensemble of its Gram operator. -/
theorem isBipartiteSeparable_of_spin_diagonal_polygon
    (A : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ) (a : Fin 4 → ℝ)
    (hA : Aᵀ * twoQubitSpinMatrix * A = Matrix.diagonal (fun i => (a i : ℂ)))
    (ha : ∀ i, 0 ≤ a i) (hpoly : ∀ i, 2 * a i ≤ ∑ j, a j) :
    IsBipartiteSeparable (A * Aᴴ) := by
  obtain ⟨p, hp, hs⟩ := complex_unit_phases_of_polygon a ha hpoly
  let Q := twoQubitPhaseMix p
  let B := A * Q
  have hBB : B * Bᴴ = A * Aᴴ := by
    calc
      B * Bᴴ = A * (Q * Qᴴ) * Aᴴ := by
        simp only [B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = A * Aᴴ := by rw [twoQubitPhaseMix_unitary p hp]; simp
  have hcong : Bᵀ * twoQubitSpinMatrix * B =
      Qᵀ * Matrix.diagonal (fun i => (a i : ℂ)) * Q := by
    calc
      Bᵀ * twoQubitSpinMatrix * B = Qᵀ * (Aᵀ * twoQubitSpinMatrix * A) * Q := by
        simp only [B, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hA]
  have hzero : ∀ k : Fin 4,
      (∑ i, ∑ j, B i k * twoQubitSpinMatrix i j * B j k) = 0 := by
    intro k
    have hform : (∑ i, ∑ j, B i k * twoQubitSpinMatrix i j * B j k) =
        (Bᵀ * twoQubitSpinMatrix * B) k k := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hform, hcong]
    exact twoQubitPhaseMix_spin_diagonal_zero p a hs k
  have hensemble : (∑ k : Fin 4, ketBra (fun i => B i k) (fun i => B i k)) =
      A * Aᴴ := by
    rw [← hBB]
    ext i j
    simp [Matrix.sum_apply, ketBra, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← hensemble]
  exact isBipartiteSeparable_of_spin_zero_ensemble (fun k i => B i k) hzero

end ThreeCopyQutritWerner
