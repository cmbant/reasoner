module

public import ThreeCopyQutritWerner.TakagiPositivePart
public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-!
# A literal finite Takagi family, with no zero-space completion

The strictly positive eigenvectors of the real antilinear realization form an
orthonormal complex family. Their positive weights reconstruct the original
complex symmetric matrix, and the sum of squared weights is its Frobenius square.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The actual strictly positive part of the real spectral index set. -/
abbrev TakagiPositiveIndex {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :=
  {j : n ⊕ n // 0 < (symmetricRealification_isHermitian X hX).eigenvalues j}

/-- The actual complex vector underlying a positive real eigenvector. -/
def takagiVector {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (j : TakagiPositiveIndex X hX) : n → ℂ :=
  symmetricComplexify ((symmetricRealification_isHermitian X hX).eigenvectorBasis j.val)

/-- The corresponding positive singular weight, as an actual real eigenvalue. -/
def takagiWeight {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (j : TakagiPositiveIndex X hX) : ℝ :=
  (symmetricRealification_isHermitian X hX).eigenvalues j.val

theorem takagiWeight_pos {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (j : TakagiPositiveIndex X hX) :
    0 < takagiWeight X hX j := j.property

/-- Real unit normalization is unchanged by the real-to-complex coordinate identification. -/
theorem takagiVector_normSq {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (j : TakagiPositiveIndex X hX) :
    vecNormSq (takagiVector X hX j) = 1 := by
  rw [takagiVector, symmetricComplexify_normSq]
  have h := (symmetricRealification_isHermitian X hX).eigenvectorBasis.inner_eq_one j.val
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial, Fintype.sum_sum_type, pow_two] using h

/-- The positive spectral family is orthonormal for the original complex inner product. -/
theorem takagiVector_braket {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (i j : TakagiPositiveIndex X hX) :
    braket (takagiVector X hX i) (takagiVector X hX j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_true, braket_self, takagiVector_normSq, Complex.ofReal_one]
  · rw [if_neg hij]
    exact symmetricRealification_positive_pair_orthogonal X hX i.val j.val
      (fun h => hij (Subtype.ext h)) i.property j.property

/-- The positive-index family, packaged in the standard complex Euclidean space. -/
theorem takagiVector_orthonormal {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :
    Orthonormal ℂ (fun j : TakagiPositiveIndex X hX => WithLp.toLp 2 (takagiVector X hX j)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [EuclideanSpace.inner_eq_star_dotProduct, braket, dotProduct, mul_comm,
    Complex.star_def] using takagiVector_braket X hX i j

/-- Dropping the zero-weight indices retains the exact symmetric spectral reconstruction. -/
theorem takagiVector_reconstruct {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (i j : n) :
    X i j = ∑ k : TakagiPositiveIndex X hX,
      (takagiWeight X hX k : ℂ) * takagiVector X hX k i * takagiVector X hX k j := by
  classical
  rw [takagiPositiveRealPart_reconstruct X hX]
  let w := (symmetricRealification_isHermitian X hX).eigenvalues
  let v := fun k => symmetricComplexify
    ((symmetricRealification_isHermitian X hX).eigenvectorBasis k)
  change (∑ k : n ⊕ n, ((max (w k) 0 : ℝ) : ℂ) * v k i * v k j) =
    ∑ k : {k : n ⊕ n // 0 < w k}, (w k.val : ℂ) * v k.val i * v k.val j
  rw [← Finset.sum_subtype (Finset.univ.filter (fun k => 0 < w k))
    (by intro k; simp) (fun k => (w k : ℂ) * v k i * v k j), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 0 < w k
  · simp [hk, max_eq_left hk.le]
  · simp [hk, max_eq_right (le_of_not_gt hk)]

/-- The unchanged positive Takagi family as a rectangular matrix of columns. -/
def takagiFrame {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) : Matrix n (TakagiPositiveIndex X hX) ℂ :=
  fun i j => takagiVector X hX j i

/-- The rectangular Takagi frame is an actual complex isometry. -/
theorem takagiFrame_gram {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :
    (takagiFrame X hX)ᴴ * takagiFrame X hX = 1 := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, takagiFrame, Matrix.one_apply,
    braket] using takagiVector_braket X hX i j

/-- The actual Takagi factorization has transpose, not adjoint, on its second frame. -/
theorem takagiFrame_factorization {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :
    X = takagiFrame X hX * Matrix.diagonal (fun j => (takagiWeight X hX j : ℂ)) *
      (takagiFrame X hX)ᵀ := by
  ext i j
  rw [takagiVector_reconstruct X hX]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, takagiFrame, mul_assoc, mul_left_comm, mul_comm]

/-- The exact squared Takagi weights sum to the original Frobenius square. -/
theorem takagiWeight_sum_sq {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :
    frobSq X = ∑ j : TakagiPositiveIndex X hX, takagiWeight X hX j ^ 2 := by
  conv_lhs => rw [takagiFrame_factorization X hX]
  rw [Matrix.mul_assoc,
    frobSq_isometry_mul _ (takagiFrame_gram X hX), ← frobSq_transpose',
    Matrix.transpose_mul, Matrix.transpose_transpose,
    frobSq_isometry_mul _ (takagiFrame_gram X hX)]
  simp [frobSq, Matrix.transpose_apply, Matrix.diagonal_apply,
    apply_ite, Complex.normSq_ofReal, pow_two]

end ThreeCopyQutritWerner
