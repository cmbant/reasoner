module

public import ThreeCopyQutritWerner.TwoCutSOS
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section


/-!
# Real symmetric realization of a complex symmetric matrix

The real operator [[Re X, Im X], [Im X, -Re X]] realizes the antilinear
map z ↦ X conjugate(z). Its ordinary real spectral theorem is a foundation
for the Takagi argument required by the sharp partial-trace inequality.
No Takagi decomposition or rank-two projection estimate is assumed here.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Identify two real coordinate copies with the original complex coordinates. -/
def symmetricComplexify {n : Type*} (x : n ⊕ n → ℝ) : n → ℂ :=
  fun i => ⟨x (Sum.inl i), x (Sum.inr i)⟩

/-- The real symmetric realization of the complex antilinear map. -/
def symmetricRealification {n : Type*} (X : Matrix n n ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks (X.map Complex.re) (X.map Complex.im)
    (X.map Complex.im) (-(X.map Complex.re))

/-- Complexification loses no real coordinate information. -/
theorem symmetricComplexify_injective {n : Type*} :
    Function.Injective (symmetricComplexify (n := n)) := by
  intro x y h
  funext i
  cases i with
  | inl i => exact congrArg Complex.re (congrFun h i)
  | inr i => exact congrArg Complex.im (congrFun h i)

/-- The real Euclidean norm is exactly the complex Euclidean norm. -/
theorem symmetricComplexify_normSq {n : Type*} [Fintype n] (x : n ⊕ n → ℝ) :
    vecNormSq (symmetricComplexify x) = ∑ i, x i ^ 2 := by
  simp [vecNormSq, symmetricComplexify, Complex.normSq_apply,
    Fintype.sum_sum_type, Finset.sum_add_distrib, pow_two]

/-- Real inner products become the real part of the unchanged complex inner product. -/
theorem symmetricComplexify_braket_re {n : Type*} [Fintype n]
    (x y : n ⊕ n → ℝ) :
    (braket (symmetricComplexify x) (symmetricComplexify y)).re =
      ∑ i, x i * y i := by
  simp [braket, symmetricComplexify, Fintype.sum_sum_type,
    Finset.sum_add_distrib, Complex.mul_re]

/-- Multiplication by the real block matrix is precisely X times complex conjugation. -/
theorem symmetricRealification_mulVec {n : Type*} [Fintype n]
    (X : Matrix n n ℂ) (x : n ⊕ n → ℝ) :
    symmetricComplexify (symmetricRealification X *ᵥ x) =
      X *ᵥ (fun i => star (symmetricComplexify x i)) := by
  funext i
  apply Complex.ext <;>
    simp [symmetricComplexify, symmetricRealification, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Complex.mul_re, Complex.mul_im, add_comm]

/-- Complex transpose symmetry gives an ordinary real Hermitian matrix. -/
theorem symmetricRealification_isHermitian {n : Type*}
    (X : Matrix n n ℂ) (hX : Xᵀ = X) : (symmetricRealification X).IsHermitian := by
  have hs (i j : n) : X j i = X i j := congrFun (congrFun hX i) j
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [symmetricRealification, Matrix.conjTranspose_apply] using
        congrArg Complex.re (hs i j)
    | inr j => simpa [symmetricRealification, Matrix.conjTranspose_apply] using
        congrArg Complex.im (hs i j)
  | inr i =>
    cases j with
    | inl j => simpa [symmetricRealification, Matrix.conjTranspose_apply] using
        congrArg Complex.im (hs i j)
    | inr j => simpa [symmetricRealification, Matrix.conjTranspose_apply] using
        congrArg (fun z : ℂ => -z.re) (hs i j)

/-- A real eigenvector is an exact antilinear complex eigenvector, with the same real eigenvalue. -/
theorem symmetricRealification_eigenvector {n : Type*} [Fintype n]
    (X : Matrix n n ℂ) (x : n ⊕ n → ℝ) (r : ℝ)
    (hx : symmetricRealification X *ᵥ x = r • x) :
    X *ᵥ (fun i => star (symmetricComplexify x i)) =
      (r : ℂ) • symmetricComplexify x := by
  rw [← symmetricRealification_mulVec, hx]
  funext i
  apply Complex.ext <;> simp [symmetricComplexify, Complex.mul_re, Complex.mul_im]

/-- The pinned real spectral theorem provides an actual complete antilinear eigenfamily. -/
theorem symmetricRealification_spectral_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (j : n ⊕ n) :
    X *ᵥ (fun i => star (symmetricComplexify
      ((symmetricRealification_isHermitian X hX).eigenvectorBasis j) i)) =
      (((symmetricRealification_isHermitian X hX).eigenvalues j : ℝ) : ℂ) •
        symmetricComplexify ((symmetricRealification_isHermitian X hX).eigenvectorBasis j) :=
  symmetricRealification_eigenvector X _ _
    ((symmetricRealification_isHermitian X hX).mulVec_eigenvectorBasis j)

/-- Symmetry relates the two Hermitian pairings of antilinear eigenvectors. -/
theorem symmetricAntilinear_pair {n : Type*} [Fintype n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (u v : n → ℂ) (a b : ℝ)
    (hu : X *ᵥ (fun i => star (u i)) = (a : ℂ) • u)
    (hv : X *ᵥ (fun i => star (v i)) = (b : ℂ) • v) :
    (b : ℂ) * braket u v = (a : ℂ) * braket v u := by
  have h := Matrix.dotProduct_transpose_mulVec X
    (fun i => star (u i)) (fun i => star (v i))
  rw [hX, hu, hv] at h
  simpa [braket, dotProduct, smul_eq_mul, Finset.mul_sum,
    mul_assoc, mul_left_comm, Complex.star_def] using h

/-- Antilinear eigenvectors whose eigenvalues have nonzero sum have a real pairing. -/
theorem symmetricAntilinear_pair_im_zero {n : Type*} [Fintype n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (u v : n → ℂ) (a b : ℝ)
    (hu : X *ᵥ (fun i => star (u i)) = (a : ℂ) • u)
    (hv : X *ᵥ (fun i => star (v i)) = (b : ℂ) • v)
    (hab : a + b ≠ 0) : (braket u v).im = 0 := by
  have h := congrArg Complex.im (symmetricAntilinear_pair X hX u v a b hu hv)
  rw [← conj_braket u v] at h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.conj_im] at h
  apply (mul_eq_zero.mp (show (a + b) * (braket u v).im = 0 by nlinarith)).resolve_left hab

/-- Distinct positive real eigenvectors form an orthogonal complex family. -/
theorem symmetricRealification_positive_pair_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (i j : n ⊕ n) (hij : i ≠ j)
    (hi : 0 < (symmetricRealification_isHermitian X hX).eigenvalues i)
    (hj : 0 < (symmetricRealification_isHermitian X hX).eigenvalues j) :
    braket
      (symmetricComplexify ((symmetricRealification_isHermitian X hX).eigenvectorBasis i))
      (symmetricComplexify ((symmetricRealification_isHermitian X hX).eigenvectorBasis j)) = 0 := by
  apply Complex.ext
  · rw [symmetricComplexify_braket_re]
    have h := (symmetricRealification_isHermitian X hX).eigenvectorBasis.orthonormal.inner_eq_zero hij
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using h
  · exact symmetricAntilinear_pair_im_zero X hX _ _ _ _
      (symmetricRealification_spectral_eigenvector X hX i)
      (symmetricRealification_spectral_eigenvector X hX j) (by linarith)

end ThreeCopyQutritWerner
