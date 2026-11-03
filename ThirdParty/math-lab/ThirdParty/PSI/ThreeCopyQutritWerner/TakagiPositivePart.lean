module

public import ThreeCopyQutritWerner.SymmetricRealification
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

@[expose] public section


/-!
# Positive real spectral reconstruction of a complex symmetric matrix

Conjugation by the real complex structure sends the antilinear realization T
to -T. Functional calculus therefore gives T = T₊ - J T₊ J-adjoint.
The real spectral expansion of T₊ then reconstructs X as a sum of complex
symmetric rank-one terms with nonnegative coefficients. Terms with positive
coefficients are the actual positive real eigenvectors, already complex orthogonal.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The ordinary real matrix representing multiplication by i. -/
def takagiRealComplexStructure {n : Type*} [DecidableEq n] : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- The real complex structure is orthogonal, hence a real unitary. -/
theorem takagiRealComplexStructure_mem_unitary {n : Type*} [Fintype n] [DecidableEq n] :
    takagiRealComplexStructure (n := n) ∈ Matrix.unitaryGroup (n ⊕ n) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change takagiRealComplexStructure * takagiRealComplexStructureᴴ = 1
  simp [takagiRealComplexStructure, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/-- Package the explicit real complex structure with its proved unitary identity. -/
def takagiRealComplexUnitary {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.unitaryGroup (n ⊕ n) ℝ :=
  ⟨takagiRealComplexStructure, takagiRealComplexStructure_mem_unitary⟩

/-- Conjugation rotates the four literal real blocks with their necessary signs. -/
theorem takagiRealComplexUnitary_conj_blocks {n : Type*} [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n ℝ) :
    Unitary.conjStarAlgAut ℝ _ (takagiRealComplexUnitary (n := n))
      (Matrix.fromBlocks A B C D) = Matrix.fromBlocks D (-C) (-B) A := by
  simp [Unitary.conjStarAlgAut_apply, takagiRealComplexUnitary, takagiRealComplexStructure,
    Matrix.star_eq_conjTranspose, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

/-- A complex antilinear operator changes sign under real complex-structure conjugation. -/
theorem takagiRealComplexUnitary_conj_realification
    {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    Unitary.conjStarAlgAut ℝ _ (takagiRealComplexUnitary (n := n))
      (symmetricRealification X) = -symmetricRealification X := by
  simp only [symmetricRealification, takagiRealComplexUnitary_conj_blocks,
    Matrix.fromBlocks_neg, neg_neg]

/-- The exact positive real spectral part; this is a definition using pinned functional calculus. -/
def takagiPositiveRealPart {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  cfc (fun r : ℝ => max r 0) (symmetricRealification X)

/-- Functional calculus commutes with the proved real unitary conjugation. -/
theorem takagiPositiveRealPart_conj {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :
    Unitary.conjStarAlgAut ℝ _ (takagiRealComplexUnitary (n := n))
      (takagiPositiveRealPart X) =
        cfc (fun r : ℝ => max (-r) 0) (symmetricRealification X) := by
  let φ := Unitary.conjStarAlgAut ℝ _ (takagiRealComplexUnitary (n := n))
  have hT : IsSelfAdjoint (symmetricRealification X) :=
    symmetricRealification_isHermitian X hX
  have hφT : IsSelfAdjoint (φ (symmetricRealification X)) := by
    rw [show φ (symmetricRealification X) = -symmetricRealification X from
      takagiRealComplexUnitary_conj_realification X]
    exact hT.neg
  have hc := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) φ
    (fun r : ℝ => max r 0) (symmetricRealification X)
    (by fun_prop) (by
      change Continuous (fun M => φ M)
      change Continuous (fun M =>
        (takagiRealComplexUnitary (n := n) : Matrix (n ⊕ n) (n ⊕ n) ℝ) * M *
          star (takagiRealComplexUnitary (n := n) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
      fun_prop) hT hφT
  change φ (cfc (fun r : ℝ => max r 0) (symmetricRealification X)) = _
  rw [hc, show φ (symmetricRealification X) = -symmetricRealification X from
    takagiRealComplexUnitary_conj_realification X]
  exact (cfc_comp_neg (fun r : ℝ => max r 0) (symmetricRealification X)
    (by fun_prop) hT).symm

/-- The full real antilinear operator is recovered from its positive spectral part. -/
theorem takagiPositiveRealPart_difference {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :
    takagiPositiveRealPart X -
      Unitary.conjStarAlgAut ℝ _ (takagiRealComplexUnitary (n := n))
        (takagiPositiveRealPart X) = symmetricRealification X := by
  rw [takagiPositiveRealPart_conj X hX]
  unfold takagiPositiveRealPart
  rw [← cfc_sub (fun r : ℝ => max r 0) (fun r : ℝ => max (-r) 0)
    (symmetricRealification X)]
  have hf : (fun r : ℝ => max r 0 - max (-r) 0) = id := by
    funext r
    by_cases hr : 0 ≤ r
    · simp [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr)]
    · have hn : r ≤ 0 := le_of_not_ge hr
      simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
  rw [hf]
  exact cfc_id' ℝ (symmetricRealification X)
    (symmetricRealification_isHermitian X hX)

/-- Coordinate form of the pinned real spectral functional calculus. -/
theorem takagiReal_cfc_entry {m : Type*} [Fintype m] [DecidableEq m]
    (T : Matrix m m ℝ) (hT : T.IsHermitian) (f : ℝ → ℝ) (i j : m) :
    cfc f T i j = ∑ k, f (hT.eigenvalues k) *
      (hT.eigenvectorBasis k i) * (hT.eigenvectorBasis k j) := by
  rw [hT.cfc_eq]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.mul_apply, Matrix.diagonal_apply, mul_assoc, mul_left_comm, mul_comm]

/-- Recover the literal real part of X from the positive real spectral matrix. -/
theorem takagiPositiveRealPart_re {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (i j : n) :
    (X i j).re = takagiPositiveRealPart X (Sum.inl i) (Sum.inl j) -
      takagiPositiveRealPart X (Sum.inr i) (Sum.inr j) := by
  have h := congrFun (congrFun (takagiPositiveRealPart_difference X hX)
    (Sum.inl i)) (Sum.inl j)
  nth_rw 2 [← Matrix.fromBlocks_toBlocks (takagiPositiveRealPart X)] at h
  rw [takagiRealComplexUnitary_conj_blocks] at h
  simpa [symmetricRealification, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂] using h.symm

/-- Recover the literal imaginary part, including the plus sign between cross blocks. -/
theorem takagiPositiveRealPart_im {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (i j : n) :
    (X i j).im = takagiPositiveRealPart X (Sum.inl i) (Sum.inr j) +
      takagiPositiveRealPart X (Sum.inr i) (Sum.inl j) := by
  have h := congrFun (congrFun (takagiPositiveRealPart_difference X hX)
    (Sum.inl i)) (Sum.inr j)
  nth_rw 2 [← Matrix.fromBlocks_toBlocks (takagiPositiveRealPart X)] at h
  rw [takagiRealComplexUnitary_conj_blocks] at h
  simpa [symmetricRealification, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using h.symm

/-- Exact symmetric spectral reconstruction, with zero coefficients on nonpositive real eigenvalues. -/
theorem takagiPositiveRealPart_reconstruct
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) (i j : n) :
    X i j = ∑ k : n ⊕ n,
      ((max ((symmetricRealification_isHermitian X hX).eigenvalues k) 0 : ℝ) : ℂ) *
        symmetricComplexify ((symmetricRealification_isHermitian X hX).eigenvectorBasis k) i *
        symmetricComplexify ((symmetricRealification_isHermitian X hX).eigenvectorBasis k) j := by
  apply Complex.ext
  · rw [takagiPositiveRealPart_re X hX]
    simp only [takagiPositiveRealPart, takagiReal_cfc_entry _
      (symmetricRealification_isHermitian X hX), Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, symmetricComplexify, zero_mul, add_zero, sub_zero]
    rw [← Finset.sum_sub_distrib]
  · rw [takagiPositiveRealPart_im X hX]
    simp only [takagiPositiveRealPart, takagiReal_cfc_entry _
      (symmetricRealification_isHermitian X hX), Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, symmetricComplexify, zero_mul, add_zero, sub_zero]
    rw [← Finset.sum_add_distrib]

end ThreeCopyQutritWerner
