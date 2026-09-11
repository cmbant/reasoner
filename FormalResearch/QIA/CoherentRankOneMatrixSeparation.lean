import FormalResearch.QIA.HilbertRealizationOperatorSeparation
import FormalResearch.QIA.HermitianInnerPairing
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Coherent rank-one matrix separation for QI-A

The Hilbert-realization separation theorem is operator-valued.  The later QI-A
memory modules are written in finite matrix coordinates and use the real
Hilbert--Schmidt pairing.  This file connects those two interfaces without
constructing the source-specific Schur/symmetric-subspace realization itself.

Given an explicit realization of algebraic symmetric power in a finite
Euclidean space, a coherent vector determines the rank-one Hermitian matrix
`|v><v|`.  Its trace pairing against a matrix is the corresponding quadratic
form.  Consequently coherent rank-one matrices separate Hermitian directions,
and hence span the full real Hermitian matrix space.
-/

namespace FormalResearch.QIA

open Matrix
open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder

noncomputable section

/-- The unnormalized rank-one matrix `|v><v|` in Euclidean coordinates. -/
def coherentRankOneMatrix
    {h : Type*} [Fintype h] (v : EuclideanSpace ℂ h) : Matrix h h ℂ :=
  Matrix.vecMulVec v (star v)

/-- A coherent rank-one matrix is Hermitian. -/
theorem coherentRankOneMatrix_isHermitian
    {h : Type*} [Fintype h] (v : EuclideanSpace ℂ h) :
    (coherentRankOneMatrix v).IsHermitian := by
  unfold coherentRankOneMatrix Matrix.IsHermitian
  rw [Matrix.conjTranspose_vecMulVec]
  simp

/-- The rank-one matrix as an element of the real Hermitian matrix space. -/
def coherentRankOneHermitian
    {h : Type*} [Fintype h] (v : EuclideanSpace ℂ h) : hermitianMatrixSpace h :=
  ⟨coherentRankOneMatrix v, (coherentRankOneMatrix_isHermitian v).isSelfAdjoint⟩

/-- Matrix trace against `|v><v|` is the Hilbert-space quadratic form. -/
theorem trace_mul_coherentRankOneMatrix
    {h : Type*} [Fintype h] [DecidableEq h]
    (A : Matrix h h ℂ) (v : EuclideanSpace ℂ h) :
    Matrix.trace (A * coherentRankOneMatrix v) =
      inner ℂ v (A.toEuclideanLin v) := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin]
  simp [coherentRankOneMatrix, Matrix.trace, Matrix.mul_apply,
    Matrix.toLin'_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, mul_assoc]

/-- Coordinate-matrix form of coherent-copy separation with complex trace
statistics.  The realization is still explicit; this theorem only identifies
the operator and matrix formulations once that realization is supplied. -/
theorem hermitianMatrix_eq_zero_of_coherent_rankOne_trace
    {E h : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype h] [DecidableEq h]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] EuclideanSpace ℂ h)
    (hreal : Continuous fun v : Fin n → E =>
      ι (SymmetricPower.tprod ℂ v))
    (A : hermitianMatrixSpace h)
    (hdiag : ∀ x : E,
      Matrix.trace
        ((A : Matrix h h ℂ) *
          coherentRankOneMatrix
            (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))) = 0) :
    A = 0 := by
  let T : EuclideanSpace ℂ h →ₗ[ℂ] EuclideanSpace ℂ h :=
    (A : Matrix h h ℂ).toEuclideanLin
  have hT : T.IsSymmetric := by
    dsimp [T]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr A.2.isHermitian
  have hTzero : T = 0 :=
    symmetricPower_hilbert_realization_operator_eq_zero_of_coherent_diagonal_of_continuous_realization
      ι T hT hreal (by
        intro x
        rw [← trace_mul_coherentRankOneMatrix]
        exact hdiag x)
  have hmat : (A : Matrix h h ℂ) = 0 := by
    apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := h) (n := h)).injective
    simpa [T] using hTzero
  exact Subtype.ext hmat

/-- For Hermitian `A`, the coherent rank-one trace statistic is real.  Thus
vanishing of its real part is already enough for coherent-copy separation. -/
theorem hermitianMatrix_eq_zero_of_coherent_rankOne_re_trace
    {E h : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype h] [DecidableEq h]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] EuclideanSpace ℂ h)
    (hreal : Continuous fun v : Fin n → E =>
      ι (SymmetricPower.tprod ℂ v))
    (A : hermitianMatrixSpace h)
    (hdiag : ∀ x : E,
      Complex.re (Matrix.trace
        ((A : Matrix h h ℂ) *
          coherentRankOneMatrix
            (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x))))) = 0) :
    A = 0 := by
  apply hermitianMatrix_eq_zero_of_coherent_rankOne_trace ι hreal A
  intro x
  let w : EuclideanSpace ℂ h :=
    ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x))
  apply Complex.ext
  · simpa [w] using hdiag x
  · rw [trace_mul_coherentRankOneMatrix]
    have hsymm : ((A : Matrix h h ℂ).toEuclideanLin).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr A.2.isHermitian
    simpa [w] using hsymm.im_inner_self_apply w

/-- The coherent rank-one Hermitian family associated to an explicit finite
Hilbert realization. -/
def coherentRankOneHermitianFamily
    {E h : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype h] {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] EuclideanSpace ℂ h) :
    Set (hermitianMatrixSpace h) :=
  Set.range fun x : E =>
    coherentRankOneHermitian
      (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))

/-- Coherent pure-state rank-one matrices span the full real Hermitian source
space, once an explicit continuous finite Hilbert realization is supplied. -/
theorem coherentRankOneHermitian_span_eq_top
    {E h : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype h] [DecidableEq h]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] EuclideanSpace ℂ h)
    (hreal : Continuous fun v : Fin n → E =>
      ι (SymmetricPower.tprod ℂ v)) :
    Submodule.span ℝ (coherentRankOneHermitianFamily ι) = ⊤ := by
  apply hermitianMatrix_span_eq_top_of_trace_separation
  intro A hA
  apply hermitianMatrix_eq_zero_of_coherent_rankOne_re_trace ι hreal A
  intro x
  apply hA
  exact ⟨x, rfl⟩

end

end FormalResearch.QIA
