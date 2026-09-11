import Mathlib.Analysis.Matrix.Order

/-!
# QI-A normalized positive matrices are bounded by identity

A positive-semidefinite complex matrix of trace one is automatically bounded
above by the identity in the matrix Loewner order.  This finite-dimensional
fact is the missing state-side bridge needed to derive the encoded-state effect
bound used by the deferred-query converse from ordinary density-matrix
hypotheses.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- A positive-semidefinite complex matrix with unit trace is bounded above by
identity. -/
theorem posSemidef_le_one_of_trace_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ}
    (hA : A.PosSemidef)
    (htrace : Matrix.trace A = 1) :
    A ≤ (1 : Matrix n n ℂ) := by
  classical
  rw [Matrix.le_iff]
  let hH : A.IsHermitian := hA.isHermitian
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have h := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simpa [htrace] using h
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hdiag :
      Matrix.diagonal (fun i => ((1 - hH.eigenvalues i : ℝ) : ℂ)) =
        (1 : Matrix n n ℂ) -
          Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply, hij]
  have hD :
      (Matrix.diagonal (fun i => ((1 - hH.eigenvalues i : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast sub_nonneg.mpr (hle i)
  rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hconj := hD.mul_mul_conjTranspose_same
    (hH.eigenvectorUnitary : Matrix n n ℂ)
  rw [hdiag] at hconj
  simpa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] using hconj

end

end FormalResearch.QIA
