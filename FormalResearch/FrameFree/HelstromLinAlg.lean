import Mathlib
import FormalResearch.FrameFree.HelstromPure
import FormalResearch.FrameFree.HelstromTwirl
import FormalResearch.FrameFree.HelstromPS

/-!
# Linear-algebra lemmas for the Chernoff-side bound

Namespace `FormalResearch.FrameFree.Helstrom`.  Closed convex sets of matrices (positive semidefinite
cone), the Hilbert-Schmidt Cauchy-Schwarz inequality `hs_cs`, idempotence `projMat_mul_self` and the
trace `tr(projMat W) = dim W` (`trace_projMat`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped MatrixOrder ComplexOrder InnerProductSpace
open Matrix

namespace FormalResearch.FrameFree.Helstrom

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuous_qf (x y : ι → ℂ) : Continuous fun M : Matrix ι ι ℂ => star x ⬝ᵥ (M *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec]
  refine continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_finset_sum _ fun j _ => ?_)
  exact (continuous_id.matrix_elem i j).mul continuous_const

theorem isClosed_posSemidef : IsClosed {M : Matrix ι ι ℂ | M.PosSemidef} := by
  have : {M : Matrix ι ι ℂ | M.PosSemidef} =
      {M | Mᴴ = M} ∩ ⋂ x : ι → ℂ, {M | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => ?_)
  exact isClosed_Ici.preimage (continuous_qf x x)

theorem convex_posSemidef : Convex ℝ {M : Matrix ι ι ℂ | M.PosSemidef} := by
  have : {M : Matrix ι ι ℂ | M.PosSemidef} = Set.Ici 0 := by
    ext M; simp [Matrix.nonneg_iff_posSemidef]
  rw [this]; exact convex_Ici 0

theorem inner_toV (A B : Matrix ι ι ℂ) : inner ℂ (toV A) (toV B) = (Aᴴ * B).trace := by
  simp only [PiLp.inner_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    toV, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

/-- Hilbert-Schmidt Cauchy-Schwarz. -/
theorem hs_cs (A B : Matrix ι ι ℂ) :
    Complex.normSq (A * B).trace ≤ (Aᴴ * A).trace.re * (B * Bᴴ).trace.re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (toV Aᴴ) (toV B)
  rw [inner_toV, Matrix.conjTranspose_conjTranspose] at h
  have h2 := sq_le_sq' (by nlinarith [norm_nonneg ((A * B).trace), norm_nonneg (toV Aᴴ), norm_nonneg (toV B), mul_nonneg (norm_nonneg (toV Aᴴ)) (norm_nonneg (toV B))]) h
  rw [mul_pow, sum_norm_sq_eq, sum_norm_sq_eq, Matrix.conjTranspose_conjTranspose, Complex.sq_norm] at h2
  exact h2

theorem projMat_mul_self (W : Submodule ℂ (EuclideanSpace ℂ ι)) : projMat W * projMat W = projMat W := by
  have : ∀ v, (projMat W * projMat W) *ᵥ v = projMat W *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec]
    exact projMat_mulVec_of_mem W (toLp_projMat_mulVec_mem W v)
  exact Matrix.ext_iff_mulVec.mpr this

theorem trace_projMat (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    (projMat W).trace = (Module.finrank ℂ W : ℂ) := by
  have h : LinearMap.IsProj W (W.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
    exact ⟨fun x => Submodule.starProjection_apply_mem W x,
      fun x hx => Submodule.starProjection_eq_self_iff.2 hx⟩
  have h1 := h.trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun ι ℂ).toBasis] at h1
  rw [← h1]
  have : (W.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) = Matrix.toEuclideanLin (projMat W) := by
    simp [projMat]
  rw [this, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

end FormalResearch.FrameFree.Helstrom
