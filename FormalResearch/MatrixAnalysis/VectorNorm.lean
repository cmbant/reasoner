module

public import Mathlib

/-!
# The squared Euclidean norm of a vector in `ι → ℂ`

`normSqVec v = Re (v† v) = ∑ᵢ |vᵢ|²`, with its basic facts and its relation to the norm of `EuclideanSpace ℂ ι`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix
open scoped ComplexOrder

noncomputable section

section
variable {ι : Type*} [Fintype ι]


/-- The squared Euclidean norm of a vector, as `Re (v† v)`. -/
def normSqVec (v : ι → ℂ) : ℝ := (star v ⬝ᵥ v).re

theorem normSqVec_eq_sum {ι : Type*} [Fintype ι] (v : ι → ℂ) : normSqVec v = ∑ i, Complex.normSq (v i) := by
  unfold normSqVec
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.normSq_apply,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem normSqVec_nonneg (v : ι → ℂ) : 0 ≤ normSqVec v := by
  unfold normSqVec
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  simp [Complex.mul_re]
  nlinarith [sq_nonneg (v i).re, sq_nonneg (v i).im]

theorem eq_zero_of_normSqVec_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℂ} (h : normSqVec v = 0) : v = 0 := by
  rw [normSqVec_eq_sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).1 h
  ext i
  simpa using this i (Finset.mem_univ i)

theorem normSqVec_real_smul {ι : Type*} [Fintype ι] (s : ℝ) (v : ι → ℂ) :
    normSqVec ((s : ℂ) • v) = s ^ 2 * normSqVec v := by
  simp only [normSqVec_eq_sum, Pi.smul_apply, smul_eq_mul, map_mul, Complex.normSq_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem star_dotProduct_self_real' {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    star a ⬝ᵥ a = ((normSqVec a : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [dotProduct, Complex.im_sum, Pi.star_apply, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    refine Finset.sum_eq_zero fun i _ => ?_
    ring

end

section Euclidean
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι]


theorem normSqVec_eq_norm_sq (x : EuclideanSpace ℂ ι) : normSqVec x.ofLp = ‖x‖ ^ 2 := by
  have h := @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ x
  have h2 : (inner ℂ x x : ℂ) = star x.ofLp ⬝ᵥ x.ofLp := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  unfold normSqVec
  rw [← h2, h]
  simp [← Complex.ofReal_pow]

end Euclidean

end

end FormalResearch.MatrixAnalysis
