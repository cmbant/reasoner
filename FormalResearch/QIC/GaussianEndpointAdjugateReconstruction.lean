import Mathlib
import FormalResearch.QIC.GaussianEndpointNonsingular

namespace FormalResearch.QIC

/-- Exact scaled reconstruction over the Gaussian integers: applying the
adjugate after the physical endpoint matrix recovers the input vector up to
the determinant scalar.  This is the correct integral inverse statement
without any unimodularity assumption. -/
theorem endpointGaussian_adjugate_reconstruction
    {L : Nat} (v : Fin14 → GaussianInt) :
    (endpointGaussian L).adjugate *ᵥ ((endpointGaussian L) *ᵥ v) =
      Matrix.det (endpointGaussian L) • v := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
  simp

/-- For every physical tail length, the reconstruction scalar is nonzero. -/
theorem endpointGaussian_adjugate_reconstruction_nonzero
    {L : Nat} (hL : 1 ≤ L) :
    Matrix.det (endpointGaussian L) ≠ 0 ∧
      ∀ v : Fin14 → GaussianInt,
        (endpointGaussian L).adjugate *ᵥ ((endpointGaussian L) *ᵥ v) =
          Matrix.det (endpointGaussian L) • v := by
  exact ⟨endpointGaussian_det_nonzero hL,
    fun v => endpointGaussian_adjugate_reconstruction v⟩

/-- Manuscript-facing certificate: endpoint data determine a canonical
Gaussian-integer multiple of the original mode by a universal polynomial
matrix operation (the adjugate), with nonzero scaling at every physical tail. -/
theorem endpointGaussian_scaled_recovery_certificate
    {L : Nat} (hL : 1 ≤ L) (v : Fin14 → GaussianInt) :
    Matrix.det (endpointGaussian L) ≠ 0 ∧
      (endpointGaussian L).adjugate *ᵥ ((endpointGaussian L) *ᵥ v) =
        Matrix.det (endpointGaussian L) • v := by
  exact ⟨endpointGaussian_det_nonzero hL,
    endpointGaussian_adjugate_reconstruction v⟩

end FormalResearch.QIC
