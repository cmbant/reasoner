import Mathlib
import FormalResearch.QIC.GaussianEndpointNonsingular

namespace FormalResearch.QIC

/-- Nonsingularity of the physical endpoint determinant gives injectivity of
the actual Gaussian-integer endpoint matrix action for every positive tail. -/
theorem endpointGaussian_mulVec_injective {L : Nat} (hL : 1 ≤ L) :
    Function.Injective (endpointGaussian L).mulVec :=
  Matrix.mulVec_injective_of_det_ne_zero (endpointGaussian_det_nonzero hL)

/-- Equivalently, the endpoint linear map has trivial kernel. -/
theorem endpointGaussian_ker_eq_bot {L : Nat} (hL : 1 ≤ L) :
    LinearMap.ker (endpointGaussian L).mulVecLin = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  exact endpointGaussian_mulVec_injective hL

/-- Manuscript-facing endpoint certificate: no nonzero endpoint mode survives
in the kernel at any physical tail length. -/
theorem endpointGaussian_no_kernel {L : Nat} (hL : 1 ≤ L)
    (v : Fin14 → GaussianInt)
    (hv : (endpointGaussian L).mulVec v = 0) :
    v = 0 := by
  exact endpointGaussian_mulVec_injective hL (by simpa using hv)

end FormalResearch.QIC
