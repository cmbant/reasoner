import Mathlib
import FormalResearch.QIC.GaussianEndpointNonsingular

namespace FormalResearch.QIC

/-- The physical 14x14 endpoint matrix has full matrix rank over the Gaussian
integers for every positive tail length. -/
theorem endpointGaussian_rank {L : Nat} (hL : 1 ≤ L) :
    (endpointGaussian L).rank = 14 := by
  simpa [Fin14] using
    (Matrix.rank_of_det_ne_zero (A := endpointGaussian L)
      (endpointGaussian_det_nonzero hL))

/-- Compact endpoint certificate exposing both nonsingularity and the exact
full-rank statement used in the copy-complexity argument. -/
theorem endpointGaussian_full_rank_certificate {L : Nat} (hL : 1 ≤ L) :
    Matrix.det (endpointGaussian L) ≠ 0 ∧ (endpointGaussian L).rank = 14 := by
  exact ⟨endpointGaussian_det_nonzero hL, endpointGaussian_rank hL⟩

end FormalResearch.QIC
