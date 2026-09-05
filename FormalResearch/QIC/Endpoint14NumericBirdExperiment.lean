import Mathlib
import FormalResearch.QIC.Endpoint14Data

namespace FormalResearch.QIC

open Matrix

/-- Evaluate the endpoint coefficient triple remaining after factoring the
universal `t^2` from every entry. -/
def evalReducedP5 (p : P5) (t : Int) : Int :=
  p 2 + p 3 * t + p 4 * t^2

/-- The exact fixed 14x14 endpoint minor with the common entrywise `t^2`
factor removed. -/
def endpointReducedAt (t : Int) : Matrix Fin14 Fin14 Int :=
  fun i j => evalReducedP5 (endpoint14 i j) t

/-- Factorized reduced determinant target. -/
def expectedReducedEndpointDet (t : Int) : Int :=
  195689447424 * (t-1)^8 * (t-2)^2 * p3Int t * p4Int t

/-- In the migrated fixed minor every entry has zero constant and linear
coefficient.  This is the data fact behind the common `t^2` factor. -/
lemma endpoint14_low_coeff_zero :
    ∀ i j : Fin14, endpoint14 i j 0 = 0 ∧ endpoint14 i j 1 = 0 := by
  native_decide

/-- Entrywise bridge to the original endpoint matrix. -/
theorem endpointAt_eq_t2_smul_reduced (t : Int) :
    endpointAt t = t^2 • endpointReducedAt t := by
  ext i j
  have hz := endpoint14_low_coeff_zero i j
  simp [endpointAt, evalP5, endpointReducedAt, evalReducedP5, hz.1, hz.2]
  ring

/-- Certified rewrite from the mathematical determinant to Bird's executable
polynomial-time determinant algorithm.  This is the same correctness theorem
used internally by mathlib's `eval_det`, but it works for an arbitrary matrix
rather than requiring `!![...]` syntax. -/
theorem endpointReduced_det_eq_bird (t : Int) :
    Matrix.det (endpointReducedAt t) =
      BirdDet.birdDet 14
        (Array.ofFn fun k : Fin (14 * 14) =>
          endpointReducedAt t k.divNat k.modNat) := by
  rw [← Matrix.ofArray_ofFn (endpointReducedAt t)]
  exact BirdDet.det_eq_birdDet
    (Array.ofFn fun k : Fin (14 * 14) =>
      endpointReducedAt t k.divNat k.modNat)
    Array.size_ofFn

/-- Engineering experiment: one concrete reduced determinant, computed through
the certified Bird array algorithm rather than the Leibniz definition. -/
example : Matrix.det (endpointReducedAt 3) = expectedReducedEndpointDet 3 := by
  rw [endpointReduced_det_eq_bird]
  native_decide

end FormalResearch.QIC
