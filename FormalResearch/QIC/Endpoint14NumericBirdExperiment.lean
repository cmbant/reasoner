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

/-- Entrywise bridge to the original endpoint matrix. -/
theorem endpointAt_eq_t2_smul_reduced (t : Int) :
    endpointAt t = t^2 • endpointReducedAt t := by
  ext i j
  simp [endpointAt, evalP5, endpointReducedAt, evalReducedP5]
  ring

/-- Engineering experiment: can the Bird determinant tactic cheaply certify one
concrete reduced 14x14 determinant after delta-unfolding the migrated data? -/
example : Matrix.det (endpointReducedAt 3) = expectedReducedEndpointDet 3 := by
  simp only [endpointReducedAt, endpoint14, evalReducedP5, p4]
  eval_det
  norm_num [expectedReducedEndpointDet, p3Int, p4Int]

end FormalResearch.QIC
