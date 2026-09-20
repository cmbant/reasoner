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

/-- Rational embedding used by the elimination certificates. -/
def endpointReducedAtRat (t : Int) : Matrix Fin14 Fin14 ℚ :=
  (endpointReducedAt t).map (Int.castRingHom ℚ)

end FormalResearch.QIC
