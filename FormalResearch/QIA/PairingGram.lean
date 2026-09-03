import Mathlib

namespace FormalResearch.QIA

abbrev Bits4 := Fin 4 → Bool

def v1Coeff (x : Bits4) : Int :=
  if x 0 = x 1 ∧ x 2 = x 3 then 1 else 0

def v2Coeff (x : Bits4) : Int :=
  if x 0 = x 2 ∧ x 1 = x 3 then 1 else 0

def v3Coeff (x : Bits4) : Int :=
  if x 0 = x 3 ∧ x 1 = x 2 then 1 else 0

def finiteDot (f g : Bits4 → Int) : Int :=
  ∑ x : Bits4, f x * g x

/-- Exact Gram data for the three pairing tensors used to build the invariant qutrit. -/
theorem pairing_gram :
    finiteDot v1Coeff v1Coeff = 4 ∧
    finiteDot v2Coeff v2Coeff = 4 ∧
    finiteDot v3Coeff v3Coeff = 4 ∧
    finiteDot v1Coeff v2Coeff = 2 ∧
    finiteDot v1Coeff v3Coeff = 2 ∧
    finiteDot v2Coeff v3Coeff = 2 := by
  native_decide

end FormalResearch.QIA
