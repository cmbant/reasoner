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

/-- Integer Gram--Schmidt combinations. These avoid introducing square roots while
checking the normalization structure behind the orthonormal invariant-qutrit basis. -/
def u1Coeff (x : Bits4) : Int := v1Coeff x

def u2Coeff (x : Bits4) : Int := 2 * v2Coeff x - v1Coeff x

def u3Coeff (x : Bits4) : Int := 3 * v3Coeff x - v1Coeff x - v2Coeff x

/-- The integer orthogonalization has squared norms 4, 12, and 24.
After division by 2, 2*sqrt(3), and 2*sqrt(6), respectively, this is the
standard normalized basis used in the four-qubit chirality calculation. -/
theorem pairing_integer_orthogonalization :
    finiteDot u1Coeff u1Coeff = 4 ∧
    finiteDot u2Coeff u2Coeff = 12 ∧
    finiteDot u3Coeff u3Coeff = 24 ∧
    finiteDot u1Coeff u2Coeff = 0 ∧
    finiteDot u1Coeff u3Coeff = 0 ∧
    finiteDot u2Coeff u3Coeff = 0 := by
  native_decide

end FormalResearch.QIA
