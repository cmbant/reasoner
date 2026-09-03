import Mathlib

namespace FormalResearch.QIC

abbrev Fin8 := Fin 8
abbrev Fin9 := Fin 9
abbrev P9 := Fin9 → Int

def pZero : P9 := fun _ => 0

def pOne : P9 := fun k => if k = 0 then 1 else 0

def lin (a b : Int) : P9 := fun k =>
  if k = 0 then a else if k = 1 then b else 0

def pScale (a : Int) (p : P9) : P9 := fun k => a * p k

def pMul (p q : P9) : P9 := fun k =>
  ∑ i : Fin9,
    if i.val ≤ k.val then
      p i * q ⟨k.val - i.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    else 0

def polyProd (xs : List P9) : P9 := xs.foldl pMul pOne

def inversionCount (σ : Equiv.Perm Fin8) : Nat :=
  ∑ i : Fin8, ∑ j : Fin8, if i < j ∧ σ i > σ j then 1 else 0

def permSign (σ : Equiv.Perm Fin8) : Int :=
  if inversionCount σ % 2 = 0 then 1 else -1

def rowProduct (A : Matrix Fin8 Fin8 P9) (σ : Equiv.Perm Fin8) : P9 :=
  polyProd (List.ofFn fun i : Fin8 => A i (σ i))

/-- A fully computable Leibniz determinant for 8x8 matrices whose entries are
coefficient vectors of degree at most eight. -/
def det8 (A : Matrix Fin8 Fin8 P9) : P9 :=
  ∑ σ : Equiv.Perm Fin8, pScale (permSign σ) (rowProduct A σ)

def tailPlus : Matrix Fin8 Fin8 P9 :=
  !![lin (-5) 4, lin 5 0, lin (-2) 0, lin (-14) (-16), lin 0 0, lin (-8) 4, lin 16 (-16), lin 0 0;
      lin 3 (-4), lin 1 4, lin 0 (-2), lin (-4) (-2), lin 4 (-4), lin (-4) 4, lin 0 0, lin 0 0;
      lin (-12) 8, lin 0 (-28), lin 14 14, lin (-4) (-2), lin 4 (-4), lin 12 (-12), lin (-8) 8, lin 0 0;
      lin 0 0, lin 0 0, lin 16 (-8), lin (-8) 0, lin 4 (-4), lin (-16) 8, lin (-16) 8, lin (-16) 8;
      lin 0 0, lin 8 (-4), lin 0 0, lin (-8) 0, lin 4 (-4), lin (-8) 4, lin (-20) 10, lin (-4) 2;
      lin (-4) 0, lin 4 (-4), lin 0 8, lin 6 0, lin 0 0, lin (-16) 8, lin 44 (-22), lin 12 (-6);
      lin 3 (-8), lin 1 8, lin 0 (-2), lin (-20) (-18), lin 0 0, lin 0 0, lin 18 (-18), lin 2 (-2);
      lin (-24) 16, lin 0 (-52), lin 14 22, lin (-20) (-18), lin 0 0, lin 36 (-36), lin 0 0, lin 14 4]

def tailMinus : Matrix Fin8 Fin8 P9 :=
  !![lin (-5) 4, lin (-3) 0, lin 14 0, lin 18 (-16), lin 0 0, lin 0 4, lin 16 (-16), lin (-16) 0;
      lin 3 (-4), lin (-7) 4, lin 8 (-2), lin 4 (-2), lin 4 (-4), lin (-4) 4, lin 0 0, lin 0 0;
      lin (-12) 8, lin 64 (-28), lin (-26) 14, lin 4 (-2), lin 4 (-4), lin 12 (-12), lin (-8) 8, lin 0 0;
      lin 0 0, lin 0 0, lin 48 (-24), lin 8 0, lin (-4) 4, lin 8 (-8), lin 0 (-8), lin (-48) 24;
      lin 0 0, lin 24 (-12), lin 0 0, lin 8 0, lin (-4) 4, lin 0 (-4), lin 4 (-10), lin (-12) 6;
      lin 28 (-32), lin (-108) 52, lin 16 (-8), lin (-42) 32, lin 0 0, lin (-40) 32, lin (-12) 6, lin 52 (-18);
      lin 3 (-8), lin (-7) 8, lin 24 (-2), lin 20 (-18), lin 0 0, lin 0 0, lin 18 (-18), lin (-14) (-2);
      lin (-24) 16, lin 120 (-52), lin (-26) 22, lin 20 (-18), lin 0 0, lin 36 (-36), lin 0 0, lin (-26) 4]

def qPlus : P9 := ![76323, -31772, -68674, -8079, 11018, 2448, 0, 0, 0]

def qMinus : P9 := ![-2181, 51862, -195988, 249625, -126366, 20304, 0, 0, 0]

def xMinus (a : Int) : P9 := lin (-a) 1

def rhsPlus : P9 := pScale 6144 (pMul (pMul (xMinus 2) (xMinus 1)) qPlus)

def rhsMinus : P9 := pScale (-6144) (pMul (pMul (xMinus 2) (xMinus 1)) qMinus)

/-- Exact all-qubit odd-tail determinant certificate from the compact 8x8 reduction. -/
theorem tailPlus_det : ∀ k : Fin9, det8 tailPlus k = rhsPlus k := by
  native_decide

/-- Exact all-qubit even-tail determinant certificate from the compact 8x8 reduction. -/
theorem tailMinus_det : ∀ k : Fin9, det8 tailMinus k = rhsMinus k := by
  native_decide

end FormalResearch.QIC
