import Mathlib
import FormalResearch.QIC.GaussianNonvanishing

namespace FormalResearch.QIC

abbrev GInt := Int × Int

def giZero : GInt := (0, 0)
def giOne : GInt := (1, 0)
def giAdd (z w : GInt) : GInt := (z.1 + w.1, z.2 + w.2)
def giMul (z w : GInt) : GInt :=
  (z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1)
def giConst (c : Int) : GInt := (c, 0)

def giPow (z : GInt) : Nat → GInt
  | 0 => giOne
  | n + 1 => giMul (giPow z n) z

def giEval5 (c0 c1 c2 c3 c4 c5 : Int) (z : GInt) : GInt :=
  giAdd (giConst c0) <| giMul z <|
  giAdd (giConst c1) <| giMul z <|
  giAdd (giConst c2) <| giMul z <|
  giAdd (giConst c3) <| giMul z <|
  giAdd (giConst c4) (giMul z (giConst c5))

def giBase : GInt := (1, -1)

def reduceG (p : Nat) (z : GInt) : GMod p :=
  ((z.1 : ZMod p), (z.2 : ZMod p))

lemma reduceG_zero (p : Nat) : reduceG p giZero = gZero := by
  rfl

lemma reduceG_add (p : Nat) (z w : GInt) :
    reduceG p (giAdd z w) = gAdd (reduceG p z) (reduceG p w) := by
  ext <;> simp [reduceG, giAdd, gAdd]

lemma reduceG_mul (p : Nat) (z w : GInt) :
    reduceG p (giMul z w) = gMul (reduceG p z) (reduceG p w) := by
  ext <;> simp [reduceG, giMul, gMul]

lemma reduceG_const (p : Nat) (c : Int) :
    reduceG p (giConst c) = gConst (c : ZMod p) := by
  rfl

lemma reduceG_pow (p : Nat) (z : GInt) (n : Nat) :
    reduceG p (giPow z n) = gPow (reduceG p z) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [giPow, gPow]
      rw [reduceG_mul, ih]

lemma reduceG_eval5 (p : Nat) (c0 c1 c2 c3 c4 c5 : Int) (z : GInt) :
    reduceG p (giEval5 c0 c1 c2 c3 c4 c5 z) =
      gEval5 (c0 : ZMod p) (c1 : ZMod p) (c2 : ZMod p)
        (c3 : ZMod p) (c4 : ZMod p) (c5 : ZMod p) (reduceG p z) := by
  simp only [giEval5, gEval5]
  rw [reduceG_add, reduceG_const, reduceG_mul,
      reduceG_add, reduceG_const, reduceG_mul,
      reduceG_add, reduceG_const, reduceG_mul,
      reduceG_add, reduceG_const, reduceG_mul,
      reduceG_add, reduceG_const, reduceG_mul, reduceG_const]

lemma reduceG_base13 : reduceG 13 giBase = base13 := by rfl
lemma reduceG_base5 : reduceG 5 giBase = base5 := by rfl
lemma reduceG_base11 : reduceG 11 giBase = base11 := by rfl
lemma reduceG_base3 : reduceG 3 giBase = base3 := by rfl

/-- Characteristic-zero nonvanishing of the `q_+` factor at every Gaussian power. -/
theorem qPlus_all_powers_nonzero (L : Nat) :
    giEval5 76323 (-31772) (-68674) (-8079) 11018 2448 (giPow giBase L) ≠ giZero := by
  intro h
  have hz := congrArg (reduceG 13) h
  rw [reduceG_eval5, reduceG_pow, reduceG_base13, reduceG_zero] at hz
  exact qPlus_all_powers_nonzero_mod13 L hz

/-- Characteristic-zero nonvanishing of the `q_-` factor at every Gaussian power. -/
theorem qMinus_all_powers_nonzero (L : Nat) :
    giEval5 (-2181) 51862 (-195988) 249625 (-126366) 20304 (giPow giBase L) ≠ giZero := by
  intro h
  have hz := congrArg (reduceG 5) h
  rw [reduceG_eval5, reduceG_pow, reduceG_base5, reduceG_zero] at hz
  exact qMinus_all_powers_nonzero_mod5 L hz

/-- Characteristic-zero nonvanishing of the endpoint cubic factor. -/
theorem p3_all_powers_nonzero (L : Nat) :
    giEval5 (-3) (-1) (-3) 2 0 0 (giPow giBase L) ≠ giZero := by
  intro h
  have hz := congrArg (reduceG 11) h
  rw [reduceG_eval5, reduceG_pow, reduceG_base11, reduceG_zero] at hz
  exact p3_all_powers_nonzero_mod11 L hz

/-- Characteristic-zero nonvanishing of the endpoint quartic factor. -/
theorem p4_all_powers_nonzero (L : Nat) :
    giEval5 258 633 (-841) (-60) 144 0 (giPow giBase L) ≠ giZero := by
  intro h
  have hz := congrArg (reduceG 3) h
  rw [reduceG_eval5, reduceG_pow, reduceG_base3, reduceG_zero] at hz
  exact p4_all_powers_nonzero_mod3 L hz

end FormalResearch.QIC
