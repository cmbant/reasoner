import Mathlib

namespace FormalResearch.QIC

abbrev GMod (p : Nat) := ZMod p × ZMod p

def gZero {p : Nat} : GMod p := (0, 0)
def gOne {p : Nat} : GMod p := (1, 0)
def gAdd {p : Nat} (z w : GMod p) : GMod p := (z.1 + w.1, z.2 + w.2)
def gMul {p : Nat} (z w : GMod p) : GMod p :=
  (z.1*w.1 - z.2*w.2, z.1*w.2 + z.2*w.1)
def gConst {p : Nat} (c : ZMod p) : GMod p := (c, 0)

def gPow {p : Nat} (z : GMod p) : Nat → GMod p
  | 0 => gOne
  | n + 1 => gMul (gPow z n) z

lemma gMul_one {p : Nat} (z : GMod p) : gMul z gOne = z := by
  ext <;> simp [gMul, gOne]

lemma gOne_mul {p : Nat} (z : GMod p) : gMul gOne z = z := by
  ext <;> simp [gMul, gOne]

lemma gMul_assoc {p : Nat} (x y z : GMod p) :
    gMul (gMul x y) z = gMul x (gMul y z) := by
  ext <;> simp [gMul] <;> ring

lemma gPow_add {p : Nat} (z : GMod p) (m n : Nat) :
    gPow z (m + n) = gMul (gPow z m) (gPow z n) := by
  induction n with
  | zero => simp [gPow, gMul_one]
  | succ n ih =>
      rw [Nat.add_succ, gPow, gPow, ih, gMul_assoc]

lemma gPow_period_multiple {p P : Nat} (z : GMod p)
    (hP : gPow z P = gOne) (k : Nat) :
    gPow z (P * k) = gOne := by
  induction k with
  | zero => simp [gPow]
  | succ k ih =>
      rw [Nat.mul_succ, gPow_add, ih, hP, gMul_one]

lemma gPow_mod_period {p P : Nat} (z : GMod p) (hPpos : 0 < P)
    (hP : gPow z P = gOne) (n : Nat) :
    gPow z n = gPow z (n % P) := by
  calc
    gPow z n = gPow z (n % P + P * (n / P)) := by
      rw [Nat.mod_add_div n P]
    _ = gMul (gPow z (n % P)) (gPow z (P * (n / P))) := gPow_add z _ _
    _ = gMul (gPow z (n % P)) gOne := by rw [gPow_period_multiple z hP]
    _ = gPow z (n % P) := gMul_one _

/-- Horner evaluation of a degree-at-most-five scalar polynomial on a Gaussian pair. -/
def gEval5 {p : Nat} (c0 c1 c2 c3 c4 c5 : ZMod p) (z : GMod p) : GMod p :=
  gAdd (gConst c0) <| gMul z <|
  gAdd (gConst c1) <| gMul z <|
  gAdd (gConst c2) <| gMul z <|
  gAdd (gConst c3) <| gMul z <|
  gAdd (gConst c4) (gMul z (gConst c5))

def base13 : GMod 13 := (1, -1)
def base5 : GMod 5 := (1, -1)
def base11 : GMod 11 := (1, -1)
def base3 : GMod 3 := (1, -1)

/-- `(1-i)` has period 12 modulo 13. -/
theorem base13_period : gPow base13 12 = gOne := by native_decide

/-- Every residue in the period gives a nonzero value of `q_+`. -/
theorem qPlus_period_nonzero :
    ∀ r : Fin 12,
      gEval5 76323 (-31772) (-68674) (-8079) 11018 2448
        (gPow base13 r.val) ≠ gZero := by
  native_decide

/-- Direct all-copy nonvanishing certificate for `q_+((1-i)^L)`, modulo 13. -/
theorem qPlus_all_powers_nonzero_mod13 (L : Nat) :
    gEval5 76323 (-31772) (-68674) (-8079) 11018 2448
      (gPow base13 L) ≠ gZero := by
  rw [gPow_mod_period base13 (by decide : 0 < 12) base13_period L]
  exact qPlus_period_nonzero ⟨L % 12, Nat.mod_lt _ (by decide)⟩

/-- `(1-i)` has period 4 modulo 5. -/
theorem base5_period : gPow base5 4 = gOne := by native_decide

theorem qMinus_period_nonzero :
    ∀ r : Fin 4,
      gEval5 (-2181) 51862 (-195988) 249625 (-126366) 20304
        (gPow base5 r.val) ≠ gZero := by
  native_decide

theorem qMinus_all_powers_nonzero_mod5 (L : Nat) :
    gEval5 (-2181) 51862 (-195988) 249625 (-126366) 20304
      (gPow base5 L) ≠ gZero := by
  rw [gPow_mod_period base5 (by decide : 0 < 4) base5_period L]
  exact qMinus_period_nonzero ⟨L % 4, Nat.mod_lt _ (by decide)⟩

/-- `(1-i)` has period 40 modulo 11. -/
theorem base11_period : gPow base11 40 = gOne := by native_decide

theorem p3_period_nonzero :
    ∀ r : Fin 40,
      gEval5 (-3) (-1) (-3) 2 0 0 (gPow base11 r.val) ≠ gZero := by
  native_decide

theorem p3_all_powers_nonzero_mod11 (L : Nat) :
    gEval5 (-3) (-1) (-3) 2 0 0 (gPow base11 L) ≠ gZero := by
  rw [gPow_mod_period base11 (by decide : 0 < 40) base11_period L]
  exact p3_period_nonzero ⟨L % 40, Nat.mod_lt _ (by decide)⟩

/-- `(1-i)` has period 8 modulo 3. -/
theorem base3_period : gPow base3 8 = gOne := by native_decide

theorem p4_period_nonzero :
    ∀ r : Fin 8,
      gEval5 258 633 (-841) (-60) 144 0 (gPow base3 r.val) ≠ gZero := by
  native_decide

theorem p4_all_powers_nonzero_mod3 (L : Nat) :
    gEval5 258 633 (-841) (-60) 144 0 (gPow base3 L) ≠ gZero := by
  rw [gPow_mod_period base3 (by decide : 0 < 8) base3_period L]
  exact p4_period_nonzero ⟨L % 8, Nat.mod_lt _ (by decide)⟩

end FormalResearch.QIC
