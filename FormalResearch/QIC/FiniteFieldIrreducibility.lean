import Mathlib

namespace FormalResearch.QIC

/-- Remainder of `x^n` modulo the monic quadratic `x^2 + a*x + b`,
represented as `(constant, linear)` coefficients. -/
def powRem {p : Nat} (a b : ZMod p) : Nat → ZMod p × ZMod p
  | 0 => (1, 0)
  | n + 1 =>
      let r := powRem a b n
      (-r.2 * b, r.1 - r.2 * a)

def pairScale {p : Nat} (c : ZMod p) (r : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (c * r.1, c * r.2)

def pairAdd {p : Nat} (r s : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (r.1 + s.1, r.2 + s.2)

/-- Evaluate a degree-at-most-five coefficient list as a polynomial. -/
def eval5 {p : Nat} (c0 c1 c2 c3 c4 c5 x : ZMod p) : ZMod p :=
  c0 + c1*x + c2*x^2 + c3*x^3 + c4*x^4 + c5*x^5

/-- Remainder of a degree-at-most-five polynomial modulo `x^2+a*x+b`. -/
def rem5 {p : Nat} (c0 c1 c2 c3 c4 c5 a b : ZMod p) : ZMod p × ZMod p :=
  pairAdd (pairScale c0 (powRem a b 0)) <|
  pairAdd (pairScale c1 (powRem a b 1)) <|
  pairAdd (pairScale c2 (powRem a b 2)) <|
  pairAdd (pairScale c3 (powRem a b 3)) <|
  pairAdd (pairScale c4 (powRem a b 4))
          (pairScale c5 (powRem a b 5))

/-- The quintic `q_+` has no linear factor modulo 29. -/
theorem qPlus_no_root_mod29 :
    ∀ x : ZMod 29,
      eval5 76323 (-31772) (-68674) (-8079) 11018 2448 x ≠ 0 := by
  native_decide

/-- The quintic `q_+` has no monic quadratic factor modulo 29.  Together with
`qPlus_no_root_mod29`, this is the complete small-factor test for a degree-five polynomial. -/
theorem qPlus_no_quadratic_mod29 :
    ∀ a b : ZMod 29,
      rem5 76323 (-31772) (-68674) (-8079) 11018 2448 a b ≠ (0, 0) := by
  native_decide

/-- The quintic `q_-` has no linear factor modulo 5. -/
theorem qMinus_no_root_mod5 :
    ∀ x : ZMod 5,
      eval5 (-2181) 51862 (-195988) 249625 (-126366) 20304 x ≠ 0 := by
  native_decide

/-- The quintic `q_-` has no monic quadratic factor modulo 5. -/
theorem qMinus_no_quadratic_mod5 :
    ∀ a b : ZMod 5,
      rem5 (-2181) 51862 (-195988) 249625 (-126366) 20304 a b ≠ (0, 0) := by
  native_decide

/-- Endpoint cubic `p_3` has no root modulo 11, hence passes the complete
finite-field irreducibility test for a cubic. -/
theorem p3_no_root_mod11 :
    ∀ x : ZMod 11,
      ((2 : ZMod 11) * x^3 - 3*x^2 - x - 3) ≠ 0 := by
  native_decide

/-- Endpoint quartic `p_4` has no root modulo 5. -/
theorem p4_no_root_mod5 :
    ∀ x : ZMod 5,
      ((144 : ZMod 5) * x^4 - 60*x^3 - 841*x^2 + 633*x + 258) ≠ 0 := by
  native_decide

/-- Remainder of the endpoint quartic modulo a monic quadratic. -/
def p4Rem5 (a b : ZMod 5) : ZMod 5 × ZMod 5 :=
  pairAdd (pairScale (258 : ZMod 5) (powRem a b 0)) <|
  pairAdd (pairScale (633 : ZMod 5) (powRem a b 1)) <|
  pairAdd (pairScale (-841 : ZMod 5) (powRem a b 2)) <|
  pairAdd (pairScale (-60 : ZMod 5) (powRem a b 3))
          (pairScale (144 : ZMod 5) (powRem a b 4))

/-- Endpoint quartic `p_4` has no monic quadratic factor modulo 5.  Together
with the no-root certificate, this is the complete small-factor test for degree four. -/
theorem p4_no_quadratic_mod5 :
    ∀ a b : ZMod 5, p4Rem5 a b ≠ (0, 0) := by
  native_decide

end FormalResearch.QIC
