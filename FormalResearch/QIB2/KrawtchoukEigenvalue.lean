import Mathlib

namespace FormalResearch.QIB2

open Polynomial
open scoped BigOperators

/-- Binary Krawtchouk polynomial in the normalization used by the Hamming
orbit sums in the three-band chirality manuscript. -/
def binaryKrawtchouk (d m r : Nat) : Int :=
  ∑ l ∈ Finset.range (r + 1),
    (-1 : Int)^l * (m.choose l : Int) * ((d - m).choose (r - l) : Int)

/-- Coefficient formula for the signed binomial factor. -/
lemma coeff_one_sub_X_pow (m k : Nat) :
    ((1 - X)^m : Int[X]).coeff k = (-1 : Int)^k * (m.choose k : Int) := by
  calc
    ((1 - X)^m : Int[X]).coeff k =
        ((((1 + X)^m : Int[X]).comp (C (-1) * X)).coeff k) := by
          congr 1
          simp
          ring
    _ = ((1 + X)^m : Int[X]).coeff k * (-1 : Int)^k := by
          rw [Polynomial.comp_C_mul_X_coeff]
    _ = (-1 : Int)^k * (m.choose k : Int) := by
          rw [Polynomial.coeff_one_add_X_pow]
          ring

/-- The manuscript's closed Krawtchouk sum is exactly the coefficient of the
standard Hamming generating polynomial `(1-X)^m (1+X)^(d-m)`. -/
theorem binaryKrawtchouk_eq_coeff (d m r : Nat) :
    binaryKrawtchouk d m r =
      (((1 - X)^m * (1 + X)^(d - m) : Int[X]).coeff r) := by
  rw [binaryKrawtchouk, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  apply Finset.sum_congr rfl
  intro l hl
  rw [coeff_one_sub_X_pow, Polynomial.coeff_one_add_X_pow]
  ring

end FormalResearch.QIB2
