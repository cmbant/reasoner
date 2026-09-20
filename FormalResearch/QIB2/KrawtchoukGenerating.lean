import Mathlib
import FormalResearch.QIB2.KrawtchoukEigenvalue

namespace FormalResearch.QIB2

open Polynomial
open scoped BigOperators

/-- Standard binary Krawtchouk generating polynomial. -/
noncomputable def binaryKrawtchoukGeneratingPoly (d m : Nat) : Int[X] :=
  (1 - X)^m * (1 + X)^(d - m)

/-- Every coefficient of the generating polynomial is the manuscript's binary
Krawtchouk eigenvalue. -/
theorem binaryKrawtchoukGeneratingPoly_coeff (d m r : Nat) :
    (binaryKrawtchoukGeneratingPoly d m).coeff r = binaryKrawtchouk d m r := by
  symm
  exact binaryKrawtchouk_eq_coeff d m r

/-- Full polynomial generating identity, obtained by assembling the already
verified coefficient formula. -/
theorem binaryKrawtchoukGeneratingPoly_expansion (d m : Nat) :
    binaryKrawtchoukGeneratingPoly d m =
      ∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
        C (binaryKrawtchouk d m r) * X^r := by
  calc
    binaryKrawtchoukGeneratingPoly d m =
        ∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
          C ((binaryKrawtchoukGeneratingPoly d m).coeff r) * X^r :=
      (binaryKrawtchoukGeneratingPoly d m).as_sum_range_C_mul_X_pow
    _ = ∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
          C (binaryKrawtchouk d m r) * X^r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [binaryKrawtchoukGeneratingPoly_coeff]

/-- Complex evaluation of the full generating identity.  This is the scalar
bridge from radial Hamming eigenvalues to a closed product expression. -/
theorem binaryKrawtchouk_generating_eval_complex (d m : Nat) (z : ℂ) :
    ∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
        (binaryKrawtchouk d m r : ℂ) * z^r =
      (1 - z)^m * (1 + z)^(d - m) := by
  calc
    (∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
        (binaryKrawtchouk d m r : ℂ) * z^r) =
      Polynomial.eval₂ (Int.castRingHom ℂ) z
        (∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
          C (binaryKrawtchouk d m r) * X^r) := by
        rw [Polynomial.eval₂_finsetSum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
        rfl
    _ = Polynomial.eval₂ (Int.castRingHom ℂ) z
        (binaryKrawtchoukGeneratingPoly d m) := by
      rw [← binaryKrawtchoukGeneratingPoly_expansion]
    _ = (1 - z)^m * (1 + z)^(d - m) := by
      simp [binaryKrawtchoukGeneratingPoly, Polynomial.eval₂_pow]

end FormalResearch.QIB2
