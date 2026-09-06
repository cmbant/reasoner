import Mathlib
import FormalResearch.QIC.Endpoint14ReducedPolynomialIdentity

namespace FormalResearch.QIC

open Polynomial Matrix Equiv.Perm

/-- Convert the fixed degree-at-most-four coefficient representation used by the
endpoint certificate into an ordinary integer polynomial. -/
noncomputable def p5Poly (p : P5) : Int[X] :=
  C (p 0) + C (p 1) * X + C (p 2) * X^2 + C (p 3) * X^3 + C (p 4) * X^4

/-- The actual 14 x 14 endpoint minor as a matrix over `Z[t]`. -/
noncomputable def endpointPoly : Matrix Fin14 Fin14 Int[X] :=
  fun i j => p5Poly (endpoint14 i j)

/-- The factorized polynomial claimed by the manuscript/exact certificate. -/
noncomputable def expectedEndpointPoly : Int[X] :=
  C 195689447424 * X^28 * (X - C 1)^8 * (X - C 2)^2 *
    (2 * X^3 - 3 * X^2 - X - 3) *
    (144 * X^4 - 60 * X^3 - 841 * X^2 + 633 * X + 258)

lemma p5Poly_eval (p : P5) (t : Int) :
    Polynomial.eval t (p5Poly p) = evalP5 p t := by
  simp [p5Poly, evalP5]

lemma endpointPoly_eval_matrix (t : Int) :
    endpointPoly.map (Polynomial.evalRingHom t) = endpointAt t := by
  ext i j
  simp [endpointPoly, endpointAt, p5Poly_eval]

/-- Evaluation commutes with the determinant of the endpoint polynomial matrix. -/
theorem endpointDetPoly_eval (t : Int) :
    Polynomial.eval t (Matrix.det endpointPoly) = Matrix.det (endpointAt t) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply,
    endpointPoly_eval_matrix]

/-- Every entry of the endpoint polynomial matrix has degree at most four. -/
theorem endpointPoly_entry_natDegree_le :
    ∀ i j : Fin14, (endpointPoly i j).natDegree ≤ 4 := by
  intro i j
  unfold endpointPoly p5Poly
  compute_degree!

/-- The 14 x 14 determinant has degree at most 14*4 = 56. -/
theorem endpointDetPoly_natDegree_le :
    (Matrix.det endpointPoly).natDegree ≤ 56 := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    (Equiv.Perm.sign g • ∏ i : Fin14, endpointPoly (g i) i).natDegree ≤
        (∏ i : Fin14, endpointPoly (g i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i : Fin14, (endpointPoly (g i) i).natDegree :=
      Polynomial.natDegree_prod_le (Finset.univ : Finset Fin14)
        (fun i : Fin14 => endpointPoly (g i) i)
    _ ≤ Finset.univ.card • 4 :=
      Finset.sum_le_card_nsmul _ _ 4 (fun i _ => endpointPoly_entry_natDegree_le (g i) i)
    _ = 56 := by native_decide

lemma expectedEndpointPoly_eval (t : Int) :
    Polynomial.eval t expectedEndpointPoly = expectedEndpointDet t := by
  simp [expectedEndpointPoly, expectedEndpointDet, p3Int, p4Int]

lemma expectedEndpointPoly_natDegree_le : expectedEndpointPoly.natDegree ≤ 56 := by
  unfold expectedEndpointPoly
  compute_degree!

/-- Polynomial-level form of the universal entrywise `X^2` factor. -/
theorem endpointPoly_eq_X2_smul_reduced :
    endpointPoly = (X^2 : Int[X]) • endpointReducedPoly := by
  ext i j
  have hz := endpoint14_low_coeff_zero i j
  simp [endpointPoly, p5Poly, endpointReducedPoly, p5ReducedPoly, hz.1, hz.2] <;> ring

lemma expectedEndpointPoly_eq_X28_mul_reduced :
    expectedEndpointPoly = X^28 * expectedReducedEndpointPoly := by
  unfold expectedEndpointPoly expectedReducedEndpointPoly
  ring

/-- Full symbolic endpoint determinant identity, now obtained from the checked
reduced degree-28 interpolation identity and the universal `X^2` entry factor. -/
theorem endpoint_det_polynomial_identity :
    Matrix.det endpointPoly = expectedEndpointPoly := by
  rw [endpointPoly_eq_X2_smul_reduced, Matrix.det_smul,
    endpoint_reduced_det_polynomial_identity]
  rw [show Fintype.card Fin14 = 14 by native_decide]
  rw [expectedEndpointPoly_eq_X28_mul_reduced]
  ring

/-- Compatibility form of the old 57-root statement.  The roots now follow
from the symbolic identity rather than serving as its proof. -/
theorem endpointDetPoly_difference_57_roots :
    ∀ k : Fin 57,
      Polynomial.eval (k.val : Int) (Matrix.det endpointPoly - expectedEndpointPoly) = 0 := by
  intro k
  rw [endpoint_det_polynomial_identity]
  simp

end FormalResearch.QIC
