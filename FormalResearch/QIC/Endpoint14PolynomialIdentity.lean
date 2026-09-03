import Mathlib
import FormalResearch.QIC.Endpoint14Evaluation

namespace FormalResearch.QIC

open Polynomial Matrix Equiv.Perm

/-- Convert the fixed degree-at-most-four coefficient representation used by the
endpoint certificate into an ordinary integer polynomial. -/
def p5Poly (p : P5) : Int[X] :=
  C (p 0) + C (p 1) * X + C (p 2) * X^2 + C (p 3) * X^3 + C (p 4) * X^4

/-- The actual 14 x 14 endpoint minor as a matrix over `Z[t]`. -/
def endpointPoly : Matrix Fin14 Fin14 Int[X] :=
  fun i j => p5Poly (endpoint14 i j)

/-- The factorized polynomial claimed by the manuscript/exact certificate. -/
def expectedEndpointPoly : Int[X] :=
  C 195689447424 * X^28 * (X - C 1)^8 * (X - C 2)^2 *
    (2 * X^3 - 3 * X^2 - X - 3) *
    (144 * X^4 - 60 * X^3 - 841 * X^2 + 633 * X + 258)

lemma p5Poly_eval (p : P5) (t : Int) :
    Polynomial.eval t (p5Poly p) = evalP5 p t := by
  simp [p5Poly, evalP5]
  ring

lemma endpointPoly_eval_matrix (t : Int) :
    endpointPoly.map (Polynomial.evalRingHom t) = endpointAt t := by
  ext i j
  simp [endpointPoly, endpointAt, p5Poly_eval]

/-- Evaluation commutes with the determinant of the endpoint polynomial matrix. -/
theorem endpointDetPoly_eval (t : Int) :
    Polynomial.eval t (Matrix.det endpointPoly) = Matrix.det (endpointAt t) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  rw [endpointPoly_eval_matrix]

/-- Every entry of the endpoint polynomial matrix has degree at most four. -/
theorem endpointPoly_entry_natDegree_le :
    ∀ i j : Fin14, (endpointPoly i j).natDegree ≤ 4 := by
  native_decide

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
  ring

lemma expectedEndpointPoly_natDegree_le : expectedEndpointPoly.natDegree ≤ 56 := by
  native_decide

/-- The difference of the actual determinant polynomial and the factorized target
vanishes at 57 distinct integer points. -/
theorem endpointDetPoly_difference_57_roots :
    ∀ k : Fin 57,
      Polynomial.eval (k.val : Int) (Matrix.det endpointPoly - expectedEndpointPoly) = 0 := by
  intro k
  rw [Polynomial.eval_sub, endpointDetPoly_eval, expectedEndpointPoly_eval,
    endpoint_det_57_values k]
  exact sub_self _

/-- Full symbolic endpoint determinant identity.  The determinant difference has
natDegree at most 56, but has the 57 distinct roots 0,...,56, so it is zero. -/
theorem endpoint_det_polynomial_identity :
    Matrix.det endpointPoly = expectedEndpointPoly := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Matrix.det endpointPoly - expectedEndpointPoly)
    (f := fun k : Fin 57 => (k.val : Int))
  · intro a b h
    apply Fin.ext
    exact_mod_cast h
  · exact endpointDetPoly_difference_57_roots
  · have hdeg :
        (Matrix.det endpointPoly - expectedEndpointPoly).natDegree ≤ 56 :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le endpointDetPoly_natDegree_le expectedEndpointPoly_natDegree_le)
    simpa using (lt_of_le_of_lt hdeg (by decide : 56 < 57))

end FormalResearch.QIC
