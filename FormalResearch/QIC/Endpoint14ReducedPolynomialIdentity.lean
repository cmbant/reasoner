import Mathlib
import FormalResearch.QIC.Endpoint14EliminationCertificate

namespace FormalResearch.QIC

open Polynomial Matrix Equiv.Perm

/-- The degree-at-most-two polynomial obtained after removing the universal
`X^2` factor from an endpoint entry. -/
noncomputable def p5ReducedPoly (p : P5) : Int[X] :=
  C (p 2) + C (p 3) * X + C (p 4) * X^2

/-- The reduced 14 x 14 endpoint minor as a matrix over `Z[X]`. -/
noncomputable def endpointReducedPoly : Matrix Fin14 Fin14 Int[X] :=
  fun i j => p5ReducedPoly (endpoint14 i j)

/-- The degree-28 reduced determinant target. -/
noncomputable def expectedReducedEndpointPoly : Int[X] :=
  C 195689447424 * (X - C 1)^8 * (X - C 2)^2 *
    (2 * X^3 - 3 * X^2 - X - 3) *
    (144 * X^4 - 60 * X^3 - 841 * X^2 + 633 * X + 258)

lemma p5ReducedPoly_eval (p : P5) (t : Int) :
    Polynomial.eval t (p5ReducedPoly p) = evalReducedP5 p t := by
  simp [p5ReducedPoly, evalReducedP5]

lemma endpointReducedPoly_eval_matrix (t : Int) :
    endpointReducedPoly.map (Polynomial.evalRingHom t) = endpointReducedAt t := by
  ext i j
  simp [endpointReducedPoly, endpointReducedAt, p5ReducedPoly_eval]

/-- Evaluation commutes with the determinant of the reduced endpoint matrix. -/
theorem endpointReducedDetPoly_eval (t : Int) :
    Polynomial.eval t (Matrix.det endpointReducedPoly) =
      Matrix.det (endpointReducedAt t) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply,
    endpointReducedPoly_eval_matrix]

/-- Every reduced endpoint entry has degree at most two. -/
theorem endpointReducedPoly_entry_natDegree_le :
    ∀ i j : Fin14, (endpointReducedPoly i j).natDegree ≤ 2 := by
  intro i j
  unfold endpointReducedPoly p5ReducedPoly
  compute_degree!

/-- The determinant of the reduced 14 x 14 matrix has degree at most 28. -/
theorem endpointReducedDetPoly_natDegree_le :
    (Matrix.det endpointReducedPoly).natDegree ≤ 28 := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    (Equiv.Perm.sign g • ∏ i : Fin14, endpointReducedPoly (g i) i).natDegree ≤
        (∏ i : Fin14, endpointReducedPoly (g i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i : Fin14, (endpointReducedPoly (g i) i).natDegree :=
      Polynomial.natDegree_prod_le (Finset.univ : Finset Fin14)
        (fun i : Fin14 => endpointReducedPoly (g i) i)
    _ ≤ Finset.univ.card • 2 :=
      Finset.sum_le_card_nsmul _ _ 2
        (fun i _ => endpointReducedPoly_entry_natDegree_le (g i) i)
    _ = 28 := by native_decide

lemma expectedReducedEndpointPoly_eval (t : Int) :
    Polynomial.eval t expectedReducedEndpointPoly = expectedReducedEndpointDet t := by
  simp [expectedReducedEndpointPoly, expectedReducedEndpointDet, p3Int, p4Int]

lemma expectedReducedEndpointPoly_natDegree_le :
    expectedReducedEndpointPoly.natDegree ≤ 28 := by
  unfold expectedReducedEndpointPoly
  compute_degree!

/-- The determinant difference vanishes at the 29 checked interpolation samples. -/
theorem endpointReducedDetPoly_difference_samples :
    ∀ k : EndpointSampleIndex,
      Polynomial.eval (endpointSample k)
        (Matrix.det endpointReducedPoly - expectedReducedEndpointPoly) = 0 := by
  intro k
  rw [Polynomial.eval_sub, endpointReducedDetPoly_eval,
    expectedReducedEndpointPoly_eval, endpointReduced_det_at_sample k]
  exact sub_self _

/-- Reduced symbolic endpoint determinant identity.  Both sides have degree at
most 28 and agree at 29 distinct integer samples. -/
theorem endpoint_reduced_det_polynomial_identity :
    Matrix.det endpointReducedPoly = expectedReducedEndpointPoly := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Matrix.det endpointReducedPoly - expectedReducedEndpointPoly)
    (f := endpointSample)
  · exact endpointSample_injective
  · exact endpointReducedDetPoly_difference_samples
  · have hdeg :
        (Matrix.det endpointReducedPoly - expectedReducedEndpointPoly).natDegree ≤ 28 :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le endpointReducedDetPoly_natDegree_le
          expectedReducedEndpointPoly_natDegree_le)
    simpa using (lt_of_le_of_lt hdeg (by native_decide : 28 < 29))

end FormalResearch.QIC
