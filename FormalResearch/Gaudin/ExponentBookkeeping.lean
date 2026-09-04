import Mathlib

namespace FormalResearch.Gaudin

open scoped BigOperators

/-- Pure algebra behind the passage from the exponentwise Gaudin rank formula
to the weighted tree-disagreement formula.  Here `e i` is the multiplicity of
an exponent `m i`, `ell = Σ eᵢ`, and `Nplus = Σ mᵢ eᵢ`. -/
theorem exponentwise_rank_sum {ι : Type*} [Fintype ι]
    (e m : ι → Nat) (ell Nplus A B : Int)
    (hEll : (∑ i : ι, (e i : Int)) = ell)
    (hN : (∑ i : ι, (e i : Int) * (m i : Int)) = Nplus) :
    (∑ i : ι, (e i : Int) * (A + ((m i : Int) - 1) * B)) =
      ell * A + (Nplus - ell) * B := by
  calc
    (∑ i : ι, (e i : Int) * (A + ((m i : Int) - 1) * B))
        = A * (∑ i : ι, (e i : Int)) +
            B * ((∑ i : ι, (e i : Int) * (m i : Int)) -
              (∑ i : ι, (e i : Int))) := by
                simp_rw [mul_add, sub_mul, mul_sub, one_mul]
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                ring
    _ = A * ell + B * (Nplus - ell) := by rw [hEll, hN]
    _ = ell * A + (Nplus - ell) * B := by ring

/-- Consequently the universal coefficient multiplying vertex disagreement is
`Nplus - ell = Σ e_m (m-1)`. -/
theorem vertex_weight_eq {ι : Type*} [Fintype ι]
    (e m : ι → Nat) (ell Nplus : Int)
    (hEll : (∑ i : ι, (e i : Int)) = ell)
    (hN : (∑ i : ι, (e i : Int) * (m i : Int)) = Nplus) :
    (∑ i : ι, (e i : Int) * ((m i : Int) - 1)) = Nplus - ell := by
  calc
    (∑ i : ι, (e i : Int) * ((m i : Int) - 1)) =
        (∑ i : ι, (e i : Int) * (m i : Int)) -
          (∑ i : ι, (e i : Int)) := by
            simp_rw [mul_sub, mul_one]
            rw [Finset.sum_sub_distrib]
    _ = Nplus - ell := by rw [hN, hEll]

end FormalResearch.Gaudin
