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
  rw [← hEll, ← hN]
  rw [sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Consequently the universal coefficient multiplying vertex disagreement is
`Nplus - ell = Σ e_m (m-1)`. -/
theorem vertex_weight_eq {ι : Type*} [Fintype ι]
    (e m : ι → Nat) (ell Nplus : Int)
    (hEll : (∑ i : ι, (e i : Int)) = ell)
    (hN : (∑ i : ι, (e i : Int) * (m i : Int)) = Nplus) :
    (∑ i : ι, (e i : Int) * ((m i : Int) - 1)) = Nplus - ell := by
  rw [← hEll, ← hN, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end FormalResearch.Gaudin
