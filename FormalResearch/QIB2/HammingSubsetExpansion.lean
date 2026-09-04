import Mathlib

namespace FormalResearch.QIB2

open scoped BigOperators

/-- Exact subset expansion behind the Hamming/Bose-Mesner formula.  Each subset
`t` records the rungs on which the `b * τᵢ` term is chosen. -/
theorem hamming_subset_expansion {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (a b : R) (τ : ι → R) :
    (∏ i ∈ s, (a + b * τ i)) =
      ∑ t ∈ s.powerset,
        b ^ t.card * a ^ (s.card - t.card) * ∏ i ∈ t, τ i := by
  calc
    (∏ i ∈ s, (a + b * τ i)) =
        ∏ i ∈ s, (b * τ i + a) := by
          apply Finset.prod_congr rfl
          intro i hi
          ring
    _ = ∑ t ∈ s.powerset,
          (∏ i ∈ t, b * τ i) * ∏ i ∈ s \ t, a := by
          rw [Finset.prod_add (fun i => b * τ i) (fun _ => a) s]
    _ = ∑ t ∈ s.powerset,
          b ^ t.card * a ^ (s.card - t.card) * ∏ i ∈ t, τ i := by
          apply Finset.sum_congr rfl
          intro t ht
          have hts : t ⊆ s := Finset.mem_powerset.mp ht
          rw [Finset.prod_mul_distrib]
          simp only [Finset.prod_const, Finset.card_sdiff hts]
          ring

/-- The same identity specialized to the complete rung set `Fin d`. -/
theorem hamming_subset_expansion_fin {d : Nat} {R : Type*} [CommRing R]
    (a b : R) (τ : Fin d → R) :
    (∏ i : Fin d, (a + b * τ i)) =
      ∑ t ∈ (Finset.univ : Finset (Fin d)).powerset,
        b ^ t.card * a ^ (d - t.card) * ∏ i ∈ t, τ i := by
  simpa using hamming_subset_expansion (s := (Finset.univ : Finset (Fin d))) a b τ

end FormalResearch.QIB2
