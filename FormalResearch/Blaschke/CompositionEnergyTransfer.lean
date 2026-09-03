import Mathlib
import FormalResearch.Blaschke.CompositionStability
import FormalResearch.Blaschke.CyclicChargeEnergy

namespace FormalResearch.Blaschke

open scoped BigOperators

/-- Gate-A composition transfer in its exact logical form.  If each factor
energy dominates its sharp baseline and a product-degree energy dominates the
weighted composition expression, then the product-degree energy satisfies the
sharp Gate-A baseline as well. -/
theorem composition_gateA_transfer
    {k m : Nat} (hk : 0 < k) (hm : 0 < m)
    {Ek Em Ekm : ℚ}
    (hEk : gateABaseline k ≤ Ek)
    (hEm : gateABaseline m ≤ Em)
    (hcomp : (k : ℚ) * Em + (1 / (m : ℚ)) * Ek ≤ Ekm) :
    gateABaseline (k * m) ≤ Ekm := by
  exact (composition_baseline_lower_bound hk hm hEk hEm).trans hcomp

/-- For the exactly solvable cyclic covers, both factor energies saturate Gate
A in every positive degree, so their weighted composition expression lands
exactly on the sharp product-degree baseline. -/
theorem cyclicCharge_energy_composition_identity
    {k m : Nat} (hk : 0 < k) (hm : 0 < m) :
    (k : ℚ) *
        (∑ j ∈ Finset.range m, (cyclicCharge m j) ^ 2) +
      (1 / (m : ℚ)) *
        (∑ j ∈ Finset.range k, (cyclicCharge k j) ^ 2) =
      gateABaseline (k * m) := by
  rw [cyclicCharge_energy hm, cyclicCharge_energy hk]
  exact composition_baseline_telescope hk hm

/-- Consequently, any product-degree energy lying above the weighted cyclic
composition expression automatically obeys the sharp Gate-A bound. -/
theorem cyclicCharge_composition_transfer
    {k m : Nat} (hk : 0 < k) (hm : 0 < m)
    {Ekm : ℚ}
    (hcomp :
      (k : ℚ) *
          (∑ j ∈ Finset.range m, (cyclicCharge m j) ^ 2) +
        (1 / (m : ℚ)) *
          (∑ j ∈ Finset.range k, (cyclicCharge k j) ^ 2) ≤ Ekm) :
    gateABaseline (k * m) ≤ Ekm := by
  rw [cyclicCharge_energy_composition_identity hk hm] at hcomp
  exact hcomp

end FormalResearch.Blaschke
