import Mathlib
import FormalResearch.Blaschke.CompositionBaseline

namespace FormalResearch.Blaschke

/-- Arithmetic composition-stability principle behind Gate A.  If two factor
energies dominate their sharp degree baselines, then the weighted composition
lower bound dominates the sharp baseline at the product degree.  This theorem
uses only the exact baseline telescope and does not assume Gate A in any new
degree. -/
theorem composition_baseline_lower_bound
    {k m : Nat} (hk : 0 < k) (hm : 0 < m)
    {Ek Em : ℚ}
    (hEk : gateABaseline k ≤ Ek)
    (hEm : gateABaseline m ≤ Em) :
    gateABaseline (k * m) ≤
      (k : ℚ) * Em + (1 / (m : ℚ)) * Ek := by
  rw [← composition_baseline_telescope hk hm]
  have hkq : (0 : ℚ) ≤ (k : ℚ) := by positivity
  have hmq : (0 : ℚ) ≤ 1 / (m : ℚ) := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left hEm hkq)
    (mul_le_mul_of_nonneg_left hEk hmq)

/-- Equality propagates exactly through the composition lower-bound expression
when both factors saturate their Gate-A baselines. -/
theorem composition_baseline_equality_propagates
    {k m : Nat} (hk : 0 < k) (hm : 0 < m)
    {Ek Em : ℚ}
    (hEk : Ek = gateABaseline k)
    (hEm : Em = gateABaseline m) :
    (k : ℚ) * Em + (1 / (m : ℚ)) * Ek = gateABaseline (k * m) := by
  rw [hEk, hEm]
  exact composition_baseline_telescope hk hm

/-- Compact stability certificate: lower bounds propagate under the weighted
composition expression, and exact saturation propagates when both factors are
sharp. -/
theorem composition_baseline_stability_certificate
    {k m : Nat} (hk : 0 < k) (hm : 0 < m)
    {Ek Em : ℚ}
    (hEk : gateABaseline k ≤ Ek)
    (hEm : gateABaseline m ≤ Em) :
    gateABaseline (k * m) ≤
      (k : ℚ) * Em + (1 / (m : ℚ)) * Ek :=
  composition_baseline_lower_bound hk hm hEk hEm

end FormalResearch.Blaschke
