import Mathlib
import FormalResearch.QIB2.HammingOrbitAction
import FormalResearch.QIB2.HammingRadialGate

namespace FormalResearch.QIB2

open Complex
open scoped BigOperators

/-- Canonically weighted radial Hamming action on an integer-valued function,
viewed in `ℂ`.  The normalization is written in the same `a^d (b/a)^r` form
as the exact Krawtchouk phase theorem. -/
def splitCanonicalHammingGateApply (d m : Nat)
    (f : Finset (Fin m) → Finset (Fin (d - m)) → Int)
    (x : Finset (Fin m)) (y : Finset (Fin (d - m))) : ℂ :=
  gateA^d *
    ∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
      (gateB / gateA)^r * (splitHammingOrbitApply d m r f x y : ℂ)

/-- Full canonical gate eigenaction on the split weight-`m` Walsh character.
The separately proved Bose--Mesner eigenvalue formula and Krawtchouk phase law
combine to give exactly the phase `i^m`. -/
theorem splitCanonicalHammingGate_walsh_eigenaction
    {d m : Nat} (hm : m ≤ d)
    (x : Finset (Fin m)) (y : Finset (Fin (d - m))) :
    splitCanonicalHammingGateApply d m splitWalshCharacter x y =
      I^m * (splitWalshCharacter x y : ℂ) := by
  unfold splitCanonicalHammingGateApply
  simp_rw [splitHammingOrbit_walsh_eigenaction]
  push_cast
  calc
    gateA^d *
        (∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
          (gateB / gateA)^r *
            ((binaryKrawtchouk d m r : ℂ) *
              (splitWalshCharacter x y : ℂ))) =
      (gateA^d *
        (∑ r ∈ Finset.range ((binaryKrawtchoukGeneratingPoly d m).natDegree + 1),
          (binaryKrawtchouk d m r : ℂ) * (gateB / gateA)^r)) *
            (splitWalshCharacter x y : ℂ) := by
      simp_rw [← Finset.sum_mul]
      ring
    _ = I^m * (splitWalshCharacter x y : ℂ) := by
      rw [canonical_gate_krawtchouk_phase hm]

end FormalResearch.QIB2
