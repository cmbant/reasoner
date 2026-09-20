import Mathlib
import FormalResearch.Bridges.B2BlaschkeWalshGauge

namespace FormalResearch.Bridges

open Complex
open scoped BigOperators

/-- Rewriting the canonical B2 Boolean-cube gate in the Blaschke Walsh
convention multiplies the usual `i^|T|` eigenphase by the gauge
`(-1)^|T|`. -/
theorem canonical_gate_blaschke_walsh_gauge_phase {d : Nat}
    (T : Finset (Fin d)) :
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      QIB2.gateB ^ S.card * QIB2.gateA ^ (d - S.card) *
        (Blaschke.walshCharacter T S : ℂ)) =
      (-1 : ℂ) ^ T.card * I ^ T.card := by
  simp_rw [blaschkeWalshCharacter_cast_eq_gauge_mul_qib2]
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      QIB2.gateB ^ S.card * QIB2.gateA ^ (d - S.card) *
        ((-1 : ℂ) ^ T.card * QIB2.booleanWalshCharacter T S)) =
      (-1 : ℂ) ^ T.card *
        (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          QIB2.gateB ^ S.card * QIB2.gateA ^ (d - S.card) *
            QIB2.booleanWalshCharacter T S) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro S hS
              ring
    _ = (-1 : ℂ) ^ T.card * I ^ T.card := by
      rw [QIB2.canonical_gate_boolean_cube_phase]

/-- Compact transferred spectral law: in the Blaschke sign convention the
same canonical Hamming gate has phase `(-i)^|T|`. -/
theorem canonical_gate_blaschke_walsh_phase {d : Nat}
    (T : Finset (Fin d)) :
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      QIB2.gateB ^ S.card * QIB2.gateA ^ (d - S.card) *
        (Blaschke.walshCharacter T S : ℂ)) =
      (-I) ^ T.card := by
  rw [canonical_gate_blaschke_walsh_gauge_phase]
  rw [show (-I : ℂ) = (-1 : ℂ) * I by ring, mul_pow]

end FormalResearch.Bridges
