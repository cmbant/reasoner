import Mathlib
import FormalResearch.QIB2.HammingBooleanCubePhase

namespace FormalResearch.QIB2

open Complex
open scoped BigOperators

/-- Boolean Walsh labels of fixed Hamming weight `m`. -/
abbrev WalshWeightIndex (d m : Nat) :=
  {T : Finset (Fin d) // T.card = m}

/-- The weight-`m` Walsh sector has the expected binomial multiplicity. -/
theorem card_WalshWeightIndex (d m : Nat) :
    Fintype.card (WalshWeightIndex d m) = d.choose m := by
  simp [WalshWeightIndex, Fintype.card_finset_len, Fintype.card_fin]

/-- Every Walsh label in the weight-`m` sector has the same canonical Hamming
phase `i^m` in the full Boolean-cube subset expansion. -/
theorem canonical_gate_weight_sector_phase {d m : Nat}
    (T : WalshWeightIndex d m) :
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      gateB ^ S.card * gateA ^ (d - S.card) * booleanWalshCharacter T.1 S) =
      I ^ m := by
  rw [canonical_gate_boolean_cube_phase T.1, T.2]

/-- Compact spectral multiplicity certificate: the phase `i^m` occurs on all
`choose d m` Walsh labels of weight `m`. -/
theorem canonical_gate_weight_sector_certificate (d m : Nat) :
    Fintype.card (WalshWeightIndex d m) = d.choose m ∧
      ∀ T : WalshWeightIndex d m,
        (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          gateB ^ S.card * gateA ^ (d - S.card) * booleanWalshCharacter T.1 S) =
          I ^ m := by
  exact ⟨card_WalshWeightIndex d m,
    fun T => canonical_gate_weight_sector_phase T⟩

end FormalResearch.QIB2
