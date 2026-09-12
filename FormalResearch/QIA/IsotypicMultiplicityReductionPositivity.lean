import FormalResearch.QIA.IsotypicMultiplicityReduction
import Mathlib.Analysis.Matrix.Order

/-!
# QI-A positivity of finite isotypic multiplicity blocks

This module proves ordinary positive-semidefinite preservation for the finite
sector partial trace introduced in `IsotypicMultiplicityReduction`.

The statement is intentionally only about ordinary positivity.  It does not
assert complete positivity or CPTP semantics; those require a separate
amplification/channel argument.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- Tracing out the finite carrier coordinate in one isotypic sector preserves
positive semidefiniteness of the multiplicity block.

This is the finite-matrix positivity fact behind
`σ_a(ρ) = Tr_{V_a}(Π_a ρ Π_a)`: each fixed carrier basis coordinate contributes
a principal submatrix of `ρ`, and the partial trace is their finite sum. -/
theorem isotypicMultiplicityBlockReduction_posSemidef
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (a : α)
    {X : Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ}
    (hX : X.PosSemidef) :
    (isotypicMultiplicityBlockReduction d g a X).PosSemidef := by
  classical
  have hsum :
      (∑ k : Fin (d a),
        X.submatrix
          (fun r : Fin (g a) => (⟨⟨a, r⟩, k⟩ : isotypicDirectSumCarrier d g))
          (fun r : Fin (g a) => (⟨⟨a, r⟩, k⟩ : isotypicDirectSumCarrier d g))).PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro k hk
    exact hX.submatrix _
  have heq :
      isotypicMultiplicityBlockReduction d g a X =
        ∑ k : Fin (d a),
          X.submatrix
            (fun r : Fin (g a) => (⟨⟨a, r⟩, k⟩ : isotypicDirectSumCarrier d g))
            (fun r : Fin (g a) => (⟨⟨a, r⟩, k⟩ : isotypicDirectSumCarrier d g)) := by
    ext r s
    change
      (∑ k : Fin (d a), X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩) =
        (∑ k : Fin (d a),
          X.submatrix
            (fun r : Fin (g a) => (⟨⟨a, r⟩, k⟩ : isotypicDirectSumCarrier d g))
            (fun r : Fin (g a) => (⟨⟨a, r⟩, k⟩ : isotypicDirectSumCarrier d g))) r s
    simp
  rw [heq]
  exact hsum

end

end FormalResearch.QIA
