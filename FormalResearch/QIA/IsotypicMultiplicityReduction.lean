import FormalResearch.QIA.IsotypicDirectSumAuxiliaryStates

/-!
# QI-A finite isotypic multiplicity reduction

Source authority: `cmbant/QIprojects@a3960aa4542eeed8ae785fceac78aaf8c0319031`,
`QI-A/paper/finite_copy_quantum_memory.tex`, Theorem `thm:symmetryReduction` and
Eq. `eq:sigmaalpha`.

This module realizes the manuscript's blockwise reduction

`σ_a(ρ) = Tr_{V_a}(Π_a ρ Π_a)`

on the explicit finite carrier `⊕_a (V_a ⊗ M_a)` already used by the QI-A
memory converse.  The carrier trace is taken by summing the diagonal carrier
coordinate in each sector; the resulting multiplicity blocks are assembled
with `Matrix.blockDiagonal'`.

The construction here starts *after* a physical Hilbert space has been put in
isotypic coordinates.  It therefore does not claim to construct the physical
Schur--Weyl decomposition, and it does not add a Hilbert structure to
Mathlib's algebraic `SymmetricPower`.
-/

namespace FormalResearch.QIA

open Matrix
open scoped BigOperators

noncomputable section

/-- The multiplicity block obtained by tracing out the carrier coordinate in
one isotypic sector.  This is the finite-matrix version of
`Tr_{V_a}(Π_a ρ Π_a)`. -/
def isotypicMultiplicityBlockReduction
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (a : α) :
    Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ →ₗ[ℂ]
      Matrix (Fin (g a)) (Fin (g a)) ℂ where
  toFun X r s :=
    ∑ k : Fin (d a), X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩
  map_add' X Y := by
    ext r s
    simp [Finset.sum_add_distrib]
  map_smul' c X := by
    ext r s
    simp [Finset.mul_sum]

/-- Assemble the sectorwise carrier partial traces into the manuscript's
direct-sum multiplicity state.  Off-sector multiplicity matrix entries are
zero by construction. -/
def isotypicMultiplicityReduction
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ →ₗ[ℂ]
      Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ where
  toFun X :=
    Matrix.blockDiagonal' (fun a => isotypicMultiplicityBlockReduction d g a X)
  map_add' X Y := by
    simp [Matrix.blockDiagonal'_add]
  map_smul' c X := by
    simp [Matrix.blockDiagonal'_smul]

@[simp] theorem isotypicMultiplicityReduction_sameSector_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ)
    (a : α) (r s : Fin (g a)) :
    isotypicMultiplicityReduction d g X ⟨a, r⟩ ⟨a, s⟩ =
      ∑ k : Fin (d a), X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩ := by
  simp [isotypicMultiplicityReduction, isotypicMultiplicityBlockReduction,
    Matrix.blockDiagonal'_apply]

/-- The finite isotypic multiplicity reduction preserves the total trace. -/
theorem isotypicMultiplicityReduction_trace
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ) :
    Matrix.trace (isotypicMultiplicityReduction d g X) = Matrix.trace X := by
  simp [isotypicMultiplicityReduction, isotypicMultiplicityBlockReduction,
    Matrix.trace_blockDiagonal', Matrix.trace, Fintype.sum_sigma]

/-- The existing source query projector reads exactly the corresponding
multiplicity-basis diagonal of the reduced state.  This is the basis-effect
instance of the manuscript's trace-statistics identity `eq:liftprob`. -/
theorem isotypicDirectSumQueryProjector_trace_mul_eq_reduction_diagonal
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ)
    (j : multiplicityMemoryCarrier g) :
    Matrix.trace (isotypicDirectSumQueryProjector d g j * X) =
      isotypicMultiplicityReduction d g X j j := by
  rcases j with ⟨a, r⟩
  simp [isotypicDirectSumQueryProjector, isotypicMultiplicityReduction,
    isotypicMultiplicityBlockReduction, Matrix.trace, Fintype.sum_sigma,
    Matrix.blockDiagonal'_apply]

end

end FormalResearch.QIA
