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
    change
      (∑ k : Fin (d a),
        (X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩ +
          Y ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩)) =
        (∑ k : Fin (d a), X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩) +
          ∑ k : Fin (d a), Y ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩
    exact Finset.sum_add_distrib
  map_smul' c X := by
    ext r s
    change
      (∑ k : Fin (d a), c * X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩) =
        c * ∑ k : Fin (d a), X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩
    rw [Finset.mul_sum]

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
    change
      Matrix.blockDiagonal'
          (fun a => isotypicMultiplicityBlockReduction d g a (X + Y)) =
        Matrix.blockDiagonal'
            (fun a => isotypicMultiplicityBlockReduction d g a X) +
          Matrix.blockDiagonal'
            (fun a => isotypicMultiplicityBlockReduction d g a Y)
    rw [← Matrix.blockDiagonal'_add]
    congr 1
    funext a
    exact (isotypicMultiplicityBlockReduction d g a).map_add X Y
  map_smul' c X := by
    change
      Matrix.blockDiagonal'
          (fun a => isotypicMultiplicityBlockReduction d g a (c • X)) =
        c • Matrix.blockDiagonal'
          (fun a => isotypicMultiplicityBlockReduction d g a X)
    rw [← Matrix.blockDiagonal'_smul]
    congr 1
    funext a
    exact (isotypicMultiplicityBlockReduction d g a).map_smul c X

@[simp] theorem isotypicMultiplicityReduction_sameSector_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ)
    (a : α) (r s : Fin (g a)) :
    isotypicMultiplicityReduction d g X ⟨a, r⟩ ⟨a, s⟩ =
      ∑ k : Fin (d a), X ⟨⟨a, r⟩, k⟩ ⟨⟨a, s⟩, k⟩ := by
  change
    Matrix.blockDiagonal'
        (fun b => isotypicMultiplicityBlockReduction d g b X)
        ⟨a, r⟩ ⟨a, s⟩ = _
  rw [Matrix.blockDiagonal'_apply_eq]
  rfl

/-- The finite isotypic multiplicity reduction preserves the total trace. -/
theorem isotypicMultiplicityReduction_trace
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    (X : Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ) :
    Matrix.trace (isotypicMultiplicityReduction d g X) = Matrix.trace X := by
  calc
    Matrix.trace (isotypicMultiplicityReduction d g X) =
        ∑ a : α, Matrix.trace (isotypicMultiplicityBlockReduction d g a X) := by
      change
        Matrix.trace
            (Matrix.blockDiagonal'
              (fun a => isotypicMultiplicityBlockReduction d g a X)) = _
      rw [Matrix.trace_blockDiagonal']
    _ = ∑ a : α, ∑ r : Fin (g a), ∑ k : Fin (d a),
        X ⟨⟨a, r⟩, k⟩ ⟨⟨a, r⟩, k⟩ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Matrix.trace]
      apply Finset.sum_congr rfl
      intro r hr
      rfl
    _ = Matrix.trace X := by
      rw [Matrix.trace, Fintype.sum_sigma, Fintype.sum_sigma]
      simp only [Matrix.diag_apply]

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
  calc
    Matrix.trace (isotypicDirectSumQueryProjector d g j * X) =
        ∑ x : multiplicityMemoryCarrier g,
          ∑ k : Fin (d x.1),
            if x = j then X ⟨x, k⟩ ⟨x, k⟩ else 0 := by
      rw [isotypicDirectSumQueryProjector, Matrix.trace, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro k hk
      simp
    _ = ∑ k : Fin (d j.1), X ⟨j, k⟩ ⟨j, k⟩ := by simp
    _ = isotypicMultiplicityReduction d g X j j := by
      rcases j with ⟨a, r⟩
      exact (isotypicMultiplicityReduction_sameSector_apply d g X a r r).symm

end

end FormalResearch.QIA
