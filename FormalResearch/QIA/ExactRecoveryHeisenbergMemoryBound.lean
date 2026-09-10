import FormalResearch.QIA.CanonicalMemoryCarriers
import FormalResearch.QIA.PureCopyMemoryCore

/-!
# QI-A exact-recovery Heisenberg memory bridge

Source authority: `cmbant/QIprojects@d3e3d2e2a74201a178cd73ca7ef249b861c4f57e`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

Part (iii) of the manuscript's pure-copy reversible-compression theorem chooses
one orthonormal basis vector in each multiplicity block.  These give
`K_G = sum_alpha dim M_alpha` mutually perfectly distinguishable pure states.
Exact recovery implies that their encoded memory states remain perfectly
distinguishable, so a `q`-dimensional memory must satisfy `K_G <= q`.

This module formalizes a finite Heisenberg-picture version of that semantic
step.  A Schrödinger recovery map `R` is paired with a trace-adjoint pullback
`Rstar`.  If `Rstar` is positive and unital, the coordinate projectors pull
back to a memory POVM.  If recovery is exact on the coordinate projectors,
trace-adjointness makes that POVM identify the encoded states perfectly.  The
existing finite POVM trace-budget theorem then gives the Hilbert-dimension
bound.

This does not construct `Rstar` from an arbitrary CPTP map, nor prove that the
maps arise from the QI-A symmetry reduction.  Those concrete channel bridges
remain separate.  The encoded-state bound `omega <= I`, automatic for density
operators, is retained as the same explicit finite-matrix hypothesis used by
`PureCopyMemoryCore`.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Rank-one coordinate projector onto the basis vector `j`.  The definition
uses a diagonal indicator so positivity is immediate from mathlib's diagonal
PSD theorem. -/
noncomputable def coordinateProjector {J : Type*} (j : J) : Matrix J J ℂ := by
  classical
  exact Matrix.diagonal (fun i => if i = j then 1 else 0)

/-- Every coordinate projector is positive semidefinite. -/
theorem coordinateProjector_posSemidef {J : Type*} (j : J) :
    (coordinateProjector j).PosSemidef := by
  classical
  unfold coordinateProjector
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases h : i = j <;> simp [h]

/-- The complete family of coordinate projectors resolves the identity. -/
@[simp] theorem sum_coordinateProjector_eq_one
    {J : Type*} [Fintype J] :
    (∑ j : J, coordinateProjector j) = (1 : Matrix J J ℂ) := by
  classical
  ext i k
  by_cases hik : i = k
  · subst k
    simp [coordinateProjector]
  · simp [coordinateProjector, hik]

/-- Coordinate projectors are idempotent. -/
@[simp] theorem coordinateProjector_mul_self
    {J : Type*} [Fintype J] (j : J) :
    coordinateProjector j * coordinateProjector j = coordinateProjector j := by
  classical
  ext i k
  simp [coordinateProjector, Matrix.mul_apply]

/-- A rank-one coordinate projector has trace one. -/
@[simp] theorem coordinateProjector_trace
    {J : Type*} [Fintype J] (j : J) :
    Matrix.trace (coordinateProjector j) = (1 : ℂ) := by
  classical
  simp [coordinateProjector, Matrix.trace]

/-- Finite Heisenberg pullback form of the exact-recovery dimension bound.

`R` is the Schrödinger recovery map and `Rstar` its assumed trace adjoint.
Positivity and unitality of `Rstar` are exactly what is needed to pull the
coordinate-projector PVM back to a memory POVM.  Exact recovery on the encoded
coordinate states then gives unit correct-message score for every basis label.
-/
theorem exactRecoveryAdjoint_card_le_memory
    {J q : Type*} [Fintype J] [Fintype q]
    (omega : J → Matrix q q ℂ)
    (R : Matrix q q ℂ →ₗ[ℂ] Matrix J J ℂ)
    (Rstar : Matrix J J ℂ →ₗ[ℂ] Matrix q q ℂ)
    (hRstarPos : ∀ A : Matrix J J ℂ,
      A.PosSemidef → (Rstar A).PosSemidef)
    (hRstarOne : Rstar (1 : Matrix J J ℂ) = (1 : Matrix q q ℂ))
    (hadjoint : ∀ (A : Matrix J J ℂ) (X : Matrix q q ℂ),
      Matrix.trace (A * R X) = Matrix.trace (Rstar A * X))
    (hrecover : ∀ j, R (omega j) = coordinateProjector j)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  classical
  let B : J → Matrix q q ℂ := fun j => Rstar (coordinateProjector j)
  apply perfectIdentification_card_le_memory B omega
  · intro j
    exact hRstarPos (coordinateProjector j) (coordinateProjector_posSemidef j)
  · exact homega
  · change (∑ j : J, Rstar (coordinateProjector j)) = (1 : Matrix q q ℂ)
    calc
      (∑ j : J, Rstar (coordinateProjector j)) =
          Rstar (∑ j : J, coordinateProjector j) := by simp
      _ = Rstar (1 : Matrix J J ℂ) := by rw [sum_coordinateProjector_eq_one]
      _ = (1 : Matrix q q ℂ) := hRstarOne
  · intro j
    unfold sectorCodeTraceScore
    change RCLike.re
      (Matrix.trace (Rstar (coordinateProjector j) * omega j)) = 1
    rw [← hadjoint (coordinateProjector j) (omega j), hrecover j]
    rw [coordinateProjector_mul_self]
    simp

/-- QI-A multiplicity-profile specialization.  Taking one coordinate basis
state for every direct-sum multiplicity basis vector turns the generic
Heisenberg recovery bound into the manuscript quantity
`K_G = multiplicityMemoryDimension g`. -/
theorem multiplicityMemoryDimension_le_of_exactRecoveryAdjoint
    {α q : Type*} [Fintype α] [Fintype q]
    (g : α → Nat)
    (omega : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (R : Matrix q q ℂ →ₗ[ℂ]
      Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ)
    (Rstar : Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ
      →ₗ[ℂ] Matrix q q ℂ)
    (hRstarPos : ∀ A :
      Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ,
      A.PosSemidef → (Rstar A).PosSemidef)
    (hRstarOne :
      Rstar (1 : Matrix (multiplicityMemoryCarrier g)
        (multiplicityMemoryCarrier g) ℂ) = (1 : Matrix q q ℂ))
    (hadjoint : ∀
      (A : Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ)
      (X : Matrix q q ℂ),
      Matrix.trace (A * R X) = Matrix.trace (Rstar A * X))
    (hrecover : ∀ j, R (omega j) = coordinateProjector j)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ)) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  have h := exactRecoveryAdjoint_card_le_memory
    omega R Rstar hRstarPos hRstarOne hadjoint hrecover homega
  rw [multiplicityMemoryCarrier_card g] at h
  exact h

end

end FormalResearch.QIA
