import FormalResearch.QIA.CanonicalMemoryCarriers
import FormalResearch.QIA.IsotypicAuxiliaryStates

/-!
# QI-A direct-sum isotypic auxiliary states

The manuscript's deferred-query converse uses one auxiliary state for every
multiplicity basis vector across all isotypic sectors.  This module packages
those witnesses into one finite matrix space while allowing the irreducible
carrier dimension to vary with the sector.

For sector dimensions `d a` and multiplicities `g a`, a source basis vector is
represented by a multiplicity-memory label `j = (a,r)` together with a carrier
coordinate in `Fin (d a)`.  The source query projector for `j` is the diagonal
projector onto all carrier coordinates above that multiplicity label, and the
auxiliary state is its normalization by `d a`.

This is a concrete finite direct-sum matrix model.  It still does not construct
the physical Schur--Weyl decomposition or identify the physical symmetric-copy
Hilbert space with this carrier.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Finite basis carrier for `⊕_a (V_a ⊗ M_a)` when `d a = dim V_a` and
`g a = dim M_a`.  We index first by a multiplicity basis label and then by a
carrier coordinate. -/
abbrev isotypicDirectSumCarrier
    {α : Type*} [Fintype α] (d g : α → Nat) : Type _ :=
  Σ j : multiplicityMemoryCarrier g, Fin (d j.1)

instance isotypicDirectSumCarrierFintype
    {α : Type*} [Fintype α] (d g : α → Nat) :
    Fintype (isotypicDirectSumCarrier d g) := inferInstance

instance isotypicDirectSumCarrierDecidableEq
    {α : Type*} [Fintype α] [DecidableEq α] (d g : α → Nat) :
    DecidableEq (isotypicDirectSumCarrier d g) := inferInstance

/-- Source query projector attached to one multiplicity basis label.  It is
identity on the corresponding irreducible carrier and zero elsewhere. -/
def isotypicDirectSumQueryProjector
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ :=
  Matrix.diagonal fun x => if x.1 = j then 1 else 0

@[simp] theorem isotypicDirectSumQueryProjector_trace
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    Matrix.trace (isotypicDirectSumQueryProjector d g j) = (d j.1 : ℂ) := by
  classical
  rw [isotypicDirectSumQueryProjector, Matrix.trace_diagonal, Fintype.sum_sigma]
  calc
    (∑ x : multiplicityMemoryCarrier g,
        ∑ _k : Fin (d x.1), (if x = j then 1 else 0 : ℂ)) =
        ∑ x : multiplicityMemoryCarrier g,
          if x = j then (d x.1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x = j <;> simp [h]
    _ = (d j.1 : ℂ) := by simp

@[simp] theorem isotypicDirectSumQueryProjector_mul_self
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    isotypicDirectSumQueryProjector d g j *
        isotypicDirectSumQueryProjector d g j =
      isotypicDirectSumQueryProjector d g j := by
  rw [isotypicDirectSumQueryProjector, Matrix.diagonal_mul_diagonal]
  congr
  funext x
  by_cases h : x.1 = j <;> simp [h]

theorem isotypicDirectSumQueryProjector_posSemidef
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    (isotypicDirectSumQueryProjector d g j).PosSemidef := by
  rw [isotypicDirectSumQueryProjector, Matrix.posSemidef_diagonal_iff]
  intro x
  by_cases h : x.1 = j <;> simp [h]

theorem isotypicDirectSumQueryProjector_isSelfAdjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    IsSelfAdjoint (isotypicDirectSumQueryProjector d g j) :=
  (isotypicDirectSumQueryProjector_posSemidef d g j).isHermitian.isSelfAdjoint

/-- The projectors over all multiplicity basis labels form a sharp PVM on the
whole direct-sum source carrier. -/
theorem isotypicDirectSumQueryProjector_sum_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    (∑ j : multiplicityMemoryCarrier g,
        isotypicDirectSumQueryProjector d g j) =
      (1 : Matrix (isotypicDirectSumCarrier d g)
        (isotypicDirectSumCarrier d g) ℂ) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [isotypicDirectSumQueryProjector, Matrix.sum_apply]
  · simp [isotypicDirectSumQueryProjector, Matrix.sum_apply, hxy]

/-- Direct-sum version of the manuscript witness
`I_{V_a}/dim(V_a) ⊗ |e_{a,r}><e_{a,r}|`. -/
def isotypicDirectSumAuxiliaryState
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    Matrix (isotypicDirectSumCarrier d g) (isotypicDirectSumCarrier d g) ℂ :=
  ((d j.1 : ℂ)⁻¹) • isotypicDirectSumQueryProjector d g j

theorem isotypicDirectSumAuxiliaryState_posSemidef
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (j : multiplicityMemoryCarrier g) :
    (isotypicDirectSumAuxiliaryState d g j).PosSemidef := by
  apply (isotypicDirectSumQueryProjector_posSemidef d g j).smul
  exact inv_nonneg.mpr (by positivity)

@[simp] theorem isotypicDirectSumAuxiliaryState_trace
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (hd : ∀ a, 0 < d a)
    (j : multiplicityMemoryCarrier g) :
    Matrix.trace (isotypicDirectSumAuxiliaryState d g j) = 1 := by
  rw [isotypicDirectSumAuxiliaryState, Matrix.trace_smul,
    isotypicDirectSumQueryProjector_trace]
  have hneNat : d j.1 ≠ 0 := Nat.ne_of_gt (hd j.1)
  have hne : (d j.1 : ℂ) ≠ 0 := by exact_mod_cast hneNat
  simp [smul_eq_mul, hne]

/-- Each global source query projector has unit score on its corresponding
normalized auxiliary state. -/
@[simp] theorem isotypicDirectSumQueryProjector_auxiliaryState_trace
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) (hd : ∀ a, 0 < d a)
    (j : multiplicityMemoryCarrier g) :
    Matrix.trace
      (isotypicDirectSumQueryProjector d g j *
        isotypicDirectSumAuxiliaryState d g j) = 1 := by
  rw [isotypicDirectSumAuxiliaryState, Matrix.mul_smul,
    isotypicDirectSumQueryProjector_mul_self, Matrix.trace_smul,
    isotypicDirectSumQueryProjector_trace]
  have hneNat : d j.1 ≠ 0 := Nat.ne_of_gt (hd j.1)
  have hne : (d j.1 : ℂ) ≠ 0 := by exact_mod_cast hneNat
  simp [smul_eq_mul, hne]

end

end FormalResearch.QIA
