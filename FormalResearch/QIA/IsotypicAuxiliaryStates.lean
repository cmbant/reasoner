import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# QI-A isotypic query projectors and auxiliary states

The deferred-query lower bound in the QI-A manuscript fixes an orthonormal
basis `e_j` of each multiplicity block and uses, inside one isotypic factor
`V ⊗ M`, the query projectors

  `P_j = I_V ⊗ |e_j><e_j|`

and auxiliary states

  `omega_j = I_V / dim(V) ⊗ |e_j><e_j|`.

This module certifies that finite matrix model in a chosen product basis.  It is
representation-independent: the carrier type `v` models one irreducible carrier
basis and `m` one multiplicity basis.  It does not construct a Schur--Weyl or
isotypic decomposition of the physical symmetric-copy Hilbert space.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker BigOperators

noncomputable section

/-- Rank-one projector onto one chosen multiplicity basis vector. -/
def multiplicityBasisProjector
    {m : Type*} [Fintype m] [DecidableEq m] (j : m) : Matrix m m ℂ :=
  Matrix.diagonal fun k => if k = j then 1 else 0

@[simp] theorem multiplicityBasisProjector_trace
    {m : Type*} [Fintype m] [DecidableEq m] (j : m) :
    Matrix.trace (multiplicityBasisProjector j) = 1 := by
  simp [multiplicityBasisProjector]

@[simp] theorem multiplicityBasisProjector_mul_self
    {m : Type*} [Fintype m] [DecidableEq m] (j : m) :
    multiplicityBasisProjector j * multiplicityBasisProjector j =
      multiplicityBasisProjector j := by
  rw [multiplicityBasisProjector, Matrix.diagonal_mul_diagonal]
  congr
  funext k
  by_cases h : k = j <;> simp [h]

theorem multiplicityBasisProjector_posSemidef
    {m : Type*} [Fintype m] [DecidableEq m] (j : m) :
    (multiplicityBasisProjector j).PosSemidef := by
  rw [multiplicityBasisProjector, Matrix.posSemidef_diagonal_iff]
  intro k
  by_cases h : k = j <;> simp [h]

/-- On one chosen isotypic product basis `v × m`, the source query effect is
`I_v ⊗ |e_j><e_j|`. -/
def isotypicQueryProjector
    {v m : Type*} [Fintype v] [DecidableEq v]
    [Fintype m] [DecidableEq m] (j : m) : Matrix (v × m) (v × m) ℂ :=
  (1 : Matrix v v ℂ) ⊗ₖ multiplicityBasisProjector j

theorem isotypicQueryProjector_posSemidef
    {v m : Type*} [Fintype v] [DecidableEq v]
    [Fintype m] [DecidableEq m] (j : m) :
    (isotypicQueryProjector (v := v) j).PosSemidef := by
  have hI : (1 : Matrix v v ℂ).PosSemidef := .one
  exact hI.kronecker (multiplicityBasisProjector_posSemidef j)

theorem isotypicQueryProjector_isSelfAdjoint
    {v m : Type*} [Fintype v] [DecidableEq v]
    [Fintype m] [DecidableEq m] (j : m) :
    IsSelfAdjoint (isotypicQueryProjector (v := v) j) :=
  (isotypicQueryProjector_posSemidef (v := v) j).isHermitian.isSelfAdjoint

@[simp] theorem isotypicQueryProjector_mul_self
    {v m : Type*} [Fintype v] [DecidableEq v]
    [Fintype m] [DecidableEq m] (j : m) :
    isotypicQueryProjector (v := v) j * isotypicQueryProjector (v := v) j =
      isotypicQueryProjector (v := v) j := by
  rw [isotypicQueryProjector, Matrix.mul_kronecker_mul, one_mul,
    multiplicityBasisProjector_mul_self]

@[simp] theorem isotypicQueryProjector_trace
    {v m : Type*} [Fintype v] [DecidableEq v]
    [Fintype m] [DecidableEq m] (j : m) :
    Matrix.trace (isotypicQueryProjector (v := v) j) = (Fintype.card v : ℂ) := by
  simp [isotypicQueryProjector, Matrix.trace_kronecker]

/-- The multiplicity-basis query projectors form the expected sharp PVM on a
single isotypic block. -/
theorem isotypicQueryProjector_sum_eq_one
    {v m : Type*} [Fintype v] [DecidableEq v]
    [Fintype m] [DecidableEq m] :
    (∑ j : m, isotypicQueryProjector (v := v) j) =
      (1 : Matrix (v × m) (v × m) ℂ) := by
  ext ⟨a, i⟩ ⟨b, k⟩
  by_cases hab : a = b
  · subst b
    by_cases hik : i = k
    · subst k
      simp [isotypicQueryProjector, multiplicityBasisProjector]
    · simp [isotypicQueryProjector, multiplicityBasisProjector, hik]
  · simp [isotypicQueryProjector, multiplicityBasisProjector, hab]

/-- Manuscript auxiliary state `I_V / dim(V) ⊗ |e_j><e_j|` in the chosen
product basis.  A nonempty carrier is the finite-basis form of `dim V > 0`. -/
def isotypicAuxiliaryState
    {v m : Type*} [Fintype v] [DecidableEq v] [Nonempty v]
    [Fintype m] [DecidableEq m] (j : m) : Matrix (v × m) (v × m) ℂ :=
  ((Fintype.card v : ℂ)⁻¹) • isotypicQueryProjector (v := v) j

theorem isotypicAuxiliaryState_posSemidef
    {v m : Type*} [Fintype v] [DecidableEq v] [Nonempty v]
    [Fintype m] [DecidableEq m] (j : m) :
    (isotypicAuxiliaryState (v := v) j).PosSemidef := by
  apply (isotypicQueryProjector_posSemidef (v := v) j).smul
  exact inv_nonneg.mpr (by positivity)

@[simp] theorem isotypicAuxiliaryState_trace
    {v m : Type*} [Fintype v] [DecidableEq v] [Nonempty v]
    [Fintype m] [DecidableEq m] (j : m) :
    Matrix.trace (isotypicAuxiliaryState (v := v) j) = 1 := by
  rw [isotypicAuxiliaryState, Matrix.trace_smul, isotypicQueryProjector_trace]
  simp [smul_eq_mul, Fintype.card_ne_zero]

/-- Each source query projector has unit score on its corresponding manuscript
auxiliary state. -/
@[simp] theorem isotypicQueryProjector_auxiliaryState_trace
    {v m : Type*} [Fintype v] [DecidableEq v] [Nonempty v]
    [Fintype m] [DecidableEq m] (j : m) :
    Matrix.trace
      (isotypicQueryProjector (v := v) j * isotypicAuxiliaryState (v := v) j) = 1 := by
  rw [isotypicAuxiliaryState, Matrix.mul_smul,
    isotypicQueryProjector_mul_self, Matrix.trace_smul,
    isotypicQueryProjector_trace]
  simp [smul_eq_mul, Fintype.card_ne_zero]

end

end FormalResearch.QIA
