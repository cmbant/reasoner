import FormalResearch.QIA.FourQubitD3BlockCensus
import FormalResearch.QIA.MultiplicityProfileDimensions

/-!
# QI-A T39 operational fingerprint dimensions

Source pin: `cmbant/QIprojects@1835b62a5ea6577c0ca685101276419cab04e671`.
Exact external verifier blob:
`d058c7650a6a75466eb47945c3948685d13f0533`
(`QI-A/scripts/verify_operational_fingerprint.py`).

This module packages the finite dimension layer requested by T39.  It proves
only the arithmetic/block-census certificate behind the four-qubit,
three-copy operational fingerprint counts.  It does not formalize tomography
sample complexity, measurement sufficiency, gate synthesis, or the later Haar
second-moment statement.
-/

namespace FormalResearch.QIA

open scoped BigOperators

/-- T39's normalized-coordinate bookkeeping quantity: one trace constraint is
removed from the full invariant-algebra dimension.  The definition itself is
only a finite dimension count; no tomography semantics are asserted here. -/
def normalizedFingerprintCoordinateCount {α : Type*} [Fintype α]
    (g : α → Nat) : Nat :=
  multiplicityAlgebraDimension g - 1

/-- The normalized-coordinate count inherits the universal decomposition of
the invariant-algebra dimension into memory and conjugation-odd directions. -/
theorem normalizedFingerprintCoordinateCount_eq_memory_add_two_odd_sub_one
    {α : Type*} [Fintype α] (g : α → Nat) :
    normalizedFingerprintCoordinateCount g =
      multiplicityMemoryDimension g + 2 * multiplicityOddDimension g - 1 := by
  unfold normalizedFingerprintCoordinateCount
  rw [multiplicityAlgebra_eq_memory_add_two_odd]

/-- Re-express the already certified four-qubit `d=3` memory count through the
generic multiplicity-profile interface used by T39. -/
theorem fourQubitD3_memory_dimension_profile :
    multiplicityMemoryDimension fourQubitD3BlockDim = 14 := by
  simpa [multiplicityMemoryDimension] using fourQubitD3_memory_dimension

/-- Re-express the already certified four-qubit `d=3` algebra dimension through
the generic multiplicity-profile interface used by T39. -/
theorem fourQubitD3_invariant_algebra_dimension_profile :
    multiplicityAlgebraDimension fourQubitD3BlockDim = 20 := by
  simpa [multiplicityAlgebraDimension] using fourQubitD3_invariant_algebra_dimension

/-- Re-express the already certified conjugation-odd dimension through the
generic multiplicity-profile interface used by T39. -/
theorem fourQubitD3_odd_hermitian_dimension_profile :
    multiplicityOddDimension fourQubitD3BlockDim = 3 := by
  simpa [multiplicityOddDimension] using fourQubitD3_odd_hermitian_dimension

/-- The finite normalized fingerprint count in the four-qubit, three-copy
example is `R - 1 = 20 - 1 = 19`. -/
theorem fourQubitD3_normalized_fingerprint_coordinate_count :
    normalizedFingerprintCoordinateCount fourQubitD3BlockDim = 19 := by
  change multiplicityAlgebraDimension fourQubitD3BlockDim - 1 = 19
  rw [fourQubitD3_invariant_algebra_dimension_profile]

/-- Finite block-shape certificate behind the notation `ℂ^11 ⊕ M₃(ℂ)`: there
are eleven nonzero scalar blocks and one nonzero multiplicity-three block, and
no other positive block dimension occurs.  This theorem records only block
dimensions, not an explicit algebra isomorphism. -/
theorem fourQubitD3_reduced_algebra_shape_certificate :
    (Finset.univ.filter
      (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 1)).card = 11 ∧
    (Finset.univ.filter
      (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 3)).card = 1 ∧
    (∀ S : Finset (Fin 4),
      fourQubitD3BlockDim S = 0 ∨ fourQubitD3BlockDim S = 1 ∨
        fourQubitD3BlockDim S = 3) := by
  exact ⟨fourQubitD3_block_census.2.1,
    fourQubitD3_block_census.2.2.1,
    fourQubitD3_block_census.2.2.2⟩

/-- Compact T39 finite fingerprint/dimension certificate.  In source notation,
this is the numerical content
`A_inv = ℂ^11 ⊕ M₃(ℂ)`, `K = 14`, `R = 20`, `R - 1 = 19`, and
`r_odd = 3`, with the algebra notation represented here by its exact block
census rather than an explicit algebra equivalence. -/
theorem fourQubitD3_operational_fingerprint_dimension_certificate :
    (Finset.univ.filter
      (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 1)).card = 11 ∧
    (Finset.univ.filter
      (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 3)).card = 1 ∧
    multiplicityMemoryDimension fourQubitD3BlockDim = 14 ∧
    multiplicityAlgebraDimension fourQubitD3BlockDim = 20 ∧
    normalizedFingerprintCoordinateCount fourQubitD3BlockDim = 19 ∧
    multiplicityOddDimension fourQubitD3BlockDim = 3 := by
  exact ⟨fourQubitD3_reduced_algebra_shape_certificate.1,
    fourQubitD3_reduced_algebra_shape_certificate.2.1,
    fourQubitD3_memory_dimension_profile,
    fourQubitD3_invariant_algebra_dimension_profile,
    fourQubitD3_normalized_fingerprint_coordinate_count,
    fourQubitD3_odd_hermitian_dimension_profile⟩

end FormalResearch.QIA
