import FormalResearch.QIA.CanonicalMemoryCarriers
import FormalResearch.QIA.PureCopyMemoryCore

/-!
# QI-A deferred-query post-separation memory bound

Source authority: `cmbant/QIprojects@f96b5b0be457867f068fc40461853048e346239d`,
`QI-A/paper/finite_copy_quantum_memory.tex`, manuscript blob
`6f4af839cc7c13b0cb2b3704fcefdeb1d88e9195`.

The manuscript's no-recovery deferred-query lower bound has two logically
separate steps.  Coherent-copy separation first upgrades equality of query
statistics on physical coherent powers to the Heisenberg operator identity

  `Cstar (F j) = P j`

on the whole symmetric-space source.  Only after that identity is known does
the proof evaluate on auxiliary states `omega j`, obtaining a perfectly
distinguishable family in the memory and hence the Hilbert-dimension bound.

This module formalizes that second, post-separation step.  In particular there
is no recovery map here.  The source Hilbert index `h` is arbitrary, so the
auxiliary states and source query projectors need not live on the multiplicity
carrier itself.  The missing source-specific input is precisely the coherent-
power separation theorem that establishes the operator identity from physical
query statistics, together with the concrete symmetry-reduction/channel
identifications.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- Post-separation finite form of the no-recovery deferred-query converse.

`C` is a Schrödinger encoding into the memory and `Cstar` its trace adjoint.
`F` is the memory POVM chosen after the query is revealed.  Once coherent-copy
separation has established `Cstar (F j) = P j`, evaluating on auxiliary source
states with unit diagonal score makes the encoded states perfectly identified.
The existing finite POVM trace budget then forces `card J ≤ card q`.

The explicit bound `C (omega j) ≤ I` is the same finite density-state bound
used by `PureCopyMemoryCore`; it is automatic for genuine density matrices but
is retained here rather than introducing a separate spectral-state API.
-/
theorem deferredAdjointOperatorIdentity_card_le_memory
    {J h q : Type*} [Fintype J] [Fintype h]
    [Fintype q] [DecidableEq q]
    (omega P : J → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (Cstar : Matrix q q ℂ →ₗ[ℂ] Matrix h h ℂ)
    (F : J → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hadjoint : ∀ (A : Matrix q q ℂ) (X : Matrix h h ℂ),
      Matrix.trace (A * C X) = Matrix.trace (Cstar A * X))
    (hoperator : ∀ j, Cstar (F j) = P j)
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  apply perfectIdentification_card_le_memory F (fun j => C (omega j))
  · exact hFpos
  · exact hencoded
  · exact hPOVM
  · intro j
    unfold sectorCodeTraceScore
    change RCLike.re (Matrix.trace (F j * C (omega j))) = 1
    rw [hadjoint (F j) (omega j), hoperator j]
    exact hdiag j

/-- QI-A multiplicity-profile specialization of the post-separation converse.
The query labels are indexed by one auxiliary basis state for every vector in
the direct sum of multiplicity spaces, so their cardinality is exactly
`K_G = multiplicityMemoryDimension g`.  The source Hilbert space remains
arbitrary, matching the manuscript where the projectors `P_{αj}` and auxiliary
states `omega_{αj}` live inside the corresponding full isotypic blocks. -/
theorem multiplicityMemoryDimension_le_of_deferredAdjointOperatorIdentity
    {α h q : Type*} [Fintype α] [Fintype h]
    [Fintype q] [DecidableEq q]
    (g : α → Nat)
    (omega P : multiplicityMemoryCarrier g → Matrix h h ℂ)
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (Cstar : Matrix q q ℂ →ₗ[ℂ] Matrix h h ℂ)
    (F : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (hadjoint : ∀ (A : Matrix q q ℂ) (X : Matrix h h ℂ),
      Matrix.trace (A * C X) = Matrix.trace (Cstar A * X))
    (hoperator : ∀ j, Cstar (F j) = P j)
    (hdiag : ∀ j,
      RCLike.re (Matrix.trace (P j * omega j)) = 1)
    (hencoded : ∀ j, C (omega j) ≤ (1 : Matrix q q ℂ)) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  have hbound := deferredAdjointOperatorIdentity_card_le_memory
    omega P C Cstar F hFpos hPOVM hadjoint hoperator hdiag hencoded
  rw [multiplicityMemoryCarrier_card g] at hbound
  exact hbound

end

end FormalResearch.QIA
