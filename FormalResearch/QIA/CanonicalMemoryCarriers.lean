import FormalResearch.QIA.CoherentWidthFactorization

/-!
# QI-A canonical finite memory carriers

Source authority: `cmbant/QIprojects@b06a104c594b029aeb0fc2c8f401f8d4c55b901b`,
`QI-A/paper/finite_copy_quantum_memory.tex`.

The QI-A manuscript's canonical invariant reduction uses the direct-sum
multiplicity Hilbert space `⊕_α M_α`, of total dimension `K = ∑_α g α`.  With
free classical sector labels, the coherent register only needs the largest
multiplicity width `w = max_α g α`.

This module formalizes the finite carrier/bookkeeping core of those upper-bound
constructions.  It does not construct the symmetry-reduction CPTP channel,
Hilbert direct sums, or sector-conditioned quantum channels.
-/

namespace FormalResearch.QIA

/-- A finite basis carrier for the direct sum of all multiplicity spaces:
one basis label `j : Fin (g a)` in each sector `a`. -/
abbrev multiplicityMemoryCarrier {α : Type*} [Fintype α] (g : α → Nat) : Type _ :=
  Σ a, Fin (g a)

instance multiplicityMemoryCarrierFintype
    {α : Type*} [Fintype α] (g : α → Nat) :
    Fintype (multiplicityMemoryCarrier g) := inferInstance

/-- The canonical direct-sum basis carrier has exactly `K = ∑_a g a`
elements. -/
theorem multiplicityMemoryCarrier_card
    {α : Type*} [Fintype α] (g : α → Nat) :
    Fintype.card (multiplicityMemoryCarrier g) = multiplicityMemoryDimension g := by
  simp [multiplicityMemoryCarrier, multiplicityMemoryDimension]

/-- The common coherent basis carrier used when the sector label is retained
classically. -/
abbrev multiplicityCoherentCarrier {α : Type*} [Fintype α] (g : α → Nat) : Type :=
  Fin (multiplicityCoherentWidth g)

instance multiplicityCoherentCarrierFintype
    {α : Type*} [Fintype α] (g : α → Nat) :
    Fintype (multiplicityCoherentCarrier g) := inferInstance

/-- The coherent carrier has exactly the maximum multiplicity width. -/
theorem multiplicityCoherentCarrier_card
    {α : Type*} [Fintype α] (g : α → Nat) :
    Fintype.card (multiplicityCoherentCarrier g) = multiplicityCoherentWidth g := by
  simp [multiplicityCoherentCarrier]

/-- Every sector basis embeds canonically into the common coherent register of
width `max_a g a`. -/
def multiplicityBlockEmbedding
    {α : Type*} [Fintype α] (g : α → Nat) (a : α) :
    Fin (g a) ↪ multiplicityCoherentCarrier g where
  toFun i :=
    ⟨i.1, lt_of_lt_of_le i.2 (multiplicity_le_coherentWidth g a)⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : multiplicityCoherentCarrier g => x.val) h

/-- A finite carrier making the free classical sector label explicit alongside
the common coherent register. -/
abbrev multiplicityFlaggedCarrier {α : Type*} [Fintype α] (g : α → Nat) : Type _ :=
  α × multiplicityCoherentCarrier g

instance multiplicityFlaggedCarrierFintype
    {α : Type*} [Fintype α] (g : α → Nat) :
    Fintype (multiplicityFlaggedCarrier g) := inferInstance

/-- The canonical direct-sum basis injects into a free classical sector label
paired with the common coherent register.  The first component is exactly the
original sector label. -/
def multiplicityFlaggedEmbedding
    {α : Type*} [Fintype α] (g : α → Nat) :
    multiplicityMemoryCarrier g ↪ multiplicityFlaggedCarrier g where
  toFun x := (x.1, multiplicityBlockEmbedding g x.1 x.2)
  inj' := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    have hab : a = b := congrArg Prod.fst h
    subst b
    have hij :
        multiplicityBlockEmbedding g a i = multiplicityBlockEmbedding g a j :=
      congrArg Prod.snd h
    have : i = j := (multiplicityBlockEmbedding g a).injective hij
    subst j
    rfl

@[simp] theorem multiplicityFlaggedEmbedding_sector
    {α : Type*} [Fintype α] (g : α → Nat)
    (x : multiplicityMemoryCarrier g) :
    (multiplicityFlaggedEmbedding g x).1 = x.1 := rfl

/-- The flagged carrier has the expected raw cardinality: number of sector
labels times coherent width. -/
theorem multiplicityFlaggedCarrier_card
    {α : Type*} [Fintype α] (g : α → Nat) :
    Fintype.card (multiplicityFlaggedCarrier g) =
      Fintype.card α * multiplicityCoherentWidth g := by
  simp [multiplicityFlaggedCarrier, multiplicityCoherentCarrier]

/-- Finite-cardinality consequence of the explicit flagged embedding.  This is
bookkeeping only: the classical label is declared free in the coherent-width
cost model, so this product cardinality is not itself the coherent-memory
cost. -/
theorem multiplicityMemoryCarrier_card_le_flaggedCarrier_card
    {α : Type*} [Fintype α] (g : α → Nat) :
    Fintype.card (multiplicityMemoryCarrier g) ≤
      Fintype.card (multiplicityFlaggedCarrier g) := by
  exact Fintype.card_le_of_injective (multiplicityFlaggedEmbedding g)
    (multiplicityFlaggedEmbedding g).injective

end FormalResearch.QIA
