import Mathlib.LinearAlgebra.Dual.Lemmas
import FormalResearch.QIA.MultiplicityProfileDimensions
import FormalResearch.QIA.SectorLabelOnlyCodeDimension

namespace FormalResearch.QIA

open Module
open Matrix
open scoped ComplexOrder MatrixOrder

/-!
# QI-A pure-copy exact-memory linear core

This module formalizes the easy finite-dimensional semantic steps immediately
downstream of the paper's coherent-copy separation lemma.

It deliberately does **not** claim the full paper theorem.  The remaining
source-specific bridge is to instantiate `s` with the reduced coherent-power
family and prove the bidegree-`(d,d)` polarization/separation statement, plus
the concrete symmetry-reduction/channel identifications.  Once that separation
input is available, the span, recovery-identity, and finite memory-cardinality
steps below are internal Lean theorems.
-/

/-- If the only linear functional vanishing on a family `s` is zero, then `s`
spans the whole finite-dimensional vector space.  This is the abstract linear
step used in the paper after coherent-copy separation and nondegeneracy of the
Hilbert--Schmidt pairing. -/
theorem span_eq_top_of_dual_annihilation
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (s : Set E)
    (hsep : ∀ f : Module.Dual 𝕜 E, (∀ x ∈ s, f x = 0) → f = 0) :
    Submodule.span 𝕜 s = ⊤ := by
  by_contra hne
  have hlt : Submodule.span 𝕜 s < ⊤ := (lt_top_iff_ne_top).2 hne
  obtain ⟨f, hfne, hfmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hlt (inferInstance)
  apply hfne
  apply hsep f
  intro x hx
  have hfx : f x ∈ (Submodule.span 𝕜 s).map f :=
    ⟨x, Submodule.subset_span hx, rfl⟩
  rw [hfmap] at hfx
  simpa using hfx

/-- Pairing form of the same span theorem.  In the paper the intended pairing
is the nondegenerate Hilbert--Schmidt trace pairing on the multiplicity
algebra. -/
theorem span_eq_top_of_surjective_pairing_separation
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (s : Set E)
    (pair : E →ₗ[𝕜] Module.Dual 𝕜 E)
    (hpair : Function.Surjective pair)
    (hsep : ∀ y : E, (∀ x ∈ s, pair y x = 0) → y = 0) :
    Submodule.span 𝕜 s = ⊤ := by
  apply span_eq_top_of_dual_annihilation s
  intro f hf
  obtain ⟨y, hy⟩ := hpair f
  rw [← hy]
  have hy0 : y = 0 := by
    apply hsep y
    intro x hx
    simpa [hy] using hf x hx
  simp [hy0]

/-- A linear endomorphism fixing a spanning family is the identity. -/
theorem linearMap_eq_id_of_fix_spanning_family
    {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (s : Set E) (hspan : Submodule.span 𝕜 s = ⊤)
    (T : E →ₗ[𝕜] E)
    (hfix : ∀ x ∈ s, T x = x) :
    T = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hOn : Set.EqOn T (LinearMap.id : E →ₗ[𝕜] E) (Submodule.span 𝕜 s) :=
    (LinearMap.eqOn_span_iff).2 (by
      intro y hy
      simpa using hfix y hy)
  have hx : x ∈ Submodule.span 𝕜 s := by
    rw [hspan]
    exact Submodule.mem_top
  simpa using hOn hx

/-- If encoding followed by recovery fixes every state in a spanning family,
then the composite is the identity on the whole linear state space.  This is
the exact linear extension used in part (ii) of the paper's pure-copy
reversible-compression theorem once full spanning is known. -/
theorem recovery_comp_encoding_eq_id_of_fix_spanning_family
    {𝕜 E M : Type*} [Semiring 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid M] [Module 𝕜 M]
    (s : Set E) (hspan : Submodule.span 𝕜 s = ⊤)
    (C : E →ₗ[𝕜] M) (R : M →ₗ[𝕜] E)
    (hfix : ∀ x ∈ s, R (C x) = x) :
    R.comp C = LinearMap.id := by
  apply linearMap_eq_id_of_fix_spanning_family s hspan
  intro x hx
  simpa using hfix x hx

/-- Perfect identification of one encoded state per message forces the message
cardinality to be no larger than the Hilbert-space dimension of the quantum
memory.  This is the finite-dimensional distinguishability step used by the
paper's exact deferred-query lower bound. -/
theorem perfectIdentification_card_le_memory
    {J q : Type*} [Fintype J]
    [Fintype q] [DecidableEq q]
    (B omega : J → Matrix q q ℂ)
    (hB : ∀ j, (B j).PosSemidef)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ))
    (hPOVM : (∑ j, B j) = (1 : Matrix q q ℂ))
    (hperfect : ∀ j, sectorCodeTraceScore (B j) (omega j) = 1) :
    Fintype.card J ≤ Fintype.card q := by
  classical
  have htotal := sectorCode_totalSuccess_le_dimension B omega hB homega hPOVM
  have hsum :
      (∑ j, sectorCodeTraceScore (B j) (omega j)) = (Fintype.card J : ℝ) := by
    simp [hperfect]
  rw [hsum] at htotal
  exact_mod_cast htotal

/-- Multiplicity-profile form of the previous cardinality bound.  If the
perfectly identified auxiliary family has exactly one state for each basis
vector across all multiplicity blocks, then any ordinary quantum memory has
dimension at least `K = sum g`.  The missing pure-copy bridge is precisely the
step establishing the required perfect-identification identities on these
auxiliary states from equality of query statistics on coherent powers. -/
theorem multiplicityMemoryDimension_le_of_perfect_basis_query
    {α J q : Type*} [Fintype α] [Fintype J]
    [Fintype q] [DecidableEq q]
    (g : α → Nat)
    (hJ : Fintype.card J = multiplicityMemoryDimension g)
    (B omega : J → Matrix q q ℂ)
    (hB : ∀ j, (B j).PosSemidef)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ))
    (hPOVM : (∑ j, B j) = (1 : Matrix q q ℂ))
    (hperfect : ∀ j, sectorCodeTraceScore (B j) (omega j) = 1) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  rw [← hJ]
  exact perfectIdentification_card_le_memory B omega hB homega hPOVM hperfect

end FormalResearch.QIA
