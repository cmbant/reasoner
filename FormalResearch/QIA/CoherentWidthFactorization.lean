import Mathlib.LinearAlgebra.Matrix.Rank
import FormalResearch.QIA.MultiplicityProfileDimensions

/-!
# QI-A exact reversible coherent-width factorization core

Source authority: `cmbant/QIprojects@ec8d5c5210e6837992ace8fcf63da77c5f8a557e`.
The QI-A manuscript states that exact reversible storage with free classical
sector labels has minimum coherent branch dimension

`w_min = max_alpha dim M_alpha`.

Its lower-bound proof uses a maximally entangled state in a largest
multiplicity block and Schmidt-number monotonicity under recovery.

This module formalizes the finite-dimensional matrix-rank core of that
argument.  If the identity on a `g`-dimensional block factors exactly through a
`q`-dimensional coherent register, then matrix rank forces `g <= q`.  Applying
this sectorwise gives `max_alpha g(alpha) <= q`.

The semantic bridge from an arbitrary exact reversible quantum storage/recovery
scheme to the displayed matrix factorization on Schmidt coefficients is not
formalized here.  Likewise the classically flagged multiplicity-register upper
bound is represented only by the elementary fact that every sector dimension
is bounded by the finite maximum; no CPTP/channel construction is claimed.
-/

namespace FormalResearch.QIA

/-- Maximum multiplicity dimension when the sector label is free classical
side information.  `Finset.sup` returns zero on an empty sector type. -/
def multiplicityCoherentWidth {α : Type*} [Fintype α] (g : α → Nat) : Nat :=
  Finset.univ.sup g

/-- Every multiplicity block fits inside the maximum coherent width. -/
theorem multiplicity_le_coherentWidth
    {α : Type*} [Fintype α] (g : α → Nat) (a : α) :
    g a ≤ multiplicityCoherentWidth g := by
  unfold multiplicityCoherentWidth
  exact Finset.le_sup (Finset.mem_univ a)

/-- Matrix-rank form of the maximally-entangled/Schmidt bottleneck.

If exact recovery makes the identity on `J` factor as a map through columns
indexed by the coherent-memory type `q`, then the memory has at least as many
dimensions as `J`. -/
theorem exactReversibleFactorization_card_le_memory
    {J q : Type*} [Fintype J] [DecidableEq J] [Fintype q]
    (C : Matrix J q ℂ) (R : Matrix q J ℂ)
    (hrecover : C * R = (1 : Matrix J J ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  have hrank : (C * R).rank = Fintype.card J := by
    rw [hrecover, Matrix.rank_one]
  calc
    Fintype.card J = (C * R).rank := hrank.symm
    _ ≤ C.rank := Matrix.rank_mul_le_left C R
    _ ≤ Fintype.card q := Matrix.rank_le_card_width C

/-- Sectorwise exact reversible factorization through one coherent branch
forces the branch dimension to dominate the largest multiplicity.  The sector
label itself is free and therefore does not enter the coherent dimension. -/
theorem multiplicityCoherentWidth_le_of_exact_sector_factorizations
    {α q : Type*} [Fintype α] [Fintype q]
    (g : α → Nat)
    (C : ∀ a, Matrix (Fin (g a)) q ℂ)
    (R : ∀ a, Matrix q (Fin (g a)) ℂ)
    (hrecover : ∀ a, C a * R a = (1 : Matrix (Fin (g a)) (Fin (g a)) ℂ)) :
    multiplicityCoherentWidth g ≤ Fintype.card q := by
  unfold multiplicityCoherentWidth
  apply Finset.sup_le
  intro a ha
  simpa using exactReversibleFactorization_card_le_memory
    (C a) (R a) (hrecover a)

/-- The exact reversible coherent-width arithmetic sandwich: `w=max g` is
large enough for every individual multiplicity block, and any common coherent
register admitting the sectorwise exact factorizations has dimension at least
`w`. -/
theorem multiplicityCoherentWidth_factorization_certificate
    {α q : Type*} [Fintype α] [Fintype q]
    (g : α → Nat)
    (C : ∀ a, Matrix (Fin (g a)) q ℂ)
    (R : ∀ a, Matrix q (Fin (g a)) ℂ)
    (hrecover : ∀ a, C a * R a = (1 : Matrix (Fin (g a)) (Fin (g a)) ℂ)) :
    (∀ a, g a ≤ multiplicityCoherentWidth g) ∧
      multiplicityCoherentWidth g ≤ Fintype.card q := by
  exact ⟨fun a => multiplicity_le_coherentWidth g a,
    multiplicityCoherentWidth_le_of_exact_sector_factorizations g C R hrecover⟩

end FormalResearch.QIA
