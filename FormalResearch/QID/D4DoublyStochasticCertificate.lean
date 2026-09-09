import Mathlib

namespace FormalResearch.QID

/-!
# Type-D4 doubly-stochastic separation certificate

This module matches the exact rational certificate in
`cmbant/QIprojects:QI-D/code/certify_ds_strict_D4.py` and its committed
verification log.  It formalizes the finite Type-D4 Weyl enumeration, the
reported rational witness `A`, the separating functional `F`, and the finite
coweight-orbit inequality audit.

The source-side equivalence between these finitely many coweight inequalities
and membership in `DS(W(D₄))` is intentionally **not** rederived here.  The
finite certificate is exposed as its own predicate so later bridge theorems can
state that semantic input explicitly rather than hiding it.
-/

abbrev D4Fin := Fin 4
abbrev D4Vec := D4Fin → ℚ
abbrev D4SignedPerm := Equiv.Perm D4Fin × (D4Fin → Bool)

/-- Number of negative coordinate signs in a signed permutation. -/
def d4NegCount (s : D4Fin → Bool) : Nat :=
  ∑ i : D4Fin, if s i then 1 else 0

/-- Type-D sign condition: an even number of sign flips. -/
def d4EvenSigns (s : D4Fin → Bool) : Bool :=
  decide (d4NegCount s % 2 = 0)

/-- The 192 elements of the Type-D4 Weyl group, represented as a permutation
and an even coordinate-sign pattern. -/
def allD4 : Finset D4SignedPerm :=
  Finset.univ.filter (fun ps => d4EvenSigns ps.2 = true)

/-- Exact cardinality `4! * 2^3 = 192`. -/
theorem allD4_card : allD4.card = 192 := by
  native_decide

/-- Signed-permutation matrix convention matching the source script:
column `c` is sent to row `σ c` with the sign attached to column `c`. -/
def d4SignedMatrix (ps : D4SignedPerm) : Matrix D4Fin D4Fin ℚ :=
  fun r c =>
    if r = ps.1 c then
      if ps.2 c then -1 else 1
    else 0

/-- Weyl action on a coweight vector. -/
def d4Act (ps : D4SignedPerm) (v : D4Vec) : D4Vec :=
  (d4SignedMatrix ps).mulVec v

/-- Fundamental coweights used by the finite dominance characterization. -/
def d4Omega0 : D4Vec := ![1, 0, 0, 0]
def d4Omega1 : D4Vec := ![1, 1, 0, 0]
def d4Omega2 : D4Vec := ![(1 : ℚ) / 2, 1 / 2, 1 / 2, -1 / 2]
def d4Omega3 : D4Vec := ![(1 : ℚ) / 2, 1 / 2, 1 / 2, 1 / 2]

def d4Omega : D4Fin → D4Vec := ![d4Omega0, d4Omega1, d4Omega2, d4Omega3]

/-- Exact coweight orbit under `W(D₄)`. -/
def d4OmegaOrbit (k : D4Fin) : Finset D4Vec :=
  allD4.image (fun ps => d4Act ps (d4Omega k))

/-- The source orbit sizes are exactly `(8,24,8,8)`. -/
theorem d4OmegaOrbit0_card : (d4OmegaOrbit 0).card = 8 := by native_decide
theorem d4OmegaOrbit1_card : (d4OmegaOrbit 1).card = 24 := by native_decide
theorem d4OmegaOrbit2_card : (d4OmegaOrbit 2).card = 8 := by native_decide
theorem d4OmegaOrbit3_card : (d4OmegaOrbit 3).card = 8 := by native_decide

/-- Rational witness from `certify_ds_strict_D4.py`. -/
def d4DSWitness : Matrix D4Fin D4Fin ℚ :=
  !![-1/3,  1/3,  0,   -1/3;
      1/3, -1/3,  0,   -1/3;
     -1/3, -1/3, -1/3,  0;
      0,    0,    0,    1/3]

/-- Exceptional Type-D4 facet normal used to separate the witness from
`conv W(D₄)`. -/
def d4FacetNormal : Matrix D4Fin D4Fin ℚ :=
  !![-2/4,  2/4,  0,   -1/4;
      2/4, -2/4,  0,   -1/4;
     -1/4, -1/4, -1/4,  0;
      0,    0,    0,    1/4]

/-- Frobenius pairing on rational `4×4` matrices. -/
def d4Frob (X Y : Matrix D4Fin D4Fin ℚ) : ℚ :=
  ∑ i : D4Fin, ∑ j : D4Fin, X i j * Y i j

/-- Exact separating value `<F,A> = 7/6`. -/
theorem d4Facet_witness_value :
    d4Frob d4FacetNormal d4DSWitness = 7 / 6 := by
  native_decide

/-- Support score of a Type-D4 Weyl matrix against the exceptional facet. -/
def d4WeylFacetScore (ps : D4SignedPerm) : ℚ :=
  d4Frob d4FacetNormal (d4SignedMatrix ps)

/-- Exhaustive support upper-bound audit. -/
def d4WeylSupportUpperCheck : Bool :=
  allD4.all (fun ps => decide (d4WeylFacetScore ps ≤ 1))

/-- Exhaustive attainment audit, so the Weyl maximum is exactly one. -/
def d4WeylSupportAttainedCheck : Bool :=
  allD4.any (fun ps => decide (d4WeylFacetScore ps = 1))

theorem d4WeylSupportUpperCheck_passes : d4WeylSupportUpperCheck = true := by
  native_decide

theorem d4WeylSupportAttainedCheck_passes : d4WeylSupportAttainedCheck = true := by
  native_decide

/-- Rational dot product. -/
def d4Dot (u v : D4Vec) : ℚ :=
  ∑ i : D4Fin, u i * v i

/-- Bilinear form `uᵀ M v`. -/
def d4Bilinear (u : D4Vec) (M : Matrix D4Fin D4Fin ℚ) (v : D4Vec) : ℚ :=
  ∑ i : D4Fin, ∑ j : D4Fin, u i * M i j * v j

/-- Dominant coweight bound `<ω_k,ω_j>`. -/
def d4CoweightBound (k j : D4Fin) : ℚ :=
  d4Dot (d4Omega k) (d4Omega j)

/-- Boolean finite certificate for all coweight-orbit inequalities.  Using
`Finset.all` keeps the audit genuinely finite even though rational vectors
form an infinite ambient type. -/
def d4FiniteDSCheck (M : Matrix D4Fin D4Fin ℚ) : Bool :=
  (Finset.univ : Finset D4Fin).all (fun k =>
    (Finset.univ : Finset D4Fin).all (fun j =>
      (d4OmegaOrbit k).all (fun u =>
        (d4OmegaOrbit j).all (fun v =>
          decide (d4Bilinear u M v ≤ d4CoweightBound k j)))))

/-- The exact witness satisfies every finite Type-D4 coweight inequality. -/
theorem d4DSWitness_finite_check : d4FiniteDSCheck d4DSWitness = true := by
  native_decide

/-- Claim-boundary bridge.  If an external semantic layer identifies the
finite coweight certificate with a predicate `DS`, and identifies membership
in a candidate convex set `Conv` with the facet upper bound `≤ 1`, then the
exact rational witness separates the two predicates. -/
theorem d4_strict_separation_of_certificate
    (DS Conv : Matrix D4Fin D4Fin ℚ → Prop)
    (hDS : d4FiniteDSCheck d4DSWitness = true → DS d4DSWitness)
    (hConv : ∀ M, Conv M → d4Frob d4FacetNormal M ≤ 1) :
    DS d4DSWitness ∧ ¬ Conv d4DSWitness := by
  constructor
  · exact hDS d4DSWitness_finite_check
  · intro hA
    have hle := hConv d4DSWitness hA
    rw [d4Facet_witness_value] at hle
    norm_num at hle

end FormalResearch.QID
