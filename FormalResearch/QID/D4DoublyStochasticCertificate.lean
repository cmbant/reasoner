import Mathlib

namespace FormalResearch.QID

/-!
# Type-D4 doubly-stochastic separation certificate

This module matches the exact rational certificate in
`cmbant/QIprojects:QI-D/code/certify_ds_strict_D4.py` and its committed
verification log, re-audited with QIprojects main at
`cf5bb7ea42362d9557172a1df96ff1d567da2fe5`.

It formalizes the finite Type-D4 Weyl enumeration, the reported rational
witness `A`, the separating functional `F`, and the finite coweight-orbit
inequality audit.

The source-side equivalence between these finitely many coweight inequalities
and membership in `DS(W(D₄))` is intentionally **not** rederived here. The
finite certificate is exposed separately so a later semantic bridge must state
that input explicitly rather than hiding it.
-/

abbrev D4Fin := Fin 4
abbrev D4Vec := D4Fin → ℚ
abbrev D4SignedPerm := Equiv.Perm D4Fin × (D4Fin → Bool)

def d4NegCount (s : D4Fin → Bool) : Nat :=
  ∑ i : D4Fin, if s i then 1 else 0

def d4EvenSigns (s : D4Fin → Bool) : Bool :=
  decide (d4NegCount s % 2 = 0)

def allD4 : Finset D4SignedPerm :=
  Finset.univ.filter (fun ps => d4EvenSigns ps.2 = true)

theorem allD4_card : allD4.card = 192 := by
  native_decide

def d4SignedMatrix (ps : D4SignedPerm) : Matrix D4Fin D4Fin ℚ :=
  fun r c =>
    if r = ps.1 c then
      if ps.2 c then -1 else 1
    else 0

def d4Act (ps : D4SignedPerm) (v : D4Vec) : D4Vec :=
  (d4SignedMatrix ps).mulVec v

def d4Omega0 : D4Vec := ![1, 0, 0, 0]
def d4Omega1 : D4Vec := ![1, 1, 0, 0]
def d4Omega2 : D4Vec := ![(1 : ℚ) / 2, 1 / 2, 1 / 2, -1 / 2]
def d4Omega3 : D4Vec := ![(1 : ℚ) / 2, 1 / 2, 1 / 2, 1 / 2]

def d4Omega : D4Fin → D4Vec := ![d4Omega0, d4Omega1, d4Omega2, d4Omega3]

def d4OmegaOrbit (k : D4Fin) : Finset D4Vec :=
  allD4.image (fun ps => d4Act ps (d4Omega k))

theorem d4OmegaOrbit0_card : (d4OmegaOrbit 0).card = 8 := by native_decide
theorem d4OmegaOrbit1_card : (d4OmegaOrbit 1).card = 24 := by native_decide
theorem d4OmegaOrbit2_card : (d4OmegaOrbit 2).card = 8 := by native_decide
theorem d4OmegaOrbit3_card : (d4OmegaOrbit 3).card = 8 := by native_decide

def d4DSWitness : Matrix D4Fin D4Fin ℚ :=
  !![-1/3,  1/3,  0,   -1/3;
      1/3, -1/3,  0,   -1/3;
     -1/3, -1/3, -1/3,  0;
      0,    0,    0,    1/3]

def d4FacetNormal : Matrix D4Fin D4Fin ℚ :=
  !![-2/4,  2/4,  0,   -1/4;
      2/4, -2/4,  0,   -1/4;
     -1/4, -1/4, -1/4,  0;
      0,    0,    0,    1/4]

def d4Frob (X Y : Matrix D4Fin D4Fin ℚ) : ℚ :=
  ∑ i : D4Fin, ∑ j : D4Fin, X i j * Y i j

theorem d4Facet_witness_value :
    d4Frob d4FacetNormal d4DSWitness = 7 / 6 := by
  native_decide

def d4WeylFacetScore (ps : D4SignedPerm) : ℚ :=
  d4Frob d4FacetNormal (d4SignedMatrix ps)

def d4WeylSupportViolationCount : Nat :=
  (allD4.filter (fun ps => decide (1 < d4WeylFacetScore ps))).card

def d4WeylSupportAttainmentCount : Nat :=
  (allD4.filter (fun ps => decide (d4WeylFacetScore ps = 1))).card

theorem d4WeylSupportViolationCount_zero : d4WeylSupportViolationCount = 0 := by
  native_decide

theorem d4WeylSupportAttainmentCount_pos : 0 < d4WeylSupportAttainmentCount := by
  native_decide

def d4Dot (u v : D4Vec) : ℚ :=
  ∑ i : D4Fin, u i * v i

def d4Bilinear (u : D4Vec) (M : Matrix D4Fin D4Fin ℚ) (v : D4Vec) : ℚ :=
  ∑ i : D4Fin, ∑ j : D4Fin, u i * M i j * v j

def d4CoweightBound (k j : D4Fin) : ℚ :=
  d4Dot (d4Omega k) (d4Omega j)

def d4ConstraintCount : Nat :=
  ∑ k : D4Fin, ∑ j : D4Fin,
    ((d4OmegaOrbit k).product (d4OmegaOrbit j)).card

def d4ViolationCount (M : Matrix D4Fin D4Fin ℚ) : Nat :=
  ∑ k : D4Fin, ∑ j : D4Fin,
    (((d4OmegaOrbit k).product (d4OmegaOrbit j)).filter (fun uv =>
      decide (d4CoweightBound k j < d4Bilinear uv.1 M uv.2))).card

def d4FiniteDSCertificate (M : Matrix D4Fin D4Fin ℚ) : Prop :=
  d4ViolationCount M = 0

theorem d4ConstraintCount_exact : d4ConstraintCount = 2304 := by
  native_decide

theorem d4DSWitness_no_violations : d4ViolationCount d4DSWitness = 0 := by
  native_decide

theorem d4DSWitness_finite_certificate :
    d4ConstraintCount = 2304 ∧ d4FiniteDSCertificate d4DSWitness := by
  refine ⟨d4ConstraintCount_exact, ?_⟩
  simpa [d4FiniteDSCertificate] using d4DSWitness_no_violations

theorem d4_strict_separation_of_certificate
    (DS Conv : Matrix D4Fin D4Fin ℚ → Prop)
    (hDS : d4FiniteDSCertificate d4DSWitness → DS d4DSWitness)
    (hConv : ∀ M, Conv M → d4Frob d4FacetNormal M ≤ 1) :
    DS d4DSWitness ∧ ¬ Conv d4DSWitness := by
  constructor
  · exact hDS d4DSWitness_finite_certificate.2
  · intro hA
    have hle := hConv d4DSWitness hA
    rw [d4Facet_witness_value] at hle
    norm_num at hle

end FormalResearch.QID
