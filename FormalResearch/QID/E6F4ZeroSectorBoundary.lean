import FormalResearch.QID.D4DoublyStochasticCertificate

namespace FormalResearch.QID

/-!
# QI-D T48 E6/F4 zero-sector boundary certificate

Source authority:
`cmbant/QIprojects:QI-D/code/certify_E6_F4_endpoint_locus_reduction.py`
and its committed verification log, audited at QIprojects main
`e2b93eda6ca2d1a9d9bf5ed280946c6b5cc71b25`.

T48 identifies the zero-restricted-root centralizer with `Spin(8)` / type `D4`.
For each of four certified E6 facet functionals, the source verifier changes to
an `m+a` adapted Cartan basis and checks on the zero-sector boundary that

* the `a`-block contributes exactly `1/3`;
* the central `W(D4)` support is exactly `2/3`;
* the corresponding active counts are `24,20,16,14`;
* hence the total zero-sector boundary support is exactly `1`.

This module formalizes that finite rational certificate while reusing the
existing exact 192-element even signed-permutation model `allD4` from
`D4DoublyStochasticCertificate`.

To make the source-coordinate match explicit, it also checks an exact change of
basis `P` from the T48 folded-fixed Cartan coordinates to the standard signed
permutation model.  The four source simple-reflection matrices are conjugated by
`P` to the standard type-D4 simple reflections, `P^T P` is the source Gram
block, and each source `F_tt` normal is transformed to the standard-coordinate
normal used in the finite support check.

This is only the T48 **zero-sector boundary** certificate. It does not formalize
the full E6 restricted-root enumeration, the identification of the three
multiplicity-eight triality modules, the PSD/rank endpoint outer locus, or the
missing common-F4/triality compatibility for interior endpoints. In particular
it does **not** prove compact-E6 simultaneous Weyl convexity; the remaining
interior problem is source-side T49.
-/

abbrev T48D4Mat := Matrix D4Fin D4Fin ℚ
abbrev T48AFin := Fin 2
abbrev T48AMat := Matrix T48AFin T48AFin ℚ

/-- Folded-fixed Cartan Gram block printed by the T48 source verifier. -/
def t48FoldedGram : T48D4Mat :=
  !![ 4, -2,  0,  0;
     -2,  4, -2,  0;
      0, -2,  2, -1;
      0,  0, -1,  2]

/-- Exact change of basis from the T48 folded-fixed coordinates to the standard
orthonormal signed-permutation realization of `W(D4)`. -/
def t48D4BasisChange : T48D4Mat :=
  !![ 0,  1, -1,  0;
      0, -1,  1, -1;
      0, -1,  0,  1;
     -2,  1,  0,  0]

/-- Explicit rational inverse of `t48D4BasisChange`. -/
def t48D4BasisChangeInv : T48D4Mat :=
  !![-1/2, -1/2, -1/2, -1/2;
     -1,   -1,   -1,    0;
     -2,   -1,   -1,    0;
     -1,   -1,    0,    0]

/-- The basis change is nonsingular, has the displayed inverse, and pulls the
standard Euclidean form back to the exact source Gram block. -/
theorem t48D4BasisChange_certificate :
    t48D4BasisChange.det = -2 ∧
      t48D4BasisChange * t48D4BasisChangeInv = 1 ∧
      t48D4BasisChangeInv * t48D4BasisChange = 1 ∧
      t48D4BasisChange.transpose * t48D4BasisChange = t48FoldedGram := by
  native_decide

/-- Four simple reflections of the zero-restricted-root D4 in the source
folded-fixed basis, in the source's reordered D4-node convention. -/
def t48SourceD4Simple (k : Fin 4) : T48D4Mat :=
  match k.1 with
  | 0 => !![1,0,0,0; 0,1,0,0; 0,2,-1,1; 0,0,0,1]
  | 1 => !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,1,-1]
  | 2 => !![1,0,0,0; 2,-1,0,1; 2,-2,1,1; 0,0,0,1]
  | _ => !![-1,0,0,1; -2,1,0,1; -2,0,1,1; 0,0,0,1]

/-- Standard D4 simple reflections in signed-permutation coordinates. The last
reflection swaps the final two coordinates and flips both signs. -/
def t48StandardD4Simple (k : Fin 4) : T48D4Mat :=
  match k.1 with
  | 0 => !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1]
  | 1 => !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  | 2 => !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]
  | _ => !![1,0,0,0; 0,1,0,0; 0,0,0,-1; 0,0,-1,0]

/-- Exact generator-level conjugacy between the T48 source D4 action and the
standard signed-permutation realization used by `allD4`. -/
theorem t48D4Simple_conjugacy (k : Fin 4) :
    t48StandardD4Simple k * t48D4BasisChange =
      t48D4BasisChange * t48SourceD4Simple k := by
  native_decide

/-- Source `F_tt` blocks for the four certified E6 facets after the T48 `m+a`
change of basis. -/
def t48FacetTBlock (k : Fin 4) : T48D4Mat :=
  match k.1 with
  | 0 =>
      !![0,0,0,0; 1/3,0,0,0; -1/6,0,0,1/3; 0,0,0,-2/3]
  | 1 =>
      !![1/6,1/2,2/3,1/3;
         0,-1/2,-2/3,-1/3;
         -1/6,0,0,1/3;
         1/3,1/2,2/3,-1/3]
  | 2 =>
      !![1/6,1/2,2/3,1/2;
         0,-1/2,-2/3,-1/3;
         1/6,1/2,2/3,2/3;
         -1/3,-1/2,-2/3,-1]
  | _ =>
      !![1/9,7/18,5/9,2/9;
         1/9,-1/3,-4/9,-2/9;
         -1/6,0,0,1/3;
         2/9,1/3,4/9,-4/9]

/-- Source `F_aa` blocks for the four certified E6 facets. -/
def t48FacetABlock (k : Fin 4) : T48AMat :=
  match k.1 with
  | 0 => !![1/9,2/9; 1/9,2/9]
  | 1 => !![1/6,-1/6; 0,1/6]
  | 2 => !![1/6,0; 0,1/6]
  | _ => !![5/27,-1/54; -1/27,4/27]

/-- The four centralizer normals in the standard signed-permutation basis. -/
def t48FacetStandardNormal (k : Fin 4) : T48D4Mat :=
  match k.1 with
  | 0 =>
      !![0,0,0,0;
         0,-1/3,1/3,1/3;
         0,1/3,-1/3,1/3;
         0,0,0,0]
  | 1 =>
      !![1/12,1/12,1/12,-1/12;
         1/12,-1/4,5/12,1/4;
         -1/12,1/4,-5/12,1/12;
         1/12,1/12,1/12,-1/12]
  | 2 =>
      !![1/12,1/6,0,-1/12;
         -1/12,-1/3,1/6,1/12;
         1/12,1/2,-1/3,1/4;
         1/12,1/6,0,-1/12]
  | _ =>
      !![1/12,1/36,1/12,-1/12;
         1/12,-11/36,5/12,1/4;
         -1/36,1/4,-13/36,5/36;
         1/12,1/36,1/12,-1/12]

/-- Exact covariance of the four source centralizer normals under the displayed
basis change. -/
theorem t48FacetStandardNormal_changeOfBasis (k : Fin 4) :
    t48FacetStandardNormal k =
      t48D4BasisChangeInv.transpose * t48FacetTBlock k *
        t48D4BasisChange.transpose := by
  native_decide

/-- The `a`-block contributes exactly `1/3` for every certified facet. -/
theorem t48FacetABlock_trace (k : Fin 4) :
    Matrix.trace (t48FacetABlock k) = 1/3 := by
  native_decide

/-- Frobenius score of a T48 centralizer normal on the existing exact D4 model. -/
def t48D4Score (k : Fin 4) (ps : D4SignedPerm) : ℚ :=
  d4Frob (t48FacetStandardNormal k) (d4SignedMatrix ps)

/-- Number of exact D4 elements exceeding the source support value `2/3`. -/
def t48D4SupportViolationCount (k : Fin 4) : Nat :=
  (allD4.filter (fun ps => decide ((2/3 : ℚ) < t48D4Score k ps))).card

/-- Number of exact D4 elements attaining the source support value `2/3`. -/
def t48D4ActiveCount (k : Fin 4) : Nat :=
  (allD4.filter (fun ps => decide (t48D4Score k ps = (2/3 : ℚ)))).card

/-- None of the 192 even signed permutations exceeds `2/3` for any of the four
T48 source normals. -/
theorem t48D4SupportViolationCount_zero (k : Fin 4) :
    t48D4SupportViolationCount k = 0 := by
  native_decide

/-- Exact source active counts for the four facets. -/
theorem t48D4ActiveCounts_exact :
    t48D4ActiveCount 0 = 24 ∧
      t48D4ActiveCount 1 = 20 ∧
      t48D4ActiveCount 2 = 16 ∧
      t48D4ActiveCount 3 = 14 := by
  native_decide

/-- Pointwise support bound exposed from the finite certificate. -/
theorem t48D4Score_le_twoThirds (k : Fin 4) (ps : D4SignedPerm)
    (hps : ps ∈ allD4) :
    t48D4Score k ps ≤ (2/3 : ℚ) := by
  by_contra hle
  have hlt : (2/3 : ℚ) < t48D4Score k ps := lt_of_not_ge hle
  have hmem : ps ∈ allD4.filter
      (fun q => decide ((2/3 : ℚ) < t48D4Score k q)) := by
    exact Finset.mem_filter.mpr ⟨hps, by simpa using hlt⟩
  have hpos : 0 < t48D4SupportViolationCount k := by
    exact Finset.card_pos.mpr ⟨ps, hmem⟩
  rw [t48D4SupportViolationCount_zero k] at hpos
  omega

/-- Each of the four support values `2/3` is attained. -/
theorem t48D4Score_twoThirds_attained (k : Fin 4) :
    ∃ ps ∈ allD4, t48D4Score k ps = (2/3 : ℚ) := by
  native_decide

/-- Total zero-sector boundary contribution for a source facet and D4 element. -/
def t48ZeroSectorValue (k : Fin 4) (ps : D4SignedPerm) : ℚ :=
  Matrix.trace (t48FacetABlock k) + t48D4Score k ps

/-- Exact upper bound `1/3+2/3=1` on every one of the 192 centralizer elements. -/
theorem t48ZeroSectorValue_le_one (k : Fin 4) (ps : D4SignedPerm)
    (hps : ps ∈ allD4) :
    t48ZeroSectorValue k ps ≤ 1 := by
  unfold t48ZeroSectorValue
  rw [t48FacetABlock_trace]
  have h := t48D4Score_le_twoThirds k ps hps
  linarith

/-- The zero-sector boundary upper bound is sharp for each of the four facets. -/
theorem t48ZeroSectorValue_one_attained (k : Fin 4) :
    ∃ ps ∈ allD4, t48ZeroSectorValue k ps = 1 := by
  obtain ⟨ps, hps, hscore⟩ := t48D4Score_twoThirds_attained k
  refine ⟨ps, hps, ?_⟩
  unfold t48ZeroSectorValue
  rw [t48FacetABlock_trace, hscore]
  norm_num

/-- Compact statement of the exact finite T48 zero-sector certificate. -/
theorem t48ZeroSectorBoundary_certificate :
    (∀ k : Fin 4, t48D4SupportViolationCount k = 0) ∧
      t48D4ActiveCount 0 = 24 ∧
      t48D4ActiveCount 1 = 20 ∧
      t48D4ActiveCount 2 = 16 ∧
      t48D4ActiveCount 3 = 14 ∧
      (∀ k : Fin 4, Matrix.trace (t48FacetABlock k) = 1/3) := by
  constructor
  · exact t48D4SupportViolationCount_zero
  exact ⟨t48D4ActiveCounts_exact.1,
    t48D4ActiveCounts_exact.2.1,
    t48D4ActiveCounts_exact.2.2.1,
    t48D4ActiveCounts_exact.2.2.2,
    t48FacetABlock_trace⟩

end FormalResearch.QID
