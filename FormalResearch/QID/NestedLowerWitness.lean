import FormalResearch.QID.D4DoublyStochasticCertificate

namespace FormalResearch.QID

/-!
# QI-D nested all-rank lower witness

This module formalizes the exact lower-witness construction used in
`cmbant/QIprojects:QI-D/notes/HADAMARD_NESTED_DS_ALL_N.md`, re-audited through
QIprojects main at `d9c4c3f4f0fd948daaefe186394dc3921c15dafe`.

For rank `n = k + 4`, the source witness is

`A_n = I_k direct_sum A_*`,

where `A_*` is the exact D4 rational witness already formalized in
`D4DoublyStochasticCertificate`.  The nested normal has the D4 exceptional
normal as its bottom-right corner, while every diagonal entry in the leading
`k x k` block is one.  Lean proves the full block definitions and the exact
all-rank pairing

`<N_n,A_n> = k + 14/3 = n + 2/3`.

The source also proves `A_n in DS(W(D_n))` by a generalized-Birkhoff nesting
lemma.  That semantic DS-nesting theorem is not silently recreated here; the
final bridge theorem accepts membership in an abstract predicate `DS`
explicitly.
-/

/-- Canonical block index for rank `k+4`: `k` stabilized coordinates followed
by the D4 core. -/
abbrev NestedIdx (k : Nat) := Fin k ⊕ D4Fin

/-- The block index has the intended rank `k+4`. -/
theorem nestedIdx_card (k : Nat) : Fintype.card (NestedIdx k) = k + 4 := by
  simp [NestedIdx]

/-- Integer D4 exceptional normal `N_4 = 4F`, using the already formalized
facet normal `F`. -/
def d4NestedNormal : Matrix D4Fin D4Fin ℚ :=
  fun i j => 4 * d4FacetNormal i j

/-- The scaled facet is exactly the source's integer D4 nested normal. -/
theorem d4NestedNormal_eq_source :
    d4NestedNormal =
      !![-2,  2,  0, -1;
          2, -2,  0, -1;
         -1, -1, -1,  0;
          0,  0,  0,  1] := by
  native_decide

/-- Exact D4 lower-witness value `<N_4,A_*>=14/3`. -/
theorem d4NestedNormal_witness_value :
    d4Frob d4NestedNormal d4DSWitness = 14 / 3 := by
  native_decide

/-- Leading `k x k` block of the nested normal. -/
def nestedTopLeft (k : Nat) : Matrix (Fin k) (Fin k) ℚ :=
  fun _ _ => 1

/-- Coupling from the stabilized rows to the D4 columns `(x,y,q,z)`.
The last stabilized row is the distinguished row and flips the `x` entry. -/
def nestedTopRight (k : Nat) : Matrix (Fin k) D4Fin ℚ :=
  fun i =>
    ![if i.1 + 1 = k then (-1 : ℚ) else 1,
      1,
      1,
      0]

/-- Coupling from the D4 rows `(u,v,q_r,z_r)` to the stabilized columns.
Only the `q_r` row is nonzero, with value `-1` on every stabilized column. -/
def nestedBottomLeft (k : Nat) : Matrix D4Fin (Fin k) ℚ :=
  fun i _ => (![0, 0, -1, 0] : D4Vec) i

/-- Full nested exceptional normal in canonical block coordinates. -/
def nestedNormal (k : Nat) : Matrix (NestedIdx k) (NestedIdx k) ℚ :=
  Matrix.fromBlocks
    (nestedTopLeft k)
    (nestedTopRight k)
    (nestedBottomLeft k)
    d4NestedNormal

/-- Nested lower witness `I_k direct_sum A_*`. -/
def nestedWitness (k : Nat) : Matrix (NestedIdx k) (NestedIdx k) ℚ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin k) (Fin k) ℚ)
    0
    0
    d4DSWitness

@[simp] theorem nestedNormal_bottomRight (k : Nat) :
    (nestedNormal k).toBlocks₂₂ = d4NestedNormal := by
  simp [nestedNormal]

@[simp] theorem nestedWitness_topLeft (k : Nat) :
    (nestedWitness k).toBlocks₁₁ = (1 : Matrix (Fin k) (Fin k) ℚ) := by
  simp [nestedWitness]

@[simp] theorem nestedWitness_bottomRight (k : Nat) :
    (nestedWitness k).toBlocks₂₂ = d4DSWitness := by
  simp [nestedWitness]

/-- Frobenius pairing on the rank-`k+4` block matrices. -/
def nestedFrob {k : Nat}
    (X Y : Matrix (NestedIdx k) (NestedIdx k) ℚ) : ℚ :=
  ∑ i : NestedIdx k, ∑ j : NestedIdx k, X i j * Y i j

/-- A block-diagonal second argument kills both off-diagonal blocks in the
Frobenius pairing and reduces the leading block to its diagonal. -/
theorem nestedFrob_fromBlocks_diag {k : Nat}
    (A : Matrix (Fin k) (Fin k) ℚ)
    (B : Matrix (Fin k) D4Fin ℚ)
    (C : Matrix D4Fin (Fin k) ℚ)
    (D E : Matrix D4Fin D4Fin ℚ) :
    nestedFrob
        (Matrix.fromBlocks A B C D)
        (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ) 0 0 E)
      = (∑ i : Fin k, A i i) +
        ∑ i : D4Fin, ∑ j : D4Fin, D i j * E i j := by
  classical
  simp [nestedFrob, Matrix.one_apply]

/-- Exact source pairing in offset form: each stabilized coordinate contributes
one, and the D4 core contributes `14/3`. -/
theorem nestedWitness_pairing_offset (k : Nat) :
    nestedFrob (nestedNormal k) (nestedWitness k) = (k : ℚ) + 14 / 3 := by
  unfold nestedNormal nestedWitness
  rw [nestedFrob_fromBlocks_diag]
  rw [show (∑ i : D4Fin, ∑ j : D4Fin,
      d4NestedNormal i j * d4DSWitness i j) =
      d4Frob d4NestedNormal d4DSWitness by rfl]
  rw [d4NestedNormal_witness_value]
  simp [nestedTopLeft]

/-- Rank form of the exact lower-witness value:
`<N_{k+4},A_{k+4}> = (k+4)+2/3`. -/
theorem nestedWitness_pairing_rank (k : Nat) :
    nestedFrob (nestedNormal k) (nestedWitness k) =
      (((k + 4 : Nat) : ℚ) + 2 / 3) := by
  rw [nestedWitness_pairing_offset]
  push_cast
  ring

/-- Explicit semantic boundary.  If an external generalized-Birkhoff layer
supplies membership of the nested witness in a predicate `DS`, Lean combines
that membership with the internally proved exact all-rank pairing. -/
theorem nestedLowerWitness_certificate (k : Nat)
    (DS : Matrix (NestedIdx k) (NestedIdx k) ℚ → Prop)
    (hDS : DS (nestedWitness k)) :
    DS (nestedWitness k) ∧
      nestedFrob (nestedNormal k) (nestedWitness k) =
        (((k + 4 : Nat) : ℚ) + 2 / 3) := by
  exact ⟨hDS, nestedWitness_pairing_rank k⟩

end FormalResearch.QID
