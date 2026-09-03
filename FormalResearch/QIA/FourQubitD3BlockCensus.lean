import Mathlib

namespace FormalResearch.QIA

open scoped BigOperators

/-- Conjugacy-class sizes of `S₃`: identity, transpositions, three-cycles. -/
def s3ClassSize : Fin 3 → Int := ![1, 3, 2]

/-- Character of the standard two-dimensional `S₃` representation on the
three conjugacy classes. -/
def s3StandardChar : Fin 3 → Int := ![2, 0, -1]

/-- Numerator of the character average giving the invariant multiplicity in
the `k`-fold tensor power of the standard `S₃` representation.  Division by
`|S₃|=6` gives the generalized-Kronecker multiplicity relevant at three
copies. -/
def s3StandardInvariantNumerator (k : Nat) : Int :=
  ∑ C : Fin 3, s3ClassSize C * (s3StandardChar C) ^ k

/-- The four-qubit, three-copy multiplicity as a function of the number `k` of
local `(2,1)`/standard factors. -/
def fourQubitD3MultiplicityByK (k : Nat) : Nat :=
  match k with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | _ => 0

/-- The multiplicities `1,0,1,1,3` are not table data: through the only
possible values `k≤4`, they are exactly the `S₃` character averages. -/
theorem fourQubitD3_multiplicity_character_certificate :
    ∀ k : Fin 5,
      s3StandardInvariantNumerator k.1 =
        6 * (fourQubitD3MultiplicityByK k.1 : Int) := by
  native_decide

/-- A local-sector tuple is encoded by the subset of the four qubits carrying
the standard `(2,1)` representation. -/
def fourQubitD3BlockDim (S : Finset (Fin 4)) : Nat :=
  fourQubitD3MultiplicityByK S.card

/-- Exact census behind `C^11 ⊕ M₃(C)`: among the 16 local Schur-label tuples,
four vanish, eleven have multiplicity one, and one has multiplicity three. -/
theorem fourQubitD3_block_census :
    (Finset.univ.filter (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 0)).card = 4 ∧
    (Finset.univ.filter (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 1)).card = 11 ∧
    (Finset.univ.filter (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 3)).card = 1 ∧
    (∀ S : Finset (Fin 4),
      fourQubitD3BlockDim S = 0 ∨ fourQubitD3BlockDim S = 1 ∨
        fourQubitD3BlockDim S = 3) := by
  native_decide

/-- The canonical direct-sum multiplicity memory has Hilbert dimension
`11·1+1·3=14`. -/
theorem fourQubitD3_memory_dimension :
    (∑ S : Finset (Fin 4), fourQubitD3BlockDim S) = 14 := by
  native_decide

/-- The full invariant observable algebra has vector-space dimension
`11·1²+1·3²=20`. -/
theorem fourQubitD3_invariant_algebra_dimension :
    (∑ S : Finset (Fin 4), (fourQubitD3BlockDim S)^2) = 20 := by
  native_decide

/-- There are exactly twelve nonzero central/isotypic sectors. -/
theorem fourQubitD3_nonzero_sector_count :
    (Finset.univ.filter
      (fun S : Finset (Fin 4) => fourQubitD3BlockDim S ≠ 0)).card = 12 := by
  native_decide

/-- Real dimension of the conjugation-odd Hermitian sector: a multiplicity-`g`
block contributes `choose g 2`; only the qutrit block contributes, giving 3. -/
theorem fourQubitD3_odd_hermitian_dimension :
    (∑ S : Finset (Fin 4), Nat.choose (fourQubitD3BlockDim S) 2) = 3 := by
  native_decide

/-- Compact certificate containing all numerical invariants of the exact
three-copy block decomposition used in the four-qubit theorem. -/
theorem fourQubitD3_complete_block_certificate :
    (Finset.univ.filter (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 1)).card = 11 ∧
    (Finset.univ.filter (fun S : Finset (Fin 4) => fourQubitD3BlockDim S = 3)).card = 1 ∧
    (∑ S : Finset (Fin 4), fourQubitD3BlockDim S) = 14 ∧
    (∑ S : Finset (Fin 4), (fourQubitD3BlockDim S)^2) = 20 ∧
    (∑ S : Finset (Fin 4), Nat.choose (fourQubitD3BlockDim S) 2) = 3 := by
  exact ⟨fourQubitD3_block_census.2.1,
    fourQubitD3_block_census.2.2.1,
    fourQubitD3_memory_dimension,
    fourQubitD3_invariant_algebra_dimension,
    fourQubitD3_odd_hermitian_dimension⟩

end FormalResearch.QIA
