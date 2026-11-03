module

public import Mathlib

/-!
# Partial transposes of three-qubit operators

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/family.tex`
(proof of `thm:ppt3-family`, "PPT and rank claims", where `X^{T_c}` is the partial transpose on
qubit `c ∈ {A, B, C}`).

Conventions as in `FormalResearch.PPTThreeQubit.Basic`: the basis vector `|abc⟩` has index
`4a + 2b + c`.  The partial transpose on a qubit exchanges the bit of that qubit between the row
and the column index: `(X^{T_A})_{(abc),(a'b'c')} = X_{(a'bc),(ab'c')}`, and similarly for `B`, `C`.
Also the cyclic shift `σ` of the qubits and its relation to the three partial transposes, which
reduces the three PPT tests for a cyclically invariant operator to one.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

/-- The partial transpose on qubit `A` (the most significant bit of the index). -/
def ptA (M : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => M ⟨4 * (j.val / 4) + i.val % 4, by omega⟩ ⟨4 * (i.val / 4) + j.val % 4, by omega⟩

/-- The partial transpose on qubit `B` (the middle bit of the index). -/
def ptB (M : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j =>
    M ⟨4 * (i.val / 4) + 2 * (j.val / 2 % 2) + i.val % 2, by omega⟩
      ⟨4 * (j.val / 4) + 2 * (i.val / 2 % 2) + j.val % 2, by omega⟩

/-- The partial transpose on qubit `C` (the least significant bit of the index). -/
def ptC (M : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => M ⟨2 * (i.val / 2) + j.val % 2, by omega⟩ ⟨2 * (j.val / 2) + i.val % 2, by omega⟩

/-- Composing the three partial transposes gives the full transpose. -/
theorem ptA_ptB_ptC (M : Matrix (Fin 8) (Fin 8) ℂ) : ptA (ptB (ptC M)) = Mᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ptA_ptA (M : Matrix (Fin 8) (Fin 8) ℂ) : ptA (ptA M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ptB_ptB (M : Matrix (Fin 8) (Fin 8) ℂ) : ptB (ptB M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ptC_ptC (M : Matrix (Fin 8) (Fin 8) ℂ) : ptC (ptC M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The cyclic shift of the qubits on indices, `(a, b, c) ↦ (b, c, a)`. -/
def cycShift (i : Fin 8) : Fin 8 := ⟨2 * (i.val % 4) + i.val / 4, by omega⟩

/-- Conjugating by the cyclic shift moves the partial transpose on `A` to the one on `C`. -/
theorem ptA_submatrix_shift (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptA (M.submatrix cycShift cycShift) = (ptC M).submatrix cycShift cycShift := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Conjugating by the square of the cyclic shift moves the partial transpose on `A` to the one
on `B`. -/
theorem ptA_submatrix_shift_shift (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptA (M.submatrix (cycShift ∘ cycShift) (cycShift ∘ cycShift)) =
      (ptB M).submatrix (cycShift ∘ cycShift) (cycShift ∘ cycShift) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cycShift_cube (i : Fin 8) : cycShift (cycShift (cycShift i)) = i := by
  fin_cases i <;> rfl

/-- If `ρ` is invariant under the cyclic shift, the partial transposes on `C` and `B` are
conjugates of that on `A`. -/
theorem ptC_eq_of_shift_invariant (M : Matrix (Fin 8) (Fin 8) ℂ)
    (h : M.submatrix cycShift cycShift = M) :
    ptC M = (ptA M).submatrix (cycShift ∘ cycShift) (cycShift ∘ cycShift) := by
  have h1 : ptA M = (ptC M).submatrix cycShift cycShift := by
    rw [← ptA_submatrix_shift, h]
  rw [h1]
  ext i j
  simp [cycShift_cube]

theorem ptB_eq_of_shift_invariant (M : Matrix (Fin 8) (Fin 8) ℂ)
    (h : M.submatrix cycShift cycShift = M) :
    ptB M = (ptA M).submatrix cycShift cycShift := by
  have h2 : M.submatrix (cycShift ∘ cycShift) (cycShift ∘ cycShift) = M := by
    conv_rhs => rw [← h, ← h]
    ext i j; simp
  have h1 : ptA M = (ptB M).submatrix (cycShift ∘ cycShift) (cycShift ∘ cycShift) := by
    rw [← ptA_submatrix_shift_shift, h2]
  rw [h1]
  ext i j
  simp [cycShift_cube]

end FormalResearch.PPTThreeQubit
