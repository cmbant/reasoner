module

public import ThreeCopyQutritWerner.TwoCutDefs
public import ThreeCopyQutritWerner.Continuation

@[expose] public section


/-!
# The three grouped cut forms of a three-site operator as two-factor cut forms

Manuscript eq. (8): `Q_i(C)` is the two-factor form of the *original* matrix `C` at
the cut `i | {1,2,3} \ {i}`.  Here `cutForm₁ C` is `cutForm C` with `L = a`, `R = b × c`,
and `cutForm₂ C`, `cutForm₃ C` are `cutForm` of `C` with the cut site moved to the
front by a reindexing equivalence.  Reindexing changes neither rank, Frobenius norm
nor trace, so a two-factor rank-two inequality applies to all three cuts of `C`
itself; no rank assumption on a reduced matrix is involved.
-/

noncomputable section

namespace ThreeCopyQutritWerner

section Reindex

variable {m n : Type*} [Fintype m] [Fintype n]

theorem frobSq_submatrix_equiv (e : n ≃ m) (X : Matrix m m ℂ) :
    frobSq (X.submatrix e e) = frobSq X := by
  unfold frobSq
  simp only [Matrix.submatrix_apply]
  exact Fintype.sum_equiv e (fun i => ∑ j, Complex.normSq (X (e i) (e j)))
    (fun i => ∑ j, Complex.normSq (X i j))
    (fun i => Fintype.sum_equiv e (fun j => Complex.normSq (X (e i) (e j)))
      (fun j => Complex.normSq (X (e i) j)) (fun _ => rfl))

theorem trace_submatrix_equiv' (e : n ≃ m) (X : Matrix m m ℂ) :
    (X.submatrix e e).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e (fun i => X (e i) (e i)) (fun i => X i i) (fun _ => rfl)

end Reindex

section Sites

variable {a b c : Type*}

variable [Fintype a] [Fintype b] [Fintype c]

theorem cutForm₁_eq_cutForm (C : Matrix (a × b × c) (a × b × c) ℂ) :
    cutForm₁ C = cutForm C := by
  have h1 : ptrace₁ C = ptraceL C := rfl
  have h2 : ptrace₂₃ C = ptraceR C := by
    ext i i'
    simp only [ptrace₂₃, ptraceR, Fintype.sum_prod_type]
  unfold cutForm₁ cutForm invN invT
  rw [h1, h2]

theorem cutForm₂_eq_cutForm (C : Matrix (a × b × c) (a × b × c) ℂ) :
    cutForm₂ C = cutForm (C.submatrix siteEquiv₂ siteEquiv₂) := by
  have h1 : ptraceL (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₂ C := rfl
  have h2 : ptraceR (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁₃ C := by
    ext j j'
    simp only [ptrace₁₃, ptraceR, Fintype.sum_prod_type]
    first | done | rfl
  unfold cutForm₂ cutForm invN invT
  rw [h1, h2, frobSq_submatrix_equiv, trace_submatrix_equiv']

theorem cutForm₃_eq_cutForm (C : Matrix (a × b × c) (a × b × c) ℂ) :
    cutForm₃ C = cutForm (C.submatrix siteEquiv₃ siteEquiv₃) := by
  have h1 : ptraceL (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₃ C := rfl
  have h2 : ptraceR (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₁₂ C := by
    ext k k'
    simp only [ptrace₁₂, ptraceR, Fintype.sum_prod_type]
    first | done | rfl
  unfold cutForm₃ cutForm invN invT
  rw [h1, h2, frobSq_submatrix_equiv, trace_submatrix_equiv']

theorem rank_submatrix_siteEquiv₂ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    (C.submatrix siteEquiv₂ siteEquiv₂).rank = C.rank :=
  Matrix.rank_submatrix C siteEquiv₂ siteEquiv₂

theorem rank_submatrix_siteEquiv₃ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    (C.submatrix siteEquiv₃ siteEquiv₃).rank = C.rank :=
  Matrix.rank_submatrix C siteEquiv₃ siteEquiv₃

/-- `S(C) ≥ 0` follows from the two-factor form being nonnegative at the three cuts of
`C` (manuscript: `S = (Q₁ + Q₂ + Q₃)/3`). -/
theorem formS_nonneg_of_cutForm_nonneg (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h1 : 0 ≤ cutForm C) (h2 : 0 ≤ cutForm (C.submatrix siteEquiv₂ siteEquiv₂))
    (h3 : 0 ≤ cutForm (C.submatrix siteEquiv₃ siteEquiv₃)) : 0 ≤ formS C := by
  rw [formS_eq_cutForm_average, cutForm₁_eq_cutForm, cutForm₂_eq_cutForm, cutForm₃_eq_cutForm]
  linarith

end Sites

end ThreeCopyQutritWerner

end
