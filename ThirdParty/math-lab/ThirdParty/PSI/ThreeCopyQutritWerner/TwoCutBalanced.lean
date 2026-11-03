module

public import ThreeCopyQutritWerner.TwoCutRotate
public import ThreeCopyQutritWerner.TwoCutIdentity
public import ThreeCopyQutritWerner.Elementary

@[expose] public section


/-!
# The two-factor form is nonnegative on balanced factors

Manuscript Appendix A, eq. (29): for `C = x₁ y₁† + x₂ y₂†` with equal Gram matrices
`X†X = Y†Y`, the grouped two-factor form `cutForm C` is a sum of nonnegative terms.  The
common unitary of `TwoCutRotate` supplies the equal-diagonal normalization, the identity
of `TwoCutIdentity` is eq. (29), and `biDefect_nonneg` is `e ≥ 0`.

This is a statement about matrices given in balanced factorized form.  That every
matrix of rank at most two has such a factorization is a separate step.
-/

noncomputable section

namespace ThreeCopyQutritWerner

variable {L R : Type*} [Fintype L] [Fintype R]

theorem ptraceNormSq_nonneg (X : Matrix (L × R) (L × R) ℂ) : 0 ≤ ptraceNormSq X := by
  unfold ptraceNormSq
  exact add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)

/-- Appendix A, eq. (29): `cutForm (x₁ y₁† + x₂ y₂†) ≥ 0` for balanced factors. -/
theorem cutForm_nonneg_of_balanced (x₁ x₂ y₁ y₂ : L × R → ℂ)
    (h1 : vecNormSq x₁ = vecNormSq y₁) (h2 : vecNormSq x₂ = vecNormSq y₂)
    (hg : braket x₁ x₂ = braket y₁ y₂) :
    0 ≤ cutForm (ketBra x₁ y₁ + ketBra x₂ y₂) := by
  obtain ⟨x₁', x₂', y₁', y₂', hsum, h1', h2', hg', hτ⟩ :=
    exists_equal_diagonal x₁ x₂ y₁ y₂ h1 h2 hg
  rw [← hsum, cutForm_ketBra_add x₁' x₂' y₁' y₂' (vecNormSq x₁') (vecNormSq x₂')
    (braket x₁' x₂') (braket y₁' x₁') rfl h1'.symm rfl h2'.symm rfl hg'.symm rfl hτ.symm]
  have e1 := biDefect_nonneg x₁' y₁'
  have e2 := biDefect_nonneg x₂' y₂'
  have e3 := biDefect_nonneg x₂' x₁'
  have e4 := biDefect_nonneg y₂' y₁'
  have e5 := ptraceNormSq_nonneg (ketBra x₂' x₁' - ketBra y₂' y₁')
  have e6 := Complex.normSq_nonneg (braket x₁' x₂')
  have e7 := sq_nonneg (vecNormSq x₁' - vecNormSq x₂')
  linarith

end ThreeCopyQutritWerner

end
