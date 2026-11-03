module

public import ThreeCopyQutritWerner.FamilyI

@[expose] public section


/-!
# The two-factor cut form: definitions

Definitions for manuscript eq. (8) and Appendix A.  An operator `X` on `L ⊗ R` is a
complex matrix indexed by `L × R`; vectors of `L ⊗ R` are functions `L × R → ℂ`.

* `cutForm X = ‖X‖_F² - (‖Tr_L X‖_F² + ‖Tr_R X‖_F²)/2 + |Tr X|²/4` is the grouped
  two-factor form of eq. (8);
* `ptraceNormSq X = ‖P(X)‖²` with `P(X) = (Tr_L X, Tr_R X)`, and `ptraceInner` is its
  polarization `⟨P(A), P(B)⟩`;
* `biDefect u v = ‖u‖²‖v‖² + |⟨v, u⟩|² - ‖P(u v†)‖²`, which equals
  `‖(I - F_L)(I - F_R)(u ⊗ v)‖²/4` (Appendix A), with `F_L`, `F_R` the swaps of the `L`, resp. `R`,
  parts of two replicas.

This file contains definitions only.
-/

noncomputable section

namespace ThreeCopyQutritWerner

/-- The Hilbert–Schmidt inner product `⟨A, B⟩ = ∑ᵢⱼ conj(A i j) B i j`. -/
def hsInner {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (A i j) * B i j

section TwoSite

variable {L R : Type*} [Fintype L] [Fintype R]

/-- `⟨P(A), P(B)⟩ = ⟨Tr_L A, Tr_L B⟩ + ⟨Tr_R A, Tr_R B⟩`. -/
def ptraceInner (A B : Matrix (L × R) (L × R) ℂ) : ℂ :=
  hsInner (ptraceL A) (ptraceL B) + hsInner (ptraceR A) (ptraceR B)

end TwoSite

end ThreeCopyQutritWerner

end
