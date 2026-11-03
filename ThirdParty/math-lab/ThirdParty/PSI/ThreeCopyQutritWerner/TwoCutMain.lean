module

public import ThreeCopyQutritWerner.TwoCutFactor
public import ThreeCopyQutritWerner.TwoCutBalanced
public import ThreeCopyQutritWerner.TwoCutTransport
public import ThreeCopyQutritWerner.Physical

@[expose] public section


/-!
# The cut inequality and `S ≥ 0` on rank at most two

Manuscript Section 3, eq. (8) and Appendix A: the grouped two-factor form is
nonnegative on every complex matrix of rank at most two, in arbitrary finite
dimensions; hence `Q_i(C) ≥ 0` at the three cuts of a three-site matrix and
`S(C) = (Q₁ + Q₂ + Q₃)/3 ≥ 0`.  With `R ≥ 0` this leaves the endpoint inequality
`0 ≤ q(C)` as the only hypothesis of the interval bound.
-/

noncomputable section

namespace ThreeCopyQutritWerner

/-- Manuscript eq. (8) in two-factor form: `cutForm X ≥ 0` for rank at most two. -/
theorem cutForm_nonneg_of_rank_le_two {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] (X : Matrix (L × R) (L × R) ℂ) (h : X.rank ≤ 2) :
    0 ≤ cutForm X := by
  obtain ⟨x₁, x₂, y₁, y₂, hX, h1, h2, hg⟩ := exists_balanced_ketBra X h
  rw [hX]
  exact cutForm_nonneg_of_balanced x₁ x₂ y₁ y₂ h1 h2 hg

section ThreeSites

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- Manuscript eq. (8), cut `1 | 23`. -/
theorem cutForm₁_nonneg_of_rank_le_two (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h : C.rank ≤ 2) : 0 ≤ cutForm₁ C := by
  rw [cutForm₁_eq_cutForm]
  exact cutForm_nonneg_of_rank_le_two C h

/-- Manuscript eq. (8), cut `2 | 13`. -/
theorem cutForm₂_nonneg_of_rank_le_two (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h : C.rank ≤ 2) : 0 ≤ cutForm₂ C := by
  rw [cutForm₂_eq_cutForm]
  exact cutForm_nonneg_of_rank_le_two _ (by rw [rank_submatrix_siteEquiv₂]; exact h)

/-- Manuscript eq. (8), cut `3 | 12`. -/
theorem cutForm₃_nonneg_of_rank_le_two (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h : C.rank ≤ 2) : 0 ≤ cutForm₃ C := by
  rw [cutForm₃_eq_cutForm]
  exact cutForm_nonneg_of_rank_le_two _ (by rw [rank_submatrix_siteEquiv₃]; exact h)

/-- `S(C) ≥ 0` for every complex matrix of rank at most two (manuscript Section 3). -/
theorem formS_nonneg_of_rank_le_two (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h : C.rank ≤ 2) : 0 ≤ formS C := by
  rw [formS_eq_cutForm_average]
  have h1 := cutForm₁_nonneg_of_rank_le_two C h
  have h2 := cutForm₂_nonneg_of_rank_le_two C h
  have h3 := cutForm₃_nonneg_of_rank_le_two C h
  linarith

/-- The interval bound of manuscript Theorem 2.1 at one matrix.  CONDITIONAL: the
endpoint inequality `0 ≤ q(C)` at that matrix is still a hypothesis. -/
theorem sharpCurve_mul_invN_le_energy_of_endpointEnergy_nonneg
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1 / 2) (hq : 0 ≤ endpointEnergy C) : sharpCurve α * invN C ≤ energy α C :=
  sharpCurve_mul_invN_le_energy_of_rank_le_two C hC h0 h1 hq (formS_nonneg_of_rank_le_two C hC)

end ThreeSites

/-- CONDITIONAL on the qutrit endpoint inequality only: no Schmidt-rank-two vector
detects three copies of `ρ_{3,α}` for `0 ≤ α ≤ 1/2`. -/
theorem not_isThreeCopyRankTwoDetectable_werner_three_of_endpoint {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1 / 2)
    (hq : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ endpointEnergy C) :
    ¬ IsThreeCopyRankTwoDetectable (werner 3 α) :=
  not_isThreeCopyRankTwoDetectable_werner_three_of_forms h0 h1 hq
    fun C hC => formS_nonneg_of_rank_le_two C hC

end ThreeCopyQutritWerner

end
