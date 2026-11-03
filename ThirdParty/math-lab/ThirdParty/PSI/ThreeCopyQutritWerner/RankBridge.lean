module

public import ThreeCopyQutritWerner.Continuation
public import ThreeCopyQutritWerner.RankTwo

@[expose] public section


/-!
# Rank-two bridge lemmas

Connects the general matrix facts of `RankTwo` to the model definitions:

* `schmidtRankLE_vec_iff`: manuscript eq. (6), `SR(vec C) = rank C`,
  in the form "Schmidt rank at most `r` iff matrix rank at most `r`";
* `formR_nonneg_of_rank_le_two`: `R(C) ≥ 0` on rank at most two (manuscript
  Section 3, eq. (7)), in arbitrary finite local dimensions.
-/

namespace ThreeCopyQutritWerner

/-- Manuscript eq. (6), `SR(vec C) = rank C`: the Schmidt rank of `vec C` across the
row/column cut is the matrix rank of `C`. -/
theorem schmidtRankLE_vec_iff {A B : Type*} [Fintype A] [Fintype B] (C : Matrix A B ℂ)
    (r : ℕ) : SchmidtRankLE r (vec C) ↔ C.rank ≤ r := by
  rw [rank_le_iff_exists_mul]
  unfold SchmidtRankLE vec
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨Matrix.of fun x k => u k x, Matrix.of fun k y => v k y, ?_⟩
    ext x y
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact h x y
  · rintro ⟨X, B', h⟩
    refine ⟨fun k x => X x k, fun k y => B' k y, fun x y => ?_⟩
    rw [h, Matrix.mul_apply]
    first | done | rfl

section ThreeSites

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- `R(C) = N - T₀/2 ≥ 0` for every complex matrix of rank at most two
(manuscript Section 3), in arbitrary finite local dimensions. -/
theorem formR_nonneg_of_rank_le_two (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h : C.rank ≤ 2) : 0 ≤ formR C := by
  have key := normSq_trace_le_two_mul_of_rank_le_two C h
  unfold formR invN invT frobSq
  linarith

/-- The interval bound with `R ≥ 0` discharged.  Still conditional: the endpoint
inequality `0 ≤ q(C)` and `0 ≤ S(C)` remain explicit hypotheses. -/
theorem sharpCurve_mul_invN_le_energy_of_rank_le_two (C : Matrix (a × b × c) (a × b × c) ℂ)
    (hC : C.rank ≤ 2) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) (hq : 0 ≤ endpointEnergy C)
    (hS : 0 ≤ formS C) : sharpCurve α * invN C ≤ energy α C :=
  sharpCurve_mul_invN_le_energy C h0 h1 hq (formR_nonneg_of_rank_le_two C hC) hS

end ThreeSites

end ThreeCopyQutritWerner
