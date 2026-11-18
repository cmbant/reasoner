module

public import Mathlib
public import FormalResearch.MatrixAnalysis.JacobiOpSchur

/-!
# Paper J, Theorem B reduction: Schur multiplier norm (definitions)

Paper J (`/home/user/scratch/paperJ2/thmB.tex`, section "Three lemmas on matrices"): for a real matrix
`Φ` the Schur multiplier norm is `‖Φ‖_S = sup {‖Φ ∘ Y‖ : ‖Y‖ ≤ 1}`.  Here the matrix norm is the
`L2` operator norm (`Matrix.Norms.L2Operator`) and `∘` is `Matrix.hadamard` (`⊙`).

* `IsSchurBdd Φ K` : `0 ≤ K` and `‖Φ ⊙ Y‖ ≤ K ‖Y‖` for all `Y` (so `‖Φ‖_S ≤ K`).
  It is definitionally `FormalResearch.MatrixAnalysis.jop_IsSchurBdd` (the Jacobi-operator package),
  see `isSchurBdd_iff_jop`.
* closure: monotone in `K`, sums, Hadamard products (constants multiply), constants, rank-one
  multipliers `Φ n k = a n` and `Φ n k = b k`.

Rows and columns are arbitrary finite index types (the paper's `Fin D` is a special case); no sub-type
indexing is needed.  Not formalised here: the Schur norm as an infimum (only the bound predicate).
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- `‖Φ‖_S ≤ K`: the Schur multiplier norm of `Φ` is at most `K` (Paper J, section 4.1). -/
def IsSchurBdd (Φ : Matrix ι κ ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ Y : Matrix ι κ ℝ, ‖Φ ⊙ Y‖ ≤ K * ‖Y‖

theorem isSchurBdd_iff_jop [DecidableEq ι] (Φ : Matrix ι κ ℝ) (K : ℝ) :
    IsSchurBdd Φ K ↔ FormalResearch.MatrixAnalysis.jop_IsSchurBdd Φ K := Iff.rfl

theorem IsSchurBdd.nonneg {Φ : Matrix ι κ ℝ} {K : ℝ} (h : IsSchurBdd Φ K) : 0 ≤ K := h.1

theorem IsSchurBdd.apply_le {Φ : Matrix ι κ ℝ} {K : ℝ} (h : IsSchurBdd Φ K) (Y : Matrix ι κ ℝ) :
    ‖Φ ⊙ Y‖ ≤ K * ‖Y‖ := h.2 Y

theorem IsSchurBdd.mono {Φ : Matrix ι κ ℝ} {K K' : ℝ} (h : IsSchurBdd Φ K) (hK : K ≤ K') :
    IsSchurBdd Φ K' :=
  ⟨h.1.trans hK, fun Y => (h.2 Y).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))⟩

theorem IsSchurBdd.add {Φ Ψ : Matrix ι κ ℝ} {K L : ℝ} (hΦ : IsSchurBdd Φ K) (hΨ : IsSchurBdd Ψ L) :
    IsSchurBdd (Φ + Ψ) (K + L) := by
  refine ⟨add_nonneg hΦ.1 hΨ.1, fun Y => ?_⟩
  rw [Matrix.add_hadamard]
  calc ‖Φ ⊙ Y + Ψ ⊙ Y‖ ≤ ‖Φ ⊙ Y‖ + ‖Ψ ⊙ Y‖ := norm_add_le _ _
    _ ≤ K * ‖Y‖ + L * ‖Y‖ := add_le_add (hΦ.2 Y) (hΨ.2 Y)
    _ = (K + L) * ‖Y‖ := by ring

/-- Schur bounds multiply under Hadamard product: `‖Φ ∘ Ψ‖_S ≤ ‖Φ‖_S ‖Ψ‖_S`. -/
theorem IsSchurBdd.hadamard {Φ Ψ : Matrix ι κ ℝ} {K L : ℝ} (hΦ : IsSchurBdd Φ K)
    (hΨ : IsSchurBdd Ψ L) : IsSchurBdd (Φ ⊙ Ψ) (K * L) := by
  refine ⟨mul_nonneg hΦ.1 hΨ.1, fun Y => ?_⟩
  rw [Matrix.hadamard_assoc]
  calc ‖Φ ⊙ (Ψ ⊙ Y)‖ ≤ K * ‖Ψ ⊙ Y‖ := hΦ.2 _
    _ ≤ K * (L * ‖Y‖) := mul_le_mul_of_nonneg_left (hΨ.2 Y) hΦ.1
    _ = K * L * ‖Y‖ := by ring

/-- The constant matrix `1` (all entries one) has Schur norm `≤ 1`. -/
theorem isSchurBdd_one : IsSchurBdd (Matrix.of fun (_ : ι) (_ : κ) => (1 : ℝ)) 1 := by
  refine ⟨zero_le_one, fun Y => ?_⟩
  have : (Matrix.of fun (_ : ι) (_ : κ) => (1 : ℝ)) ⊙ Y = Y := by
    ext n k; simp
  rw [this]; simp

/-- A constant matrix `c` has Schur norm `≤ |c|`. -/
theorem isSchurBdd_const (c : ℝ) : IsSchurBdd (Matrix.of fun (_ : ι) (_ : κ) => c) |c| := by
  refine ⟨abs_nonneg _, fun Y => ?_⟩
  have : (Matrix.of fun (_ : ι) (_ : κ) => c) ⊙ Y = c • Y := by
    ext n k; simp
  rw [this, norm_smul, Real.norm_eq_abs]

/-- Rank-one multiplier depending on the row only: `Φ n k = a n`, `K = sup |a|`. -/
theorem IsSchurBdd.rank_one_left [DecidableEq ι] (a : ι → ℝ) {K : ℝ} (hK : 0 ≤ K) (h : ∀ n, |a n| ≤ K) :
    IsSchurBdd (Matrix.of fun (n : ι) (_ : κ) => a n) K := by
  refine ⟨hK, fun Y => ?_⟩
  have : (Matrix.of fun (n : ι) (_ : κ) => a n) ⊙ Y = diagonal a * Y := by
    ext n k; simp [Matrix.diagonal_mul]
  rw [this]
  refine (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact FormalResearch.MatrixAnalysis.jop_norm_diagonal_le a hK h

/-- Rank-one multiplier depending on the column only: `Φ n k = b k`, `K = sup |b|`. -/
theorem IsSchurBdd.rank_one_right (b : κ → ℝ) {K : ℝ} (hK : 0 ≤ K) (h : ∀ k, |b k| ≤ K) :
    IsSchurBdd (Matrix.of fun (_ : ι) (k : κ) => b k) K := by
  refine ⟨hK, fun Y => ?_⟩
  have : (Matrix.of fun (_ : ι) (k : κ) => b k) ⊙ Y = Y * diagonal b := by
    ext n k; simp [Matrix.mul_diagonal, mul_comm]
  rw [this]
  refine (l2_opNorm_mul _ _).trans ?_
  have := FormalResearch.MatrixAnalysis.jop_norm_diagonal_le b hK h
  nlinarith [norm_nonneg Y]

end FormalResearch.JB
