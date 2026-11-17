module

public import Mathlib

/-!
# Masked Frobenius bounds and the union-mask inequality (Weyl P5/M7, REG.1)

Source: `Weyl/P5/notes/m7_review_and_open_gates.md` §C, **(REG.1)** (PR 250, head `cfad461d2`):
if `‖K^{AG} ∘ U‖_F ≤ ε_AG` and `‖K^{DB} ∘ U‖_F ≤ ε_DB` for two 0-1 entry masks, then the union mask
`K = K^{AG} ∨ K^{DB}` satisfies
`‖K ∘ U‖_{op} ≤ ‖K ∘ U‖_F ≤ (ε_AG² + ε_DB²)^{1/2}`,
"for each entry the squared union indicator is bounded by the sum of the two squared original
indicators; sum and take square roots", for moving, disconnected masks.

* `frobSq M = ∑ᵢⱼ M_ij²`, `maskMul K U = K ∘ U` (entrywise product with a decidable 0-1 mask).
* `frobSq_maskMul_or` : `‖(K₁ ∨ K₂) ∘ U‖_F² ≤ ‖K₁ ∘ U‖_F² + ‖K₂ ∘ U‖_F²`.
* `sq_mulVec_le_frobSq` : `‖M x‖² ≤ ‖M‖_F² ‖x‖²` (Cauchy–Schwarz), and
  `l2_opNorm_le_sqrt_frobSq` : Mathlib's `L2` operator norm is at most `√(frobSq M)`.
* `reg1` : **(REG.1)**, both for `√(frobSq)` and the operator norm.

Claim class: proved.  The statements are for arbitrary real matrices; "Frobenius norm" is
`√(frobSq ·)`, identified with Mathlib's (scoped) Frobenius norm in `frobenius_norm_eq_sqrt_frobSq`.
Not formalised: the AG/DB masks themselves (see `FormalResearch.Jacobi.CombesThomas`, which proves
the generic Dirichlet-block inequality (DB.1) that produces the `DB` mask bound).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace FormalResearch.MatrixAnalysis

open Matrix Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The squared Frobenius norm `∑ᵢⱼ M_ij²`. -/
def frobSq (M : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

theorem frobSq_nonneg (M : Matrix ι κ ℝ) : 0 ≤ frobSq M :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- Entrywise (Hadamard) product `K ∘ U` of a 0-1 mask with a matrix. -/
def maskMul (K : ι → κ → Prop) [∀ i j, Decidable (K i j)] (U : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  Matrix.of fun i j => if K i j then U i j else 0

/-- The union mask: `‖(K₁ ∨ K₂) ∘ U‖_F² ≤ ‖K₁ ∘ U‖_F² + ‖K₂ ∘ U‖_F²`. -/
theorem frobSq_maskMul_or (K₁ K₂ : ι → κ → Prop) [∀ i j, Decidable (K₁ i j)]
    [∀ i j, Decidable (K₂ i j)] (U : Matrix ι κ ℝ) :
    frobSq (maskMul (fun i j => K₁ i j ∨ K₂ i j) U) ≤
      frobSq (maskMul K₁ U) + frobSq (maskMul K₂ U) := by
  unfold frobSq
  rw [← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun j _ => ?_
  simp only [maskMul, Matrix.of_apply]
  by_cases h1 : K₁ i j <;> by_cases h2 : K₂ i j <;> simp [h1, h2]
  all_goals positivity

/-- `‖M x‖² ≤ ‖M‖_F² ‖x‖²` (Cauchy–Schwarz). -/
theorem sq_mulVec_le_frobSq (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    ∑ i, (M *ᵥ x) i ^ 2 ≤ frobSq M * ∑ j, x j ^ 2 := by
  unfold frobSq
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  simpa [mulVec, dotProduct] using sum_mul_sq_le_sq_mul_sq univ (fun j => M i j) x

/-- The `L2` operator norm of Mathlib is at most the Frobenius norm. -/
theorem l2_opNorm_le_of_sq [DecidableEq κ] (M : Matrix ι κ ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : κ → ℝ, ∑ i, (M *ᵥ x) i ^ 2 ≤ C ^ 2 * ∑ j, x j ^ 2) :
    ‖M‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  have := h x.ofLp
  simp only [Real.norm_eq_abs, sq_abs]
  calc _ ≤ √(C ^ 2 * ∑ j, x.ofLp j ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact this
    _ = C * √(∑ j, x.ofLp j ^ 2) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]

theorem l2_opNorm_le_sqrt_frobSq [DecidableEq κ] (M : Matrix ι κ ℝ) : ‖M‖ ≤ √(frobSq M) :=
  l2_opNorm_le_of_sq M (Real.sqrt_nonneg _) fun x => by
    rw [Real.sq_sqrt (frobSq_nonneg M)]; exact sq_mulVec_le_frobSq M x

/-- **(REG.1)** Union of two certified masks.  If `‖K₁ ∘ U‖_F ≤ ε₁` and `‖K₂ ∘ U‖_F ≤ ε₂` then
`‖(K₁ ∨ K₂) ∘ U‖_op ≤ ‖(K₁ ∨ K₂) ∘ U‖_F ≤ (ε₁² + ε₂²)^{1/2}`; no structure of the masks (they may move
with the column, be disconnected, …) is used. -/
theorem reg1 [DecidableEq κ] (K₁ K₂ : ι → κ → Prop) [∀ i j, Decidable (K₁ i j)]
    [∀ i j, Decidable (K₂ i j)] (U : Matrix ι κ ℝ) {ε₁ ε₂ : ℝ}
    (h₁ : √(frobSq (maskMul K₁ U)) ≤ ε₁) (h₂ : √(frobSq (maskMul K₂ U)) ≤ ε₂) :
    ‖maskMul (fun i j => K₁ i j ∨ K₂ i j) U‖ ≤
        √(frobSq (maskMul (fun i j => K₁ i j ∨ K₂ i j) U)) ∧
      √(frobSq (maskMul (fun i j => K₁ i j ∨ K₂ i j) U)) ≤ √(ε₁ ^ 2 + ε₂ ^ 2) := by
  refine ⟨l2_opNorm_le_sqrt_frobSq _, Real.sqrt_le_sqrt ?_⟩
  have e₁ : frobSq (maskMul K₁ U) ≤ ε₁ ^ 2 := (Real.sqrt_le_iff.mp h₁).2
  have e₂ : frobSq (maskMul K₂ U) ≤ ε₂ ^ 2 := (Real.sqrt_le_iff.mp h₂).2
  linarith [frobSq_maskMul_or K₁ K₂ U]

/-- info: 'FormalResearch.MatrixAnalysis.reg1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reg1

end FormalResearch.MatrixAnalysis

section FrobeniusNorm

open scoped Matrix.Norms.Frobenius

/-- `√(frobSq M)` is Mathlib's (scoped) Frobenius norm. -/
theorem FormalResearch.MatrixAnalysis.frobenius_norm_eq_sqrt_frobSq {ι κ : Type*} [Fintype ι]
    [Fintype κ] (M : Matrix ι κ ℝ) :
    ‖M‖ = √(FormalResearch.MatrixAnalysis.frobSq M) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  unfold FormalResearch.MatrixAnalysis.frobSq
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

end FrobeniusNorm
