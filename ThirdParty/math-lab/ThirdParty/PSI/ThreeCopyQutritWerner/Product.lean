module

public import ThreeCopyQutritWerner.Basic

@[expose] public section


/-!
# Product operators: the three-copy energy factorizes

For a product operator `M₁ ⊗ M₂ ⊗ M₃` every invariant in manuscript eq. (2)
factorizes, hence `q_α(M₁ ⊗ M₂ ⊗ M₃) = ∏ᵢ (‖Mᵢ‖_F² - α |Tr Mᵢ|²)`.  This is the
factorization used for the sharpness example of Section 3, for the
`α > 1/2` test matrix in Corollary 2.2, and for family I (eq. (21)).  Valid in arbitrary
finite local dimensions.
-/

namespace ThreeCopyQutritWerner

section Helpers

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sum_prod_mul (f : ι → ι → ℝ) (g : κ → κ → ℝ) :
    ∑ x : ι × κ, ∑ y : ι × κ, f x.1 y.1 * g x.2 y.2 =
      (∑ i, ∑ i', f i i') * (∑ j, ∑ j', g j j') := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem sum_prod_single (f : ι → ℂ) (g : κ → ℂ) :
    ∑ x : ι × κ, f x.1 * g x.2 = (∑ i, f i) * (∑ j, g j) := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem frobSq_smul {m n : Type*} [Fintype m] [Fintype n] (z : ℂ) (M : Matrix m n ℂ) :
    frobSq (z • M) = Complex.normSq z * frobSq M := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem frobSq_tensor₂ (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ) :
    frobSq (tensor₂ M N) = frobSq M * frobSq N := by
  have h := sum_prod_mul (fun i i' => Complex.normSq (M i i'))
    (fun j j' => Complex.normSq (N j j'))
  simp only [frobSq, tensor₂, Complex.normSq_mul]
  exact h

end Helpers

section Tensor

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
variable (M₁ : Matrix a a ℂ) (M₂ : Matrix b b ℂ) (M₃ : Matrix c c ℂ)

theorem tensor₃_eq_tensor₂ :
    tensor₃ M₁ M₂ M₃ = tensor₂ M₁ (tensor₂ M₂ M₃) := by
  ext x y
  simp only [tensor₃, tensor₂, mul_assoc]

theorem frobSq_tensor₃ :
    frobSq (tensor₃ M₁ M₂ M₃) = frobSq M₁ * (frobSq M₂ * frobSq M₃) := by
  rw [tensor₃_eq_tensor₂, frobSq_tensor₂, frobSq_tensor₂]

theorem trace_tensor₃ :
    (tensor₃ M₁ M₂ M₃).trace = M₁.trace * (M₂.trace * M₃.trace) := by
  simp only [Matrix.trace, Matrix.diag_apply, tensor₃, mul_assoc]
  rw [← sum_prod_single (fun j => M₂ j j) (fun k => M₃ k k)]
  exact sum_prod_single (fun i => M₁ i i) (fun p : b × c => M₂ p.1 p.1 * M₃ p.2 p.2)

theorem ptrace₁_tensor₃ : ptrace₁ (tensor₃ M₁ M₂ M₃) = M₁.trace • tensor₂ M₂ M₃ := by
  ext y y'
  simp only [ptrace₁, tensor₃, tensor₂, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  first | done | exact Finset.sum_congr rfl fun i _ => by ring

theorem ptrace₂_tensor₃ : ptrace₂ (tensor₃ M₁ M₂ M₃) = M₂.trace • tensor₂ M₁ M₃ := by
  ext x x'
  simp only [ptrace₂, tensor₃, tensor₂, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  first | done | exact Finset.sum_congr rfl fun i _ => by ring

theorem ptrace₃_tensor₃ : ptrace₃ (tensor₃ M₁ M₂ M₃) = M₃.trace • tensor₂ M₁ M₂ := by
  ext x x'
  simp only [ptrace₃, tensor₃, tensor₂, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  first | done | exact Finset.sum_congr rfl fun i _ => by ring

theorem ptrace₁₂_tensor₃ : ptrace₁₂ (tensor₃ M₁ M₂ M₃) = (M₁.trace * M₂.trace) • M₃ := by
  ext k k'
  simp only [ptrace₁₂, tensor₃, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  first | done | exact Finset.sum_congr rfl fun j _ => by ring

theorem ptrace₁₃_tensor₃ : ptrace₁₃ (tensor₃ M₁ M₂ M₃) = (M₁.trace * M₃.trace) • M₂ := by
  ext j j'
  simp only [ptrace₁₃, tensor₃, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  first | done | exact Finset.sum_congr rfl fun k _ => by ring

theorem ptrace₂₃_tensor₃ : ptrace₂₃ (tensor₃ M₁ M₂ M₃) = (M₂.trace * M₃.trace) • M₁ := by
  ext i i'
  simp only [ptrace₂₃, tensor₃, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  first | done | exact Finset.sum_congr rfl fun k _ => by ring

/-- The energy of a product operator factorizes over the three sites. -/
theorem energy_tensor₃ (α : ℝ) :
    energy α (tensor₃ M₁ M₂ M₃) =
      (frobSq M₁ - α * Complex.normSq M₁.trace) *
        ((frobSq M₂ - α * Complex.normSq M₂.trace) *
          (frobSq M₃ - α * Complex.normSq M₃.trace)) := by
  simp only [energy, invN, invA, invB, invT, frobSq_tensor₃, trace_tensor₃, ptrace₁_tensor₃,
    ptrace₂_tensor₃, ptrace₃_tensor₃, ptrace₁₂_tensor₃, ptrace₁₃_tensor₃, ptrace₂₃_tensor₃,
    frobSq_smul, frobSq_tensor₂, Complex.normSq_mul]
  ring

/-- `N` of a product operator. -/
theorem invN_tensor₃ :
    invN (tensor₃ M₁ M₂ M₃) = frobSq M₁ * (frobSq M₂ * frobSq M₃) := by
  simp only [invN, frobSq_tensor₃]

end Tensor

/-- A matrix with an explicit width-two factorization has rank at most two. -/
theorem rank_le_two_of_eq_mul {m n : Type*} [Fintype m] [Fintype n] (C : Matrix m n ℂ)
    (X : Matrix m (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ) (h : C = X * B) : C.rank ≤ 2 := by
  rw [h]
  exact (Matrix.rank_mul_le_left X B).trans (by simpa using X.rank_le_card_width)

end ThreeCopyQutritWerner
