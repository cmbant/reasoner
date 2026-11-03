module

public import ThreeCopyQutritWerner.Interior

@[expose] public section


/-!
# Every matrix of the shape of eq. (5) attains the sharp curve

Manuscript Section 3: the matrix of eq. (5) has `(N, A, B, T₀) = (1, 4, 5, 2)`
and `q_α = f(α)`.  Here for every two-plane `E`, unit vectors `u`, `v`, phase, and site
placement: such a matrix has rank at most two, `N = 1`, and `q_α = (1 - 2α)(1 - α)²` for every
real `α`.  Together with `isInteriorMinimizerShape_of_isMin` this makes the interior
classification a characterization (still CONDITIONAL on the endpoint inequality).
-/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

section Smul

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

theorem ptrace₁_smul (z : ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁ (z • C) = z • ptrace₁ C := by
  ext y y'
  simp only [ptrace₁, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptrace₂_smul (z : ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂ (z • C) = z • ptrace₂ C := by
  ext y y'
  simp only [ptrace₂, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptrace₃_smul (z : ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₃ (z • C) = z • ptrace₃ C := by
  ext y y'
  simp only [ptrace₃, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptrace₁₂_smul (z : ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₂ (z • C) = z • ptrace₁₂ C := by
  ext y y'
  simp only [ptrace₁₂, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptrace₁₃_smul (z : ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₃ (z • C) = z • ptrace₁₃ C := by
  ext y y'
  simp only [ptrace₁₃, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptrace₂₃_smul (z : ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂₃ (z • C) = z • ptrace₂₃ C := by
  ext y y'
  simp only [ptrace₂₃, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The energy is homogeneous of degree two. -/
theorem energy_smul (z : ℂ) (α : ℝ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    energy α (z • C) = Complex.normSq z * energy α C := by
  simp only [energy, invN, invA, invB, invT, ptrace₁_smul, ptrace₂_smul, ptrace₃_smul,
    ptrace₁₂_smul, ptrace₁₃_smul, ptrace₂₃_smul, frobSq_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.normSq_mul]
  ring

theorem invN_smul (z : ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    invN (z • C) = Complex.normSq z * invN C := by
  simp only [invN, frobSq_smul]

end Smul

section Factors

variable {ι : Type*} [Fintype ι]

theorem frobSq_proj (f₁ f₂ : ι → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1)
    (h12 : braket f₁ f₂ = 0) : frobSq (ketBra f₁ f₁ + ketBra f₂ f₂) = 2 := by
  rw [frobSq_add, frobSq_ketBra_vecNormSq, frobSq_ketBra_vecNormSq, hsInner_ketBra, h12,
    zero_mul, Complex.zero_re, h1, h2]
  norm_num

theorem trace_proj (f₁ f₂ : ι → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) :
    (ketBra f₁ f₁ + ketBra f₂ f₂).trace = 2 := by
  rw [Matrix.trace_add, trace_ketBra, trace_ketBra, braket_self, braket_self, h1, h2]
  norm_num

theorem frobSq_ketBra_unit (u : ι → ℂ) (hu : vecNormSq u = 1) : frobSq (ketBra u u) = 1 := by
  rw [frobSq_ketBra_vecNormSq, hu]
  norm_num

theorem trace_ketBra_unit (u : ι → ℂ) (hu : vecNormSq u = 1) : (ketBra u u).trace = 1 := by
  rw [trace_ketBra, braket_self, hu]
  norm_num

theorem normSq_two_complex : Complex.normSq (2 : ℂ) = 4 := by
  norm_num [Complex.normSq_apply]

end Factors

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Every matrix of the shape of eq. (5) has `N = 1` and `q_α = (1 - 2α)(1 - α)²` for every
real `α`. -/
theorem energy_eq_sharpCurve_of_isInteriorMinimizerShape (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h : IsInteriorMinimizerShape C) (α : ℝ) : invN C = 1 ∧ energy α C = sharpCurve α := by
  obtain ⟨z, hz, hC⟩ := h
  rcases hC with ⟨f₁, f₂, u, v, h1, h2, h12, hu, hv, rfl⟩ |
      ⟨u, f₁, f₂, v, h1, h2, h12, hu, hv, rfl⟩ | ⟨u, v, f₁, f₂, h1, h2, h12, hu, hv, rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [invN_smul, invN_tensor₃, frobSq_proj f₁ f₂ h1 h2 h12, frobSq_ketBra_unit u hu,
        frobSq_ketBra_unit v hv, hz]
      norm_num
    · rw [energy_smul, energy_tensor₃, frobSq_proj f₁ f₂ h1 h2 h12, trace_proj f₁ f₂ h1 h2,
        frobSq_ketBra_unit u hu, trace_ketBra_unit u hu, frobSq_ketBra_unit v hv,
        trace_ketBra_unit v hv, hz, normSq_two_complex, map_one]
      unfold sharpCurve
      ring
  · refine ⟨?_, ?_⟩
    · rw [invN_smul, invN_tensor₃, frobSq_proj f₁ f₂ h1 h2 h12, frobSq_ketBra_unit u hu,
        frobSq_ketBra_unit v hv, hz]
      norm_num
    · rw [energy_smul, energy_tensor₃, frobSq_proj f₁ f₂ h1 h2 h12, trace_proj f₁ f₂ h1 h2,
        frobSq_ketBra_unit u hu, trace_ketBra_unit u hu, frobSq_ketBra_unit v hv,
        trace_ketBra_unit v hv, hz, normSq_two_complex, map_one]
      unfold sharpCurve
      ring
  · refine ⟨?_, ?_⟩
    · rw [invN_smul, invN_tensor₃, frobSq_proj f₁ f₂ h1 h2 h12, frobSq_ketBra_unit u hu,
        frobSq_ketBra_unit v hv, hz]
      norm_num
    · rw [energy_smul, energy_tensor₃, frobSq_proj f₁ f₂ h1 h2 h12, trace_proj f₁ f₂ h1 h2,
        frobSq_ketBra_unit u hu, trace_ketBra_unit u hu, frobSq_ketBra_unit v hv,
        trace_ketBra_unit v hv, hz, normSq_two_complex, map_one]
      unfold sharpCurve
      ring

/-- Every matrix of the shape of eq. (5) has rank at most two. -/
theorem rank_le_two_of_isInteriorMinimizerShape (C : Matrix (a × b × c) (a × b × c) ℂ)
    (h : IsInteriorMinimizerShape C) : C.rank ≤ 2 := by
  obtain ⟨z, -, hC⟩ := h
  rcases hC with ⟨f₁, f₂, u, v, -, -, -, -, -, rfl⟩ |
      ⟨u, f₁, f₂, v, -, -, -, -, -, rfl⟩ | ⟨u, v, f₁, f₂, -, -, -, -, -, rfl⟩
  · refine rank_le_two_of_eq_mul _
      (Matrix.of fun x k => z * (![f₁, f₂] k) x.1 * u x.2.1 * v x.2.2)
      (Matrix.of fun k y => conj ((![f₁, f₂] k) y.1) * conj (u y.2.1) * conj (v y.2.2)) ?_
    ext x y
    simp only [Matrix.smul_apply, smul_eq_mul, tensor₃, Matrix.add_apply, ketBra,
      Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  · refine rank_le_two_of_eq_mul _
      (Matrix.of fun x k => z * u x.1 * (![f₁, f₂] k) x.2.1 * v x.2.2)
      (Matrix.of fun k y => conj (u y.1) * conj ((![f₁, f₂] k) y.2.1) * conj (v y.2.2)) ?_
    ext x y
    simp only [Matrix.smul_apply, smul_eq_mul, tensor₃, Matrix.add_apply, ketBra,
      Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  · refine rank_le_two_of_eq_mul _
      (Matrix.of fun x k => z * u x.1 * v x.2.1 * (![f₁, f₂] k) x.2.2)
      (Matrix.of fun k y => conj (u y.1) * conj (v y.2.1) * conj ((![f₁, f₂] k) y.2.2)) ?_
    ext x y
    simp only [Matrix.smul_apply, smul_eq_mul, tensor₃, Matrix.add_apply, ketBra,
      Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring

end ThreeCopyQutritWerner

end
