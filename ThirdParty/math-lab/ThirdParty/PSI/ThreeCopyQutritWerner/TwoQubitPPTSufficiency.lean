module

public import ThreeCopyQutritWerner.TwoQubitSpinInvariants
public import ThreeCopyQutritWerner.TwoQubitPolygonDeterminant
public import ThreeCopyQutritWerner.TwoQubitHadamard

@[expose] public section


/-! Two-qubit PPT sufficiency for the existing literal partial transpose and
finite positive-product decomposition. There is no spectral, factorization,
ensemble, normalization, or literature theorem in the hypotheses. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace ThreeCopyQutritWerner

/-- Every positive two-qubit operator with positive partial transpose has a
finite decomposition into positive product operators. The zero operator and
singular states are included; trace normalization is unnecessary. -/
theorem twoQubit_ppt_separable
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.PosSemidef) (hpt : (partialTranspose ρ).PosSemidef) :
    IsBipartiteSeparable ρ := by
  classical
  obtain ⟨A, a, hρA, ha, hA⟩ := exists_psd_symmetric_congruence_factor
    ρ twoQubitSpinMatrix hρ twoQubitSpinMatrix_transpose
  have hpoly := twoQubitSpin_polynomial_nonneg_of_ppt A a ha hA
    (by rw [← hρA]; exact hpt)
  let e : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm
  let B : Matrix (Fin 2 × Fin 2) (Fin 4) ℂ := A.submatrix id e
  let b : Fin 4 → ℝ := fun i => a (e i)
  have hBB : B * Bᴴ = A * Aᴴ := by
    change A.submatrix id e * Aᴴ.submatrix e id = A * Aᴴ
    exact Matrix.submatrix_mul_equiv A Aᴴ id e id
  have hB : Bᵀ * twoQubitSpinMatrix * B =
      Matrix.diagonal (fun i => (b i : ℂ)) := by
    calc
      Bᵀ * twoQubitSpinMatrix * B =
          (Aᵀ * twoQubitSpinMatrix * A).submatrix e e := by rfl
      _ = Matrix.diagonal (fun i => (b i : ℂ)) := by
        rw [hA]
        ext i j
        simp [Matrix.submatrix_apply, Matrix.diagonal_apply, b, e.injective.eq_iff]
  have hsum2 : (∑ i, (b i) ^ 2) = ∑ i, (a i) ^ 2 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hsum4 : (∑ i, (b i) ^ 4) = ∑ i, (a i) ^ 4 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hprod : (∏ i, b i) = ∏ i, a i :=
    Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hb : ∀ i, 0 ≤ b i := fun i => ha (e i)
  have hbp : ∀ i, 2 * b i ≤ ∑ j, b j :=
    four_polygon_of_spin_polynomial_nonneg b hb (by rwa [hsum2, hsum4, hprod])
  rw [hρA, ← hBB]
  exact isBipartiteSeparable_of_spin_diagonal_polygon B b hB hb hbp

end ThreeCopyQutritWerner
