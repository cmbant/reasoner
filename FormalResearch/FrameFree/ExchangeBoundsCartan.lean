import FormalResearch.FrameFree.FilteredGateLaw
import FormalResearch.FrameFree.Sharing

/-!
# Exchange gates as Cartan gates (`thm:heis`, translation part)

The repository carries two gate conventions: `FTG.Ug c = exp(-i ∑ c_j σ_j ⊗ σ_j)` (filtered-gate law) and
`Sharing.Ug C S = C·1 + S·SWAP` (exchange gates).  Since `XX + YY + ZZ = 2 SWAP - 1`,
`FTG.Ug (x,x,x) = e^{ix} (cos 2x - i sin 2x SWAP)` (`FTG_Ug_iso`).
-/

open scoped Matrix Kronecker ComplexConjugate

namespace FormalResearch.FrameFree.ExchangeBounds

open FormalResearch.FrameFree

theorem Pm01 : FTG.Pm 0 * FTG.Pm 1 = -FTG.Pm 2 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [FTG.Pm, FTG.sig, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply]

theorem Pm02 : FTG.Pm 0 * FTG.Pm 2 = -FTG.Pm 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [FTG.Pm, FTG.sig, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply]

theorem Pm12 : FTG.Pm 1 * FTG.Pm 2 = -FTG.Pm 0 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [FTG.Pm, FTG.sig, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply]

/-- `XX + YY + ZZ = 2 SWAP - 1`. -/
theorem Sw_eq : Sharing.Sw = (1 / 2 : ℂ) • (FTG.Pm 0 + FTG.Pm 1 + FTG.Pm 2 + 1) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Sharing.Sw, FTG.Pm, FTG.sig, Matrix.add_apply, Matrix.one_apply,
      Matrix.kroneckerMap_apply] <;> norm_num

theorem FTG_Ug_iso (x : ℝ) :
    FTG.Ug (fun _ => x) = ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) •
      Sharing.Ug (Real.cos (2 * x) : ℝ) (-(Complex.I * (Real.sin (2 * x) : ℝ))) := by
  have h00 := FTG.Pm_sq 0
  have h11 := FTG.Pm_sq 1
  have h22 := FTG.Pm_sq 2
  unfold FTG.Ug
  unfold Sharing.Ug
  rw [Sw_eq]
  simp only [FTG.Uk, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    smul_add, smul_sub, smul_smul]
  simp only [Matrix.mul_assoc, Pm01, Pm02, Pm12, h00, h11, h22, Matrix.neg_mul, smul_neg]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  push_cast
  have hs2 : Complex.sin (x : ℂ) ^ 2 = 1 - Complex.cos (x : ℂ) ^ 2 := by
    linear_combination Complex.cos_sq_add_sin_sq (x : ℂ)
  have hs3 : Complex.sin (x : ℂ) ^ 3 = Complex.sin (x : ℂ) - Complex.sin (x : ℂ) * Complex.cos (x : ℂ) ^ 2 := by
    linear_combination Complex.sin (x : ℂ) * hs2
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  match_scalars <;>
    (ring_nf; try simp only [Complex.I_sq, hI3, hs2, hs3]; try ring_nf)

end FormalResearch.FrameFree.ExchangeBounds
