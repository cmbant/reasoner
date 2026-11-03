module

public import ThreeCopyQutritWerner.Basic

@[expose] public section


/-!
# Partial transpose of the flip and of the Werner state

Manuscript Section 2, used for eq. (6): `F_d^Γ = Ω_d`, hence
`ρ_{d,α}^Γ = (I - α Ω_d) / (d (d - α))`.
-/

namespace ThreeCopyQutritWerner

/-- `F^Γ = Ω`: the partial transpose of the flip is the unnormalized projector onto
`|Ω⟩ = ∑ⱼ |jj⟩`. -/
theorem partialTranspose_swapOp (d : Type*) [DecidableEq d] :
    partialTranspose (swapOp d) = omegaOp d := by
  ext ⟨i, j⟩ ⟨k, l⟩
  have h2 : (i = j ∧ l = k) ↔ (i = j ∧ k = l) :=
    ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  simp only [partialTranspose, swapOp, omegaOp, h2]

/-- `ρ_{d,α}^Γ = (I - α Ω_d) / (d (d - α))`. -/
theorem partialTranspose_werner (d : ℕ) (α : ℝ) :
    partialTranspose (werner d α) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) •
        ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • omegaOp (Fin d)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  have h1 : ((i, l) = (k, j)) ↔ ((i, j) = (k, l)) := by
    simp only [Prod.mk.injEq]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  have h2 : (i = j ∧ l = k) ↔ (i = j ∧ k = l) :=
    ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  simp only [partialTranspose, werner, swapOp, omegaOp, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, smul_eq_mul, h1, h2]

end ThreeCopyQutritWerner
