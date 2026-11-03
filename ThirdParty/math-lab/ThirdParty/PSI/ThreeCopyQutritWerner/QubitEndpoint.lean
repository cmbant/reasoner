module

public import ThreeCopyQutritWerner.Corollaries
public import ThreeCopyQutritWerner.PPTRegion

@[expose] public section


/-!
# The qubit half endpoint is separable (the `d = 2` remark on Theorem 2.1)

Manuscript, the `d = 2` remark on Theorem 2.1: the half endpoint `ρ_{2,1/2}` is separable, and
NPT begins only above it.  The six stabilizer states of `ℂ²` form a 2-design, which gives the
explicit finite separable decomposition (`werner_two_half_eq_sum`)

`ρ_{2,1/2} = ∑ₖ pₖ |uₖ⟩⟨uₖ| ⊗ |wₖ⟩⟨wₖ|`,

with weights `(1/6, 1/6, 1/24, 1/24, 1/24, 1/24)`, `u = (e₀, e₁, (1,1), (1,-1), (1,i), (1,-i))`
and orthogonal partners `w = (e₁, e₀, (1,-1), (1,1), (1,-i), (1,i))`.  NPT exactly above
`α = 1/2` at `d = 2` is `isNPT_werner_iff`.

`IsBipartiteSeparable` (finite nonnegative combinations of tensor products of positive
semidefinite operators) is defined in `Basic.lean`.
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

theorem ketBra_self_posSemidef {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    (ketBra u u).PosSemidef := by
  have h : ketBra u u = Matrix.vecMulVec u (star u) := by
    ext i j
    first | rfl | simp [ketBra, Matrix.vecMulVec_apply, starRingEnd_apply]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star u

/-- The weights of the decomposition. -/
def sepWeight : Fin 6 → ℝ := ![1 / 6, 1 / 6, 1 / 24, 1 / 24, 1 / 24, 1 / 24]

/-- The six stabilizer states, unnormalized: `e₀, e₁, (1,1), (1,-1), (1,i), (1,-i)`. -/
def sepU : Fin 6 → Fin 2 → ℂ :=
  ![![1, 0], ![0, 1], ![1, 1], ![1, -1], ![1, Complex.I], ![1, -Complex.I]]

/-- Their orthogonal partners: `e₁, e₀, (1,-1), (1,1), (1,-i), (1,i)`. -/
def sepW : Fin 6 → Fin 2 → ℂ :=
  ![![0, 1], ![1, 0], ![1, -1], ![1, 1], ![1, -Complex.I], ![1, Complex.I]]

theorem werner_two_half_coeff :
    (((2 : ℕ) : ℂ) * (((2 : ℕ) : ℂ) - (((1 / 2 : ℝ)) : ℂ)))⁻¹ = 1 / 3 := by
  norm_num

set_option maxHeartbeats 4000000 in
/-- `ρ_{2,1/2} = ∑ₖ pₖ |uₖ⟩⟨uₖ| ⊗ |wₖ⟩⟨wₖ|`. -/
theorem werner_two_half_eq_sum :
    werner 2 (1 / 2) = ∑ k : Fin 6, ((sepWeight k : ℝ) : ℂ) •
      (ketBra (sepU k) (sepU k) ⊗ₖ ketBra (sepW k) (sepW k)) := by
  rw [werner, werner_two_half_coeff]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, swapOp, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, ketBra, Fin.sum_univ_six, smul_eq_mul, Prod.mk.injEq]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sepWeight, sepU, sepW] <;>
    first
      | (norm_num; done)
      | (apply Complex.ext <;> simp <;> norm_num; done)
      | (simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
          Complex.inv_re, Complex.inv_im, Complex.normSq_ofNat]; norm_num)

/-- The `d = 2` remark on Theorem 2.1: the half endpoint `ρ_{2,1/2}` is separable. -/
theorem werner_two_half_isSeparable : IsBipartiteSeparable (werner 2 (1 / 2)) := by
  unfold IsBipartiteSeparable
  exact ⟨6, sepWeight, fun k => ketBra (sepU k) (sepU k), fun k => ketBra (sepW k) (sepW k),
    fun k => by fin_cases k <;> norm_num [sepWeight],
    fun k => ketBra_self_posSemidef _, fun k => ketBra_self_posSemidef _,
    werner_two_half_eq_sum⟩

/-- The `d = 2` remark on Theorem 2.1: NPT begins only above the half endpoint. -/
theorem isNPT_werner_two_iff {α : ℝ} (h1 : α ≤ 1) : IsNPT (werner 2 α) ↔ 1 / 2 < α := by
  simpa using isNPT_werner_iff 2 le_rfl α h1

end ThreeCopyQutritWerner

end
