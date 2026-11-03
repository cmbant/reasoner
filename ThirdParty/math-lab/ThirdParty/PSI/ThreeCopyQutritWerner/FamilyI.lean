module

public import ThreeCopyQutritWerner.Witness

@[expose] public section


/-!
# Family I endpoint zeros

Manuscript eq. (21): `C = (P_E/√2) ⊗ |χ⟩⟨η|` is a normalized endpoint zero of
rank at most two for arbitrary unit vectors `χ`, `η` on the other two sites,
entangled or not.  Here the active site is site 1 and `P_E/√2` carries the
phase `w` of `Witness.lean`.

The general fact behind it: for `M₁` on site 1 and an arbitrary operator `X`
on sites 2 and 3, `q_α(M₁ ⊗ X)` is the one-site factor of `M₁` times the
two-site form of `X`; the one-site factor of `P_E/√2` vanishes at the endpoint
`α = 1/2`.
-/

noncomputable section

namespace ThreeCopyQutritWerner

section TwoSite

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

variable (M₁ : Matrix a a ℂ) (X : Matrix (b × c) (b × c) ℂ)

theorem trace_tensor₂ : (tensor₂ M₁ X).trace = M₁.trace * X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, tensor₂]
  exact sum_prod_single (fun i => M₁ i i) (fun p => X p p)

theorem ptrace₁_tensor₂ : ptrace₁ (tensor₂ M₁ X) = M₁.trace • X := by
  ext y y'
  simp only [ptrace₁, tensor₂, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul]
  exact (Finset.sum_mul _ _ _).symm

theorem ptrace₂_tensor₂ : ptrace₂ (tensor₂ M₁ X) = tensor₂ M₁ (ptraceL X) := by
  ext x x'
  simp only [ptrace₂, tensor₂, ptraceL]
  exact (Finset.mul_sum _ _ _).symm

theorem ptrace₃_tensor₂ : ptrace₃ (tensor₂ M₁ X) = tensor₂ M₁ (ptraceR X) := by
  ext x x'
  simp only [ptrace₃, tensor₂, ptraceR]
  exact (Finset.mul_sum _ _ _).symm

theorem ptrace₁₂_tensor₂ : ptrace₁₂ (tensor₂ M₁ X) = M₁.trace • ptraceL X := by
  ext k k'
  simp only [ptrace₁₂, tensor₂, ptraceL, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact (Finset.sum_mul_sum _ _ _ _).symm

theorem ptrace₁₃_tensor₂ : ptrace₁₃ (tensor₂ M₁ X) = M₁.trace • ptraceR X := by
  ext j j'
  simp only [ptrace₁₃, tensor₂, ptraceR, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact (Finset.sum_mul_sum _ _ _ _).symm

theorem ptrace₂₃_tensor₂ : ptrace₂₃ (tensor₂ M₁ X) = X.trace • M₁ := by
  ext i i'
  simp only [ptrace₂₃, tensor₂, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The energy of `M₁ ⊗ X`, with `X` an arbitrary operator on sites 2 and 3. -/
theorem energy_tensor₂ (α : ℝ) :
    energy α (tensor₂ M₁ X) =
      (frobSq M₁ - α * Complex.normSq M₁.trace) *
        (frobSq X - α * (frobSq (ptraceL X) + frobSq (ptraceR X)) +
          α ^ 2 * Complex.normSq X.trace) := by
  simp only [energy, invN, invA, invB, invT, frobSq_tensor₂, trace_tensor₂, ptrace₁_tensor₂,
    ptrace₂_tensor₂, ptrace₃_tensor₂, ptrace₁₂_tensor₂, ptrace₁₃_tensor₂, ptrace₂₃_tensor₂,
    frobSq_smul, Complex.normSq_mul]
  ring

end TwoSite

theorem frobSq_ketBra {ι : Type*} [Fintype ι] (χ η : ι → ℂ) :
    frobSq (ketBra χ η) = (∑ y, Complex.normSq (χ y)) * ∑ y, Complex.normSq (η y) := by
  simp only [frobSq, ketBra, Complex.normSq_mul, Complex.normSq_conj, Finset.sum_mul_sum]

theorem rank_tensor₂_scaledPlaneProj_ketBra_le {κ : Type*} [Fintype κ] (χ η : κ → ℂ) :
    (tensor₂ scaledPlaneProj (ketBra χ η)).rank ≤ 2 := by
  refine rank_le_two_of_eq_mul _
    (Matrix.of fun x k => halfPhase * planeVec k x.1 * χ x.2)
    (Matrix.of fun k y => planeVec k y.1 * (starRingEnd ℂ) (η y.2)) ?_
  ext x y
  simp only [tensor₂, scaledPlaneProj, ketBra, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]
  ring

/-- Manuscript eq. (21), with site 1 active: for arbitrary unit vectors `χ`, `η` on
sites 2 and 3, `w P_E ⊗ |χ⟩⟨η|` has rank at most two, `N = 1`, and endpoint energy zero. -/
theorem familyI_endpoint_zero {b c : Type*} [Fintype b] [Fintype c] (χ η : b × c → ℂ)
    (hχ : ∑ y, Complex.normSq (χ y) = 1) (hη : ∑ y, Complex.normSq (η y) = 1) :
    (tensor₂ scaledPlaneProj (ketBra χ η)).rank ≤ 2 ∧
      invN (tensor₂ scaledPlaneProj (ketBra χ η)) = 1 ∧
      endpointEnergy (tensor₂ scaledPlaneProj (ketBra χ η)) = 0 := by
  refine ⟨rank_tensor₂_scaledPlaneProj_ketBra_le χ η, ?_, ?_⟩
  · unfold invN
    rw [frobSq_tensor₂, frobSq_scaledPlaneProj, frobSq_ketBra, hχ, hη]
    norm_num
  · unfold endpointEnergy
    rw [energy_tensor₂, frobSq_scaledPlaneProj, normSq_trace_scaledPlaneProj]
    ring

end ThreeCopyQutritWerner

end
