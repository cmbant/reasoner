module

public import ThreeCopyQutritWerner.Witness
public import ThreeCopyQutritWerner.RankBridge

@[expose] public section


/-!
# Elementary consequences

Small unconditional facts used around manuscript Theorem 2.1 and Corollary 2.2:

* the form is nonnegative on every matrix for `α ≤ 0` (the matrix-level content of the case
  `α < 0` in the proof of Corollary 2.2), and equals `N` at `α = 0`;
* the one-factor rank-two inequality `‖C‖_F² - α |Tr C|² ≥ 0` for `α ≤ 1/2`;
* for `α > 1/2` an explicit rank-at-most-two qutrit matrix has negative energy;
* the endpoint value zero is attained, and `w P_E ⊗ M₂ ⊗ M₃` is an endpoint zero for
  arbitrary `M₂`, `M₃` (the product case of manuscript eq. (21));
* three copies and the partial transpose commute.

None of these is the endpoint inequality `0 ≤ q(C)` on rank at most two.
-/

namespace ThreeCopyQutritWerner

theorem frobSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    0 ≤ frobSq M := by
  unfold frobSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem sharpCurve_zero : sharpCurve 0 = 1 := by
  unfold sharpCurve
  norm_num

theorem sharpCurve_half : sharpCurve (1 / 2) = 0 := by
  unfold sharpCurve
  norm_num

theorem sharpCurve_nonneg {α : ℝ} (h1 : α ≤ 1 / 2) : 0 ≤ sharpCurve α := by
  unfold sharpCurve
  exact mul_nonneg (by linarith) (sq_nonneg _)

section ThreeSites

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

theorem invN_nonneg (C : Matrix (a × b × c) (a × b × c) ℂ) : 0 ≤ invN C := by
  unfold invN
  exact frobSq_nonneg C

theorem invA_nonneg (C : Matrix (a × b × c) (a × b × c) ℂ) : 0 ≤ invA C := by
  have h1 := frobSq_nonneg (ptrace₁ C)
  have h2 := frobSq_nonneg (ptrace₂ C)
  have h3 := frobSq_nonneg (ptrace₃ C)
  unfold invA
  linarith

theorem invB_nonneg (C : Matrix (a × b × c) (a × b × c) ℂ) : 0 ≤ invB C := by
  have h1 := frobSq_nonneg (ptrace₁₂ C)
  have h2 := frobSq_nonneg (ptrace₁₃ C)
  have h3 := frobSq_nonneg (ptrace₂₃ C)
  unfold invB
  linarith

theorem invT_nonneg (C : Matrix (a × b × c) (a × b × c) ℂ) : 0 ≤ invT C := by
  unfold invT
  exact Complex.normSq_nonneg _

/-- At `α = 0` the energy is `N` (manuscript, the `α = 0` remark on Theorem 2.1). -/
theorem energy_zero (C : Matrix (a × b × c) (a × b × c) ℂ) : energy 0 C = invN C := by
  unfold energy
  ring

/-- For `α ≤ 0` the form `q_α` is nonnegative on every matrix, with no rank condition. -/
theorem energy_nonneg_of_nonpos (C : Matrix (a × b × c) (a × b × c) ℂ) {α : ℝ}
    (hα : α ≤ 0) : 0 ≤ energy α C := by
  have hN := invN_nonneg C
  have hA := mul_nonneg (neg_nonneg.mpr hα) (invA_nonneg C)
  have hB := mul_nonneg (sq_nonneg α) (invB_nonneg C)
  have hT := mul_nonneg (pow_nonneg (neg_nonneg.mpr hα) 3) (invT_nonneg C)
  unfold energy
  nlinarith [hN, hA, hB, hT]

end ThreeSites

/-- One-factor rank-two inequality: `‖C‖_F² - α |Tr C|² ≥ 0` for rank at most two
and `α ≤ 1/2`, in any finite dimension. -/
theorem frobSq_sub_mul_normSq_trace_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (h : C.rank ≤ 2) {α : ℝ} (hα : α ≤ 1 / 2) :
    0 ≤ frobSq C - α * Complex.normSq C.trace := by
  have key := normSq_trace_le_two_mul_of_rank_le_two C h
  have hT := Complex.normSq_nonneg C.trace
  have hprod := mul_nonneg (sub_nonneg.mpr hα) hT
  unfold frobSq
  nlinarith [key, hT, hprod]

/-- For `α > 1/2` an explicit complex qutrit matrix of rank at most two has negative
energy (manuscript proof of Corollary 2.2, the `α > 1/2` direction at matrix level). -/
theorem exists_rank_le_two_energy_neg {α : ℝ} (hα : 1 / 2 < α) :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ energy α C < 0 := by
  refine ⟨distillWitness, rank_distillWitness, ?_⟩
  rw [energy_distillWitness]
  linarith

/-- The endpoint value zero is attained by a normalized matrix of rank at most two. -/
theorem exists_rank_le_two_endpointEnergy_eq_zero :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ endpointEnergy C = 0 := by
  refine ⟨sharpWitness, rank_sharpWitness, invN_sharpWitness, ?_⟩
  unfold endpointEnergy
  rw [energy_sharpWitness]
  exact sharpCurve_half

/-- Product case of manuscript eq. (21): `w P_E ⊗ M₂ ⊗ M₃` has zero endpoint energy
for arbitrary matrices on the other two sites. -/
theorem endpointEnergy_tensor₃_scaledPlaneProj {b c : Type*} [Fintype b] [Fintype c]
    (M₂ : Matrix b b ℂ) (M₃ : Matrix c c ℂ) :
    endpointEnergy (tensor₃ scaledPlaneProj M₂ M₃) = 0 := by
  unfold endpointEnergy
  rw [energy_tensor₃, frobSq_scaledPlaneProj, normSq_trace_scaledPlaneProj]
  ring

/-- Three copies and the partial transpose commute: `(ρ^{⊗3})^Γ = (ρ^Γ)^{⊗3}`. -/
theorem partialTranspose_tripleCopy {m n : Type*} (ρ : Matrix (m × n) (m × n) ℂ) :
    partialTranspose (tripleCopy ρ) = tripleCopy (partialTranspose ρ) := by
  ext x y
  rfl

end ThreeCopyQutritWerner
