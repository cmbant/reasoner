module

public import ThreeCopyQutritWerner.Product

@[expose] public section


/-!
# Explicit qutrit test matrices

Two explicit rank-at-most-two matrices on `(ℂ³)^{⊗3}` with `N = 1`:

* `sharpWitness = w P_E ⊗ |0⟩⟨0| ⊗ |0⟩⟨0|` has `q_α = (1 - 2α)(1 - α)²`
  (manuscript eq. (5) and the sharpness example of Section 3);
* `distillWitness = w P_E ⊗ |0⟩⟨1| ⊗ |0⟩⟨1|` has `q_α = 1 - 2α`
  (manuscript proof of Corollary 2.2).

Here `E = span(e₀, e₁)` and `w = (1 + i)/2` is the phase `e^{iπ/4}` times `1/√2`.
These are attainment statements only; they do not prove any lower bound.
-/

noncomputable section

namespace ThreeCopyQutritWerner

/-- The coordinate vector `e_k`, `k < 2`, of the two-plane `E = span(e₀, e₁) ⊂ ℂ³`. -/
def planeVec (k : Fin 2) : Fin 3 → ℂ := fun i => if (i : ℕ) = (k : ℕ) then 1 else 0

/-- The scalar `w = (1 + i)/2`, with `|w|² = 1/2`. -/
def halfPhase : ℂ := ⟨1 / 2, 1 / 2⟩

/-- `w P_E`, a phase multiple of `P_E / √2`. -/
def scaledPlaneProj : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => halfPhase * (planeVec 0 i * planeVec 0 j + planeVec 1 i * planeVec 1 j)

/-- The matrix unit `|p⟩⟨q|` on `ℂ³`. -/
def matUnit (p q : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (if i = p then 1 else 0) * (if j = q then 1 else 0)

theorem normSq_halfPhase : Complex.normSq halfPhase = 1 / 2 := by
  unfold halfPhase
  rw [Complex.normSq_mk]
  norm_num

theorem frobSq_scaledPlaneProj : frobSq scaledPlaneProj = 1 := by
  simp only [frobSq, scaledPlaneProj, Complex.normSq_mul, normSq_halfPhase, Fin.sum_univ_three]
  norm_num [planeVec]

theorem trace_scaledPlaneProj : scaledPlaneProj.trace = halfPhase * 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, scaledPlaneProj, Fin.sum_univ_three]
  norm_num [planeVec]
  ring

theorem normSq_trace_scaledPlaneProj : Complex.normSq scaledPlaneProj.trace = 2 := by
  rw [trace_scaledPlaneProj, Complex.normSq_mul, normSq_halfPhase]
  norm_num [Complex.normSq_apply]

theorem frobSq_matUnit_zero_zero : frobSq (matUnit 0 0) = 1 := by
  norm_num [frobSq, matUnit, Fin.sum_univ_three]

theorem trace_matUnit_zero_zero : (matUnit 0 0).trace = 1 := by
  norm_num [Matrix.trace, matUnit, Fin.sum_univ_three]

theorem frobSq_matUnit_zero_one : frobSq (matUnit 0 1) = 1 := by
  norm_num [frobSq, matUnit, Fin.sum_univ_three]

theorem trace_matUnit_zero_one : (matUnit 0 1).trace = 0 := by
  norm_num [Matrix.trace, matUnit, Fin.sum_univ_three]

/-- `w P_E ⊗ |p⟩⟨q| ⊗ |p'⟩⟨q'|` has rank at most two. -/
theorem rank_tensor₃_scaledPlaneProj_matUnit_le (p q p' q' : Fin 3) :
    (tensor₃ scaledPlaneProj (matUnit p q) (matUnit p' q')).rank ≤ 2 := by
  refine rank_le_two_of_eq_mul _
    (Matrix.of fun x k => halfPhase * planeVec k x.1 * (if x.2.1 = p then 1 else 0) *
      (if x.2.2 = p' then 1 else 0))
    (Matrix.of fun k y => planeVec k y.1 * (if y.2.1 = q then 1 else 0) *
      (if y.2.2 = q' then 1 else 0)) ?_
  ext x y
  simp only [tensor₃, scaledPlaneProj, matUnit, Matrix.mul_apply, Matrix.of_apply,
    Fin.sum_univ_two]
  ring

/-- The sharpness witness `w P_E ⊗ |0⟩⟨0| ⊗ |0⟩⟨0|`. -/
def sharpWitness : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  tensor₃ scaledPlaneProj (matUnit 0 0) (matUnit 0 0)

/-- The `α > 1/2` test matrix `w P_E ⊗ |0⟩⟨1| ⊗ |0⟩⟨1|`. -/
def distillWitness : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  tensor₃ scaledPlaneProj (matUnit 0 1) (matUnit 0 1)

theorem rank_sharpWitness : sharpWitness.rank ≤ 2 :=
  rank_tensor₃_scaledPlaneProj_matUnit_le 0 0 0 0

theorem rank_distillWitness : distillWitness.rank ≤ 2 :=
  rank_tensor₃_scaledPlaneProj_matUnit_le 0 1 0 1

theorem invN_sharpWitness : invN sharpWitness = 1 := by
  unfold sharpWitness
  rw [invN_tensor₃, frobSq_scaledPlaneProj, frobSq_matUnit_zero_zero]
  norm_num

theorem invN_distillWitness : invN distillWitness = 1 := by
  unfold distillWitness
  rw [invN_tensor₃, frobSq_scaledPlaneProj, frobSq_matUnit_zero_one]
  norm_num

theorem energy_sharpWitness (α : ℝ) : energy α sharpWitness = sharpCurve α := by
  unfold sharpWitness sharpCurve
  rw [energy_tensor₃, frobSq_scaledPlaneProj, normSq_trace_scaledPlaneProj,
    frobSq_matUnit_zero_zero, trace_matUnit_zero_zero]
  simp only [map_one]
  ring

theorem energy_distillWitness (α : ℝ) : energy α distillWitness = 1 - 2 * α := by
  unfold distillWitness
  rw [energy_tensor₃, frobSq_scaledPlaneProj, normSq_trace_scaledPlaneProj,
    frobSq_matUnit_zero_one, trace_matUnit_zero_one]
  simp only [map_zero]
  ring

/-- Attainment half of manuscript Theorem 2.1 at `d = 3`: for every real `α` a
normalized complex matrix of rank at most two has `q_α = (1 - 2α)(1 - α)²`. -/
theorem exists_rank_le_two_energy_eq_sharpCurve (α : ℝ) :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = sharpCurve α :=
  ⟨sharpWitness, rank_sharpWitness, invN_sharpWitness, energy_sharpWitness α⟩

/-- The test matrix in the proof of manuscript Corollary 2.2 at `d = 3`: a
normalized complex matrix of rank at most two with `q_α = 1 - 2α`, which is
negative exactly when `α > 1/2`. -/
theorem exists_rank_le_two_energy_eq_one_sub_two_mul (α : ℝ) :
    ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 ∧ invN C = 1 ∧ energy α C = 1 - 2 * α :=
  ⟨distillWitness, rank_distillWitness, invN_distillWitness, energy_distillWitness α⟩

end ThreeCopyQutritWerner

end
