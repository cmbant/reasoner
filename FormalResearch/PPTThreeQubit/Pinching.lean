module

public import FormalResearch.PPTThreeQubit.TraceDistance
public import FormalResearch.MatrixAnalysis.TraceNormGeneral

/-!
# `eq:ppt3-pinch` in the paper's form

For the triplet/singlet projectors `P₃ = (1 + S_BC)/2`, `P₁ = (1 - S_BC)/2` of `BC`,
`P₃ρP₁ + P₁ρP₃ = (ρ - S_BC ρ S_BC)/2`, so

* `bsDist_le_tnormG_P3P1`: `D(ρ, BS) ≤ ‖P₃ ρ P₁‖₁` for every PSD, `A|BC`-PPT, unit-trace `ρ`
  (`eq:ppt3-pinch`, `cor:ppt3-symmetrisation` (c)), with the trace norm `MatrixAnalysis.tnormG`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.MatrixAnalysis
open scoped ComplexOrder

noncomputable section

/-! ### The triplet/singlet pinching -/

/-- The swap `S_BC` of the qubits `B`, `C` as a permutation matrix. -/
def swapMat : Matrix (Fin 8) (Fin 8) ℂ := Matrix.of fun i j => if i = swapBC j then 1 else 0

theorem swapBC_eq_iff (i j : Fin 8) : i = swapBC j ↔ j = swapBC i := by
  constructor
  · rintro rfl; rw [swapBC_swapBC]
  · rintro rfl; rw [swapBC_swapBC]

theorem swapMat_mul (M : Matrix (Fin 8) (Fin 8) ℂ) : swapMat * M = M.submatrix swapBC id := by
  ext i j
  simp only [swapMat, Matrix.mul_apply, Matrix.of_apply, submatrix_apply, id]
  rw [Finset.sum_eq_single (swapBC i)]
  · simp [swapBC_swapBC]
  · intro k _ hk
    rw [ite_eq_right, zero_mul]
    intro h; exact hk ((swapBC_eq_iff i k).1 h)
  · simp

theorem mul_swapMat (M : Matrix (Fin 8) (Fin 8) ℂ) : M * swapMat = M.submatrix id swapBC := by
  ext i j
  simp only [swapMat, Matrix.mul_apply, Matrix.of_apply, submatrix_apply, id]
  rw [Finset.sum_eq_single (swapBC j)]
  · simp
  · intro k _ hk
    rw [ite_eq_right, mul_zero]
    intro h; exact hk h
  · simp

theorem swapMat_conj (ρ : Matrix (Fin 8) (Fin 8) ℂ) :
    swapMat * ρ * swapMat = ρ.submatrix swapBC swapBC := by
  rw [mul_swapMat, swapMat_mul]; ext i j; simp

theorem swapMat_herm : swapMatᴴ = swapMat := by
  ext i j
  simp only [swapMat, conjTranspose_apply, Matrix.of_apply]
  by_cases h : j = swapBC i
  · rw [ite_eq_left h, ite_eq_left ((swapBC_eq_iff i j).2 h)]; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((swapBC_eq_iff i j).1 h'))]; simp

/-- The triplet projector of `BC`: `P₃ = (1 + S_BC)/2`. -/
def P3 : Matrix (Fin 8) (Fin 8) ℂ := (1 / 2 : ℝ) • (1 + swapMat)

/-- The singlet projector of `BC`: `P₁ = (1 - S_BC)/2`. -/
def P1 : Matrix (Fin 8) (Fin 8) ℂ := (1 / 2 : ℝ) • (1 - swapMat)

theorem pinch_offdiag {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.IsHermitian) :
    P3 * ρ * P1 + (P3 * ρ * P1)ᴴ = (1 / 2 : ℝ) • (ρ - ρ.submatrix swapBC swapBC) := by
  rw [← swapMat_conj]
  have hS := swapMat_herm
  simp only [P3, P1, conjTranspose_mul, conjTranspose_smul, conjTranspose_add, conjTranspose_sub,
    hS, hρ.eq, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, smul_add, smul_sub, smul_smul,
    Matrix.mul_assoc]
  simp only [star_trivial]
  module

/-- **`eq:ppt3-pinch`** in the paper's form: for every PSD, unit-trace `ρ` that is PPT at `A|BC`,
`D(ρ, BS) ≤ ‖P₃ ρ P₁‖₁`. -/
theorem bsDist_le_tnormG_P3P1 {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptA ρ).PosSemidef) (ht : ρ.trace = 1) : bsDist ρ ≤ tnormG (P3 * ρ * P1) := by
  have h1 := bsDist_le_swap_average hρ hT ht
  have hD : (ρ - ρ.submatrix swapBC swapBC).IsHermitian := hρ.1.sub (hρ.1.submatrix _)
  have h2 := tnorm_le_two_tnormG (P3 * ρ * P1)
  rw [pinch_offdiag hρ.1, tnorm_real_smul hD (by norm_num)] at h2
  linarith

/-- info: 'FormalResearch.PPTThreeQubit.bsDist_le_tnormG_P3P1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsDist_le_tnormG_P3P1


end

end FormalResearch.PPTThreeQubit
