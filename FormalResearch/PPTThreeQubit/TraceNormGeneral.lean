module

public import FormalResearch.PPTThreeQubit.TraceDistance

/-!
# The trace norm of a non-Hermitian matrix and `eq:ppt3-pinch` in the paper's form

`tnormG X = sup {Re tr(U X) : U†U ≤ 1}` (the dual of the operator norm; it equals `∑ σ_i(X)`).
For a Hermitian `X + X†` it dominates half the Hermitian trace norm `QIB.tnorm` (`tnorm_le_two_tnormG`);
for the triplet/singlet projectors `P₃ = (1 + S_BC)/2`, `P₁ = (1 - S_BC)/2` of `BC`,
`P₃ρP₁ + P₁ρP₃ = (ρ - S_BC ρ S_BC)/2`, so

* `bsDist_le_tnormG_P3P1`: `D(ρ, BS) ≤ ‖P₃ ρ P₁‖₁` for every PSD, `A|BC`-PPT, unit-trace `ρ`
  (`eq:ppt3-pinch`, `cor:ppt3-symmetrisation` (c)).
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.QIB
open FormalResearch.FrameFree.Helstrom (IsEffect)
open scoped ComplexOrder

noncomputable section

section General
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A contraction: `U†U ≤ 1`. -/
def IsContraction (U : Matrix n n ℂ) : Prop := (1 - Uᴴ * U).PosSemidef

/-- The trace norm of an arbitrary matrix, as the supremum of `Re tr(U X)` over contractions. -/
def tnormG (X : Matrix n n ℂ) : ℝ := sSup {r | ∃ U, IsContraction U ∧ r = (U * X).trace.re}

theorem IsContraction.entry_le {U : Matrix n n ℂ} (hU : IsContraction U) (i j : n) : ‖U i j‖ ≤ 1 := by
  have hd := hU.diag_nonneg (i := j)
  have h1 : (1 - Uᴴ * U) j j = 1 - ∑ k, (Complex.normSq (U k j) : ℂ) := by
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, conjTranspose_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  rw [h1] at hd
  have hre : (0 : ℝ) ≤ 1 - ∑ k, Complex.normSq (U k j) := by
    have := (Complex.nonneg_iff.mp hd).1
    simpa using this
  have hsingle : Complex.normSq (U i j) ≤ ∑ k, Complex.normSq (U k j) :=
    Finset.single_le_sum (f := fun k => Complex.normSq (U k j)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have : Complex.normSq (U i j) ≤ 1 := by linarith
  rw [Complex.normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (U i j)]

theorem tnormG_bddAbove (X : Matrix n n ℂ) :
    BddAbove {r | ∃ U, IsContraction U ∧ r = (U * X).trace.re} := by
  refine ⟨∑ i, ∑ j, ‖X j i‖, ?_⟩
  rintro _ ⟨U, hU, rfl⟩
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine Finset.sum_le_sum fun j _ => ?_
  calc (U i j * X j i).re ≤ ‖U i j * X j i‖ := Complex.re_le_norm _
    _ = ‖U i j‖ * ‖X j i‖ := norm_mul _ _
    _ ≤ 1 * ‖X j i‖ := by gcongr; exact hU.entry_le i j
    _ = ‖X j i‖ := one_mul _

theorem le_tnormG {U X : Matrix n n ℂ} (hU : IsContraction U) : (U * X).trace.re ≤ tnormG X :=
  le_csSup (tnormG_bddAbove X) ⟨U, hU, rfl⟩

theorem negProj_mul_self {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    negProj D hD * negProj D hD = negProj D hD := by
  unfold negProj
  set U : Matrix n n ℂ := (hD.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := star_mul_self_U hD
  have hdd : (diagonal fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) *
      (diagonal fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) =
      diagonal fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0 := by
    rw [diagonal_mul_diagonal]
    congr 1; ext i; split_ifs <;> simp
  calc U * diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) * star U *
        (U * diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) * star U)
      = U * (diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) * (star U * U) *
        diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hUU, Matrix.mul_one, hdd]

/-- **Hermitian trace norm vs. general trace norm.** -/
theorem tnorm_le_two_tnormG (X : Matrix n n ℂ) : tnorm (X + Xᴴ) ≤ 2 * tnormG X := by
  have hO : (X + Xᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  set E := negProj (X + Xᴴ) hO with hEdef
  have hEh : E.IsHermitian := (negProj_isEffect hO).1.isHermitian
  have hE2 : E * E = E := negProj_mul_self hO
  set M : Matrix n n ℂ := 1 - (2 : ℂ) • E with hM
  have hMh : Mᴴ = M := by
    rw [hM, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hEh.eq]; simp
  have hMM : Mᴴ * M = 1 := by
    rw [hMh, hM]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hE2, smul_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcon : IsContraction M := by
    unfold IsContraction
    rw [hMM, sub_self]
    exact Matrix.PosSemidef.zero
  have h1 : (M * (X + Xᴴ)).trace.re = tnorm (X + Xᴴ) := by
    have := negProj_trace_mul_eq hO
    rw [hM, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul]
    have h22 : ∀ c : ℂ, ((2 : ℂ) • c).re = 2 * c.re := fun c => by rw [smul_eq_mul]; simp
    rw [Complex.sub_re, h22]
    rw [← hEdef] at this
    linarith
  have h2 : (M * Xᴴ).trace.re = (M * X).trace.re := by
    have : M * Xᴴ = (X * M)ᴴ := by rw [conjTranspose_mul, hMh]
    rw [this, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.trace_mul_comm]
  have h3 := le_tnormG (X := X) hcon
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, h2] at h1
  linarith

end General

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
    rw [if_neg, zero_mul]
    intro h; exact hk ((swapBC_eq_iff i k).1 h)
  · simp

theorem mul_swapMat (M : Matrix (Fin 8) (Fin 8) ℂ) : M * swapMat = M.submatrix id swapBC := by
  ext i j
  simp only [swapMat, Matrix.mul_apply, Matrix.of_apply, submatrix_apply, id]
  rw [Finset.sum_eq_single (swapBC j)]
  · simp [swapBC_swapBC]
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro h; exact hk h
  · simp

theorem swapMat_conj (ρ : Matrix (Fin 8) (Fin 8) ℂ) :
    swapMat * ρ * swapMat = ρ.submatrix swapBC swapBC := by
  rw [mul_swapMat, swapMat_mul]; ext i j; simp

theorem swapMat_herm : swapMatᴴ = swapMat := by
  ext i j
  simp only [swapMat, conjTranspose_apply, Matrix.of_apply]
  by_cases h : j = swapBC i
  · rw [if_pos h, if_pos ((swapBC_eq_iff i j).2 h)]; simp
  · rw [if_neg h, if_neg (fun h' => h ((swapBC_eq_iff i j).1 h'))]; simp

/-- The triplet projector of `BC`: `P₃ = (1 + S_BC)/2`. -/
def P3 : Matrix (Fin 8) (Fin 8) ℂ := (1 / 2 : ℝ) • (1 + swapMat)

/-- The singlet projector of `BC`: `P₁ = (1 - S_BC)/2`. -/
def P1 : Matrix (Fin 8) (Fin 8) ℂ := (1 / 2 : ℝ) • (1 - swapMat)

theorem pinch_offdiag {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.IsHermitian) :
    P3 * ρ * P1 + (P3 * ρ * P1)ᴴ = (1 / 2 : ℝ) • (ρ - ρ.submatrix swapBC swapBC) := by
  rw [← swapMat_conj]
  have hS := swapMat_herm
  simp only [P3, P1, conjTranspose_mul, conjTranspose_smul, conjTranspose_add, conjTranspose_sub,
    conjTranspose_one, hS, hρ.eq, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_sub, smul_smul,
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
