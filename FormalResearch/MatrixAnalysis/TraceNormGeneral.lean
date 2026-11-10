module

public import FormalResearch.MatrixAnalysis.TraceNorm

/-!
# The trace norm of a non-Hermitian matrix

`tnormG X = sup {Re tr(U X) : U†U ≤ 1}` (the dual of the operator norm; it equals `∑ σ_i(X)`), and
`tnorm_le_two_tnormG`: for the Hermitian matrix `X + X†`, `tnorm (X + X†) ≤ 2 tnormG X`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix
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

/-- info: 'FormalResearch.MatrixAnalysis.tnorm_le_two_tnormG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tnorm_le_two_tnormG

end

end FormalResearch.MatrixAnalysis
