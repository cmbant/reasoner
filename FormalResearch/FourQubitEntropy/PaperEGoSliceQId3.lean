module

public import FormalResearch.FourQubitEntropy.PaperEGoSliceQId2
public import FormalResearch.FourQubitEntropy.PaperEGoSliceGen

/-!
# `SliceQIdentity` from `sexticQ_psiZ`

Specialises `sexticQ_psiZ` to the slice matrix `Z = √3 X + i Y`: with `A = 3XXᵀ + YYᵀ`, `B = YXᵀ - XYᵀ`,
`Z Zᴴ = A + i√3 B`, `Re tr (ZZᴴ)² = tr A² - 3 tr B²`, `Re tr (ZZᴴ)³ = tr A³ - 9 tr A B²`, and
`Z Zᵀ Z - (s/2) Z = √3 Nr + i Ni`, so `‖N‖² = 3‖Nr‖² + ‖Ni‖²`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

theorem toF_conjTranspose (M : Mat4) : toF Mᴴ = (toF M)ᴴ := by
  unfold toF; rw [Matrix.conjTranspose_submatrix]

theorem toF_sZ (v : SV) : toF (sZ v) = Matrix.of (Zc v) := by
  ext i j
  have hi : pairIdx (pairEquiv.symm i) = i := pairEquiv.apply_symm_apply i
  have hj : pairIdx (pairEquiv.symm j) = j := pairEquiv.apply_symm_apply j
  simp only [toF, Matrix.submatrix_apply, Matrix.of_apply, sZ_eq, hi, hj]

theorem h3c : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  exact_mod_cast this

/-- `Z Zᴴ = A + i√3 B` for the slice matrix. -/
theorem ZZH_slice (v : SV) :
    Matrix.of (Zc v) * (Matrix.of (Zc v))ᴴ =
      Matrix.of fun i j => ((sA v i j : ℝ) : ℂ) + Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * (sB v i j : ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Zc, Fin.sum_univ_four,
    Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, sA, sB,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply]
  push_cast
  ring_nf
  simp only [Complex.I_sq, h3c, show ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 by rw [pow_two]; exact h3c]
  push_cast
  ring_nf


theorem h3r : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- `A + i √3 B` for real matrices `A, B`. -/
def Mm (A B : M4R) : M4C :=
  Matrix.of fun i j => ((A i j : ℝ) : ℂ) + Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * ((B i j : ℝ) : ℂ)

theorem re_trace_sq (A B : M4R) :
    (Matrix.trace (Mm A B * Mm A B)).re = Matrix.trace (A * A) - 3 * Matrix.trace (B * B) := by
  have term : ∀ i j, (Mm A B i j * Mm A B j i).re = A i j * A j i - 3 * (B i j * B j i) := by
    intro i j
    simp only [Mm, Matrix.of_apply, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linear_combination (-(B i j * B j i)) * h3r
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum, term,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem re_trace_cube (A B : M4R) :
    (Matrix.trace (Mm A B * Mm A B * Mm A B)).re =
      Matrix.trace (A * A * A) - 9 * Matrix.trace (A * B * B) := by
  have hcyc1 : Matrix.trace (B * A * B) = Matrix.trace (A * B * B) := by
    calc Matrix.trace (B * A * B) = Matrix.trace (B * (A * B)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (A * B * B) := Matrix.trace_mul_comm _ _
  have hcyc2 : Matrix.trace (B * B * A) = Matrix.trace (A * B * B) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have key : (Matrix.trace (Mm A B * Mm A B * Mm A B)).re =
      Matrix.trace (A * A * A) - 3 * (Matrix.trace (A * B * B) + Matrix.trace (B * A * B) +
        Matrix.trace (B * B * A)) := by
    simp only [Mm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
      Fin.sum_univ_four, Complex.re_sum]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_sum, Complex.im_sum,
      Fin.sum_univ_four]
    ring_nf
    simp only [show Real.sqrt 3 ^ 2 = 3 by rw [pow_two]; exact h3r]
    ring_nf
  rw [key, hcyc1, hcyc2]; ring


set_option maxRecDepth 100000 in
theorem Nf_slice (v : SV) :
    Nf (Matrix.of (Zc v)) = Matrix.of fun i j =>
      ((Real.sqrt 3 : ℝ) : ℂ) * ((sNr v i j : ℝ) : ℂ) + Complex.I * ((sNi v i j : ℝ) : ℂ) := by
  have h3sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by rw [pow_two]; exact h3c
  have h3cu : ((Real.sqrt 3 : ℝ) : ℂ) ^ 3 = 3 * ((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [pow_succ, h3sq]
  ext i j
  simp only [Nf, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Zc, Fin.sum_univ_four, Matrix.trace, Matrix.diag_apply, smul_eq_mul, sNr, sNi,
    sC, sD, sR, sI, Matrix.add_apply, Matrix.neg_apply]
  push_cast
  ring_nf
  simp only [Complex.I_sq, Ipow3, h3sq, h3cu]
  push_cast
  ring_nf

theorem NN_slice (v : SV) :
    ∑ i, ∑ j, Complex.normSq (Nf (Matrix.of (Zc v)) i j) = 3 * fn4 (sNr v) + fn4 (sNi v) := by
  have term : ∀ i j, Complex.normSq (Nf (Matrix.of (Zc v)) i j) =
      3 * sNr v i j ^ 2 + sNi v i j ^ 2 := by
    intro i j
    rw [Nf_slice]
    simp only [Matrix.of_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    linear_combination (sNr v i j ^ 2) * h3r
  simp only [term, fn4, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem sum_normSq_psiZ (Z : Mat4) :
    ∑ p, ∑ q, Complex.normSq (Z p q) = normSqPsi (psiZ Z) := by
  rw [← frob_coord (psiZ Z), coord_of_eq (zmat_psiZ Z)]

/-- **`SliceQIdentity` is a theorem**: `Q` of the slice state is the slice polynomial `sliceQ`. -/
theorem sliceQIdentity : SliceQIdentity := by
  intro v
  have h := sexticQ_psiZ (sZ v)
  have e : psiZ (sZ v) = sState v := rfl
  rw [e] at h
  rw [h]
  have hn : ∑ p, ∑ q, Complex.normSq (sZ v p q) = sN v := by
    rw [sum_normSq_psiZ, e, normSqPsi_sState]
  have hZZ : toF (sZ v * (sZ v)ᴴ) = Mm (sA v) (sB v) := by
    rw [toF_mul, toF_conjTranspose, toF_sZ]
    exact ZZH_slice v
  have hp2 : (Matrix.trace (sZ v * (sZ v)ᴴ * (sZ v * (sZ v)ᴴ))).re =
      Matrix.trace (sA v * sA v) - 3 * Matrix.trace (sB v * sB v) := by
    rw [← toF_trace, toF_mul, hZZ]
    exact re_trace_sq _ _
  have hp3 : (Matrix.trace (sZ v * (sZ v)ᴴ * (sZ v * (sZ v)ᴴ) * (sZ v * (sZ v)ᴴ))).re =
      Matrix.trace (sA v * sA v * sA v) - 9 * Matrix.trace (sA v * sB v * sB v) := by
    rw [← toF_trace, toF_mul, toF_mul, hZZ]
    exact re_trace_cube _ _
  have hNN : ∑ p, ∑ q, Complex.normSq (Nm (sZ v) p q) = 3 * fn4 (sNr v) + fn4 (sNi v) := by
    rw [← NN_slice, ← toF_sZ]
    simp only [← toF_Nm]
    exact (sum_toF (fun p q => Complex.normSq (Nm (sZ v) p q))).symm
  rw [hn, hp2, hp3, hNN]
  unfold sliceQ
  ring

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.sliceQIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceQIdentity

end

end FormalResearch.FourQubitEntropy.GO
