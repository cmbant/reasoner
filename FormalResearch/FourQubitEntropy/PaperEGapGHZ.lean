import FormalResearch.FourQubitEntropy.PaperEFidelityFloor
import FormalResearch.FourQubitEntropy.EnvelopeCoefficientSharp

/-!
# `lem:fqe-hs-fidelity-floor`: attainment of the floor by GHZ

Paper E, `global_overlap_certificate.tex`, `lem:fqe-hs-fidelity-floor`: the inequality
`Φ ≥ (1+√τ)/6` (`OD.fidelity_floor`) is attained by the GHZ state `(|0000⟩+|1111⟩)/√2`, for which
`τ = 1` and `Φ = 1/3`.

Proof (as in the paper): the magic diagonal of GHZ is `(1,0,0,-1)/√2`, i.e. `GHZ = G(v)` with
`v = (c,0,0,-c)`, `c = 1/√2` (`ghz_eq_Gv`); `G(v)` is critical, so the signed-Birkhoff reduction
`Phi_Gv_le` bounds `Φ` by the maximum of the 32 representative overlaps `qH a v`, each `≤ 1/3`
(`qH_ghz_le`).  The matching lower bound is `OD.fidelity_floor` with `τ = 1`.
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.OD
open CO PaperECritical

/-- The GHZ state `(|0000⟩ + |1111⟩)/√2`. -/
noncomputable def ghzHalf : Psi := ghzState (1 / Real.sqrt 2) (1 / Real.sqrt 2)

/-- The magic diagonal `(1,0,0,-1)/√2` of GHZ. -/
noncomputable def vGhz : V := fun p =>
  match p with
  | (0, 0) => ((1 / Real.sqrt 2 : ℝ) : ℂ)
  | (1, 1) => -((1 / Real.sqrt 2 : ℝ) : ℂ)
  | _ => 0

theorem ghz_eq_Gv : Gv vGhz = ghzHalf := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hrt : rt * rt = 1 / 2 := rt_mul_rt
  have hc : ((1 / Real.sqrt 2 : ℝ) : ℂ) = Real.sqrt 2 / 2 * 1 := by
    have : (1 / Real.sqrt 2 : ℝ) = Real.sqrt 2 / 2 := by
      field_simp; linarith
    rw [this]; push_cast; ring
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Gv, ofZmat, Matrix.mul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.transpose_apply, magicB, vGhz, ghzHalf, ghzState] <;>
    (try (rw [← mul_assoc]; ring_nf)) <;>
    (try (have hr2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hrt
          simp only [hr2, Complex.I_sq]; ring))

theorem ghzHalf_normSq : normSqPsi ghzHalf = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold ghzHalf
  rw [ghz_normSq]
  have : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [this]; norm_num

theorem ghzHalf_spinFlipForm : spinFlipForm ghzHalf = 1 := by
  unfold ghzHalf
  rw [ghz_spinFlipForm]
  have : 2 * (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 := by
    have h : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [h]
  rw [this]; simp

/-- Each of the 32 representative overlaps with the GHZ diagonal is at most `1/3`. -/
theorem qH_ghz_le (a : Fin 32) : qH a vGhz ≤ 1 / 3 := by
  have hc : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  set c : ℝ := 1 / Real.sqrt 2 with hcdef
  have hcoord : coord vGhz = ![(c : ℂ), 0, 0, -(c : ℂ)] := by
    funext j; fin_cases j <;> simp [coord, vGhz, hcdef]
  unfold qH Aq Cq Sx Sy
  simp only [hcoord, idxI]
  fin_cases a <;> simp [epsOf, Fin.sum_univ_four, Complex.normSq_apply] <;> nlinarith [hc, sq_nonneg c]

/-- **Attainment in `lem:fqe-hs-fidelity-floor`**: for the GHZ state `(|0000⟩+|1111⟩)/√2`,
`Φ = 1/3 = (1+√τ)/6` with `τ = 1`. -/
theorem fidelity_floor_ghz_attained :
    normSqPsi ghzHalf = 1 ∧ spinFlipForm ghzHalf = 1 ∧ Phi ghzHalf = 1 / 3 ∧
      Phi ghzHalf = (1 + Real.sqrt (Complex.normSq (spinFlipForm ghzHalf))) / 6 := by
  have hu := ghzHalf_normSq
  have hτ := ghzHalf_spinFlipForm
  have hlow := fidelity_floor hu
  rw [hτ] at hlow
  simp only [map_one, Real.sqrt_one] at hlow
  have hup : Phi ghzHalf ≤ 1 / 3 := by
    rw [← ghz_eq_Gv]; exact Phi_Gv_le qH_ghz_le
  have h3 : Phi ghzHalf = 1 / 3 := by linarith
  refine ⟨hu, hτ, h3, ?_⟩
  rw [hτ]; simp [h3]; norm_num

end FormalResearch.FourQubitEntropy.OD

#print axioms FormalResearch.FourQubitEntropy.OD.fidelity_floor_ghz_attained
