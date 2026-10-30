import FormalResearch.FourQubitEntropy.CriticalOrbitUpper
import FormalResearch.FourQubitEntropy.CriticalOrbitMain

/-!
# Sharp critical-orbit stability: the theorem and its sharpness

`critical_orbit_sharp` bundles `eq:fqe-critical-fidelity`, `eq:fqe-critical-distance` and
`eq:fqe-critical-entropy` of `thm:fqe-critical-orbit-sharp` (given the all-state comparison
`Q ≥ 1 - Φ` of `thm:fqe-global-overlap` for `Φ ≥ 1/2`).  `bell_product_sharp` shows both constants
are optimal: the product of two Bell pairs `G(e₀)` has `Q = Φ = 1/2`, `d² = 2 - √2`, so
`Q = 1 - Φ = 3/2 - 2Φ = ((2+√2)/4) d²` (this uses the upper bound `Phi_Gv_le`).
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- `thm:fqe-critical-orbit-sharp`. -/
theorem critical_orbit_sharp {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hglob : 1 / 2 ≤ Phi ψ → 1 - Phi ψ ≤ sexticQ ψ) :
    max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) ≤ sexticQ ψ ∧
    (2 + Real.sqrt 2) / 4 * dist2 ψ ≤ sexticQ ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) *
        (max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ meanEntropy M4 - meanEntropy ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) *
        ((2 + Real.sqrt 2) / 4 * dist2 ψ + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ meanEntropy M4 - meanEntropy ψ :=
  ⟨critical_fidelity hψ hW hglob, critical_distance hψ hW hglob,
    critical_entropy_fidelity hψ hW hglob, critical_entropy_distance hψ hW hglob⟩

/-- The vector `e₀ = (1,0,0,0)`; `G(e₀)` is the product of two Bell pairs. -/
def e0 : V := fun p => if p = (0, 0) then 1 else 0

/-- `G(e₀)` is `|Φ⁺⟩₁₂ ⊗ |Φ⁺⟩₃₄`. -/
theorem Gv_e0_apply (a b c d : Fin 2) :
    Gv e0 a b c d = (if a = b then rt else 0) * (if c = d then rt else 0) := by
  show (magicB * Matrix.diagonal e0 * magicBᵀ) (a, b) (c, d) = _
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [Matrix.mul_apply, Matrix.diagonal_apply, magicB, e0, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem Nv_e0 : Nv e0 = 1 := by
  simp [Nv, e0, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem Qv_e0 : Qv e0 = 1 / 2 := by
  unfold Qv
  rw [Nv_e0, sum12 (fun k => pr e0 k ^ 2), sum12 (fun k => pr e0 k ^ 3)]
  simp [pr, e0, wp, wm, Complex.normSq_apply]
  norm_num

theorem qH_e0_le (a : Fin 32) : qH a e0 ≤ 1 / 2 := by
  fin_cases a <;> simp [qH, Aq, Cq, Sx, Sy, coord, epsOf, idxI, e0, Fin.sum_univ_four,
    Complex.normSq_apply] <;> norm_num

theorem qH_e0_zero : qH 0 e0 = 1 / 2 := by
  simp [qH, Aq, Cq, Sx, Sy, coord, epsOf, idxI, e0, Fin.sum_univ_four, Complex.normSq_apply]
  norm_num

theorem Phi_e0 : Phi (Gv e0) = 1 / 2 := by
  have hG : normSqPsi (Gv e0) = 1 := by rw [Gv_n]; simpa [Nv] using Nv_e0
  exact le_antisymm (Phi_Gv_le qH_e0_le)
    (qH_e0_zero ▸ qH_le_Phi (LUEquiv.refl _) hG 0)

/-- **Sharpness** (`thm:fqe-critical-orbit-sharp`): the Bell-pair product `G(e₀)` is critical with
`Q = Φ = 1/2` and `d² = 2 - √2`, so `Q = 1 - Φ = 3/2 - 2Φ = ((2+√2)/4) d²`. -/
theorem bell_product_sharp :
    normSqPsi (Gv e0) = 1 ∧ blochSq (Gv e0) = 0 ∧ sexticQ (Gv e0) = 1 / 2 ∧ Phi (Gv e0) = 1 / 2 ∧
      dist2 (Gv e0) = 2 - Real.sqrt 2 ∧ sexticQ (Gv e0) = 1 - Phi (Gv e0) ∧
      sexticQ (Gv e0) = 3 / 2 - 2 * Phi (Gv e0) ∧
      sexticQ (Gv e0) = (2 + Real.sqrt 2) / 4 * dist2 (Gv e0) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hQ : sexticQ (Gv e0) = 1 / 2 := by rw [sexticQ_Gv, Qv_e0]
  have hsq : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
    nlinarith
  have hd : dist2 (Gv e0) = 2 - Real.sqrt 2 := by
    unfold dist2; rw [Phi_e0, hsq]; ring
  refine ⟨by rw [Gv_n]; simpa [Nv] using Nv_e0, blochSq_zero_of_LU_Gv e0 _ (LUEquiv.refl _), hQ,
    Phi_e0, hd, by rw [hQ, Phi_e0]; norm_num, by rw [hQ, Phi_e0]; norm_num, ?_⟩
  rw [hQ, hd]; nlinarith

end FormalResearch.FourQubitEntropy.CO
