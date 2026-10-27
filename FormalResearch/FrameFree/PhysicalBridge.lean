import FormalResearch.FrameFree.WeylRealisation
import FormalResearch.FrameFree.WeylVertex
import FormalResearch.FrameFree.MaxChiral

/-!
# The Weyl-vertex value is a lower bound for the physical rotation overlap

`FKmag d` (`WeylVertex.lean`) is the maximum of `|dᵀ w d|²` over the 192 even signed
permutations.  `WeylRealisation.lean` realises each of them by local `SU(2)⁴` rotations, so
`FKmag d ≤ F_K(ψ_d)` for the physical rotation overlap.  The reverse inequality (the recalled
Weyl-vertex input R7 of the paper) is **not** formalised here.  Combined with the exact values of
`FKmag` this gives the lower bounds `F_K(M₄) ≥ 4/9`.
-/

open scoped ComplexConjugate
open FormalResearch.FourQubitEntropy

namespace FormalResearch.FrameFree

/-- `FKmag d` is at most the rotation overlap of `ψ_d` with its conjugate. -/
theorem FKmag_le_rotOverlap (d : Fin 4 → ℂ) :
    FKmag d ≤ rotOverlap (psiMag d) (Psi.conj (psiMag d)) := by
  rw [FKmag_le_iff]
  intro w hw
  have hw' := hw
  unfold weylSet at hw'
  rw [Finset.mem_filter] at hw'
  have hprod : ∏ k, sg (w.2 k) = 1 := hw'.2
  have hs : ∀ k, sg (w.2 k) = 1 ∨ sg (w.2 k) = -1 := by
    intro k; cases h : w.2 k <;> simp [sg]
  have := weyl_le_rotOverlap_conj w.1 (fun k => sg (w.2 k)) hs hprod d
  simpa [weylVal] using this

/-- `F_K(M₄) ≥ 4/9` for the actual four-qubit state `M₄`. -/
theorem four_ninths_le_rotOverlap_M4 :
    (4 / 9 : ℝ) ≤ rotOverlap M4 (Psi.conj M4) := by
  have hd : ![rt6, rt6, Complex.I * rt, rt6] =
      (((1 / Real.sqrt 6 : ℝ) : ℂ) • dz (Complex.I * (Real.sqrt 3 : ℝ))) ∘
        (Equiv.swap (2 : Fin 4) 3) := by
    have h6 : (Real.sqrt 6 : ℝ) = Real.sqrt 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    have h3 : (Real.sqrt 3 : ℝ) ≠ 0 := by positivity
    funext k
    fin_cases k <;> simp [dz, rt6, rt, Equiv.swap_apply_of_ne_of_ne]
    · rw [h6]; push_cast; field_simp
  rw [M4_eq_psiMag]
  have hF : FKmag ![rt6, rt6, Complex.I * rt, rt6] = 4 / 9 := by
    rw [hd, FKmag_comp, FKmag_M4]
  exact hF ▸ FKmag_le_rotOverlap ![rt6, rt6, Complex.I * rt, rt6]

/-- Maximal chirality, physical form (`thm:maxchiral`, the lower bound): every critical
four-qubit state `ψ_q` with unit coefficient vector has `F_K(ψ_q) ≥ 4/9`. -/
theorem four_ninths_le_rotOverlap (q : Fin 4 → ℂ) (hq : nrm2 q = 1) :
    (4 / 9 : ℝ) ≤ rotOverlap (psiMag q) (Psi.conj (psiMag q)) :=
  (FKmag_ge_four_ninths' q hq).trans (FKmag_le_rotOverlap q)

end FormalResearch.FrameFree
