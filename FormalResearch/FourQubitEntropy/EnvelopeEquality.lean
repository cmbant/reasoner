import FormalResearch.FourQubitEntropy.GeneralEnvelope
import FormalResearch.FourQubitEntropy.PaperECriticalTwoFlat

/-!
# Sharpness of the envelope (`prop:fqe-critical-envelope`, `thm:fqe-general-envelope`)

* `critFam κ`: for every `κ ∈ [0,1]` the critical state `G(a, ib, ib, ib)` with `a² = (1+κ)/2`,
  `b² = (1-κ)/6` is a unit vector with `W₁ = 0`, `|s| = κ` and
  `F = κ² - κ³ = τ - τ^{3/2}` (`τ = κ²`): the critical envelope is attained for every `τ ∈ [0,1]`.
* `envelope_eq_forces_critical`: a unit vector with `F = τ - τ^{3/2}` has `W₁ = 0`; so equality in the
  critical envelope on a non-critical state never happens, and equality in the general envelope with
  `W₁ > 0` is the strictly stronger condition `F = (3/4 + 7τ/(8(1+√τ))) W₁ + τ - τ^{3/2}`.

Not formalized: the full classification of the equality set (the `τ = 0` zero set of `H`, and the
orbit description of the equality states for `τ > 0`); see `THEOREM_MAP.md`.
-/

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy

open FormalResearch.FourQubitEntropy.PaperECritical

/-- The family `v = (a, ib, ib, ib)`. -/
noncomputable def critFam (a b : ℝ) : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 0) then (a : ℂ) else (b : ℂ) * Complex.I

theorem Zsum_critFam (a b : ℝ) : Zsum (critFam a b) = 6 * b ^ 2 * (a ^ 2 - 3 * b ^ 2) ^ 2 := by
  simp [Zsum, Zterm, critFam, Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem critFam_normSq (a b : ℝ) :
    ∑ k, Complex.normSq (critFam a b k) = a ^ 2 + 3 * b ^ 2 := by
  simp [critFam, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem critFam_sq (a b : ℝ) : ∑ k, critFam a b k ^ 2 = ((a ^ 2 - 3 * b ^ 2 : ℝ) : ℂ) := by
  simp [critFam, Fintype.sum_prod_type, Fin.sum_univ_two, pow_two]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem spinFlipForm_Gv (v : Fin 2 × Fin 2 → ℂ) : spinFlipForm (Gv v) = ∑ k, v k ^ 2 := by
  rw [spinFlip_coord, coord_Gv, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  simp [Matrix.trace, pow_two]

/-- **Sharpness of `prop:fqe-critical-envelope`**: for every `κ ∈ [0,1]` there is a critical unit
vector with `|s| = κ` and `F = τ - τ^{3/2}`, `τ = κ²`. -/
theorem critical_envelope_attained (κ : ℝ) (h0 : 0 ≤ κ) (h1 : κ ≤ 1) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ blochSq ψ = 0 ∧ Complex.normSq (spinFlipForm ψ) = κ ^ 2 ∧
      sexticF ψ = Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)) := by
  set a := Real.sqrt ((1 + κ) / 2) with ha
  set b := Real.sqrt ((1 - κ) / 6) with hb
  have ha2 : a ^ 2 = (1 + κ) / 2 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (1 - κ) / 6 := Real.sq_sqrt (by linarith)
  refine ⟨Gv (critFam a b), ?_, ?_, ?_, ?_⟩
  · rw [Gv_n, critFam_normSq]; linarith
  · exact blochSq_zero_of_LU_Gv _ _ (LUEquiv.refl _)
  · rw [spinFlipForm_Gv, critFam_sq, Complex.normSq_ofReal]
    have : a ^ 2 - 3 * b ^ 2 = κ := by linarith
    rw [this]; ring
  · have hτ : Complex.normSq (spinFlipForm (Gv (critFam a b))) = κ ^ 2 := by
      rw [spinFlipForm_Gv, critFam_sq, Complex.normSq_ofReal]
      have : a ^ 2 - 3 * b ^ 2 = κ := by linarith
      rw [this]; ring
    rw [hτ, sexticF_Gv, Zsum_critFam, Real.sqrt_sq h0]
    have : a ^ 2 - 3 * b ^ 2 = κ := by linarith
    rw [this, hb2]; ring

/-- Equality in the critical envelope forces criticality: if a unit vector has
`F = τ - τ^{3/2}` then `W₁ = 0` (the coefficient of `W₁` in `thm:fqe-general-envelope` is positive). -/
theorem envelope_eq_forces_critical (ψ : Psi) (hψ : normSqPsi ψ = 1)
    (h : sexticF ψ = Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))) :
    blochSq ψ = 0 := by
  have hG := general_envelope_unit ψ hψ
  have hW := blochSq_nonneg ψ
  have hτ := Complex.normSq_nonneg (spinFlipForm ψ)
  set τ := Complex.normSq (spinFlipForm ψ)
  have hc : 0 < 3 / 4 + 7 * τ / (8 * (1 + Real.sqrt τ)) := by positivity
  rw [h] at hG
  have : (3 / 4 + 7 * τ / (8 * (1 + Real.sqrt τ))) * blochSq ψ ≤ 0 := by linarith
  by_contra hne
  have hpos : 0 < blochSq ψ := lt_of_le_of_ne hW (Ne.symm hne)
  have := mul_pos hc hpos
  linarith

end FormalResearch.FourQubitEntropy
