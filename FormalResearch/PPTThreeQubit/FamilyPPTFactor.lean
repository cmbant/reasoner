import FormalResearch.PPTThreeQubit.FamilyGME
import FormalResearch.PPTThreeQubit.PartialTranspose

/-!
# The rank-five family `ρ_t`: cyclic symmetry and the `LDL*` factorization of `ρ_t^{T_A}`

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/family.tex`,
`thm:ppt3-family`, proof "PPT and rank claims" (cyclic symmetry, `eq:ppt3-minors`).

Technical half of `FamilyPPT.lean`: `ρ_t` is invariant under the cyclic qubit shift
(`rhoT_cycShift`), and for `t > 3`, `t² ≠ 12` the partial transpose `ρ_t^{T_A}` is
`(7(t+3))⁻¹ ∑ₖ dₖ |lₖ⟩⟨lₖ|` with explicit pivots `dₖ` (ratios of consecutive leading minors of
`eq:ppt3-minors`) and columns `lₖ` (`ptA_rhoT_eq`), checked entrywise.  The positivity of the pivots
on the PPT interval and the converse are in `FamilyPPT.lean`.
-/

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-! ### Cyclic invariance of `ρ_t` -/

theorem submatrix_vecMulVec_star (x : Fin 8 → ℂ) (f : Fin 8 → Fin 8) :
    (vecMulVec x (star x)).submatrix f f = vecMulVec (x ∘ f) (star (x ∘ f)) := by
  ext i j; simp [vecMulVec_apply]

theorem vecMulVec_phase (c : ℂ) (hc : c * star c = 1) (x : Fin 8 → ℂ) :
    vecMulVec (c • x) (star (c • x)) = vecMulVec x (star x) := by
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_smul, smul_eq_mul]
  linear_combination (x i * star (x j)) * hc

theorem eVec_cycShift : eVec ∘ cycShift = ω ^ 2 • eVec := by
  funext i
  fin_cases i <;> simp [cycShift, eVec] <;>
    first | linear_combination (-1 : ℂ) * ω_cube | linear_combination (-ω) * ω_cube

theorem oVec_cycShift : oVec ∘ cycShift = ω ^ 2 • oVec := by
  funext i
  fin_cases i <;> simp [cycShift, oVec] <;>
    first | linear_combination (-1 : ℂ) * ω_cube | linear_combination (-ω) * ω_cube

theorem uVec_cycShift : uVec 1 ∘ cycShift = uVec 1 := by
  funext i; fin_cases i <;> simp [cycShift, uVec]

theorem vVec_cycShift : vVec ∘ cycShift = vVec := by
  funext i; fin_cases i <;> simp [cycShift, vVec]

theorem wVec_cycShift : wVec ∘ cycShift = wVec := by
  funext i; fin_cases i <;> simp [cycShift, wVec]

theorem ω_sq_mul_star : ω ^ 2 * star (ω ^ 2) = 1 := by
  rw [star_pow, star_ω]; linear_combination (ω ^ 3 + 1) * ω_cube

/-- `ρ_t` is invariant under the cyclic shift of the qubits (`ρ_t` is cyclically symmetric, used
in the proof of `thm:ppt3-family`). -/
theorem rhoT_cycShift (t : ℝ) : (rhoT t).submatrix cycShift cycShift = rhoT t := by
  ext i j
  rw [submatrix_apply, rhoT_eq]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  have key : ∀ x : Fin 8 → ℂ, vecMulVec x (star x) (cycShift i) (cycShift j) =
      vecMulVec (x ∘ cycShift) (star (x ∘ cycShift)) i j := fun x => rfl
  simp only [key, uVec_cycShift, vVec_cycShift, wVec_cycShift, eVec_cycShift, oVec_cycShift,
    vecMulVec_phase _ ω_sq_mul_star]


/-! ### The `LDL*` factorization of `ρ_t^{T_A}` -/

/-- `x + y ω` with real coefficients. -/
def cw (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * ω

/-- The columns `l_k` of the LDL* factor of the numerator of `ρ_t^{T_A}`: four on the even parity
block (indices `0, 3, 5, 6`), four on the odd block (indices `1, 2, 4, 7`). -/
def lvec (t : ℝ) : Fin 8 → Fin 8 → ℂ := ![
  ![1, 0, 0, -1, 0, cw (2 / t) (-1 / t), cw (3 / t) (1 / t), 0],
  ![0, 0, 0, 1, 0, cw (2 / 3) (-1 / 3), cw 1 (1 / 3), 0],
  ![0, 0, 0, 0, 0, 1, cw ((3 * t ^ 2 - 8 * t - 24) / ((t + 3) * (3 * t - 7)))
      ((4 * t - 15) / ((t + 3) * (3 * t - 7))), 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 1, cw (1 / 2) (-1 / 4), 0, cw (-t / 4) 0, 0, 0, cw ((t - 3) / 4) (-3 / 4)],
  ![0, 0, 1, 0, cw (-t / 9) (t / 9), 0, 0, cw (t / 9 + 2 / 3) (7 / 3 - t / 9)],
  ![0, 0, 0, 0, 1, 0, 0, cw (t * (3 - t) / (t ^ 2 - 12)) 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- The pivots of the factorization (the ratios of consecutive leading minors, `eq:ppt3-minors`). -/
def dpiv (t : ℝ) : Fin 8 → ℝ := ![t, 3, (t + 3) * (3 * t - 7) / (3 * t),
  3 * (8 * t ^ 2 - 15 * t - 36) / ((t + 3) * (3 * t - 7)), 4, 9 / 4, (12 - t ^ 2) / 3,
  (t - 3) * (3 * t ^ 2 + 4 * t - 48) / (t ^ 2 - 12)]

theorem conj_ω : (starRingEnd ℂ) ω = ω ^ 2 := star_ω

theorem conj_cw (x y : ℝ) : (starRingEnd ℂ) (cw x y) = cw (x - y) (-y) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  simp only [cw, map_add, map_mul, conj_ω, Complex.conj_ofReal, h2]
  push_cast
  ring

/-- Entries of `ρ_t` from `eq:ppt3-rho`. -/
theorem rhoT_apply (t : ℝ) (i j : Fin 8) :
    rhoT t i j = ((1 / (7 * (t + 3)) : ℝ) : ℂ) *
      ((t : ℂ) * (uVec 1 i * star (uVec 1 j)) + 3 * t * (vVec i * star (vVec j))
        + 3 * (wVec i * star (wVec j)) + 3 * (eVec i * star (eVec j)) + oVec i * star (oVec j)) := by
  rw [rhoT_eq]
  simp only [Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]

theorem ω_pow4 : ω ^ 4 = ω := by linear_combination ω * ω_cube

theorem ω_pow5 : ω ^ 5 = -1 - ω := by
  linear_combination (ω ^ 2) * ω_cube + ω_sq_add_ω_add_one

theorem ω_pow6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * ω_cube

set_option maxHeartbeats 4000000 in
/-- Entrywise form of the `LDL*` factorization of `ρ_t^{T_A}` for `t > 3`, `t² ≠ 12`. -/
theorem ptA_rhoT_entry (t : ℝ) (ht : 3 < t) (h12 : t ^ 2 ≠ 12) (i j : Fin 8) :
    (ptA (rhoT t)) i j = (((1 / (7 * (t + 3)) : ℝ) : ℂ)) *
      ∑ k, (dpiv t k : ℂ) * lvec t k i * star (lvec t k j) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : t ≠ 0)
  have ht3 : (t : ℂ) + 3 ≠ 0 := by exact_mod_cast (by linarith : t + 3 ≠ 0)
  have ht7 : 3 * (t : ℂ) - 7 ≠ 0 := by exact_mod_cast (by linarith : 3 * t - 7 ≠ 0)
  have ht7' : -7 + (t : ℂ) * 3 ≠ 0 := by
    intro h; apply ht7; linear_combination h
  have ht12 : (t : ℂ) ^ 2 - 12 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr h12)
  simp only [ptA, of_apply, rhoT_apply]
  fin_cases i <;> fin_cases j <;>
    simp [uVec, vVec, wVec, eVec, oVec, Fin.sum_univ_eight, lvec, dpiv, conj_cw, conj_ω,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  all_goals
    try simp only [cw]
    try push_cast
    try field_simp
    try ring_nf
    try simp only [ω_cube, ω_pow4, ω_pow5, ω_pow6, h2]
    try ring_nf
    try simp only [or_true]
    try field_simp
    try ring_nf
    try simp only [ω_cube, ω_pow4, ω_pow5, ω_pow6, h2]
    try ring_nf


/-- `ρ_t^{T_A}` as a sum of rank-one operators with the pivots `dpiv` as weights. -/
theorem ptA_rhoT_eq (t : ℝ) (ht : 3 < t) (h12 : t ^ 2 ≠ 12) :
    ptA (rhoT t) = (1 / (7 * (t + 3)) : ℝ) •
      ∑ k, dpiv t k • vecMulVec (lvec t k) (star (lvec t k)) := by
  ext i j
  rw [ptA_rhoT_entry t ht h12 i j]
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Complex.real_smul,
    Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

end
end FormalResearch.PPTThreeQubit
