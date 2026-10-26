import Mathlib

/-!
# Exact scalar consequences of the seven-qubit icosahedral certificate

These identities formalize the scalar reductions used for `thm:ico` and
`cor:ico-entropy-separation` in `ResearchNotes/QI/seven_qubit_entanglement/icosahedral_state.tex`.
The state tensor and representative reduced-matrix entries are developed separately in
`SevenQubitIcoState.lean`; the family-wide mean-purity polynomial and all-cut spectra here remain
scalar statements rather than consequences derived from those matrices.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- The parameter `u = α²` in the icosahedral family. -/
noncomputable def u (x : ℝ) : ℝ := (1 - 2 * x) / 30

/-- The support counts `30` and `2` give the unit-norm coefficient identity. -/
theorem coefficient_norm_identity (x : ℝ) : 30 * u x + 2 * x = 1 := by
  unfold u
  ring

/-- The mean three-body purity polynomial obtained from the IC-1--IC-4 certificate. -/
noncomputable def meanPurity (x : ℝ) : ℝ :=
  (4470 * u x ^ 2 + 70 * x ^ 2 + 300 * u x * x) / 35

/-- The displayed mean purity polynomial after substituting `u = (1-2x)/30`. -/
theorem meanPurity_expanded (x : ℝ) :
    meanPurity x = 149 / 1050 - 148 / 525 * x + 1048 / 525 * x ^ 2 := by
  unfold meanPurity u
  ring

/-- Exact completed-square form around the family minimizer. -/
theorem meanPurity_sub_minimum (x : ℝ) :
    meanPurity x - meanPurity (37 / 524) = 1048 / 525 * (x - 37 / 524) ^ 2 := by
  rw [meanPurity_expanded, meanPurity_expanded]
  ring

theorem meanPurity_minimum (x : ℝ) : meanPurity (37 / 524) ≤ meanPurity x := by
  rw [← sub_nonneg]
  rw [meanPurity_sub_minimum]
  positivity

theorem meanPurity_at_minimum : meanPurity (37 / 524) = 121 / 917 := by
  unfold meanPurity u
  norm_num

/-- The two spectral patterns asserted for the 35 three-qubit reductions. -/
theorem spectrum_traces (x : ℝ) :
    6 * (4 * u x) + 2 * (3 * u x + x) = 1 ∧
      8 * u x + 5 * (4 * u x) + 2 * (u x + x) = 1 := by
  unfold u
  constructor <;> ring

/-- The four distinct eigenvalues at the state minimizing the family purity. -/
theorem spectrum_values_at_minimum :
    4 * u (37 / 524) = 15 / 131 ∧
      3 * u (37 / 524) + 37 / 524 = 41 / 262 ∧
      8 * u (37 / 524) = 30 / 131 ∧
      u (37 / 524) + 37 / 524 = 13 / 131 := by
  norm_num [u]

theorem triple_purities_at_minimum :
    2 * (41 / 262 : ℝ) ^ 2 + 6 * (15 / 131) ^ 2 = 4381 / 34322 ∧
      (30 / 131 : ℝ) ^ 2 + 5 * (15 / 131) ^ 2 + 2 * (13 / 131) ^ 2 =
        2363 / 17161 := by
  norm_num

noncomputable def entropyDerivativeRatioAtMinimum : ℝ :=
  ((30 : ℝ) ^ 10 * 15 ^ 5 / (13 ^ 7 * 41 ^ 8)) ^ 4

theorem derivative_ratio_at_minimum_lt_one : entropyDerivativeRatioAtMinimum < 1 := by
  norm_num [entropyDerivativeRatioAtMinimum]

/-- The exact logarithmic factor in the entropy derivative is negative at the purity minimum. -/
theorem entropy_log_factor_at_minimum :
    Real.log entropyDerivativeRatioAtMinimum < 0 := by
  have hnum : 0 < (30 : ℝ) ^ 10 * 15 ^ 5 := by positivity
  have hden : 0 < (13 : ℝ) ^ 7 * 41 ^ 8 := by positivity
  have hbase : 0 < (30 : ℝ) ^ 10 * 15 ^ 5 / (13 ^ 7 * 41 ^ 8) :=
    div_pos hnum hden
  apply Real.log_neg
  · simpa [entropyDerivativeRatioAtMinimum] using pow_pos hbase 4
  · exact derivative_ratio_at_minimum_lt_one

/-- The logarithmic factor at the left endpoint has the opposite sign. -/
theorem entropy_log_factor_at_zero :
    0 < Real.log ((16 / 3 : ℝ) ^ 32) := by
  apply Real.log_pos
  norm_num

end FormalResearch.FourQubitEntropy.SevenQubitIco
