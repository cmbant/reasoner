import FormalResearch.FourQubitEntropy.SevenQubitLinearPurity

/-!
# `prop:seven-adaptive-purity-band` (conditional): the competitor purity band

Every pure seven-qubit state with `E₃(z) ≥ E_*` obeys `121/917 ≤ π₃(z) < p_c := 8693/64000`
(`seven_qubit_entropy_joint.tex`, AH-1).

Entropies are in nats (`meanEntropy3`), so `E_* > 59307/20000` bits reads
`E_* > (59307/20000) ln 2`.

* Lower bound: the sharp purity bound `SevenPurityBound` (`π₃ ≥ 121/917`), an explicit hypothesis
  (its proof is a computer certificate that is not formalized).
* Upper bound (proved from `lem:seven-entropy-linear-purity`, `SevenQubitLinearPurity`): averaging
  `3 ln 2 - S_T ≥ (2/5) ln 2 (8 tr ρ_T² - 1)` over the 35 cuts gives
  `3 ln 2 - E₃ ≥ (2/5) ln 2 (8 π₃ - 1)`; with `E₃ ≥ E_* > (59307/20000) ln 2` (SC-2 lower witness,
  **hypothesis**) rearrangement gives `π₃ < (1 + (5/2)(3 - 59307/20000))/8 = 8693/64000`.
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

/-- Averaged linear purity bound: `(2/5) ln 2 (8 π₃ - 1) ≤ 3 ln 2 - E₃` for every unit vector (proved). -/
theorem meanEntropy3_linear_purity (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    (2 / 5) * log 2 * (8 * meanPurity3 ψ - 1) ≤ 3 * log 2 - meanEntropy3 ψ := by
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hmem : ∀ T ∈ tripleMasks, weight T = 3 := fun T hT => (Finset.mem_filter.1 hT).2
  have hT : ∀ T ∈ tripleMasks, (2 / 5) * log 2 * excess T ψ ≤
      3 * log 2 - cutEntropy (maskCut 3 4 T) ψ := fun T hT =>
    LinPur.cutEntropy_linear_purity _ ψ (maskCut_bijective_three T (hmem T hT)) hψ
  have hsum := Finset.sum_le_sum hT
  have e1 : ∑ T ∈ tripleMasks, (2 / 5) * log 2 * excess T ψ =
      (2 / 5) * log 2 * (280 * meanPurity3 ψ - 35) := by
    rw [← Finset.mul_sum, ← excessSum_eq]; rfl
  have e3 : ∑ T ∈ tripleMasks, (3 * log 2 - cutEntropy (maskCut 3 4 T) ψ) =
      35 * (3 * log 2 - meanEntropy3 ψ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, tripleMasks_card]
    unfold meanEntropy3
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [e1, e3] at hsum
  nlinarith [hsum]

/-- **`prop:seven-adaptive-purity-band` (conditional).**  Assume the sharp purity bound
`SevenPurityBound` and the SC-2 lower witness `Estar > (59307/20000) ln 2`.  Every unit vector with
`E₃(ψ) ≥ Estar` has `121/917 ≤ π₃(ψ) < 8693/64000`.  The upper bound is proved from
`entropy_linear_purity`; the lower bound is `SevenPurityBound`. -/
theorem adaptive_purity_band (hPB : SevenPurityBound) (ψ : BitString → ℂ) (hψ : UnitVec ψ)
    {Estar : ℝ} (hwit : (59307 / 20000) * log 2 < Estar) (hE : Estar ≤ meanEntropy3 ψ) :
    121 / 917 ≤ meanPurity3 ψ ∧ meanPurity3 ψ < 8693 / 64000 := by
  refine ⟨hPB ψ hψ, ?_⟩
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have h := meanEntropy3_linear_purity ψ hψ
  by_contra hcon
  have hge : 8693 / 64000 ≤ meanPurity3 ψ := not_lt.1 hcon
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : 8693 / 8000 ≤ 8 * meanPurity3 ψ)
    (by positivity : 0 ≤ (2 / 5) * log 2)]

end FormalResearch.FourQubitEntropy.SevenQubitConseq
