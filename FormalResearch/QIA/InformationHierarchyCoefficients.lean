import Mathlib

namespace FormalResearch.QIA

/-!
# QI-A repeated-block information hierarchy coefficients

This module matches the exact scalar certificate in `cmbant/QIprojects`,
current source pin `f15afef701b769e5a4f1ec83c549ec4506f77af4`, with QI-A bytes unchanged
from the earlier theorem audit at `a32a35809edd12b7d7cb7c23b332edad36efa5bc`.
The source scripts are `QI-A/scripts/verify_information_hierarchy.py` and
`QI-A/scripts/verify_measured_chernoff_qutrit.py`.

The theorem scope here is deliberately scalar.  We formalize the exact
Chernoff-coefficient constants reported by the source certificate, their
strict ordering, and the induced ordering after applying `-log`.  We do not
rederive the operational measurement optimization, sandwiched-Renyi data
processing, or the density-matrix reductions that identify these constants.
-/

/-- Three-copy SWAP-word two-outcome coefficient. -/
noncomputable def infoWordQ : ℝ := Real.sqrt (1 - 9 / 4096)

/-- Repeated one-shot Helstrom-bit coefficient. -/
noncomputable def infoHelstromBitQ : ℝ := Real.sqrt (255 / 256)

/-- Fixed local `ZYYX` coefficient with the full ternary record retained. -/
noncomputable def infoZYYXQ : ℝ := (44 + Real.sqrt 7) / 48

/-- Optimal immediate-classicalization coefficient on the informative qutrit. -/
def infoMeasuredConditionalQ : ℝ := 7 / 11

/-- Full immediate-classicalization coefficient after restoring the identical
`7/8` complement. -/
def infoMeasuredFullQ : ℝ := 7 / 8 + infoMeasuredConditionalQ / 8

/-- Coherent-qutrit Chernoff coefficient from the exact QI-A spectrum. -/
noncomputable def infoCoherentQ : ℝ := (162 + Real.sqrt 33) / 176

/-- Exact full measured coefficient `Q_meas,full = 21/22`. -/
theorem infoMeasuredFullQ_closed : infoMeasuredFullQ = 21 / 22 := by
  norm_num [infoMeasuredFullQ, infoMeasuredConditionalQ]

lemma info_sqrt7_sq : (Real.sqrt (7 : ℝ)) ^ 2 = 7 := by
  exact Real.sq_sqrt (by norm_num)

lemma info_sqrt33_sq : (Real.sqrt (33 : ℝ)) ^ 2 = 33 := by
  exact Real.sq_sqrt (by norm_num)

lemma infoCoherentQ_pos : 0 < infoCoherentQ := by
  unfold infoCoherentQ
  positivity

lemma infoCoherentQ_lt_measured : infoCoherentQ < infoMeasuredFullQ := by
  rw [infoMeasuredFullQ_closed]
  unfold infoCoherentQ
  have hs33 : Real.sqrt (33 : ℝ) < 6 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 6)]
    norm_num
  nlinarith

lemma infoMeasuredQ_lt_zyyx : infoMeasuredFullQ < infoZYYXQ := by
  rw [infoMeasuredFullQ_closed]
  unfold infoZYYXQ
  have hs7nonneg : 0 ≤ Real.sqrt (7 : ℝ) := Real.sqrt_nonneg _
  have hs7gt2 : 2 < Real.sqrt (7 : ℝ) := by
    nlinarith [info_sqrt7_sq]
  nlinarith

lemma infoZYYXQ_lt_helstrom : infoZYYXQ < infoHelstromBitQ := by
  unfold infoZYYXQ infoHelstromBitQ
  have hs7nonneg : 0 ≤ Real.sqrt (7 : ℝ) := Real.sqrt_nonneg _
  have hs7lt4 : Real.sqrt (7 : ℝ) < 4 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hzsq : ((44 + Real.sqrt (7 : ℝ)) / 48) ^ 2 < (255 : ℝ) / 256 := by
    nlinarith [info_sqrt7_sq]
  have hhsq : (Real.sqrt ((255 : ℝ) / 256)) ^ 2 = (255 : ℝ) / 256 := by
    exact Real.sq_sqrt (by norm_num)
  have hznonneg : 0 ≤ (44 + Real.sqrt (7 : ℝ)) / 48 := by positivity
  have hhnonneg : 0 ≤ Real.sqrt ((255 : ℝ) / 256) := Real.sqrt_nonneg _
  nlinarith

lemma infoHelstromQ_lt_word : infoHelstromBitQ < infoWordQ := by
  unfold infoHelstromBitQ infoWordQ
  have hhsq : (Real.sqrt ((255 : ℝ) / 256)) ^ 2 = (255 : ℝ) / 256 := by
    exact Real.sq_sqrt (by norm_num)
  have hwsq : (Real.sqrt (1 - (9 : ℝ) / 4096)) ^ 2 = 1 - (9 : ℝ) / 4096 := by
    exact Real.sq_sqrt (by norm_num)
  have hh0 : 0 ≤ Real.sqrt ((255 : ℝ) / 256) := Real.sqrt_nonneg _
  have hw0 : 0 ≤ Real.sqrt (1 - (9 : ℝ) / 4096) := Real.sqrt_nonneg _
  nlinarith

lemma infoWordQ_lt_one : infoWordQ < 1 := by
  unfold infoWordQ
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- Reverse coefficient ordering corresponding to the source's strict
information-exponent hierarchy. -/
theorem informationHierarchy_coefficients_strict :
    0 < infoCoherentQ ∧
    infoCoherentQ < infoMeasuredFullQ ∧
    infoMeasuredFullQ < infoZYYXQ ∧
    infoZYYXQ < infoHelstromBitQ ∧
    infoHelstromBitQ < infoWordQ ∧
    infoWordQ < 1 := by
  exact ⟨infoCoherentQ_pos, infoCoherentQ_lt_measured,
    infoMeasuredQ_lt_zyyx, infoZYYXQ_lt_helstrom,
    infoHelstromQ_lt_word, infoWordQ_lt_one⟩

noncomputable def infoWordXi : ℝ := -Real.log infoWordQ
noncomputable def infoHelstromBitXi : ℝ := -Real.log infoHelstromBitQ
noncomputable def infoZYYXXi : ℝ := -Real.log infoZYYXQ
noncomputable def infoMeasuredXi : ℝ := -Real.log infoMeasuredFullQ
noncomputable def infoCoherentXi : ℝ := -Real.log infoCoherentQ

/-- Exact source identity `xi_meas = log(22/21)`. -/
theorem infoMeasuredXi_closed : infoMeasuredXi = Real.log (22 / 21 : ℝ) := by
  unfold infoMeasuredXi
  rw [infoMeasuredFullQ_closed]
  rw [← Real.log_inv]
  norm_num

/-- Exact strict exponent ordering certified by the QI-A scalar constants. -/
theorem informationHierarchy_exponents_strict :
    0 < infoWordXi ∧
    infoWordXi < infoHelstromBitXi ∧
    infoHelstromBitXi < infoZYYXXi ∧
    infoZYYXXi < infoMeasuredXi ∧
    infoMeasuredXi < infoCoherentXi := by
  rcases informationHierarchy_coefficients_strict with
    ⟨hC0, hCM, hMZ, hZH, hHW, hW1⟩
  have hM0 : 0 < infoMeasuredFullQ := lt_trans hC0 hCM
  have hZ0 : 0 < infoZYYXQ := lt_trans hM0 hMZ
  have hH0 : 0 < infoHelstromBitQ := lt_trans hZ0 hZH
  have hW0 : 0 < infoWordQ := lt_trans hH0 hHW
  have hxiW0 : 0 < -Real.log infoWordQ := by
    have hlog := Real.log_neg hW0 hW1
    linarith
  have hxiWH : -Real.log infoWordQ < -Real.log infoHelstromBitQ := by
    have hlog := Real.log_lt_log hH0 hHW
    linarith
  have hxiHZ : -Real.log infoHelstromBitQ < -Real.log infoZYYXQ := by
    have hlog := Real.log_lt_log hZ0 hZH
    linarith
  have hxiZM : -Real.log infoZYYXQ < -Real.log infoMeasuredFullQ := by
    have hlog := Real.log_lt_log hM0 hMZ
    linarith
  have hxiMC : -Real.log infoMeasuredFullQ < -Real.log infoCoherentQ := by
    have hlog := Real.log_lt_log hC0 hCM
    linarith
  exact ⟨hxiW0, hxiWH, hxiHZ, hxiZM, hxiMC⟩

end FormalResearch.QIA
