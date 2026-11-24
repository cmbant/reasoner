module

public import FormalResearch.Special.AiryAsymNegComplex
public import FormalResearch.Special.AiryAsymNeg
public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryAsymSector

/-!
# `GT.1`, Remark `T.6`: the two-exponential form of `Ai(-w)` with sector amplitudes

For `w` in the sector `{re w > 0, |im w| < re w / 2}` put `q = w^{1/2}` and `ξ(w) = (2/3) q³` (`negPhase`).  The rotation identity
`Ai(z) = -ω Ai(ω z) - ω² Ai(ω² z)` at `z = -w` splits

`Ai(-w) = a₊(w) e^{-iξ(w)} + a₋(w) e^{iξ(w)}`,  `Ai'(-w) = a₊'(w) e^{-iξ(w)} + a₋'(w) e^{iξ(w)}`

(`neg_split`, `neg_split'`) with the entire-times-phase amplitudes `a₊ = -ω² Ai(ω²(-w)) e^{iξ}`, `a₋ = -ω Ai(ω(-w)) e^{-iξ}` (`negAmpP`,
`negAmpM`) and their `Ai'` analogues (`negAmpP'`, `negAmpM'`).  The sector asymptotics `norm_airyAiC_sq_sub_lead_le`,
`norm_deriv_airyAiC_sq_add_lead_le` (with `s = 1/2`) bound them for `‖w‖ ≥ 1`:
`‖a_±(w)‖ ≤ 2 ‖w‖^{-1/4}` and `‖a_±'(w)‖ ≤ 4 ‖w‖^{1/4}` (`negAmpP_bound`, ...), the order-`1/4` and order-`-1/4` symbol sizes.

Status: proved.  Not formalised here: the symbol (Cauchy) consequences, in `Gt1NegTail.lean`.
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- The phase `ξ(w) = (2/3) (w^{1/2})³`. -/
noncomputable def negPhase (w : ℂ) : ℂ := (2 / 3 : ℂ) * (w ^ (1 / 2 : ℂ)) ^ 3

/-- Amplitude of `e^{-iξ}` in `Ai(-w)`: `-ω² Ai(ω²(-w)) e^{iξ}`. -/
noncomputable def negAmpP (w : ℂ) : ℂ :=
  -(airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * (-w))) * cexp (I * negPhase w)

/-- Amplitude of `e^{iξ}` in `Ai(-w)`: `-ω Ai(ω(-w)) e^{-iξ}`. -/
noncomputable def negAmpM (w : ℂ) : ℂ :=
  -(airyOmega * airyAiC (airyOmega * (-w))) * cexp (-(I * negPhase w))

/-- Amplitude of `e^{-iξ}` in `Ai'(-w)`. -/
noncomputable def negAmpP' (w : ℂ) : ℂ :=
  -(airyOmega * deriv airyAiC (airyOmega ^ 2 * (-w))) * cexp (I * negPhase w)

/-- Amplitude of `e^{iξ}` in `Ai'(-w)`. -/
noncomputable def negAmpM' (w : ℂ) : ℂ :=
  -(airyOmega ^ 2 * deriv airyAiC (airyOmega * (-w))) * cexp (-(I * negPhase w))

lemma exp_mul_exp_neg (φ : ℂ) : cexp (I * φ) * cexp (-(I * φ)) = 1 := by
  rw [← Complex.exp_add]; simp

/-- `Ai(-w) = a₊ e^{-iξ} + a₋ e^{iξ}`. -/
theorem neg_split (w : ℂ) :
    airyAiC (-w) = negAmpP w * cexp (-(I * negPhase w)) + negAmpM w * cexp (I * negPhase w) := by
  have h := airyAiC_rotation (-w)
  have hE := exp_mul_exp_neg (negPhase w)
  unfold negAmpP negAmpM
  linear_combination h + (airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * (-w)) +
    airyOmega * airyAiC (airyOmega * (-w))) * hE

/-- `Ai'(-w) = a₊' e^{-iξ} + a₋' e^{iξ}`. -/
theorem neg_split' (w : ℂ) :
    deriv airyAiC (-w) = negAmpP' w * cexp (-(I * negPhase w)) + negAmpM' w * cexp (I * negPhase w) := by
  have h := deriv_airyAiC_rotation (-w)
  have hE := exp_mul_exp_neg (negPhase w)
  unfold negAmpP' negAmpM'
  linear_combination h + (airyOmega * deriv airyAiC (airyOmega ^ 2 * (-w)) +
    airyOmega ^ 2 * deriv airyAiC (airyOmega * (-w))) * hE

lemma re_ge_half {w : ℂ} (hre : 0 < w.re) (him : |w.im| < w.re / 2) : ‖w‖ / 2 ≤ w.re := by
  have := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_pos hre] at this
  linarith

lemma root_sector {w : ℂ} (hre : 0 < w.re) (him : |w.im| < w.re / 2) (h1 : 1 ≤ ‖w‖) :
    NegSector (w ^ (1 / 2 : ℂ)) ∧ 1 ≤ ‖w ^ (1 / 2 : ℂ)‖ := by
  have hw0 : 0 < ‖w‖ := by linarith
  have hh := re_ge_half hre him
  have h3 : (2 * (√3 / 2) ^ 2 - 1) = 1 / 2 := by
    have : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [div_pow, this]; norm_num
  obtain ⟨h, -⟩ := sector_root_facts (z := w) (s := √3 / 2) (by positivity) hw0 (by rw [h3]; linarith)
  refine ⟨h, ?_⟩
  rw [norm_cpow_half]
  exact Real.one_le_sqrt.mpr h1

lemma ai_sq_le {W : ℂ} (h1 : 1 ≤ ‖W‖) (hre : ‖W‖ / 2 ≤ W.re) :
    ‖airyAiC (W ^ 2)‖ ≤ 3 * ‖airyLead W‖ := by
  have hw0 : 0 < W.re := by linarith
  have b := norm_airyAiC_sq_sub_lead_le (w := W) (s := 1 / 2) (by norm_num) (by linarith) hw0
  have hs : (1 / 2 : ℝ) ≤ √(1 / 2 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
  have hW3 : 1 ≤ ‖W‖ ^ 3 := one_le_pow₀ h1
  have hden := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 3)) hW3
    (by norm_num) (by positivity)
  have hη : 5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖W‖ ^ 3) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hL := norm_nonneg (airyLead W)
  calc ‖airyAiC (W ^ 2)‖ ≤ ‖airyAiC (W ^ 2) - airyLead W‖ + ‖airyLead W‖ := by
        have := norm_sub_norm_le (airyAiC (W ^ 2)) (airyLead W)
        linarith
    _ ≤ 2 * ‖airyLead W‖ + ‖airyLead W‖ := by
        have := mul_le_mul_of_nonneg_right hη hL
        linarith
    _ = 3 * ‖airyLead W‖ := by ring

lemma aip_sq_le {W : ℂ} (h1 : 1 ≤ ‖W‖) (hre : ‖W‖ / 2 ≤ W.re) :
    ‖deriv airyAiC (W ^ 2)‖ ≤ 7 * (‖W‖ * ‖airyLead W‖) := by
  have hw0 : 0 < W.re := by linarith
  have b := norm_deriv_airyAiC_sq_add_lead_le (w := W) (s := 1 / 2) (by norm_num) (by norm_num) (by linarith) hw0
  have hs : (1 / 2 : ℝ) ≤ √(1 / 2 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
  have hW3 : 1 ≤ ‖W‖ ^ 3 := one_le_pow₀ h1
  have hden := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 3)) hW3
    (by norm_num) (by positivity)
  have hη : 17 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖W‖ ^ 3) ≤ 6 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hL : 0 ≤ ‖W * airyLead W‖ := norm_nonneg _
  rw [norm_mul] at hL b
  calc ‖deriv airyAiC (W ^ 2)‖ ≤ ‖deriv airyAiC (W ^ 2) + W * airyLead W‖ + ‖W‖ * ‖airyLead W‖ := by
        have := norm_sub_norm_le (deriv airyAiC (W ^ 2)) (-(W * airyLead W))
        rw [sub_neg_eq_add, norm_neg, norm_mul] at this
        linarith
    _ ≤ 6 * (‖W‖ * ‖airyLead W‖) + ‖W‖ * ‖airyLead W‖ := by
        have := mul_le_mul_of_nonneg_right hη hL
        linarith
    _ = 7 * (‖W‖ * ‖airyLead W‖) := by ring

/-! ### The leading terms times the phase -/

lemma half_le_pi_ratio {N : ℝ} (_hN : 0 < N) (t : ℝ) (ht : √N = t) (ht0 : 0 < t) :
    1 / (2 * π) * √(π / N) ≤ 1 / 2 * t⁻¹ := by
  have hp : 1 ≤ √π := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have h1 : √π ≤ π := by nlinarith [Real.mul_self_sqrt Real.pi_pos.le]
  have h2 : 1 / (2 * π) * √π ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  rw [Real.sqrt_div Real.pi_pos.le, ht]
  calc 1 / (2 * π) * (√π / t) = (1 / (2 * π) * √π) * t⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ 1 / 2 * t⁻¹ := mul_le_mul_of_nonneg_right h2 (by positivity)

lemma norm_root_eq {w q : ℂ} (hq : q = w ^ (1 / 2 : ℂ)) : ‖q‖ = ‖w‖ ^ (1 / 2 : ℝ) := by
  rw [hq, norm_cpow_half, Real.sqrt_eq_rpow]

lemma sqrt_norm_root {w q : ℂ} (hq : q = w ^ (1 / 2 : ℂ)) : √‖q‖ = ‖w‖ ^ (1 / 4 : ℝ) := by
  rw [norm_root_eq hq, Real.sqrt_eq_rpow, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

lemma lead_P {w q : ℂ} (hq : q = w ^ (1 / 2 : ℂ)) (hw0 : 0 < ‖w‖) :
    ‖airyLead (airyEps * q)‖ * ‖cexp (I * negPhase w)‖ ≤ 1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by
  have hq0 : 0 < ‖q‖ := by rw [norm_root_eq hq]; positivity
  have hph : negPhase w = (2 / 3 : ℂ) * q ^ 3 := by rw [hq]; rfl
  have hre : (I * negPhase w).re = -((2 / 3 : ℂ) * q ^ 3).im := by
    rw [hph]; simp [Complex.mul_re]
  rw [norm_airyLead, airyNorm_eps_mul, Complex.norm_exp, Complex.norm_exp, airyRe_phase_eps, hre]
  have e : Real.exp (((2 / 3 : ℂ) * q ^ 3).im) * Real.exp (-((2 / 3 : ℂ) * q ^ 3).im) = 1 := by
    rw [← Real.exp_add]; simp
  have hN := sqrt_norm_root hq
  have hpos : 0 < ‖w‖ ^ (1 / 4 : ℝ) := by positivity
  have hb := half_le_pi_ratio hq0 _ hN hpos
  calc 1 / (2 * π) * Real.exp (((2 / 3 : ℂ) * q ^ 3).im) * √(π / ‖q‖) *
        Real.exp (-((2 / 3 : ℂ) * q ^ 3).im)
      = 1 / (2 * π) * √(π / ‖q‖) *
        (Real.exp (((2 / 3 : ℂ) * q ^ 3).im) * Real.exp (-((2 / 3 : ℂ) * q ^ 3).im)) := by ring
    _ = 1 / (2 * π) * √(π / ‖q‖) := by rw [e, mul_one]
    _ ≤ 1 / 2 * (‖w‖ ^ (1 / 4 : ℝ))⁻¹ := hb
    _ = 1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_neg (norm_nonneg _)]

lemma lead_M {w q : ℂ} (hq : q = w ^ (1 / 2 : ℂ)) (hw0 : 0 < ‖w‖) :
    ‖airyLead ((starRingEnd ℂ) airyEps * q)‖ * ‖cexp (-(I * negPhase w))‖ ≤
      1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by
  have hq0 : 0 < ‖q‖ := by rw [norm_root_eq hq]; positivity
  have hph : negPhase w = (2 / 3 : ℂ) * q ^ 3 := by rw [hq]; rfl
  have hre : (-(I * negPhase w)).re = ((2 / 3 : ℂ) * q ^ 3).im := by
    rw [hph]; simp [Complex.mul_re]
  rw [norm_airyLead, airyNorm_conj_eps_mul, Complex.norm_exp, Complex.norm_exp, airyRe_phase_conj_eps, hre]
  have e : Real.exp (-((2 / 3 : ℂ) * q ^ 3).im) * Real.exp (((2 / 3 : ℂ) * q ^ 3).im) = 1 := by
    rw [← Real.exp_add]; simp
  have hN := sqrt_norm_root hq
  have hpos : 0 < ‖w‖ ^ (1 / 4 : ℝ) := by positivity
  have hb := half_le_pi_ratio hq0 _ hN hpos
  calc 1 / (2 * π) * Real.exp (-((2 / 3 : ℂ) * q ^ 3).im) * √(π / ‖q‖) *
        Real.exp (((2 / 3 : ℂ) * q ^ 3).im)
      = 1 / (2 * π) * √(π / ‖q‖) *
        (Real.exp (-((2 / 3 : ℂ) * q ^ 3).im) * Real.exp (((2 / 3 : ℂ) * q ^ 3).im)) := by ring
    _ = 1 / (2 * π) * √(π / ‖q‖) := by rw [e, mul_one]
    _ ≤ 1 / 2 * (‖w‖ ^ (1 / 4 : ℝ))⁻¹ := hb
    _ = 1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_neg (norm_nonneg _)]

/-! ### Amplitude bounds on the sector -/

theorem negAmpP_bound {w : ℂ} (hre : 0 < w.re) (him : |w.im| < w.re / 2) (h1 : 1 ≤ ‖w‖) :
    ‖negAmpP w‖ ≤ 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨hq, hq1⟩ := root_sector hre him h1
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = w ^ (1 / 2 : ℂ) := ⟨_, rfl⟩
  rw [← hqdef] at hq hq1
  have hq2 : q ^ 2 = w := by rw [hqdef]; exact cpow_half_sq w
  have hsq : (airyEps * q) ^ 2 = airyOmega ^ 2 * (-w) := by
    rw [mul_pow, airyEps_sq, hq2]; ring
  have hW := ai_sq_le (W := airyEps * q) (by rw [airyNorm_eps_mul]; exact hq1)
    (by rw [airyNorm_eps_mul]; exact hq.re_eps)
  rw [hsq] at hW
  have hw0 : 0 < ‖w‖ := by linarith
  have hl := lead_P hqdef hw0
  have hE := norm_nonneg (cexp (I * negPhase w))
  unfold negAmpP
  rw [norm_mul, norm_neg, norm_mul, norm_pow, norm_airyOmega, one_pow, one_mul]
  calc ‖airyAiC (airyOmega ^ 2 * -w)‖ * ‖cexp (I * negPhase w)‖
      ≤ 3 * ‖airyLead (airyEps * q)‖ * ‖cexp (I * negPhase w)‖ := mul_le_mul_of_nonneg_right hW hE
    _ = 3 * (‖airyLead (airyEps * q)‖ * ‖cexp (I * negPhase w)‖) := by ring
    _ ≤ 3 * (1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ))) := by gcongr
    _ ≤ 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by
        have : 0 ≤ ‖w‖ ^ (-(1 / 4 : ℝ)) := by positivity
        linarith

theorem negAmpM_bound {w : ℂ} (hre : 0 < w.re) (him : |w.im| < w.re / 2) (h1 : 1 ≤ ‖w‖) :
    ‖negAmpM w‖ ≤ 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨hq, hq1⟩ := root_sector hre him h1
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = w ^ (1 / 2 : ℂ) := ⟨_, rfl⟩
  rw [← hqdef] at hq hq1
  have hq2 : q ^ 2 = w := by rw [hqdef]; exact cpow_half_sq w
  have hsq : ((starRingEnd ℂ) airyEps * q) ^ 2 = airyOmega * (-w) := by
    rw [mul_pow, airyConj_eps_sq, hq2]; ring
  have hW := ai_sq_le (W := (starRingEnd ℂ) airyEps * q) (by rw [airyNorm_conj_eps_mul]; exact hq1)
    (by rw [airyNorm_conj_eps_mul]; exact hq.re_conj_eps)
  rw [hsq] at hW
  have hw0 : 0 < ‖w‖ := by linarith
  have hl := lead_M hqdef hw0
  have hE := norm_nonneg (cexp (-(I * negPhase w)))
  unfold negAmpM
  rw [norm_mul, norm_neg, norm_mul, norm_airyOmega, one_mul]
  calc ‖airyAiC (airyOmega * -w)‖ * ‖cexp (-(I * negPhase w))‖
      ≤ 3 * ‖airyLead ((starRingEnd ℂ) airyEps * q)‖ * ‖cexp (-(I * negPhase w))‖ :=
        mul_le_mul_of_nonneg_right hW hE
    _ = 3 * (‖airyLead ((starRingEnd ℂ) airyEps * q)‖ * ‖cexp (-(I * negPhase w))‖) := by ring
    _ ≤ 3 * (1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ))) := by gcongr
    _ ≤ 2 * ‖w‖ ^ (-(1 / 4 : ℝ)) := by
        have : 0 ≤ ‖w‖ ^ (-(1 / 4 : ℝ)) := by positivity
        linarith

/-- `‖q‖ * ‖w‖^{-1/4} = ‖w‖^{1/4}`. -/
lemma norm_root_mul {w q : ℂ} (hq : q = w ^ (1 / 2 : ℂ)) (hw0 : 0 < ‖w‖) :
    ‖q‖ * ‖w‖ ^ (-(1 / 4 : ℝ)) = ‖w‖ ^ (1 / 4 : ℝ) := by
  rw [norm_root_eq hq, ← Real.rpow_add hw0]; norm_num

theorem negAmpP'_bound {w : ℂ} (hre : 0 < w.re) (him : |w.im| < w.re / 2) (h1 : 1 ≤ ‖w‖) :
    ‖negAmpP' w‖ ≤ 4 * ‖w‖ ^ (-(-(1 / 4 : ℝ))) := by
  obtain ⟨hq, hq1⟩ := root_sector hre him h1
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = w ^ (1 / 2 : ℂ) := ⟨_, rfl⟩
  rw [← hqdef] at hq hq1
  have hq2 : q ^ 2 = w := by rw [hqdef]; exact cpow_half_sq w
  have hsq : (airyEps * q) ^ 2 = airyOmega ^ 2 * (-w) := by
    rw [mul_pow, airyEps_sq, hq2]; ring
  have hW := aip_sq_le (W := airyEps * q) (by rw [airyNorm_eps_mul]; exact hq1)
    (by rw [airyNorm_eps_mul]; exact hq.re_eps)
  rw [hsq, airyNorm_eps_mul] at hW
  have hw0 : 0 < ‖w‖ := by linarith
  have hl := lead_P hqdef hw0
  have hE := norm_nonneg (cexp (I * negPhase w))
  have hqn := norm_root_mul hqdef hw0
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  unfold negAmpP'
  rw [norm_mul, norm_neg, norm_mul, norm_airyOmega, one_mul]
  calc ‖deriv airyAiC (airyOmega ^ 2 * -w)‖ * ‖cexp (I * negPhase w)‖
      ≤ 7 * (‖q‖ * ‖airyLead (airyEps * q)‖) * ‖cexp (I * negPhase w)‖ := mul_le_mul_of_nonneg_right hW hE
    _ = 7 * ‖q‖ * (‖airyLead (airyEps * q)‖ * ‖cexp (I * negPhase w)‖) := by ring
    _ ≤ 7 * ‖q‖ * (1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ))) := by gcongr
    _ = 7 / 2 * (‖q‖ * ‖w‖ ^ (-(1 / 4 : ℝ))) := by ring
    _ = 7 / 2 * ‖w‖ ^ (1 / 4 : ℝ) := by rw [hqn]
    _ ≤ 4 * ‖w‖ ^ (-(-(1 / 4 : ℝ))) := by
        rw [neg_neg]
        have : 0 ≤ ‖w‖ ^ (1 / 4 : ℝ) := by positivity
        linarith

theorem negAmpM'_bound {w : ℂ} (hre : 0 < w.re) (him : |w.im| < w.re / 2) (h1 : 1 ≤ ‖w‖) :
    ‖negAmpM' w‖ ≤ 4 * ‖w‖ ^ (-(-(1 / 4 : ℝ))) := by
  obtain ⟨hq, hq1⟩ := root_sector hre him h1
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = w ^ (1 / 2 : ℂ) := ⟨_, rfl⟩
  rw [← hqdef] at hq hq1
  have hq2 : q ^ 2 = w := by rw [hqdef]; exact cpow_half_sq w
  have hsq : ((starRingEnd ℂ) airyEps * q) ^ 2 = airyOmega * (-w) := by
    rw [mul_pow, airyConj_eps_sq, hq2]; ring
  have hW := aip_sq_le (W := (starRingEnd ℂ) airyEps * q) (by rw [airyNorm_conj_eps_mul]; exact hq1)
    (by rw [airyNorm_conj_eps_mul]; exact hq.re_conj_eps)
  rw [hsq, airyNorm_conj_eps_mul] at hW
  have hw0 : 0 < ‖w‖ := by linarith
  have hl := lead_M hqdef hw0
  have hE := norm_nonneg (cexp (-(I * negPhase w)))
  have hqn := norm_root_mul hqdef hw0
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  unfold negAmpM'
  rw [norm_mul, norm_neg, norm_mul, norm_pow, norm_airyOmega, one_pow, one_mul]
  calc ‖deriv airyAiC (airyOmega * -w)‖ * ‖cexp (-(I * negPhase w))‖
      ≤ 7 * (‖q‖ * ‖airyLead ((starRingEnd ℂ) airyEps * q)‖) * ‖cexp (-(I * negPhase w))‖ :=
        mul_le_mul_of_nonneg_right hW hE
    _ = 7 * ‖q‖ * (‖airyLead ((starRingEnd ℂ) airyEps * q)‖ * ‖cexp (-(I * negPhase w))‖) := by ring
    _ ≤ 7 * ‖q‖ * (1 / 2 * ‖w‖ ^ (-(1 / 4 : ℝ))) := by gcongr
    _ = 7 / 2 * (‖q‖ * ‖w‖ ^ (-(1 / 4 : ℝ))) := by ring
    _ = 7 / 2 * ‖w‖ ^ (1 / 4 : ℝ) := by rw [hqn]
    _ ≤ 4 * ‖w‖ ^ (-(-(1 / 4 : ℝ))) := by
        rw [neg_neg]
        have : 0 ≤ ‖w‖ ^ (1 / 4 : ℝ) := by positivity
        linarith

/-- info: 'FormalResearch.SignUncertainty.neg_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms neg_split
/-- info: 'FormalResearch.SignUncertainty.neg_split'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms neg_split'
/-- info: 'FormalResearch.SignUncertainty.negAmpP_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negAmpP_bound
/-- info: 'FormalResearch.SignUncertainty.negAmpM_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negAmpM_bound
/-- info: 'FormalResearch.SignUncertainty.negAmpP'_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negAmpP'_bound
/-- info: 'FormalResearch.SignUncertainty.negAmpM'_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negAmpM'_bound

end FormalResearch.SignUncertainty
