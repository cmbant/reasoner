module

public import FormalResearch.Special.AiryAsymNegComplex

/-!
# `Ai'` near the negative axis: the complex two-exponential asymptotics with remainder

The derivative analogue of `AiryAsymNegComplex.airyAiC_neg_complex` (DLMF 9.7.10 in a complex neighbourhood of the
negative axis, explicit remainder).  For `q ∈ ℂ`, `q ≠ 0`, `|arg q| ≤ π/6` (`NegSector`), `ξ = (2/3) q³`,
`τ = (π/q)^{1/2}` (principal root):

* `deriv_airyAiC_neg_complex`:
  `‖Ai'(-q²) - (1/π) q τ sin(ξ - π/4)‖ ≤ (41/10) e^{|Im ξ|} (√(π/‖q‖)/π) / ‖q‖²`.

In terms of `r = ‖z‖ = ‖q‖²` the relative remainder (against the size `r^{1/4} e^{|Im ξ|}` of `Ai'`) is `O(r^{-3/2})`,
exactly as for `Ai`.  Proof: the derivative of the rotation identity (`airyAiC_rotation_deriv`) at `z = -q²` gives
`Ai'(-q²) = -ω² Ai'((ε̄ q)²) - ω Ai'((ε q)²)`; the sector estimate
`norm_deriv_airyAiC_sq_add_lead_le` (`s = 1/2`) replaces each `Ai'((ε^{±1} q)²)` by `-(ε^{±1} q) L(ε^{±1} q)`, and the two
leading terms combine, via `ω² ε̄ e^{iπ/12} = -e^{iπ/4}` and `ω ε e^{-iπ/12} = -e^{-iπ/4}`, into
`(1/π) q τ sin(ξ - π/4)`.

Numerical check (mpmath, 30 digits; `‖q‖ ∈ {0.5, 1, 2, 3, 5, 8, 15, 30}`, 61 angles across `|arg q| ≤ π/6`): the true
error is at most `0.036` times the stated bound.

Used by `AiryCft2ComboBounds` (good circles for `P·Ai + Q·Ai'`).  Not formalised: the `Bi'` combination (not needed:
`Bi' - iAi'` is a rotated `Ai'`, `AiryCft2ComboBounds`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### Phase identities -/

lemma airyC2_omega_sq_conj_eps_exp :
    airyOmega ^ 2 * (starRingEnd ℂ) airyEps * cexp (((π / 12 : ℝ) : ℂ) * I) =
      -cexp (((π / 4 : ℝ) : ℂ) * I) := by
  rw [airyOmega_sq_eq_exp, conj_airyEps_eq_exp, ← Complex.exp_add, ← Complex.exp_add]
  have h1 : -cexp (((π / 4 : ℝ) : ℂ) * I) = cexp (((π / 4 : ℝ) : ℂ) * I + π * I) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring
  rw [h1, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨0, ?_⟩
  push_cast
  ring

lemma airyC2_omega_eps_exp :
    airyOmega * airyEps * cexp (((-(π / 12) : ℝ) : ℂ) * I) = -cexp (((-(π / 4) : ℝ) : ℂ) * I) := by
  rw [airyOmega_eq_exp', airyEps_eq_exp', ← Complex.exp_add, ← Complex.exp_add]
  have h1 : -cexp (((-(π / 4) : ℝ) : ℂ) * I) = cexp (((-(π / 4) : ℝ) : ℂ) * I + π * I) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring
  rw [h1, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨0, ?_⟩
  push_cast
  ring

/-- `-ω Ai'((ε̄q)²)`-type leading terms combine: `ω² (ε̄ q) L(ε̄ q) + ω (ε q) L(ε q) = (1/π) q τ sin(ξ - π/4)`. -/
lemma airyC2_lead_sum_eq {q : ℂ} (hq : NegSector q) (hq0 : 0 < ‖q‖) :
    airyOmega ^ 2 * (((starRingEnd ℂ) airyEps * q) * airyLead ((starRingEnd ℂ) airyEps * q)) +
        airyOmega * ((airyEps * q) * airyLead (airyEps * q)) =
      (1 / (π : ℂ)) * q * ((π : ℂ) / q) ^ (1 / 2 : ℂ) * Complex.sin ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ)) := by
  rw [airyLead_eps_mul hq hq0, airyLead_conj_eps_mul hq hq0]
  set τ := ((π : ℂ) / q) ^ (1 / 2 : ℂ)
  set ξ : ℂ := (2 / 3 : ℂ) * q ^ 3
  have h1 := airyC2_omega_sq_conj_eps_exp
  have h2 := airyC2_omega_eps_exp
  have hsin : Complex.sin (ξ - (π / 4 : ℂ)) = -Complex.cos (ξ + (π / 4 : ℂ)) := by
    have := Complex.cos_add_pi_div_two (ξ - (π / 4 : ℂ))
    have e : ξ - (π / 4 : ℂ) + (π : ℂ) / 2 = ξ + (π / 4 : ℂ) := by ring
    rw [e] at this
    linear_combination this
  have hc : 2 * Complex.cos (ξ + (π / 4 : ℂ)) =
      cexp (I * ξ) * cexp (((π / 4 : ℝ) : ℂ) * I) + cexp (-(I * ξ)) * cexp (((-(π / 4) : ℝ) : ℂ) * I) := by
    rw [Complex.two_cos, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [hsin]
  have hcos : Complex.cos (ξ + (π / 4 : ℂ)) = 1 / 2 *
      (cexp (I * ξ) * cexp (((π / 4 : ℝ) : ℂ) * I) + cexp (-(I * ξ)) * cexp (((-(π / 4) : ℝ) : ℂ) * I)) := by
    rw [← hc]; ring
  rw [hcos]
  linear_combination (1 / (2 * (π : ℂ)) * cexp (I * ξ) * τ * q) * h1 +
    (1 / (2 * (π : ℂ)) * cexp (-(I * ξ)) * τ * q) * h2

/-! ### The remainder -/

lemma airyC2_const_le {N : ℝ} (hN : 0 < N) :
    17 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * N ^ 3) ≤ 41 / 10 / N ^ 3 := by
  have h : (7 / 10 : ℝ) ≤ √(1 / 2 : ℝ) := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have hpos : 0 < (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * N ^ 3 := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have : (7 / 80 : ℝ) * N ^ 3 ≤ (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * N ^ 3 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ (1 / 2) ^ 3))
      (by positivity : (0:ℝ) ≤ N ^ 3)
    nlinarith
  nlinarith [pow_pos hN 3]

/-- **`Ai'` in a complex neighbourhood of the negative axis** (DLMF 9.7.10 with explicit remainder).
For `q ≠ 0` with `|arg q| ≤ π/6` (`NegSector`), `ξ = (2/3) q³`:
`‖Ai'(-q²) - (1/π) q (π/q)^{1/2} sin(ξ - π/4)‖ ≤ (41/10) e^{|Im ξ|} (√(π/‖q‖)/π) / ‖q‖²`. -/
theorem deriv_airyAiC_neg_complex {q : ℂ} (hq : NegSector q) (hq0 : 0 < ‖q‖) :
    ‖deriv airyAiC (-(q ^ 2)) - (1 / (π : ℂ)) * q * ((π : ℂ) / q) ^ (1 / 2 : ℂ) *
        Complex.sin ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ≤
      41 / 10 * Real.exp |((2 / 3 : ℂ) * q ^ 3).im| * (√(π / ‖q‖) / π) / ‖q‖ ^ 2 := by
  set Y := |((2 / 3 : ℂ) * q ^ 3).im| with hY
  have hre : 0 < q.re := lt_of_lt_of_le (by positivity) hq
  have hw1 := hq.re_conj_eps
  have hw2 := hq.re_eps
  set w1 : ℂ := (starRingEnd ℂ) airyEps * q with hw1def
  set w2 : ℂ := airyEps * q with hw2def
  have hrot := airyAiC_rotation_deriv (-(q ^ 2))
  have e1 : airyOmega * (-(q ^ 2)) = w1 ^ 2 := by
    rw [hw1def, mul_pow, airyConj_eps_sq]; ring
  have e2 : airyOmega ^ 2 * (-(q ^ 2)) = w2 ^ 2 := by
    rw [hw2def, mul_pow, airyEps_sq]; ring
  rw [e1, e2, airyOmega_pow_four] at hrot
  have e : deriv airyAiC (-(q ^ 2)) - (1 / (π : ℂ)) * q * ((π : ℂ) / q) ^ (1 / 2 : ℂ) *
        Complex.sin ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ)) =
      -(airyOmega ^ 2 * (deriv airyAiC (w1 ^ 2) + w1 * airyLead w1)) -
        airyOmega * (deriv airyAiC (w2 ^ 2) + w2 * airyLead w2) := by
    rw [← airyC2_lead_sum_eq hq hq0]
    linear_combination hrot
  rw [e]
  have b1 := norm_deriv_airyAiC_sq_add_lead_le (w := w1) (s := 1 / 2) (by norm_num) (by norm_num)
    (by rw [hw1def, airyNorm_conj_eps_mul]; linarith) (by linarith)
  have b2 := norm_deriv_airyAiC_sq_add_lead_le (w := w2) (s := 1 / 2) (by norm_num) (by norm_num)
    (by rw [hw2def, airyNorm_eps_mul]; linarith) (by linarith)
  have nw1 : ‖w1‖ = ‖q‖ := airyNorm_conj_eps_mul q
  have nw2 : ‖w2‖ = ‖q‖ := airyNorm_eps_mul q
  rw [nw1] at b1
  rw [nw2] at b2
  have c := airyC2_const_le hq0
  have n1 : ‖airyLead w1‖ ≤ 1 / (2 * π) * Real.exp Y * √(π / ‖q‖) := by
    rw [norm_airyLead, nw1]
    have := airyNorm_cexp_le_of_re (w := w1) (Y := Y) (by
      rw [hw1def, airyRe_phase_conj_eps]; exact (neg_le_abs _).trans (le_of_eq hY.symm))
    gcongr
  have n2 : ‖airyLead w2‖ ≤ 1 / (2 * π) * Real.exp Y * √(π / ‖q‖) := by
    rw [norm_airyLead, nw2]
    have := airyNorm_cexp_le_of_re (w := w2) (Y := Y) (by
      rw [hw2def, airyRe_phase_eps]; exact (le_abs_self _).trans (le_of_eq hY.symm))
    gcongr
  have hω : ‖airyOmega‖ = 1 := norm_airyOmega
  have hω2 : ‖airyOmega ^ 2‖ = 1 := norm_airyOmega_sq
  have hN3 : 0 < ‖q‖ ^ 3 := by positivity
  have hc : 0 ≤ 41 / 10 / ‖q‖ ^ 3 := by positivity
  have m1 : ‖w1 * airyLead w1‖ ≤ ‖q‖ * (1 / (2 * π) * Real.exp Y * √(π / ‖q‖)) := by
    rw [norm_mul, nw1]; exact mul_le_mul_of_nonneg_left n1 hq0.le
  have m2 : ‖w2 * airyLead w2‖ ≤ ‖q‖ * (1 / (2 * π) * Real.exp Y * √(π / ‖q‖)) := by
    rw [norm_mul, nw2]; exact mul_le_mul_of_nonneg_left n2 hq0.le
  calc ‖-(airyOmega ^ 2 * (deriv airyAiC (w1 ^ 2) + w1 * airyLead w1)) -
        airyOmega * (deriv airyAiC (w2 ^ 2) + w2 * airyLead w2)‖
      ≤ ‖deriv airyAiC (w1 ^ 2) + w1 * airyLead w1‖ + ‖deriv airyAiC (w2 ^ 2) + w2 * airyLead w2‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, norm_mul, hω, hω2, one_mul, one_mul]
    _ ≤ 41 / 10 / ‖q‖ ^ 3 * (‖q‖ * (1 / (2 * π) * Real.exp Y * √(π / ‖q‖))) +
        41 / 10 / ‖q‖ ^ 3 * (‖q‖ * (1 / (2 * π) * Real.exp Y * √(π / ‖q‖))) := by
        refine add_le_add (b1.trans ?_) (b2.trans ?_)
        · exact (mul_le_mul_of_nonneg_right c (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left m1 hc)
        · exact (mul_le_mul_of_nonneg_right c (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left m2 hc)
    _ = _ := by field_simp; ring

/-- info: 'FormalResearch.Special.deriv_airyAiC_neg_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.deriv_airyAiC_neg_complex

end FormalResearch.Special
