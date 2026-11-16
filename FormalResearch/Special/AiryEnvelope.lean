module

public import FormalResearch.Special.AiryEnvelopeBound

/-!
# The complex envelope of the Airy function

With `z^{3/2}` the principal branch (`z ^ (3/2 : ℂ)`, so `Re z^{3/2} = |z|^{3/2} cos(3 arg z / 2)` with
`arg z ∈ (-π, π]`, which vanishes on the closed negative axis from either side):

* **(E1)** `airyAiC_envelope`: for **all** `z ∈ ℂ`,
  `‖Ai(z)‖ ≤ 3 (1 + |z|)^{-1/4} exp(-(2/3) Re z^{3/2})`.
  The constant `3` is not optimal: the numerical supremum of `‖Ai‖ (1+|z|)^{1/4} exp((2/3) Re z^{3/2})`
  over `|z| ≤ 30` is about `0.64` (attained near `z = -1`).
* **(E1′)** `airyAiC_deriv_envelope`: `‖Ai'(z)‖ ≤ 5 (1 + |z|)^{1/4} exp(-(2/3) Re z^{3/2})` on all of `ℂ`.
* **Order 3/2** `airyAiC_norm_le_exp_rpow`: `‖Ai(z)‖ ≤ 3 exp((2/3) |z|^{3/2})`, and likewise for `Ai'`.
* **Squared envelope** `airyAiC_norm_sq_le`: `‖Ai(z)‖² ≤ 9 (1 + |z|)^{-1/2} e(z)`,
  `e(z) = exp(-(4/3) Re z^{3/2})` (`airyEnv`).

Mechanism: `z = w²` with `w = z^{1/2}` the principal root (`Re w ≥ 0`, `w³ = z^{3/2}`), see `AiryEnvelopeBound`.
On `|arg z| ≤ 2π/3` the bound is the Laplace estimate with the contour through the saddle `Re t = Re √z`
(this is exact: `c³/3 - c Re z + (Im z)²/(4c) = -(2/3) Re z^{3/2}` for `c = Re √z`); the remaining sector
`2π/3 < |arg z| ≤ π` is reduced to it by `Ai(z) = -ω Ai(ωz) - ω² Ai(ω²z)`.
Nothing here is an asymptotic expansion: there is no `1 + o(1)`, only the uniform two-sided-in-`z` envelope.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The principal square root squares back to `z`. -/
lemma cpow_half_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  have := cpow_nat_inv_pow z (n := 2) two_ne_zero
  simp [one_div] at this ⊢

/-- `(z^{1/2})³ = z^{3/2}` for the principal branch. -/
lemma cpow_half_cube (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 3 = z ^ (3 / 2 : ℂ) := by
  have := cpow_nat_mul z 3 (1 / 2 : ℂ)
  rw [show ((3 : ℕ) : ℂ) * (1 / 2 : ℂ) = 3 / 2 by push_cast; ring] at this
  exact this.symm

/-- The principal square root has nonnegative real part. -/
lemma cpow_half_re_nonneg (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by
  by_cases hz : z = 0
  · subst hz; simp
  rw [cpow_def_of_ne_zero hz, Complex.exp_re]
  refine mul_nonneg (Real.exp_pos _).le ?_
  have h1 : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by
    simp [Complex.log_im]; ring
  rw [h1]
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Complex.neg_pi_lt_arg z])
    (by linarith [Complex.arg_le_pi z])

lemma norm_cpow_half_sq (z : ℂ) : ‖z ^ (1 / 2 : ℂ)‖ ^ 2 = ‖z‖ := by
  rw [← norm_pow, cpow_half_sq]

lemma norm_cpow_half (z : ℂ) : ‖z ^ (1 / 2 : ℂ)‖ = √‖z‖ := by
  rw [← norm_cpow_half_sq z, Real.sqrt_sq (norm_nonneg _)]

/-- `‖z^{3/2}‖ = ‖z‖^{3/2}`. -/
lemma norm_cpow_three_halves (z : ℂ) : ‖z ^ (3 / 2 : ℂ)‖ = ‖z‖ ^ (3 / 2 : ℝ) := by
  by_cases hz : z = 0
  · subst hz; simp
  rw [← cpow_half_cube, norm_pow, norm_cpow_half, sqrt_cube_eq_rpow (norm_pos_iff.mpr hz)]

lemma re_cpow_three_halves_le (z : ℂ) : -(z ^ (3 / 2 : ℂ)).re ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
  rw [← norm_cpow_three_halves]
  have := Complex.abs_re_le_norm (z ^ (3 / 2 : ℂ))
  linarith [neg_abs_le (z ^ (3 / 2 : ℂ)).re]

/-- **(E1)** The complex envelope: for all `z ∈ ℂ` (principal branch of `z^{3/2}`),
`‖Ai(z)‖ ≤ 3 (1 + |z|)^{-1/4} exp(-(2/3) Re z^{3/2})`. -/
theorem airyAiC_envelope (z : ℂ) :
    ‖airyAiC z‖ ≤ 3 * (1 + ‖z‖) ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re) := by
  have h := airy_sq_envelope (cpow_half_re_nonneg z)
  rw [cpow_half_sq, norm_cpow_half_sq, cpow_half_cube] at h
  have hq0 : 0 < (1 + ‖z‖) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have : 3 * (1 + ‖z‖) ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re) =
      (3 * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) / (1 + ‖z‖) ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_neg (by positivity)]; field_simp
  rw [this, le_div_iff₀ hq0]
  exact h

/-- **(E1′)** The envelope for the derivative: for all `z ∈ ℂ`,
`‖Ai'(z)‖ ≤ 5 (1 + |z|)^{1/4} exp(-(2/3) Re z^{3/2})`. -/
theorem airyAiC_deriv_envelope (z : ℂ) :
    ‖deriv airyAiC z‖ ≤ 5 * (1 + ‖z‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re) := by
  have h := airy_deriv_sq_envelope (cpow_half_re_nonneg z)
  rwa [cpow_half_sq, norm_cpow_half_sq, cpow_half_cube] at h

lemma rpow_neg_quarter_le_one (z : ℂ) : (1 + ‖z‖) ^ (-(1 / 4) : ℝ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by norm_num)

/-- **Order `3/2`**: `‖Ai(z)‖ ≤ 3 exp((2/3) |z|^{3/2})` on `ℂ`. -/
theorem airyAiC_norm_le_exp_rpow (z : ℂ) :
    ‖airyAiC z‖ ≤ 3 * Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) := by
  refine (airyAiC_envelope z).trans ?_
  have h1 := rpow_neg_quarter_le_one z
  have h2 : Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re) ≤ Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [re_cpow_three_halves_le z])
  have h3 := Real.exp_pos (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)
  have h4 : 0 < (1 + ‖z‖) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  calc 3 * (1 + ‖z‖) ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)
      ≤ 3 * 1 * Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) := by gcongr
    _ = _ := by ring

/-- **Order `3/2` for the derivative**: `‖Ai'(z)‖ ≤ 5 (1+|z|)^{1/4} exp((2/3) |z|^{3/2})`. -/
theorem airyAiC_deriv_norm_le_exp_rpow (z : ℂ) :
    ‖deriv airyAiC z‖ ≤ 5 * (1 + ‖z‖) ^ (1 / 4 : ℝ) * Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) := by
  refine (airyAiC_deriv_envelope z).trans ?_
  have h2 : Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re) ≤ Real.exp ((2 / 3) * ‖z‖ ^ (3 / 2 : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [re_cpow_three_halves_le z])
  have h4 : 0 < (1 + ‖z‖) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  gcongr

/-- The squared envelope `e(z) = exp(-(4/3) Re z^{3/2})` (principal branch). -/
noncomputable def airyEnv (z : ℂ) : ℝ := Real.exp (-(4 / 3) * (z ^ (3 / 2 : ℂ)).re)

lemma airyEnv_pos (z : ℂ) : 0 < airyEnv z := Real.exp_pos _

/-- **Squared envelope**: `‖Ai(z)‖² ≤ 9 (1 + |z|)^{-1/2} e(z)`, `e(z) = exp(-(4/3) Re z^{3/2})`. -/
theorem airyAiC_norm_sq_le (z : ℂ) :
    ‖airyAiC z‖ ^ 2 ≤ 9 * (1 + ‖z‖) ^ (-(1 / 2) : ℝ) * airyEnv z := by
  have h := airyAiC_envelope z
  have h0 := norm_nonneg (airyAiC z)
  have h1 := pow_le_pow_left₀ h0 h 2
  refine h1.trans (le_of_eq ?_)
  have e1 : ((1 + ‖z‖) ^ (-(1 / 4) : ℝ)) ^ 2 = (1 + ‖z‖) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have e2 : (Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2 = airyEnv z := by
    rw [airyEnv, ← Real.exp_nat_mul]; norm_num; ring_nf
  calc (3 * (1 + ‖z‖) ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2
      = 9 * ((1 + ‖z‖) ^ (-(1 / 4) : ℝ)) ^ 2 * (Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2 := by
        ring
    _ = _ := by rw [e1, e2]

/-- info: 'FormalResearch.Special.airyAiC_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_envelope

/-- info: 'FormalResearch.Special.airyAiC_deriv_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_deriv_envelope

/-- info: 'FormalResearch.Special.airyAiC_norm_le_exp_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_norm_le_exp_rpow

/-- info: 'FormalResearch.Special.airyAiC_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_norm_sq_le

end FormalResearch.Special
