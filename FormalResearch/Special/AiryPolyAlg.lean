module

public import FormalResearch.Special.AiryCft2ComboAlg

/-!
# `N = P·Ai + Q·Ai'` for real **polynomials** `P, Q`: algebra and the upper bound for `M - iN`

Setting of `CFT/notes/general_theorems.tex` Lemma 1.0′ and `SOFT_EDGE_THEOREMS.md` Lemmas 4.4, 4.6 (the Blaschke-extension
Airy summation): `P, Q ∈ ℝ[X]`, `N = P Ai + Q Ai'`, `M = P Bi + Q Bi'`, `D = P (P + Q') - Q (P' + z Q)`.  The constant-coefficient
case is `AiryCft2ComboAlg` (`airyNC`, `D = P² - z Q²`); here:

* `airyPQc p z` : the complex evaluation of a real polynomial, with `HasDerivAt`, conjugation symmetry and the coefficient
  sum;
* `airyPQN`, `airyPQM`, `airyPQN'`, `airyPQM'`, `airyPQD` and the **Wronskian** `N M' - N' M = D/π`
  (`airyPQ_wronskian`; `(N, N')ᵀ = A (Ai, Ai')ᵀ` with `det A = D`), hence at a zero `t` of `N`: `N'(t) M(t) = -D(t)/π`;
* the **upper bound** `‖a (Bi - iAi) + b (Bi' - iAi')‖² e(u) ≤ 4 (3‖a‖ (1+|u|)^{-1/4} + 5‖b‖ (1+|u|)^{1/4})²` for
  `Im u ≥ 0` and arbitrary complex `a, b` (`airyAB_sub_I_mul_sq_le`), applied to `a = P(u)`, `b = Q(u)`
  (`airyPQ_sub_I_mul_sq_le`).

All proved (axiom-checked below).  Not formalised here: lower bounds (`AiryPolyCircle`), zeros (`AiryPolyZeros`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace FormalResearch.Special

/-! ### Complex evaluation of a real polynomial -/

/-- The complex evaluation of a real polynomial. -/
noncomputable def airyPQc (p : ℝ[X]) (z : ℂ) : ℂ := (p.map (algebraMap ℝ ℂ)).eval z

lemma airyPQc_eq_sum (p : ℝ[X]) (z : ℂ) :
    airyPQc p z = ∑ k ∈ Finset.range (p.natDegree + 1), (p.coeff k : ℂ) * z ^ k := by
  unfold airyPQc
  rw [Polynomial.eval_eq_sum_range' (n := p.natDegree + 1)]
  · simp [Polynomial.coeff_map]
  · exact lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _)

lemma airyPQc_add (p q : ℝ[X]) (z : ℂ) : airyPQc (p + q) z = airyPQc p z + airyPQc q z := by
  simp [airyPQc, Polynomial.map_add]

lemma airyPQc_mul (p q : ℝ[X]) (z : ℂ) : airyPQc (p * q) z = airyPQc p z * airyPQc q z := by
  simp [airyPQc, Polynomial.map_mul]

lemma airyPQc_zero (z : ℂ) : airyPQc 0 z = 0 := by simp [airyPQc]

lemma airyPQc_C (a : ℝ) (z : ℂ) : airyPQc (Polynomial.C a) z = (a : ℂ) := by simp [airyPQc]

lemma airyPQc_ofReal (p : ℝ[X]) (x : ℝ) : airyPQc p (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  have := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x (p := p)
  unfold airyPQc
  rw [Polynomial.eval_map]
  simpa using this

lemma hasDerivAt_airyPQc (p : ℝ[X]) (z : ℂ) :
    HasDerivAt (airyPQc p) (airyPQc (Polynomial.derivative p) z) z := by
  have := (p.map (algebraMap ℝ ℂ)).hasDerivAt z
  rw [Polynomial.derivative_map] at this
  exact this

lemma differentiable_airyPQc (p : ℝ[X]) : Differentiable ℂ (airyPQc p) :=
  fun z => (hasDerivAt_airyPQc p z).differentiableAt

lemma conj_airyPQc (p : ℝ[X]) (z : ℂ) : (starRingEnd ℂ) (airyPQc p z) = airyPQc p ((starRingEnd ℂ) z) := by
  rw [airyPQc_eq_sum, airyPQc_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, Complex.conj_ofReal]

/-! ### The combinations -/

/-- `N = P Ai + Q Ai'` for real polynomials `P`, `Q`. -/
noncomputable def airyPQN (P Q : ℝ[X]) (z : ℂ) : ℂ := airyPQc P z * airyAiC z + airyPQc Q z * deriv airyAiC z

/-- `M = P Bi + Q Bi'`. -/
noncomputable def airyPQM (P Q : ℝ[X]) (z : ℂ) : ℂ := airyPQc P z * airyBiC z + airyPQc Q z * airyBiC' z

/-- `N' = P' Ai + (P + Q') Ai' + z Q Ai`. -/
noncomputable def airyPQN' (P Q : ℝ[X]) (z : ℂ) : ℂ :=
  airyPQc (derivative P) z * airyAiC z + (airyPQc P z + airyPQc (derivative Q) z) * deriv airyAiC z +
    z * airyPQc Q z * airyAiC z

/-- `M' = P' Bi + (P + Q') Bi' + z Q Bi`. -/
noncomputable def airyPQM' (P Q : ℝ[X]) (z : ℂ) : ℂ :=
  airyPQc (derivative P) z * airyBiC z + (airyPQc P z + airyPQc (derivative Q) z) * airyBiC' z +
    z * airyPQc Q z * airyBiC z

/-- The weight function `D = P (P + Q') - Q (P' + z Q)`. -/
noncomputable def airyPQD (P Q : ℝ[X]) (z : ℂ) : ℂ :=
  airyPQc P z * (airyPQc P z + airyPQc (derivative Q) z) -
    airyPQc Q z * (airyPQc (derivative P) z + z * airyPQc Q z)

lemma hasDerivAt_airyPQN (P Q : ℝ[X]) (z : ℂ) : HasDerivAt (airyPQN P Q) (airyPQN' P Q z) z := by
  have h1 : HasDerivAt airyAiC (deriv airyAiC z) z := differentiable_airyAiC.differentiableAt.hasDerivAt
  have h2 := hasDerivAt_deriv_airyAiC z
  have := ((hasDerivAt_airyPQc P z).mul h1).add ((hasDerivAt_airyPQc Q z).mul h2)
  exact this.congr_deriv (by unfold airyPQN'; ring)

lemma hasDerivAt_airyPQM (P Q : ℝ[X]) (z : ℂ) : HasDerivAt (airyPQM P Q) (airyPQM' P Q z) z := by
  have h := isAirySol_airyBiC z
  have := ((hasDerivAt_airyPQc P z).mul h.1).add ((hasDerivAt_airyPQc Q z).mul h.2)
  exact this.congr_deriv (by unfold airyPQM'; ring)

lemma differentiable_airyPQN (P Q : ℝ[X]) : Differentiable ℂ (airyPQN P Q) :=
  fun z => (hasDerivAt_airyPQN P Q z).differentiableAt

lemma differentiable_airyPQM (P Q : ℝ[X]) : Differentiable ℂ (airyPQM P Q) :=
  fun z => (hasDerivAt_airyPQM P Q z).differentiableAt

lemma deriv_airyPQN (P Q : ℝ[X]) (z : ℂ) : deriv (airyPQN P Q) z = airyPQN' P Q z :=
  (hasDerivAt_airyPQN P Q z).deriv

/-- **Wronskian**: `N M' - N' M = D / π`. -/
theorem airyPQ_wronskian (P Q : ℝ[X]) (z : ℂ) :
    airyPQN P Q z * airyPQM' P Q z - airyPQN' P Q z * airyPQM P Q z = airyPQD P Q z * ((1 / π : ℝ) : ℂ) := by
  have hW := airyAiC_wronskian_airyBiC_eq z
  unfold airyPQN airyPQM' airyPQN' airyPQM airyPQD
  linear_combination
    (airyPQc P z * (airyPQc P z + airyPQc (derivative Q) z) -
      airyPQc Q z * (airyPQc (derivative P) z + z * airyPQc Q z)) * hW

/-- At a zero `t` of `N`: `N'(t) M(t) = -D(t)/π`. -/
theorem airyPQ_mul_at_zero {P Q : ℝ[X]} {t : ℂ} (h : airyPQN P Q t = 0) :
    airyPQN' P Q t * airyPQM P Q t = -(airyPQD P Q t * ((1 / π : ℝ) : ℂ)) := by
  have := airyPQ_wronskian P Q t
  rw [h, zero_mul, zero_sub] at this
  linear_combination -this

/-- At a zero `t` of `N` with `N'(t) ≠ 0`: `-π M(t)/N'(t) = D(t)/N'(t)²`. -/
lemma airyPQ_weight_eq (P Q : ℝ[X]) {t : ℂ} (h : airyPQN P Q t = 0) (hd : airyPQN' P Q t ≠ 0) :
    -((π : ℂ) * (airyPQM P Q t / airyPQN' P Q t)) = airyPQD P Q t / airyPQN' P Q t ^ 2 := by
  have h1 := airyPQ_mul_at_zero h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : ((1 / π : ℝ) : ℂ) = 1 / (π : ℂ) := by push_cast; ring
  rw [e] at h1
  field_simp
  field_simp at h1
  linear_combination -h1

/-! ### Conjugation -/

lemma conj_airyPQN (P Q : ℝ[X]) (z : ℂ) : (starRingEnd ℂ) (airyPQN P Q z) = airyPQN P Q ((starRingEnd ℂ) z) := by
  unfold airyPQN
  rw [map_add, map_mul, map_mul, conj_airyPQc, conj_airyPQc, conj_airyAiC, conj_deriv_airyAiC]

lemma conj_airyPQM (P Q : ℝ[X]) (z : ℂ) : (starRingEnd ℂ) (airyPQM P Q z) = airyPQM P Q ((starRingEnd ℂ) z) := by
  unfold airyPQM
  rw [map_add, map_mul, map_mul, conj_airyPQc, conj_airyPQc, conj_airyBiC, conj_airyBiC']

/-! ### The upper bound for `M - iN` -/

/-- `a (Bi - iAi) + b (Bi' - iAi') = 2 ε̄ (a Ai(ω² z) + b ω² Ai'(ω² z))`. -/
theorem airyAB_sub_I_mul (a b z : ℂ) :
    a * (airyBiC z - I * airyAiC z) + b * (airyBiC' z - I * deriv airyAiC z) =
      2 * (starRingEnd ℂ) airyEps *
        (a * airyAiC (airyOmega ^ 2 * z) + b * (airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z))) := by
  rw [airyBiC_sub_I_mul_airyAiC z, airyBiC'_sub_I_mul z]
  ring

lemma airyPQ_sub_I_mul (P Q : ℝ[X]) (z : ℂ) :
    airyPQM P Q z - I * airyPQN P Q z =
      airyPQc P z * (airyBiC z - I * airyAiC z) + airyPQc Q z * (airyBiC' z - I * deriv airyAiC z) := by
  unfold airyPQM airyPQN; ring

/-- **Upper bound for the numerator** (`Im u ≥ 0`, arbitrary complex `a`, `b`):
`‖a (Bi - iAi)(u) + b (Bi' - iAi')(u)‖² e(u) ≤ 4 (3‖a‖(1+‖u‖)^{-1/4} + 5‖b‖(1+‖u‖)^{1/4})²`. -/
theorem airyAB_sub_I_mul_sq_le (a b : ℂ) {u : ℂ} (hu : 0 ≤ u.im) :
    ‖a * (airyBiC u - I * airyAiC u) + b * (airyBiC' u - I * deriv airyAiC u)‖ ^ 2 * airyEnv u ≤
      4 * (3 * ‖a‖ * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) + 5 * ‖b‖ * (1 + ‖u‖) ^ (1 / 4 : ℝ)) ^ 2 := by
  set w : ℂ := airyOmega ^ 2 * u with hw
  have hwn : ‖w‖ = ‖u‖ := by rw [hw, norm_mul, norm_airyOmega_sq, one_mul]
  have hre : (w ^ (3 / 2 : ℂ)).re = -(u ^ (3 / 2 : ℂ)).re := re_cpow_three_halves_omega_sq hu
  set s : ℝ := Real.exp ((2 / 3) * (u ^ (3 / 2 : ℂ)).re) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hss : s ^ 2 * airyEnv u = 1 := by
    rw [hs, airyEnv, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [← Real.exp_zero]; congr 1; push_cast; ring
  have hE := airyAiC_envelope w
  have hD := airyAiC_deriv_envelope w
  rw [hre, hwn] at hE hD
  have e1 : Real.exp (-(2 / 3) * -(u ^ (3 / 2 : ℂ)).re) = s := by rw [hs]; congr 1; ring
  rw [e1] at hE hD
  have hnum : ‖a * (airyBiC u - I * airyAiC u) + b * (airyBiC' u - I * deriv airyAiC u)‖ ≤
      2 * (3 * ‖a‖ * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) + 5 * ‖b‖ * (1 + ‖u‖) ^ (1 / 4 : ℝ)) * s := by
    rw [airyAB_sub_I_mul, norm_mul, norm_mul, Complex.norm_two, norm_conj_airyEps, mul_one]
    have h1 : ‖a * airyAiC w + b * (airyOmega ^ 2 * deriv airyAiC w)‖ ≤
        (3 * ‖a‖ * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) + 5 * ‖b‖ * (1 + ‖u‖) ^ (1 / 4 : ℝ)) * s := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_airyOmega, one_pow, one_mul]
      have h1 : ‖a‖ * ‖airyAiC w‖ ≤ ‖a‖ * (3 * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) * s) :=
        mul_le_mul_of_nonneg_left hE (norm_nonneg _)
      have h2 : ‖b‖ * ‖deriv airyAiC w‖ ≤ ‖b‖ * (5 * (1 + ‖u‖) ^ (1 / 4 : ℝ) * s) :=
        mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      nlinarith
    nlinarith
  calc _ ≤ (2 * (3 * ‖a‖ * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) + 5 * ‖b‖ * (1 + ‖u‖) ^ (1 / 4 : ℝ)) * s) ^ 2 *
        airyEnv u :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnum 2) (airyEnv_pos u).le
    _ = 4 * (3 * ‖a‖ * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) + 5 * ‖b‖ * (1 + ‖u‖) ^ (1 / 4 : ℝ)) ^ 2 *
        (s ^ 2 * airyEnv u) := by ring
    _ = _ := by rw [hss]; ring

/-- **Upper bound for `M - iN`** (`Im u ≥ 0`). -/
theorem airyPQ_sub_I_mul_sq_le (P Q : ℝ[X]) {u : ℂ} (hu : 0 ≤ u.im) :
    ‖airyPQM P Q u - I * airyPQN P Q u‖ ^ 2 * airyEnv u ≤
      4 * (3 * ‖airyPQc P u‖ * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) +
        5 * ‖airyPQc Q u‖ * (1 + ‖u‖) ^ (1 / 4 : ℝ)) ^ 2 := by
  rw [airyPQ_sub_I_mul]
  exact airyAB_sub_I_mul_sq_le _ _ hu

/-- info: 'FormalResearch.Special.airyPQ_wronskian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_wronskian

/-- info: 'FormalResearch.Special.airyAB_sub_I_mul_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAB_sub_I_mul_sq_le

end FormalResearch.Special
