module

public import FormalResearch.SignUncertainty.AirySquareBound
public import FormalResearch.SignUncertainty.ShellGapOriginFloor
public import FormalResearch.CohnElkies.AirySeedFloors
public import FormalResearch.Special.AiryCftWeights

/-!
# Generalized Rational–Airy Space and Cardinal Seeds (`lem:al-seeds`)

Source:
* `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, `(e22)`–`(e23)` (`\mathcal{R}_{\mathrm{Ai}}^{\mathrm{gen}}`,
  `\beta_{00}`, `\beta_{11}`, `\beta_\infty`).
* `CFT/sign_uncertainty/paper/ce_shifted_witnesses.tex`, `(eq:ce-beta-plus)` (`\beta_+`) and
  `(eq:ce-beta-minus)`.
* `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex`:
  - Lemma `lem:al-seeds` (`lem_al_seeds`): cardinal seeds `f_n(u) = \Ai(u)^2 / (u - a_n)`,
    `g_n(u) = \Ai(u)^2 / (u - a_n)^2`, and `g_1'(u) = \Ai'(u)^2 / (u - a_1')^2`.

Uniform negative-axis / `L¹` / Laplace seed bounds and `lem:al-far-cardinal-laplace` live in
`FormalResearch.SignUncertainty.AiryFarCardinalLaplace`.

Indexing convention (matching `AirySquareKernel`, `AirySquareBound`, `AirySquareSimple`):
`airyZ n = airyZero (n + 1)` (`n : ℕ`, `0`-indexed so `airyZ 0 = a_1 > airyZ 1 = a_2 > …`).
Thus `airySeedF n` and `airySeedG n` (`n : ℕ`) represent the paper's `f_{n+1}` and `g_{n+1}` at `a_{n+1}`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies

/-! ### Section 1: The Generalized Rational–Airy Class `\mathcal{R}_{\mathrm{Ai}}^{\mathrm{gen}}` -/

/-- Rational–Airy representation `(e22)`–`(e23)` with asymptotic coefficients `(β₀₀, β₁₁)`:
`F ∈ 𝒢` admits real polynomials `(P₀₀, Q₀₀), (P₀₁, Q₀₁), (P₁₁, Q₁₁)` with monic denominators whose
zeros are real and lie in `[-R_*, R_*]` (`R_* ≥ 4`; the paper's "poles inside `[-R_*, R_*]`"), satisfying
`(e22)` for `‖z‖ > R_*` (hence, by the identity theorem, off the removable real poles) and `(e23)` for
`‖w‖ ≥ R_* + 2`. Membership in `𝒢` (`InAiryClass`: entire, real on `ℝ`, integrable, Airy-type growth) is
part of the definition; the paper derives it from `(e22)`-`(e23)` (`u1c_o1_upper.tex`, after `(e23)`). -/
def HasGenRationalAiryCoeffs (F : ℂ → ℂ) (β₀₀ β₁₁ : ℝ) : Prop :=
  InAiryClass F ∧
  ∃ (R_star C : ℝ) (P00 Q00 P01 Q01 P11 Q11 : ℝ[X]),
    4 ≤ R_star ∧ 0 ≤ C ∧
    Q00.Monic ∧ Q01.Monic ∧ Q11.Monic ∧
    (∀ z : ℂ, Polynomial.aeval z Q00 = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star) ∧
    (∀ z : ℂ, Polynomial.aeval z Q01 = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star) ∧
    (∀ z : ℂ, Polynomial.aeval z Q11 = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star) ∧
    (∀ z : ℂ, R_star < ‖z‖ →
      F z = (Polynomial.aeval z P00 / Polynomial.aeval z Q00) * airyAiC z ^ 2 +
            (Polynomial.aeval z P01 / Polynomial.aeval z Q01) * (airyAiC z * deriv airyAiC z) +
            (Polynomial.aeval z P11 / Polynomial.aeval z Q11) * deriv airyAiC z ^ 2) ∧
    (∀ w : ℂ, R_star + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00 - (β₀₀ : ℂ) * w⁻¹‖ ≤
        C * ‖w‖ ^ (-2 : ℝ) ∧
      ‖Polynomial.aeval (-w) P01 / Polynomial.aeval (-w) Q01‖ ≤
        C * ‖w‖ ^ (-2 : ℝ) ∧
      ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11 - (β₁₁ : ℂ) * (w ^ 2)⁻¹‖ ≤
        C * ‖w‖ ^ (-3 : ℝ))

/-- Membership in `\mathcal{R}_{\mathrm{Ai}}^{\mathrm{gen}}` (`u1c_o1_upper.tex`, `(e22)`–`(e23)`). -/
def InGenRationalAiry (F : ℂ → ℂ) : Prop :=
  ∃ β₀₀ β₁₁ : ℝ, HasGenRationalAiryCoeffs F β₀₀ β₁₁

lemma InGenRationalAiry.inAiryClass {F : ℂ → ℂ} (h : InGenRationalAiry F) : InAiryClass F := by
  obtain ⟨_, _, hF, _⟩ := h
  exact hF

private lemma aeval_ofReal_eq_eval (P : ℝ[X]) (x : ℝ) :
    Polynomial.aeval (x : ℂ) P = ((Polynomial.eval x P : ℝ) : ℂ) := by
  exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval x P

private lemma aeval_ne_zero_of_gt {Q : ℝ[X]} {R_star : ℝ}
    (hQ : ∀ z : ℂ, Polynomial.aeval z Q = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star) {z : ℂ} (hz : R_star < ‖z‖) :
    Polynomial.aeval z Q ≠ 0 :=
  fun h0 => not_le_of_gt hz (hQ z h0).2

/-- Real-axis Airy envelopes on `(-∞, 0]`: `|\Ai(u)| ≤ 3 (1 + |u|)^{-1/4}` and
`|\Ai'(u)| ≤ 5 (1 + |u|)^{1/4}`. -/
lemma airyAi_and_deriv_neg_bounds {u : ℝ} (hu : u ≤ 0) :
    |airyAi u| ≤ 3 * (1 + |u|) ^ (-(1 / 4 : ℝ)) ∧
    |airyAi' u| ≤ 5 * (1 + |u|) ^ (1 / 4 : ℝ) := by
  have hre_ge : 0 ≤ ((u : ℂ) ^ (3 / 2 : ℂ)).re := by
    rcases hu.lt_or_eq with hlt | rfl
    · have h := airyEnv_ofReal_neg hlt
      unfold airyEnv at h
      have := Real.exp_injective (h.trans Real.exp_zero.symm)
      linarith only [this]
    · simp
  have hexp_le : Real.exp (-(2 / 3) * ((u : ℂ) ^ (3 / 2 : ℂ)).re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hre_ge])
  have hnu : ‖(u : ℂ)‖ = |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 := airyAiC_envelope (u : ℂ)
  have h2 := airyAiC_deriv_envelope (u : ℂ)
  rw [airyAiC_ofReal, hnu, Complex.norm_real, Real.norm_eq_abs] at h1
  rw [deriv_airyAiC_ofReal, hnu, Complex.norm_real, Real.norm_eq_abs] at h2
  have hp1 : 0 ≤ 3 * (1 + |u|) ^ (-(1 / 4 : ℝ)) := by positivity
  have hp2 : 0 ≤ 5 * (1 + |u|) ^ (1 / 4 : ℝ) := by positivity
  exact ⟨h1.trans (mul_le_of_le_one_right hp1 hexp_le),
    h2.trans (mul_le_of_le_one_right hp2 hexp_le)⟩

/-- Airy–WKB negative-axis asymptotic `(eq:ce-beta-minus)` for any `HasGenRationalAiryCoeffs F β₀₀ β₁₁`:
for `x ≥ R₀`, `π x^{3/2} F(-x) = β₀₀ sin² ϑ(x) + β₁₁ cos² ϑ(x) + O(x^{-1/2})`. -/
theorem HasGenRationalAiryCoeffs.neg_axis_wkb {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    ∃ R₀ K : ℝ, 5 ≤ R₀ ∧ 0 ≤ K ∧ ∀ x : ℝ, R₀ ≤ x →
      |π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re -
        (β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2)| ≤
          K * x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨_, R_star, C, P00, Q00, P01, Q01, P11, Q11, hR4, hC0, _, _, _, hQ00, hQ01, hQ11,
    hrep, hasym⟩ := hF
  set R₀ : ℝ := R_star + 2
  have hR5 : 5 ≤ R₀ := by dsimp [R₀]; linarith only [hR4]
  set K : ℝ := π * ((|β₀₀| + C + 1) + 6 * C + (2 * |β₁₁| + C + 1))
  refine ⟨R₀, K, hR5, by positivity, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith only [hR5, hx]
  have hx0 : 0 < x := by linarith only [hx1]
  have hnx : ‖((-x : ℝ) : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hx0]
  have hnx' : ‖(x : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hgt : R_star < ‖((-x : ℝ) : ℂ)‖ := by rw [hnx]; dsimp [R₀] at hx; linarith only [hx]
  have hge : R_star + 2 ≤ ‖(x : ℂ)‖ := by rw [hnx']; exact hx
  have hFx := hrep ((-x : ℝ) : ℂ) hgt
  obtain ⟨hb00, hb01, hb11⟩ := hasym (x : ℂ) hge
  have hneg_eq : (-(x : ℂ)) = ((-x : ℝ) : ℂ) := by push_cast; ring
  rw [hneg_eq, hnx'] at hb00 hb01 hb11
  set r00 : ℝ := P00.eval (-x) / Q00.eval (-x)
  set r01 : ℝ := P01.eval (-x) / Q01.eval (-x)
  set r11 : ℝ := P11.eval (-x) / Q11.eval (-x)
  have hdiv_real : ∀ P Q : ℝ[X],
      Polynomial.aeval ((-x : ℝ) : ℂ) P / Polynomial.aeval ((-x : ℝ) : ℂ) Q =
        ((P.eval (-x) / Q.eval (-x) : ℝ) : ℂ) := by
    intro P Q
    rw [aeval_ofReal_eq_eval, aeval_ofReal_eq_eval, ← Complex.ofReal_div]
  rw [hdiv_real P00 Q00, hdiv_real P01 Q01, hdiv_real P11 Q11,
    airyAiC_ofReal, deriv_airyAiC_ofReal] at hFx
  have hFre : (F ((-x : ℝ) : ℂ)).re =
      r00 * airyAi (-x) ^ 2 + r01 * (airyAi (-x) * airyAi' (-x)) + r11 * airyAi' (-x) ^ 2 := by
    have hcast : (((r00 * airyAi (-x) ^ 2 + r01 * (airyAi (-x) * airyAi' (-x)) +
        r11 * airyAi' (-x) ^ 2 : ℝ)) : ℂ) = F ((-x : ℝ) : ℂ) := by
      dsimp [r00, r01, r11]
      rw [hFx]
      push_cast
      rfl
    rw [← hcast, Complex.ofReal_re]
  have hr00 : |r00 - β₀₀ * x⁻¹| ≤ C * x ^ (-2 : ℝ) := by
    rw [hdiv_real P00 Q00, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at hb00
    exact hb00
  have hr01 : |r01| ≤ C * x ^ (-2 : ℝ) := by
    rw [hdiv_real P01 Q01, Complex.norm_real, Real.norm_eq_abs] at hb01
    exact hb01
  have hr11 : |r11 - β₁₁ * (x ^ 2)⁻¹| ≤ C * x ^ (-3 : ℝ) := by
    have hsq : ((x : ℂ) ^ 2)⁻¹ = (((x ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hdiv_real P11 Q11, hsq, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at hb11
    exact hb11
  have hAi_env : |airyAi (-x)| ≤ 3 * x ^ (-(1 / 4 : ℝ)) := by
    have hb := (airyAi_and_deriv_neg_bounds (neg_nonpos.mpr hx0.le)).1
    rw [abs_neg, abs_of_pos hx0] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx0 (by linarith only [hx0]) (by norm_num)) (by norm_num))
  have hpi1 : 1 ≤ √π := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  set L1 := -(x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π)
  have hAi' : |airyAi' (-x) - L1| ≤ 2 / (5 * x ^ (5 / 4 : ℝ)) := by
    simpa [L1, sub_neg_eq_add] using airyAi'_neg_asymptotic_theta hx0
  have hL1 : |L1| ≤ x ^ (1 / 4 : ℝ) := by
    dsimp [L1]
    rw [abs_neg, abs_div, abs_mul, abs_of_pos (by positivity), abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    calc x ^ (1 / 4 : ℝ) * |Real.cos (cohnTheta x)| / √π
        ≤ x ^ (1 / 4 : ℝ) * 1 / 1 := div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)) zero_lt_one hpi1
      _ = x ^ (1 / 4 : ℝ) := by ring
  have hrem1 : 2 / (5 * x ^ (5 / 4 : ℝ)) ≤ x ^ (1 / 4 : ℝ) := by
    have h14 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    have h54 : 1 ≤ x ^ (5 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    calc 2 / (5 * x ^ (5 / 4 : ℝ)) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num)
          (by norm_num) (by linarith only [h54])
      _ ≤ 1 := by norm_num
      _ ≤ x ^ (1 / 4 : ℝ) := h14
  have hAi'_env : |airyAi' (-x)| ≤ 2 * x ^ (1 / 4 : ℝ) := by
    have htri := abs_add_le (airyAi' (-x) - L1) L1
    rw [sub_add_cancel] at htri
    linarith only [htri, hAi', hL1, hrem1]
  have hprod_Ai : |airyAi (-x) * airyAi' (-x)| ≤ 6 := by
    rw [abs_mul]
    calc |airyAi (-x)| * |airyAi' (-x)|
        ≤ (3 * x ^ (-(1 / 4 : ℝ))) * (2 * x ^ (1 / 4 : ℝ)) :=
          mul_le_mul hAi_env hAi'_env (abs_nonneg _) (by positivity)
      _ = 6 * (x ^ (-(1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ)) := by ring
      _ = 6 := by rw [← Real.rpow_add hx0]; norm_num
  set S0 : ℝ := Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))
  set C0 : ℝ := x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π
  have hAi_sq : |airyAi (-x) ^ 2 - S0| ≤ x ^ (-2 : ℝ) := by
    set L0 := Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))
    have hAi := airyAi_neg_asymptotic_theta hx0
    have hL0 : |L0| ≤ x ^ (-(1 / 4 : ℝ)) := by
      dsimp [L0]
      rw [abs_div, abs_of_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (by positivity)),
        Real.rpow_neg hx0.le]
      calc |Real.sin (cohnTheta x)| / (√π * x ^ (1 / 4 : ℝ))
          ≤ 1 / (1 * x ^ (1 / 4 : ℝ)) := div_le_div₀ zero_le_one (Real.abs_sin_le_one _)
            (by positivity) (mul_le_mul_of_nonneg_right hpi1 (by positivity))
        _ = (x ^ (1 / 4 : ℝ))⁻¹ := by ring
    have hsum0 : |airyAi (-x) + L0| ≤ 4 * x ^ (-(1 / 4 : ℝ)) := by
      have htri := abs_add_le (airyAi (-x)) L0
      linarith only [htri, hAi_env, hL0]
    have hL0_sq : L0 ^ 2 = S0 := by
      dsimp [L0, S0]
      have hx12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hx12]
    rw [← hL0_sq, show airyAi (-x) ^ 2 - L0 ^ 2 = (airyAi (-x) - L0) * (airyAi (-x) + L0) by ring,
      abs_mul]
    have hcomb0 : (1 / (8 * x ^ (7 / 4 : ℝ))) * (4 * x ^ (-(1 / 4 : ℝ))) = (1 / 2) * x ^ (-2 : ℝ) := by
      have h74 : (x ^ (7 / 4 : ℝ))⁻¹ = x ^ (-(7 / 4 : ℝ)) := (Real.rpow_neg hx0.le _).symm
      calc (1 / (8 * x ^ (7 / 4 : ℝ))) * (4 * x ^ (-(1 / 4 : ℝ)))
          = (1 / 2) * ((x ^ (7 / 4 : ℝ))⁻¹ * x ^ (-(1 / 4 : ℝ))) := by ring
        _ = (1 / 2) * (x ^ (-(7 / 4 : ℝ)) * x ^ (-(1 / 4 : ℝ))) := by rw [h74]
        _ = (1 / 2) * x ^ (-2 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
    calc |airyAi (-x) - L0| * |airyAi (-x) + L0|
        ≤ (1 / (8 * x ^ (7 / 4 : ℝ))) * (4 * x ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul hAi hsum0 (abs_nonneg _) (by positivity)
      _ = (1 / 2) * x ^ (-2 : ℝ) := hcomb0
      _ ≤ x ^ (-2 : ℝ) := by
          have : 0 ≤ x ^ (-2 : ℝ) := by positivity
          linarith only [this]
  have hAi'_sq : |airyAi' (-x) ^ 2 - C0| ≤ 2 * x ^ (-1 : ℝ) := by
    have hsum1 : |airyAi' (-x) + L1| ≤ 3 * x ^ (1 / 4 : ℝ) := by
      have htri := abs_add_le (airyAi' (-x)) L1
      linarith only [htri, hAi'_env, hL1]
    have hL1_sq : L1 ^ 2 = C0 := by
      dsimp [L1, C0]
      have hx12 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      rw [neg_sq, div_pow, mul_pow, hx12, Real.sq_sqrt Real.pi_pos.le]
    rw [← hL1_sq, show airyAi' (-x) ^ 2 - L1 ^ 2 = (airyAi' (-x) - L1) * (airyAi' (-x) + L1) by ring,
      abs_mul]
    have hcomb1 : (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ)) = (6 / 5) * x ^ (-1 : ℝ) := by
      have h54 : (x ^ (5 / 4 : ℝ))⁻¹ = x ^ (-(5 / 4 : ℝ)) := (Real.rpow_neg hx0.le _).symm
      calc (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ))
          = (6 / 5) * ((x ^ (5 / 4 : ℝ))⁻¹ * x ^ (1 / 4 : ℝ)) := by ring
        _ = (6 / 5) * (x ^ (-(5 / 4 : ℝ)) * x ^ (1 / 4 : ℝ)) := by rw [h54]
        _ = (6 / 5) * x ^ (-1 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
    calc |airyAi' (-x) - L1| * |airyAi' (-x) + L1|
        ≤ (2 / (5 * x ^ (5 / 4 : ℝ))) * (3 * x ^ (1 / 4 : ℝ)) :=
          mul_le_mul hAi' hsum1 (abs_nonneg _) (by positivity)
      _ = (6 / 5) * x ^ (-1 : ℝ) := hcomb1
      _ ≤ 2 * x ^ (-1 : ℝ) := by
          have : 0 ≤ x ^ (-1 : ℝ) := by positivity
          linarith only [this]
  have hAi_sq_le : airyAi (-x) ^ 2 ≤ x ^ (-(1 / 2 : ℝ)) := by
    have h1 := (abs_le.mp hAi_sq).2
    have hsin : S0 ≤ (1 / 3) * x ^ (-(1 / 2 : ℝ)) := by
      dsimp [S0]
      rw [Real.rpow_neg hx0.le]
      calc Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))
          ≤ 1 / (3 * x ^ (1 / 2 : ℝ)) := div_le_div₀ zero_le_one
            ((sq_le_one_iff_abs_le_one _).mpr (Real.abs_sin_le_one _)) (by positivity)
            (mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity))
        _ = (1 / 3) * (x ^ (1 / 2 : ℝ))⁻¹ := by ring
    have h2 : x ^ (-2 : ℝ) ≤ (2 / 3) * x ^ (-(1 / 2 : ℝ)) := by
      calc x ^ (-2 : ℝ) = x ^ (-(3 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) := by
            rw [← Real.rpow_add hx0]; norm_num
        _ ≤ (2 / 3) * x ^ (-(1 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            calc x ^ (-(3 / 2 : ℝ)) ≤ 5 ^ (-(3 / 2 : ℝ)) :=
                  Real.rpow_le_rpow_of_nonpos (by norm_num) (hR5.trans hx) (by norm_num)
              _ ≤ 5 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ ≤ 2 / 3 := by norm_num
    linarith only [h1, hsin, h2]
  have hAi'_sq_le : airyAi' (-x) ^ 2 ≤ x ^ (1 / 2 : ℝ) := by
    have h1 := (abs_le.mp hAi'_sq).2
    have hcos : C0 ≤ (1 / 3) * x ^ (1 / 2 : ℝ) := by
      dsimp [C0]
      calc x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π
          ≤ x ^ (1 / 2 : ℝ) * 1 / 3 := div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left ((sq_le_one_iff_abs_le_one _).mpr (Real.abs_cos_le_one _))
              (by positivity)) (by norm_num) Real.pi_gt_three.le
        _ = (1 / 3) * x ^ (1 / 2 : ℝ) := by ring
    have h2 : 2 * x ^ (-1 : ℝ) ≤ (2 / 3) * x ^ (1 / 2 : ℝ) := by
      calc 2 * x ^ (-1 : ℝ) = 2 * x ^ (-(3 / 2 : ℝ)) * x ^ (1 / 2 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hx0]; norm_num
        _ ≤ (2 / 3) * x ^ (1 / 2 : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : x ^ (-(3 / 2 : ℝ)) ≤ 1 / 5 := by
              calc x ^ (-(3 / 2 : ℝ)) ≤ 5 ^ (-(3 / 2 : ℝ)) :=
                    Real.rpow_le_rpow_of_nonpos (by norm_num) (hR5.trans hx) (by norm_num)
                _ ≤ 5 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 1 / 5 := by norm_num
            linarith only [this]
    linarith only [h1, hcos, h2]
  rw [hFre]
  have hx32_1 : x ^ (3 / 2 : ℝ) * x⁻¹ * (x ^ (1 / 2 : ℝ))⁻¹ = 1 := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have hx32_2 : x ^ (3 / 2 : ℝ) * (x ^ 2)⁻¹ * x ^ (1 / 2 : ℝ) = 1 := by
    have : (x ^ 2)⁻¹ = x ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hx0.le, show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
    rw [this, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have hpi_ne : π ≠ 0 := Real.pi_ne_zero
  set inv1 : ℝ := x⁻¹
  set inv2 : ℝ := (x ^ 2)⁻¹
  have ht1 : π * x ^ (3 / 2 : ℝ) * (β₀₀ * inv1 * S0) = β₀₀ * Real.sin (cohnTheta x) ^ 2 := by
    dsimp [inv1, S0]
    calc π * x ^ (3 / 2 : ℝ) * (β₀₀ * x⁻¹ * (Real.sin (cohnTheta x) ^ 2 / (π * x ^ (1 / 2 : ℝ))))
        = β₀₀ * Real.sin (cohnTheta x) ^ 2 * (π / π) *
            (x ^ (3 / 2 : ℝ) * x⁻¹ * (x ^ (1 / 2 : ℝ))⁻¹) := by ring
      _ = β₀₀ * Real.sin (cohnTheta x) ^ 2 := by rw [div_self hpi_ne, hx32_1]; ring
  have ht2 : π * x ^ (3 / 2 : ℝ) * (β₁₁ * inv2 * C0) = β₁₁ * Real.cos (cohnTheta x) ^ 2 := by
    dsimp [inv2, C0]
    calc π * x ^ (3 / 2 : ℝ) *
            (β₁₁ * (x ^ 2)⁻¹ * (x ^ (1 / 2 : ℝ) * Real.cos (cohnTheta x) ^ 2 / π))
        = β₁₁ * Real.cos (cohnTheta x) ^ 2 * (π / π) *
            (x ^ (3 / 2 : ℝ) * (x ^ 2)⁻¹ * x ^ (1 / 2 : ℝ)) := by ring
      _ = β₁₁ * Real.cos (cohnTheta x) ^ 2 := by rw [div_self hpi_ne, hx32_2]; ring
  have hsplit : π * x ^ (3 / 2 : ℝ) *
      (r00 * airyAi (-x) ^ 2 + r01 * (airyAi (-x) * airyAi' (-x)) + r11 * airyAi' (-x) ^ 2) -
      (β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2) =
      π * x ^ (3 / 2 : ℝ) *
        ((r00 - β₀₀ * inv1) * airyAi (-x) ^ 2 +
         β₀₀ * inv1 * (airyAi (-x) ^ 2 - S0) +
         r01 * (airyAi (-x) * airyAi' (-x)) +
         (r11 - β₁₁ * inv2) * airyAi' (-x) ^ 2 +
         β₁₁ * inv2 * (airyAi' (-x) ^ 2 - C0)) := by
    calc π * x ^ (3 / 2 : ℝ) *
          (r00 * airyAi (-x) ^ 2 + r01 * (airyAi (-x) * airyAi' (-x)) + r11 * airyAi' (-x) ^ 2) -
          (β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2)
        = π * x ^ (3 / 2 : ℝ) *
            (r00 * airyAi (-x) ^ 2 + r01 * (airyAi (-x) * airyAi' (-x)) + r11 * airyAi' (-x) ^ 2) -
            (π * x ^ (3 / 2 : ℝ) * (β₀₀ * inv1 * S0) +
              π * x ^ (3 / 2 : ℝ) * (β₁₁ * inv2 * C0)) := by rw [← ht1, ← ht2]
      _ = _ := by ring
  rw [hsplit, abs_mul, abs_of_pos (mul_pos Real.pi_pos (by positivity))]
  have he1 : |(r00 - β₀₀ * inv1) * airyAi (-x) ^ 2| ≤ C * x ^ (-(5 / 2 : ℝ)) := by
    rw [abs_mul, (abs_of_nonneg (sq_nonneg _) : |airyAi (-x) ^ 2| = airyAi (-x) ^ 2)]
    calc |r00 - β₀₀ * inv1| * airyAi (-x) ^ 2
        ≤ (C * x ^ (-2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul hr00 hAi_sq_le (sq_nonneg _) (by positivity)
      _ = C * (x ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ))) := by ring
      _ = C * x ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hx0]; norm_num
  have he2 : |β₀₀ * inv1 * (airyAi (-x) ^ 2 - S0)| ≤ |β₀₀| * x ^ (-3 : ℝ) := by
    have hinv1_pos : 0 < inv1 := inv_pos.mpr hx0
    rw [abs_mul, abs_mul, (abs_of_pos hinv1_pos : |inv1| = inv1)]
    calc |β₀₀| * inv1 * |airyAi (-x) ^ 2 - S0|
        ≤ |β₀₀| * inv1 * x ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left hAi_sq (by positivity)
      _ = |β₀₀| * (x ^ (-1 : ℝ) * x ^ (-2 : ℝ)) := by dsimp [inv1]; rw [Real.rpow_neg_one]; ring
      _ = |β₀₀| * x ^ (-3 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  have he3 : |r01 * (airyAi (-x) * airyAi' (-x))| ≤ 6 * C * x ^ (-2 : ℝ) := by
    rw [abs_mul]
    calc |r01| * |airyAi (-x) * airyAi' (-x)|
        ≤ (C * x ^ (-2 : ℝ)) * 6 := mul_le_mul hr01 hprod_Ai (abs_nonneg _) (by positivity)
      _ = 6 * C * x ^ (-2 : ℝ) := by ring
  have he4 : |(r11 - β₁₁ * inv2) * airyAi' (-x) ^ 2| ≤ C * x ^ (-(5 / 2 : ℝ)) := by
    rw [abs_mul, (abs_of_nonneg (sq_nonneg _) : |airyAi' (-x) ^ 2| = airyAi' (-x) ^ 2)]
    calc |r11 - β₁₁ * inv2| * airyAi' (-x) ^ 2
        ≤ (C * x ^ (-3 : ℝ)) * x ^ (1 / 2 : ℝ) :=
          mul_le_mul hr11 hAi'_sq_le (sq_nonneg _) (by positivity)
      _ = C * (x ^ (-3 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
      _ = C * x ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hx0]; norm_num
  have he5 : |β₁₁ * inv2 * (airyAi' (-x) ^ 2 - C0)| ≤ 2 * |β₁₁| * x ^ (-3 : ℝ) := by
    have hinv2_pos : 0 < inv2 := by dsimp [inv2]; positivity
    rw [abs_mul, abs_mul, (abs_of_pos hinv2_pos : |inv2| = inv2)]
    have hsq2 : inv2 = x ^ (-2 : ℝ) := by
      dsimp [inv2]; rw [Real.rpow_neg hx0.le, show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
    calc |β₁₁| * inv2 * |airyAi' (-x) ^ 2 - C0|
        ≤ |β₁₁| * x ^ (-2 : ℝ) * (2 * x ^ (-1 : ℝ)) := by
          rw [hsq2]; exact mul_le_mul_of_nonneg_left hAi'_sq (by positivity)
      _ = 2 * |β₁₁| * (x ^ (-2 : ℝ) * x ^ (-1 : ℝ)) := by ring
      _ = 2 * |β₁₁| * x ^ (-3 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  have hpow25 : x ^ (-(5 / 2 : ℝ)) ≤ x ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hpow3 : x ^ (-3 : ℝ) ≤ x ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hsum_in : |(r00 - β₀₀ * inv1) * airyAi (-x) ^ 2 +
      β₀₀ * inv1 * (airyAi (-x) ^ 2 - S0) +
      r01 * (airyAi (-x) * airyAi' (-x)) +
      (r11 - β₁₁ * inv2) * airyAi' (-x) ^ 2 +
      β₁₁ * inv2 * (airyAi' (-x) ^ 2 - C0)| ≤
      ((|β₀₀| + C + 1) + 6 * C + (2 * |β₁₁| + C + 1)) * x ^ (-2 : ℝ) := by
    have ht_a := abs_add_le
      ((r00 - β₀₀ * inv1) * airyAi (-x) ^ 2 +
        β₀₀ * inv1 * (airyAi (-x) ^ 2 - S0) +
        r01 * (airyAi (-x) * airyAi' (-x)) +
        (r11 - β₁₁ * inv2) * airyAi' (-x) ^ 2)
      (β₁₁ * inv2 * (airyAi' (-x) ^ 2 - C0))
    have ht_b := abs_add_le
      ((r00 - β₀₀ * inv1) * airyAi (-x) ^ 2 +
        β₀₀ * inv1 * (airyAi (-x) ^ 2 - S0) +
        r01 * (airyAi (-x) * airyAi' (-x)))
      ((r11 - β₁₁ * inv2) * airyAi' (-x) ^ 2)
    have ht_c := abs_add_le
      ((r00 - β₀₀ * inv1) * airyAi (-x) ^ 2 +
        β₀₀ * inv1 * (airyAi (-x) ^ 2 - S0))
      (r01 * (airyAi (-x) * airyAi' (-x)))
    have ht_d := abs_add_le
      ((r00 - β₀₀ * inv1) * airyAi (-x) ^ 2)
      (β₀₀ * inv1 * (airyAi (-x) ^ 2 - S0))
    have hx2_nn : 0 ≤ x ^ (-2 : ℝ) := by positivity
    nlinarith only [ht_a, ht_b, ht_c, ht_d, he1, he2, he3, he4, he5, hpow25, hpow3, hC0,
      abs_nonneg β₀₀, abs_nonneg β₁₁, hx2_nn]
  calc π * x ^ (3 / 2 : ℝ) * _
      ≤ π * x ^ (3 / 2 : ℝ) *
          (((|β₀₀| + C + 1) + 6 * C + (2 * |β₁₁| + C + 1)) * x ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_in (by positivity)
    _ = K * (x ^ (3 / 2 : ℝ) * x ^ (-2 : ℝ)) := by dsimp [K]; ring
    _ = K * x ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hx0]; norm_num

/-- Uniqueness of `(β₀₀, β₁₁)` in `HasGenRationalAiryCoeffs F β₀₀ β₁₁`. -/
theorem HasGenRationalAiryCoeffs.unique {F : ℂ → ℂ} {β₀₀ β₁₁ β₀₀' β₁₁' : ℝ}
    (h1 : HasGenRationalAiryCoeffs F β₀₀ β₁₁) (h2 : HasGenRationalAiryCoeffs F β₀₀' β₁₁') :
    β₀₀ = β₀₀' ∧ β₁₁ = β₁₁' := by
  obtain ⟨R1, K1, _, hK1, hb1⟩ := h1.neg_axis_wkb
  obtain ⟨R2, K2, _, hK2, hb2⟩ := h2.neg_axis_wkb
  let xSeq : ℕ → ℝ := fun k => ((3 / 2 : ℝ) * ((k : ℝ) * π + π / 4)) ^ (2 / 3 : ℝ)
  have hx_pos : ∀ k : ℕ, 0 < (3 / 2 : ℝ) * ((k : ℝ) * π + π / 4) := fun k => by
    have := Real.pi_pos; positivity
  have hx_theta : ∀ k : ℕ, cohnTheta (xSeq k) = (k : ℝ) * π + π / 2 := by
    intro k
    unfold cohnTheta xSeq
    rw [← Real.rpow_mul (hx_pos k).le]
    norm_num
    ring
  have hx_atTop : Tendsto xSeq atTop atTop := by
    refine (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp ?_
    refine Tendsto.const_mul_atTop (by norm_num) ?_
    exact Tendsto.atTop_add (Tendsto.atTop_mul_const Real.pi_pos tendsto_natCast_atTop_atTop)
      tendsto_const_nhds
  have hx_inv_zero : Tendsto (fun k : ℕ => (xSeq k) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx_atTop
  have hlim_00 : ∀ β_a β_b R K, 0 ≤ K →
      (∀ x : ℝ, R ≤ x →
        |π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re -
          (β_a * Real.sin (cohnTheta x) ^ 2 + β_b * Real.cos (cohnTheta x) ^ 2)| ≤
          K * x ^ (-(1 / 2 : ℝ))) →
      Tendsto (fun k : ℕ => π * (xSeq k) ^ (3 / 2 : ℝ) * (F ((-xSeq k : ℝ) : ℂ)).re)
        atTop (𝓝 β_a) := by
    intro β_a β_b R K _ hbd
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hx_inv_zero.const_mul K)
    filter_upwards [hx_atTop.eventually (eventually_ge_atTop R)] with k hk
    have h := hbd (xSeq k) hk
    rw [hx_theta k, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
      Real.cos_nat_mul_pi, Real.sin_nat_mul_pi] at h
    have h1_sq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [h1_sq] at h
    simpa [Real.norm_eq_abs] using h
  have hβ00 : β₀₀ = β₀₀' :=
    tendsto_nhds_unique (hlim_00 β₀₀ β₁₁ R1 K1 hK1 hb1) (hlim_00 β₀₀' β₁₁' R2 K2 hK2 hb2)
  let ySeq : ℕ → ℝ := fun k => ((3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) * π - π / 4)) ^ (2 / 3 : ℝ)
  have hy_pos : ∀ k : ℕ, 0 < (3 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ) * π - π / 4) := fun k => by
    have hpi := Real.pi_gt_three
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast
    nlinarith only [hpi, hk0]
  have hy_theta : ∀ k : ℕ, cohnTheta (ySeq k) = ((k + 1 : ℕ) : ℝ) * π := by
    intro k
    unfold cohnTheta ySeq
    rw [← Real.rpow_mul (hy_pos k).le]
    norm_num
    ring
  have hy_atTop : Tendsto ySeq atTop atTop := by
    refine (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp ?_
    refine Tendsto.const_mul_atTop (by norm_num) ?_
    refine Tendsto.atTop_add ?_ tendsto_const_nhds
    exact Tendsto.atTop_mul_const Real.pi_pos
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hy_inv_zero : Tendsto (fun k : ℕ => (ySeq k) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hy_atTop
  have hlim_11 : ∀ β_a β_b R K, 0 ≤ K →
      (∀ x : ℝ, R ≤ x →
        |π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re -
          (β_a * Real.sin (cohnTheta x) ^ 2 + β_b * Real.cos (cohnTheta x) ^ 2)| ≤
          K * x ^ (-(1 / 2 : ℝ))) →
      Tendsto (fun k : ℕ => π * (ySeq k) ^ (3 / 2 : ℝ) * (F ((-ySeq k : ℝ) : ℂ)).re)
        atTop (𝓝 β_b) := by
    intro β_a β_b R K _ hbd
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hy_inv_zero.const_mul K)
    filter_upwards [hy_atTop.eventually (eventually_ge_atTop R)] with k hk
    have h := hbd (ySeq k) hk
    rw [hy_theta k, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at h
    have h1_sq : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [h1_sq] at h
    simpa [Real.norm_eq_abs] using h
  exact ⟨hβ00,
    tendsto_nhds_unique (hlim_11 β₀₀ β₁₁ R1 K1 hK1 hb1) (hlim_11 β₀₀' β₁₁' R2 K2 hK2 hb2)⟩

/-- Leading negative-axis `\Ai^2` coefficient `\beta_{00}(F)` (`(e23)`). -/
noncomputable def airyBeta00 (F : ℂ → ℂ) : ℝ := by
  classical
  exact if h : InGenRationalAiry F then h.choose else 0

/-- Leading negative-axis `\Ai'^2` coefficient `\beta_{11}(F)` (`(e23)`). -/
noncomputable def airyBeta11 (F : ℂ → ℂ) : ℝ := by
  classical
  exact if h : InGenRationalAiry F then h.choose_spec.choose else 0

/-- Negative-axis total tail coefficient `\beta_\infty(F) = \beta_{00}(F) + \beta_{11}(F)` (`(e23)`). -/
noncomputable def airyBetaInf (F : ℂ → ℂ) : ℝ :=
  airyBeta00 F + airyBeta11 F

/-- Positive-axis leading coefficient `\beta_+(F) = -\beta_{00}(F) + \beta_{11}(F)` (`eq:ce-beta-plus`). -/
noncomputable def airyBetaPlus (F : ℂ → ℂ) : ℝ :=
  -airyBeta00 F + airyBeta11 F

theorem HasGenRationalAiryCoeffs.beta_eq {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (h : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    airyBeta00 F = β₀₀ ∧ airyBeta11 F = β₁₁ ∧
    airyBetaInf F = β₀₀ + β₁₁ ∧ airyBetaPlus F = -β₀₀ + β₁₁ := by
  have hex : InGenRationalAiry F := ⟨β₀₀, β₁₁, h⟩
  have hspec : HasGenRationalAiryCoeffs F hex.choose hex.choose_spec.choose :=
    hex.choose_spec.choose_spec
  obtain ⟨e0, e1⟩ := hspec.unique h
  have hb0 : airyBeta00 F = β₀₀ := by unfold airyBeta00; simp [hex, e0]
  have hb1 : airyBeta11 F = β₁₁ := by unfold airyBeta11; simp [hex, e1]
  exact ⟨hb0, hb1, by unfold airyBetaInf; rw [hb0, hb1], by unfold airyBetaPlus; rw [hb0, hb1]⟩

theorem InGenRationalAiry.hasCoeffs {F : ℂ → ℂ} (h : InGenRationalAiry F) :
    HasGenRationalAiryCoeffs F (airyBeta00 F) (airyBeta11 F) := by
  obtain ⟨β₀₀, β₁₁, hF⟩ := h
  obtain ⟨e0, e1, _, _⟩ := hF.beta_eq
  rwa [e0, e1]

/-! ### Vector-space closure of `InGenRationalAiry` and linearity of `\beta_{00}, \beta_{11}, \beta_\infty, \beta_+` -/

theorem HasGenRationalAiryCoeffs.zero : HasGenRationalAiryCoeffs (fun _ => 0) 0 0 := by
  refine ⟨⟨differentiable_const 0, integrable_zero _ _ _, ⟨0, 0, le_rfl, fun _ => by simp⟩,
    fun _ => by simp⟩, 4, 0, 0, 1, 0, 1, 0, 1, le_rfl, le_rfl,
    Polynomial.monic_one, Polynomial.monic_one, Polynomial.monic_one,
    fun z h => by simp at h, fun z h => by simp at h, fun z h => by simp at h,
    fun z _ => by simp, fun w _ => by simp⟩

theorem HasGenRationalAiryCoeffs.smul {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (h : HasGenRationalAiryCoeffs F β₀₀ β₁₁) (c : ℝ) :
    HasGenRationalAiryCoeffs (fun z => (c : ℂ) * F z) (c * β₀₀) (c * β₁₁) := by
  obtain ⟨hF, R_star, C, P00, Q00, P01, Q01, P11, Q11, hR4, hC0, hm00, hm01, hm11,
    hQ00, hQ01, hQ11, hrep, hasym⟩ := h
  refine ⟨hF.smul c, R_star, |c| * C, Polynomial.C c * P00, Q00, Polynomial.C c * P01, Q01,
    Polynomial.C c * P11, Q11, hR4, by positivity, hm00, hm01, hm11, hQ00, hQ01, hQ11, ?_, ?_⟩
  · intro z hz
    dsimp only
    rw [hrep z hz]
    simp only [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Complex.real_smul,
      mul_one]
    ring
  · intro w hw
    obtain ⟨b00, b01, b11⟩ := hasym w hw
    simp only [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Complex.real_smul,
      mul_one, Complex.ofReal_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [show (c : ℂ) * Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00 -
          (c : ℂ) * (β₀₀ : ℂ) * w⁻¹ =
          (c : ℂ) * (Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00 - (β₀₀ : ℂ) * w⁻¹) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left b00 (abs_nonneg c)
    · rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left b01 (abs_nonneg c)
    · rw [show (c : ℂ) * Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11 -
          (c : ℂ) * (β₁₁ : ℂ) * (w ^ 2)⁻¹ =
          (c : ℂ) * (Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11 -
            (β₁₁ : ℂ) * (w ^ 2)⁻¹) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left b11 (abs_nonneg c)

theorem HasGenRationalAiryCoeffs.neg {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (h : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    HasGenRationalAiryCoeffs (fun z => -F z) (-β₀₀) (-β₁₁) := by
  have hs := h.smul (-1)
  simpa using hs

theorem HasGenRationalAiryCoeffs.add {F G : ℂ → ℂ} {α₀₀ α₁₁ β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F α₀₀ α₁₁) (hG : HasGenRationalAiryCoeffs G β₀₀ β₁₁) :
    HasGenRationalAiryCoeffs (fun z => F z + G z) (α₀₀ + β₀₀) (α₁₁ + β₁₁) := by
  obtain ⟨hcF, R1, C1, P00a, Q00a, P01a, Q01a, P11a, Q11a, hR1, hC1,
    hm00a, hm01a, hm11a, hQ00a, hQ01a, hQ11a, hrepF, hasymF⟩ := hF
  obtain ⟨hcG, R2, C2, P00b, Q00b, P01b, Q01b, P11b, Q11b, hR2, hC2,
    hm00b, hm01b, hm11b, hQ00b, hQ01b, hQ11b, hrepG, hasymG⟩ := hG
  set R_star : ℝ := max R1 R2
  refine ⟨hcF.add hcG, R_star, C1 + C2,
    P00a * Q00b + Q00a * P00b, Q00a * Q00b,
    P01a * Q01b + Q01a * P01b, Q01a * Q01b,
    P11a * Q11b + Q11a * P11b, Q11a * Q11b,
    hR1.trans (le_max_left _ _), add_nonneg hC1 hC2,
    hm00a.mul hm00b, hm01a.mul hm01b, hm11a.mul hm11b,
    fun z h0 => (mul_eq_zero.mp (by simpa [map_mul] using h0)).elim
      (fun h => ⟨(hQ00a z h).1, (hQ00a z h).2.trans (le_max_left _ _)⟩)
      (fun h => ⟨(hQ00b z h).1, (hQ00b z h).2.trans (le_max_right _ _)⟩),
    fun z h0 => (mul_eq_zero.mp (by simpa [map_mul] using h0)).elim
      (fun h => ⟨(hQ01a z h).1, (hQ01a z h).2.trans (le_max_left _ _)⟩)
      (fun h => ⟨(hQ01b z h).1, (hQ01b z h).2.trans (le_max_right _ _)⟩),
    fun z h0 => (mul_eq_zero.mp (by simpa [map_mul] using h0)).elim
      (fun h => ⟨(hQ11a z h).1, (hQ11a z h).2.trans (le_max_left _ _)⟩)
      (fun h => ⟨(hQ11b z h).1, (hQ11b z h).2.trans (le_max_right _ _)⟩),
    ?_, ?_⟩
  · intro z hz
    dsimp only
    have hz1 : R1 < ‖z‖ := (le_max_left R1 R2).trans_lt hz
    have hz2 : R2 < ‖z‖ := (le_max_right R1 R2).trans_lt hz
    have h00a := aeval_ne_zero_of_gt hQ00a hz1
    have h00b := aeval_ne_zero_of_gt hQ00b hz2
    have h01a := aeval_ne_zero_of_gt hQ01a hz1
    have h01b := aeval_ne_zero_of_gt hQ01b hz2
    have h11a := aeval_ne_zero_of_gt hQ11a hz1
    have h11b := aeval_ne_zero_of_gt hQ11b hz2
    rw [hrepF z hz1, hrepG z hz2]
    simp only [map_add, map_mul]
    rw [← div_add_div _ _ h00a h00b, ← div_add_div _ _ h01a h01b, ← div_add_div _ _ h11a h11b]
    ring
  · intro w hw
    have hw1 : R1 + 2 ≤ ‖w‖ := (add_le_add_left (le_max_left R1 R2) 2).trans hw
    have hw2 : R2 + 2 ≤ ‖w‖ := (add_le_add_left (le_max_right R1 R2) 2).trans hw
    have hnw1 : R1 < ‖-w‖ := by rw [norm_neg]; linarith only [hw1]
    have hnw2 : R2 < ‖-w‖ := by rw [norm_neg]; linarith only [hw2]
    obtain ⟨f00, f01, f11⟩ := hasymF w hw1
    obtain ⟨g00, g01, g11⟩ := hasymG w hw2
    simp only [map_add, map_mul, Complex.ofReal_add]
    rw [← div_add_div _ _ (aeval_ne_zero_of_gt hQ00a hnw1) (aeval_ne_zero_of_gt hQ00b hnw2),
        ← div_add_div _ _ (aeval_ne_zero_of_gt hQ01a hnw1) (aeval_ne_zero_of_gt hQ01b hnw2),
        ← div_add_div _ _ (aeval_ne_zero_of_gt hQ11a hnw1) (aeval_ne_zero_of_gt hQ11b hnw2)]
    refine ⟨?_, ?_, ?_⟩
    · rw [show Polynomial.aeval (-w) P00a / Polynomial.aeval (-w) Q00a +
            Polynomial.aeval (-w) P00b / Polynomial.aeval (-w) Q00b -
            ((α₀₀ : ℂ) + (β₀₀ : ℂ)) * w⁻¹ =
            (Polynomial.aeval (-w) P00a / Polynomial.aeval (-w) Q00a - (α₀₀ : ℂ) * w⁻¹) +
            (Polynomial.aeval (-w) P00b / Polynomial.aeval (-w) Q00b - (β₀₀ : ℂ) * w⁻¹) by ring]
      exact (norm_add_le _ _).trans (by linarith only [f00, g00])
    · exact (norm_add_le _ _).trans (by linarith only [f01, g01])
    · rw [show Polynomial.aeval (-w) P11a / Polynomial.aeval (-w) Q11a +
            Polynomial.aeval (-w) P11b / Polynomial.aeval (-w) Q11b -
            ((α₁₁ : ℂ) + (β₁₁ : ℂ)) * (w ^ 2)⁻¹ =
            (Polynomial.aeval (-w) P11a / Polynomial.aeval (-w) Q11a - (α₁₁ : ℂ) * (w ^ 2)⁻¹) +
            (Polynomial.aeval (-w) P11b / Polynomial.aeval (-w) Q11b - (β₁₁ : ℂ) * (w ^ 2)⁻¹) by ring]
      exact (norm_add_le _ _).trans (by linarith only [f11, g11])

theorem HasGenRationalAiryCoeffs.sub {F G : ℂ → ℂ} {α₀₀ α₁₁ β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F α₀₀ α₁₁) (hG : HasGenRationalAiryCoeffs G β₀₀ β₁₁) :
    HasGenRationalAiryCoeffs (fun z => F z - G z) (α₀₀ - β₀₀) (α₁₁ - β₁₁) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem InGenRationalAiry.zero : InGenRationalAiry (fun _ => 0) :=
  ⟨0, 0, HasGenRationalAiryCoeffs.zero⟩

theorem InGenRationalAiry.smul {F : ℂ → ℂ} (h : InGenRationalAiry F) (c : ℝ) :
    InGenRationalAiry (fun z => (c : ℂ) * F z) :=
  ⟨c * airyBeta00 F, c * airyBeta11 F, h.hasCoeffs.smul c⟩

theorem InGenRationalAiry.neg {F : ℂ → ℂ} (h : InGenRationalAiry F) :
    InGenRationalAiry (fun z => -F z) :=
  ⟨-airyBeta00 F, -airyBeta11 F, h.hasCoeffs.neg⟩

theorem InGenRationalAiry.add {F G : ℂ → ℂ} (hF : InGenRationalAiry F) (hG : InGenRationalAiry G) :
    InGenRationalAiry (fun z => F z + G z) :=
  ⟨airyBeta00 F + airyBeta00 G, airyBeta11 F + airyBeta11 G, hF.hasCoeffs.add hG.hasCoeffs⟩

theorem InGenRationalAiry.sub {F G : ℂ → ℂ} (hF : InGenRationalAiry F) (hG : InGenRationalAiry G) :
    InGenRationalAiry (fun z => F z - G z) :=
  ⟨airyBeta00 F - airyBeta00 G, airyBeta11 F - airyBeta11 G, hF.hasCoeffs.sub hG.hasCoeffs⟩

theorem HasGenRationalAiryCoeffs.finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (b00 b11 : ι → ℝ) (h : ∀ i ∈ s, HasGenRationalAiryCoeffs (F i) (b00 i) (b11 i)) :
    HasGenRationalAiryCoeffs (fun z => ∑ i ∈ s, F i z) (∑ i ∈ s, b00 i) (∑ i ∈ s, b11 i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasGenRationalAiryCoeffs.zero
  | insert j s hj ih =>
    have hj_mem := h j (Finset.mem_insert_self j s)
    have hs_mem := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hsum := hj_mem.add hs_mem
    simpa [Finset.sum_insert hj] using hsum

/-! ### Section 2: Cardinal Seeds `f_n`, `g_n`, `g_1'` and Lemma `lem:al-seeds` -/

/-- Simple-pole Airy cardinal seed `f_{n+1}(z) = \Ai(z)^2 / (z - a_{n+1}) = \Ai(z) k_n(z)` (`n : ℕ`). -/
noncomputable def airySeedF (n : ℕ) (z : ℂ) : ℂ :=
  airyAiC z * airyCardinal n z

/-- Double-pole Airy cardinal seed `g_{n+1}(z) = \Ai(z)^2 / (z - a_{n+1})^2 = k_n(z)^2` (`n : ℕ`). -/
noncomputable def airySeedG (n : ℕ) (z : ℂ) : ℂ :=
  airyCardinal n z ^ 2

/-- Derivative Airy seed `g_1'(z) = \Ai'(z)^2 / (z - a_1')^2`. -/
noncomputable def airySeedG1Deriv (z : ℂ) : ℂ :=
  airyDerivCardinalC z ^ 2

lemma airySeedF_eq_trialSquareWitness (n : ℕ) (z : ℂ) :
    airySeedF n z =
      airyTrialSquareWitness (n + 1) (Pi.single ⟨n, Nat.lt_succ_self n⟩ 1) (airyZ n) z := by
  unfold airySeedF airyTrialSquareWitness airySectionPoly
  rw [Finset.sum_eq_single ⟨n, Nat.lt_succ_self n⟩]
  · simp only [Pi.single_eq_same, Complex.ofReal_one, one_mul, sq]
    rw [← mul_assoc, mul_airyCardinal]
  · intro m _ hmn
    simp [Pi.single_eq_of_ne hmn]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma airySeedF_ofReal (n : ℕ) (u : ℝ) :
    airySeedF n (u : ℂ) = ((airyAi u * airyCardinalR n u : ℝ) : ℂ) := by
  unfold airySeedF
  rw [airyAiC_ofReal, ← ofReal_airyCardinalR, Complex.ofReal_mul]

lemma airySeedF_re (n : ℕ) (u : ℝ) :
    (airySeedF n (u : ℂ)).re = airyAi u * airyCardinalR n u := by
  rw [airySeedF_ofReal, Complex.ofReal_re]

lemma airySeedF_re_of_ne (n : ℕ) {u : ℝ} (hu : u ≠ airyZ n) :
    (airySeedF n (u : ℂ)).re = airyAi u ^ 2 / (u - airyZ n) := by
  rw [airySeedF_re, airyCardinalR_of_ne n hu, sq, mul_div_assoc]

lemma airySeedG_ofReal (n : ℕ) (u : ℝ) :
    airySeedG n (u : ℂ) = ((airyCardinalR n u ^ 2 : ℝ) : ℂ) := by
  unfold airySeedG
  rw [← ofReal_airyCardinalR, Complex.ofReal_pow]

lemma airySeedG_re (n : ℕ) (u : ℝ) :
    (airySeedG n (u : ℂ)).re = airyCardinalR n u ^ 2 := by
  rw [airySeedG_ofReal, Complex.ofReal_re]

lemma airySeedG_re_nonneg (n : ℕ) (u : ℝ) : 0 ≤ (airySeedG n (u : ℂ)).re := by
  rw [airySeedG_re]; exact sq_nonneg _

lemma airySeedG_re_of_ne (n : ℕ) {u : ℝ} (hu : u ≠ airyZ n) :
    (airySeedG n (u : ℂ)).re = airyAi u ^ 2 / (u - airyZ n) ^ 2 := by
  rw [airySeedG_re, airyCardinalR_of_ne n hu, div_pow]

lemma airySeedG1Deriv_eq_sub_refJ0 (z : ℂ) :
    airySeedG1Deriv z = airyRefJ0 z - airySeedG 0 z := by
  unfold airySeedG1Deriv airyRefJ0 airySeedG
  ring

lemma airySeedG1Deriv_re (u : ℝ) :
    (airySeedG1Deriv (u : ℂ)).re = ceG1Deriv airyDerivFirstZero u := by
  unfold airySeedG1Deriv ceG1Deriv
  rw [airyDerivCardinalC_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]

lemma airySeedG1Deriv_re_nonneg (u : ℝ) : 0 ≤ (airySeedG1Deriv (u : ℂ)).re := by
  rw [airySeedG1Deriv_re]; exact sq_nonneg _

theorem airySeedF_inAiryClass (n : ℕ) : InAiryClass (airySeedF n) := by
  rw [funext (airySeedF_eq_trialSquareWitness n)]
  exact airyTrialSquareWitness_inAiryClass _ _

theorem airySeedG_inAiryClass (n : ℕ) : InAiryClass (airySeedG n) := by
  have heq : airySeedG n = fun z => airyCardinal n z * airyCardinal n z := by
    ext z; unfold airySeedG; ring
  rw [heq]
  exact airyCardinal_mul_inAiryClass n n

theorem airySeedG1Deriv_inAiryClass : InAiryClass airySeedG1Deriv := by
  rw [funext airySeedG1Deriv_eq_sub_refJ0]
  exact airyRefJ0_inAiryClass.sub (airySeedG_inAiryClass 0)

theorem integral_airySeedF (n : ℕ) : ∫ u : ℝ, (airySeedF n (u : ℂ)).re = 0 := by
  have heq : (fun u : ℝ => (airySeedF n (u : ℂ)).re) =
      fun u : ℝ => (airyTrialSquareWitness (n + 1) (Pi.single ⟨n, Nat.lt_succ_self n⟩ 1)
        (airyZ n) (u : ℂ)).re := by
    ext u; rw [airySeedF_eq_trialSquareWitness]
  rw [heq, integral_airyTrialSquareWitness]
  rw [Finset.sum_eq_single ⟨n, Nat.lt_succ_self n⟩]
  · simp
  · intro m _ hmn; simp [Pi.single_eq_of_ne hmn]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem integral_airySeedG (n : ℕ) : ∫ u : ℝ, (airySeedG n (u : ℂ)).re = 1 := by
  have heq : (fun u : ℝ => (airySeedG n (u : ℂ)).re) =
      fun u : ℝ => airyCardinalR n u * airyCardinalR n u := by
    ext u; rw [airySeedG_re, sq]
  rw [heq, integral_airyCardinalR_mul n n]
  simp

theorem integral_airySeedG1Deriv :
    ∫ u : ℝ, (airySeedG1Deriv (u : ℂ)).re = |airyDerivFirstZero| := by
  have heq : (fun u : ℝ => (airySeedG1Deriv (u : ℂ)).re) = ceG1Deriv airyDerivFirstZero :=
    funext airySeedG1Deriv_re
  rw [heq]
  exact airy_seed_integrals.2.2.2

theorem hasGenRationalAiryCoeffs_airySeedF (n : ℕ) :
    HasGenRationalAiryCoeffs (airySeedF n) (-1) 0 := by
  set a : ℝ := airyZ n
  set R_star : ℝ := max 4 (2 * |a|)
  refine ⟨airySeedF_inAiryClass n, R_star, 2 * |a|, 1, Polynomial.X - Polynomial.C a,
    0, 1, 0, 1, le_max_left _ _, by positivity,
    Polynomial.monic_X_sub_C a, Polynomial.monic_one, Polynomial.monic_one,
    ?_, fun _ h => by simp at h, fun _ h => by simp at h, ?_, ?_⟩
  · intro z hz
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
      Complex.real_smul, mul_one, sub_eq_zero] at hz
    rw [hz, Complex.norm_real, Real.norm_eq_abs]
    exact ⟨Complex.ofReal_im _,
      (by linarith only [abs_nonneg a] : |a| ≤ 2 * |a|).trans (le_max_right _ _)⟩
  · intro z hz
    have hza : z ≠ (a : ℂ) := by
      intro h0
      rw [h0, Complex.norm_real, Real.norm_eq_abs] at hz
      have : 2 * |a| < |a| := (le_max_right 4 (2 * |a|)).trans_lt hz
      linarith only [this, abs_nonneg a]
    unfold airySeedF
    rw [airyCardinal_of_ne n hza]
    simp only [map_one, map_zero, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, zero_div, zero_mul, add_zero]
    dsimp [a]
    ring
  · intro w hw
    have hw4 : 4 ≤ ‖w‖ := by linarith only [le_max_left 4 (2 * |a|), hw]
    have hw_pos : 0 < ‖w‖ := by linarith only [hw4]
    have hw_ne : w ≠ 0 := norm_ne_zero_iff.mp hw_pos.ne'
    have ha_le : 2 * |a| ≤ ‖w‖ := by linarith only [le_max_right 4 (2 * |a|), hw]
    have hden : ‖w‖ / 2 ≤ ‖-w - (a : ℂ)‖ := by
      have htri := norm_sub_norm_le w (-(a : ℂ))
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at htri
      have heq : ‖-w - (a : ℂ)‖ = ‖w - (-(a : ℂ))‖ := by
        rw [← norm_neg (-w - (a : ℂ))]; congr 1; ring
      rw [heq]
      linarith only [htri, ha_le]
    have hden_pos : 0 < ‖-w - (a : ℂ)‖ := by linarith only [hw_pos, hden]
    have hden_ne : -w - (a : ℂ) ≠ 0 := norm_ne_zero_iff.mp hden_pos.ne'
    simp only [map_one, map_zero, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, zero_div, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_zero, zero_mul, sub_zero, norm_zero]
    refine ⟨?_, by positivity, by positivity⟩
    have hid : 1 / (-w - (a : ℂ)) - (-1 : ℂ) * w⁻¹ = -(a : ℂ) / (w * (-w - (a : ℂ))) := by
      field_simp [hw_ne, hden_ne]; ring
    rw [hid, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.rpow_neg hw_pos.le, show ‖w‖ ^ (2 : ℝ) = ‖w‖ ^ 2 by norm_cast]
    calc |a| / (‖w‖ * ‖-w - (a : ℂ)‖)
        ≤ |a| / (‖w‖ * (‖w‖ / 2)) := div_le_div_of_nonneg_left (abs_nonneg a)
          (by positivity) (mul_le_mul_of_nonneg_left hden hw_pos.le)
      _ = 2 * |a| * (‖w‖ ^ 2)⁻¹ := by field_simp [hw_pos.ne']

theorem hasGenRationalAiryCoeffs_airySeedG (n : ℕ) :
    HasGenRationalAiryCoeffs (airySeedG n) 0 0 := by
  set a : ℝ := airyZ n
  set R_star : ℝ := max 4 (2 * |a|)
  refine ⟨airySeedG_inAiryClass n, R_star, 4, 1, (Polynomial.X - Polynomial.C a) ^ 2,
    0, 1, 0, 1, le_max_left _ _, by norm_num,
    (Polynomial.monic_X_sub_C a).pow 2, Polynomial.monic_one, Polynomial.monic_one,
    ?_, fun _ h => by simp at h, fun _ h => by simp at h, ?_, ?_⟩
  · intro z hz
    simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, sq_eq_zero_iff, sub_eq_zero] at hz
    rw [hz, Complex.norm_real, Real.norm_eq_abs]
    exact ⟨Complex.ofReal_im _,
      (by linarith only [abs_nonneg a] : |a| ≤ 2 * |a|).trans (le_max_right _ _)⟩
  · intro z hz
    have hza : z ≠ (a : ℂ) := by
      intro h0
      rw [h0, Complex.norm_real, Real.norm_eq_abs] at hz
      have : 2 * |a| < |a| := (le_max_right 4 (2 * |a|)).trans_lt hz
      linarith only [this, abs_nonneg a]
    unfold airySeedG
    rw [airyCardinal_of_ne n hza]
    simp only [map_one, map_zero, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, zero_div, zero_mul, add_zero]
    dsimp [a]
    field_simp [sub_ne_zero.mpr hza]
  · intro w hw
    have hw4 : 4 ≤ ‖w‖ := by linarith only [le_max_left 4 (2 * |a|), hw]
    have hw_pos : 0 < ‖w‖ := by linarith only [hw4]
    have ha_le : 2 * |a| ≤ ‖w‖ := by linarith only [le_max_right 4 (2 * |a|), hw]
    have hden : ‖w‖ / 2 ≤ ‖-w - (a : ℂ)‖ := by
      have htri := norm_sub_norm_le w (-(a : ℂ))
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at htri
      have heq : ‖-w - (a : ℂ)‖ = ‖w - (-(a : ℂ))‖ := by
        rw [← norm_neg (-w - (a : ℂ))]; congr 1; ring
      rw [heq]
      linarith only [htri, ha_le]
    simp only [map_one, map_zero, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, zero_div, Complex.ofReal_zero,
      zero_mul, sub_zero, norm_zero]
    refine ⟨?_, by positivity, by positivity⟩
    rw [norm_div, norm_one, norm_pow, Real.rpow_neg hw_pos.le,
      show ‖w‖ ^ (2 : ℝ) = ‖w‖ ^ 2 by norm_cast]
    calc 1 / ‖-w - (a : ℂ)‖ ^ 2
        ≤ 1 / (‖w‖ / 2) ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity)
          (pow_le_pow_left₀ (by positivity) hden 2)
      _ = 4 * (‖w‖ ^ 2)⁻¹ := by field_simp [hw_pos.ne']; ring

theorem hasGenRationalAiryCoeffs_airySeedG1Deriv :
    HasGenRationalAiryCoeffs airySeedG1Deriv 0 1 := by
  set a1' : ℝ := airyDerivFirstZero
  set R_star : ℝ := max 4 (2 * |a1'|)
  have ha1'_zero : deriv airyAiC (a1' : ℂ) = 0 := by
    rw [deriv_airyAiC_ofReal, airyDerivFirstZero_spec.2.2, Complex.ofReal_zero]
  refine ⟨airySeedG1Deriv_inAiryClass, R_star, 10 * |a1'|, 0, 1, 0, 1,
    1, (Polynomial.X - Polynomial.C a1') ^ 2, le_max_left _ _, by positivity,
    Polynomial.monic_one, Polynomial.monic_one, (Polynomial.monic_X_sub_C a1').pow 2,
    fun _ h => by simp at h, fun _ h => by simp at h, ?_, ?_, ?_⟩
  · intro z hz
    simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, sq_eq_zero_iff, sub_eq_zero] at hz
    rw [hz, Complex.norm_real, Real.norm_eq_abs]
    exact ⟨Complex.ofReal_im _,
      (by linarith only [abs_nonneg a1'] : |a1'| ≤ 2 * |a1'|).trans (le_max_right _ _)⟩
  · intro z hz
    have hza : z ≠ (a1' : ℂ) := by
      intro h0
      rw [h0, Complex.norm_real, Real.norm_eq_abs] at hz
      have : 2 * |a1'| < |a1'| := (le_max_right 4 (2 * |a1'|)).trans_lt hz
      linarith only [this, abs_nonneg a1']
    unfold airySeedG1Deriv airyDerivCardinalC
    rw [dslope_of_ne _ hza, slope_def_field, ha1'_zero, sub_zero]
    simp only [map_one, map_zero, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, zero_div, zero_mul, zero_add]
    dsimp [a1']
    field_simp [sub_ne_zero.mpr hza]
  · intro w hw
    have hw4 : 4 ≤ ‖w‖ := by linarith only [le_max_left 4 (2 * |a1'|), hw]
    have hw_pos : 0 < ‖w‖ := by linarith only [hw4]
    have hw_ne : w ≠ 0 := norm_ne_zero_iff.mp hw_pos.ne'
    have ha_le : 2 * |a1'| ≤ ‖w‖ := by linarith only [le_max_right 4 (2 * |a1'|), hw]
    have hden : ‖w‖ / 2 ≤ ‖-w - (a1' : ℂ)‖ := by
      have htri := norm_sub_norm_le w (-(a1' : ℂ))
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at htri
      have heq : ‖-w - (a1' : ℂ)‖ = ‖w - (-(a1' : ℂ))‖ := by
        rw [← norm_neg (-w - (a1' : ℂ))]; congr 1; ring
      rw [heq]
      linarith only [htri, ha_le]
    have hden_pos : 0 < ‖-w - (a1' : ℂ)‖ := by linarith only [hw_pos, hden]
    have hden_ne : -w - (a1' : ℂ) ≠ 0 := norm_ne_zero_iff.mp hden_pos.ne'
    simp only [map_one, map_zero, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, zero_div, Complex.ofReal_zero,
      Complex.ofReal_one, one_mul, zero_mul, sub_zero, norm_zero]
    refine ⟨by positivity, by positivity, ?_⟩
    have hid : 1 / (-w - (a1' : ℂ)) ^ 2 - (w ^ 2)⁻¹ =
        (-(2 : ℂ) * (a1' : ℂ) * w - (a1' : ℂ) ^ 2) / (w ^ 2 * (-w - (a1' : ℂ)) ^ 2) := by
      field_simp [hw_ne, hden_ne]; ring
    rw [hid, norm_div, norm_mul, norm_pow, norm_pow, Real.rpow_neg hw_pos.le,
      show ‖w‖ ^ (3 : ℝ) = ‖w‖ ^ 3 by norm_cast]
    have hnum : ‖-(2 : ℂ) * (a1' : ℂ) * w - (a1' : ℂ) ^ 2‖ ≤ (5 / 2) * |a1'| * ‖w‖ := by
      have h1 : ‖-(2 : ℂ) * (a1' : ℂ) * w‖ = 2 * |a1'| * ‖w‖ := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(a1' : ℂ) ^ 2‖ ≤ (1 / 2) * |a1'| * ‖w‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
        nlinarith only [ha_le, abs_nonneg a1']
      exact (norm_sub_le _ _).trans (by linarith only [h1, h2])
    have hden_sq : ‖w‖ ^ 4 / 4 ≤ ‖w‖ ^ 2 * ‖-w - (a1' : ℂ)‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hden 2
      nlinarith only [mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖w‖)]
    calc ‖-(2 : ℂ) * (a1' : ℂ) * w - (a1' : ℂ) ^ 2‖ / (‖w‖ ^ 2 * ‖-w - (a1' : ℂ)‖ ^ 2)
        ≤ ((5 / 2) * |a1'| * ‖w‖) / (‖w‖ ^ 4 / 4) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden_sq
      _ = 10 * |a1'| * (‖w‖ ^ 3)⁻¹ := by field_simp [hw_pos.ne']; ring

/-- **Lemma `lem:al-seeds`** (`ce_airy_lp_proofs.tex`): membership in `\mathcal{R}_{\mathrm{Ai}}^{\mathrm{gen}}`,
nonnegativity of `g_n`, exact integrals, and leading coefficients `\beta_\infty` and `\beta_+` of
`f_n`, `g_n`, and `g_1'`. -/
theorem lem_al_seeds :
    (∀ n : ℕ,
      InGenRationalAiry (airySeedF n) ∧
      InGenRationalAiry (airySeedG n) ∧
      (∀ u : ℝ, 0 ≤ (airySeedG n (u : ℂ)).re) ∧
      (∫ u : ℝ, (airySeedF n (u : ℂ)).re) = 0 ∧
      (∫ u : ℝ, (airySeedG n (u : ℂ)).re) = 1 ∧
      airyBetaInf (fun z => -airySeedF n z) = 1 ∧
      airyBetaInf (airySeedG n) = 0 ∧
      airyBetaPlus (airySeedF n) = 1 ∧
      airyBetaPlus (airySeedG n) = 0) ∧
    InGenRationalAiry airySeedG1Deriv ∧
    (∫ u : ℝ, (airySeedG1Deriv (u : ℂ)).re) = |airyDerivFirstZero| ∧
    airyBetaInf airySeedG1Deriv = 1 ∧
    airyBetaPlus airySeedG1Deriv = 1 := by
  refine ⟨fun n => ?_, ?_⟩
  · have hf := hasGenRationalAiryCoeffs_airySeedF n
    have hg := hasGenRationalAiryCoeffs_airySeedG n
    have hnf := hf.neg
    refine ⟨⟨-1, 0, hf⟩, ⟨0, 0, hg⟩, airySeedG_re_nonneg n, integral_airySeedF n,
      integral_airySeedG n, ?_, ?_, ?_, ?_⟩
    · rw [hnf.beta_eq.2.2.1]; norm_num
    · rw [hg.beta_eq.2.2.1]; norm_num
    · rw [hf.beta_eq.2.2.2]; norm_num
    · rw [hg.beta_eq.2.2.2]; norm_num
  · have hg' := hasGenRationalAiryCoeffs_airySeedG1Deriv
    refine ⟨⟨0, 1, hg'⟩, integral_airySeedG1Deriv, ?_, ?_⟩
    · rw [hg'.beta_eq.2.2.1]; norm_num
    · rw [hg'.beta_eq.2.2.2]; norm_num

/-- info: 'FormalResearch.SignUncertainty.lem_al_seeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_al_seeds


end FormalResearch.SignUncertainty
