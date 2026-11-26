module

public import FormalResearch.SignUncertainty.CtDualUnif

/-!
# The Gaussian regulariser of `ct:dual-id` (2) and its amplitude bounds

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (2), proof (the regulariser `M_δ`; here
`M_δ(ζ) = e^{-δ ζ(1-ζ)}` instead of `(1 + δζ(1-ζ))⁻¹`, which has the same properties used there: entire, `M_δ(1-ζ) = M_δ(ζ)`,
`M_δ(ζ̄) = conj M_δ(ζ)`, `|M_δ(σ+iτ)| ≤ e^{-δτ²}`).  **Proved.**

`ampBd_mulM`: an `AmpBd` amplitude times a factor with `|M| ≤ 1`, `|M'| ≤ K₁/(1+τ)`, `|M''| ≤ K₂/(1+τ)²` is an `AmpBd`
amplitude with constant `C_A(1 + 2K₁ + K₂)`; `gcut_bounds`: `K₁ = 4`, `K₂ = 36` for the Gaussian factor uniformly in `δ ∈ [0,1]`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtOsc

lemma div_le_neg_half {τ : ℝ} (hτ : 0 < τ) : τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (-1 / 2 : ℝ) := by
  rw [← rpow_half_div hτ]
  exact div_le_div_of_nonneg_left (by positivity) hτ (by linarith)

lemma div_le_neg_three_half {τ : ℝ} (hτ : 0 < τ) : τ ^ (-1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (-3 / 2 : ℝ) := by
  rw [← rpow_neg_half_div hτ]
  exact div_le_div_of_nonneg_left (by positivity) hτ (by linarith)

/-- The product bound for `AmpBd`. -/
theorem ampBd_mulM {CA K1 K2 : ℝ} {A A1 A2 M M1 M2 : ℝ → ℂ} (hA : AmpBd CA A A1 A2) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hM : ∀ τ : ℝ, 0 < τ → HasDerivAt M (M1 τ) τ) (hM1 : ∀ τ : ℝ, 0 < τ → HasDerivAt M1 (M2 τ) τ)
    (hM2c : ContinuousOn M2 (Ioi 0)) (b0 : ∀ τ : ℝ, 0 < τ → ‖M τ‖ ≤ 1)
    (b1 : ∀ τ : ℝ, 0 < τ → ‖M1 τ‖ ≤ K1 / (1 + τ)) (b2 : ∀ τ : ℝ, 0 < τ → ‖M2 τ‖ ≤ K2 / (1 + τ) ^ 2) :
    AmpBd (CA * (1 + 2 * K1 + K2)) (fun τ => A τ * M τ) (fun τ => A1 τ * M τ + A τ * M1 τ)
      (fun τ => (A2 τ * M τ + A1 τ * M1 τ) + (A1 τ * M1 τ + A τ * M2 τ)) where
  CA0 := by have := hA.CA0; positivity
  d1 τ hτ := (hA.d1 τ hτ).mul (hM τ hτ)
  d2 τ hτ := ((hA.d2 τ hτ).mul (hM τ hτ)).add ((hA.d1 τ hτ).mul (hM1 τ hτ))
  c2 := by
    have cA : ContinuousOn A (Ioi 0) := fun τ hτ => (hA.d1 τ hτ).continuousAt.continuousWithinAt
    have cA1 : ContinuousOn A1 (Ioi 0) := fun τ hτ => (hA.d2 τ hτ).continuousAt.continuousWithinAt
    have cM : ContinuousOn M (Ioi 0) := fun τ hτ => (hM τ hτ).continuousAt.continuousWithinAt
    have cM1 : ContinuousOn M1 (Ioi 0) := fun τ hτ => (hM1 τ hτ).continuousAt.continuousWithinAt
    exact ((hA.c2.mul cM).add (cA1.mul cM1)).add ((cA1.mul cM1).add (cA.mul hM2c))
  b0 τ hτ := by
    have hCA := hA.CA0
    have hu : 0 ≤ τ ^ (1 / 2 : ℝ) / (1 + τ) := by positivity
    have h1 : ‖A τ * M τ‖ ≤ CA * τ ^ (1 / 2 : ℝ) / (1 + τ) := by
      rw [norm_mul]
      refine le_trans ?_ (hA.b0 τ hτ)
      calc ‖A τ‖ * ‖M τ‖ ≤ ‖A τ‖ * 1 := mul_le_mul_of_nonneg_left (b0 τ hτ) (norm_nonneg _)
        _ = ‖A τ‖ := mul_one _
    refine h1.trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hK1, hK2, hCA]) hu
  b1 τ hτ := by
    have hCA := hA.CA0
    have hf1 : τ ^ (1 / 2 : ℝ) / (1 + τ) / (1 + τ) ≤ τ ^ (-1 / 2 : ℝ) / (1 + τ) :=
      div_le_div_of_nonneg_right (div_le_neg_half hτ) (by positivity)
    have hs : 0 < 1 + τ := by linarith
    have e1 : ‖A1 τ * M τ‖ ≤ CA * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by
      rw [norm_mul]
      calc ‖A1 τ‖ * ‖M τ‖ ≤ ‖A1 τ‖ * 1 := mul_le_mul_of_nonneg_left (b0 τ hτ) (norm_nonneg _)
        _ = ‖A1 τ‖ := mul_one _
        _ ≤ CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) := hA.b1 τ hτ
        _ = _ := mul_div_assoc _ _ _
    have e2 : ‖A τ * M1 τ‖ ≤ CA * K1 * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by
      rw [norm_mul]
      have h0 : ‖A τ‖ ≤ CA * (τ ^ (1 / 2 : ℝ) / (1 + τ)) := by
        have := hA.b0 τ hτ; rwa [mul_div_assoc] at this
      have := mul_le_mul h0 (b1 τ hτ) (norm_nonneg _) (by positivity)
      refine this.trans ?_
      calc CA * (τ ^ (1 / 2 : ℝ) / (1 + τ)) * (K1 / (1 + τ)) = CA * K1 * (τ ^ (1 / 2 : ℝ) / (1 + τ) / (1 + τ)) := by ring
        _ ≤ CA * K1 * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := mul_le_mul_of_nonneg_left hf1 (by positivity)
    have hu : 0 ≤ τ ^ (-1 / 2 : ℝ) / (1 + τ) := by positivity
    calc ‖A1 τ * M τ + A τ * M1 τ‖ ≤ ‖A1 τ * M τ‖ + ‖A τ * M1 τ‖ := norm_add_le _ _
      _ ≤ CA * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) + CA * K1 * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := add_le_add e1 e2
      _ ≤ CA * (1 + 2 * K1 + K2) * τ ^ (-1 / 2 : ℝ) / (1 + τ) := by
          rw [mul_div_assoc _ (τ ^ (-1 / 2 : ℝ))]
          have : CA * (1 + 2 * K1 + K2) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) -
            (CA * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) + CA * K1 * (τ ^ (-1 / 2 : ℝ) / (1 + τ))) =
            (CA * (K1 + K2) * (τ ^ (-1 / 2 : ℝ) / (1 + τ))) := by ring
          have h2 : 0 ≤ CA * (K1 + K2) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by positivity
          linarith only [this, h2]
  b2 τ hτ := by
    have hCA := hA.CA0
    have hs : 0 < 1 + τ := by linarith
    have hf1 : τ ^ (1 / 2 : ℝ) / (1 + τ) / (1 + τ) ≤ τ ^ (-1 / 2 : ℝ) / (1 + τ) :=
      div_le_div_of_nonneg_right (div_le_neg_half hτ) hs.le
    have hf2 : τ ^ (-1 / 2 : ℝ) / (1 + τ) / (1 + τ) ≤ τ ^ (-3 / 2 : ℝ) / (1 + τ) :=
      div_le_div_of_nonneg_right (div_le_neg_three_half hτ) hs.le
    have hf3 : τ ^ (1 / 2 : ℝ) / (1 + τ) / (1 + τ) / (1 + τ) ≤ τ ^ (-3 / 2 : ℝ) / (1 + τ) :=
      (div_le_div_of_nonneg_right hf1 hs.le).trans hf2
    have e1 : ‖A2 τ * M τ‖ ≤ CA * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by
      rw [norm_mul]
      calc ‖A2 τ‖ * ‖M τ‖ ≤ ‖A2 τ‖ * 1 := mul_le_mul_of_nonneg_left (b0 τ hτ) (norm_nonneg _)
        _ = ‖A2 τ‖ := mul_one _
        _ ≤ CA * τ ^ (-3 / 2 : ℝ) / (1 + τ) := hA.b2 τ hτ
        _ = _ := mul_div_assoc _ _ _
    have e2 : ‖A1 τ * M1 τ‖ ≤ CA * K1 * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by
      rw [norm_mul]
      have h0 : ‖A1 τ‖ ≤ CA * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by
        have := hA.b1 τ hτ; rwa [mul_div_assoc] at this
      have := mul_le_mul h0 (b1 τ hτ) (norm_nonneg _) (by positivity)
      refine this.trans ?_
      calc CA * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) * (K1 / (1 + τ)) = CA * K1 * (τ ^ (-1 / 2 : ℝ) / (1 + τ) / (1 + τ)) := by ring
        _ ≤ CA * K1 * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := mul_le_mul_of_nonneg_left hf2 (by positivity)
    have e3 : ‖A τ * M2 τ‖ ≤ CA * K2 * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by
      rw [norm_mul]
      have h0 : ‖A τ‖ ≤ CA * (τ ^ (1 / 2 : ℝ) / (1 + τ)) := by
        have := hA.b0 τ hτ; rwa [mul_div_assoc] at this
      have := mul_le_mul h0 (b2 τ hτ) (norm_nonneg _) (by positivity)
      refine this.trans ?_
      calc CA * (τ ^ (1 / 2 : ℝ) / (1 + τ)) * (K2 / (1 + τ) ^ 2) =
            CA * K2 * (τ ^ (1 / 2 : ℝ) / (1 + τ) / (1 + τ) / (1 + τ)) := by field_simp
        _ ≤ CA * K2 * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := mul_le_mul_of_nonneg_left hf3 (by positivity)
    have hu : 0 ≤ τ ^ (-3 / 2 : ℝ) / (1 + τ) := by positivity
    calc ‖(A2 τ * M τ + A1 τ * M1 τ) + (A1 τ * M1 τ + A τ * M2 τ)‖ ≤
          (‖A2 τ * M τ‖ + ‖A1 τ * M1 τ‖) + (‖A1 τ * M1 τ‖ + ‖A τ * M2 τ‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ (CA * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) + CA * K1 * (τ ^ (-3 / 2 : ℝ) / (1 + τ))) +
          (CA * K1 * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) + CA * K2 * (τ ^ (-3 / 2 : ℝ) / (1 + τ))) :=
          add_le_add (add_le_add e1 e2) (add_le_add e2 e3)
      _ = CA * (1 + 2 * K1 + K2) * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by ring
      _ = CA * (1 + 2 * K1 + K2) * τ ^ (-3 / 2 : ℝ) / (1 + τ) := (mul_div_assoc _ _ _).symm

/-- The Gaussian regulariser on the imaginary axis, `M_δ(iτ) = e^{-δ iτ(1-iτ)} = e^{-δ(τ² + iτ)}`. -/
noncomputable def gcut (δ τ : ℝ) : ℂ := Complex.exp (-(δ : ℂ) * ((τ : ℂ) ^ 2 + Complex.I * τ))

noncomputable def gcut1 (δ τ : ℝ) : ℂ := (-(δ : ℂ) * (2 * τ + Complex.I)) * gcut δ τ

noncomputable def gcut2 (δ τ : ℝ) : ℂ := ((δ : ℂ) ^ 2 * (2 * τ + Complex.I) ^ 2 - 2 * δ) * gcut δ τ

lemma norm_gcut (δ τ : ℝ) : ‖gcut δ τ‖ = Real.exp (-(δ * τ ^ 2)) := by
  unfold gcut
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, pow_two, Complex.add_re, Complex.mul_im]

lemma hasDerivAt_gcut (δ τ : ℝ) : HasDerivAt (gcut δ) (gcut1 δ τ) τ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 τ := (hasDerivAt_id τ).ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => -(δ : ℂ) * ((x : ℂ) ^ 2 + Complex.I * x))
      (-(δ : ℂ) * (2 * τ + Complex.I)) τ := by
    have := ((h1.pow 2).add (h1.const_mul Complex.I)).const_mul (-(δ : ℂ))
    refine this.congr_deriv ?_
    simp
  have := h2.cexp
  unfold gcut1
  refine this.congr_deriv ?_
  unfold gcut; ring

lemma hasDerivAt_gcut1 (δ τ : ℝ) : HasDerivAt (gcut1 δ) (gcut2 δ τ) τ := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 τ := (hasDerivAt_id τ).ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => -(δ : ℂ) * (2 * (x : ℂ) + Complex.I)) (-(δ : ℂ) * 2) τ := by
    have := ((h1.const_mul (2 : ℂ)).add_const Complex.I).const_mul (-(δ : ℂ))
    refine this.congr_deriv ?_
    simp
  have := h2.mul (hasDerivAt_gcut δ τ)
  unfold gcut1 gcut2
  refine this.congr_deriv ?_
  unfold gcut1; ring

lemma continuous_gcut2 (δ : ℝ) : Continuous (gcut2 δ) := by
  unfold gcut2 gcut
  fun_prop

lemma exp_neg_aux1 {x : ℝ} (hx : 0 ≤ x) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hp := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hp]
  linarith

lemma exp_neg_aux2 {x : ℝ} (hx : 0 ≤ x) : (1 + x) ^ 2 * Real.exp (-x) ≤ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hx
  have hp := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hp]
  nlinarith [sq_nonneg x, hx]

lemma norm_two_tau_I (τ : ℝ) (hτ : 0 < τ) : ‖(2 * (τ : ℂ) + Complex.I)‖ ≤ 2 * τ + 1 := by
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_I, norm_mul, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos hτ]

lemma gcut_b0 {δ τ : ℝ} (hδ : 0 ≤ δ) : ‖gcut δ τ‖ ≤ 1 := by
  rw [norm_gcut]
  exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg τ])

lemma gcut_b1 {δ τ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) : ‖gcut1 δ τ‖ ≤ 4 / (1 + τ) := by
  unfold gcut1
  rw [norm_mul, norm_gcut, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
  have hn := norm_two_tau_I τ hτ
  have hx : 0 ≤ δ * τ ^ 2 := by positivity
  have e := exp_neg_aux1 hx
  have he := (Real.exp_pos (-(δ * τ ^ 2))).le
  rw [le_div_iff₀ (by linarith)]
  have h1 : δ * ‖(2 * (τ : ℂ) + Complex.I)‖ * Real.exp (-(δ * τ ^ 2)) * (1 + τ) ≤
      δ * (2 * τ + 1) * (1 + τ) * Real.exp (-(δ * τ ^ 2)) := by
    have : δ * ‖(2 * (τ : ℂ) + Complex.I)‖ ≤ δ * (2 * τ + 1) := mul_le_mul_of_nonneg_left hn hδ
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg he (by linarith : (0 : ℝ) ≤ 1 + τ))]
  have h2 : δ * (2 * τ + 1) * (1 + τ) ≤ 4 * (1 + δ * τ ^ 2) := by
    nlinarith [mul_nonneg hδ (sq_nonneg (τ - 1)), mul_nonneg hδ hτ.le, sq_nonneg τ, mul_nonneg hδ (sq_nonneg τ)]
  have h3 : δ * (2 * τ + 1) * (1 + τ) * Real.exp (-(δ * τ ^ 2)) ≤ 4 * ((1 + δ * τ ^ 2) * Real.exp (-(δ * τ ^ 2))) := by
    have := mul_le_mul_of_nonneg_right h2 he
    linarith only [this]
  linarith only [h1, h3, e]

lemma gcut_b2 {δ τ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) : ‖gcut2 δ τ‖ ≤ 36 / (1 + τ) ^ 2 := by
  unfold gcut2
  rw [norm_mul, norm_gcut]
  have hn := norm_two_tau_I τ hτ
  have hx : 0 ≤ δ * τ ^ 2 := by positivity
  set x := δ * τ ^ 2 with hxdef
  have e1 := exp_neg_aux1 hx
  have e2 := exp_neg_aux2 hx
  have he := (Real.exp_pos (-x)).le
  have hs : 0 < (1 + τ) ^ 2 := by positivity
  rw [le_div_iff₀ hs]
  have hq : ‖(δ : ℂ) ^ 2 * (2 * (τ : ℂ) + Complex.I) ^ 2 - 2 * δ‖ ≤ δ ^ 2 * (2 * τ + 1) ^ 2 + 2 * δ := by
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ?_ ?_
    · rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity)
    · rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
  have hA : (2 * τ + 1) * (1 + τ) ≤ 4 * (1 + τ ^ 2) := by nlinarith [sq_nonneg (τ - 1)]
  have hB : δ ^ 2 * (2 * τ + 1) ^ 2 * (1 + τ) ^ 2 ≤ 16 * (1 + x) ^ 2 := by
    have h1 : ((2 * τ + 1) * (1 + τ)) ^ 2 ≤ (4 * (1 + τ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hA 2
    have h2 : δ * (1 + τ ^ 2) ≤ 1 + x := by rw [hxdef]; nlinarith
    have h3 : (δ * (1 + τ ^ 2)) ^ 2 ≤ (1 + x) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    calc δ ^ 2 * (2 * τ + 1) ^ 2 * (1 + τ) ^ 2 = δ ^ 2 * ((2 * τ + 1) * (1 + τ)) ^ 2 := by ring
      _ ≤ δ ^ 2 * (4 * (1 + τ ^ 2)) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 16 * (δ * (1 + τ ^ 2)) ^ 2 := by ring
      _ ≤ 16 * (1 + x) ^ 2 := by linarith only [h3]
  have hC : 2 * δ * (1 + τ) ^ 2 ≤ 4 * (1 + x) := by
    have : (1 + τ) ^ 2 ≤ 2 * (1 + τ ^ 2) := by nlinarith [sq_nonneg (τ - 1)]
    have h2 : δ * (1 + τ ^ 2) ≤ 1 + x := by rw [hxdef]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hδ]
  have h4 : ‖(δ : ℂ) ^ 2 * (2 * (τ : ℂ) + Complex.I) ^ 2 - 2 * δ‖ * Real.exp (-x) * (1 + τ) ^ 2 ≤
      (δ ^ 2 * (2 * τ + 1) ^ 2 + 2 * δ) * (1 + τ) ^ 2 * Real.exp (-x) := by
    have := mul_le_mul_of_nonneg_right hq (mul_nonneg he hs.le)
    nlinarith [this]
  have h5 : (δ ^ 2 * (2 * τ + 1) ^ 2 + 2 * δ) * (1 + τ) ^ 2 ≤ 16 * (1 + x) ^ 2 + 4 * (1 + x) := by
    nlinarith only [hB, hC]
  have h6 := mul_le_mul_of_nonneg_right h5 he
  nlinarith only [h4, h6, e1, e2]

lemma gcut_ampBd {CA : ℝ} {A A1 A2 : ℝ → ℂ} (hA : AmpBd CA A A1 A2) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    AmpBd (CA * (1 + 2 * 4 + 36)) (fun τ => A τ * gcut δ τ)
      (fun τ => A1 τ * gcut δ τ + A τ * gcut1 δ τ)
      (fun τ => (A2 τ * gcut δ τ + A1 τ * gcut1 δ τ) + (A1 τ * gcut1 δ τ + A τ * gcut2 δ τ)) :=
  ampBd_mulM hA (by norm_num) (by norm_num) (fun τ _ => hasDerivAt_gcut δ τ) (fun τ _ => hasDerivAt_gcut1 δ τ)
    (continuous_gcut2 δ).continuousOn (fun τ _ => gcut_b0 hδ) (fun τ hτ => gcut_b1 hδ hδ1 hτ)
    (fun τ hτ => gcut_b2 hδ hδ1 hτ)

/-- info: 'FormalResearch.SignUncertainty.CtOsc.ampBd_mulM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampBd_mulM

/-- info: 'FormalResearch.SignUncertainty.CtOsc.gcut_ampBd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gcut_ampBd

end FormalResearch.SignUncertainty.CtOsc
