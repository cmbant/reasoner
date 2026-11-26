/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspBase

/-!
# Integration by parts with explicit majorants (`fct:unscaled-cusp`, F2a)

`ibp_step`: one integration by parts `∫_α^β e^{iΦ} h = [e^{iΦ} h/(iΦ')]_α^β + i ∫_α^β e^{iΦ} (h/Φ')'`, stated with `HasDerivAt`
hypotheses only (`Φ' = D1`, `Φ'' = D2`, `h' = h1`).
`ibp_one_bound`, `ibp_two_bound`: one and two integrations by parts, with the pointwise majorants `‖h‖ ≤ B0`, `‖h'‖ ≤ B1`,
`‖h''‖ ≤ B2`, `|Φ'| ≥ P1 > 0`, `|Φ''| ≤ P2`, `|Φ'''| ≤ P3`: the bounds only involve the endpoint values and one integral of
the majorants.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

/-- **One integration by parts** on `[α, β]`. -/
theorem ibp_step {α β : ℝ} (hαβ : α ≤ β) {Φ D1 D2 : ℝ → ℝ} {h h1 : ℝ → ℂ}
    (hΦ : ∀ x ∈ Icc α β, HasDerivAt Φ (D1 x) x) (hD1 : ∀ x ∈ Icc α β, HasDerivAt D1 (D2 x) x)
    (hne : ∀ x ∈ Icc α β, D1 x ≠ 0) (hh : ∀ x ∈ Icc α β, HasDerivAt h (h1 x) x)
    (hh1c : ContinuousOn h1 (Icc α β)) (hD2c : ContinuousOn D2 (Icc α β)) :
    ∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * h x =
      Complex.exp (Complex.I * (Φ β : ℂ)) * (h β / (Complex.I * (D1 β : ℂ))) -
        Complex.exp (Complex.I * (Φ α : ℂ)) * (h α / (Complex.I * (D1 α : ℂ))) +
      Complex.I * ∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) *
        (h1 x / (D1 x : ℂ) - h x * (D2 x : ℂ) / (D1 x : ℂ) ^ 2) := by
  set u : ℝ → ℂ := fun x => h x / (D1 x : ℂ) with hu
  set v : ℝ → ℂ := fun x => Complex.exp (Complex.I * (Φ x : ℂ)) / Complex.I with hv
  set u' : ℝ → ℂ := fun x => h1 x / (D1 x : ℂ) - h x * (D2 x : ℂ) / (D1 x : ℂ) ^ 2 with hu'
  set v' : ℝ → ℂ := fun x => Complex.exp (Complex.I * (Φ x : ℂ)) * (D1 x : ℂ) with hv'
  have hD1c : ContinuousOn D1 (Icc α β) := fun x hx => (hD1 x hx).continuousAt.continuousWithinAt
  have hΦc : ContinuousOn Φ (Icc α β) := fun x hx => (hΦ x hx).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc α β) := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  have hu_d : ∀ x ∈ uIcc α β, HasDerivAt u (u' x) x := by
    intro x hx
    rw [uIcc_of_le hαβ] at hx
    have hne' : (D1 x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne x hx)
    have := (hh x hx).div (hD1 x hx).ofReal_comp hne'
    refine this.congr_deriv ?_
    simp only [hu']; field_simp
  have hv_d : ∀ x ∈ uIcc α β, HasDerivAt v (v' x) x := by
    intro x hx
    rw [uIcc_of_le hαβ] at hx
    have h1 : HasDerivAt (fun t => Complex.I * (Φ t : ℂ)) (Complex.I * (D1 x : ℂ)) x :=
      (hΦ x hx).ofReal_comp.const_mul Complex.I
    have h2 := h1.cexp
    refine (h2.div_const Complex.I).congr_deriv ?_
    simp only [hv']; field_simp [Complex.I_ne_zero]
  have hu'c : ContinuousOn u' (Icc α β) := by
    have hne' : ∀ x ∈ Icc α β, (D1 x : ℂ) ≠ 0 := fun x hx => Complex.ofReal_ne_zero.mpr (hne x hx)
    have hD1C : ContinuousOn (fun x => (D1 x : ℂ)) (Icc α β) := Complex.continuous_ofReal.comp_continuousOn hD1c
    have hD2C : ContinuousOn (fun x => (D2 x : ℂ)) (Icc α β) := Complex.continuous_ofReal.comp_continuousOn hD2c
    exact (hh1c.div hD1C hne').sub (((hhc.mul hD2C).div (hD1C.pow 2) fun x hx => pow_ne_zero 2 (hne' x hx)))
  have hv'c : ContinuousOn v' (Icc α β) := by
    have h1 : ContinuousOn (fun x => Complex.exp (Complex.I * (Φ x : ℂ))) (Icc α β) :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp_continuousOn hΦc
    exact h1.mul (Complex.continuous_ofReal.comp_continuousOn hD1c)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_d hv_d
    (hu'c.intervalIntegrable_of_Icc hαβ) (hv'c.intervalIntegrable_of_Icc hαβ)
  have hlhs : ∫ x in α..β, u x * v' x = ∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * h x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hαβ] at hx
    have hne' : (D1 x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne x hx)
    simp only [hu, hv']; field_simp
  have hrhs : ∫ x in α..β, u' x * v x =
      (-Complex.I) * ∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * u' x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hv]; rw [div_eq_mul_inv, Complex.inv_I]; ring
  rw [hlhs, hrhs] at hibp
  have hb : u β * v β = Complex.exp (Complex.I * (Φ β : ℂ)) * (h β / (Complex.I * (D1 β : ℂ))) := by
    simp only [hu, hv]; ring
  have ha : u α * v α = Complex.exp (Complex.I * (Φ α : ℂ)) * (h α / (Complex.I * (D1 α : ℂ))) := by
    simp only [hu, hv]; ring
  rw [hb, ha] at hibp
  linear_combination hibp

/-- The amplitude `g = (h/Φ')'` produced by one integration by parts. -/
noncomputable def ibpG (D1 D2 : ℝ → ℝ) (h h1 : ℝ → ℂ) (x : ℝ) : ℂ :=
  h1 x / (D1 x : ℂ) - h x * (D2 x : ℂ) / (D1 x : ℂ) ^ 2

/-- The derivative of `ibpG`. -/
noncomputable def ibpG1 (D1 D2 D3 : ℝ → ℝ) (h h1 h2 : ℝ → ℂ) (x : ℝ) : ℂ :=
  h2 x / (D1 x : ℂ) - 2 * h1 x * (D2 x : ℂ) / (D1 x : ℂ) ^ 2 - h x * (D3 x : ℂ) / (D1 x : ℂ) ^ 2 +
    2 * h x * (D2 x : ℂ) ^ 2 / (D1 x : ℂ) ^ 3

lemma ibpG_continuousOn {α β : ℝ} {D1 D2 : ℝ → ℝ} {h h1 : ℝ → ℂ} (hD1c : ContinuousOn D1 (Icc α β))
    (hD2c : ContinuousOn D2 (Icc α β)) (hne : ∀ x ∈ Icc α β, D1 x ≠ 0) (hhc : ContinuousOn h (Icc α β))
    (hh1c : ContinuousOn h1 (Icc α β)) : ContinuousOn (ibpG D1 D2 h h1) (Icc α β) := by
  have hne' : ∀ x ∈ Icc α β, (D1 x : ℂ) ≠ 0 := fun x hx => Complex.ofReal_ne_zero.mpr (hne x hx)
  have hD1C : ContinuousOn (fun x => (D1 x : ℂ)) (Icc α β) := Complex.continuous_ofReal.comp_continuousOn hD1c
  have hD2C : ContinuousOn (fun x => (D2 x : ℂ)) (Icc α β) := Complex.continuous_ofReal.comp_continuousOn hD2c
  exact (hh1c.div hD1C hne').sub (((hhc.mul hD2C).div (hD1C.pow 2) fun x hx => pow_ne_zero 2 (hne' x hx)))

lemma hasDerivAt_ibpG {D1 D2 D3 : ℝ → ℝ} {h h1 h2 : ℝ → ℂ} {x : ℝ} (hD1 : HasDerivAt D1 (D2 x) x)
    (hD2 : HasDerivAt D2 (D3 x) x) (hne : D1 x ≠ 0) (hh : HasDerivAt h (h1 x) x) (hh1 : HasDerivAt h1 (h2 x) x) :
    HasDerivAt (ibpG D1 D2 h h1) (ibpG1 D1 D2 D3 h h1 h2 x) x := by
  have hne' : (D1 x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
  have a1 := hh1.div hD1.ofReal_comp hne'
  have a2 := (hh.mul hD2.ofReal_comp).div ((hD1.ofReal_comp).pow 2) (pow_ne_zero 2 hne')
  have := a1.sub a2
  refine this.congr_deriv ?_
  simp only [ibpG1, Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

lemma ibpG1_continuousOn {α β : ℝ} {D1 D2 D3 : ℝ → ℝ} {h h1 h2 : ℝ → ℂ} (hD1c : ContinuousOn D1 (Icc α β))
    (hD2c : ContinuousOn D2 (Icc α β)) (hD3c : ContinuousOn D3 (Icc α β)) (hne : ∀ x ∈ Icc α β, D1 x ≠ 0)
    (hhc : ContinuousOn h (Icc α β)) (hh1c : ContinuousOn h1 (Icc α β)) (hh2c : ContinuousOn h2 (Icc α β)) :
    ContinuousOn (ibpG1 D1 D2 D3 h h1 h2) (Icc α β) := by
  have hne' : ∀ x ∈ Icc α β, (D1 x : ℂ) ≠ 0 := fun x hx => Complex.ofReal_ne_zero.mpr (hne x hx)
  have hD1C : ContinuousOn (fun x => (D1 x : ℂ)) (Icc α β) := Complex.continuous_ofReal.comp_continuousOn hD1c
  have hD2C : ContinuousOn (fun x => (D2 x : ℂ)) (Icc α β) := Complex.continuous_ofReal.comp_continuousOn hD2c
  have hD3C : ContinuousOn (fun x => (D3 x : ℂ)) (Icc α β) := Complex.continuous_ofReal.comp_continuousOn hD3c
  have hp2 : ∀ x ∈ Icc α β, (D1 x : ℂ) ^ 2 ≠ 0 := fun x hx => pow_ne_zero 2 (hne' x hx)
  have hp3 : ∀ x ∈ Icc α β, (D1 x : ℂ) ^ 3 ≠ 0 := fun x hx => pow_ne_zero 3 (hne' x hx)
  have t1 := hh2c.div hD1C hne'
  have t2 := (((continuousOn_const (c := (2 : ℂ))).mul hh1c).mul hD2C).div (hD1C.pow 2) hp2
  have t3 := (hhc.mul hD3C).div (hD1C.pow 2) hp2
  have t4 := (((continuousOn_const (c := (2 : ℂ))).mul hhc).mul (hD2C.pow 2)).div (hD1C.pow 3) hp3
  exact ((t1.sub t2).sub t3).add t4

/-- **One integration by parts, norm form**: `|∫_α^β e^{iΦ} h| ≤ |h/Φ'|_{α,β} + ∫_α^β |(h/Φ')'|`. -/
theorem ibp_norm_one {α β : ℝ} (hαβ : α ≤ β) {Φ D1 D2 : ℝ → ℝ} {h h1 : ℝ → ℂ}
    (hΦ : ∀ x ∈ Icc α β, HasDerivAt Φ (D1 x) x) (hD1 : ∀ x ∈ Icc α β, HasDerivAt D1 (D2 x) x)
    (hne : ∀ x ∈ Icc α β, D1 x ≠ 0) (hh : ∀ x ∈ Icc α β, HasDerivAt h (h1 x) x)
    (hh1c : ContinuousOn h1 (Icc α β)) (hD2c : ContinuousOn D2 (Icc α β)) :
    ‖∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * h x‖ ≤
      ‖h β‖ / |D1 β| + ‖h α‖ / |D1 α| + ∫ x in α..β, ‖ibpG D1 D2 h h1 x‖ := by
  have hstep := ibp_step hαβ hΦ hD1 hne hh hh1c hD2c
  rw [hstep]
  have hD1c : ContinuousOn D1 (Icc α β) := fun x hx => (hD1 x hx).continuousAt.continuousWithinAt
  have hΦc : ContinuousOn Φ (Icc α β) := fun x hx => (hΦ x hx).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc α β) := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  have hgc := ibpG_continuousOn hD1c hD2c hne hhc hh1c
  have hexpc : ContinuousOn (fun x => Complex.exp (Complex.I * (Φ x : ℂ))) (Icc α β) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp_continuousOn hΦc
  have hint : ‖∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * ibpG D1 D2 h h1 x‖ ≤
      ∫ x in α..β, ‖ibpG D1 D2 h h1 x‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hαβ).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp [norm_mul, Complex.norm_exp_I_mul_ofReal]
  have hb : ∀ x : ℝ, ‖Complex.exp (Complex.I * (Φ x : ℂ)) * (h x / (Complex.I * (D1 x : ℂ)))‖ = ‖h x‖ / |D1 x| := by
    intro x
    simp [norm_mul, Complex.norm_exp_I_mul_ofReal, norm_div]
  calc _ ≤ ‖Complex.exp (Complex.I * (Φ β : ℂ)) * (h β / (Complex.I * (D1 β : ℂ))) -
        Complex.exp (Complex.I * (Φ α : ℂ)) * (h α / (Complex.I * (D1 α : ℂ)))‖ +
        ‖Complex.I * ∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * ibpG D1 D2 h h1 x‖ := norm_add_le _ _
    _ ≤ (‖h β‖ / |D1 β| + ‖h α‖ / |D1 α|) + ∫ x in α..β, ‖ibpG D1 D2 h h1 x‖ := by
        gcongr
        · refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [hb, hb]
        · rw [norm_mul, Complex.norm_I, one_mul]; exact hint
    _ = _ := by ring

/-- **Two integrations by parts, norm form**. -/
theorem ibp_norm_two {α β : ℝ} (hαβ : α ≤ β) {Φ D1 D2 D3 : ℝ → ℝ} {h h1 h2 : ℝ → ℂ}
    (hΦ : ∀ x ∈ Icc α β, HasDerivAt Φ (D1 x) x) (hD1 : ∀ x ∈ Icc α β, HasDerivAt D1 (D2 x) x)
    (hD2 : ∀ x ∈ Icc α β, HasDerivAt D2 (D3 x) x) (hne : ∀ x ∈ Icc α β, D1 x ≠ 0)
    (hh : ∀ x ∈ Icc α β, HasDerivAt h (h1 x) x) (hh1 : ∀ x ∈ Icc α β, HasDerivAt h1 (h2 x) x)
    (hh2c : ContinuousOn h2 (Icc α β)) (hD3c : ContinuousOn D3 (Icc α β)) :
    ‖∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * h x‖ ≤
      ‖h β‖ / |D1 β| + ‖h α‖ / |D1 α| + ‖ibpG D1 D2 h h1 β‖ / |D1 β| + ‖ibpG D1 D2 h h1 α‖ / |D1 α| +
        ∫ x in α..β, ‖ibpG D1 D2 (ibpG D1 D2 h h1) (ibpG1 D1 D2 D3 h h1 h2) x‖ := by
  have hD1c : ContinuousOn D1 (Icc α β) := fun x hx => (hD1 x hx).continuousAt.continuousWithinAt
  have hD2c : ContinuousOn D2 (Icc α β) := fun x hx => (hD2 x hx).continuousAt.continuousWithinAt
  have hh1c : ContinuousOn h1 (Icc α β) := fun x hx => (hh1 x hx).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc α β) := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  have hg : ∀ x ∈ Icc α β, HasDerivAt (ibpG D1 D2 h h1) (ibpG1 D1 D2 D3 h h1 h2 x) x := fun x hx =>
    hasDerivAt_ibpG (hD1 x hx) (hD2 x hx) (hne x hx) (hh x hx) (hh1 x hx)
  have hg1c := ibpG1_continuousOn hD1c hD2c hD3c hne hhc hh1c hh2c
  have e2 := ibp_norm_one hαβ hΦ hD1 hne hg hg1c hD2c
  have hstep := ibp_step hαβ hΦ hD1 hne hh hh1c hD2c
  have hgc := ibpG_continuousOn hD1c hD2c hne hhc hh1c
  have hb : ∀ x : ℝ, ‖Complex.exp (Complex.I * (Φ x : ℂ)) * (h x / (Complex.I * (D1 x : ℂ)))‖ = ‖h x‖ / |D1 x| := by
    intro x
    simp [norm_mul, Complex.norm_exp_I_mul_ofReal, norm_div]
  rw [hstep]
  calc _ ≤ ‖Complex.exp (Complex.I * (Φ β : ℂ)) * (h β / (Complex.I * (D1 β : ℂ))) -
        Complex.exp (Complex.I * (Φ α : ℂ)) * (h α / (Complex.I * (D1 α : ℂ)))‖ +
        ‖Complex.I * ∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * ibpG D1 D2 h h1 x‖ := norm_add_le _ _
    _ ≤ (‖h β‖ / |D1 β| + ‖h α‖ / |D1 α|) +
        (‖ibpG D1 D2 h h1 β‖ / |D1 β| + ‖ibpG D1 D2 h h1 α‖ / |D1 α| +
          ∫ x in α..β, ‖ibpG D1 D2 (ibpG D1 D2 h h1) (ibpG1 D1 D2 D3 h h1 h2) x‖) := by
        gcongr
        · refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [hb, hb]
        · rw [norm_mul, Complex.norm_I, one_mul]; exact e2
    _ = _ := by ring

lemma ibpG_norm_le {D1 D2 : ℝ → ℝ} {h h1 : ℝ → ℂ} {x b0 b1 p1 p2 : ℝ} (hb0 : ‖h x‖ ≤ b0) (hb1 : ‖h1 x‖ ≤ b1)
    (hp1 : 0 < p1) (hD1 : p1 ≤ |D1 x|) (hD2 : |D2 x| ≤ p2) :
    ‖ibpG D1 D2 h h1 x‖ ≤ b1 / p1 + b0 * p2 / p1 ^ 2 := by
  have hD1pos : 0 < |D1 x| := lt_of_lt_of_le hp1 hD1
  have hb0' : 0 ≤ b0 := (norm_nonneg _).trans hb0
  have hb1' : 0 ≤ b1 := (norm_nonneg _).trans hb1
  have hp2 : 0 ≤ p2 := (abs_nonneg _).trans hD2
  have t1 : ‖h1 x / (D1 x : ℂ)‖ ≤ b1 / p1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc ‖h1 x‖ / |D1 x| ≤ b1 / |D1 x| := div_le_div_of_nonneg_right hb1 hD1pos.le
      _ ≤ b1 / p1 := div_le_div_of_nonneg_left hb1' hp1 hD1
  have t2 : ‖h x * (D2 x : ℂ) / (D1 x : ℂ) ^ 2‖ ≤ b0 * p2 / p1 ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖h x‖ * |D2 x| / |D1 x| ^ 2 ≤ b0 * p2 / |D1 x| ^ 2 := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul hb0 hD2 (abs_nonneg _) hb0'
      _ ≤ b0 * p2 / p1 ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  unfold ibpG
  exact (norm_sub_le _ _).trans (add_le_add t1 t2)

lemma ibpG1_norm_le {D1 D2 D3 : ℝ → ℝ} {h h1 h2 : ℝ → ℂ} {x b0 b1 b2 p1 p2 p3 : ℝ} (hb0 : ‖h x‖ ≤ b0)
    (hb1 : ‖h1 x‖ ≤ b1) (hb2 : ‖h2 x‖ ≤ b2) (hp1 : 0 < p1) (hD1 : p1 ≤ |D1 x|) (hD2 : |D2 x| ≤ p2)
    (hD3 : |D3 x| ≤ p3) :
    ‖ibpG1 D1 D2 D3 h h1 h2 x‖ ≤ b2 / p1 + 2 * b1 * p2 / p1 ^ 2 + b0 * p3 / p1 ^ 2 + 2 * b0 * p2 ^ 2 / p1 ^ 3 := by
  have hD1pos : 0 < |D1 x| := lt_of_lt_of_le hp1 hD1
  have hb0' : 0 ≤ b0 := (norm_nonneg _).trans hb0
  have hb1' : 0 ≤ b1 := (norm_nonneg _).trans hb1
  have hb2' : 0 ≤ b2 := (norm_nonneg _).trans hb2
  have hp2 : 0 ≤ p2 := (abs_nonneg _).trans hD2
  have hp3 : 0 ≤ p3 := (abs_nonneg _).trans hD3
  have e1 : b2 / |D1 x| ≤ b2 / p1 := div_le_div_of_nonneg_left hb2' hp1 hD1
  have e2 : 2 * b1 * p2 / |D1 x| ^ 2 ≤ 2 * b1 * p2 / p1 ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  have e3 : b0 * p3 / |D1 x| ^ 2 ≤ b0 * p3 / p1 ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  have e4 : 2 * b0 * p2 ^ 2 / |D1 x| ^ 3 ≤ 2 * b0 * p2 ^ 2 / p1 ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  have t1 : ‖h2 x / (D1 x : ℂ)‖ ≤ b2 / |D1 x| := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]; gcongr
  have t2 : ‖2 * h1 x * (D2 x : ℂ) / (D1 x : ℂ) ^ 2‖ ≤ 2 * b1 * p2 / |D1 x| ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    simp only [Complex.norm_ofNat]
    gcongr
  have t3 : ‖h x * (D3 x : ℂ) / (D1 x : ℂ) ^ 2‖ ≤ b0 * p3 / |D1 x| ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have t4 : ‖2 * h x * (D2 x : ℂ) ^ 2 / (D1 x : ℂ) ^ 3‖ ≤ 2 * b0 * p2 ^ 2 / |D1 x| ^ 3 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    simp only [Complex.norm_ofNat]
    have : |D2 x| ^ 2 ≤ p2 ^ 2 := by gcongr
    gcongr
  unfold ibpG1
  calc _ ≤ ‖h2 x / (D1 x : ℂ)‖ + ‖2 * h1 x * (D2 x : ℂ) / (D1 x : ℂ) ^ 2‖ + ‖h x * (D3 x : ℂ) / (D1 x : ℂ) ^ 2‖ +
        ‖2 * h x * (D2 x : ℂ) ^ 2 / (D1 x : ℂ) ^ 3‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact (norm_sub_le _ _)
    _ ≤ _ := by linarith

/-- **One integration by parts with majorants.** -/
theorem ibp_one_bound {α β : ℝ} (hαβ : α ≤ β) {Φ D1 D2 : ℝ → ℝ} {h h1 : ℝ → ℂ} {B0 B1 P1 P2 : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc α β, HasDerivAt Φ (D1 x) x) (hD1 : ∀ x ∈ Icc α β, HasDerivAt D1 (D2 x) x)
    (hne : ∀ x ∈ Icc α β, D1 x ≠ 0) (hh : ∀ x ∈ Icc α β, HasDerivAt h (h1 x) x)
    (hh1c : ContinuousOn h1 (Icc α β)) (hD2c : ContinuousOn D2 (Icc α β))
    (hB0 : ∀ x ∈ Icc α β, ‖h x‖ ≤ B0 x) (hB1 : ∀ x ∈ Icc α β, ‖h1 x‖ ≤ B1 x)
    (hP1 : ∀ x ∈ Icc α β, 0 < P1 x ∧ P1 x ≤ |D1 x|) (hP2 : ∀ x ∈ Icc α β, |D2 x| ≤ P2 x)
    (hint : IntervalIntegrable (fun x => B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) volume α β) :
    ‖∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * h x‖ ≤
      B0 β / P1 β + B0 α / P1 α + ∫ x in α..β, (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) := by
  have hmain := ibp_norm_one hαβ hΦ hD1 hne hh hh1c hD2c
  have hD1c : ContinuousOn D1 (Icc α β) := fun x hx => (hD1 x hx).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc α β) := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  have hgc := ibpG_continuousOn hD1c hD2c hne hhc hh1c
  have hbd : ∀ x ∈ Icc α β, ‖h x‖ / |D1 x| ≤ B0 x / P1 x := fun x hx =>
    (div_le_div_of_nonneg_right (hB0 x hx) (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left ((norm_nonneg _).trans (hB0 x hx)) (hP1 x hx).1 (hP1 x hx).2)
  have hint2 : ∫ x in α..β, ‖ibpG D1 D2 h h1 x‖ ≤ ∫ x in α..β, (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) := by
    refine intervalIntegral.integral_mono_on hαβ (hgc.norm.intervalIntegrable_of_Icc hαβ) hint fun x hx => ?_
    exact ibpG_norm_le (hB0 x hx) (hB1 x hx) (hP1 x hx).1 (hP1 x hx).2 (hP2 x hx)
  have := hbd β (right_mem_Icc.mpr hαβ)
  have := hbd α (left_mem_Icc.mpr hαβ)
  linarith

/-- **Two integrations by parts with majorants.** -/
theorem ibp_two_bound {α β : ℝ} (hαβ : α ≤ β) {Φ D1 D2 D3 : ℝ → ℝ} {h h1 h2 : ℝ → ℂ} {B0 B1 B2 P1 P2 P3 : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc α β, HasDerivAt Φ (D1 x) x) (hD1 : ∀ x ∈ Icc α β, HasDerivAt D1 (D2 x) x)
    (hD2 : ∀ x ∈ Icc α β, HasDerivAt D2 (D3 x) x) (hne : ∀ x ∈ Icc α β, D1 x ≠ 0)
    (hh : ∀ x ∈ Icc α β, HasDerivAt h (h1 x) x) (hh1 : ∀ x ∈ Icc α β, HasDerivAt h1 (h2 x) x)
    (hh2c : ContinuousOn h2 (Icc α β)) (hD3c : ContinuousOn D3 (Icc α β))
    (hB0 : ∀ x ∈ Icc α β, ‖h x‖ ≤ B0 x) (hB1 : ∀ x ∈ Icc α β, ‖h1 x‖ ≤ B1 x) (hB2 : ∀ x ∈ Icc α β, ‖h2 x‖ ≤ B2 x)
    (hP1 : ∀ x ∈ Icc α β, 0 < P1 x ∧ P1 x ≤ |D1 x|) (hP2 : ∀ x ∈ Icc α β, |D2 x| ≤ P2 x)
    (hP3 : ∀ x ∈ Icc α β, |D3 x| ≤ P3 x)
    (hint : IntervalIntegrable (fun x => (B2 x / P1 x + 2 * B1 x * P2 x / P1 x ^ 2 + B0 x * P3 x / P1 x ^ 2 +
        2 * B0 x * P2 x ^ 2 / P1 x ^ 3) / P1 x +
      (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) * P2 x / P1 x ^ 2) volume α β) :
    ‖∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * h x‖ ≤
      B0 β / P1 β + B0 α / P1 α + (B1 β / P1 β + B0 β * P2 β / P1 β ^ 2) / P1 β +
        (B1 α / P1 α + B0 α * P2 α / P1 α ^ 2) / P1 α +
      ∫ x in α..β, ((B2 x / P1 x + 2 * B1 x * P2 x / P1 x ^ 2 + B0 x * P3 x / P1 x ^ 2 +
        2 * B0 x * P2 x ^ 2 / P1 x ^ 3) / P1 x +
        (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) * P2 x / P1 x ^ 2) := by
  have hmain := ibp_norm_two hαβ hΦ hD1 hD2 hne hh hh1 hh2c hD3c
  have hD1c : ContinuousOn D1 (Icc α β) := fun x hx => (hD1 x hx).continuousAt.continuousWithinAt
  have hD2c : ContinuousOn D2 (Icc α β) := fun x hx => (hD2 x hx).continuousAt.continuousWithinAt
  have hh1c : ContinuousOn h1 (Icc α β) := fun x hx => (hh1 x hx).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc α β) := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  have hgc := ibpG_continuousOn hD1c hD2c hne hhc hh1c
  have hg1c := ibpG1_continuousOn hD1c hD2c hD3c hne hhc hh1c hh2c
  have hg2c := ibpG_continuousOn hD1c hD2c hne hgc hg1c
  have hG0 : ∀ x ∈ Icc α β, ‖ibpG D1 D2 h h1 x‖ ≤ B1 x / P1 x + B0 x * P2 x / P1 x ^ 2 := fun x hx =>
    ibpG_norm_le (hB0 x hx) (hB1 x hx) (hP1 x hx).1 (hP1 x hx).2 (hP2 x hx)
  have hG1 : ∀ x ∈ Icc α β, ‖ibpG1 D1 D2 D3 h h1 h2 x‖ ≤ B2 x / P1 x + 2 * B1 x * P2 x / P1 x ^ 2 +
      B0 x * P3 x / P1 x ^ 2 + 2 * B0 x * P2 x ^ 2 / P1 x ^ 3 := fun x hx =>
    ibpG1_norm_le (hB0 x hx) (hB1 x hx) (hB2 x hx) (hP1 x hx).1 (hP1 x hx).2 (hP2 x hx) (hP3 x hx)
  have hint2 : ∫ x in α..β, ‖ibpG D1 D2 (ibpG D1 D2 h h1) (ibpG1 D1 D2 D3 h h1 h2) x‖ ≤
      ∫ x in α..β, ((B2 x / P1 x + 2 * B1 x * P2 x / P1 x ^ 2 + B0 x * P3 x / P1 x ^ 2 +
        2 * B0 x * P2 x ^ 2 / P1 x ^ 3) / P1 x +
        (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) * P2 x / P1 x ^ 2) := by
    refine intervalIntegral.integral_mono_on hαβ (hg2c.norm.intervalIntegrable_of_Icc hαβ) hint fun x hx => ?_
    exact ibpG_norm_le (hG0 x hx) (hG1 x hx) (hP1 x hx).1 (hP1 x hx).2 (hP2 x hx)
  have hbd : ∀ x ∈ Icc α β, ‖h x‖ / |D1 x| ≤ B0 x / P1 x := fun x hx =>
    (div_le_div_of_nonneg_right (hB0 x hx) (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left ((norm_nonneg _).trans (hB0 x hx)) (hP1 x hx).1 (hP1 x hx).2)
  have hbd' : ∀ x ∈ Icc α β, ‖ibpG D1 D2 h h1 x‖ / |D1 x| ≤
      (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) / P1 x := fun x hx =>
    (div_le_div_of_nonneg_right (hG0 x hx) (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left ((norm_nonneg _).trans (hG0 x hx)) (hP1 x hx).1 (hP1 x hx).2)
  have e1 := hbd β (right_mem_Icc.mpr hαβ)
  have e2 := hbd α (left_mem_Icc.mpr hαβ)
  have e3 := hbd' β (right_mem_Icc.mpr hαβ)
  have e4 := hbd' α (left_mem_Icc.mpr hαβ)
  linarith

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.ibp_one_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ibp_one_bound

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.ibp_two_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ibp_two_bound

end FormalResearch.SignUncertainty.FctUnscaledCusp
