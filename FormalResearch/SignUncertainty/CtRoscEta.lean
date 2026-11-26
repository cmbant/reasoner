module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscUpper
public import FormalResearch.SignUncertainty.CtDyadicEta

/-!
# The upper half of the circle integral `η(R)` (`(ct:rosc)`, error term)

`ctEta c₁ ε c f R = ∫_0^{2π} R (‖Ψ̃(Re^{iθ})‖ + ‖f_c(Re^{iθ})‖)/e(Re^{iθ}) dθ` is a Bochner integral, so `∫_0^π ≤ ∫_0^{2π}` needs integrability on
the whole circle (otherwise the integral is `0`).  `airyEnv` is not continuous on `ℂ` but its restriction to the circle is: on the upper half
circle `1/e = ‖airyUpE‖`, on the lower one `e(ū) = e(u)`.  `ctEta_ge_half`: for `Ψ̃, G` continuous on the circle `|u| = R`,
`∫_0^π R ‖G‖ ‖airyUpE‖ dθ ≤ ∫_0^{2π} R (‖Ψ̃‖ + ‖G‖)/e dθ`.  Proved.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

lemma circleMap_two_pi_sub (R s : ℝ) :
    circleMap 0 R (2 * π - s) = (starRingEnd ℂ) (circleMap 0 R s) := by
  simp only [circleMap, zero_add, map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show ((2 * π - s : ℝ) : ℂ) * I = -((s : ℂ) * I) + 2 * π * I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  congr 2; ring

lemma ctEta_ge_half {R : ℝ} (hR : 0 < R) {Ψ G : ℂ → ℂ} (hΨ : ContinuousOn Ψ (sphere 0 R))
    (hG : ContinuousOn G (sphere 0 R)) :
    (∫ θ in (0 : ℝ)..π, R * ‖G (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) ≤
      ∫ θ in (0 : ℝ)..(2 * π),
        R * (‖Ψ (circleMap 0 R θ)‖ + ‖G (circleMap 0 R θ)‖) / airyEnv (circleMap 0 R θ) := by
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwc : Continuous w := continuous_circleMap 0 R
  have hws : ∀ θ, w θ ∈ sphere (0 : ℂ) R := fun θ => by simp [hw, abs_of_pos hR]
  have hwim : ∀ θ ∈ Icc (0 : ℝ) π, 0 ≤ (w θ).im := fun θ hθ => by
    rw [hw, cftDef_im_circleMap]
    exact mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
  have hEc : ContinuousOn (fun θ => airyUpE (w θ)) (Icc 0 π) :=
    continuousOn_airyUpE.comp hwc.continuousOn (fun θ hθ => hwim θ hθ)
  have hΨc : Continuous fun θ => ‖Ψ (w θ)‖ := (hΨ.comp_continuous hwc hws).norm
  have hGc : Continuous fun θ => ‖G (w θ)‖ := (hG.comp_continuous hwc hws).norm
  set η : ℝ → ℝ := fun θ => R * (‖Ψ (w θ)‖ + ‖G (w θ)‖) / airyEnv (w θ) with hη
  -- the two halves
  have h1 : ContinuousOn η (Icc 0 π) := by
    have : ContinuousOn (fun θ => R * (‖Ψ (w θ)‖ + ‖G (w θ)‖) * ‖airyUpE (w θ)‖) (Icc 0 π) :=
      (continuousOn_const.mul (hΨc.add hGc).continuousOn).mul hEc.norm
    refine this.congr (fun θ hθ => ?_)
    simp only [hη]
    rw [norm_airyUpE (hwim θ hθ), div_eq_mul_inv]
  have h2 : ContinuousOn η (Icc π (2 * π)) := by
    have hrefl : ContinuousOn (fun θ : ℝ => 2 * π - θ) (Icc π (2 * π)) := by fun_prop
    have hmaps : MapsTo (fun θ : ℝ => 2 * π - θ) (Icc π (2 * π)) (Icc 0 π) := fun θ hθ =>
      ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hE2 : ContinuousOn (fun θ => ‖airyUpE (w (2 * π - θ))‖) (Icc π (2 * π)) :=
      (hEc.comp hrefl hmaps).norm
    have : ContinuousOn (fun θ => R * (‖Ψ (w θ)‖ + ‖G (w θ)‖) * ‖airyUpE (w (2 * π - θ))‖) (Icc π (2 * π)) :=
      (continuousOn_const.mul (hΨc.add hGc).continuousOn).mul hE2
    refine this.congr (fun θ hθ => ?_)
    simp only [hη]
    have hs : 2 * π - θ ∈ Icc (0 : ℝ) π := hmaps hθ
    have hconj : w θ = (starRingEnd ℂ) (w (2 * π - θ)) := by
      rw [hw, circleMap_two_pi_sub, Complex.conj_conj]
    have hE : airyEnv (w θ) = airyEnv (w (2 * π - θ)) := by
      conv_lhs => rw [hconj]
      exact airyEnv_conj _
    rw [hE, norm_airyUpE (hwim _ hs), div_eq_mul_inv]
  have hη0 : ∀ θ, 0 ≤ η θ := fun θ => by
    simp only [hη]
    exact div_nonneg (mul_nonneg hR.le (add_nonneg (norm_nonneg _) (norm_nonneg _))) (airyEnv_pos _).le
  have hi1 : IntervalIntegrable η volume 0 π := h1.intervalIntegrable_of_Icc Real.pi_pos.le
  have hi2 : IntervalIntegrable η volume π (2 * π) := h2.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hnn : 0 ≤ ∫ θ in π..(2 * π), η θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => hη0 θ)
  have hmono : (∫ θ in (0 : ℝ)..π, R * ‖G (w θ)‖ * ‖airyUpE (w θ)‖) ≤ ∫ θ in (0 : ℝ)..π, η θ := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ hi1 (fun θ hθ => ?_)
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le Real.pi_pos.le]
      exact (continuousOn_const.mul hGc.continuousOn).mul hEc.norm
    · have := h1.continuousWithinAt hθ
      have e : η θ = R * (‖Ψ (w θ)‖ + ‖G (w θ)‖) * ‖airyUpE (w θ)‖ := by
        simp only [hη]
        rw [norm_airyUpE (hwim θ hθ), div_eq_mul_inv]
      rw [e]
      have : 0 ≤ ‖airyUpE (w θ)‖ := norm_nonneg _
      nlinarith [mul_nonneg hR.le (norm_nonneg (Ψ (w θ))), mul_nonneg (mul_nonneg hR.le (norm_nonneg (Ψ (w θ)))) this]
  show _ ≤ ∫ θ in (0 : ℝ)..(2 * π), η θ
  linarith

/-- info: 'FormalResearch.SignUncertainty.ctEta_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctEta_ge_half

end FormalResearch.SignUncertainty
