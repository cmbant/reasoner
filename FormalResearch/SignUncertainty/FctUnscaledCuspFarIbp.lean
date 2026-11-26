/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspSetup

/-!
# `fct:unscaled-cusp`, regime `u ≥ 1`: two integrations by parts with a free dominating function (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, third estimate.

`ibp_two_bound` (`FctUnscaledCuspIbp`) bounds the remaining integral by the integral of the majorant expression `ibpF`
itself.  In the regime `u ≥ 1` the lower bound `P₁` of `|Φ'|` jumps (gap `u/2` before the cut `t_*`, a fixed constant
afterwards), and the majorant is dominated, pointwise, by a smooth function `Ψ` that is easy to integrate.
`ibp_two_bound_psi` and `cusp_ibp_two_psi` are `ibp_two_bound` and `cusp_ibp_two` with the integral of `ibpF` replaced by
the integral of any integrable `Ψ ≥ ibpF`; the endpoint terms are those of `ibp_two_bound`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-- The majorant expression of two integrations by parts. -/
noncomputable def ibpF (b0 b1 b2 p1 p2 p3 : ℝ) : ℝ :=
  (b2 / p1 + 2 * b1 * p2 / p1 ^ 2 + b0 * p3 / p1 ^ 2 + 2 * b0 * p2 ^ 2 / p1 ^ 3) / p1 +
    (b1 / p1 + b0 * p2 / p1 ^ 2) * p2 / p1 ^ 2

/-- The endpoint term of two integrations by parts. -/
noncomputable def ibpEnd (b0 b1 p1 p2 : ℝ) : ℝ := b0 / p1 + (b1 / p1 + b0 * p2 / p1 ^ 2) / p1

/-- **Two integrations by parts with a free dominating function.** -/
theorem ibp_two_bound_psi {α β : ℝ} (hαβ : α ≤ β) {Φ D1 D2 D3 : ℝ → ℝ} {h h1 h2 : ℝ → ℂ}
    {B0 B1 B2 P1 P2 P3 Ψ : ℝ → ℝ}
    (hΦ : ∀ x ∈ Icc α β, HasDerivAt Φ (D1 x) x) (hD1 : ∀ x ∈ Icc α β, HasDerivAt D1 (D2 x) x)
    (hD2 : ∀ x ∈ Icc α β, HasDerivAt D2 (D3 x) x) (hne : ∀ x ∈ Icc α β, D1 x ≠ 0)
    (hh : ∀ x ∈ Icc α β, HasDerivAt h (h1 x) x) (hh1 : ∀ x ∈ Icc α β, HasDerivAt h1 (h2 x) x)
    (hh2c : ContinuousOn h2 (Icc α β)) (hD3c : ContinuousOn D3 (Icc α β))
    (hB0 : ∀ x ∈ Icc α β, ‖h x‖ ≤ B0 x) (hB1 : ∀ x ∈ Icc α β, ‖h1 x‖ ≤ B1 x) (hB2 : ∀ x ∈ Icc α β, ‖h2 x‖ ≤ B2 x)
    (hP1 : ∀ x ∈ Icc α β, 0 < P1 x ∧ P1 x ≤ |D1 x|) (hP2 : ∀ x ∈ Icc α β, |D2 x| ≤ P2 x)
    (hP3 : ∀ x ∈ Icc α β, |D3 x| ≤ P3 x)
    (hΨ : ∀ x ∈ Icc α β, ibpF (B0 x) (B1 x) (B2 x) (P1 x) (P2 x) (P3 x) ≤ Ψ x)
    (hint : IntervalIntegrable Ψ volume α β) :
    ‖∫ x in α..β, Complex.exp (Complex.I * (Φ x : ℂ)) * h x‖ ≤
      ibpEnd (B0 β) (B1 β) (P1 β) (P2 β) + ibpEnd (B0 α) (B1 α) (P1 α) (P2 α) + ∫ x in α..β, Ψ x := by
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
  have hint2 : ∫ x in α..β, ‖ibpG D1 D2 (ibpG D1 D2 h h1) (ibpG1 D1 D2 D3 h h1 h2) x‖ ≤ ∫ x in α..β, Ψ x := by
    refine intervalIntegral.integral_mono_on hαβ (hg2c.norm.intervalIntegrable_of_Icc hαβ) hint fun x hx => ?_
    refine (ibpG_norm_le (hG0 x hx) (hG1 x hx) (hP1 x hx).1 (hP1 x hx).2 (hP2 x hx)).trans ?_
    exact hΨ x hx
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
  unfold ibpEnd
  linarith

section IbpCuspPsi

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ} {η Ca M : ℝ} {a : ℝ → ℂ}

/-- Two integrations by parts for `∫_α^β e^{icφ(x;u)} a(x)` with a free dominating function `Ψ`. -/
theorem cusp_ibp_two_psi (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) {c u α β : ℝ} (hc : 0 < c)
    (hα : 0 < α) (hαβ : α ≤ β) {B0 B1 B2 P1 P2 P3 Ψ : ℝ → ℝ}
    (hB0 : ∀ x ∈ Icc α β, ‖a x‖ ≤ B0 x) (hB1 : ∀ x ∈ Icc α β, ‖deriv a x‖ ≤ B1 x)
    (hB2 : ∀ x ∈ Icc α β, ‖deriv (deriv a) x‖ ≤ B2 x)
    (hP1 : ∀ x ∈ Icc α β, 0 < P1 x ∧ P1 x ≤ c * |u - 𝔪 x|) (hP2 : ∀ x ∈ Icc α β, c * deriv 𝔪 x ≤ P2 x)
    (hP3 : ∀ x ∈ Icc α β, c * C₂ ≤ P3 x)
    (hΨ : ∀ x ∈ Icc α β, ibpF (B0 x) (B1 x) (B2 x) (P1 x) (P2 x) (P3 x) ≤ Ψ x)
    (hint : IntervalIntegrable Ψ volume α β) :
    ‖∫ x in α..β, Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      ibpEnd (B0 β) (B1 β) (P1 β) (P2 β) + ibpEnd (B0 α) (B1 α) (P1 α) (P2 α) + ∫ x in α..β, Ψ x := by
  have hpos : ∀ x ∈ Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα hx.1
  have hD1c : ∀ x ∈ Icc α β, |c * (u - 𝔪 x)| = c * |u - 𝔪 x| := fun x _ => by
    rw [abs_mul, abs_of_pos hc]
  have hD1d : ∀ x, HasDerivAt (fun x => c * (u - 𝔪 x)) (-c * deriv 𝔪 x) x := fun x =>
    (((hasDerivAt_const x u).sub (h.hasDerivAt x)).const_mul c).congr_deriv (by ring)
  have hD2d : ∀ x, HasDerivAt (fun x => -c * deriv 𝔪 x) (-c * iteratedDeriv 2 𝔪 x) x := fun x =>
    ((h.hasDerivAt₂ x).const_mul (-c))
  refine ibp_two_bound_psi hαβ (Φ := fun x => c * cuspPhase 𝔪 u x) (D1 := fun x => c * (u - 𝔪 x))
    (D2 := fun x => -c * deriv 𝔪 x) (D3 := fun x => -c * iteratedDeriv 2 𝔪 x) (h := a) (h1 := deriv a)
    (h2 := deriv (deriv a)) (B0 := B0) (B1 := B1) (B2 := B2) (P1 := P1) (P2 := P2) (P3 := P3) (Ψ := Ψ)
    (fun x _ => (h.hasDerivAt_phase u x).const_mul c) (fun x _ => hD1d x) (fun x _ => hD2d x) ?_
    (fun x hx => ha.hasDerivAt_a (hpos x hx)) (fun x hx => ha.hasDerivAt_a1 (hpos x hx))
    (ha.continuousOn_a2.mono fun x hx => hpos x hx)
    (by exact (continuous_const.mul h.continuous_deriv₂).continuousOn) hB0 hB1 hB2 ?_ ?_ ?_ hΨ hint
  · intro x hx
    have := hP1 x hx
    have h2 : 0 < c * |u - 𝔪 x| := lt_of_lt_of_le this.1 this.2
    have : u - 𝔪 x ≠ 0 := fun h0 => by simp [h0] at h2
    exact mul_ne_zero hc.ne' this
  · intro x hx
    refine ⟨(hP1 x hx).1, ?_⟩
    rw [hD1c x hx]; exact (hP1 x hx).2
  · intro x hx
    have := h.deriv_nonneg (hpos x hx)
    rw [show -c * deriv 𝔪 x = -(c * deriv 𝔪 x) by ring, abs_neg, abs_of_pos (mul_pos hc this)]
    exact hP2 x hx
  · intro x hx
    rw [show -c * iteratedDeriv 2 𝔪 x = -(c * iteratedDeriv 2 𝔪 x) by ring, abs_neg, abs_mul, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left (h.deriv2_bound x) hc.le).trans (hP3 x hx)

end IbpCuspPsi

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cusp_ibp_two_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cusp_ibp_two_psi

end FormalResearch.SignUncertainty.FctUnscaledCusp
