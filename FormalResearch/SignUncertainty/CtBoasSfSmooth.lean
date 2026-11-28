/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasSigmaLip
public import FormalResearch.SignUncertainty.CtChartPsiAnalytic
public import FormalResearch.SignUncertainty.CtDyadicChartReal

/-!
# `C^{1,1}` (Lipschitz-derivative) estimates for `boasSf`, `ctYRD`, and `ctPsi` (`ct:boas` Step 3)

1. `hasDerivAt_one_sub_boasSf`, `sfNegDeriv_lip`: `1 - sFar c (c * exp L / π²)` has derivative `sfNegDeriv c`
   bounded by `O(1 + log c)` and `O((1 + log c)^3)`-Lipschitz on `(-∞, log(π² log c) + 3]`.
2. `ctYRD_lip`: `|ctYRD w₁ - ctYRD w₂| ≤ 7000 |w₁ - w₂|` on `[-5e-4, 5e-4]` via Cauchy estimate.
3. `ctPsi_deriv_lip`: `deriv (ctPsi ε)` is Lipschitz on `(-ρ₀, 0)` near `0⁻` via `ctPsiAnalytic` + Cauchy estimate.

Class: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.SignUncertainty.CtCfu

/-! ### `HasDerivAt` and `C^{1,1}` bound for `1 - sFar c (c * exp L / π²)` -/

/-- Derivative of `L ↦ 1 - sFar c (c * exp L / π²)`. -/
noncomputable def sfNegDeriv (c L : ℝ) : ℝ :=
  -(c * (Real.exp L / π ^ 2) * gaussK (farW c) (c * (Real.exp L / π ^ 2) - farD c))

lemma hasDerivAt_sFar {c : ℝ} (hc : 1 < c) (Δ : ℝ) :
    HasDerivAt (sFar c) (gaussK (farW c) (Δ - farD c)) Δ := by
  have hW : 0 < farW c := by unfold farW; linarith
  set a : ℝ := Δ - farD c - 1 with ha
  have hint : Integrable (gaussK (farW c)) := integrable_gaussK hW
  have hcG : Continuous (gaussK (farW c)) := continuous_gaussK (farW c)
  have hev : sFar c =ᶠ[𝓝 Δ] fun x => (∫ y in Iio a, gaussK (farW c) y) +
      ∫ y in a..(x - farD c), gaussK (farW c) y := by
    filter_upwards [Metric.ball_mem_nhds Δ (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have hlt : a < x - farD c := by linarith [hx.1]
    have hU : Iio (x - farD c) = Iio a ∪ Ico a (x - farD c) := by
      ext y; simp only [Set.mem_Iio, Set.mem_union, Set.mem_Ico]
      exact ⟨fun h => (lt_or_ge y a).imp id (fun h1 => ⟨h1, h⟩),
        fun h => h.elim (fun h1 => h1.trans hlt) And.right⟩
    have hdisj : Disjoint (Iio a) (Ico a (x - farD c)) :=
      Set.disjoint_left.2 fun _ h1 h2 => not_lt_of_ge h2.1 h1
    rw [sFar_eq_Iio, hU, setIntegral_union hdisj measurableSet_Ico hint.integrableOn hint.integrableOn,
      integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le hlt.le]
  have hid := intervalIntegral.integral_hasDerivAt_right (f := gaussK (farW c))
    (hcG.intervalIntegrable a (Δ - farD c))
    (hcG.stronglyMeasurableAtFilter volume (𝓝 (Δ - farD c))) hcG.continuousAt
  have h1 : HasDerivAt (fun x : ℝ => x - farD c) 1 Δ := (hasDerivAt_id Δ).sub_const _
  have hcomp : HasDerivAt (fun x => ∫ y in a..(x - farD c), gaussK (farW c) y)
      (gaussK (farW c) (Δ - farD c)) Δ := by
    have hraw := (hid.comp Δ h1).congr_deriv (mul_one _)
    exact hraw
  have hsum : HasDerivAt (fun x => (∫ y in Iio a, gaussK (farW c) y) +
      ∫ y in a..(x - farD c), gaussK (farW c) y) (gaussK (farW c) (Δ - farD c)) Δ :=
    hcomp.const_add _
  exact hsum.congr_of_eventuallyEq hev

lemma hasDerivAt_one_sub_boasSf {c : ℝ} (hc : 1 < c) (L : ℝ) :
    HasDerivAt (fun x => 1 - sFar c (c * (Real.exp x / π ^ 2))) (sfNegDeriv c L) L := by
  have hΔ : HasDerivAt (fun x => c * (Real.exp x / π ^ 2)) (c * (Real.exp L / π ^ 2)) L :=
    ((Real.hasDerivAt_exp L).div_const _).const_mul c
  have hcomp := (hasDerivAt_sFar hc (c * (Real.exp L / π ^ 2))).comp L hΔ
  exact (hcomp.const_sub 1).congr_deriv (by unfold sfNegDeriv; ring)

lemma gaussK_hasDerivAt {W : ℝ} (hW : 0 < W) (y : ℝ) :
    HasDerivAt (gaussK W) (-(y / W ^ 2) * gaussK W y) y := by
  have hd : HasDerivAt (fun t : ℝ => -(1 / (2 * W ^ 2)) * t ^ 2) (-(1 / (2 * W ^ 2)) * (2 * y)) y := by
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    exact h2.const_mul (-(1 / (2 * W ^ 2)))
  have h2 := (hd.exp).div_const (√(2 * π) * W)
  rw [show (fun t : ℝ => Real.exp (-(1 / (2 * W ^ 2)) * t ^ 2) / (√(2 * π) * W)) = gaussK W from
    funext fun t => by unfold gaussK; ring_nf] at h2
  refine h2.congr_deriv ?_
  unfold gaussK
  have hW0 : W ≠ 0 := hW.ne'
  field_simp

lemma sfNegDeriv_bounds {c : ℝ} (hc : 3 ≤ c) {L : ℝ} (hL : L ≤ Real.log (π ^ 2 * Real.log c) + 3) :
    |sfNegDeriv c L| ≤ 85 * (1 + Real.log c) ∧
    |deriv (sfNegDeriv c) L| ≤ 600000 * (1 + Real.log c) ^ 3 := by
  have hc1 : 1 < c := by linarith
  have hc0 : 0 < c := by linarith
  have hW : 0 < farW c := by unfold farW; linarith
  have hlogc : 1 ≤ Real.log c := by
    rw [Real.le_log_iff_exp_le hc0]; linarith [Real.exp_one_lt_d9]
  have hpi : 0 < π ^ 2 := by positivity
  set Δ : ℝ := c * (Real.exp L / π ^ 2) with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have he3 : Real.exp 3 ≤ 21 := by
    have h := Real.exp_one_lt_d9
    have heq3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      have := (Real.exp_nat_mul 1 3).symm
      simp [this]
    rw [heq3]
    calc Real.exp 1 ^ 3 ≤ (2.72 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
      _ ≤ 21 := by norm_num
  have hΔ_le : Δ ≤ Real.exp 3 * (c * Real.log c) := by
    have h1 : Real.exp L ≤ Real.exp (Real.log (π ^ 2 * Real.log c) + 3) := Real.exp_le_exp.2 hL
    rw [Real.exp_add, Real.exp_log (by positivity)] at h1
    rw [hΔ, show c * (Real.exp L / π ^ 2) = Real.exp L * c / π ^ 2 by ring, div_le_iff₀ hpi]
    calc Real.exp L * c ≤ (π ^ 2 * Real.log c * Real.exp 3) * c :=
          mul_le_mul_of_nonneg_right h1 hc0.le
      _ = Real.exp 3 * (c * Real.log c) * π ^ 2 := by ring
  have hΔ21 : Δ ≤ 21 * (c * Real.log c) :=
    hΔ_le.trans (mul_le_mul_of_nonneg_right he3 (mul_nonneg hc0.le (by linarith)))
  have hsqrt2pi : 2 < √(2 * π) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith [Real.pi_gt_three]
  have hG_bd : gaussK (farW c) (Δ - farD c) ≤ 4 / c := by
    unfold gaussK
    have hnum : Real.exp (-(1 / (2 * farW c ^ 2)) * (Δ - farD c) ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (sq_nonneg _))
    have hden : c / 2 ≤ √(2 * π) * farW c := by unfold farW; nlinarith [hsqrt2pi]
    calc Real.exp (-(1 / (2 * farW c ^ 2)) * (Δ - farD c) ^ 2) / (√(2 * π) * farW c)
        ≤ 1 / (√(2 * π) * farW c) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 1 / (c / 2) := div_le_div_of_nonneg_left zero_le_one (div_pos hc0 (by norm_num)) hden
      _ = 2 / c := by ring
      _ ≤ 4 / c := div_le_div_of_nonneg_right (by norm_num) hc0.le
  have hG0 : 0 ≤ gaussK (farW c) (Δ - farD c) := gaussK_nonneg' _ _ hW
  have h84 : Δ * gaussK (farW c) (Δ - farD c) ≤ 84 * Real.log c := by
    calc Δ * gaussK (farW c) (Δ - farD c) ≤ (21 * (c * Real.log c)) * (4 / c) :=
          mul_le_mul hΔ21 hG_bd hG0 (by positivity)
      _ = 84 * Real.log c := by field_simp; norm_num
  refine ⟨?_, ?_⟩
  · unfold sfNegDeriv
    rw [abs_neg, abs_mul, abs_of_pos hΔ0, abs_of_nonneg hG0]
    linarith
  · have hΔd : HasDerivAt (fun x => c * (Real.exp x / π ^ 2)) Δ L :=
      ((Real.hasDerivAt_exp L).div_const _).const_mul c
    have hGd_aux := (gaussK_hasDerivAt hW (Δ - farD c)).comp L (hΔd.sub_const (farD c))
    have hGd : HasDerivAt (fun x => gaussK (farW c) (c * (Real.exp x / π ^ 2) - farD c))
        ((-( (Δ - farD c) / farW c ^ 2) * gaussK (farW c) (Δ - farD c)) * Δ) L := by
      simpa [Function.comp_def, ← hΔ] using hGd_aux
    have hfull : HasDerivAt (sfNegDeriv c)
        (-(Δ * gaussK (farW c) (Δ - farD c) * (1 - Δ * (Δ - farD c) / farW c ^ 2))) L := by
      have hprod := (hΔd.mul hGd).neg
      change HasDerivAt (sfNegDeriv c) _ L at hprod
      exact hprod.congr_deriv (by ring)
    rw [hfull.deriv, abs_neg, abs_mul, abs_mul, abs_of_pos hΔ0, abs_of_nonneg hG0]
    have hsub_le : |Δ - farD c| ≤ 21 * (c * Real.log c) := by
      have hD_le : farD c = c * Real.log c := rfl
      rw [hD_le, abs_le]
      constructor <;> nlinarith [mul_pos hc0 (by linarith : 0 < Real.log c)]
    have hfac : |1 - Δ * (Δ - farD c) / farW c ^ 2| ≤ 1 + 16 * (21 * Real.log c) ^ 2 := by
      have hW2 : farW c ^ 2 = c ^ 2 / 16 := by unfold farW; ring
      have hterm : |Δ * (Δ - farD c) / farW c ^ 2| ≤ 16 * (21 * Real.log c) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos hΔ0, hW2, abs_of_pos (by positivity : 0 < c ^ 2 / 16)]
        have h1 : Δ * |Δ - farD c| ≤ (21 * (c * Real.log c)) ^ 2 := by
          rw [sq]
          exact mul_le_mul hΔ21 hsub_le (abs_nonneg _) (by positivity)
        calc Δ * |Δ - farD c| / (c ^ 2 / 16) ≤ (21 * (c * Real.log c)) ^ 2 / (c ^ 2 / 16) :=
              div_le_div_of_nonneg_right h1 (by positivity)
          _ = 16 * (21 * Real.log c) ^ 2 := by field_simp
      exact (abs_sub _ _).trans (by rw [abs_one]; linarith)
    have hfac2 : 1 + 16 * (21 * Real.log c) ^ 2 ≤ 7100 * (1 + Real.log c) ^ 2 := by
      have hlc1 : Real.log c ≤ 1 + Real.log c := by linarith
      nlinarith [sq_nonneg (1 + Real.log c), sq_nonneg (Real.log c)]
    calc Δ * gaussK (farW c) (Δ - farD c) * |1 - Δ * (Δ - farD c) / farW c ^ 2|
        ≤ (84 * (1 + Real.log c)) * (7100 * (1 + Real.log c) ^ 2) :=
          mul_le_mul (by linarith) (hfac.trans hfac2) (abs_nonneg _) (by positivity)
      _ ≤ 600000 * (1 + Real.log c) ^ 3 := by nlinarith [pow_pos (by linarith : 0 < 1 + Real.log c) 3]

lemma sfNegDeriv_lip {c : ℝ} (hc : 3 ≤ c) {L₁ L₂ : ℝ}
    (h1 : L₁ ≤ Real.log (π ^ 2 * Real.log c) + 3) (h2 : L₂ ≤ Real.log (π ^ 2 * Real.log c) + 3) :
    |sfNegDeriv c L₁ - sfNegDeriv c L₂| ≤ 600000 * (1 + Real.log c) ^ 3 * |L₁ - L₂| := by
  have hW : 0 < farW c := by unfold farW; linarith
  have hc1 : 1 < c := by linarith
  have hdiff : ∀ x, DifferentiableAt ℝ (sfNegDeriv c) x := fun x => by
    have hΔd : HasDerivAt (fun t => c * (Real.exp t / π ^ 2)) (c * (Real.exp x / π ^ 2)) x :=
      ((Real.hasDerivAt_exp x).div_const _).const_mul c
    have hGd := (gaussK_hasDerivAt hW (c * (Real.exp x / π ^ 2) - farD c)).comp x (hΔd.sub_const (farD c))
    have hprod := (hΔd.mul hGd).neg
    change HasDerivAt (sfNegDeriv c) _ x at hprod
    exact hprod.differentiableAt
  have hmv := (convex_Iic (Real.log (π ^ 2 * Real.log c) + 3)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hdiff x) (fun x hx => by
      rw [Real.norm_eq_abs]; exact (sfNegDeriv_bounds hc hx).2) h2 h1
  simpa [Real.norm_eq_abs, Real.dist_eq] using hmv

/-! ### Cauchy Lipschitz bounds for `ctYRD` and `deriv (ctPsi ε)` -/

lemma ctYRD_lip {w₁ w₂ : ℝ} (h1 : |w₁| ≤ 5e-4) (h2 : |w₂| ≤ 5e-4) :
    |ctYRD w₁ - ctYRD w₂| ≤ 7000 * |w₁ - w₂| := by
  have hdiff : DifferentiableOn ℂ (chartY etaC) (Metric.ball 0 1e-3) := fun z hz => by
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact (hasDerivAt_chartY langerEta_etaC hz.le).differentiableAt.differentiableWithinAt
  have hdiff' : DifferentiableOn ℂ (deriv (chartY etaC)) (Metric.ball 0 1e-3) :=
    hdiff.deriv Metric.isOpen_ball
  have hbd : ∀ z₀ ∈ Metric.closedBall (0 : ℂ) 5e-4, ‖deriv (deriv (chartY etaC)) z₀‖ ≤ 7000 := by
    intro z₀ hz₀
    have hz0n : ‖z₀‖ ≤ 5e-4 := by simpa using hz₀
    have hsph : ∀ w ∈ Metric.sphere z₀ 3e-4, ‖deriv (chartY etaC) w‖ ≤ 2 := fun w hw => by
      have hw_dist : ‖w - z₀‖ = 3e-4 := by simpa [dist_eq_norm] using hw
      have hwn : ‖w‖ ≤ 1e-3 := calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ 3e-4 + 5e-4 := add_le_add hw_dist.le hz0n
        _ ≤ 1e-3 := by norm_num
      rw [(hasDerivAt_chartY langerEta_etaC hwn).deriv]
      have h2 := norm_chartYD_add_one_le langerEta_etaC hwn
      calc ‖chartYD etaC w‖ = ‖(chartYD etaC w + 1) - 1‖ := by ring_nf
        _ ≤ ‖chartYD etaC w + 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 4e-3 + 1 := by simpa using add_le_add_right h2 1
        _ ≤ 2 := by norm_num
    have hcl : closure (Metric.ball z₀ 3e-4) ⊆ Metric.ball 0 1e-3 := fun w hw => by
      have h1' : ‖w - z₀‖ ≤ 3e-4 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using Metric.closure_ball_subset_closedBall hw
      have h2' : ‖w‖ < 1e-3 := calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ 3e-4 + 5e-4 := add_le_add h1' hz0n
        _ < 1e-3 := by norm_num
      simpa using h2'
    have hdiff_sub : DiffContOnCl ℂ (deriv (chartY etaC)) (Metric.ball z₀ 3e-4) :=
      ⟨hdiff'.mono (subset_closure.trans hcl), hdiff'.continuousOn.mono hcl⟩
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 3e-4)
      hdiff_sub (fun w hw => hsph w (by simpa using hw))
    exact hc.trans (by norm_num)
  have hmv := (convex_closedBall (0 : ℂ) 5e-4).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hdiff' z (Metric.closedBall_subset_ball (by norm_num) hz)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball (by norm_num) hz)))
    hbd (show (w₂ : ℂ) ∈ Metric.closedBall 0 5e-4 by simpa [Real.norm_eq_abs] using h2)
    (show (w₁ : ℂ) ∈ Metric.closedBall 0 5e-4 by simpa [Real.norm_eq_abs] using h1)
  have heq : ∀ w : ℝ, |w| ≤ 5e-4 → deriv (chartY etaC) (w : ℂ) = chartYD etaC (w : ℂ) := fun w hw =>
    (hasDerivAt_chartY langerEta_etaC (by simpa [Real.norm_eq_abs] using hw.trans (by norm_num))).deriv
  rw [heq w₁ h1, heq w₂ h2] at hmv
  have hre : |ctYRD w₁ - ctYRD w₂| ≤ ‖chartYD etaC w₁ - chartYD etaC w₂‖ := by
    unfold ctYRD
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (chartYD etaC w₁ - chartYD etaC w₂)
  refine hre.trans (hmv.trans_eq ?_)
  rw [show (w₁ : ℂ) - (w₂ : ℂ) = ((w₁ - w₂ : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

lemma ctPsi_deriv_lip {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ ρ₀ Kψ : ℝ, 0 < ρ₀ ∧ 0 ≤ Kψ ∧
      ∀ a₁ a₂ : ℝ, a₁ ∈ Ioo (-ρ₀) 0 → a₂ ∈ Ioo (-ρ₀) 0 →
        |deriv (ctPsi ε) a₁ - deriv (ctPsi ε) a₂| ≤ Kψ * |a₁ - a₂| := by
  obtain ⟨ρ, Ψ, hρ, hdiff, -, hval⟩ := ctPsiAnalytic hε
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn
    (hdiff.continuousOn.mono (Metric.closedBall_subset_ball (by linarith)))
  have hB0 : ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2), ‖Ψ z‖ ≤ max B 0 := fun z hz =>
    (hB z hz).trans (le_max_left _ _)
  have hBnn : 0 ≤ max B 0 := le_max_right _ _
  have hd1_bd : ∀ z ∈ Metric.closedBall (0 : ℂ) (3 * ρ / 8), ‖deriv Ψ z‖ ≤ max B 0 / (ρ / 8) := by
    intro z hz
    have hzn : ‖z‖ ≤ 3 * ρ / 8 := by simpa using hz
    have hcl : closure (Metric.ball z (ρ / 8)) ⊆ Metric.ball 0 ρ := fun w hw => by
      have h1 : ‖w - z‖ ≤ ρ / 8 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using Metric.closure_ball_subset_closedBall hw
      have h2 : ‖w‖ ≤ ρ / 2 := calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ρ / 8 + 3 * ρ / 8 := add_le_add h1 hzn
        _ = ρ / 2 := by ring
      simpa [Metric.mem_ball] using lt_of_le_of_lt h2 (by linarith)
    have hsub : DiffContOnCl ℂ Ψ (Metric.ball z (ρ / 8)) :=
      ⟨hdiff.mono (subset_closure.trans hcl), hdiff.continuousOn.mono hcl⟩
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hsub fun w hw => ?_
    have hw_dist : ‖w - z‖ = ρ / 8 := by simpa [dist_eq_norm] using hw
    refine hB0 w ?_
    simpa [Metric.mem_closedBall] using calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ρ / 8 + 3 * ρ / 8 := add_le_add hw_dist.le hzn
      _ = ρ / 2 := by ring
  have hdiff' : DifferentiableOn ℂ (deriv Ψ) (Metric.ball 0 ρ) := hdiff.deriv Metric.isOpen_ball
  have hd2_bd : ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 4),
      ‖deriv (deriv Ψ) z‖ ≤ (max B 0 / (ρ / 8)) / (ρ / 8) := by
    intro z hz
    have hzn : ‖z‖ ≤ ρ / 4 := by simpa using hz
    have hcl : closure (Metric.ball z (ρ / 8)) ⊆ Metric.ball 0 ρ := fun w hw => by
      have h1 : ‖w - z‖ ≤ ρ / 8 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using Metric.closure_ball_subset_closedBall hw
      have h2 : ‖w‖ ≤ 3 * ρ / 8 := calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ρ / 8 + ρ / 4 := add_le_add h1 hzn
        _ = 3 * ρ / 8 := by ring
      simpa [Metric.mem_ball] using lt_of_le_of_lt h2 (by linarith)
    have hsub : DiffContOnCl ℂ (deriv Ψ) (Metric.ball z (ρ / 8)) :=
      ⟨hdiff'.mono (subset_closure.trans hcl), hdiff'.continuousOn.mono hcl⟩
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hsub fun w hw => ?_
    have hw_dist : ‖w - z‖ = ρ / 8 := by simpa [dist_eq_norm] using hw
    refine hd1_bd w ?_
    simpa [Metric.mem_closedBall] using calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ρ / 8 + ρ / 4 := add_le_add hw_dist.le hzn
      _ = 3 * ρ / 8 := by ring
  refine ⟨ρ / 4, (max B 0 / (ρ / 8)) / (ρ / 8), by positivity, by positivity, fun a₁ a₂ ha₁ ha₂ => ?_⟩
  have hmv := (convex_closedBall (0 : ℂ) (ρ / 4)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hdiff' z (Metric.closedBall_subset_ball (by linarith) hz)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball (by linarith) hz)))
    hd2_bd (show (a₂ : ℂ) ∈ Metric.closedBall 0 (ρ / 4) by
      simpa [Metric.mem_closedBall, Real.norm_eq_abs, abs_of_neg ha₂.2] using (by linarith [ha₂.1] : -a₂ ≤ ρ / 4))
    (show (a₁ : ℂ) ∈ Metric.closedBall 0 (ρ / 4) by
      simpa [Metric.mem_closedBall, Real.norm_eq_abs, abs_of_neg ha₁.2] using (by linarith [ha₁.1] : -a₁ ≤ ρ / 4))
  have hderiv_eq : ∀ a ∈ Ioo (-(ρ / 4)) 0, deriv (ctPsi ε) a = (deriv Ψ (a : ℂ)).re := fun a ha => by
    have ha_ball : (a : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
      simpa [Metric.mem_ball, Real.norm_eq_abs, abs_of_neg ha.2] using lt_trans (by linarith [ha.1] : -a < ρ / 4) (by linarith)
    have hΨd : HasDerivAt Ψ (deriv Ψ (a : ℂ)) (a : ℂ) :=
      ((hdiff _ ha_ball).differentiableAt (Metric.isOpen_ball.mem_nhds ha_ball)).hasDerivAt
    have hre_d : HasDerivAt (fun t : ℝ => (Ψ (t : ℂ)).re) (deriv Ψ (a : ℂ)).re a :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hΨd.comp_ofReal
    have hev : (fun t : ℝ => (Ψ (t : ℂ)).re) =ᶠ[𝓝 a] ctPsi ε := by
      filter_upwards [Ioo_mem_nhds (by linarith [ha.1] : -ρ < a) ha.2] with t ht
      rw [hval t ht.1 ht.2, Complex.ofReal_re]
    exact (hre_d.congr_of_eventuallyEq hev.symm).deriv
  rw [hderiv_eq a₁ ha₁, hderiv_eq a₂ ha₂]
  have hre : |(deriv Ψ (a₁ : ℂ)).re - (deriv Ψ (a₂ : ℂ)).re| ≤ ‖deriv Ψ (a₁ : ℂ) - deriv Ψ (a₂ : ℂ)‖ := by
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (deriv Ψ (a₁ : ℂ) - deriv Ψ (a₂ : ℂ))
  refine hre.trans (hmv.trans_eq ?_)
  rw [show (a₁ : ℂ) - (a₂ : ℂ) = ((a₁ - a₂ : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

end FormalResearch.SignUncertainty
