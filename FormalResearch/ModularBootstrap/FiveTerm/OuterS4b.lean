module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterDphi
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS4bPhi

/-!
# FIVE-S, S4b: `ΔΦ_δ` is holomorphic on the band with bounded derivatives, and `Re ΔΦ_δ = 0` on `E_+`

`ΔΦ_δ(b) = (1/π) ∫_{ξ_*}^∞ δφ_δ'(y) φ_y(b) dy`.  Inputs: `outerS4a` (so `δφ_δ' ∈ L¹(ξ_*, ∞)`, continuous), and from
`OuterS4bPhi` the uniform bounds `‖φ_y‖ ≤ 15 + π`, `‖φ_y'‖ ≤ 4π`, `‖φ_y''‖ ≤ 8π²` on the band `|Im b - 1/2| < 1/4`.
Differentiation under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) twice.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

lemma isOpen_band : IsOpen (bandUpper (1 / 4)) := by
  have : bandUpper (1 / 4) = {b : ℂ | |b.im - 1 / 2| < 1 / 4} := rfl
  rw [this]
  exact isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const

lemma dphi_deriv_diffAt (δ : ℝ) {y : ℝ} (hy : xiStar < y) : DifferentiableAt ℝ (deriv (dphi δ)) y := by
  obtain ⟨C, -, Θ1, Θ2, hd1, hd2, -⟩ := thetaOutT_data
  have h1 : ∀ τ, HasDerivAt (fun τ => -thetaOutT τ + gfun (1 - δ) τ) (-Θ1 τ + g1 (1 - δ) τ) τ :=
    fun τ => (hd1 τ).neg.add (hasDerivAt_gfun _ τ)
  have h2 : ∀ τ, HasDerivAt (fun τ => -Θ1 τ + g1 (1 - δ) τ) (-Θ2 τ + g2 (1 - δ) τ) τ :=
    fun τ => (hd2 τ).neg.add (hasDerivAt_g1 _ τ)
  have hth : ∀ w, xiStar < w →
      HasDerivAt (fun w => -thetaOutT (tauOfX w) + gfun (1 - δ) (tauOfX w))
        ((-Θ1 (tauOfX w) + g1 (1 - δ) (tauOfX w)) * tx w) w := fun w hw =>
    (h1 (tauOfX w)).scomp w (hasDerivAt_tauOfX hw) |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hd : ∀ w, xiStar < w → deriv (dphi δ) w = (-Θ1 (tauOfX w) + g1 (1 - δ) (tauOfX w)) * tx w := by
    intro w hw
    have hev : ∀ᶠ v in 𝓝 w, xiStar < v := Ioi_mem_nhds hw
    have hF : dphi δ =ᶠ[𝓝 w] fun w => -thetaOutT (tauOfX w) + gfun (1 - δ) (tauOfX w) :=
      hev.mono fun v hv => dphi_eq hv
    exact (hF.deriv_eq).trans (hth w hw).deriv
  have hev : ∀ᶠ v in 𝓝 y, xiStar < v := Ioi_mem_nhds hy
  have heq : deriv (dphi δ) =ᶠ[𝓝 y] fun w => (-Θ1 (tauOfX w) + g1 (1 - δ) (tauOfX w)) * tx w :=
    hev.mono fun w hw => hd w hw
  have h3 : HasDerivAt (fun w => -Θ1 (tauOfX w) + g1 (1 - δ) (tauOfX w))
      ((-Θ2 (tauOfX y) + g2 (1 - δ) (tauOfX y)) * tx y) y :=
    (h2 (tauOfX y)).scomp y (hasDerivAt_tauOfX hy) |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
  exact ((h3.mul (hasDerivAt_tx hy)).differentiableAt).congr_of_eventuallyEq heq

lemma continuousOn_dphi_deriv (δ : ℝ) : ContinuousOn (deriv (dphi δ)) (Ioi xiStar) :=
  fun _ hy => (dphi_deriv_diffAt δ hy).continuousAt.continuousWithinAt

lemma integrableOn_dphi_deriv {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    IntegrableOn (deriv (dphi δ)) (Ioi xiStar) := by
  obtain ⟨C, hC, hb⟩ := outerS4a
  have hmeas := continuousOn_dphi_deriv δ
  have hxi := xiStar_pos
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : xiStar ≤ xiStar + 1)]
  refine IntegrableOn.union ?_ ?_
  · have hI : IntegrableOn (fun y => C * (y - xiStar) ^ (-(1 : ℝ) / 2)) (Ioc xiStar (xiStar + 1)) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1 : ℝ) / 2)
        (by norm_num)).comp_sub_right xiStar
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h
      simp only [zero_add, add_comm (1 : ℝ) xiStar] at h
      exact h.const_mul C
    refine Integrable.mono' hI
      ((hmeas.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hyx : xiStar < y := hy.1
    have h := (hb δ hδ0 hδ1 y hyx).1
    rw [min_eq_left (by linarith [hy.2])] at h
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hr : 0 < (y - xiStar) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    have he : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    nlinarith [mul_pos hC hr]
  · have hI : IntegrableOn (fun y => C * Real.exp (-π * y)) (Ioi (xiStar + 1)) :=
      (exp_neg_integrableOn_Ioi _ Real.pi_pos).const_mul C
    refine Integrable.mono' hI
      ((hmeas.mono (Ioi_subset_Ioi (by linarith))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyx : xiStar < y := by have : xiStar + 1 < y := hy; linarith
    have h := (hb δ hδ0 hδ1 y hyx).1
    rw [min_eq_right (by have : xiStar + 1 < y := hy; linarith), Real.one_rpow, mul_one] at h
    rw [Real.norm_eq_abs]
    refine h.trans (le_of_eq ?_)
    rw [neg_mul]

/-- Differentiation under the integral on the band, for a bounded smooth family `P y b`. -/
lemma hasDerivAt_param {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi xiStar)) {P P' : ℝ → ℂ → ℂ} {K0 K1 : ℝ}
    (hPc : ∀ b ∈ bandUpper (1 / 4), Continuous fun y => P y b)
    (hP'c : ∀ b ∈ bandUpper (1 / 4), Continuous fun y => P' y b)
    (hP0 : ∀ y b, b ∈ bandUpper (1 / 4) → ‖P y b‖ ≤ K0)
    (hP1 : ∀ y b, b ∈ bandUpper (1 / 4) → ‖P' y b‖ ≤ K1)
    (hd : ∀ y, ∀ b ∈ bandUpper (1 / 4), HasDerivAt (P y) (P' y b) b) :
    ∀ b ∈ bandUpper (1 / 4), HasDerivAt (fun b => ∫ y in Ioi xiStar, ((g y : ℝ) : ℂ) * P y b)
      (∫ y in Ioi xiStar, ((g y : ℝ) : ℂ) * P' y b) b := by
  intro b0 hb0
  have hgc : AEStronglyMeasurable (fun y => ((g y : ℝ) : ℂ)) (volume.restrict (Ioi xiStar)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hnorm : ∀ (Q : ℝ → ℂ) (K : ℝ), (∀ y, ‖Q y‖ ≤ K) →
      ∀ y, ‖((g y : ℝ) : ℂ) * Q y‖ ≤ ‖g y‖ * K := by
    intro Q K hQ y
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hQ y) (norm_nonneg _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun y => ‖g y‖ * K1)
    (isOpen_band.mem_nhds hb0) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact (isOpen_band.mem_nhds hb0).mono fun b hb => hgc.mul (hPc b hb).aestronglyMeasurable
  · exact Integrable.mono' (hg.norm.mul_const K0) (hgc.mul (hPc b0 hb0).aestronglyMeasurable)
      (ae_of_all _ (hnorm (fun y => P y b0) K0 (fun y => hP0 y b0 hb0)))
  · exact hgc.mul (hP'c b0 hb0).aestronglyMeasurable
  · exact ae_of_all _ fun y b hb => hnorm (fun y => P' y b) K1 (fun y => hP1 y b hb) y
  · exact hg.norm.mul_const K1
  · exact ae_of_all _ fun y b hb => (hd y b hb).const_mul _

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
