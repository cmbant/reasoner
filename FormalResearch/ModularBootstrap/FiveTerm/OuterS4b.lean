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
    (F := fun b y => ((g y : ℝ) : ℂ) * P y b) (F' := fun b y => ((g y : ℝ) : ℂ) * P' y b)
    (μ := volume.restrict (Ioi xiStar)) (s := bandUpper (1 / 4))
    (isOpen_band.mem_nhds hb0) ?_ ?_ ?_ ?_ ?_ ?_).2
  · have hev : ∀ᶠ b in 𝓝 b0, b ∈ bandUpper (1 / 4) := isOpen_band.mem_nhds hb0
    exact hev.mono fun b hb => hgc.mul (hPc b hb).aestronglyMeasurable
  · exact Integrable.mono' (hg.norm.mul_const K0) (hgc.mul (hPc b0 hb0).aestronglyMeasurable)
      (ae_of_all _ (hnorm (fun y => P y b0) K0 (fun y => hP0 y b0 hb0)))
  · exact hgc.mul (hP'c b0 hb0).aestronglyMeasurable
  · exact ae_of_all _ fun y b hb => hnorm (fun y => P' y b) K1 (fun y => hP1 y b hb) y
  · exact hg.norm.mul_const K1
  · exact ae_of_all _ fun y b hb => (hd y b hb).const_mul _


/-! ### Continuity in `y` and derivatives of `φ_y` on the band -/

lemma continuous_Tcx_y {b : ℂ} (hb : b ∈ imStrip) : Continuous fun y : ℝ => Tcx y b := by
  unfold Tcx
  simp only [Complex.tanh_eq_sinh_div_cosh]
  refine Continuous.mul (Continuous.div (by fun_prop) (by fun_prop) (fun y => cosh_half₁ hb))
    (Continuous.div (by fun_prop) (by fun_prop) (fun y => cosh_half₂ hb))

lemma continuous_phiY_y {b : ℂ} (hb : b ∈ imStrip) : Continuous fun y : ℝ => phiY y b := by
  have : (fun y : ℝ => phiY y b) = fun y => Complex.log (-(Tcx y b)) := funext fun y => phiY_eq hb
  rw [this]
  exact (continuous_Tcx_y hb).neg.clog (fun y => neg_Tcx_mem_slit hb)

lemma continuous_phiYDeriv_y {b : ℂ} (hb : b ∈ imStrip) : Continuous fun y : ℝ => phiYDeriv y b := by
  unfold phiYDeriv
  refine continuous_const.mul (Continuous.add (Continuous.div continuous_const (by fun_prop) (fun y => sinh_w₁ hb))
    (Continuous.div continuous_const (by fun_prop) (fun y => sinh_w₂ hb)))

lemma continuous_phiYDeriv2_y {b : ℂ} (hb : b ∈ imStrip) : Continuous fun y : ℝ => phiYDeriv2 y b := by
  unfold phiYDeriv2
  refine continuous_const.mul (Continuous.add
    (Continuous.div (by fun_prop) (by fun_prop) (fun y => pow_ne_zero 2 (sinh_w₁ hb)))
    (Continuous.div (by fun_prop) (by fun_prop) (fun y => pow_ne_zero 2 (sinh_w₂ hb))))

lemma hasDerivAt_phiY {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : HasDerivAt (phiY y) (phiYDeriv y b) b := by
  have hev : ∀ᶠ z in 𝓝 b, z ∈ imStrip := isOpen_imStrip.mem_nhds hb
  exact (hasDerivAt_logTcx hb).congr_of_eventuallyEq (hev.mono fun z hz => phiY_eq hz)

lemma integrable_param {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi xiStar)) {Q : ℝ → ℂ} {K : ℝ}
    (hQc : Continuous Q) (hQ : ∀ y, ‖Q y‖ ≤ K) :
    Integrable (fun y => ((g y : ℝ) : ℂ) * Q y) (volume.restrict (Ioi xiStar)) := by
  have hgc : AEStronglyMeasurable (fun y => ((g y : ℝ) : ℂ)) (volume.restrict (Ioi xiStar)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable
  refine Integrable.mono' (hg.norm.mul_const K) (hgc.mul hQc.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (hQ y) (norm_nonneg _)

lemma norm_int_le {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi xiStar)) {Q : ℝ → ℂ} {K : ℝ}
    (hQ : ∀ y, ‖Q y‖ ≤ K) :
    ‖∫ y in Ioi xiStar, ((g y : ℝ) : ℂ) * Q y‖ ≤ (∫ y in Ioi xiStar, ‖g y‖) * K := by
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi xiStar))
    (f := fun y => ((g y : ℝ) : ℂ) * Q y) (hg.norm.mul_const K) (ae_of_all _ fun y => by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hQ y) (norm_nonneg _))
  rwa [integral_mul_const] at h

lemma etaDelta_small : etaDelta (1 / 40) < 1 / 16 := by
  unfold etaDelta
  have hpi := Real.pi_pos
  have hs2 : √2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2' : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hq : √2 * (2 * (1 / 40 : ℝ) - (1 / 40 : ℝ) ^ 2) / (2 - 2 * (1 / 40 : ℝ) + (1 / 40 : ℝ) ^ 2) < 1 / 8 := by
    rw [div_lt_iff₀ (by norm_num)]; nlinarith
  have hq0 : 0 ≤ √2 * (2 * (1 / 40 : ℝ) - (1 / 40 : ℝ) ^ 2) / (2 - 2 * (1 / 40 : ℝ) + (1 / 40 : ℝ) ^ 2) := by
    positivity
  have hsin : 1 / 8 ≤ Real.sin (π / 16) := by
    have := Real.mul_le_sin (x := π / 16) (by positivity) (by linarith)
    have e : 2 / π * (π / 16) = 1 / 8 := by field_simp; norm_num
    linarith
  have hsin1 : Real.sin (π / 16) ≤ 1 := Real.sin_le_one _
  have hq0' : (-1 : ℝ) ≤ √2 * (2 * (1 / 40 : ℝ) - (1 / 40 : ℝ) ^ 2) / (2 - 2 * (1 / 40 : ℝ) + (1 / 40 : ℝ) ^ 2) := by
    linarith
  have hqle : √2 * (2 * (1 / 40 : ℝ) - (1 / 40 : ℝ) ^ 2) / (2 - 2 * (1 / 40 : ℝ) + (1 / 40 : ℝ) ^ 2) ≤ 1 := by
    linarith
  have hsn0 : 0 ≤ Real.sin (π / 16) := by linarith
  have h1 : Real.arcsin (√2 * (2 * (1 / 40 : ℝ) - (1 / 40 : ℝ) ^ 2) / (2 - 2 * (1 / 40 : ℝ) + (1 / 40 : ℝ) ^ 2)) <
      Real.arcsin (Real.sin (π / 16)) :=
    Real.strictMonoOn_arcsin ⟨hq0', hqle⟩ ⟨by linarith, hsin1⟩ (by linarith)
  rw [Real.arcsin_sin (by linarith) (by linarith)] at h1
  rw [div_lt_iff₀ hpi]
  linarith

lemma integrableOn_mbound :
    IntegrableOn (fun y => (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y))) (Ioi xiStar) := by
  have hxi := xiStar_pos
  have hmeas : ContinuousOn (fun y => (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y))) (Ioi xiStar) := by
    refine ContinuousOn.mul ?_ (by fun_prop)
    refine ContinuousOn.rpow_const (by fun_prop) (fun y hy => Or.inl ?_)
    have : xiStar < y := hy
    exact (lt_min (by linarith) one_pos).ne'
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : xiStar ≤ xiStar + 1)]
  refine IntegrableOn.union ?_ ?_
  · have hI : IntegrableOn (fun y => (y - xiStar) ^ (-(1 : ℝ) / 2)) (Ioc xiStar (xiStar + 1)) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1 : ℝ) / 2)
        (by norm_num)).comp_sub_right xiStar
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h
      simpa only [zero_add, add_comm (1 : ℝ) xiStar] using h
    refine Integrable.mono' hI
      ((hmeas.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hyx : xiStar < y := hy.1
    rw [min_eq_left (by linarith [hy.2])]
    have hr : 0 < (y - xiStar) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    have he : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  · have hI : IntegrableOn (fun y => Real.exp (-π * y)) (Ioi (xiStar + 1)) :=
      exp_neg_integrableOn_Ioi _ Real.pi_pos
    refine Integrable.mono' hI
      ((hmeas.mono (Ioi_subset_Ioi (by linarith))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyx : xiStar + 1 < y := hy
    rw [min_eq_right (by linarith), Real.one_rpow, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      neg_mul]

lemma norm_inv_pi_mul (z : ℂ) : ‖(1 / (π : ℂ)) * z‖ = ‖z‖ / π := by
  rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

/-- **`OuterS4b`** (`cts:smooth-env` (3), potential): `ΔΦ_δ` is holomorphic on the band with `Re ΔΦ_δ = 0` on `E_+` and
bounded derivatives of order `0, 1, 2`.  Class: proved. -/
theorem outerS4b : OuterS4b := by
  have hpi := Real.pi_pos
  obtain ⟨C0, hC0, hb⟩ := outerS4a
  have hJ := integrableOn_mbound
  set J := ∫ y in Ioi xiStar, (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y)) with hJdef
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun y hy => by
    have : xiStar < y := hy
    positivity
  set Cc : ℝ := C0 * J * ((15 + π) / π + 4 + 8 * π) + 1 with hCc
  have hCcπ : Cc * π = C0 * J * (15 + π) + C0 * J * (4 * π) + C0 * J * (8 * π ^ 2) + π := by
    rw [hCc]; field_simp
  have hCJ : 0 ≤ C0 * J := mul_nonneg hC0.le hJ0
  refine ⟨1 / 40, by norm_num, by norm_num, etaDelta_small, Cc, by rw [hCc]; positivity, ?_⟩
  intro δ hδ0 hδ1
  have hδ1' : δ < 1 / 4 := by linarith
  have hg := integrableOn_dphi_deriv hδ0 hδ1'
  have hI : (∫ y in Ioi xiStar, ‖deriv (dphi δ) y‖) ≤ C0 * J := by
    calc (∫ y in Ioi xiStar, ‖deriv (dphi δ) y‖)
        ≤ ∫ y in Ioi xiStar, C0 * ((min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y))) :=
          setIntegral_mono_on hg.norm (hJ.const_mul C0) measurableSet_Ioi (fun y hy => by
            have h := (hb δ hδ0 hδ1' y hy).1
            rw [Real.norm_eq_abs, ← mul_assoc]; exact h)
      _ = C0 * J := integral_const_mul _ _
  set I := ∫ y in Ioi xiStar, ‖deriv (dphi δ) y‖ with hIdef
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun y _ => norm_nonneg _
  have hband : ∀ b ∈ bandUpper (1 / 4), b ∈ imStrip := fun b hb => band_sub_strip hb
  have d1 := hasDerivAt_param (g := deriv (dphi δ)) hg (P := phiY) (P' := phiYDeriv) (K0 := 15 + π)
    (K1 := 4 * π) (fun b hb => continuous_phiY_y (hband b hb)) (fun b hb => continuous_phiYDeriv_y (hband b hb))
    (fun y b hb => norm_phiY_le hb) (fun y b hb => norm_phiYDeriv_le hb)
    (fun y b hb => hasDerivAt_phiY (hband b hb))
  have d2 := hasDerivAt_param (g := deriv (dphi δ)) hg (P := phiYDeriv) (P' := phiYDeriv2) (K0 := 4 * π)
    (K1 := 8 * π ^ 2) (fun b hb => continuous_phiYDeriv_y (hband b hb))
    (fun b hb => continuous_phiYDeriv2_y (hband b hb))
    (fun y b hb => norm_phiYDeriv_le hb) (fun y b hb => norm_phiYDeriv2_le hb)
    (fun y b hb => hasDerivAt_phiYDeriv (hband b hb))
  set D1 : ℂ → ℂ := fun b => (1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiYDeriv y b with hD1
  set D2 : ℂ → ℂ := fun b => (1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiYDeriv2 y b
    with hD2
  have hdΔ : ∀ b ∈ bandUpper (1 / 4), HasDerivAt (DeltaPhi δ) (D1 b) b := fun b hb =>
    (d1 b hb).const_mul (1 / (π : ℂ))
  have hD1d : ∀ b ∈ bandUpper (1 / 4), HasDerivAt D1 (D2 b) b := fun b hb => (d2 b hb).const_mul (1 / (π : ℂ))
  have hder : ∀ b ∈ bandUpper (1 / 4), deriv (DeltaPhi δ) b = D1 b := fun b hb => (hdΔ b hb).deriv
  have hdd : ∀ b ∈ bandUpper (1 / 4), HasDerivAt (deriv (DeltaPhi δ)) (D2 b) b := by
    intro b hb
    have hev : ∀ᶠ z in 𝓝 b, z ∈ bandUpper (1 / 4) := isOpen_band.mem_nhds hb
    exact (hD1d b hb).congr_of_eventuallyEq (hev.mono fun z hz => hder z hz)
  refine ⟨fun b hb => (hdΔ b hb).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro v
    have hbv : ((v : ℂ) + Complex.I / 2) ∈ bandUpper (1 / 4) := by
      show |(((v : ℂ) + Complex.I / 2)).im - 1 / 2| < 1 / 4
      simp
    have hbs := hband _ hbv
    have hint := integrable_param hg (Q := fun y => phiY y ((v : ℂ) + Complex.I / 2))
      (continuous_phiY_y hbs) (K := 15 + π) (fun y => norm_phiY_le hbv)
    have hre : ∀ y, (((deriv (dphi δ) y : ℝ) : ℂ) * phiY y ((v : ℂ) + Complex.I / 2)).re = 0 := by
      intro y; simp [Complex.mul_re, re_phiY_half]
    have h1 : (∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y ((v : ℂ) + Complex.I / 2)).re = 0 := by
      have h := Complex.reCLM.integral_comp_comm hint
      simp only [Complex.reCLM_apply, hre, integral_zero] at h
      exact h.symm
    show ((1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y ((v : ℂ) + Complex.I / 2)).re = 0
    rw [show (1 / (π : ℂ)) = (((1 / π : ℝ)) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, h1, mul_zero]
  · intro b hb
    refine ⟨?_, ?_, ?_⟩
    · show ‖(1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b‖ ≤ _
      rw [norm_inv_pi_mul, div_le_iff₀ hpi]
      have := norm_int_le hg (Q := fun y => phiY y b) (K := 15 + π) (fun y => norm_phiY_le hb)
      have h2 : I * (15 + π) ≤ C0 * J * (15 + π) := mul_le_mul_of_nonneg_right hI (by positivity)
      have p1 : 0 ≤ C0 * J * (4 * π) := by positivity
      have p2 : 0 ≤ C0 * J * (8 * π ^ 2) := by positivity
      linarith
    · rw [hder b hb]
      show ‖(1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiYDeriv y b‖ ≤ _
      rw [norm_inv_pi_mul, div_le_iff₀ hpi]
      have := norm_int_le hg (Q := fun y => phiYDeriv y b) (K := 4 * π) (fun y => norm_phiYDeriv_le hb)
      have h2 : I * (4 * π) ≤ C0 * J * (4 * π) := mul_le_mul_of_nonneg_right hI (by positivity)
      have p1 : 0 ≤ C0 * J * (15 + π) := by positivity
      have p2 : 0 ≤ C0 * J * (8 * π ^ 2) := by positivity
      linarith
    · rw [(hdd b hb).deriv]
      show ‖(1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiYDeriv2 y b‖ ≤ _
      rw [norm_inv_pi_mul, div_le_iff₀ hpi]
      have := norm_int_le hg (Q := fun y => phiYDeriv2 y b) (K := 8 * π ^ 2) (fun y => norm_phiYDeriv2_le hb)
      have h2 : I * (8 * π ^ 2) ≤ C0 * J * (8 * π ^ 2) := mul_le_mul_of_nonneg_right hI (by positivity)
      have p1 : 0 ≤ C0 * J * (15 + π) := by positivity
      have p2 : 0 ≤ C0 * J * (4 * π) := by positivity
      linarith

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS4b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerS4b

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
