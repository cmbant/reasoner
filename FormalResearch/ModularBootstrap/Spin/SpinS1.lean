module

public import FormalResearch.ModularBootstrap.Spin.SpinD3W

/-!
# Remaining Theorem S1 parts (`spinnotes:S1`(a), (d), (e))

Proves the three `Prop`s of `Spin/Statements.lean` not previously discharged:
- `spinS1a : SpinS1a`: separate holomorphy of `spinZHatC a ν` on `{Re z > 0}²`, equivalence
  between Euclidean modular `S`-invariance (`z₂ = conj z₁`) and independent-temperature
  real crossing `(sd:eSD1)`, and equivalence between `(sd:eSD1)` and odd two-variable Laguerre
  moment matching (via 1D complex analytic continuation + `spin_tensor_cayley_iff`).
- `spinS1d : SpinS1d`: weak-duality obstruction on the Liouville cone (`spinDW`).
- `spinS1e : SpinS1e`: equality of optimal continuous-spin, `J`-finite, and dual gaps on
  `liouvilleCone`, and primal-dual / attainment equality for `SpinCertifiedClass` on
  `integerSpinCone` (`spinDSD`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: Analyticity and crossing identities for `spinZHatC` (`SpinS1a`) -/

private lemma spin_rhp_isOpen : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma spin_rhp_isPreconnected : IsPreconnected {z : ℂ | 0 < z.re} :=
  (convex_halfSpace_re_gt 0).isPreconnected

private lemma spin_inv_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < z⁻¹.re := by
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr fun h0 => by simp [h0] at hz)

private lemma spin_inv_differentiableOn_rhp :
    DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {z : ℂ | 0 < z.re} := by
  intro z hz
  refine (differentiableAt_inv ?_).differentiableWithinAt
  intro h0
  simp [h0] at hz

private lemma spin_diffStrip_isOpen (x : ℝ) : IsOpen {w : ℂ | |w.re| < x} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

private lemma spin_diffStrip_convex (x : ℝ) : Convex ℝ {w : ℂ | |w.re| < x} := by
  have heq : {w : ℂ | |w.re| < x} = {w : ℂ | -x < w.re} ∩ {w : ℂ | w.re < x} := by
    ext w
    simp [abs_lt]
  rw [heq]
  exact (convex_halfSpace_re_gt (-x)).inter (convex_halfSpace_re_lt x)

private lemma spin_prod_re_pos_on_diffStrip {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : |w.re| < x) :
    0 < (((x : ℂ) + w) * ((x : ℂ) - w)).re := by
  have h1 : |w.re| ^ 2 < x ^ 2 := by
    nlinarith [abs_nonneg w.re]
  rw [sq_abs] at h1
  have hre : (((x : ℂ) + w) * ((x : ℂ) - w)).re = x ^ 2 - w.re ^ 2 + w.im ^ 2 := by
    simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_add, zero_sub]
    ring
  rw [hre]
  nlinarith [sq_nonneg w.im]

private lemma spin_zHatC_comp_differentiableOn {a : ℝ} {ν : Measure (ℝ × ℝ)}
    (hsupp : ν ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) = 0)
    (hlap : ∀ {β : ℝ}, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    {U : Set ℂ} (hU : IsOpen U) {g₁ g₂ : ℂ → ℂ}
    (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
    (hre : ∀ w ∈ U, 0 < (g₁ w).re ∧ 0 < (g₂ w).re) :
    DifferentiableOn ℂ (fun w => spinZHatC a ν (g₁ w) (g₂ w)) U := by
  have hae_nn : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    have hnot : ∀ᵐ p ∂ν, p ∉ ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) :=
      measure_eq_zero_iff_ae_notMem.1 hsupp
    filter_upwards [hnot] with p hp
    exact not_not.mp hp
  intro w₀ hw₀
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  have hcb_sub : Metric.closedBall w₀ (r / 2) ⊆ U :=
    Metric.closedBall_subset_ball (half_lt_self hr_pos) |>.trans hr_sub
  have hcb_ne : (Metric.closedBall w₀ (r / 2)).Nonempty :=
    ⟨w₀, Metric.mem_closedBall_self (by positivity)⟩
  let φ_re : ℂ → ℝ := fun w => min (g₁ w).re (g₂ w).re
  have hφ_cont : ContinuousOn φ_re (Metric.closedBall w₀ (r / 2)) :=
    ContinuousOn.inf
      (Complex.continuous_re.comp_continuousOn (hg₁.continuousOn.mono hcb_sub))
      (Complex.continuous_re.comp_continuousOn (hg₂.continuousOn.mono hcb_sub))
  obtain ⟨w_min, hw_min_mem, hw_min⟩ := isCompact_closedBall w₀ (r / 2) |>.exists_isMinOn hcb_ne hφ_cont
  set δ : ℝ := φ_re w_min
  have hδ_pos : 0 < δ := lt_min (hre w_min (hcb_sub hw_min_mem)).1 (hre w_min (hcb_sub hw_min_mem)).2
  have hre_ge : ∀ w ∈ Metric.closedBall w₀ (r / 2), δ ≤ (g₁ w).re ∧ δ ≤ (g₂ w).re := fun w hw => by
    have hle : δ ≤ φ_re w := hw_min hw
    exact ⟨hle.trans (min_le_left _ _), hle.trans (min_le_right _ _)⟩
  have hdg₁_cont : ContinuousOn (fun w => ‖deriv g₁ w‖) (Metric.closedBall w₀ (r / 2)) :=
    ((hg₁.analyticOnNhd hU).deriv.continuousOn.mono hcb_sub).norm
  have hdg₂_cont : ContinuousOn (fun w => ‖deriv g₂ w‖) (Metric.closedBall w₀ (r / 2)) :=
    ((hg₂.analyticOnNhd hU).deriv.continuousOn.mono hcb_sub).norm
  obtain ⟨w₁, _, hw₁⟩ := isCompact_closedBall w₀ (r / 2) |>.exists_isMaxOn hcb_ne hdg₁_cont
  obtain ⟨w₂, _, hw₂⟩ := isCompact_closedBall w₀ (r / 2) |>.exists_isMaxOn hcb_ne hdg₂_cont
  set M : ℝ := max (max ‖deriv g₁ w₁‖ ‖deriv g₂ w₂‖) 0
  have hM_nn : 0 ≤ M := le_max_right _ _
  have hderiv_le : ∀ w ∈ Metric.closedBall w₀ (r / 2), ‖deriv g₁ w‖ ≤ M ∧ ‖deriv g₂ w‖ ≤ M :=
    fun w hw =>
      ⟨(hw₁ hw).trans ((le_max_left _ _).trans (le_max_left _ _)),
       (hw₂ hw).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  let F : ℂ → ℝ × ℝ → ℂ := fun w p =>
    Complex.exp (-2 * π * (g₁ w * (p.1 : ℂ) + g₂ w * (p.2 : ℂ)))
  let F' : ℂ → ℝ × ℝ → ℂ := fun w p =>
    -2 * π * (deriv g₁ w * (p.1 : ℂ) + deriv g₂ w * (p.2 : ℂ)) * F w p
  let bound : ℝ × ℝ → ℝ := fun p =>
    (2 * M / δ) * Real.exp (-2 * π * (δ / 2) * (p.1 + p.2))
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) ν :=
    Eventually.of_forall fun w => by
      have hc : Continuous (F w) := by dsimp [F]; fun_prop
      exact hc.aestronglyMeasurable
  have hF_dom_ball : ∀ w ∈ Metric.closedBall w₀ (r / 2), ∀ p : ℝ × ℝ, 0 ≤ p.1 ∧ 0 ≤ p.2 →
      ‖F w p‖ ≤ Real.exp (-2 * π * δ * (p.1 + p.2)) := by
    intro w hw p hp
    have hw_re := hre_ge w hw
    dsimp [F]
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hmul_re : (-2 * π * (g₁ w * (p.1 : ℂ) + g₂ w * (p.2 : ℂ))).re =
        -2 * π * ((g₁ w).re * p.1 + (g₂ w).re * p.2) := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hmul_re]
    have hp1 : δ * p.1 ≤ (g₁ w).re * p.1 := mul_le_mul_of_nonneg_right hw_re.1 hp.1
    have hp2 : δ * p.2 ≤ (g₂ w).re * p.2 := mul_le_mul_of_nonneg_right hw_re.2 hp.2
    nlinarith [Real.pi_pos]
  have hF_int : Integrable (F w₀) ν := by
    refine (hlap hδ_pos).mono' (hF_meas.self_of_nhds) ?_
    filter_upwards [hae_nn] with p hp
    exact hF_dom_ball w₀ (Metric.mem_closedBall_self (by positivity)) p hp
  have hF'_meas : AEStronglyMeasurable (F' w₀) ν := by
    have hc : Continuous (F' w₀) := by dsimp [F', F]; fun_prop
    exact hc.aestronglyMeasurable
  have hF'_bound : ∀ᵐ p ∂ν, ∀ w ∈ Metric.ball w₀ (r / 2), ‖F' w p‖ ≤ bound p := by
    filter_upwards [hae_nn] with p hp w hw
    have hw_cb : w ∈ Metric.closedBall w₀ (r / 2) := Metric.ball_subset_closedBall hw
    have hd_w := hderiv_le w hw_cb
    have hF_bd := hF_dom_ball w hw_cb p hp
    have hlin : ‖deriv g₁ w * (p.1 : ℂ) + deriv g₂ w * (p.2 : ℂ)‖ ≤ M * (p.1 + p.2) := by
      calc ‖deriv g₁ w * (p.1 : ℂ) + deriv g₂ w * (p.2 : ℂ)‖
          ≤ ‖deriv g₁ w * (p.1 : ℂ)‖ + ‖deriv g₂ w * (p.2 : ℂ)‖ := norm_add_le _ _
        _ = ‖deriv g₁ w‖ * |p.1| + ‖deriv g₂ w‖ * |p.2| := by
            simp [Complex.norm_real, Real.norm_eq_abs]
        _ = ‖deriv g₁ w‖ * p.1 + ‖deriv g₂ w‖ * p.2 := by
            rw [abs_of_nonneg hp.1, abs_of_nonneg hp.2]
        _ ≤ M * p.1 + M * p.2 := add_le_add (mul_le_mul_of_nonneg_right hd_w.1 hp.1)
            (mul_le_mul_of_nonneg_right hd_w.2 hp.2)
        _ = M * (p.1 + p.2) := by ring
    have h2pi_norm : ‖(-2 * π : ℂ)‖ = 2 * π := by
      have hne : (-2 * π : ℂ) = ((-2 * π : ℝ) : ℂ) := by push_cast; rfl
      rw [hne, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [Real.pi_pos])]
      ring
    have hexp_u : (p.1 + p.2) * Real.exp (-2 * π * δ * (p.1 + p.2)) ≤
        (1 / (π * δ)) * Real.exp (-2 * π * (δ / 2) * (p.1 + p.2)) := by
      have hu_nn : 0 ≤ p.1 + p.2 := add_nonneg hp.1 hp.2
      have h1 : π * δ * (p.1 + p.2) ≤ Real.exp (π * δ * (p.1 + p.2)) := by
        linarith [Real.add_one_le_exp (π * δ * (p.1 + p.2))]
      have h2 : p.1 + p.2 ≤ (1 / (π * δ)) * Real.exp (π * δ * (p.1 + p.2)) := by
        have hpid_pos : 0 < π * δ := mul_pos Real.pi_pos hδ_pos
        calc p.1 + p.2 = (1 / (π * δ)) * (π * δ * (p.1 + p.2)) := by field_simp [hpid_pos.ne']
          _ ≤ (1 / (π * δ)) * Real.exp (π * δ * (p.1 + p.2)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
      have hmul := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-2 * π * δ * (p.1 + p.2))).le
      have hexp_eq : Real.exp (π * δ * (p.1 + p.2)) * Real.exp (-2 * π * δ * (p.1 + p.2)) =
          Real.exp (-2 * π * (δ / 2) * (p.1 + p.2)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hmul' : (p.1 + p.2) * Real.exp (-2 * π * δ * (p.1 + p.2)) ≤
          1 / (π * δ) * (Real.exp (π * δ * (p.1 + p.2)) * Real.exp (-2 * π * δ * (p.1 + p.2))) := by
        simpa [mul_assoc] using hmul
      rwa [hexp_eq] at hmul'
    calc ‖F' w p‖
        = ‖(-2 * π : ℂ)‖ * ‖deriv g₁ w * (p.1 : ℂ) + deriv g₂ w * (p.2 : ℂ)‖ * ‖F w p‖ := by
          dsimp [F']; rw [norm_mul, norm_mul]
      _ ≤ (2 * π) * (M * (p.1 + p.2)) * Real.exp (-2 * π * δ * (p.1 + p.2)) := by
          rw [h2pi_norm]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hlin (by positivity)) hF_bd
            (norm_nonneg _) (mul_nonneg (by positivity) (mul_nonneg hM_nn (add_nonneg hp.1 hp.2)))
      _ = (2 * π * M) * ((p.1 + p.2) * Real.exp (-2 * π * δ * (p.1 + p.2))) := by ring
      _ ≤ (2 * π * M) * ((1 / (π * δ)) * Real.exp (-2 * π * (δ / 2) * (p.1 + p.2))) :=
          mul_le_mul_of_nonneg_left hexp_u (mul_nonneg (by positivity) hM_nn)
      _ = bound p := by
          dsimp [bound]
          have hpi_ne : π ≠ 0 := Real.pi_pos.ne'
          field_simp [hpi_ne, hδ_pos.ne']
  have hbound_int : Integrable bound ν := (hlap (half_pos hδ_pos)).const_mul (2 * M / δ)
  have hF_deriv : ∀ᵐ p ∂ν, ∀ w ∈ Metric.ball w₀ (r / 2),
      HasDerivAt (fun z => F z p) (F' w p) w := by
    refine Eventually.of_forall fun p w hw => ?_
    have hwU : w ∈ U := hcb_sub (Metric.ball_subset_closedBall hw)
    have hdg₁ : HasDerivAt g₁ (deriv g₁ w) w := (hg₁.differentiableAt (hU.mem_nhds hwU)).hasDerivAt
    have hdg₂ : HasDerivAt g₂ (deriv g₂ w) w := (hg₂.differentiableAt (hU.mem_nhds hwU)).hasDerivAt
    have hlin : HasDerivAt (fun z => -2 * π * (g₁ z * (p.1 : ℂ) + g₂ z * (p.2 : ℂ)))
        (-2 * π * (deriv g₁ w * (p.1 : ℂ) + deriv g₂ w * (p.2 : ℂ))) w :=
      ((hdg₁.mul_const (p.1 : ℂ)).add (hdg₂.mul_const (p.2 : ℂ))).const_mul (-2 * π : ℂ)
    exact hlin.cexp.congr_deriv (by dsimp [F', F]; ring)
  obtain ⟨_, hderiv_int⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w₀ (half_pos hr_pos))
    hF_meas hF_int hF'_meas hF'_bound hbound_int hF_deriv
  have hdiff_vac : DifferentiableAt ℂ (fun w =>
      Complex.exp (π * (a : ℂ) * (g₁ w + g₂ w)) *
        (1 - Complex.exp (-2 * π * g₁ w)) * (1 - Complex.exp (-2 * π * g₂ w))) w₀ := by
    have hg₁₀ := hg₁.differentiableAt (hU.mem_nhds hw₀)
    have hg₂₀ := hg₂.differentiableAt (hU.mem_nhds hw₀)
    have he0 : DifferentiableAt ℂ (fun w => Complex.exp (π * (a : ℂ) * (g₁ w + g₂ w))) w₀ :=
      ((hg₁₀.add hg₂₀).const_mul (π * (a : ℂ))).cexp
    have he1 : DifferentiableAt ℂ (fun w => 1 - Complex.exp (-2 * π * g₁ w)) w₀ :=
      (differentiableAt_const 1).sub ((hg₁₀.const_mul (-2 * π : ℂ)).cexp)
    have he2 : DifferentiableAt ℂ (fun w => 1 - Complex.exp (-2 * π * g₂ w)) w₀ :=
      (differentiableAt_const 1).sub ((hg₂₀.const_mul (-2 * π : ℂ)).cexp)
    exact (he0.mul he1).mul he2
  have hdiff_full : DifferentiableAt ℂ (fun w => spinZHatC a ν (g₁ w) (g₂ w)) w₀ := by
    unfold spinZHatC
    exact hdiff_vac.add hderiv_int.differentiableAt
  exact hdiff_full.differentiableWithinAt

private lemma spinThermalX_integrable {ν : Measure (ℝ × ℝ)}
    (hsupp : ν ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) = 0)
    (hlap : ∀ {β : ℝ}, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (βL * p.1 + βR * p.2))) ν ∧
    Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 / βL + p.2 / βR))) ν ∧
    Integrable (fun p : ℝ × ℝ => spinThermalX βL βR p.1 p.2) ν := by
  have hae_nn : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    have hnot : ∀ᵐ p ∂ν, p ∉ ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) :=
      measure_eq_zero_iff_ae_notMem.1 hsupp
    filter_upwards [hnot] with p hp
    exact not_not.mp hp
  have hint_pair : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
      Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (γL * p.1 + γR * p.2))) ν := by
    intro γL γR hγL hγR
    refine (hlap (lt_min hγL hγR)).mono' (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.exp (-2 * π * (γL * p.1 + γR * p.2))).aestronglyMeasurable ?_
    filter_upwards [hae_nn] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hm1 : min γL γR * p.1 ≤ γL * p.1 := mul_le_mul_of_nonneg_right (min_le_left _ _) hp.1
    have hm2 : min γL γR * p.2 ≤ γR * p.2 := mul_le_mul_of_nonneg_right (min_le_right _ _) hp.2
    nlinarith [Real.pi_pos]
  have h1 := hint_pair hβL hβR
  have h2' := hint_pair (inv_pos.mpr hβL) (inv_pos.mpr hβR)
  have h2 : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 / βL + p.2 / βR))) ν := by
    convert h2' using 1
    ext p; simp [div_eq_mul_inv, mul_comm]
  refine ⟨h1, h2, ?_⟩
  unfold spinThermalX
  exact h1.sub (h2.const_mul _)

private lemma spinZHatC_ofReal_eq (a : ℝ) (ν : Measure (ℝ × ℝ))
    {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    spinZHatC a ν (βL : ℂ) (βR : ℂ) =
      (((spinVacuumV a βL βR +
        ∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν) : ℝ) : ℂ) := by
  unfold spinZHatC spinVacuumV spinVacuumQ
  push_cast
  have h1 : Complex.exp (π * (a : ℂ) * ((βL : ℂ) + (βR : ℂ))) *
        (1 - Complex.exp (-2 * π * (βL : ℂ))) * (1 - Complex.exp (-2 * π * (βR : ℂ))) =
      ((Real.exp (π * a * βL) * (1 - Real.exp (-2 * π * βL)) *
        (Real.exp (π * a * βR) * (1 - Real.exp (-2 * π * βR))) : ℝ) : ℂ) := by
    have he1 : Complex.exp (π * (a : ℂ) * ((βL : ℂ) + (βR : ℂ))) =
        ((Real.exp (π * a * βL) * Real.exp (π * a * βR) : ℝ) : ℂ) := by
      rw [show (π : ℂ) * (a : ℂ) * ((βL : ℂ) + (βR : ℂ)) =
          ((π * a * βL + π * a * βR : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp, Real.exp_add]
      push_cast; rfl
    have he2 : (1 - Complex.exp (-2 * π * (βL : ℂ))) = ((1 - Real.exp (-2 * π * βL) : ℝ) : ℂ) := by
      rw [show -(2 : ℂ) * π * (βL : ℂ) = ((-2 * π * βL : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp]
      push_cast; rfl
    have he3 : (1 - Complex.exp (-2 * π * (βR : ℂ))) = ((1 - Real.exp (-2 * π * βR) : ℝ) : ℂ) := by
      rw [show -(2 : ℂ) * π * (βR : ℂ) = ((-2 * π * βR : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp]
      push_cast; rfl
    rw [he1, he2, he3]
    push_cast; ring
  have h2 : (∫ p : ℝ × ℝ, Complex.exp (-2 * π * ((βL : ℂ) * (p.1 : ℂ) + (βR : ℂ) * (p.2 : ℂ))) ∂ν) =
      ((∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν : ℝ) : ℂ) := by
    have hfun : (fun p : ℝ × ℝ =>
        Complex.exp (-2 * π * ((βL : ℂ) * (p.1 : ℂ) + (βR : ℂ) * (p.2 : ℂ)))) =
        fun p : ℝ × ℝ => ((Real.exp (-2 * π * (βL * p.1 + βR * p.2)) : ℝ) : ℂ) := by
      ext p
      rw [show -(2 : ℂ) * π * ((βL : ℂ) * (p.1 : ℂ) + (βR : ℂ) * (p.2 : ℂ)) =
          ((-2 * π * (βL * p.1 + βR * p.2) : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp]
    rw [hfun]
    simpa only [← Complex.coe_algebraMap] using
      (integral_ofReal (f := fun p : ℝ × ℝ => Real.exp (-2 * π * (βL * p.1 + βR * p.2))) (μ := ν))
  rw [h1, h2]
  push_cast; ring

private lemma spinZHatC_crossing_ofReal_iff (a : ℝ) {ν : Measure (ℝ × ℝ)}
    (hsupp : ν ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) = 0)
    (hlap : ∀ {β : ℝ}, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    spinZHatC a ν (βL : ℂ) (βR : ℂ) -
        ((βL : ℂ) * (βR : ℂ)) ^ (-(1 / 2 : ℂ)) * spinZHatC a ν (βL⁻¹ : ℂ) (βR⁻¹ : ℂ) = 0 ↔
      ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν = -spinThermalXVac a βL βR := by
  have hint := spinThermalX_integrable hsupp hlap hβL hβR
  have hcpow : ((βL : ℂ) * (βR : ℂ)) ^ (-(1 / 2 : ℂ)) =
      (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have hmul : (βL : ℂ) * (βR : ℂ) = ((βL * βR : ℝ) : ℂ) := by push_cast; rfl
    have hexp : -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hmul, hexp, ← Complex.ofReal_cpow (mul_pos hβL hβR).le]
  have hL : (βL : ℂ)⁻¹ = ((βL⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hR : (βR : ℂ)⁻¹ = ((βR⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [spinZHatC_ofReal_eq a ν hβL hβR, hL, hR,
    spinZHatC_ofReal_eq a ν (inv_pos.mpr hβL) (inv_pos.mpr hβR), hcpow]
  have hsub_int :
      (∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) *
          (∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL⁻¹ * p.1 + βR⁻¹ * p.2)) ∂ν) =
        ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν := by
    have h2eq : (fun p : ℝ × ℝ => Real.exp (-2 * π * (βL⁻¹ * p.1 + βR⁻¹ * p.2))) =
        fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 / βL + p.2 / βR)) := by
      ext p; simp [div_eq_mul_inv, mul_comm]
    rw [h2eq, ← integral_const_mul, ← integral_sub hint.1 (hint.2.1.const_mul _)]
    rfl
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_sub,
    Complex.ofReal_eq_zero]
  have halg : spinVacuumV a βL βR + (∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ∂ν) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) *
          (spinVacuumV a βL⁻¹ βR⁻¹ + ∫ p : ℝ × ℝ, Real.exp (-2 * π * (βL⁻¹ * p.1 + βR⁻¹ * p.2)) ∂ν) =
      spinThermalXVac a βL βR + ∫ p : ℝ × ℝ, spinThermalX βL βR p.1 p.2 ∂ν := by
    have hvac : spinVacuumV a βL βR - (βL * βR) ^ (-(1 / 2 : ℝ)) * spinVacuumV a βL⁻¹ βR⁻¹ =
        spinThermalXVac a βL βR := by
      unfold spinThermalXVac spinVacuumV spinVacuumQ
      rw [← one_div βL, ← one_div βR]
    linarith [hsub_int, hvac]
  rw [halg]
  constructor
  · intro h; linarith
  · intro h; linarith

private lemma spin_diffStrip_crossing_analyticOnNhd (a : ℝ) {ν : Measure (ℝ × ℝ)}
    (hsupp : ν ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ) = 0)
    (hlap : ∀ {β : ℝ}, 0 < β → Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * β * (p.1 + p.2))) ν)
    {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (fun w : ℂ =>
      spinZHatC a ν ((x : ℂ) + w) ((x : ℂ) - w) -
        (((x : ℂ) + w) * ((x : ℂ) - w)) ^ (-(1 / 2 : ℂ)) *
          spinZHatC a ν ((x : ℂ) + w)⁻¹ ((x : ℂ) - w)⁻¹) {w : ℂ | |w.re| < x} := by
  have hU := spin_diffStrip_isOpen x
  have hpos_pm : ∀ w ∈ {w : ℂ | |w.re| < x},
      0 < ((x : ℂ) + w).re ∧ 0 < ((x : ℂ) - w).re := fun w hw => by
    change |w.re| < x at hw
    have hlt := abs_lt.mp hw
    simp [Complex.add_re, Complex.sub_re]
    exact ⟨by linarith, by linarith⟩
  have hdiff_p : DifferentiableOn ℂ (fun w : ℂ => (x : ℂ) + w) {w : ℂ | |w.re| < x} :=
    (differentiableOn_const _).add differentiableOn_id
  have hdiff_m : DifferentiableOn ℂ (fun w : ℂ => (x : ℂ) - w) {w : ℂ | |w.re| < x} :=
    (differentiableOn_const _).sub differentiableOn_id
  have hdiff_pinv : DifferentiableOn ℂ (fun w : ℂ => ((x : ℂ) + w)⁻¹) {w : ℂ | |w.re| < x} := by
    intro w hw
    refine (hdiff_p.differentiableAt (hU.mem_nhds hw)).inv ?_ |>.differentiableWithinAt
    intro h0
    have := (hpos_pm w hw).1
    simp [h0] at this
  have hdiff_minv : DifferentiableOn ℂ (fun w : ℂ => ((x : ℂ) - w)⁻¹) {w : ℂ | |w.re| < x} := by
    intro w hw
    refine (hdiff_m.differentiableAt (hU.mem_nhds hw)).inv ?_ |>.differentiableWithinAt
    intro h0
    have := (hpos_pm w hw).2
    simp [h0] at this
  have hdiff1 : DifferentiableOn ℂ (fun w => spinZHatC a ν ((x : ℂ) + w) ((x : ℂ) - w))
      {w : ℂ | |w.re| < x} :=
    spin_zHatC_comp_differentiableOn hsupp hlap hU hdiff_p hdiff_m hpos_pm
  have hdiff2 : DifferentiableOn ℂ (fun w => spinZHatC a ν ((x : ℂ) + w)⁻¹ ((x : ℂ) - w)⁻¹)
      {w : ℂ | |w.re| < x} :=
    spin_zHatC_comp_differentiableOn hsupp hlap hU hdiff_pinv hdiff_minv
      (fun w hw => ⟨spin_inv_re_pos (hpos_pm w hw).1, spin_inv_re_pos (hpos_pm w hw).2⟩)
  have hdiff_pref : DifferentiableOn ℂ
      (fun w : ℂ => (((x : ℂ) + w) * ((x : ℂ) - w)) ^ (-(1 / 2 : ℂ))) {w : ℂ | |w.re| < x} :=
    DifferentiableOn.cpow_const (hdiff_p.mul hdiff_m) fun w hw =>
      Complex.mem_slitPlane_iff.mpr (Or.inl (spin_prod_re_pos_on_diffStrip hx hw))
  exact (hdiff1.sub (hdiff_pref.mul hdiff2)).analyticOnNhd hU

/-- **Theorem S1 (`spinnotes:S1`(a), Crossing).** -/
theorem spinS1a : SpinS1a := by
  intro a ha ν hsupp hlap
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Separate holomorphy on `{Re z > 0}²`
    refine ⟨fun z₂ hz₂ => ?_, fun z₁ hz₁ => ?_⟩
    · exact spin_zHatC_comp_differentiableOn hsupp hlap spin_rhp_isOpen
        differentiableOn_id (differentiableOn_const z₂) fun z₁ hz₁ => ⟨hz₁, hz₂⟩
    · exact spin_zHatC_comp_differentiableOn hsupp hlap spin_rhp_isOpen
        (differentiableOn_const z₁) differentiableOn_id fun z₂ hz₂ => ⟨hz₁, hz₂⟩
  · -- Part 2: Euclidean `S`-invariance ↔ independent-temperature real crossing
    constructor
    · intro hEuclid βL βR hβL hβR
      set x : ℝ := (βL + βR) / 2
      set u : ℝ := (βL - βR) / 2
      have hx : 0 < x := by dsimp [x]; linarith
      have hu_lt : |u| < x := by
        rw [abs_lt]
        dsimp [u, x]
        constructor <;> linarith
      have han := spin_diffStrip_crossing_analyticOnNhd a hsupp hlap hx
      have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
          spinZHatC a ν ((x : ℂ) + w) ((x : ℂ) - w) -
            (((x : ℂ) + w) * ((x : ℂ) - w)) ^ (-(1 / 2 : ℂ)) *
              spinZHatC a ν ((x : ℂ) + w)⁻¹ ((x : ℂ) - w)⁻¹ = 0 := by
        have htend : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · have hcont : Continuous (fun y : ℝ => (y : ℂ) * Complex.I) := by fun_prop
            have h0 : (fun y : ℝ => (y : ℂ) * Complex.I) 0 = (0 : ℂ) := by simp
            simpa [h0] using hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          · refine eventually_nhdsWithin_of_forall fun y hy => ?_
            exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hy) Complex.I_ne_zero
        refine htend.frequently (Filter.Eventually.frequently (eventually_nhdsWithin_of_forall fun y _ => ?_))
        set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
        have hz_re : 0 < z.re := by simp [z, hx]
        have hconj : (x : ℂ) - (y : ℂ) * Complex.I = starRingEnd ℂ z := by
          apply Complex.ext <;> simp [z]
        have hz_eq := hEuclid z hz_re
        have haddz : (x : ℂ) + (y : ℂ) * Complex.I = z := rfl
        calc spinZHatC a ν ((x : ℂ) + (y : ℂ) * Complex.I) ((x : ℂ) - (y : ℂ) * Complex.I) -
              (((x : ℂ) + (y : ℂ) * Complex.I) * ((x : ℂ) - (y : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ)) *
                spinZHatC a ν ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ((x : ℂ) - (y : ℂ) * Complex.I)⁻¹
            = spinZHatC a ν z (starRingEnd ℂ z) -
                (z * starRingEnd ℂ z) ^ (-(1 / 2 : ℂ)) *
                  spinZHatC a ν z⁻¹ (starRingEnd ℂ z)⁻¹ := by rw [haddz, hconj]
          _ = 0 := by rw [hz_eq, sub_self]
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (spin_diffStrip_convex x).isPreconnected (by simp [hx]) hfreq
      have h0u := hzero (show (u : ℂ) ∈ {w : ℂ | |w.re| < x} by simpa using hu_lt)
      have hadd : (x : ℂ) + (u : ℂ) = (βL : ℂ) := by
        dsimp [x, u]; push_cast; ring
      have hsub : (x : ℂ) - (u : ℂ) = (βR : ℂ) := by
        dsimp [x, u]; push_cast; ring
      have h0u' : spinZHatC a ν ((x : ℂ) + (u : ℂ)) ((x : ℂ) - (u : ℂ)) -
          (((x : ℂ) + (u : ℂ)) * ((x : ℂ) - (u : ℂ))) ^ (-(1 / 2 : ℂ)) *
            spinZHatC a ν ((x : ℂ) + (u : ℂ))⁻¹ ((x : ℂ) - (u : ℂ))⁻¹ = 0 := h0u
      rw [hadd, hsub] at h0u'
      exact (spinZHatC_crossing_ofReal_iff a hsupp hlap hβL hβR).1 h0u'
    · intro hReal z hz
      set x : ℝ := z.re
      set y : ℝ := z.im
      have hx : 0 < x := hz
      have han := spin_diffStrip_crossing_analyticOnNhd a hsupp hlap hx
      have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
          spinZHatC a ν ((x : ℂ) + w) ((x : ℂ) - w) -
            (((x : ℂ) + w) * ((x : ℂ) - w)) ^ (-(1 / 2 : ℂ)) *
              spinZHatC a ν ((x : ℂ) + w)⁻¹ ((x : ℂ) - w)⁻¹ = 0 := by
        have htend : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          · exact eventually_nhdsWithin_of_forall fun u hu => Complex.ofReal_ne_zero.mpr hu
        refine htend.frequently (Filter.Eventually.frequently ?_)
        have hIoo : Set.Ioo (-x) x ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith, hx⟩
        filter_upwards [nhdsWithin_le_nhds hIoo] with u hu
        have hβL : 0 < x + u := by linarith [hu.1]
        have hβR : 0 < x - u := by linarith [hu.2]
        have hadd : (x : ℂ) + (u : ℂ) = ((x + u : ℝ) : ℂ) := by push_cast; rfl
        have hsub : (x : ℂ) - (u : ℂ) = ((x - u : ℝ) : ℂ) := by push_cast; rfl
        change spinZHatC a ν ((x : ℂ) + (u : ℂ)) ((x : ℂ) - (u : ℂ)) -
            (((x : ℂ) + (u : ℂ)) * ((x : ℂ) - (u : ℂ))) ^ (-(1 / 2 : ℂ)) *
              spinZHatC a ν ((x : ℂ) + (u : ℂ))⁻¹ ((x : ℂ) - (u : ℂ))⁻¹ = 0
        rw [hadd, hsub]
        exact (spinZHatC_crossing_ofReal_iff a hsupp hlap hβL hβR).2 (hReal hβL hβR)
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (spin_diffStrip_convex x).isPreconnected (by simp [hx]) hfreq
      have hw_mem : ((y : ℂ) * Complex.I) ∈ {w : ℂ | |w.re| < x} := by
        simpa using hx
      have h0w : spinZHatC a ν ((x : ℂ) + (y : ℂ) * Complex.I) ((x : ℂ) - (y : ℂ) * Complex.I) -
          (((x : ℂ) + (y : ℂ) * Complex.I) * ((x : ℂ) - (y : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ)) *
            spinZHatC a ν ((x : ℂ) + (y : ℂ) * Complex.I)⁻¹ ((x : ℂ) - (y : ℂ) * Complex.I)⁻¹ = 0 :=
        hzero hw_mem
      have hadd : (x : ℂ) + (y : ℂ) * Complex.I = z := by
        apply Complex.ext <;> simp [x, y]
      have hsub : (x : ℂ) - (y : ℂ) * Complex.I = starRingEnd ℂ z := by
        apply Complex.ext <;> simp [x, y]
      rw [hadd, hsub] at h0w
      exact sub_eq_zero.mp h0w
  · -- Part 3: Independent-temperature crossing ↔ odd two-variable Laguerre moments
    have hνB : ν (spinConeB 0)ᶜ = 0 := by
      have heq : spinConeB 0 = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
        ext p; simp [spinConeB]
      rwa [heq]
    have hθ0 : (0 : ℝ) < 1 / 2 := by norm_num
    have hθ1 : (1 / 2 : ℝ) < 1 := by norm_num
    have hint_s : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta (1 / 2) * (p.1 + p.2))) ν :=
      hlap (sTheta_pos hθ0 hθ1)
    have hiff := spin_tensor_cayley_iff ha le_rfl hθ0 hθ1 hνB hint_s
    have hvac_eq : ∀ m n : ℕ,
        -spinVacT a (fun q => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) =
          -(∫ p : ℝ × ℝ, lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2) *
            spinV1 a p.1 * spinV1 a p.2) := by
      intro m n
      simp only [spinVacT, spinPhiVac, spinLiftTToR]
    constructor
    · intro hReal m n hmn
      have hloc : ∀ βL βR : ℝ, sTheta (1 / 2) < βL → βL < 1 / sTheta (1 / 2) →
          sTheta (1 / 2) < βR → βR < 1 / sTheta (1 / 2) →
          ∫ q : ℝ × ℝ, spinThermalX βL βR q.1 q.2 ∂ν = -spinThermalXVac a βL βR := by
        intro βL βR hL1 _ hR1 _
        exact hReal ((sTheta_pos hθ0 hθ1).trans hL1) ((sTheta_pos hθ0 hθ1).trans hR1)
      simpa only [hvac_eq m n] using hiff.1 hloc m n hmn
    · intro hmom βL βR hβL hβR
      have hmom' : ∀ m n : ℕ, Odd (m + n) →
          ∫ q : ℝ × ℝ, lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2 ∂ν =
            -spinVacT a (fun q => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) := by
        intro m n hmn
        rw [hvac_eq m n]
        exact hmom m n hmn
      have hloc := hiff.2 hmom'
      have hs_lt_1 : sTheta (1 / 2) < 1 := by
        unfold sTheta; norm_num
      have h1_lt_sinv : (1 : ℝ) < 1 / sTheta (1 / 2) := by
        unfold sTheta; norm_num
      have hstep1 : ∀ {βR' : ℝ}, sTheta (1 / 2) < βR' → βR' < 1 / sTheta (1 / 2) →
          ∀ z₁ : ℂ, 0 < z₁.re →
            spinZHatC a ν z₁ (βR' : ℂ) -
              (z₁ * (βR' : ℂ)) ^ (-(1 / 2 : ℂ)) * spinZHatC a ν z₁⁻¹ ((βR' : ℝ)⁻¹ : ℂ) = 0 := by
        intro βR' hR1 hR2 z₁ hz₁
        have hβR' : 0 < βR' := (sTheta_pos hθ0 hθ1).trans hR1
        have hdiff_1 : DifferentiableOn ℂ (fun z : ℂ => spinZHatC a ν z (βR' : ℂ)) {z : ℂ | 0 < z.re} :=
          spin_zHatC_comp_differentiableOn hsupp hlap spin_rhp_isOpen
            differentiableOn_id (differentiableOn_const _) fun z hz => ⟨hz, hβR'⟩
        have hdiff_2 : DifferentiableOn ℂ (fun z : ℂ => spinZHatC a ν z⁻¹ ((βR' : ℝ)⁻¹ : ℂ))
            {z : ℂ | 0 < z.re} :=
          spin_zHatC_comp_differentiableOn hsupp hlap spin_rhp_isOpen
            spin_inv_differentiableOn_rhp (differentiableOn_const _) fun z hz =>
              ⟨spin_inv_re_pos hz, by simpa using inv_pos.mpr hβR'⟩
        have hdiff_pref : DifferentiableOn ℂ (fun z : ℂ => (z * (βR' : ℂ)) ^ (-(1 / 2 : ℂ)))
            {z : ℂ | 0 < z.re} :=
          DifferentiableOn.cpow_const (differentiableOn_id.mul_const _) fun z hz => by
            refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
            simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            exact mul_pos hz hβR'
        have han : AnalyticOnNhd ℂ (fun z : ℂ => spinZHatC a ν z (βR' : ℂ) -
            (z * (βR' : ℂ)) ^ (-(1 / 2 : ℂ)) * spinZHatC a ν z⁻¹ ((βR' : ℝ)⁻¹ : ℂ))
            {z : ℂ | 0 < z.re} :=
          (hdiff_1.sub (hdiff_pref.mul hdiff_2)).analyticOnNhd spin_rhp_isOpen
        have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
            spinZHatC a ν z (βR' : ℂ) -
              (z * (βR' : ℂ)) ^ (-(1 / 2 : ℂ)) * spinZHatC a ν z⁻¹ ((βR' : ℝ)⁻¹ : ℂ) = 0 := by
          have htend : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
            refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
            · simpa [Complex.ofReal_one] using
                Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            · exact eventually_nhdsWithin_of_forall fun u hu => Complex.ofReal_injective.ne hu
          refine htend.frequently (Filter.Eventually.frequently ?_)
          have hIoo : Set.Ioo (sTheta (1 / 2)) (1 / sTheta (1 / 2)) ∈ 𝓝 (1 : ℝ) :=
            isOpen_Ioo.mem_nhds ⟨hs_lt_1, h1_lt_sinv⟩
          filter_upwards [nhdsWithin_le_nhds hIoo] with u hu
          have hu_pos : 0 < u := (sTheta_pos hθ0 hθ1).trans hu.1
          exact (spinZHatC_crossing_ofReal_iff a hsupp hlap hu_pos hβR').2
            (hloc u βR' hu.1 hu.2 hR1 hR2)
        exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero spin_rhp_isPreconnected
          (by simp) hfreq hz₁
      have hdiff_1' : DifferentiableOn ℂ (fun z : ℂ => spinZHatC a ν (βL : ℂ) z) {z : ℂ | 0 < z.re} :=
        spin_zHatC_comp_differentiableOn hsupp hlap spin_rhp_isOpen
          (differentiableOn_const _) differentiableOn_id fun z hz => ⟨hβL, hz⟩
      have hdiff_2' : DifferentiableOn ℂ (fun z : ℂ => spinZHatC a ν (βL⁻¹ : ℂ) z⁻¹)
          {z : ℂ | 0 < z.re} :=
        spin_zHatC_comp_differentiableOn hsupp hlap spin_rhp_isOpen
          (differentiableOn_const _) spin_inv_differentiableOn_rhp fun z hz =>
            ⟨by simpa using inv_pos.mpr hβL, spin_inv_re_pos hz⟩
      have hdiff_pref' : DifferentiableOn ℂ (fun z : ℂ => ((βL : ℂ) * z) ^ (-(1 / 2 : ℂ)))
          {z : ℂ | 0 < z.re} :=
        DifferentiableOn.cpow_const (differentiableOn_id.const_mul _) fun z hz => by
          refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          exact mul_pos hβL hz
      have han' : AnalyticOnNhd ℂ (fun z : ℂ => spinZHatC a ν (βL : ℂ) z -
          ((βL : ℂ) * z) ^ (-(1 / 2 : ℂ)) * spinZHatC a ν (βL⁻¹ : ℂ) z⁻¹) {z : ℂ | 0 < z.re} :=
        (hdiff_1'.sub (hdiff_pref'.mul hdiff_2')).analyticOnNhd spin_rhp_isOpen
      have hfreq' : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
          spinZHatC a ν (βL : ℂ) z -
            ((βL : ℂ) * z) ^ (-(1 / 2 : ℂ)) * spinZHatC a ν (βL⁻¹ : ℂ) z⁻¹ = 0 := by
        have htend : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · simpa [Complex.ofReal_one] using
              Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          · exact eventually_nhdsWithin_of_forall fun u hu => Complex.ofReal_injective.ne hu
        refine htend.frequently (Filter.Eventually.frequently ?_)
        have hIoo : Set.Ioo (sTheta (1 / 2)) (1 / sTheta (1 / 2)) ∈ 𝓝 (1 : ℝ) :=
          isOpen_Ioo.mem_nhds ⟨hs_lt_1, h1_lt_sinv⟩
        filter_upwards [nhdsWithin_le_nhds hIoo] with u hu
        have h1 := hstep1 hu.1 hu.2 (βL : ℂ) (by simpa using hβL)
        have hbinv : ((βL : ℂ))⁻¹ = (βL⁻¹ : ℂ) := by push_cast; rfl
        simpa [hbinv] using h1
      have hfinal := han'.eqOn_zero_of_preconnected_of_frequently_eq_zero spin_rhp_isPreconnected
        (by simp) hfreq' (show (βR : ℂ) ∈ {z : ℂ | 0 < z.re} by simpa using hβR)
      have hbinvL : ((βL : ℂ))⁻¹ = (βL⁻¹ : ℂ) := by push_cast; rfl
      rw [hbinvL] at hfinal
      exact (spinZHatC_crossing_ofReal_iff a hsupp hlap hβL hβR).1 hfinal

/-! ### Section 2: `SpinS1d` and `SpinS1e` via `spinDW` and `spinDSD` -/

/-- **Theorem S1 (`spinnotes:S1`(d), Weak duality).** -/
theorem spinS1d : SpinS1d := by
  intro c T hc Φ hΦ ⟨meas, hsupp⟩
  have ha : 2 ≤ (c - 1) / 12 := by linarith
  set T' : ℝ := max T 1
  have hT'_pos : 0 < T' := lt_max_of_lt_right one_pos
  have hnonneg : ∀ p ∈ liouvilleCone T', 0 ≤ spinEvalT Φ p := fun p hp =>
    hΦ.2.2 p ⟨hp.1, hp.2.1, (le_max_left T 1).trans hp.2.2⟩
  have hae : ∀ᵐ p ∂meas.ν, 0 ≤ spinEvalT Φ p := by
    have hnot : ∀ᵐ p ∂meas.ν, p ∉ (liouvilleCone T)ᶜ :=
      measure_eq_zero_iff_ae_notMem.1 hsupp
    filter_upwards [hnot] with p hp
    exact hΦ.2.2 p (not_not.mp hp)
  have hweak := (spinDW ha meas hΦ.1 hT'_pos hnonneg).2.2.1 hae
  linarith [hΦ.2.1]

private lemma spinCertifiedClass_iff_exists_lift {a : ℝ} {Φ : ℝ × ℝ → ℝ} :
    SpinCertifiedClass a Φ ↔ ∃ Ψ : ℝ × ℝ → ℝ, SpinCertifiedT a Ψ ∧ Φ = spinLiftTToR Ψ := by
  constructor
  · intro hΦ
    unfold SpinCertifiedClass at hΦ
    refine Submodule.span_induction
      (p := fun f _ => ∃ Ψ : ℝ × ℝ → ℝ, SpinCertifiedT a Ψ ∧ f = spinLiftTToR Ψ)
      ?_ ?_ ?_ ?_ hΦ
    · rintro _ (⟨m, n, hmn, rfl⟩ | ⟨β₀, hβ₀0, hβ₀1, rfl⟩)
      · exact ⟨spinOddLagBasisT m n,
          Submodule.subset_span (Or.inl ⟨m, n, hmn, rfl⟩), rfl⟩
      · refine ⟨fun p => hMaj a β₀ (p.1 + p.2),
          Submodule.subset_span (Or.inr ⟨β₀, hβ₀0, hβ₀1, rfl⟩), ?_⟩
        ext r; unfold spinLiftTToR spinRadialLift; rfl
    · exact ⟨0, Submodule.zero_mem _, rfl⟩
    · rintro f g _ _ ⟨Ψ₁, h₁, rfl⟩ ⟨Ψ₂, h₂, rfl⟩
      exact ⟨Ψ₁ + Ψ₂, Submodule.add_mem _ h₁ h₂, rfl⟩
    · rintro r f _ ⟨Ψ, hΨ, rfl⟩
      exact ⟨r • Ψ, Submodule.smul_mem _ r hΨ, rfl⟩
  · rintro ⟨Ψ, hΨ, rfl⟩
    unfold SpinCertifiedT at hΨ
    refine Submodule.span_induction
      (p := fun Ψ _ => SpinCertifiedClass a (spinLiftTToR Ψ))
      ?_ ?_ ?_ ?_ hΨ
    · rintro _ (⟨m, n, hmn, rfl⟩ | ⟨β₀, hβ₀0, hβ₀1, rfl⟩)
      · exact Submodule.subset_span (Or.inl ⟨m, n, hmn, rfl⟩)
      · have heq : spinLiftTToR (fun p : ℝ × ℝ => hMaj a β₀ (p.1 + p.2)) =
            spinRadialLift (hMaj a β₀) := by
          ext r; unfold spinLiftTToR spinRadialLift; rfl
        rw [heq]
        exact Submodule.subset_span (Or.inr ⟨β₀, hβ₀0, hβ₀1, rfl⟩)
    · exact Submodule.zero_mem _
    · rintro f g _ _ hf hg
      exact Submodule.add_mem _ hf hg
    · rintro r f _ hf
      exact Submodule.smul_mem _ r hf

private lemma spin_coneSlice_duality_and_attainment {a : ℝ} (ha : 2 ≤ a)
    {Ω₀ : Set (ℝ × ℝ)} (hΩ₀_closed : IsClosed Ω₀) (hΩ₀_swap : IsSwapInvariantSet Ω₀)
    (hΩ₀_sub : Ω₀ ⊆ spinConeB 0) (hTpos : 0 < spinCertifiedThr a Ω₀ ∅) :
    spinTauMax a (spinConeSlice Ω₀) = spinCertifiedThr a Ω₀ ∅ ∧
    ∃ meas : SpinCrossingMeasure a,
      meas.ν (spinConeSlice Ω₀ (spinTauMax a (spinConeSlice Ω₀)))ᶜ = 0 := by
  have hsd := (spinDSD.1 ha le_rfl hΩ₀_closed hΩ₀_swap hΩ₀_sub
    isCompact_empty (fun _ h => absurd h (notMem_empty _))
    (fun _ h => absurd h (notMem_empty _)) hTpos)
  have hset_eq :
      {τ : ℝ | 0 < τ ∧ ∃ meas : SpinCrossingMeasure a, meas.ν (spinConeSlice Ω₀ τ)ᶜ = 0} =
      {τ : ℝ | 0 < τ ∧ Nonempty (SpinCrossingMeasureOn a (∅ ∪ spinConeSlice Ω₀ τ))} := by
    ext τ
    simp only [Set.mem_ofPred_eq, Set.empty_union]
    constructor
    · rintro ⟨hτ, meas, hsupp⟩
      exact ⟨hτ, ⟨{
        ν := meas.ν
        supp := hsupp
        finite_laplace := meas.finite_laplace
        crossing := meas.crossing
      }⟩⟩
    · rintro ⟨hτ, ⟨meas⟩⟩
      exact ⟨hτ, meas.toQuadrant (Set.inter_subset_left.trans hΩ₀_sub), meas.supp⟩
  have htau : spinTauMax a (spinConeSlice Ω₀) = spinCertifiedThr a Ω₀ ∅ := by
    unfold spinTauMax
    rw [hset_eq]
    exact hsd.1.csSup_eq
  refine ⟨htau, ?_⟩
  rw [htau]
  obtain ⟨meas, _⟩ := hsd.2.1
  have hsupp : meas.ν (spinConeSlice Ω₀ (spinCertifiedThr a Ω₀ ∅))ᶜ = 0 := by
    simpa [Set.empty_union] using meas.supp
  let meas' : SpinCrossingMeasureOn a (spinConeSlice Ω₀ (spinCertifiedThr a Ω₀ ∅)) :=
    ⟨meas.ν, hsupp, meas.finite_laplace, meas.crossing⟩
  exact ⟨meas'.toQuadrant (Set.inter_subset_left.trans hΩ₀_sub), hsupp⟩

/-- **Theorem S1 (`spinnotes:S1`(e), Exact duality and attainment).** -/
theorem spinS1e : SpinS1e := by
  intro c hc
  set a : ℝ := (c - 1) / 12
  have ha : 2 ≤ a := by dsimp [a]; linarith
  refine ⟨?_, ?_⟩
  · intro _
    have hsd2 := spinDSD.2 ha
    have hTpos : 0 < spinCertifiedThr a (spinConeB 0) ∅ := by
      linarith [hsd2.1, hsd2.2.1, hsd2.2.2]
    obtain ⟨htau, meas, hsupp⟩ := spin_coneSlice_duality_and_attainment ha
      (isClosed_spinConeB 0) (isSwapInvariantSet_spinConeB 0) Subset.rfl hTpos
    have hslice_eq : spinConeSlice (spinConeB 0) = liouvilleCone := by
      ext τ p
      exact (congrArg (p ∈ ·) (spinConeSlice_quadrant τ)).to_iff
    rw [hslice_eq] at htau hsupp
    refine ⟨?_, ?_, meas, hsupp⟩
    · unfold spinDeltaL spinDeltaSpin
      rw [hsd2.2.1]
    · unfold spinDeltaL
      rw [hsd2.2.1, hsd2.2.2, ← htau]
  · intro hT_pos
    have hΩ₀_sub : integerSpinCone 0 ⊆ spinConeB 0 := fun p hp => by
      simp only [spinConeB, neg_zero, Set.mem_ofPred_eq]
      exact ⟨hp.1.1, hp.1.2.1⟩
    have hΩ₀_closed : IsClosed (integerSpinCone 0) := by
      have heq : integerSpinCone 0 =
          liouvilleCone 0 ∩ ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.range (Int.cast : ℤ → ℝ)) := by
        ext p
        simp [integerSpinCone, eq_comm]
      rw [heq]
      refine ((isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_const (continuous_fst.add continuous_snd)))).inter ?_
      exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage
        (continuous_fst.sub continuous_snd)
    have hΩ₀_swap : IsSwapInvariantSet (integerSpinCone 0) := by
      rintro p ⟨⟨h1, h2, h3⟩, j, hj⟩
      change (p.swap ∈ liouvilleCone 0) ∧ ∃ k : ℤ, p.swap.1 - p.swap.2 = (k : ℝ)
      refine ⟨⟨h2, h1, by simp [Prod.swap]; linarith⟩, -j, ?_⟩
      simp only [Prod.swap, Int.cast_neg]
      linarith
    have hslice_int : ∀ {τ : ℝ}, 0 ≤ τ → spinConeSlice (integerSpinCone 0) τ = integerSpinCone τ := by
      intro τ hτ
      ext p
      simp only [spinConeSlice, mem_inter_iff, mem_ofPred_eq, integerSpinCone, liouvilleCone]
      constructor
      · rintro ⟨⟨⟨h1, h2, _⟩, hj⟩, hsum⟩
        exact ⟨⟨h1, h2, hsum⟩, hj⟩
      · rintro ⟨⟨h1, h2, hsum⟩, hj⟩
        exact ⟨⟨⟨h1, h2, hτ.trans hsum⟩, hj⟩, hsum⟩
    have hthr_eq : spinThrInf (SpinCertifiedClass a) integerSpinCone a =
        spinCertifiedThr a (integerSpinCone 0) ∅ := by
      unfold spinThrInf spinCertifiedThr
      congr 1
      ext T
      simp only [Set.mem_setOf_eq, Set.empty_union, SpinIsFeasible]
      constructor
      · rintro ⟨hT, Φ, hΦ, hvac, hpos⟩
        obtain ⟨Ψ, hΨ, rfl⟩ := spinCertifiedClass_iff_exists_lift.1 hΦ
        refine ⟨hT, Ψ, hΨ, hvac, fun p hp => ?_⟩
        rw [hslice_int hT.le] at hp
        have hp0 := hpos p hp
        have heval : spinEvalT (spinLiftTToR Ψ) p = Ψ p := by
          unfold spinEvalT spinLiftTToR
          rw [Real.sq_sqrt (by linarith [hp.1.1]), Real.sq_sqrt (by linarith [hp.1.2.1])]
          ring_nf
        rwa [← heval]
      · rintro ⟨hT, Ψ, hΨ, hvac, hpos⟩
        refine ⟨hT, spinLiftTToR Ψ, spinCertifiedClass_iff_exists_lift.2 ⟨Ψ, hΨ, rfl⟩, hvac,
          fun p hp => ?_⟩
        have hp' : p ∈ spinConeSlice (integerSpinCone 0) T := by rwa [hslice_int hT.le]
        have heval : spinEvalT (spinLiftTToR Ψ) p = Ψ p := by
          unfold spinEvalT spinLiftTToR
          rw [Real.sq_sqrt (by linarith [hp.1.1]), Real.sq_sqrt (by linarith [hp.1.2.1])]
          ring_nf
        rw [heval]
        exact hpos p hp'
    rw [hthr_eq] at hT_pos ⊢
    obtain ⟨htau, meas, hsupp⟩ := spin_coneSlice_duality_and_attainment ha
      hΩ₀_closed hΩ₀_swap hΩ₀_sub hT_pos
    have htau_max : spinTauMax a (spinConeSlice (integerSpinCone 0)) = spinTauMax a integerSpinCone := by
      unfold spinTauMax
      congr 1
      ext τ
      constructor
      · rintro ⟨hτ, m, hm⟩
        refine ⟨hτ, m, ?_⟩
        rwa [← hslice_int hτ.le]
      · rintro ⟨hτ, m, hm⟩
        refine ⟨hτ, m, ?_⟩
        rwa [hslice_int hτ.le]
    rw [htau_max] at htau
    refine ⟨htau.symm, meas, ?_⟩
    rw [htau_max] at hsupp
    rwa [← hslice_int (htau.symm ▸ hT_pos).le]

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS1a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS1a

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS1d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS1d

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS1e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS1e

end FormalResearch.ModularBootstrap.Spin
