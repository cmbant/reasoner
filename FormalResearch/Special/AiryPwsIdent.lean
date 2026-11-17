module

public import FormalResearch.Special.AiryPwsConverse

/-!
# Theorem 3.1 `(b) ⇒ (a)`, test-function calculus

For a compactly supported smooth `Φ : ℝ → ℂ` put `ψ(ζ) = ∫ Φ(t) e^{iζt} dt` (`airyTestPsi`).

* `airyTestPsi_ibp`: `∫ Φ'(t) e^{iζt} dt = -iζ ψ(ζ)`;
* `airyTestPsi_decay`: `(1 + (Re ζ)²) |ψ(ζ)| ≤ D` uniformly for `0 ≤ Im ζ ≤ 1` (two integrations by parts);
* `continuous_airyTestPsi`;
* `airy_inversion`: `Φ(u) = (2π)⁻¹ ∫ ψ(ξ) e^{-iξu} dξ`, from Mathlib's Fourier inversion.

**Not formalised** here: the identification `f = f_E` (`AiryPwsIdent2`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real ContDiff FourierTransform

namespace FormalResearch.Special

/-- `ψ(ζ) = ∫ Φ(t) e^{iζt} dt`. -/
noncomputable def airyTestPsi (Φ : ℝ → ℂ) (ζ : ℂ) : ℂ := ∫ t : ℝ, Φ t * cexp (I * ζ * (t : ℂ))

lemma exists_supp_bound {Φ : ℝ → ℂ} (hc : HasCompactSupport Φ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, Φ t ≠ 0 → |t| ≤ R := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun t ht => ?_⟩
  have := hR (subset_tsupport _ ht)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma continuous_cexp_line (ζ : ℂ) : Continuous fun t : ℝ => cexp (I * ζ * (t : ℂ)) := by fun_prop

lemma integrable_mul_cexp_line {Φ : ℝ → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) (ζ : ℂ) :
    Integrable fun t : ℝ => Φ t * cexp (I * ζ * (t : ℂ)) :=
  (hΦ.mul (continuous_cexp_line ζ)).integrable_of_hasCompactSupport (hc.mul_right)

lemma airyTestPsi_ibp {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hc : HasCompactSupport Φ) (ζ : ℂ) :
    ∫ t : ℝ, deriv Φ t * cexp (I * ζ * (t : ℂ)) = -(I * ζ) * airyTestPsi Φ ζ := by
  have hd : Continuous (deriv Φ) := hΦ.continuous_deriv le_rfl
  have hcd : HasCompactSupport (deriv Φ) := hc.deriv
  have hcont := hΦ.continuous
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Φ t * cexp (I * ζ * (t : ℂ)))
      (deriv Φ t * cexp (I * ζ * (t : ℂ)) + Φ t * (cexp (I * ζ * (t : ℂ)) * (I * ζ))) t := by
    intro t
    have h1 : HasDerivAt Φ (deriv Φ t) t := ((hΦ.differentiable one_ne_zero) t).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => I * ζ * (t : ℂ)) (I * ζ) t := by
      simpa using ((hasDerivAt_id (t : ℝ)).ofReal_comp).const_mul (I * ζ)
    exact h1.mul h2.cexp
  have hi1 := integrable_mul_cexp_line hd hcd ζ
  have hi2 : Integrable fun t : ℝ => Φ t * (cexp (I * ζ * (t : ℂ)) * (I * ζ)) := by
    have := (integrable_mul_cexp_line hcont hc ζ).mul_const (I * ζ)
    simpa [mul_assoc] using this
  have hz : Tendsto (fun t : ℝ => Φ t * cexp (I * ζ * (t : ℂ))) (cocompact ℝ) (𝓝 0) := by
    have h2 := (hc.mul_right (f' := fun t : ℝ => cexp (I * ζ * (t : ℂ))))
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2
    exact tendsto_const_nhds.congr' h2.symm
  rw [cocompact_eq_atBot_atTop] at hz
  have := integral_of_hasDerivAt_of_tendsto hder (hi1.add hi2) (hz.mono_left le_sup_left)
    (hz.mono_left le_sup_right)
  rw [sub_zero, integral_add hi1 hi2] at this
  have h3 : ∫ t : ℝ, Φ t * (cexp (I * ζ * (t : ℂ)) * (I * ζ)) = I * ζ * airyTestPsi Φ ζ := by
    unfold airyTestPsi
    rw [← integral_const_mul]
    congr 1; funext t; ring
  rw [h3] at this
  linear_combination this

lemma norm_cexp_line (ζ : ℂ) (t : ℝ) : ‖cexp (I * ζ * (t : ℂ))‖ = Real.exp (-(ζ.im * t)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

lemma airyTestPsi_norm_le {Φ : ℝ → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) {R : ℝ}
    (hR : ∀ t, Φ t ≠ 0 → |t| ≤ R) {ζ : ℂ} (h0 : 0 ≤ ζ.im) (h1 : ζ.im ≤ 1) :
    ‖airyTestPsi Φ ζ‖ ≤ Real.exp R * ∫ t : ℝ, ‖Φ t‖ := by
  have hint : Integrable fun t : ℝ => ‖Φ t‖ := (hΦ.integrable_of_hasCompactSupport hc).norm
  unfold airyTestPsi
  rw [← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono
    (integrable_mul_cexp_line hΦ hc ζ).norm (hint.const_mul _) fun t => ?_)
  by_cases ht : Φ t = 0
  · simp [ht]
  · rw [norm_mul, norm_cexp_line, mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have := hR t ht
    have h2 : -(ζ.im * t) ≤ ζ.im * |t| := by nlinarith [neg_abs_le t, abs_nonneg t]
    nlinarith [abs_nonneg t]

lemma continuous_airyTestPsi {Φ : ℝ → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) :
    Continuous (airyTestPsi Φ) := by
  obtain ⟨R, hR0, hR⟩ := exists_supp_bound hc
  have hcont : Continuous (Function.uncurry fun (ζ : ℂ) (t : ℝ) => Φ t * cexp (I * ζ * (t : ℂ))) := by
    fun_prop
  have := continuous_parametric_integral_of_continuous (μ := volume) hcont
    (isCompact_Icc (a := -R) (b := R))
  refine this.congr fun ζ => ?_
  unfold airyTestPsi
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_)
  have : Φ t = 0 := by
    by_contra hne
    exact ht (abs_le.mp (hR t hne) |> fun h => ⟨h.1, h.2⟩)
  simp [this]

lemma airyTestPsi_ibp2 {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) (ζ : ℂ) :
    ∫ t : ℝ, deriv (deriv Φ) t * cexp (I * ζ * (t : ℂ)) = -ζ ^ 2 * airyTestPsi Φ ζ := by
  have h1 : ContDiff ℝ ∞ (deriv Φ) := (contDiff_infty_iff_deriv.mp hΦ).2
  rw [airyTestPsi_ibp (h1.of_le (by exact_mod_cast le_top)) hc.deriv]
  have e := airyTestPsi_ibp (hΦ.of_le (by exact_mod_cast le_top)) hc ζ
  rw [show airyTestPsi (deriv Φ) ζ = ∫ t : ℝ, deriv Φ t * cexp (I * ζ * (t : ℂ)) from rfl, e]
  linear_combination (ζ ^ 2 * airyTestPsi Φ ζ) * Complex.I_sq

/-- Uniform decay of `ψ` on the strip `0 ≤ Im ζ ≤ 1`. -/
lemma airyTestPsi_decay {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ζ : ℂ, 0 ≤ ζ.im → ζ.im ≤ 1 → (1 + ζ.re ^ 2) * ‖airyTestPsi Φ ζ‖ ≤ D := by
  have h1 : ContDiff ℝ ∞ (deriv Φ) := (contDiff_infty_iff_deriv.mp hΦ).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv Φ)) := (contDiff_infty_iff_deriv.mp h1).2
  have hc2 : HasCompactSupport (deriv (deriv Φ)) := hc.deriv.deriv
  obtain ⟨R, hR0, hR⟩ := exists_supp_bound hc
  obtain ⟨R2, hR20, hR2⟩ := exists_supp_bound hc2
  refine ⟨Real.exp R * (∫ t : ℝ, ‖Φ t‖) + Real.exp R2 * ∫ t : ℝ, ‖deriv (deriv Φ) t‖, by positivity, fun ζ h0 h1' => ?_⟩
  have hb1 := airyTestPsi_norm_le hΦ.continuous hc hR h0 h1'
  have hb2 := airyTestPsi_norm_le (h2.continuous) hc2 hR2 (ζ := ζ) h0 h1'
  have hib := airyTestPsi_ibp2 hΦ hc ζ
  have hP : ‖∫ t : ℝ, deriv (deriv Φ) t * cexp (I * ζ * (t : ℂ))‖ ≤
      Real.exp R2 * ∫ t : ℝ, ‖deriv (deriv Φ) t‖ := by
    have := airyTestPsi_norm_le (h2.continuous) hc2 hR2 (ζ := ζ) h0 h1'
    simpa [airyTestPsi] using this
  rw [hib, norm_mul, norm_neg, norm_pow] at hP
  have hz : ζ.re ^ 2 ≤ ‖ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg ζ.im]
  have hn := norm_nonneg (airyTestPsi Φ ζ)
  calc (1 + ζ.re ^ 2) * ‖airyTestPsi Φ ζ‖ = ‖airyTestPsi Φ ζ‖ + ζ.re ^ 2 * ‖airyTestPsi Φ ζ‖ := by ring
    _ ≤ ‖airyTestPsi Φ ζ‖ + ‖ζ‖ ^ 2 * ‖airyTestPsi Φ ζ‖ := by gcongr
    _ ≤ _ := add_le_add hb1 hP

lemma integrable_airyTestPsi {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    Integrable fun ξ : ℝ => airyTestPsi Φ (ξ : ℂ) := by
  obtain ⟨D, hD0, hD⟩ := airyTestPsi_decay hΦ hc
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul D)
    ((continuous_airyTestPsi hΦ.continuous hc).comp Complex.continuous_ofReal).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  have h := hD (ξ : ℂ) (by simp) (by simp)
  simp only [Complex.ofReal_re] at h
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-- Fourier inversion for a compactly supported smooth function, in the `e^{iζt}` normalisation. -/
theorem airy_inversion {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) (u : ℝ) :
    Φ u = (2 * π : ℝ)⁻¹ * ∫ ξ : ℝ, airyTestPsi Φ (ξ : ℂ) * cexp (-(I * (ξ : ℂ) * (u : ℂ))) := by
  have hF : ∀ w : ℝ, 𝓕 Φ w = airyTestPsi Φ (((-2 * π * w : ℝ)) : ℂ) := by
    intro w
    rw [Real.fourier_real_eq_integral_exp_smul]
    unfold airyTestPsi
    congr 1; funext v
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast; ring
  have hint : Integrable Φ := hΦ.continuous.integrable_of_hasCompactSupport hc
  have hψ := integrable_airyTestPsi hΦ hc
  have hFint : Integrable (𝓕 Φ) := by
    have := hψ.comp_mul_left' (R := -2 * π)
      (by have := Real.pi_pos; intro h; linarith)
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only [hF]
  have key := hint.fourierInv_fourier_eq hFint (v := u) hΦ.continuous.continuousAt
  rw [← key, Real.fourierInv_eq']
  have hin : ∀ v : ℝ, inner ℝ v u = u * v := fun v => by simp [inner]
  set g : ℝ → ℂ := fun ξ => airyTestPsi Φ (ξ : ℂ) * cexp (-(I * (ξ : ℂ) * (u : ℂ))) with hg
  have e1 : ∀ v : ℝ, cexp (↑(2 * π * inner ℝ v u) * I) • 𝓕 Φ v = g (-2 * π * v) := by
    intro v
    rw [hF, smul_eq_mul, hin, hg]
    simp only
    rw [mul_comm]
    congr 2
    push_cast; ring
  simp_rw [e1]
  rw [Measure.integral_comp_mul_left g (-2 * π)]
  rw [Complex.real_smul]
  congr 1
  push_cast
  rw [abs_inv, abs_of_neg (by have := Real.pi_pos; linarith)]
  push_cast
  field_simp

end FormalResearch.Special
