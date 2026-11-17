module

public import FormalResearch.Special.AiryPwsIdent

/-!
# Theorem 3.1 `(b) ⇒ (a)`, pairing with a test function

For `Φ` smooth with compact support and `η > 0` (`AiryHinf Fh B`):

* `airyPws_pairing_eta`: `∫ Φ(u) I_η(u) du = ∫ Λ(ξ+iη) ψ(ξ+iη) dξ` (Fubini, Gaussian majorant);
* `airyPws_pairing_eq`: the right side tends to `∫ Λ(ξ) ψ(ξ) dξ` as `η → 0⁺` (dominated convergence with the uniform
  decay `airyTestPsi_decay`); since `I_η = I_1` it follows that `∫ Φ I_1 = ∫ Λ ψ`.

Continued in the next module of the chain `AiryPwsIdent`, `AiryPwsIdent2`, `AiryPwsIdent3`, `AiryPwsConverseMain`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real ContDiff

namespace FormalResearch.Special

lemma norm_airyLam_le {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {ζ : ℂ} (h0 : 0 ≤ ζ.im) (h1 : ζ.im ≤ 1) :
    ‖airyLam Fh ζ‖ ≤ B / airyPhiK * Real.exp (1 / 12) := by
  unfold airyLam
  rw [norm_mul, norm_mul, airyPws_norm_cexp_cube, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos airyPhiK_pos]
  have hB := airyHinf_nonneg h
  have hk := airyPhiK_pos
  have hb := h.bound ζ h0
  have he : Real.exp (-(3 * ζ.re ^ 2 * ζ.im - ζ.im ^ 3) / 12) ≤ Real.exp (1 / 12) := by
    refine Real.exp_le_exp.mpr ?_
    have : ζ.im ^ 3 ≤ 1 := pow_le_one₀ h0 h1
    nlinarith [mul_nonneg (sq_nonneg ζ.re) h0]
  calc (airyPhiK)⁻¹ * Real.exp (-(3 * ζ.re ^ 2 * ζ.im - ζ.im ^ 3) / 12) * ‖Fh ζ‖
      ≤ (airyPhiK)⁻¹ * Real.exp (1 / 12) * B := by gcongr
    _ = _ := by ring

lemma continuous_airyLam_line {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η : ℝ} (hη : 0 ≤ η) :
    Continuous fun ξ : ℝ => airyLam Fh ((ξ : ℂ) + η * I) :=
  (continuousOn_airyLam h).comp_continuous (by fun_prop) (fun ξ => by simp [hη])

lemma airyPws_pairing_eta {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {Φ : ℝ → ℂ} (hΦ : Continuous Φ)
    (hc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) :
    ∫ u : ℝ, Φ u * airyIeta Fh η (u : ℂ) =
      ∫ ξ : ℝ, airyLam Fh ((ξ : ℂ) + η * I) * airyTestPsi Φ ((ξ : ℂ) + η * I) := by
  obtain ⟨R, hR0, hR⟩ := airyPws_exists_supp_bound hc
  set C : ℝ := B / airyPhiK * Real.exp (η ^ 3 / 12 + η * R + 2 * R ^ 2 / η) with hC
  have hint : Integrable fun u : ℝ => Φ u := hΦ.integrable_of_hasCompactSupport hc
  have hG : Integrable (fun z : ℝ × ℝ => ‖Φ z.1‖ * (C * Real.exp (-(η / 8) * z.2 ^ 2))) (volume.prod volume) :=
    hint.norm.mul_prod ((integrable_exp_neg_mul_sq (by positivity : 0 < η / 8)).const_mul C)
  have hcont : Continuous (Function.uncurry fun (u ξ : ℝ) => Φ u * airyKE Fh (u : ℂ) ((ξ : ℂ) + η * I)) := by
    have h1 : Continuous fun z : ℝ × ℝ => airyLam Fh ((z.2 : ℂ) + η * I) :=
      (continuousOn_airyLam h).comp_continuous (by fun_prop) (fun z => by simp [hη.le])
    unfold airyKE
    have : Continuous fun z : ℝ × ℝ => Φ z.1 * (airyLam Fh ((z.2 : ℂ) + η * I) *
        cexp (I * ((z.2 : ℂ) + η * I) * (z.1 : ℂ))) := by
      exact (hΦ.comp continuous_fst).mul (h1.mul (by fun_prop))
    exact this
  have hfub : Integrable (Function.uncurry fun (u ξ : ℝ) => Φ u * airyKE Fh (u : ℂ) ((ξ : ℂ) + η * I))
      (volume.prod volume) := by
    refine hG.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    show ‖Φ z.1 * airyKE Fh (z.1 : ℂ) ((z.2 : ℂ) + η * I)‖ ≤ _
    rw [norm_mul]
    by_cases hz : Φ z.1 = 0
    · simp [hz]
    · have := norm_airyKE_le_maj h hη (ρ := R) (u := (z.1 : ℂ)) (by simpa using hR z.1 hz) z.2
      calc ‖Φ z.1‖ * ‖airyKE Fh (z.1 : ℂ) ((z.2 : ℂ) + η * I)‖ ≤ ‖Φ z.1‖ * (C * Real.exp (-(η / 8) * z.2 ^ 2)) := by
            gcongr
        _ = _ := rfl
  have hswap := integral_integral_swap hfub
  unfold airyIeta
  calc ∫ u : ℝ, Φ u * ∫ ξ : ℝ, airyKE Fh (u : ℂ) ((ξ : ℂ) + η * I)
      = ∫ u : ℝ, ∫ ξ : ℝ, Φ u * airyKE Fh (u : ℂ) ((ξ : ℂ) + η * I) := by
        congr 1; funext u; rw [integral_const_mul]
    _ = ∫ ξ : ℝ, ∫ u : ℝ, Φ u * airyKE Fh (u : ℂ) ((ξ : ℂ) + η * I) := hswap
    _ = _ := by
        congr 1; funext ξ
        unfold airyTestPsi airyKE
        rw [← integral_const_mul]
        congr 1; funext u; ring

/-- `∫ Φ I_1 = ∫ Λ ψ` (boundary values, `η → 0⁺`). -/
theorem airyPws_pairing_eq {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hc : HasCompactSupport Φ) :
    ∫ u : ℝ, Φ u * airyIeta Fh 1 (u : ℂ) = ∫ ξ : ℝ, airyLam Fh (ξ : ℂ) * airyTestPsi Φ (ξ : ℂ) := by
  obtain ⟨D, hD0, hD⟩ := airyTestPsi_decay hΦ hc
  have hΦc := hΦ.continuous
  have hψc := continuous_airyTestPsi hΦc hc
  have hB := airyHinf_nonneg h
  have hk := airyPhiK_pos
  set J : ℝ → ℂ := fun η => ∫ ξ : ℝ, airyLam Fh ((ξ : ℂ) + η * I) * airyTestPsi Φ ((ξ : ℂ) + η * I) with hJ
  have hlim : Tendsto J (𝓝[>] (0 : ℝ)) (𝓝 (∫ ξ : ℝ, airyLam Fh (ξ : ℂ) * airyTestPsi Φ (ξ : ℂ))) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
      (F := fun (η : ℝ) (ξ : ℝ) => airyLam Fh ((ξ : ℂ) + η * I) * airyTestPsi Φ ((ξ : ℂ) + η * I))
      (f := fun ξ : ℝ => airyLam Fh (ξ : ℂ) * airyTestPsi Φ (ξ : ℂ))
      (fun ξ => B / airyPhiK * Real.exp (1 / 12) * (D * (1 + ξ ^ 2)⁻¹))
      (by
        filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη
        exact ((continuous_airyLam_line h hη.1.le).mul
          (hψc.comp (by fun_prop))).aestronglyMeasurable)
      (by
        filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη
        refine Eventually.of_forall fun ξ => ?_
        have h1 := norm_airyLam_le h (ζ := (ξ : ℂ) + η * I) (by simp [hη.1.le]) (by simp [hη.2.le])
        have h2 := hD ((ξ : ℂ) + η * I) (by simp [hη.1.le]) (by simp [hη.2.le])
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero] at h2
        have h3 : ‖airyTestPsi Φ ((ξ : ℂ) + η * I)‖ ≤ D * (1 + ξ ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
        rw [norm_mul]
        gcongr)
      (integrable_inv_one_add_sq.const_mul D |>.const_mul _)
      (Eventually.of_forall fun ξ => by
        have hf : ∀ η : ℝ, 0 ≤ η → ((ξ : ℂ) + η * I).im ≥ 0 := fun η hη => by simp [hη]
        have hcont : ContinuousOn (fun η : ℝ => airyLam Fh ((ξ : ℂ) + η * I) *
            airyTestPsi Φ ((ξ : ℂ) + η * I)) (Ici 0) := by
          have hf1 : Continuous fun η : ℝ => (ξ : ℂ) + η * I := by fun_prop
          have e1 := (continuousOn_airyLam h).comp hf1.continuousOn
            (fun η (hη : η ∈ Ici (0 : ℝ)) => by simpa using hη)
          exact e1.mul (hψc.comp hf1).continuousOn
        have := (hcont 0 (by simp)).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
        simpa using this)
    simpa [hJ] using this
  have hconst : Tendsto J (𝓝[>] (0 : ℝ)) (𝓝 (∫ u : ℝ, Φ u * airyIeta Fh 1 (u : ℂ))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with η hη
    rw [hJ]; simp only
    rw [← airyPws_pairing_eta h hΦc hc hη.1]
    congr 1; funext u
    rw [airyIeta_eq' h hη.1 (by norm_num : (0 : ℝ) < 1)]
  exact tendsto_nhds_unique hconst hlim

/-- info: 'FormalResearch.Special.airyPws_pairing_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPws_pairing_eq

end FormalResearch.Special
