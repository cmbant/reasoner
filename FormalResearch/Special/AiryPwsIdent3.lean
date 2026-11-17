module

public import FormalResearch.Special.AiryPwsIdent2

/-!
# Theorem 3.1 `(b) ⇒ (a)`, identification with the `L¹` function

Let `f₀ ∈ L¹(ℝ)` and let `Fh` be `H^∞` (`AiryHinf`) with boundary values `Λ(ξ) = k⁻¹ e^{iξ³/12} Fh(ξ) = f̂₀(ξ)`
(that is `Fh(ξ) = k e^{-iξ³/12} f̂₀(ξ)`, the real-line value of the twisted transform).  Then `f₀ = (2π)⁻¹ I_1` a.e.:
both pair with every smooth compactly supported `φ` to `(2π)⁻¹ ∫ f̂₀ ψ_φ` (`pairing_f0`, `pairing_eq`).

Continued in `AiryPwsConverseMain` (packaging as the class `G`, identification `F̃ = Fh`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real ContDiff

namespace FormalResearch.Special

/-- `f̂₀(ξ) = ∫ f₀(u) e^{-iξu} du` for `f₀ : ℝ → ℂ`. -/
noncomputable def airyFhatR (f₀ : ℝ → ℂ) (ξ : ℝ) : ℂ := ∫ u : ℝ, f₀ u * cexp (-(I * (ξ : ℂ) * (u : ℂ)))

lemma norm_cexp_neg_real (ξ u : ℝ) : ‖cexp (-(I * (ξ : ℂ) * (u : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp [Complex.mul_re, Complex.mul_im]

lemma pairing_f0 {f₀ : ℝ → ℂ} (hf : Integrable f₀) {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hc : HasCompactSupport Φ) :
    ∫ u : ℝ, Φ u * f₀ u = (2 * π : ℝ)⁻¹ * ∫ ξ : ℝ, airyTestPsi Φ (ξ : ℂ) * airyFhatR f₀ ξ := by
  have hψ := integrable_airyTestPsi hΦ hc
  have hψc := continuous_airyTestPsi hΦ.continuous hc
  set G : ℝ → ℝ → ℂ := fun u ξ => f₀ u * (airyTestPsi Φ (ξ : ℂ) * cexp (-(I * (ξ : ℂ) * (u : ℂ)))) with hG
  have hfub : Integrable (Function.uncurry G) (volume.prod volume) := by
    have hm : AEStronglyMeasurable (Function.uncurry G) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => f₀ z.1) (volume.prod volume) :=
        hf.aestronglyMeasurable.comp_fst
      have h2 : Continuous fun z : ℝ × ℝ => airyTestPsi Φ (z.2 : ℂ) * cexp (-(I * (z.2 : ℂ) * (z.1 : ℂ))) :=
        (hψc.comp (by fun_prop)).mul (by fun_prop)
      exact h1.mul h2.aestronglyMeasurable
    refine (hf.norm.mul_prod hψ.norm).mono' hm (Eventually.of_forall fun z => ?_)
    show ‖f₀ z.1 * (airyTestPsi Φ (z.2 : ℂ) * cexp (-(I * (z.2 : ℂ) * (z.1 : ℂ))))‖ ≤ _
    rw [norm_mul, norm_mul, norm_cexp_neg_real, mul_one]
  have hswap := integral_integral_swap hfub
  have e1 : ∀ u : ℝ, Φ u * f₀ u = (2 * π : ℝ)⁻¹ * ∫ ξ : ℝ, G u ξ := by
    intro u
    rw [hG]; simp only
    rw [integral_const_mul, airy_inversion hΦ hc u]
    ring
  simp_rw [e1]
  rw [integral_const_mul, hswap]
  congr 1
  congr 1; funext ξ
  rw [hG]; simp only
  unfold airyFhatR
  rw [← integral_const_mul]
  congr 1; funext u; ring

end FormalResearch.Special
