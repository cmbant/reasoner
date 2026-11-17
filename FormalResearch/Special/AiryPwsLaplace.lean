module

public import FormalResearch.Special.AiryPwsPlaneWave

/-!
# Theorem 3.1 `(c) ⇒ (b)` for an absolutely continuous one-sided measure

If `f(u) = ∫_0^∞ Φ_τ(u) m(τ) dτ` with `m ∈ L¹(0,∞)`, then for `Im ζ > 0` the twisted transform of `f` is the
Laplace transform of `m`:

`F̃_f(ζ) = ∫_0^∞ e^{iζτ} m(τ) dτ`    (`airyFtilde_laplace`),

by Fubini (the integrand has the integrable majorant `|Ai(k(u+τ))| e^{(Im ζ) u} |m(τ)|`) and the plane-wave identity
`airyFtilde_airyPhi`.  In particular `|F̃_f| ≤ ‖m‖₁` on `Im ζ > 0`.  This is the `(c) ⇒ (b)` direction of Theorem 3.1
for `μ = m dτ` and the form in which the kernel `m_n` of the Gram/Clark computation enters.

**Not formalised** here: `f ∈ L¹` for such `f` (not automatic: `Ai ∉ L¹`), and general tempered one-sided `μ`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma airyPhi_ofReal (τ u : ℝ) : airyPhi τ (u : ℂ) = (airyAi (airyPhiK * (u + τ)) : ℂ) := by
  unfold airyPhi
  have h1 : (airyPhiK : ℂ) * ((u : ℂ) + (τ : ℂ)) = ((airyPhiK * (u + τ) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, airyAiC_ofReal]

theorem airyFtilde_laplace {m : ℝ → ℂ} (hm : Integrable m (volume.restrict (Ioi (0 : ℝ)))) {f : ℂ → ℂ}
    (hf : ∀ u : ℝ, f (u : ℂ) = ∫ τ in Ioi (0 : ℝ), airyPhi τ (u : ℂ) * m τ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    airyFtilde f ζ = ∫ τ in Ioi (0 : ℝ), cexp (I * ζ * τ) * m τ := by
  have hk := airyPhiK_pos
  have hk0 : (airyPhiK : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  set η := ζ.im with hη
  set c : ℝ := η / airyPhiK with hc
  have hc0 : 0 < c := by positivity
  set gA : ℝ → ℝ := fun x => |airyAi x| * Real.exp (c * x) with hgA
  have hg : Integrable gA := by
    have := (integrable_airyAi_mul_exp hc0).norm
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rfl
  set A : ℝ := ∫ x : ℝ, gA x with hA
  set H : ℝ → ℝ → ℂ := fun u τ => airyPhi τ (u : ℂ) * cexp (-(I * ζ * (u : ℂ))) * m τ with hH
  have hnorm : ∀ u τ : ℝ, ‖H u τ‖ = Real.exp (-(η * τ)) * ‖m τ‖ * gA (airyPhiK * (u + τ)) := by
    intro u τ
    rw [hH]; simp only
    rw [norm_mul, norm_mul, airyPhi_ofReal, norm_cexp_airyFhat, Complex.norm_real, Real.norm_eq_abs, hgA]
    simp only
    have : Real.exp (c * (airyPhiK * (u + τ))) = Real.exp (η * u) * Real.exp (η * τ) := by
      rw [← Real.exp_add]; congr 1; rw [hc]; field_simp
    rw [this]
    have h2 : Real.exp (-(η * τ)) * Real.exp (η * τ) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (|airyAi (airyPhiK * (u + τ))| * Real.exp (η * u) * ‖m τ‖) * (-h2)
  have hint_u : ∀ τ : ℝ, Integrable fun u : ℝ => gA (airyPhiK * (u + τ)) := fun τ =>
    (hg.comp_mul_left' hk.ne').comp_add_right τ
  have hval_u : ∀ τ : ℝ, ∫ u : ℝ, gA (airyPhiK * (u + τ)) = airyPhiK⁻¹ * A := by
    intro τ
    have := integral_add_right_eq_self (μ := volume) (fun u : ℝ => gA (airyPhiK * u)) τ
    rw [this, Measure.integral_comp_mul_left gA airyPhiK, abs_inv, abs_of_pos hk, smul_eq_mul]
  have hHcont : Continuous (Function.uncurry fun u τ : ℝ => airyPhi τ (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))) := by
    have : (Function.uncurry fun u τ : ℝ => airyPhi τ (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))) =
        fun z : ℝ × ℝ => (airyAi (airyPhiK * (z.1 + z.2)) : ℂ) * cexp (-(I * ζ * (z.1 : ℂ))) := by
      funext z
      show airyPhi z.2 (z.1 : ℂ) * cexp (-(I * ζ * (z.1 : ℂ))) = _
      rw [airyPhi_ofReal]
    rw [this]
    have := contDiff_airyAi.continuous
    fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry H) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hHcont.aestronglyMeasurable.mul hm.aestronglyMeasurable.comp_snd
  have hfub : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine Eventually.of_forall fun τ => ?_
      refine ((hint_u τ).const_mul (Real.exp (-(η * τ)) * ‖m τ‖)).mono' ?_ (Eventually.of_forall fun u => ?_)
      · exact (hHcont.comp (by fun_prop : Continuous fun u : ℝ => (u, τ))).aestronglyMeasurable.mul
          (aestronglyMeasurable_const (b := m τ))
      · show ‖H u τ‖ ≤ _
        rw [hnorm]
    · have e : ∀ τ : ℝ, ∫ u : ℝ, ‖H u τ‖ = Real.exp (-(η * τ)) * ‖m τ‖ * (airyPhiK⁻¹ * A) := by
        intro τ
        simp_rw [hnorm]
        rw [integral_const_mul, hval_u]
      simp_rw [Function.uncurry_apply_pair, e]
      have hA0 : 0 ≤ A := integral_nonneg fun x => by positivity
      refine ((hm.norm.mul_const (airyPhiK⁻¹ * A))).mono' ?_ ?_
      · exact ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul hm.norm.aestronglyMeasurable).mul
          aestronglyMeasurable_const
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
        have : Real.exp (-(η * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by have := hζ; nlinarith [hτ.out])
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h3 : 0 ≤ ‖m τ‖ * (airyPhiK⁻¹ * A) := by positivity
        nlinarith
  have hswap := integral_integral_swap hfub
  have e1 : airyFhat f ζ = ∫ u : ℝ, ∫ τ in Ioi (0 : ℝ), H u τ := by
    unfold airyFhat
    congr 1; funext u
    rw [hf u, ← integral_mul_const]
    congr 1; funext τ; simp only [hH]; ring
  have e2 : ∀ τ : ℝ, ∫ u : ℝ, H u τ = m τ * (((airyPhiK : ℂ))⁻¹ * cexp (I * ζ ^ 3 / 12) * cexp (I * ζ * τ)) := by
    intro τ
    rw [← airyFhat_airyPhi hζ τ]
    unfold airyFhat
    rw [← integral_const_mul]
    congr 1; funext u; rw [hH]; ring
  unfold airyFtilde
  rw [e1]
  rw [hswap]
  simp_rw [e2]
  rw [← integral_const_mul]
  congr 1; funext τ
  have e : cexp (-(I * ζ ^ 3 / 12)) * cexp (I * ζ ^ 3 / 12) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination ((airyPhiK : ℂ) * (airyPhiK : ℂ)⁻¹ * cexp (I * ζ * τ) * m τ) * e +
    (cexp (I * ζ * τ) * m τ) * (mul_inv_cancel₀ hk0)

/-- info: 'FormalResearch.Special.airyFtilde_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyFtilde_laplace

end FormalResearch.Special
