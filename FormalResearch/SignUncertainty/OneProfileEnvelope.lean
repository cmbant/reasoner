module

public import FormalResearch.SignUncertainty.ShellLaplaceBase
public import FormalResearch.Special.AiryPwsConverseMain
public import FormalResearch.Special.AiryPwsMain

/-!
# The uniform Airy envelope of unit-`L¹` members of `𝒢` (`gt:3.1`, as used in `prop:ce-one-profile`)

Every `H ∈ 𝒢` (`InAiryClass`) with `‖H‖₁ = 1` satisfies `‖H(z)‖ ≤ C₀ (1+|z|) e(z)` with a universal `C₀`
(`inAiryClass_envelope`): by Theorem 3.1 `(a) ⇒ (b)` (`airyFtilde_norm_le`) the twisted transform is in
`H^∞` with norm `≤ k`, and the inversion integral `airyIeta` of Theorem 3.1 `(b) ⇒ (a)` (`norm_airyIeta_global`)
reproduces `H` on `ℝ`, hence on `ℂ` by the identity theorem.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

lemma eq_of_eq_on_real {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ)) : ∀ z, f z = g z := by
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
  have h0 : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto 0
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h0.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with x hx
          simpa using hx)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z :=
    ht.frequently (Filter.Frequently.of_forall fun x => h x)
  intro z
  exact hfa.eqOn_of_preconnected_of_frequently_eq hga isPreconnected_univ (mem_univ 0) hfreq (mem_univ z)

theorem inAiryClass_envelope {H : ℂ → ℂ} (hH : InAiryClass H) (h1 : ∫ x : ℝ, ‖H (x : ℂ)‖ = 1) :
    ∀ z : ℂ, ‖H z‖ ≤ ((2 * π)⁻¹ * (1 * √(4 * π) * Real.exp 8)) * (1 + ‖z‖) ^ (1 : ℝ) * airyEnv z := by
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, -⟩ := hH
  have hG : AiryClassG H := by
    refine ⟨hd, hi, C, ⌈ν⌉₊, hC, fun z => (hb z).trans ?_⟩
    have : (1 + ‖z‖) ^ ν ≤ (1 + ‖z‖) ^ (⌈ν⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (Nat.le_ceil ν)
    rw [Real.rpow_natCast] at this
    gcongr
    exact airyEnv_pos z |>.le
  have hAH : AiryHinf (airyFtilde H) (airyPhiK * 1) := by
    refine ⟨airyFtilde_diffContOnCl hG, fun ζ hζ => ?_⟩
    have := airyFtilde_norm_le hG hζ
    rwa [h1] at this
  have hb : ∀ ξ : ℝ, airyFtilde H (ξ : ℂ) = (airyPhiK : ℂ) * cexp (-(I * (ξ : ℂ) ^ 3 / 12)) *
      airyFhatR (fun u : ℝ => H (u : ℂ)) ξ := fun ξ => rfl
  have hae := airy_converse_ae hAH hi hb
  set f : ℂ → ℂ := fun z => ((2 * π : ℝ) : ℂ)⁻¹ * airyIeta (airyFtilde H) 1 z with hf
  have hfd : Differentiable ℂ f := (differentiable_airyIeta hAH one_pos).const_mul _
  have hc1 : Continuous fun x : ℝ => H (x : ℂ) := hd.continuous.comp Complex.continuous_ofReal
  have hc2 : Continuous fun x : ℝ => f (x : ℂ) := hfd.continuous.comp Complex.continuous_ofReal
  have heq : (fun x : ℝ => f (x : ℂ)) = fun x : ℝ => H (x : ℂ) :=
    (Continuous.ae_eq_iff_eq volume hc2 hc1).mp hae
  have hreal : ∀ x : ℝ, H (x : ℂ) = f (x : ℂ) := fun x => (congrFun heq x).symm
  intro z
  rw [eq_of_eq_on_real hd hfd hreal z, hf]
  simp only
  have hk := airyPhiK_pos
  have hglob := norm_airyIeta_global hAH z
  have e : airyPhiK * 1 / airyPhiK = 1 := by field_simp
  rw [e] at hglob
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
    Real.rpow_one]
  calc (2 * π)⁻¹ * ‖airyIeta (airyFtilde H) 1 z‖
      ≤ (2 * π)⁻¹ * (1 * √(4 * π) * Real.exp 8 * (1 + ‖z‖) * airyEnv z) := by gcongr
    _ = _ := by ring

theorem inAiryClass_envelope_exists : ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℂ → ℂ, InAiryClass H →
    (∫ x : ℝ, ‖H (x : ℂ)‖) = 1 → ∀ z : ℂ, ‖H z‖ ≤ C * (1 + ‖z‖) ^ (1 : ℝ) * airyEnv z :=
  ⟨(2 * π)⁻¹ * (1 * √(4 * π) * Real.exp 8), by positivity, fun H hH h1 => inAiryClass_envelope hH h1⟩

/-- `prop:ce-one-profile`, attainment step: normalised one-profile witnesses obey a uniform Airy envelope
(`gt:3.1`); the bound does not depend on the configuration or on the threshold. -/
theorem one_profile_envelope_aux (D : ShellHBData) (u₀ : ℝ) (_ : OneProfileFeasible D u₀) :
    ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u₀ ≤ u →
      ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D u H → (∫ x : ℝ, ‖H (x : ℂ)‖) = 1 →
        ∀ z : ℂ, ‖H z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z := by
  obtain ⟨C, hC, h⟩ := inAiryClass_envelope_exists
  exact ⟨C, 1, hC, fun u _ H hH h1 => h H hH.1 h1⟩

/-- info: 'FormalResearch.SignUncertainty.inAiryClass_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inAiryClass_envelope

/-- info: 'FormalResearch.SignUncertainty.one_profile_envelope_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_profile_envelope_aux

end FormalResearch.SignUncertainty
