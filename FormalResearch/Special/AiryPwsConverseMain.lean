module

public import FormalResearch.Special.AiryPwsIdent3

/-!
# Airy Paley–Wiener–Schwartz, Theorem 3.1 `(b) ⇒ (a)`

Let `f₀ ∈ L¹(ℝ)` and suppose the twisted transform `F̃(ξ) = k e^{-iξ³/12} f̂₀(ξ)` of `f₀` on the real line is the
boundary value of a function `Fh` that is holomorphic on `Im ζ > 0`, continuous on `Im ζ ≥ 0` and bounded
(`AiryHinf`).  Then `f₀` agrees almost everywhere with an entire function `f` of class `G`
(`|f(z)| ≤ C (1+|z|) e(z)`, `f|_ℝ ∈ L¹`), and the twisted transform of `f` is `Fh` on `Im ζ ≥ 0`
(`airyPws_converse`).  With `airyFtilde_norm_le` (`AiryPwsMain`) this is the equivalence `(a) ⇔ (b)` of
Theorem 3.1 of `CFT/notes/general_theorems.tex`, for complex-valued `f` (reality of `f` is not needed).

* `airy_converse_ae`: `(2π)⁻¹ I_1 = f₀` almost everywhere (test functions, Fubini, Fourier inversion);
* `airyPws_converse`: packaging, using the Phragmén–Lindelöf lemma `pl_halfPlane` with `B = 0` to identify
  `airyFtilde f = Fh` on the closed half plane.

**Not formalised**: statement `(c)` (representation `f = ∫ Φ_τ dμ` with a measure supported on `[0,∞)`), which needs a
Paley–Wiener–Schwartz/Titchmarsh theorem for tempered distributions that is not in Mathlib.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real ContDiff

namespace FormalResearch.Special

lemma airyLam_real {Fh : ℂ → ℂ} {f₀ : ℝ → ℂ}
    (hb : ∀ ξ : ℝ, Fh (ξ : ℂ) = (airyPhiK : ℂ) * cexp (-(I * (ξ : ℂ) ^ 3 / 12)) * airyFhatR f₀ ξ) (ξ : ℝ) :
    airyLam Fh (ξ : ℂ) = airyFhatR f₀ ξ := by
  unfold airyLam
  rw [hb ξ]
  have hk : (airyPhiK : ℂ) ≠ 0 := by exact_mod_cast airyPhiK_pos.ne'
  have e : cexp (I * (ξ : ℂ) ^ 3 / 12) * cexp (-(I * (ξ : ℂ) ^ 3 / 12)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc ((airyPhiK : ℂ))⁻¹ * cexp (I * (ξ : ℂ) ^ 3 / 12) *
        ((airyPhiK : ℂ) * cexp (-(I * (ξ : ℂ) ^ 3 / 12)) * airyFhatR f₀ ξ)
      = (airyPhiK : ℂ)⁻¹ * (airyPhiK : ℂ) * (cexp (I * (ξ : ℂ) ^ 3 / 12) * cexp (-(I * (ξ : ℂ) ^ 3 / 12))) *
        airyFhatR f₀ ξ := by ring
    _ = _ := by rw [e, inv_mul_cancel₀ hk]; ring

theorem airy_converse_ae {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {f₀ : ℝ → ℂ} (hf : Integrable f₀)
    (hb : ∀ ξ : ℝ, Fh (ξ : ℂ) = (airyPhiK : ℂ) * cexp (-(I * (ξ : ℂ) ^ 3 / 12)) * airyFhatR f₀ ξ) :
    ∀ᵐ u : ℝ, ((2 * π : ℝ) : ℂ)⁻¹ * airyIeta Fh 1 (u : ℂ) = f₀ u := by
  set fE : ℝ → ℂ := fun u => ((2 * π : ℝ) : ℂ)⁻¹ * airyIeta Fh 1 (u : ℂ) with hfE
  have hfEc : Continuous fE := by
    have := (differentiable_airyIeta h one_pos).continuous
    exact continuous_const.mul (this.comp Complex.continuous_ofReal)
  have hloc : LocallyIntegrable (fun u => fE u - f₀ u) volume :=
    (hfEc.locallyIntegrable).sub hf.locallyIntegrable
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun φ hφ hφc => by
    set Φ : ℝ → ℂ := fun t => (φ t : ℂ) with hΦ
    have hΦd : ContDiff ℝ ∞ Φ := Complex.ofRealCLM.contDiff.comp hφ
    have hΦc : HasCompactSupport Φ := hφc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
    have hΦcont := hΦd.continuous
    obtain ⟨C0, hC0⟩ := hΦcont.bounded_above_of_compact_support hΦc
    have i1 : Integrable fun u : ℝ => Φ u * fE u :=
      (hΦcont.mul hfEc).integrable_of_hasCompactSupport hΦc.mul_right
    have i2 : Integrable fun u : ℝ => Φ u * f₀ u :=
      hf.bdd_mul hΦcont.aestronglyMeasurable (Eventually.of_forall hC0)
    have e1 : ∀ u : ℝ, φ u • (fE u - f₀ u) = Φ u * fE u - Φ u * f₀ u := fun u => by
      rw [Complex.real_smul, hΦ]; ring
    simp_rw [e1]
    rw [integral_sub i1 i2]
    have e2 : ∫ u : ℝ, Φ u * fE u = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, Φ u * airyIeta Fh 1 (u : ℂ) := by
      rw [← integral_const_mul]; congr 1; funext u; rw [hfE]; ring
    rw [e2, pairing_eq h hΦd hΦc, pairing_f0 hf hΦd hΦc]
    have e3 : ∀ ξ : ℝ, airyLam Fh (ξ : ℂ) * airyTestPsi Φ (ξ : ℂ) = airyTestPsi Φ (ξ : ℂ) * airyFhatR f₀ ξ :=
      fun ξ => by rw [airyLam_real hb ξ]; ring
    simp_rw [e3]
    push_cast
    ring)
  filter_upwards [key] with u hu
  exact sub_eq_zero.mp hu

/-- **Theorem 3.1 `(b) ⇒ (a)`.**  `f₀ ∈ L¹(ℝ)`, `Fh ∈ H^∞` with real boundary values `k e^{-iξ³/12} f̂₀(ξ)`.
Then `f₀` is a.e. equal to an entire `f` of class `G`, and `F̃_f = Fh` on `Im ζ ≥ 0`. -/
theorem airyPws_converse {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {f₀ : ℝ → ℂ} (hf : Integrable f₀)
    (hb : ∀ ξ : ℝ, Fh (ξ : ℂ) = (airyPhiK : ℂ) * cexp (-(I * (ξ : ℂ) ^ 3 / 12)) * airyFhatR f₀ ξ) :
    ∃ f : ℂ → ℂ, AiryClassG f ∧ (∀ᵐ u : ℝ, f (u : ℂ) = f₀ u) ∧
      ∀ ζ : ℂ, 0 ≤ ζ.im → airyFtilde f ζ = Fh ζ := by
  set f : ℂ → ℂ := fun z => ((2 * π : ℝ) : ℂ)⁻¹ * airyIeta Fh 1 z with hfdef
  have hae : ∀ᵐ u : ℝ, f (u : ℂ) = f₀ u := airy_converse_ae h hf hb
  have hB := airyHinf_nonneg h
  have hk := airyPhiK_pos
  have hG : AiryClassG f := by
    refine ⟨(differentiable_airyIeta h one_pos).const_mul _, hf.congr (hae.mono fun u hu => hu.symm), ?_⟩
    refine ⟨(2 * π)⁻¹ * (B / airyPhiK * √(4 * π) * Real.exp 8), 1, by positivity, fun z => ?_⟩
    have := norm_airyIeta_global h z
    rw [hfdef]; simp only
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    calc (2 * π)⁻¹ * ‖airyIeta Fh 1 z‖ ≤ (2 * π)⁻¹ * (B / airyPhiK * √(4 * π) * Real.exp 8 * (1 + ‖z‖) * airyEnv z) := by
          gcongr
      _ = _ := by ring
  refine ⟨f, hG, hae, fun ζ hζ => ?_⟩
  -- boundary values agree
  have hreal : ∀ ξ : ℝ, airyFtilde f (ξ : ℂ) - Fh (ξ : ℂ) = 0 := by
    intro ξ
    have e : airyFhat f (ξ : ℂ) = airyFhatR f₀ ξ := by
      unfold airyFhat airyFhatR
      refine integral_congr_ae (hae.mono fun u hu => ?_)
      simp only [hu]
    unfold airyFtilde
    rw [e, hb ξ]
    ring_nf
  obtain ⟨A, M, hA, hpoly⟩ := airyFtilde_poly hG
  have hg := airyFtilde_diffContOnCl hG |>.sub h.diffContOnCl
  have := pl_halfPlane (g := fun ζ => airyFtilde f ζ - Fh ζ) (A := A + B) (B := 0) (M := M)
    (by positivity) hg (fun ζ hζ => by
      have h1 := hpoly ζ hζ
      have h2 := h.bound ζ hζ
      have h3 : (1 : ℝ) ≤ (1 + ‖ζ‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg ζ])
      calc ‖airyFtilde f ζ - Fh ζ‖ ≤ ‖airyFtilde f ζ‖ + ‖Fh ζ‖ := norm_sub_le _ _
        _ ≤ A * (1 + ‖ζ‖) ^ M + B * (1 + ‖ζ‖) ^ M := add_le_add h1 (h2.trans (by nlinarith))
        _ = _ := by ring)
    (fun ξ => by rw [hreal ξ]; simp) hζ
  have h0 : ‖airyFtilde f ζ - Fh ζ‖ ≤ 0 := this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- info: 'FormalResearch.Special.airyPws_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPws_converse

/-- info: 'FormalResearch.Special.airy_converse_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_converse_ae

end FormalResearch.Special
