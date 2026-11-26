module

public import FormalResearch.ModularBootstrap.Blowup.AiryNormLimit
public import FormalResearch.TwoEdgeBootstrap.FoldTipSeed

/-!
# Local Airy model: the class `𝒢`, quadrature positivity and the density hypotheses

Source: `CFT/modular_bootstrap/paper/remainder.tex`, Theorem B-stab (`rem:thmBstab`) and
`CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem `se:terminal-stability`
(Airy case).

* `AiryG f`: `f` entire, real on `ℝ`, `f ∈ L¹(ℝ)` and `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (the class `𝒢`).
* `AiryG.quadrature_ge`: if `f ≥ 0` on `(-∞, a₁]`, then `∫ f ≥ f(a₁)/Ai'(a₁)² ≥ ...` and `∫ f ≥ 0`
  (Theorem Q, `airyQ_hasSum_unc`; all other quadrature samples are nonnegative).
* `AiryG.densityHyp`: a norm-one `f ∈ 𝒢` which is `≥ 0` on `(-∞, u_T]` satisfies the density
  hypotheses `DensityHyp` of `Blowup.NormLimitCore` on `|u| ≤ R` with `ς = 0`, `C₀ = 1/(4π)` (the sharp
  Theorem Q (2) envelope, `airyQ_pointwise_sharp`) and `δ = ∫ f + τ(R)`; so that the normal-families
  and equality-case machinery of `Blowup/` applies to near-minimisers of `I(δ)` (`AiryStability`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.TwoEdgeBootstrap

/-- The class `𝒢`: entire, real on `ℝ`, integrable on `ℝ`, with the Airy growth bound. -/
structure AiryG (f : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ f
  integrable : Integrable (fun x : ℝ => f (x : ℂ))
  growth : ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u
  real : ∀ x : ℝ, (f (x : ℂ)).im = 0

namespace AiryG

variable {f : ℂ → ℂ}

lemma norm_real (hf : AiryG f) (x : ℝ) : ‖f (x : ℂ)‖ = |(f (x : ℂ)).re| := by
  have heq : f (x : ℂ) = (((f (x : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (hf.real x)
  conv_lhs => rw [heq]
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma re_integral (hf : AiryG f) : ∫ x : ℝ, (f (x : ℂ)).re = (∫ x : ℝ, f (x : ℂ)).re :=
  integral_re hf.integrable

lemma integrable_re (hf : AiryG f) : Integrable (fun x : ℝ => (f (x : ℂ)).re) :=
  hf.integrable.re

lemma integrable_norm (hf : AiryG f) : Integrable (fun x : ℝ => ‖f (x : ℂ)‖) :=
  hf.integrable.norm

lemma continuous_re (hf : AiryG f) : Continuous (fun x : ℝ => (f (x : ℂ)).re) :=
  Complex.continuous_re.comp (hf.diff.continuous.comp continuous_ofReal)

lemma smul (hf : AiryG f) (c : ℝ) : AiryG (fun u => (c : ℂ) * f u) where
  diff := (differentiable_const _).mul hf.diff
  integrable := hf.integrable.const_mul _
  growth := by
    obtain ⟨C, ν, hC, hb⟩ := hf.growth
    refine ⟨|c| * C, ν, by positivity, fun u => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hb u) (abs_nonneg c)
  real := fun x => by simp [hf.real x]

/-- Quadrature positivity: if `f ≥ 0` on `(-∞, a₁]`, then `∫ f ≥ 0` and
`f(a₁)/Ai'(a₁)² ≤ ∫ f` (all other samples `f(a_n)/Ai'(a_n)²` are nonnegative). -/
theorem quadrature_ge (hf : AiryG f) (hpos : ∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (f (x : ℂ)).re) :
    0 ≤ ∫ x : ℝ, (f (x : ℂ)).re ∧
      (f (airyZero 1 : ℂ)).re / (airyAi' (airyZero 1)) ^ 2 ≤ ∫ x : ℝ, (f (x : ℂ)).re := by
  obtain ⟨C, ν, hC, hb⟩ := hf.growth
  have hsum := airyQ_hasSum_unc hf.diff hf.integrable hC hb
  have hre := Complex.reCLM.hasSum hsum
  have hterm : ∀ n : ℕ, (Complex.reCLM
      (f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)) =
      (f (airyZero (n + 1) : ℂ)).re / (airyAi' (airyZero (n + 1))) ^ 2 := by
    intro n
    simp only [Complex.reCLM_apply, deriv_airyAiC_ofReal]
    rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  simp only [hterm] at hre
  rw [Complex.reCLM_apply, ← hf.re_integral] at hre
  have hnn : ∀ n : ℕ, 0 ≤ (f (airyZero (n + 1) : ℂ)).re / (airyAi' (airyZero (n + 1))) ^ 2 := by
    intro n
    refine div_nonneg (hpos _ ?_) (sq_nonneg _)
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · exact le_rfl
    · exact (airyZero_lt_of_lt le_rfl (by omega)).le
  refine ⟨hre.nonneg hnn, ?_⟩
  have := le_hasSum hre 0 (fun j _ => hnn j)
  simpa using this

lemma re_cpow_half_pos_of_cut {u : ℂ} (hu : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    0 < (u ^ (1 / 2 : ℂ)).re := by
  by_contra hle
  have hre0 : (u ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg u)
  have him_u : u.im = 2 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im :=
    (airySqrtRe_mul_im u).symm
  have hre_u : u.re = (u ^ (1 / 2 : ℂ)).re ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 :=
    (airySqrtRe_sq_sub u).symm
  rw [hre0] at him_u hre_u
  exact hu ⟨by linarith, by nlinarith [sq_nonneg (u ^ (1 / 2 : ℂ)).im]⟩

/-- The sharp envelope of Theorem Q (2) in the form of the type-(II) hypothesis of `DensityHyp`
(with `ς = 0` and `C₀ = ‖f‖_b/(4π)`, `‖f‖_b = ∫_{x ≤ 0}‖f‖`). -/
theorem env_sharp (hf : AiryG f) {u : ℂ} (hu : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    ‖f u‖ ≤ (4 * π)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u *
      ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
  obtain ⟨C, ν, hC, hb⟩ := hf.growth
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := re_cpow_half_pos_of_cut hu
  have hu_ne : u ≠ 0 := fun h0 => hu (by simp [h0])
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have h := airyQ_pointwise_sharp hf.diff hf.integrable hC hb hu_re_pos
  have hn : ‖u ^ (1 / 2 : ℂ)‖ = √‖u‖ := by
    rw [← norm_cpow_half_sq u, Real.sqrt_sq (norm_nonneg _)]
  have hconv : (4 * π * ‖u ^ (1 / 2 : ℂ)‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ =
      (4 * π)⁻¹ * (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
    rw [hn, Real.rpow_neg hu_norm_pos.le, ← Real.sqrt_eq_rpow]
    have := Real.pi_pos
    field_simp
  rw [hconv] at h
  calc ‖f u‖ ≤ (4 * π)⁻¹ * (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) *
        (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u := h
    _ = _ := by ring


lemma norm_Iic_le (hf : AiryG f) (hn : ∫ x : ℝ, ‖f (x : ℂ)‖ = 1) :
    ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ ≤ 1 := by
  rw [← hn]
  exact setIntegral_le_integral hf.integrable_norm (Eventually.of_forall fun x => norm_nonneg _)

/-- The envelope at positive real points. -/
theorem env_pos (hf : AiryG f) (hn : ∫ x : ℝ, ‖f (x : ℂ)‖ = 1) {x : ℝ} (hx0 : 0 < x) :
    ‖f (x : ℂ)‖ ≤ (4 * π)⁻¹ * airyEnv (x : ℂ) * Real.exp (0 * √x) * x⁻¹ := by
  have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := by
    intro h0; simp only [Complex.ofReal_re] at h0; linarith [h0.2]
  have h1 := hf.env_sharp hcut
  have hcp : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hx0.le, Complex.ofReal_re, Real.sqrt_eq_rpow]
  have hnorm_inv : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ = x⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hcp,
      Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hx0.le]
  have hB := hf.norm_Iic_le hn
  have he := airyEnv_pos (x : ℂ)
  have hxi : 0 < x⁻¹ := inv_pos.mpr hx0
  have hpi : 0 < (4 * π)⁻¹ := by positivity
  calc ‖f (x : ℂ)‖ ≤ (4 * π)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv (x : ℂ) *
        (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹) := by
        simpa only [mul_assoc] using h1
    _ = (4 * π)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv (x : ℂ) * x⁻¹ := by
        rw [hnorm_inv]
    _ ≤ (4 * π)⁻¹ * 1 * airyEnv (x : ℂ) * x⁻¹ := by gcongr
    _ = (4 * π)⁻¹ * airyEnv (x : ℂ) * Real.exp (0 * √x) * x⁻¹ := by simp

/-- Tail of the norm on `(A, ∞)`: `∫_A^∞ ‖f‖ ≤ τ(A)`, `τ(A) = (6/5) C₀ e^{-5A/6}`, `C₀ = 1/(4π)`. -/
theorem tail_Ioi (hf : AiryG f) (hn : ∫ x : ℝ, ‖f (x : ℂ)‖ = 1) {A : ℝ} (hA : 1 ≤ A) :
    ∫ x in Ioi A, ‖f (x : ℂ)‖ ≤ tailBound (4 * π)⁻¹ A := by
  have hint : IntegrableOn (fun x : ℝ => ‖f (x : ℂ)‖) (Ioi A) := hf.integrable_norm.integrableOn
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi A hint tendsto_id
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop A] with B hB
  have hC0 : (0 : ℝ) < (4 * π)⁻¹ := by positivity
  exact clarkTail_norm_le hC0 le_rfl (by norm_num) hA hB
    (hf.diff.continuous.comp continuous_ofReal).continuousOn
    (fun x hx0 _ => hf.env_pos hn hx0)

/-- **Density hypotheses for a norm-one `f ∈ 𝒢`.**  If `f ≥ 0` on `(-∞, u_T]`, `-R ≤ u_T`, `R ≥ 1` and
`ε := ∫ f ≥ 0`, then `f` satisfies `DensityHyp` on `|u| ≤ R` with `ς = 0`, `C₀ = 1/(4π)` and
`δ = ε + τ(R)`. -/
theorem densityHyp (hf : AiryG f) (hn : ∫ x : ℝ, ‖f (x : ℂ)‖ = 1) {R uT : ℝ} (hR : 1 ≤ R)
    (hRu : -R ≤ uT) (hnn : ∀ x : ℝ, x ≤ uT → 0 ≤ (f (x : ℂ)).re)
    (hε : 0 ≤ ∫ x : ℝ, (f (x : ℂ)).re) :
    DensityHyp (4 * π)⁻¹ R 0 ((∫ x : ℝ, (f (x : ℂ)).re) + tailBound (4 * π)⁻¹ R) f uT := by
  have hR0 : 0 ≤ R := by linarith
  have hτ := hf.tail_Ioi hn hR
  have hint_g : Integrable (fun x : ℝ => (f (x : ℂ)).re) := hf.integrable_re
  have hint_n : Integrable (fun x : ℝ => ‖f (x : ℂ)‖) := hf.integrable_norm
  -- splitting of integrals along `Iic`, `Ioi`
  have hsplit : ∀ (φ : ℝ → ℝ), Integrable φ → ∀ a : ℝ,
      (∫ x in Iic R, φ x) - (∫ x in Iic a, φ x) = ∫ x in a..R, φ x := fun φ hφ a =>
    intervalIntegral.integral_Iic_sub_Iic hφ.integrableOn hφ.integrableOn
  have htot : ∀ (φ : ℝ → ℝ), Integrable φ → (∫ x in Iic R, φ x) + (∫ x in Ioi R, φ x) = ∫ x, φ x :=
    fun φ hφ => intervalIntegral.integral_Iic_add_Ioi hφ.integrableOn hφ.integrableOn
  refine
    { analytic := fun z _ => hf.diff.analyticAt z
      real := fun x _ => hf.real x
      env := ?_
      nonneg := fun x _ hx => hnn x hx
      l1 := ?_
      neg := ?_
      top := ?_ }
  · intro u _ hu
    have h1 := hf.env_sharp hu
    have hre := re_cpow_half_pos_of_cut hu
    have hu_ne : u ≠ 0 := fun h0 => hu (by simp [h0])
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hB := hf.norm_Iic_le hn
    have he := airyEnv_pos u
    have hq : 0 ≤ ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg hu_norm_pos.le _) (inv_nonneg.mpr hre.le)
    calc ‖f u‖ ≤ (4 * π)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := h1
      _ = (4 * π)⁻¹ * (∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖) * airyEnv u *
          (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by ring
      _ ≤ (4 * π)⁻¹ * 1 * airyEnv u * (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
          gcongr
      _ = _ := by simp [mul_assoc]
  · rw [intervalIntegral.integral_of_le (by linarith)]
    rw [← hn]
    exact setIntegral_le_integral hint_n (Eventually.of_forall fun x => norm_nonneg _)
  · -- negative mass
    set φ : ℝ → ℝ := fun x => max 0 (-(f (x : ℂ)).re) with hφ
    have hφ_int : Integrable φ :=
      hint_g.neg_part.congr (Eventually.of_forall fun x => max_comm _ _)
    have hφ_eq : ∀ x : ℝ, φ x = (‖f (x : ℂ)‖ - (f (x : ℂ)).re) / 2 := by
      intro x
      rw [hf.norm_real x]
      rcases le_total 0 (f (x : ℂ)).re with h | h
      · rw [hφ]; simp only; rw [max_eq_left (by linarith), abs_of_nonneg h]; ring
      · rw [hφ]; simp only; rw [max_eq_right (by linarith), abs_of_nonpos h]; ring
    have hφ_val : ∫ x : ℝ, φ x = (1 - ∫ x : ℝ, (f (x : ℂ)).re) / 2 := by
      simp_rw [hφ_eq]
      rw [integral_div, integral_sub hint_n hint_g, hn]
    have hφ_left : ∫ x in Iic (-R), φ x = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      have := hnn x (le_trans (mem_Iic.mp hx) (by linarith))
      rw [hφ]; exact max_eq_left (by linarith)
    have hφ_right : ∫ x in Ioi R, φ x ≤ tailBound (4 * π)⁻¹ R := by
      refine le_trans (setIntegral_mono hφ_int.integrableOn hint_n.integrableOn fun x => ?_) hτ
      rw [hφ]
      refine max_le (norm_nonneg _) ?_
      exact (neg_le_abs _).trans (by rw [hf.norm_real x])
    have h1 := hsplit φ hφ_int (-R)
    have h2 := htot φ hφ_int
    rw [hφ_left, sub_zero] at h1
    linarith
  · intro R' hR' hR'u
    set g : ℝ → ℝ := fun x => (f (x : ℂ)).re with hg
    have h1 := hsplit g hint_g (-R')
    have h2 := htot g hint_g
    have hleft : 0 ≤ ∫ x in Iic (-R'), g x :=
      setIntegral_nonneg measurableSet_Iic fun x hx => hnn x (le_trans (mem_Iic.mp hx) hR'u)
    have hright : -(∫ x in Ioi R, g x) ≤ tailBound (4 * π)⁻¹ R := by
      rw [← integral_neg]
      refine le_trans (setIntegral_mono hint_g.neg.integrableOn hint_n.integrableOn fun x => ?_) hτ
      rw [hg]
      exact (neg_le_abs _).trans (by rw [hf.norm_real x])
    linarith

end AiryG

lemma hasDerivAt_re_ofReal {h : ℂ → ℂ} (hd : Differentiable ℂ h) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (h (t : ℂ)).re) ((deriv h (x : ℂ)).re) x := by
  have hdG : HasDerivAt (fun t : ℝ => h (t : ℂ)) (deriv h (x : ℂ)) x := by
    simpa only [mul_one] using (hd (x : ℂ)).hasDerivAt.comp_ofReal
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hdG

lemma tailBound_tendsto_real (C₀ : ℝ) : Tendsto (fun x : ℝ => tailBound C₀ x) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => -(5 / 6 : ℝ) * x) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num : -(5 / 6 : ℝ) < 0)
  simpa [tailBound] using ((Real.tendsto_exp_atBot.comp ht).const_mul ((6 / 5 : ℝ) * C₀))

end FormalResearch.ModularBootstrap.Stability
