module

public import FormalResearch.Special.AiryPwsPW

/-!
# Theorem 3.1 `(b) ⇒ (a)`, construction of the entire function `f_E`

Let `Fh = F̃` be holomorphic on `Im ζ > 0`, continuous on `Im ζ ≥ 0` and bounded by `B` there (`H^∞`).  Put
`Λ(ζ) = k⁻¹ e^{iζ³/12} Fh(ζ)` (`airyLam`; `|e^{iζ³/12}| = exp(-(3ξ²η-η³)/12)` is a Gaussian in `ξ`) and, for `η > 0`,
`I_η(u) = ∫_ℝ Λ(ξ+iη) e^{i(ξ+iη)u} dξ`, `f_E = I_η/(2π)` (`airyIeta`).

* `norm_airyKE_le_maj`: `|Λ(ξ+iη)e^{i(ξ+iη)u}| ≤ (B/k) exp(η³/12+η|u|+2|u|²/η) e^{-ηξ²/8}` (uniform in `|u| ≤ ρ`);
* `differentiable_airyIeta`: `u ↦ I_η(u)` is entire (differentiation under the integral sign, `ℂ`-parameter);
* `airyIeta_eq`: `I_η(u)` is **independent of `η > 0`** (Cauchy–Goursat on `[-R,R]×[η₁,η₂]`, the vertical sides vanish by the Gaussian);
* `norm_airyIeta_le`: the saddle estimate `|I_η(u)| ≤ (B/k) √(4π/η) exp(η³/12 - η Re u + (Im u)²/η)`.

The choice `η = 2 Re √u` gives `|f_E(u)| ≤ B e(u)/(k √(2π Re √u))`, and a second choice near the cut `η = 1/(1+|u|)`, the global bound
`|f_E(u)| ≤ C (1+|u|) e(u)` in `AiryPwsConverse2`.

**Not formalised** here: the identification `f = f_E` a.e. with the given `L¹` function (`AiryPwsConverse2`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

/-- `(b)`: holomorphic on `Im ζ > 0`, continuous on the closure, bounded by `B` on `Im ζ ≥ 0`. -/
structure AiryHinf (Fh : ℂ → ℂ) (B : ℝ) : Prop where
  diffContOnCl : DiffContOnCl ℂ Fh {ζ : ℂ | 0 < ζ.im}
  bound : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖Fh ζ‖ ≤ B

/-- `Λ(ζ) = k⁻¹ e^{iζ³/12} F̃(ζ)`. -/
noncomputable def airyLam (Fh : ℂ → ℂ) (ζ : ℂ) : ℂ := ((airyPhiK : ℂ))⁻¹ * cexp (I * ζ ^ 3 / 12) * Fh ζ

/-- The kernel `Λ(ζ) e^{iζu}`. -/
noncomputable def airyKE (Fh : ℂ → ℂ) (u ζ : ℂ) : ℂ := airyLam Fh ζ * cexp (I * ζ * u)

/-- `I_η(u) = ∫ Λ(ξ+iη) e^{i(ξ+iη)u} dξ`. -/
noncomputable def airyIeta (Fh : ℂ → ℂ) (η : ℝ) (u : ℂ) : ℂ := ∫ ξ : ℝ, airyKE Fh u ((ξ : ℂ) + η * I)

lemma airyHinf_nonneg {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) : 0 ≤ B :=
  le_trans (norm_nonneg _) (h.bound 0 (by simp))

lemma norm_cexp_cube (ζ : ℂ) : ‖cexp (I * ζ ^ 3 / 12)‖ =
    Real.exp (-(3 * ζ.re ^ 2 * ζ.im - ζ.im ^ 3) / 12) := by
  rw [Complex.norm_exp]
  congr 1
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

lemma norm_cexp_mul (ζ u : ℂ) : ‖cexp (I * ζ * u)‖ = Real.exp (-(ζ.re * u.im + ζ.im * u.re)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `‖K(ζ,u)‖` for `ζ = ξ + iη`, `η ≥ 0`. -/
lemma norm_airyKE_le {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) (u ζ : ℂ) (hζ : 0 ≤ ζ.im) :
    ‖airyKE Fh u ζ‖ ≤ B / airyPhiK * Real.exp (ζ.im ^ 3 / 12 - ζ.im * ζ.re ^ 2 / 4 - ζ.re * u.im - ζ.im * u.re) := by
  unfold airyKE airyLam
  rw [norm_mul, norm_mul, norm_mul, norm_cexp_cube, norm_cexp_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos airyPhiK_pos]
  have hb := h.bound ζ hζ
  have e : Real.exp (-(3 * ζ.re ^ 2 * ζ.im - ζ.im ^ 3) / 12) * Real.exp (-(ζ.re * u.im + ζ.im * u.re)) =
      Real.exp (ζ.im ^ 3 / 12 - ζ.im * ζ.re ^ 2 / 4 - ζ.re * u.im - ζ.im * u.re) := by
    rw [← Real.exp_add]; congr 1; ring
  have hk := airyPhiK_pos
  calc (airyPhiK)⁻¹ * Real.exp (-(3 * ζ.re ^ 2 * ζ.im - ζ.im ^ 3) / 12) * ‖Fh ζ‖ *
        Real.exp (-(ζ.re * u.im + ζ.im * u.re))
      = (airyPhiK)⁻¹ * ‖Fh ζ‖ * (Real.exp (-(3 * ζ.re ^ 2 * ζ.im - ζ.im ^ 3) / 12) *
        Real.exp (-(ζ.re * u.im + ζ.im * u.re))) := by ring
    _ ≤ (airyPhiK)⁻¹ * B * (Real.exp (-(3 * ζ.re ^ 2 * ζ.im - ζ.im ^ 3) / 12) *
        Real.exp (-(ζ.re * u.im + ζ.im * u.re))) := by
        gcongr
    _ = _ := by rw [e]; ring

/-- Uniform Gaussian majorant for `‖u‖ ≤ ρ`, `ζ = ξ + iη`, `η > 0`. -/
lemma norm_airyKE_le_maj {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η ρ : ℝ} (hη : 0 < η) {u : ℂ}
    (hu : ‖u‖ ≤ ρ) (ξ : ℝ) :
    ‖airyKE Fh u ((ξ : ℂ) + η * I)‖ ≤
      B / airyPhiK * Real.exp (η ^ 3 / 12 + η * ρ + 2 * ρ ^ 2 / η) * Real.exp (-(η / 8) * ξ ^ 2) := by
  have h1 := norm_airyKE_le h u ((ξ : ℂ) + η * I) (by simp [hη.le])
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_mul] at h1
  have hB := airyHinf_nonneg h
  have hk := airyPhiK_pos
  refine h1.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hr : |u.re| ≤ ρ := (Complex.abs_re_le_norm u).trans hu
  have hi : |u.im| ≤ ρ := (Complex.abs_im_le_norm u).trans hu
  have h2 : -(ξ * u.im) ≤ ρ * |ξ| := by
    have := abs_mul ξ u.im
    nlinarith [neg_abs_le (ξ * u.im), abs_nonneg ξ, abs_nonneg u.im, mul_le_mul_of_nonneg_left hi (abs_nonneg ξ)]
  have h3 : -(η * u.re) ≤ η * ρ := by nlinarith [neg_abs_le u.re]
  have h4 : ρ * |ξ| ≤ (η / 8) * ξ ^ 2 + 2 * ρ ^ 2 / η := by
    have : 0 ≤ (η / 8) * ξ ^ 2 + 2 * ρ ^ 2 / η - ρ * |ξ| := by
      have e : (η / 8) * ξ ^ 2 + 2 * ρ ^ 2 / η - ρ * |ξ| = (η / 8) * (|ξ| - 4 * ρ / η) ^ 2 := by
        rw [← sq_abs ξ]; field_simp; ring
      rw [e]; positivity
    linarith
  have h5 : η * 0 = 0 := by ring
  nlinarith [sq_nonneg ξ]

lemma continuousOn_airyLam {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) :
    ContinuousOn (airyLam Fh) {ζ : ℂ | 0 ≤ ζ.im} := by
  have hc : ContinuousOn Fh {ζ : ℂ | 0 ≤ ζ.im} := by
    simpa [closure_setOfPred_lt_im] using h.diffContOnCl.continuousOn
  unfold airyLam
  have : Continuous fun ζ : ℂ => ((airyPhiK : ℂ))⁻¹ * cexp (I * ζ ^ 3 / 12) := by fun_prop
  exact this.continuousOn.mul hc

lemma continuous_airyKE_line {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η : ℝ} (hη : 0 < η) (u : ℂ) :
    Continuous fun ξ : ℝ => airyKE Fh u ((ξ : ℂ) + η * I) := by
  unfold airyKE
  have h1 : Continuous fun ξ : ℝ => airyLam Fh ((ξ : ℂ) + η * I) :=
    (continuousOn_airyLam h).comp_continuous (by fun_prop) (fun ξ => by simp [hη.le])
  exact h1.mul (by fun_prop)

lemma integrable_airyKE {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η : ℝ} (hη : 0 < η) (u : ℂ) :
    Integrable fun ξ : ℝ => airyKE Fh u ((ξ : ℂ) + η * I) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (by positivity : 0 < η / 8)).const_mul
    (B / airyPhiK * Real.exp (η ^ 3 / 12 + η * ‖u‖ + 2 * ‖u‖ ^ 2 / η)))
    (continuous_airyKE_line h hη u).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  exact norm_airyKE_le_maj h hη le_rfl ξ

/-- The saddle estimate: for every `η > 0`, `|I_η(u)| ≤ (B/k) √(4π/η) exp(η³/12 - η Re u + (Im u)²/η)`. -/
theorem norm_airyIeta_le {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η : ℝ} (hη : 0 < η) (u : ℂ) :
    ‖airyIeta Fh η u‖ ≤ B / airyPhiK * √(4 * π / η) *
      Real.exp (η ^ 3 / 12 - η * u.re + u.im ^ 2 / η) := by
  unfold airyIeta
  set c : ℝ := B / airyPhiK * Real.exp (η ^ 3 / 12 - η * u.re + u.im ^ 2 / η) with hc
  have hpt : ∀ ξ : ℝ, ‖airyKE Fh u ((ξ : ℂ) + η * I)‖ ≤
      c * Real.exp (-(η / 4) * (ξ + 2 * u.im / η) ^ 2) := by
    intro ξ
    have h1 := norm_airyKE_le h u ((ξ : ℂ) + η * I) (by simp [hη.le])
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_mul] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hc, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  have hint : Integrable fun ξ : ℝ => c * Real.exp (-(η / 4) * (ξ + 2 * u.im / η) ^ 2) :=
    ((integrable_exp_neg_mul_sq (by positivity : 0 < η / 4)).comp_add_right (2 * u.im / η)).const_mul c
  have hval : ∫ ξ : ℝ, c * Real.exp (-(η / 4) * (ξ + 2 * u.im / η) ^ 2) = c * √(4 * π / η) := by
    rw [integral_const_mul]
    congr 1
    have := integral_add_right_eq_self (μ := volume) (fun ξ : ℝ => Real.exp (-(η / 4) * ξ ^ 2)) (2 * u.im / η)
    rw [this, integral_gaussian]
    congr 1
    field_simp
  calc ‖∫ ξ : ℝ, airyKE Fh u ((ξ : ℂ) + η * I)‖
      ≤ ∫ ξ : ℝ, c * Real.exp (-(η / 4) * (ξ + 2 * u.im / η) ^ 2) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = c * √(4 * π / η) := hval
    _ = _ := by rw [hc]; ring

lemma hasDerivAt_airyKE_u (Fh : ℂ → ℂ) (ζ u : ℂ) :
    HasDerivAt (fun u : ℂ => airyKE Fh u ζ) (airyKE Fh u ζ * (I * ζ)) u := by
  unfold airyKE
  have h1 : HasDerivAt (fun u : ℂ => I * ζ * u) (I * ζ) u := by
    simpa using (hasDerivAt_id u).const_mul (I * ζ)
  have h2 := (h1.cexp).const_mul (airyLam Fh ζ)
  convert h2 using 1
  ring

lemma continuous_airyKE_u {Fh : ℂ → ℂ} (ζ : ℂ) : Continuous fun u : ℂ => airyKE Fh u ζ := by
  unfold airyKE; fun_prop

/-- `u ↦ I_η(u)` is entire. -/
theorem differentiable_airyIeta {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η : ℝ} (hη : 0 < η) :
    Differentiable ℂ (airyIeta Fh η) := by
  intro u0
  set ρ : ℝ := ‖u0‖ + 1 with hρ
  set C : ℝ := B / airyPhiK * Real.exp (η ^ 3 / 12 + η * ρ + 2 * ρ ^ 2 / η) with hC
  have hB := airyHinf_nonneg h
  have hk := airyPhiK_pos
  have hC0 : 0 ≤ C := by positivity
  have ha : 0 < η / 8 := by positivity
  have hball : Metric.ball u0 1 ∈ 𝓝 u0 := Metric.ball_mem_nhds _ one_pos
  have hbd : ∀ u ∈ Metric.ball u0 1, ‖u‖ ≤ ρ := by
    intro u hu
    have : ‖u - u0‖ < 1 := by simpa [dist_eq_norm] using hu
    have := norm_le_norm_add_norm_sub' u u0
    rw [hρ]; linarith [norm_sub_rev u u0, norm_sub_rev u0 u]
  have hint : Integrable fun ξ : ℝ => C * (η * Real.exp (-(η / 8) * ξ ^ 2) + ‖ξ * Real.exp (-(η / 8) * ξ ^ 2)‖) :=
    ((((integrable_exp_neg_mul_sq ha).const_mul η).add (integrable_mul_exp_neg_mul_sq ha).norm).const_mul C)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (u : ℂ) (ξ : ℝ) => airyKE Fh u ((ξ : ℂ) + η * I))
    (F' := fun (u : ℂ) (ξ : ℝ) => airyKE Fh u ((ξ : ℂ) + η * I) * (I * ((ξ : ℂ) + η * I)))
    (s := Metric.ball u0 1) (x₀ := u0) (bound := fun ξ => C * (η * Real.exp (-(η / 8) * ξ ^ 2) +
      ‖ξ * Real.exp (-(η / 8) * ξ ^ 2)‖)) hball
    (Eventually.of_forall fun u => (continuous_airyKE_line h hη u).aestronglyMeasurable)
    (integrable_airyKE h hη u0)
    (by
      have h1 := continuous_airyKE_line h hη u0
      have h2 : Continuous fun ξ : ℝ => I * ((ξ : ℂ) + η * I) := by fun_prop
      exact (h1.mul h2).aestronglyMeasurable)
    (Eventually.of_forall fun ξ u hu => by
      have h1 := norm_airyKE_le_maj h hη (hbd u hu) ξ
      have h2 : ‖I * ((ξ : ℂ) + η * I)‖ ≤ η + |ξ| := by
        rw [norm_mul, Complex.norm_I, one_mul]
        refine (norm_add_le _ _).trans ?_
        simp [abs_of_pos hη, add_comm]
      rw [norm_mul]
      have hE := Real.exp_pos (-(η / 8) * ξ ^ 2)
      have h3 : ‖ξ * Real.exp (-(η / 8) * ξ ^ 2)‖ = |ξ| * Real.exp (-(η / 8) * ξ ^ 2) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE]
      rw [h3]
      calc ‖airyKE Fh u ((ξ : ℂ) + η * I)‖ * ‖I * ((ξ : ℂ) + η * I)‖
          ≤ (C * Real.exp (-(η / 8) * ξ ^ 2)) * (η + |ξ|) := by gcongr
        _ = _ := by ring)
    hint
    (Eventually.of_forall fun ξ u _ => hasDerivAt_airyKE_u Fh _ u)
  exact (key.2).differentiableAt

lemma tendsto_gauss_lin (a b c : ℝ) (hb : 0 < b) :
    Tendsto (fun R : ℝ => Real.exp (-b * R ^ 2 + a * R + c)) atTop (𝓝 0) := by
  refine (Real.tendsto_exp_atBot).comp ?_
  have h1 : Tendsto (fun R : ℝ => (R - a / (2 * b)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 := (h1.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  have h3 := tendsto_atBot_add_const_right _ (a ^ 2 / (4 * b) + c) h2
  refine h3.congr fun R => ?_
  field_simp
  ring

lemma airyKE_differentiableOn {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) (u : ℂ) :
    DifferentiableOn ℂ (airyKE Fh u) {ζ : ℂ | 0 < ζ.im} := by
  unfold airyKE airyLam
  have hF := h.diffContOnCl.differentiableOn
  have e : Differentiable ℂ fun ζ : ℂ => ((airyPhiK : ℂ))⁻¹ * cexp (I * ζ ^ 3 / 12) := by fun_prop
  have e2 : Differentiable ℂ fun ζ : ℂ => cexp (I * ζ * u) := by fun_prop
  exact ((e.differentiableOn).mul hF).mul e2.differentiableOn

/-- Vertical-side bound for the Cauchy rectangle. -/
lemma norm_airyKE_vert {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η₁ η₂ : ℝ} (hη₁ : 0 < η₁)
    (hη : η₁ ≤ η₂) (u : ℂ) {x y : ℝ} (hy : y ∈ Set.Icc η₁ η₂) :
    ‖airyKE Fh u ((x : ℂ) + y * I)‖ ≤ B / airyPhiK * Real.exp (-(η₁ / 4) * |x| ^ 2 + |u.im| * |x| +
      (η₂ ^ 3 / 12 + η₂ * |u.re|)) := by
  have hy0 : 0 < y := lt_of_lt_of_le hη₁ hy.1
  have h1 := norm_airyKE_le h u ((x : ℂ) + y * I) (by simp [hy0.le])
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_mul] at h1
  have hB := airyHinf_nonneg h
  have hk := airyPhiK_pos
  refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  have a1 : y ^ 3 ≤ η₂ ^ 3 := pow_le_pow_left₀ hy0.le hy.2 3
  have a2 : η₁ * x ^ 2 ≤ y * x ^ 2 := mul_le_mul_of_nonneg_right hy.1 (sq_nonneg x)
  have a3 : -(x * u.im) ≤ |u.im| * |x| := by
    have := neg_abs_le (x * u.im); rw [abs_mul] at this; nlinarith [abs_nonneg x, abs_nonneg u.im, neg_le_abs (x * u.im)]
  have a4 : -(y * u.re) ≤ η₂ * |u.re| := by
    have := neg_le_abs u.re
    nlinarith [abs_nonneg u.re, hy.2, neg_abs_le u.re]
  have a5 : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith

lemma airyIeta_eq {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (u : ℂ) :
    airyIeta Fh η₁ u = airyIeta Fh η₂ u := by
  have hη₂ : 0 < η₂ := lt_of_lt_of_le hη₁ hη
  set g := airyKE Fh u with hg
  set Hh : ℝ → ℝ → ℂ := fun R y => ∫ x : ℝ in (-R)..R, g ((x : ℂ) + y * I) with hHh
  set V : ℝ → ℂ := fun R => I • (∫ y : ℝ in η₁..η₂, g ((R : ℂ) + y * I)) -
      I • (∫ y : ℝ in η₁..η₂, g (((-R : ℝ) : ℂ) + y * I)) with hV
  have hcauchy : ∀ R : ℝ, Hh R η₁ - Hh R η₂ + V R = 0 := by
    intro R
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
      (((-R : ℝ) : ℂ) + η₁ * I) ((R : ℂ) + η₂ * I) (by
        refine (airyKE_differentiableOn h u).mono ?_
        intro ζ hζ
        rw [Complex.mem_reProdIm] at hζ
        have := hζ.2
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
          Complex.ofReal_re, Complex.I_im, mul_one, zero_add, add_zero] at this
        show 0 < ζ.im
        rcases le_total η₁ η₂ with _ | _
        · rw [Set.uIcc_of_le hη] at this; linarith [this.1]
        · rw [Set.uIcc_of_ge ‹_›] at this; linarith [this.1])
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_mul, zero_add] at this
    simp only [hHh, hV]
    linear_combination this
  have hT : ∀ y : ℝ, 0 < y → Tendsto (fun R : ℝ => Hh R y) atTop (𝓝 (airyIeta Fh y u)) := by
    intro y hy
    exact intervalIntegral_tendsto_integral (integrable_airyKE h hy u) tendsto_neg_atTop_atBot tendsto_id
  have hVt : Tendsto V atTop (𝓝 0) := by
    have hbd : ∀ R : ℝ, ‖V R‖ ≤ 2 * ((η₂ - η₁) * (B / airyPhiK * Real.exp (-(η₁ / 4) * R ^ 2 + |u.im| * R +
        (η₂ ^ 3 / 12 + η₂ * |u.re|)))) ∨ R < 0 := by
      intro R
      rcases lt_or_ge R 0 with hR | hR
      · exact Or.inr hR
      left
      have hv : ∀ x : ℝ, ‖∫ y : ℝ in η₁..η₂, g ((x : ℂ) + y * I)‖ ≤
          B / airyPhiK * Real.exp (-(η₁ / 4) * |x| ^ 2 + |u.im| * |x| + (η₂ ^ 3 / 12 + η₂ * |u.re|)) *
            |η₂ - η₁| := fun x =>
        intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => by
          rw [Set.uIoc_of_le hη] at hy
          exact norm_airyKE_vert h hη₁ hη u ⟨hy.1.le, hy.2⟩)
      have e1 := hv R
      have e2 := hv (-R)
      rw [abs_of_nonneg hR] at e1
      rw [abs_neg, abs_of_nonneg hR] at e2
      rw [abs_of_nonneg (sub_nonneg.mpr hη)] at e1 e2
      simp only [hV]
      calc ‖I • (∫ y : ℝ in η₁..η₂, g ((R : ℂ) + y * I)) - I • (∫ y : ℝ in η₁..η₂, g (((-R : ℝ) : ℂ) + y * I))‖
          ≤ ‖I • (∫ y : ℝ in η₁..η₂, g ((R : ℂ) + y * I))‖ +
            ‖I • (∫ y : ℝ in η₁..η₂, g (((-R : ℝ) : ℂ) + y * I))‖ := norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
          linarith
    have hlim : Tendsto (fun R : ℝ => 2 * ((η₂ - η₁) * (B / airyPhiK * Real.exp (-(η₁ / 4) * R ^ 2 +
        |u.im| * R + (η₂ ^ 3 / 12 + η₂ * |u.re|))))) atTop (𝓝 0) := by
      have := ((tendsto_gauss_lin |u.im| (η₁ / 4) (η₂ ^ 3 / 12 + η₂ * |u.re|) (by positivity)).const_mul
        (B / airyPhiK)).const_mul (η₂ - η₁) |>.const_mul 2
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rcases hbd R with h1 | h1
    · exact h1
    · exact absurd hR (not_le.mpr h1)
  have h12 : Tendsto (fun R : ℝ => Hh R η₁ - Hh R η₂) atTop (𝓝 (airyIeta Fh η₁ u - airyIeta Fh η₂ u)) :=
    (hT η₁ hη₁).sub (hT η₂ hη₂)
  have h0 : Tendsto (fun R : ℝ => Hh R η₁ - Hh R η₂) atTop (𝓝 0) := by
    have := hVt.neg
    simp only [neg_zero] at this
    refine this.congr fun R => ?_
    have := hcauchy R
    linear_combination -this
  exact sub_eq_zero.mp (tendsto_nhds_unique h12 h0)

lemma airyIeta_eq' {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (u : ℂ) :
    airyIeta Fh η₁ u = airyIeta Fh η₂ u := by
  rcases le_total η₁ η₂ with hle | hle
  · exact airyIeta_eq h hη₁ hle u
  · exact (airyIeta_eq h hη₂ hle u).symm

/-- Parametrisation of the principal square root. -/
lemma airy_sqrt_facts (u : ℂ) : ∃ a b : ℝ, 0 ≤ a ∧ u.re = a ^ 2 - b ^ 2 ∧ u.im = 2 * a * b ∧
    ‖u‖ = a ^ 2 + b ^ 2 ∧ airyEnv u = Real.exp (-(4 / 3) * (a ^ 3 - 3 * a * b ^ 2)) := by
  set s : ℂ := u ^ (1 / 2 : ℂ) with hs
  have hs2 : s ^ 2 = u := by
    have := Complex.cpow_nat_inv_pow u (n := 2) (by norm_num)
    rw [hs]; convert this using 3; norm_num
  have hs3 : u ^ (3 / 2 : ℂ) = s ^ 3 := by
    rcases eq_or_ne u 0 with rfl | hu
    · rw [hs]; simp
    · have : (3 / 2 : ℂ) = 1 + 1 / 2 := by norm_num
      rw [this, Complex.cpow_add _ _ hu, Complex.cpow_one, pow_succ, hs2]
  have ha : 0 ≤ s.re := by
    rcases eq_or_ne u 0 with rfl | hu
    · rw [hs]; simp
    · rw [hs, Complex.cpow_def_of_ne_zero hu, Complex.exp_re]
      refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
      · simp only [Complex.mul_im, Complex.log_re, Complex.log_im]
        have := Complex.neg_pi_lt_arg u
        norm_num
        linarith
      · simp only [Complex.mul_im, Complex.log_re, Complex.log_im]
        have := Complex.arg_le_pi u
        norm_num
        linarith
  refine ⟨s.re, s.im, ha, ?_, ?_, ?_, ?_⟩
  · rw [← hs2]; simp [sq, Complex.mul_re]
  · rw [← hs2]; simp [sq, Complex.mul_im]; ring
  · rw [← hs2, norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  · unfold airyEnv
    rw [hs3]
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring

lemma sqrt_aux {η N : ℝ} (hη : 0 < η) (hN : 0 ≤ N) (h : 1 / η ≤ (1 + N) ^ 2) :
    √(4 * π / η) ≤ √(4 * π) * (1 + N) := by
  have : 4 * π / η ≤ 4 * π * (1 + N) ^ 2 := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h (by positivity)
  calc √(4 * π / η) ≤ √(4 * π * (1 + N) ^ 2) := Real.sqrt_le_sqrt this
    _ = √(4 * π) * (1 + N) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **Global growth bound** for `I_1`: `|I_1(u)| ≤ (B/k) √(4π) e⁸ (1+|u|) e(u)`. -/
theorem norm_airyIeta_global {Fh : ℂ → ℂ} {B : ℝ} (h : AiryHinf Fh B) (u : ℂ) :
    ‖airyIeta Fh 1 u‖ ≤ B / airyPhiK * √(4 * π) * Real.exp 8 * (1 + ‖u‖) * airyEnv u := by
  obtain ⟨a, b, ha, hre, him, hn, henv⟩ := airy_sqrt_facts u
  have hB := airyHinf_nonneg h
  have hk := airyPhiK_pos
  have hN : 0 ≤ ‖u‖ := norm_nonneg u
  set N := ‖u‖ with hNdef
  have hcoef : 0 ≤ B / airyPhiK * √(4 * π) := by positivity
  by_cases hc : 1 / (1 + N) ≤ a
  · -- saddle at `η = 2a`
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) hc
    have h1 := norm_airyIeta_le h (η := 2 * a) (by positivity) u
    rw [← airyIeta_eq' h (by norm_num : (0 : ℝ) < 1) (by positivity : (0 : ℝ) < 2 * a)] at h1
    have hex : (2 * a) ^ 3 / 12 - 2 * a * u.re + u.im ^ 2 / (2 * a) = -(4 / 3) * (a ^ 3 - 3 * a * b ^ 2) := by
      rw [hre, him]; field_simp; ring
    rw [hex, ← henv] at h1
    have hs : √(4 * π / (2 * a)) ≤ √(4 * π) * (1 + N) := by
      refine sqrt_aux (by positivity) hN ?_
      have : 1 / a ≤ 1 + N := by
        rw [div_le_iff₀ hapos]
        rw [div_le_iff₀ (by positivity)] at hc
        nlinarith
      have h2 : 1 / (2 * a) ≤ 1 + N := by
        calc 1 / (2 * a) = (1 / a) / 2 := by field_simp
          _ ≤ 1 + N := by linarith
      nlinarith
    have he8 : (1 : ℝ) ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
    have hen := (airyEnv_pos u).le
    calc ‖airyIeta Fh 1 u‖ ≤ B / airyPhiK * √(4 * π / (2 * a)) * airyEnv u := h1
      _ ≤ B / airyPhiK * (√(4 * π) * (1 + N)) * airyEnv u := by gcongr
      _ ≤ B / airyPhiK * (√(4 * π) * (1 + N)) * airyEnv u * Real.exp 8 := le_mul_of_one_le_right (by positivity) he8
      _ = _ := by ring
  · -- near the cut: `η = 1/(1+N)`
    push_neg at hc
    set η : ℝ := 1 / (1 + N) with hη
    have hηpos : 0 < η := by positivity
    have hη1 : η * (1 + N) = 1 := by rw [hη]; field_simp
    have hinv : 1 / η = 1 + N := by rw [hη]; field_simp
    have h1 := norm_airyIeta_le h hηpos u
    rw [← airyIeta_eq' h (by norm_num : (0 : ℝ) < 1) hηpos] at h1
    have hηle : η ≤ 1 := by rw [hη, div_le_one (by positivity)]; linarith
    have hb2 : b ^ 2 ≤ N := by rw [hn]; nlinarith [sq_nonneg a]
    have ha2 : a ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ ha hc.le 2
    have hexp : η ^ 3 / 12 - η * u.re + u.im ^ 2 / η ≤ 6 := by
      have t1 : η ^ 3 / 12 ≤ 1 / 12 := by
        have : η ^ 3 ≤ 1 := pow_le_one₀ hηpos.le hηle
        linarith
      have t2 : -(η * u.re) ≤ 1 := by
        have : -u.re ≤ N := by rw [hre, hn]; nlinarith [sq_nonneg a, sq_nonneg b]
        nlinarith
      have t3 : u.im ^ 2 / η ≤ 4 := by
        rw [div_eq_mul_one_div, hinv, him]
        have : (2 * a * b) ^ 2 = 4 * (a ^ 2 * b ^ 2) := by ring
        rw [this]
        have h5 : a ^ 2 * b ^ 2 ≤ η ^ 2 * N := mul_le_mul ha2 hb2 (sq_nonneg b) (sq_nonneg η)
        have h6 : η ^ 2 * N * (1 + N) ≤ 1 := by
          have : η ^ 2 * N * (1 + N) = η * N * (η * (1 + N)) := by ring
          rw [this, hη1, mul_one]
          nlinarith
        nlinarith
      linarith
    have hs : √(4 * π / η) ≤ √(4 * π) * (1 + N) := by
      refine sqrt_aux hηpos hN ?_
      rw [hinv]; nlinarith
    have hen : Real.exp (-(4 / 3)) ≤ airyEnv u := by
      rw [henv]
      refine Real.exp_le_exp.mpr ?_
      have ha1 : a ≤ 1 := hc.le.trans hηle
      have : a ^ 3 ≤ 1 := pow_le_one₀ ha ha1
      nlinarith [mul_nonneg ha (sq_nonneg b)]
    have e6 : Real.exp 6 ≤ Real.exp 8 * airyEnv u := by
      calc Real.exp 6 ≤ Real.exp 8 * Real.exp (-(4 / 3)) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by norm_num)
        _ ≤ _ := by gcongr
    calc ‖airyIeta Fh 1 u‖ ≤ B / airyPhiK * √(4 * π / η) * Real.exp (η ^ 3 / 12 - η * u.re + u.im ^ 2 / η) := h1
      _ ≤ B / airyPhiK * (√(4 * π) * (1 + N)) * Real.exp 6 := by
          gcongr
      _ ≤ B / airyPhiK * (√(4 * π) * (1 + N)) * (Real.exp 8 * airyEnv u) := by gcongr
      _ = _ := by ring

end FormalResearch.Special
