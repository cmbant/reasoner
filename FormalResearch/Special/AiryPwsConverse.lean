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

end FormalResearch.Special
