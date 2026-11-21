module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The `L¹` norm of a Fourier transform and `‖T_c f‖_∞` via `H¹(ℝ)` (FG.3, T.5)

Source: `CFT/sign_uncertainty/paper/ce_physical_log_far.tex`, Lemma FG.3 (`cepf:FG3`, eqs. `(FG.3a)`–`(FG.3)`),
and `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.5 (`mat:T5`, eq. `(FG.3c)`).

Normalisation: `f̂(ξ) = ∫ f(X) e^{-iXξ} dX` (`fourierPaper`), with `L²` extension `fourierPaperL2` defined via
`MeasureTheory.Lp.fourierTransformₗᵢ`. `l2norm f = (∫ |f|²)^{1/2}`.

**Statements proved:**

* `fourier_L1_le_sqrt_mul` (Schwartz) and `fourier_L1_le_sqrt_mul_H1` (**Lemma T.5 / `(FG.3c)`**, for any `f ∈ H¹(ℝ)`
  via `WeakDerivL2 f f'`): `𝓕 f ∈ L¹(ℝ)` and `∫ ξ, ‖f̂(ξ)‖ ≤ 2π · (‖f‖₂ · ‖f'‖₂)^{1/2}`.
* `opT_eq_fourier_multiplier` (`(FG.3b)`) and `Tc_sup_bound` (**Lemma FG.3 / `(FG.3)`**): for `0 < c`, `c_s ≠ 0`,
  `a ∈ L¹(ℝ)` with `‖a τ‖ ≤ M`, `R` real-measurable, and `f ∈ H¹(ℝ)`, the convolution operator
  `(T_c f)(L) = (c / (2π)) ∫ f(X) K_c(L - c_s X) dX` satisfies `(FG.3b)` and
  `‖(T_c f)(L)‖ ≤ (M / |c_s|) · (‖f‖₂ · ‖f'‖₂)^{1/2}`.
-/

@[expose] public section

namespace FormalResearch.CohnElkies

open MeasureTheory Real
open scoped FourierTransform

/-! ### Real inequalities -/

/-- If `c ≤ (t P + t⁻¹ Q)/2` for every `t > 0`, then `c² ≤ P Q`. -/
lemma sq_le_mul_of_forall_t (c P Q : ℝ) (hc : 0 ≤ c) (hP : 0 ≤ P) (hQ : 0 < Q)
    (h : ∀ t : ℝ, 0 < t → c ≤ (t * P + t⁻¹ * Q) / 2) : c ^ 2 ≤ P * Q := by
  by_contra H
  rw [not_le] at H
  have hc0 : 0 < c := by
    rcases eq_or_lt_of_le hc with h0 | h0
    · subst h0
      nlinarith [mul_nonneg hP hQ.le]
    · exact h0
  have hcne : c ≠ 0 := hc0.ne'
  have h1 := h (Q / c) (div_pos hQ hc0)
  have e : (Q / c)⁻¹ * Q = c := by
    field_simp
  rw [e] at h1
  have h2 : c ≤ Q / c * P := by linarith
  have e2 : Q / c * P * c = Q * P := by
    field_simp
  have h3 : c * c ≤ Q * P := by
    rw [← e2]
    exact mul_le_mul_of_nonneg_right h2 hc
  nlinarith [h3, H]

/-- The `κ`-optimised bound: if `c² ≤ π (N/κ + κ Y)` for all `κ > 0`, then `c² ≤ 2π √(N Y)`. -/
lemma sq_le_two_pi_mul_sqrt (c N Y : ℝ) (hN : 0 ≤ N) (hY : 0 ≤ Y)
    (h : ∀ κ : ℝ, 0 < κ → c ^ 2 ≤ π * (N / κ + κ * Y)) :
    c ^ 2 ≤ 2 * π * Real.sqrt (N * Y) := by
  by_contra H
  rw [not_le] at H
  have hpi : 0 < π := Real.pi_pos
  have hpi0 : π ≠ 0 := hpi.ne'
  have hsq0 : 0 ≤ 2 * π * Real.sqrt (N * Y) := by positivity
  have hc2 : 0 < c ^ 2 := lt_of_le_of_lt hsq0 H
  rcases eq_or_lt_of_le hY with hY0 | hYpos
  · subst hY0
    have hN1 : (0 : ℝ) < N + 1 := by linarith
    have hκ : 0 < π * (N + 1) / c ^ 2 := div_pos (mul_pos hpi hN1) hc2
    have h1 := h _ hκ
    simp only [mul_zero, add_zero] at h1
    have e : π * (N / (π * (N + 1) / c ^ 2)) = c ^ 2 * (N / (N + 1)) := by
      field_simp
    rw [e] at h1
    have hlt : N / (N + 1) < 1 := by
      rw [div_lt_one hN1]
      linarith
    have := mul_lt_mul_of_pos_left hlt hc2
    linarith
  · rcases eq_or_lt_of_le hN with hN0 | hNpos
    · subst hN0
      have hYne : Y ≠ 0 := hYpos.ne'
      have hκ : 0 < c ^ 2 / (2 * π * Y) := div_pos hc2 (mul_pos (mul_pos two_pos hpi) hYpos)
      have h1 := h _ hκ
      have e : π * (0 / (c ^ 2 / (2 * π * Y)) + c ^ 2 / (2 * π * Y) * Y) = c ^ 2 / 2 := by
        rw [zero_div, zero_add]
        field_simp
      rw [e] at h1
      linarith
    · obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.sqrt (N / Y) := ⟨_, rfl⟩
      have hκpos : 0 < κ := by
        rw [hκdef]
        exact Real.sqrt_pos.2 (div_pos hNpos hYpos)
      have hκ2 : κ ^ 2 = N / Y := by
        rw [hκdef, Real.sq_sqrt (div_nonneg hN hY)]
      have hYne : Y ≠ 0 := hYpos.ne'
      have hκne : κ ≠ 0 := hκpos.ne'
      have hNe : N = κ ^ 2 * Y := by
        rw [hκ2]
        field_simp
      have hdiv : N / κ = κ * Y := by
        rw [hNe]
        field_simp
      have hsq : Real.sqrt (N * Y) = κ * Y := by
        rw [hNe, show κ ^ 2 * Y * Y = (κ * Y) ^ 2 by ring]
        exact Real.sqrt_sq (mul_nonneg hκpos.le hY)
      have h1 := h κ hκpos
      rw [hdiv] at h1
      rw [hsq] at H
      nlinarith [h1, H]

/-- Pointwise AM–GM with a weight: `a ≤ (t (w a²) + t⁻¹ w⁻¹)/2` for `w, t > 0` and all real `a`. -/
lemma amgm_pointwise (a w t : ℝ) (hw : 0 < w) (ht : 0 < t) :
    a ≤ (t * (w * a ^ 2) + t⁻¹ * w⁻¹) / 2 := by
  have hs : 0 < t * w := mul_pos ht hw
  have hs' : t * w ≠ 0 := hs.ne'
  have h1 : (t * w) * ((t * w) * a ^ 2 + (t * w)⁻¹ - 2 * a) = ((t * w) * a - 1) ^ 2 := by
    field_simp
    ring
  have h2 : 0 ≤ (t * w) * ((t * w) * a ^ 2 + (t * w)⁻¹ - 2 * a) := by
    rw [h1]
    positivity
  have h3 : 0 ≤ (t * w) * a ^ 2 + (t * w)⁻¹ - 2 * a := (mul_nonneg_iff_of_pos_left hs).1 h2
  have e : (t * (w * a ^ 2) + t⁻¹ * w⁻¹) / 2 = ((t * w) * a ^ 2 + (t * w)⁻¹) / 2 := by
    rw [mul_inv]
    ring
  rw [e]
  linarith

/-! ### Fourier transforms of Schwartz functions -/

/-- The `L²` norm of a function on `ℝ`, `‖f‖₂ = (∫ |f|²)^{1/2}`. -/
noncomputable def l2norm (f : ℝ → ℂ) : ℝ := Real.sqrt (∫ x, ‖f x‖ ^ 2)

/-- The Fourier transform of FG.3: `f̂(ξ) = ∫ f(X) e^{-iXξ} dX`. -/
noncomputable def fourierPaper (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(Complex.I * ((x * ξ : ℝ) : ℂ))) * f x

/-- Mathlib's transform (with `2π` in the exponent) evaluated at `ξ / (2π)` is the paper's transform. -/
lemma fourierPaper_eq (g : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierPaper g ξ = (𝓕 g : SchwartzMap ℝ ℂ) ((2 * π)⁻¹ * ξ) := by
  have hπC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  show _ = 𝓕 (⇑g) ((2 * π)⁻¹ * ξ)
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold fourierPaper
  congr 1
  funext x
  rw [smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- The change of variables from Mathlib's transform to the paper's `f̂`: a factor `2π`. -/
lemma integral_fourierPaper (g : SchwartzMap ℝ ℂ) :
    ∫ ξ : ℝ, ‖fourierPaper g ξ‖ = 2 * π * ∫ η : ℝ, ‖(𝓕 g : SchwartzMap ℝ ℂ) η‖ := by
  have h1 : ∀ ξ : ℝ, ‖fourierPaper g ξ‖ = ‖(𝓕 g : SchwartzMap ℝ ℂ) ((2 * π)⁻¹ * ξ)‖ :=
    fun ξ => by rw [fourierPaper_eq]
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have h2 := Measure.integral_comp_mul_left (fun η : ℝ => ‖(𝓕 g : SchwartzMap ℝ ℂ) η‖) (2 * π)⁻¹
  rw [inv_inv, abs_of_pos hpos, smul_eq_mul] at h2
  simp only [h1]
  exact h2

/-- Plancherel integrability: `ξ ↦ |𝓕 f(ξ)|²` is integrable for a Schwartz function `f`. -/
lemma integrable_norm_sq_fourier (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ => ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
  have hm : MemLp ⇑(𝓕 f : SchwartzMap ℝ ℂ) ((2 : ℕ) : ENNReal) volume :=
    SchwartzMap.memLp (𝓕 f : SchwartzMap ℝ ℂ) _ volume
  exact hm.integrable_norm_pow (by norm_num)

/-- The derivative of a Schwartz function, as a function. -/
lemma deriv_coe_eq (f : SchwartzMap ℝ ℂ) : deriv (⇑f) = ⇑(SchwartzMap.derivCLM ℂ ℂ f) := by
  funext x
  rw [SchwartzMap.derivCLM_apply]

/-- Pointwise: `|𝓕 f'(ξ)|² = (2π)² ξ² |𝓕 f(ξ)|²` for the derivative `f' = derivCLM f`. -/
lemma norm_sq_fourier_deriv (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ‖(𝓕 (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) ξ‖ ^ 2
      = (2 * π) ^ 2 * (ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
  have hdiff : Differentiable ℝ (⇑f) := f.differentiable
  have hint' : Integrable (deriv (⇑f)) := by
    rw [deriv_coe_eq]
    exact (SchwartzMap.derivCLM ℂ ℂ f).integrable
  have key := Real.fourier_deriv f.integrable hdiff hint'
  have e : ((𝓕 (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (deriv (⇑f)) := by
    rw [deriv_coe_eq]
    rfl
  change ‖(𝓕 (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) ξ‖ ^ 2 = _
  rw [e, key]
  change ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ)) • (𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 = _
  have hn : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [smul_eq_mul, norm_mul, hn]
  linear_combination (2 * π) ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 * sq_abs ξ

/-- `(2π)² ∫ ξ² |𝓕 f|² = ∫ |f'|²` (Plancherel for `f'`). -/
lemma integral_fourier_deriv_sq (f : SchwartzMap ℝ ℂ) :
    (2 * π) ^ 2 * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 = ∫ x, ‖deriv (⇑f) x‖ ^ 2 := by
  have hP := SchwartzMap.integral_norm_sq_fourier (SchwartzMap.derivCLM ℂ ℂ f)
  rw [← deriv_coe_eq] at hP
  simp_rw [norm_sq_fourier_deriv] at hP
  rw [integral_const_mul] at hP
  exact hP

/-- Integrability of `ξ ↦ ξ² |𝓕 f(ξ)|²`, from the integrability of `|𝓕 f'|²`. -/
lemma integrable_sq_mul_norm_sq_fourier (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ => ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
  have h := (integrable_norm_sq_fourier (SchwartzMap.derivCLM ℂ ℂ f)).const_mul (((2 * π) ^ 2)⁻¹)
  refine h.congr (ae_of_all _ fun ξ => ?_)
  show ((2 * π) ^ 2)⁻¹ * ‖(𝓕 (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) ξ‖ ^ 2
    = ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2
  rw [norm_sq_fourier_deriv, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `ξ ↦ (1 + κ² ξ²)⁻¹` is integrable for `κ ≠ 0`. -/
lemma integrable_inv_one_add_sq_scaled (κ : ℝ) (hκ : κ ≠ 0) :
    Integrable (fun ξ : ℝ => (1 + κ ^ 2 * ξ ^ 2)⁻¹) := by
  have h := (integrable_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) hκ).2
    integrable_inv_one_add_sq
  refine h.congr (ae_of_all _ fun ξ => ?_)
  show (1 + (κ * ξ) ^ 2)⁻¹ = (1 + κ ^ 2 * ξ ^ 2)⁻¹
  rw [mul_pow]

/-- `∫ (1 + κ² ξ²)⁻¹ dξ = π / κ` for `κ > 0`. -/
lemma integral_inv_one_add_sq_scaled (κ : ℝ) (hκ : 0 < κ) :
    ∫ ξ : ℝ, (1 + κ ^ 2 * ξ ^ 2)⁻¹ = π / κ := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) κ
  simp only [mul_pow] at h
  rw [integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.2 hκ), smul_eq_mul] at h
  rw [h, div_eq_inv_mul]

/-- The core estimate: `(∫|𝓕 f|)² ≤ 2π √(‖f‖₂² · ∫ ξ²|𝓕 f|²)`. -/
lemma l1_sq_le (f : SchwartzMap ℝ ℂ) :
    (∫ ξ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖) ^ 2 ≤
      2 * π * Real.sqrt ((∫ x, ‖f x‖ ^ 2) * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
  have hI1 : Integrable (fun ξ => ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖) := (𝓕 f).integrable.norm
  have hI2 : Integrable (fun ξ => ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) :=
    integrable_norm_sq_fourier f
  have hI3 : Integrable (fun ξ => ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) :=
    integrable_sq_mul_norm_sq_fourier f
  have hN : ∫ ξ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 :=
    SchwartzMap.integral_norm_sq_fourier f
  have hNnn : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hYnn : 0 ≤ ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  have hcnn : 0 ≤ ∫ ξ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ := integral_nonneg fun ξ => norm_nonneg _
  have hbound : ∀ κ : ℝ, 0 < κ →
      (∫ ξ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖) ^ 2
        ≤ π * ((∫ x, ‖f x‖ ^ 2) / κ + κ * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
    intro κ hκ
    have hκne : κ ≠ 0 := hκ.ne'
    have hPint : Integrable (fun ξ => (1 + κ ^ 2 * ξ ^ 2) * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
      refine (hI2.add (hI3.const_mul (κ ^ 2))).congr (ae_of_all _ fun ξ => ?_)
      show ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 + κ ^ 2 * (ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
        = (1 + κ ^ 2 * ξ ^ 2) * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2
      ring
    have hQint : Integrable (fun ξ : ℝ => (1 + κ ^ 2 * ξ ^ 2)⁻¹) :=
      integrable_inv_one_add_sq_scaled κ hκne
    have hP : ∫ ξ, (1 + κ ^ 2 * ξ ^ 2) * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2
        = (∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 := by
      have e : (fun ξ => (1 + κ ^ 2 * ξ ^ 2) * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
          = fun ξ => ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 + κ ^ 2 * (ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
        funext ξ
        ring
      rw [e, integral_add hI2 (hI3.const_mul _), integral_const_mul, hN]
    have hQ : ∫ ξ : ℝ, (1 + κ ^ 2 * ξ ^ 2)⁻¹ = π / κ := integral_inv_one_add_sq_scaled κ hκ
    have hPnn : 0 ≤ (∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2 :=
      add_nonneg hNnn (mul_nonneg (sq_nonneg κ) hYnn)
    have hQpos : 0 < π / κ := div_pos Real.pi_pos hκ
    have hT : ∀ t : ℝ, 0 < t →
        (∫ ξ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖) ≤
          (t * ((∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
            + t⁻¹ * (π / κ)) / 2 := by
      intro t ht
      have hpt : ∀ ξ : ℝ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ≤
          (t * ((1 + κ ^ 2 * ξ ^ 2) * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
            + t⁻¹ * (1 + κ ^ 2 * ξ ^ 2)⁻¹) / 2 := by
        intro ξ
        have hw : 0 < 1 + κ ^ 2 * ξ ^ 2 := by positivity
        exact amgm_pointwise _ _ t hw ht
      have hRint : Integrable (fun ξ : ℝ =>
          (t * ((1 + κ ^ 2 * ξ ^ 2) * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
            + t⁻¹ * (1 + κ ^ 2 * ξ ^ 2)⁻¹) / 2) :=
        ((hPint.const_mul t).add (hQint.const_mul t⁻¹)).div_const 2
      calc (∫ ξ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖)
          ≤ ∫ ξ : ℝ, (t * ((1 + κ ^ 2 * ξ ^ 2) * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
              + t⁻¹ * (1 + κ ^ 2 * ξ ^ 2)⁻¹) / 2 :=
            integral_mono hI1 hRint hpt
        _ = (t * ((∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
              + t⁻¹ * (π / κ)) / 2 := by
            rw [integral_div, integral_add (hPint.const_mul t) (hQint.const_mul t⁻¹),
              integral_const_mul, integral_const_mul, hP, hQ]
    have hmain := sq_le_mul_of_forall_t (∫ ξ, ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖) _ (π / κ) hcnn hPnn
      hQpos hT
    have e : ((∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) * (π / κ)
        = π * ((∫ x, ‖f x‖ ^ 2) / κ + κ * ∫ ξ, ξ ^ 2 * ‖(𝓕 f : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
      field_simp
    rw [e] at hmain
    exact hmain
  exact sq_le_two_pi_mul_sqrt _ _ _ hNnn hYnn hbound

/-- **FG.3 (Fourier `L¹` interpolation), Schwartz form.** For a Schwartz function `g` on `ℝ`,
`∫ |ĝ(ξ)| dξ ≤ 2π (‖g‖₂ ‖g'‖₂)^{1/2}`, with `ĝ(ξ) = ∫ g(X) e^{-iXξ} dX` (the FG.3 normalisation). -/
theorem fourier_L1_le_sqrt_mul (g : SchwartzMap ℝ ℂ) :
    ∫ ξ : ℝ, ‖fourierPaper g ξ‖ ≤ 2 * π * Real.sqrt (l2norm (⇑g) * l2norm (deriv (⇑g))) := by
  rw [integral_fourierPaper g]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hc := l1_sq_le g
  have hD := integral_fourier_deriv_sq g
  have hNnn : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hsqrt : Real.sqrt (∫ x, ‖g x‖ ^ 2) * Real.sqrt (∫ x, ‖deriv (⇑g) x‖ ^ 2)
      = 2 * π * Real.sqrt ((∫ x, ‖g x‖ ^ 2) * ∫ ξ, ξ ^ 2 * ‖(𝓕 g : SchwartzMap ℝ ℂ) ξ‖ ^ 2) := by
    rw [← hD, ← Real.sqrt_mul hNnn]
    rw [show (∫ x, ‖g x‖ ^ 2) * ((2 * π) ^ 2 * ∫ ξ, ξ ^ 2 * ‖(𝓕 g : SchwartzMap ℝ ℂ) ξ‖ ^ 2)
        = (2 * π) ^ 2 * ((∫ x, ‖g x‖ ^ 2) * ∫ ξ, ξ ^ 2 * ‖(𝓕 g : SchwartzMap ℝ ℂ) ξ‖ ^ 2) by ring]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * π) ^ 2),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [← hsqrt] at hc
  unfold l2norm
  exact (le_abs_self _).trans (Real.abs_le_sqrt hc)

/-- info: 'FormalResearch.CohnElkies.fourier_L1_le_sqrt_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_L1_le_sqrt_mul

section H1Extension

open scoped ComplexInnerProductSpace ComplexConjugate

/-- `f'` is the `L²` weak derivative of `f` on `ℝ`: both `f, f' ∈ L²(ℝ)`, and for every Schwartz test function
`φ : 𝓢(ℝ, ℂ)`, `∫ x, deriv (⇑φ) x * f x = -∫ x, φ x * f' x`. -/
structure WeakDerivL2 (f f' : ℝ → ℂ) : Prop where
  memLp : MemLp f 2 volume
  memLp_deriv : MemLp f' 2 volume
  ibp : ∀ φ : SchwartzMap ℝ ℂ, ∫ x : ℝ, deriv (⇑φ) x * f x = -∫ x : ℝ, φ x * f' x

lemma WeakDerivL2.of_schwartz (g : SchwartzMap ℝ ℂ) : WeakDerivL2 (⇑g) (deriv ⇑g) where
  memLp := g.memLp 2 volume
  memLp_deriv := by
    rw [deriv_coe_eq]
    exact (SchwartzMap.derivCLM ℂ ℂ g).memLp 2 volume
  ibp φ := by
    have hu : ∀ x ∈ tsupport (⇑g), HasDerivAt (⇑φ) (deriv (⇑φ) x) x := fun x _ =>
      φ.differentiable.differentiableAt.hasDerivAt
    have hv : ∀ x ∈ tsupport (⇑φ), HasDerivAt (⇑g) (deriv (⇑g) x) x := fun x _ =>
      g.differentiable.differentiableAt.hasDerivAt
    have huv' : Integrable (fun x => φ x * deriv (⇑g) x) := by
      rw [deriv_coe_eq]
      exact (φ.memLp 2 volume).integrable_mul ((SchwartzMap.derivCLM ℂ ℂ g).memLp 2 volume)
    have hu'v : Integrable (fun x => deriv (⇑φ) x * g x) := by
      have h : Integrable (fun x => (SchwartzMap.derivCLM ℂ ℂ φ) x * g x) :=
        ((SchwartzMap.derivCLM ℂ ℂ φ).memLp 2 volume).integrable_mul (g.memLp 2 volume)
      refine h.congr (ae_of_all _ fun x => ?_)
      rw [← deriv_coe_eq]
    have huv : Integrable (fun x => φ x * g x) :=
      (φ.memLp 2 volume).integrable_mul (g.memLp 2 volume)
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv
    calc ∫ x : ℝ, deriv (⇑φ) x * g x
        = - -∫ x : ℝ, deriv (⇑φ) x * g x := (neg_neg _).symm
      _ = -∫ x : ℝ, φ x * deriv (⇑g) x := by rw [hibp]

/-- `l2norm f` equals the `Lp ℂ 2` norm of `hf.toLp f`. -/
lemma l2norm_eq_norm_toLp {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    l2norm f = ‖hf.toLp f‖ := by
  unfold l2norm
  set U : Lp ℂ 2 volume := hf.toLp f
  have h1 : (∫ x, ‖f x‖ ^ 2) = ∫ x, ‖(U : ℝ → ℂ) x‖ ^ 2 :=
    integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp [U, hx])
  have h2 : ∫ x, ‖(U : ℝ → ℂ) x‖ ^ 2 = ‖U‖ ^ 2 := by
    have hnorm : ‖U‖ ^ 2 = ((‖U‖ ^ 2 : ℝ) : ℂ).re := (Complex.ofReal_re _).symm
    have hin : ⟪U, U⟫ = ∫ x : ℝ, ((‖(U : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      rw [RCLike.inner_apply, Complex.mul_conj', Complex.ofReal_pow]
    have hnorm2 : ‖U‖ ^ 2 = (⟪U, U⟫).re := by
      have h : ⟪U, U⟫ = ((‖U‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [Complex.coe_algebraMap, Complex.ofReal_pow] using
          inner_self_eq_norm_sq_to_K (𝕜 := ℂ) U
      rw [h, Complex.ofReal_re]
    rw [hnorm2, hin, integral_complex_ofReal, Complex.ofReal_re]
  rw [h1, h2, Real.sqrt_sq (norm_nonneg _)]

private noncomputable def conjSchwartz (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  φ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp]
private lemma conjSchwartz_apply (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    conjSchwartz φ x = starRingEnd ℂ (φ x) := rfl

private lemma deriv_conjSchwartz (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (⇑(conjSchwartz φ)) x = starRingEnd ℂ (deriv (⇑φ) x) := by
  have hd : HasDerivAt (⇑(conjSchwartz φ)) (starRingEnd ℂ (deriv (⇑φ) x)) x :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt x
      φ.differentiable.differentiableAt.hasDerivAt)
  exact hd.deriv

private lemma memLp_two_bdd_mul {b u : ℝ → ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (hb_meas : AEStronglyMeasurable b volume) (hb : ∀ x, ‖b x‖ ≤ C)
    (hu : MemLp u 2 volume) : MemLp (fun x => b x * u x) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (hb_meas.mul hu.aestronglyMeasurable)).mpr ?_
  refine ((hu.integrable_norm_pow (by norm_num)).const_mul (C ^ 2)).mono'
    ((hb_meas.mul hu.aestronglyMeasurable).norm.pow 2) (ae_of_all _ fun x => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (sq_nonneg _), Pi.mul_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (sq_nonneg _)

private lemma continuous_inv_one_add_sq_complex :
    Continuous (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ)) :=
  (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun ξ : ℝ => (1 + ξ ^ 2 : ℝ))).inv₀
    (fun ξ => Complex.ofReal_ne_zero.mpr (by positivity))

private lemma memLp_inv_one_add_sq_mul {u : ℝ → ℂ} (hu : MemLp u 2 volume) :
    MemLp (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) * u ξ) 2 volume := by
  refine memLp_two_bdd_mul zero_le_one continuous_inv_one_add_sq_complex.aestronglyMeasurable
    (fun ξ => ?_) hu
  have hden : 0 < 1 + ξ ^ 2 := by positivity
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg ξ])

private lemma memLp_xi_div_one_add_sq_mul {u : ℝ → ℂ} (hu : MemLp u 2 volume) :
    MemLp (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) * (2 * π * Complex.I * (ξ : ℂ) * u ξ)) 2 volume := by
  have hrewrite : (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) * (2 * π * Complex.I * (ξ : ℂ) * u ξ)) =
      fun ξ : ℝ => (((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) * (2 * π * Complex.I * (ξ : ℂ))) * u ξ := by
    funext ξ; ring
  rw [hrewrite]
  have hc : Continuous (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) * (2 * π * Complex.I * (ξ : ℂ))) :=
    continuous_inv_one_add_sq_complex.mul (by fun_prop)
  refine memLp_two_bdd_mul Real.pi_pos.le hc.aestronglyMeasurable (fun ξ => ?_) hu
  have hden : 0 < 1 + ξ ^ 2 := by positivity
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden,
    norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, inv_mul_le_iff₀ hden]
  nlinarith [Real.pi_pos, sq_abs ξ, sq_nonneg (1 - |ξ|)]

private lemma inv_one_add_sq_hasTemperateGrowth :
    (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ)).HasTemperateGrowth := by
  have hr : (fun ξ : ℝ => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1)
  have heq : (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ)) =
      fun ξ : ℝ => Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) := by
    funext ξ
    simp [Real.rpow_neg_one]
  rw [heq]
  exact Complex.hasTemperateGrowth_ofReal.comp hr

private lemma eq_zero_ae_of_forall_schwartz_inner {u : ℝ → ℂ} (hu : MemLp u 2 volume)
    (h0 : ∀ η : SchwartzMap ℝ ℂ, ∫ x : ℝ, starRingEnd ℂ (η x) * u x = 0) :
    u =ᵐ[volume] 0 := by
  set U : Lp ℂ 2 volume := hu.toLp u
  have hinner : ∀ η : SchwartzMap ℝ ℂ, ⟪η.toLp 2 volume, U⟫ = 0 := by
    intro η
    rw [MeasureTheory.L2.inner_def]
    refine (integral_congr_ae ?_).trans (h0 η)
    filter_upwards [η.coeFn_toLp 2 volume, hu.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply]
    ring
  have hinner_all : ∀ v : Lp ℂ 2 volume, ⟪v, U⟫ = 0 := by
    intro v
    have hcont : Continuous (fun w : Lp ℂ 2 volume => ⟪w, U⟫) :=
      continuous_id.inner continuous_const
    have hd : DenseRange (fun η : SchwartzMap ℝ ℂ => η.toLp 2 volume) :=
      SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top
    exact congrFun (hd.equalizer hcont continuous_const (funext hinner)) v
  have hU0 : U = 0 := inner_self_eq_zero.mp (hinner_all U)
  have hzero : U =ᵐ[volume] (0 : ℝ → ℂ) := by
    rw [hU0]; exact Lp.coeFn_zero _ _ _
  exact hu.coeFn_toLp.symm.trans hzero

/-- Weak-derivative multiplier identity in `L²(ℝ)`: for `h : WeakDerivL2 f f'`,
`𝓕(f') = (2π i ξ) 𝓕(f)` a.e. -/
theorem fourierL2Deriv_ae {f f' : ℝ → ℂ} (h : WeakDerivL2 f f') :
    ∀ᵐ ξ ∂volume,
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp_deriv.toLp f') : Lp ℂ 2 volume) : ℝ → ℂ) ξ =
        2 * π * Complex.I * (ξ : ℂ) *
          ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) ξ := by
  set F : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f)
  set G : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp_deriv.toLp f')
  have hF : MemLp (F : ℝ → ℂ) 2 volume := Lp.memLp F
  have hG : MemLp (G : ℝ → ℂ) 2 volume := Lp.memLp G
  have htest : ∀ ψ : SchwartzMap ℝ ℂ,
      ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (G : ℝ → ℂ) ξ =
        ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ) := by
    intro ψ
    set φ₀ : SchwartzMap ℝ ℂ := 𝓕⁻ ψ
    set φ : SchwartzMap ℝ ℂ := conjSchwartz φ₀
    have hLHS : ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (G : ℝ → ℂ) ξ = ∫ x : ℝ, φ x * f' x := by
      have h1 : ⟪ψ.toLp 2 volume, G⟫ = ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (G : ℝ → ℂ) ξ := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [ψ.coeFn_toLp 2 volume] with ξ hξ
        rw [hξ, RCLike.inner_apply]
        ring
      have h2 : ⟪ψ.toLp 2 volume, G⟫ = ⟪φ₀.toLp 2 volume, h.memLp_deriv.toLp f'⟫ := by
        have hstep := MeasureTheory.Lp.inner_fourier_eq (𝓕⁻ (ψ.toLp 2 volume)) (h.memLp_deriv.toLp f')
        have hl : 𝓕 (𝓕⁻ (ψ.toLp 2 volume)) = ψ.toLp 2 volume :=
          FourierInvPair.fourier_fourierInv_eq _
        have hr : 𝓕 (h.memLp_deriv.toLp f') = G := rfl
        rw [hl, hr] at hstep
        rw [hstep, SchwartzMap.toLp_fourierInv_eq]
      have h3 : ⟪φ₀.toLp 2 volume, h.memLp_deriv.toLp f'⟫ = ∫ x : ℝ, φ x * f' x := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [φ₀.coeFn_toLp 2 volume, h.memLp_deriv.coeFn_toLp] with x hx1 hx2
        rw [hx1, hx2, RCLike.inner_apply, conjSchwartz_apply]
        ring
      rw [← h1, h2, h3]
    have hRHS_ibp : ∫ x : ℝ, φ x * f' x = -∫ x : ℝ, deriv (⇑φ) x * f x := by
      rw [h.ibp φ, neg_neg]
    have hRHS_der : -∫ x : ℝ, deriv (⇑φ) x * f x =
        ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ) := by
      set dφ₀ : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ φ₀
      have h1 : ∫ x : ℝ, deriv (⇑φ) x * f x = ⟪dφ₀.toLp 2 volume, h.memLp.toLp f⟫ := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [dφ₀.coeFn_toLp 2 volume, h.memLp.coeFn_toLp] with x hx1 hx2
        have hd : deriv (⇑φ) x = starRingEnd ℂ (dφ₀ x) := by
          simpa [φ, dφ₀, SchwartzMap.derivCLM_apply] using deriv_conjSchwartz φ₀ x
        rw [hd, hx1, hx2, RCLike.inner_apply]
        ring
      have h2 : ⟪dφ₀.toLp 2 volume, h.memLp.toLp f⟫ = ⟪(𝓕 dφ₀).toLp 2 volume, F⟫ := by
        have hstep := (MeasureTheory.Lp.inner_fourier_eq (dφ₀.toLp 2 volume) (h.memLp.toLp f)).symm
        rw [SchwartzMap.toLp_fourier_eq] at hstep
        exact hstep
      have hfd : ∀ ξ : ℝ, (𝓕 dφ₀ : SchwartzMap ℝ ℂ) ξ = (2 * π * Complex.I * (ξ : ℂ)) * ψ ξ := by
        intro ξ
        have hdiff : Differentiable ℝ (⇑φ₀) := φ₀.differentiable
        have hint' : Integrable (deriv ⇑φ₀) := by
          rw [deriv_coe_eq]; exact dφ₀.integrable
        have key := Real.fourier_deriv φ₀.integrable hdiff hint'
        have e : ((𝓕 dφ₀ : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (deriv ⇑φ₀) := by
          change 𝓕 (⇑dφ₀) = _
          rw [← deriv_coe_eq]
        change (𝓕 dφ₀ : SchwartzMap ℝ ℂ) ξ = _
        rw [e, key]
        have hinv : (𝓕 (⇑φ₀)) ξ = ψ ξ := by
          change (𝓕 (𝓕⁻ ψ) : SchwartzMap ℝ ℂ) ξ = ψ ξ
          rw [FourierInvPair.fourier_fourierInv_eq]
        change (2 * π * Complex.I * (ξ : ℂ)) • (𝓕 (⇑φ₀)) ξ = _
        rw [hinv, smul_eq_mul]
      have h3 : -⟪(𝓕 dφ₀).toLp 2 volume, F⟫ =
          ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ) := by
        rw [MeasureTheory.L2.inner_def, ← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards [(𝓕 dφ₀).coeFn_toLp 2 volume] with ξ hξ
        rw [hξ, hfd, RCLike.inner_apply, map_mul, map_mul, map_mul, map_mul,
          Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal, map_ofNat]
        ring
      rw [h1, h2, h3]
    rw [hLHS, hRHS_ibp, hRHS_der]
  set u : ℝ → ℂ := fun ξ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) * ((G : ℝ → ℂ) ξ - 2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ)
  have hu : MemLp u 2 volume := by
    have h1 := memLp_inv_one_add_sq_mul hG
    have h2 := memLp_xi_div_one_add_sq_mul hF
    refine (h1.sub h2).ae_eq (ae_of_all _ fun ξ => ?_)
    dsimp [u]; ring
  have h0 : ∀ η : SchwartzMap ℝ ℂ, ∫ ξ : ℝ, starRingEnd ℂ (η ξ) * u ξ = 0 := by
    intro η
    set ψ : SchwartzMap ℝ ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ)) η
    have hψ : ∀ ξ : ℝ, starRingEnd ℂ (η ξ) * u ξ =
        starRingEnd ℂ (ψ ξ) * (G : ℝ → ℂ) ξ -
          starRingEnd ℂ (ψ ξ) * (2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ) := by
      intro ξ
      have hval : ψ ξ = ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) * η ξ := by
        simpa [ψ, smul_eq_mul] using
          SchwartzMap.smulLeftCLM_apply_apply inv_one_add_sq_hasTemperateGrowth η ξ
      rw [hval, map_mul, map_inv₀, Complex.conj_ofReal]
      dsimp [u]
      ring
    have hi1 : Integrable (fun ξ => starRingEnd ℂ (ψ ξ) * (G : ℝ → ℂ) ξ) :=
      ((conjSchwartz ψ).memLp 2 volume).integrable_mul hG
    have hi2 : Integrable (fun ξ => starRingEnd ℂ (ψ ξ) * (2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ)) := by
      set ψ1 : SchwartzMap ℝ ℂ :=
        SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => 2 * π * Complex.I * (ξ : ℂ)) (conjSchwartz ψ)
      have htg : (fun ξ : ℝ => 2 * π * Complex.I * (ξ : ℂ)).HasTemperateGrowth := by fun_prop
      have heq : (fun ξ => starRingEnd ℂ (ψ ξ) * (2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ)) =
          fun ξ => ψ1 ξ * (F : ℝ → ℂ) ξ := by
        funext ξ
        have hval : ψ1 ξ = (2 * π * Complex.I * (ξ : ℂ)) * conjSchwartz ψ ξ := by
          simpa [ψ1, smul_eq_mul] using SchwartzMap.smulLeftCLM_apply_apply htg (conjSchwartz ψ) ξ
        rw [hval, conjSchwartz_apply]
        ring
      rw [heq]
      exact (ψ1.memLp 2 volume).integrable_mul hF
    rw [integral_congr_ae (ae_of_all _ hψ), integral_sub hi1 hi2, htest ψ, sub_self]
  filter_upwards [eq_zero_ae_of_forall_schwartz_inner hu h0] with ξ hξ
  have hden : ((1 + ξ ^ 2 : ℝ)⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (by positivity : (1 + ξ ^ 2 : ℝ) ≠ 0)
  have hsub : (G : ℝ → ℂ) ξ - 2 * π * Complex.I * (ξ : ℂ) * (F : ℝ → ℂ) ξ = 0 :=
    (mul_eq_zero.mp hξ).resolve_left hden
  exact sub_eq_zero.mp hsub

/-- The paper-normalised `L²`-Fourier transform `f̂(ξ) = (𝓕_{L²} f)((2π)⁻¹ ξ)` for `f ∈ H¹(ℝ)`. -/
noncomputable def fourierPaperL2 {f f' : ℝ → ℂ} (h : WeakDerivL2 f f') (ξ : ℝ) : ℂ :=
  ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) ((2 * π)⁻¹ * ξ)

/-- For `h : WeakDerivL2 f f'`, Mathlib's `L²`-Fourier transform `F = 𝓕 f` is in `L¹(ℝ)`, and
`ξ ↦ ξ² ‖F ξ‖²` is integrable with `(2π)² ∫ ξ² ‖F ξ‖² = ‖f'‖₂²`. -/
lemma integrable_fourier_H1 {f f' : ℝ → ℂ} (h : WeakDerivL2 f f') :
    Integrable ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) ∧
      (2 * π) ^ 2 * ∫ ξ : ℝ, ξ ^ 2 *
          ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 =
        ∫ x : ℝ, ‖f' x‖ ^ 2 ∧
      ∫ ξ : ℝ,
          ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 =
        ∫ x : ℝ, ‖f x‖ ^ 2 := by
  set F : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f)
  set G : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp_deriv.toLp f')
  have hF2 : Integrable (fun ξ : ℝ => ‖(F : ℝ → ℂ) ξ‖ ^ 2) := (Lp.memLp F).integrable_norm_pow two_ne_zero
  have hG2 : Integrable (fun ξ : ℝ => ‖(G : ℝ → ℂ) ξ‖ ^ 2) := (Lp.memLp G).integrable_norm_pow two_ne_zero
  have hae : ∀ᵐ ξ ∂volume, ‖(G : ℝ → ℂ) ξ‖ ^ 2 = (2 * π) ^ 2 * (ξ ^ 2 * ‖(F : ℝ → ℂ) ξ‖ ^ 2) := by
    filter_upwards [fourierL2Deriv_ae h] with ξ hξ
    rw [hξ, norm_mul]
    have hn : ‖2 * (π : ℂ) * Complex.I * (ξ : ℂ)‖ = 2 * π * |ξ| := by
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    rw [hn]
    linear_combination (2 * π) ^ 2 * ‖(F : ℝ → ℂ) ξ‖ ^ 2 * sq_abs ξ
  have hX2 : Integrable (fun ξ : ℝ => ξ ^ 2 * ‖(F : ℝ → ℂ) ξ‖ ^ 2) := by
    refine (hG2.const_mul (((2 * π) ^ 2)⁻¹)).congr ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hL1 : Integrable (F : ℝ → ℂ) := by
    have hdom : Integrable (fun ξ : ℝ => ((1 + ξ ^ 2) * ‖(F : ℝ → ℂ) ξ‖ ^ 2 + (1 + ξ ^ 2)⁻¹) / 2) := by
      have hA : Integrable (fun ξ : ℝ => (1 + ξ ^ 2) * ‖(F : ℝ → ℂ) ξ‖ ^ 2) :=
        (hF2.add hX2).congr (ae_of_all _ fun ξ => by dsimp; ring)
      exact (hA.add integrable_inv_one_add_sq).div_const 2
    refine hdom.mono (Lp.aestronglyMeasurable F) (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_of_nonneg (div_nonneg (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity)) two_pos.le)]
    simpa using amgm_pointwise ‖(F : ℝ → ℂ) ξ‖ (1 + ξ ^ 2) 1 (by positivity) one_pos
  have hPF : ∫ ξ : ℝ, ‖(F : ℝ → ℂ) ξ‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    have hn : ‖F‖ = ‖h.memLp.toLp f‖ := MeasureTheory.Lp.norm_fourier_eq _
    have h1 := l2norm_eq_norm_toLp (Lp.memLp F)
    have h2 := l2norm_eq_norm_toLp h.memLp
    have heq : l2norm (F : ℝ → ℂ) = l2norm f := by
      have hm := Lp.memLp F
      rw [h1, show hm.toLp (F : ℝ → ℂ) = F from by ext1; exact hm.coeFn_toLp, hn, ← h2]
    have hsq := congr_arg (fun r : ℝ => r ^ 2) heq
    dsimp [l2norm] at hsq
    rwa [Real.sq_sqrt (integral_nonneg fun _ => by positivity),
      Real.sq_sqrt (integral_nonneg fun _ => by positivity)] at hsq
  have hPG : ∫ ξ : ℝ, ‖(G : ℝ → ℂ) ξ‖ ^ 2 = ∫ x : ℝ, ‖f' x‖ ^ 2 := by
    have hn : ‖G‖ = ‖h.memLp_deriv.toLp f'‖ := MeasureTheory.Lp.norm_fourier_eq _
    have h1 := l2norm_eq_norm_toLp (Lp.memLp G)
    have h2 := l2norm_eq_norm_toLp h.memLp_deriv
    have heq : l2norm (G : ℝ → ℂ) = l2norm f' := by
      have hm := Lp.memLp G
      rw [h1, show hm.toLp (G : ℝ → ℂ) = G from by ext1; exact hm.coeFn_toLp, hn, ← h2]
    have hsq := congr_arg (fun r : ℝ => r ^ 2) heq
    dsimp [l2norm] at hsq
    rwa [Real.sq_sqrt (integral_nonneg fun _ => by positivity),
      Real.sq_sqrt (integral_nonneg fun _ => by positivity)] at hsq
  refine ⟨hL1, ?_, hPF⟩
  rw [← hPG, ← integral_const_mul]
  exact (integral_congr_ae hae).symm

/-- **Lemma T.5 / `(FG.3c)` (`H¹(ℝ)` extension):** for any `f ∈ H¹(ℝ)` (`WeakDerivL2 f f'`),
the `L²`-Fourier transform `fourierPaperL2 h` is integrable and
`∫ ξ, ‖fourierPaperL2 h ξ‖ ≤ 2π (‖f‖₂ ‖f'‖₂)^{1/2}`. -/
theorem fourier_L1_le_sqrt_mul_H1 {f f' : ℝ → ℂ} (h : WeakDerivL2 f f') :
    Integrable (fourierPaperL2 h) ∧
      ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖ ≤ 2 * π * Real.sqrt (l2norm f * l2norm f') := by
  obtain ⟨hL1, hD, hPF⟩ := integrable_fourier_H1 h
  set F : ℝ → ℂ := ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ)
  have hpL1 : Integrable (fourierPaperL2 h) := by
    have hcomp := (integrable_comp_mul_left_iff F (inv_ne_zero (by positivity : (2 * π) ≠ 0))).2 hL1
    refine hcomp.congr (ae_of_all _ fun ξ => ?_)
    dsimp [fourierPaperL2]
  refine ⟨hpL1, ?_⟩
  have hcov : ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖ = 2 * π * ∫ η : ℝ, ‖F η‖ := by
    have hpos : (0 : ℝ) < 2 * π := by positivity
    have h2 := Measure.integral_comp_mul_left (fun η : ℝ => ‖F η‖) (2 * π)⁻¹
    rw [inv_inv, abs_of_pos hpos, smul_eq_mul] at h2
    exact h2
  rw [hcov]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hF2 : Integrable (fun ξ : ℝ => ‖F ξ‖ ^ 2) := (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hae : ∀ᵐ ξ ∂volume, ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp_deriv.toLp f') : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 =
      (2 * π) ^ 2 * (ξ ^ 2 * ‖F ξ‖ ^ 2) := by
    filter_upwards [fourierL2Deriv_ae h] with ξ hξ
    rw [hξ, norm_mul]
    have hn : ‖2 * (π : ℂ) * Complex.I * (ξ : ℂ)‖ = 2 * π * |ξ| := by
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    rw [hn]
    linear_combination (2 * π) ^ 2 * ‖F ξ‖ ^ 2 * sq_abs ξ
  have hX2 : Integrable (fun ξ : ℝ => ξ ^ 2 * ‖F ξ‖ ^ 2) := by
    refine (((Lp.memLp (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp_deriv.toLp f'))).integrable_norm_pow
      (by norm_num)).const_mul (((2 * π) ^ 2)⁻¹)).congr ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hNnn : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hYnn : 0 ≤ ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hcnn : 0 ≤ ∫ ξ, ‖F ξ‖ := integral_nonneg fun _ => norm_nonneg _
  have hbound : ∀ κ : ℝ, 0 < κ →
      (∫ ξ, ‖F ξ‖) ^ 2 ≤ π * ((∫ x, ‖f x‖ ^ 2) / κ + κ * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) := by
    intro κ hκ
    have hκne : κ ≠ 0 := hκ.ne'
    have hPint : Integrable (fun ξ => (1 + κ ^ 2 * ξ ^ 2) * ‖F ξ‖ ^ 2) :=
      (hF2.add (hX2.const_mul (κ ^ 2))).congr (ae_of_all _ fun ξ => by dsimp; ring)
    have hQint : Integrable (fun ξ : ℝ => (1 + κ ^ 2 * ξ ^ 2)⁻¹) :=
      integrable_inv_one_add_sq_scaled κ hκne
    have hP : ∫ ξ, (1 + κ ^ 2 * ξ ^ 2) * ‖F ξ‖ ^ 2 =
        (∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2 := by
      have e : (fun ξ => (1 + κ ^ 2 * ξ ^ 2) * ‖F ξ‖ ^ 2) =
          fun ξ => ‖F ξ‖ ^ 2 + κ ^ 2 * (ξ ^ 2 * ‖F ξ‖ ^ 2) := by funext ξ; ring
      rw [e, integral_add hF2 (hX2.const_mul _), integral_const_mul, hPF]
    have hQ : ∫ ξ : ℝ, (1 + κ ^ 2 * ξ ^ 2)⁻¹ = π / κ := integral_inv_one_add_sq_scaled κ hκ
    have hPnn : 0 ≤ (∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2 :=
      add_nonneg hNnn (mul_nonneg (sq_nonneg κ) hYnn)
    have hT : ∀ t : ℝ, 0 < t →
        (∫ ξ, ‖F ξ‖) ≤
          (t * ((∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) + t⁻¹ * (π / κ)) / 2 := by
      intro t ht
      have hpt : ∀ ξ : ℝ, ‖F ξ‖ ≤
          (t * ((1 + κ ^ 2 * ξ ^ 2) * ‖F ξ‖ ^ 2) + t⁻¹ * (1 + κ ^ 2 * ξ ^ 2)⁻¹) / 2 :=
        fun ξ => amgm_pointwise _ _ t (by positivity) ht
      have hRint : Integrable (fun ξ : ℝ =>
          (t * ((1 + κ ^ 2 * ξ ^ 2) * ‖F ξ‖ ^ 2) + t⁻¹ * (1 + κ ^ 2 * ξ ^ 2)⁻¹) / 2) :=
        ((hPint.const_mul t).add (hQint.const_mul t⁻¹)).div_const 2
      calc (∫ ξ, ‖F ξ‖)
          ≤ ∫ ξ : ℝ, (t * ((1 + κ ^ 2 * ξ ^ 2) * ‖F ξ‖ ^ 2) + t⁻¹ * (1 + κ ^ 2 * ξ ^ 2)⁻¹) / 2 :=
            integral_mono hL1.norm hRint hpt
        _ = (t * ((∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) + t⁻¹ * (π / κ)) / 2 := by
            rw [integral_div, integral_add (hPint.const_mul t) (hQint.const_mul t⁻¹),
              integral_const_mul, integral_const_mul, hP, hQ]
    have hmain := sq_le_mul_of_forall_t (∫ ξ, ‖F ξ‖) _ (π / κ) hcnn hPnn (div_pos Real.pi_pos hκ) hT
    have e : ((∫ x, ‖f x‖ ^ 2) + κ ^ 2 * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) * (π / κ) =
        π * ((∫ x, ‖f x‖ ^ 2) / κ + κ * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) := by field_simp
    rwa [e] at hmain
  have hc := sq_le_two_pi_mul_sqrt _ _ _ hNnn hYnn hbound
  have hsqrt : Real.sqrt (∫ x, ‖f x‖ ^ 2) * Real.sqrt (∫ x, ‖f' x‖ ^ 2) =
      2 * π * Real.sqrt ((∫ x, ‖f x‖ ^ 2) * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) := by
    rw [← hD, ← Real.sqrt_mul hNnn]
    rw [show (∫ x, ‖f x‖ ^ 2) * ((2 * π) ^ 2 * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) =
        (2 * π) ^ 2 * ((∫ x, ‖f x‖ ^ 2) * ∫ ξ, ξ ^ 2 * ‖F ξ‖ ^ 2) by ring]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * π) ^ 2),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [← hsqrt] at hc
  unfold l2norm
  exact (le_abs_self _).trans (Real.abs_le_sqrt hc)

/-! ### Lemma FG.3 (`‖T_c f‖_∞` bound on `H¹(ℝ)`) -/

/-- The positive-argument kernel `K_c(y) = ∫ a(τ) e^{i c (y τ + R(τ))} dτ` (`ce_physical_log_far.tex`, (FG.3a)). -/
noncomputable def kernelPaper (a : ℝ → ℂ) (R : ℝ → ℝ) (c y : ℝ) : ℂ :=
  ∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * (y * τ + R τ) : ℝ) : ℂ))

/-- The convolution operator `(T_c f)(L) = (c / (2π)) ∫ f(X) K_c(L - c_s X) dX` (`(FG.3a)`). -/
noncomputable def opT (a : ℝ → ℂ) (R : ℝ → ℝ) (c cs : ℝ) (f : ℝ → ℂ) (L : ℝ) : ℂ :=
  ((c / (2 * π) : ℝ) : ℂ) * ∫ X : ℝ, f X * kernelPaper a R c (L - cs * X)

private lemma memLp_two_of_integrable_bdd {h : ℝ → ℂ} {M : ℝ} (hh1 : Integrable h)
    (hhM : ∀ x, ‖h x‖ ≤ M) : MemLp h 2 volume := by
  have hM0 : 0 ≤ M := (norm_nonneg (h 0)).trans (hhM 0)
  rw [memLp_two_iff_integrable_sq_norm hh1.aestronglyMeasurable]
  refine (hh1.norm.const_mul M).mono' (hh1.aestronglyMeasurable.norm.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (hhM x) (norm_nonneg _)

private lemma fourier_toLp_eq_integral_ae {h : ℝ → ℂ} (hh1 : Integrable h) (hh2 : MemLp h 2 volume) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hh2.toLp h) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 h := by
  set U : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hh2.toLp h)
  have hU : MemLp (U : ℝ → ℂ) 2 volume := Lp.memLp U
  have htest : ∀ ψ : SchwartzMap ℝ ℂ,
      ∫ X : ℝ, starRingEnd ℂ (ψ X) * (U : ℝ → ℂ) X =
        ∫ X : ℝ, starRingEnd ℂ (ψ X) * (𝓕 h) X := by
    intro ψ
    have h1 : ∫ X : ℝ, starRingEnd ℂ (ψ X) * (U : ℝ → ℂ) X = ⟪ψ.toLp 2 volume, U⟫ := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [ψ.coeFn_toLp 2 volume] with X hX
      rw [hX, RCLike.inner_apply, starRingEnd_apply]
      ring
    have h2 : ⟪ψ.toLp 2 volume, U⟫ = ⟪(𝓕⁻ ψ).toLp 2 volume, hh2.toLp h⟫ := by
      have hstep := MeasureTheory.Lp.inner_fourier_eq (𝓕⁻ (ψ.toLp 2 volume)) (hh2.toLp h)
      have hleft : 𝓕 (𝓕⁻ (ψ.toLp 2 volume)) = ψ.toLp 2 volume :=
        FourierInvPair.fourier_fourierInv_eq _
      have hright : 𝓕 (hh2.toLp h) = U := rfl
      rw [hleft, hright] at hstep
      rw [hstep, SchwartzMap.toLp_fourierInv_eq]
    have h3 : ⟪(𝓕⁻ ψ).toLp 2 volume, hh2.toLp h⟫ =
        ∫ v : ℝ, starRingEnd ℂ ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) v) * h v := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(𝓕⁻ ψ).coeFn_toLp 2 volume, hh2.coeFn_toLp] with v hv1 hv2
      rw [hv1, hv2, RCLike.inner_apply, starRingEnd_apply]
      ring
    have hprod : Integrable (fun p : ℝ × ℝ =>
        starRingEnd ℂ (ψ p.1) * (Complex.exp (-(2 * π * Complex.I * ((p.1 * p.2 : ℝ) : ℂ))) * h p.2))
        (volume.prod volume) := by
      have hsep : Integrable (fun p : ℝ × ℝ => ‖ψ p.1‖ * ‖h p.2‖) (volume.prod volume) :=
        ψ.integrable.norm.mul_prod hh1.norm
      refine hsep.mono' ?_ (ae_of_all _ fun p => ?_)
      · have hcont1 : Continuous fun p : ℝ × ℝ =>
            starRingEnd ℂ (ψ p.1) * Complex.exp (-(2 * π * Complex.I * ((p.1 * p.2 : ℝ) : ℂ))) :=
          (Complex.continuous_conj.comp (ψ.continuous.comp continuous_fst)).mul
            (Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul
              (Complex.continuous_ofReal.comp (continuous_fst.mul continuous_snd)))))
        have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
            (starRingEnd ℂ (ψ p.1) * Complex.exp (-(2 * π * Complex.I * ((p.1 * p.2 : ℝ) : ℂ)))) * h p.2)
            (volume.prod volume) :=
          (hcont1.aestronglyMeasurable (μ := volume.prod volume)).mul
            (hh1.aestronglyMeasurable.comp_snd (μ := volume))
        refine hm.congr (ae_of_all _ fun p => ?_)
        exact mul_assoc _ _ _
      · have hne : ‖Complex.exp (-(2 * π * Complex.I * ((p.1 * p.2 : ℝ) : ℂ)))‖ = 1 := by
          have : -(2 * (π : ℂ) * Complex.I * ((p.1 * p.2 : ℝ) : ℂ)) =
              ((-(2 * π * (p.1 * p.2)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        rw [norm_mul, norm_mul, Complex.norm_conj, hne, one_mul]
    have hFub : ∫ X : ℝ, starRingEnd ℂ (ψ X) * (𝓕 h) X =
        ∫ v : ℝ, (∫ X : ℝ, starRingEnd ℂ (ψ X) * Complex.exp (-(2 * π * Complex.I * ((X * v : ℝ) : ℂ)))) * h v := by
      have hL : ∫ X : ℝ, starRingEnd ℂ (ψ X) * (𝓕 h) X =
          ∫ X : ℝ, ∫ v : ℝ, starRingEnd ℂ (ψ X) * (Complex.exp (-(2 * π * Complex.I * ((X * v : ℝ) : ℂ))) * h v) := by
        refine integral_congr_ae (ae_of_all _ fun X => ?_)
        dsimp only
        rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
        congr 1; funext v
        rw [smul_eq_mul]
        congr 2; congr 1; push_cast; ring
      rw [hL, integral_integral_swap hprod]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      have hpull : (fun x : ℝ => starRingEnd ℂ (ψ x) * (Complex.exp (-(2 * π * Complex.I * ((x * v : ℝ) : ℂ))) * h v)) =
          fun x : ℝ => (starRingEnd ℂ (ψ x) * Complex.exp (-(2 * π * Complex.I * ((x * v : ℝ) : ℂ)))) * h v := by
        funext x; ring
      simp_rw [hpull]
      exact integral_mul_const _ _
    have hconj : ∀ v : ℝ,
        (∫ X : ℝ, starRingEnd ℂ (ψ X) * Complex.exp (-(2 * π * Complex.I * ((X * v : ℝ) : ℂ)))) =
          starRingEnd ℂ ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) v) := by
      intro v
      have hinv : ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) v) =
          ∫ X : ℝ, Complex.exp (2 * π * Complex.I * ((X * v : ℝ) : ℂ)) * ψ X := by
        change (𝓕 (⇑ψ)) (-v) = _
        rw [Real.fourier_real_eq_integral_exp_smul]
        congr 1; funext X
        rw [smul_eq_mul]
        congr 2; push_cast; ring
      rw [hinv, ← integral_conj]
      congr 1; funext X
      rw [map_mul]
      have hexp : starRingEnd ℂ (Complex.exp (2 * π * Complex.I * ((X * v : ℝ) : ℂ))) =
          Complex.exp (-(2 * π * Complex.I * ((X * v : ℝ) : ℂ))) := by
        rw [← Complex.exp_conj]
        congr 1
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
        ring
      rw [hexp, mul_comm]
    rw [h1, h2, h3, hFub]
    simp_rw [hconj]
  set w : ℝ → ℂ := fun X => ((1 + X ^ 2 : ℝ)⁻¹ : ℂ) * ((U : ℝ → ℂ) X - (𝓕 h) X)
  have hFourCont : Continuous (𝓕 h) := by
    have hrew : (𝓕 h) = fun X : ℝ =>
        ∫ v : ℝ, Complex.exp (-(2 * π * Complex.I * ((X * v : ℝ) : ℂ))) * h v := by
      funext X
      rw [Real.fourier_real_eq_integral_exp_smul]
      congr 1; funext v
      rw [smul_eq_mul]
      congr 2; push_cast; ring
    rw [hrew]
    refine continuous_of_dominated (bound := fun v => ‖h v‖) ?_ ?_ hh1.norm ?_
    · intro X
      exact ((by fun_prop : Continuous fun v : ℝ =>
        Complex.exp (-(2 * π * Complex.I * ((X * v : ℝ) : ℂ)))).aestronglyMeasurable.mul
        hh1.aestronglyMeasurable)
    · intro X
      refine ae_of_all _ fun v => ?_
      have he : -(2 * (π : ℂ) * Complex.I * ((X * v : ℝ) : ℂ)) =
          (((-(2 * π * (X * v)) : ℝ) : ℂ) * Complex.I) := by push_cast; ring
      rw [norm_mul, he, Complex.norm_exp_ofReal_mul_I, one_mul]
    · exact ae_of_all _ fun v => by fun_prop
  have hFourBdd : ∀ X : ℝ, ‖(𝓕 h) X‖ ≤ ∫ v : ℝ, ‖h v‖ := by
    intro X
    calc ‖(𝓕 h) X‖
        = ‖∫ v : ℝ, Complex.exp ((↑(-2 * π * v * X) : ℂ) * Complex.I) • h v‖ := by
            rw [Real.fourier_real_eq_integral_exp_smul]
      _ ≤ ∫ v : ℝ, ‖Complex.exp ((↑(-2 * π * v * X) : ℂ) * Complex.I) • h v‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, ‖h v‖ := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          dsimp only
          rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hwMem : MemLp w 2 volume := by
    have hinv2 : MemLp (fun X : ℝ => ((1 + X ^ 2 : ℝ)⁻¹ : ℂ)) 2 volume := by
      refine (memLp_two_iff_integrable_sq_norm continuous_inv_one_add_sq_complex.aestronglyMeasurable).mpr ?_
      refine integrable_inv_one_add_sq.mono' (continuous_inv_one_add_sq_complex.aestronglyMeasurable.norm.pow 2)
        (ae_of_all _ fun X => ?_)
      have hden : 0 < 1 + X ^ 2 := by positivity
      have hle : (1 + X ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [sq_nonneg X])
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden, sq]
      simpa using mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hden.le)
    have h2 : MemLp (fun X => (𝓕 h) X * ((1 + X ^ 2 : ℝ)⁻¹ : ℂ)) 2 volume :=
      memLp_two_bdd_mul (integral_nonneg fun _ => norm_nonneg _) hFourCont.aestronglyMeasurable
        hFourBdd hinv2
    have h1 := memLp_inv_one_add_sq_mul hU
    refine (h1.sub h2).ae_eq (ae_of_all _ fun X => ?_)
    dsimp [w]; ring
  have h0 : ∀ η : SchwartzMap ℝ ℂ, ∫ X : ℝ, starRingEnd ℂ (η X) * w X = 0 := by
    intro η
    set ψ : SchwartzMap ℝ ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun X : ℝ => ((1 + X ^ 2 : ℝ)⁻¹ : ℂ)) η
    have hval : ∀ X : ℝ, ψ X = ((1 + X ^ 2 : ℝ)⁻¹ : ℂ) * η X := fun X => by
      simpa [ψ, smul_eq_mul] using
        SchwartzMap.smulLeftCLM_apply_apply inv_one_add_sq_hasTemperateGrowth η X
    have hi1 : Integrable (fun X => starRingEnd ℂ (ψ X) * (U : ℝ → ℂ) X) :=
      ((conjSchwartz ψ).memLp 2 volume).integrable_mul hU
    have hi2 : Integrable (fun X => starRingEnd ℂ (ψ X) * (𝓕 h) X) := by
      refine (ψ.integrable.norm.const_mul (∫ v : ℝ, ‖h v‖)).mono' ?_ (ae_of_all _ fun X => ?_)
      · exact ((by fun_prop : Continuous fun X : ℝ => starRingEnd ℂ (ψ X)).aestronglyMeasurable.mul
          hFourCont.aestronglyMeasurable)
      · rw [norm_mul, Complex.norm_conj, mul_comm]
        exact mul_le_mul_of_nonneg_right (hFourBdd X) (norm_nonneg _)
    have hsub : (fun X => starRingEnd ℂ (η X) * w X) = fun X =>
        starRingEnd ℂ (ψ X) * (U : ℝ → ℂ) X - starRingEnd ℂ (ψ X) * (𝓕 h) X := by
      funext X
      rw [hval, map_mul, map_inv₀, Complex.conj_ofReal]
      dsimp [w]; ring
    rw [hsub, integral_sub hi1 hi2, htest ψ, sub_self]
  filter_upwards [eq_zero_ae_of_forall_schwartz_inner hwMem h0] with X hX
  have hden : ((1 + X ^ 2 : ℝ)⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (by positivity : (1 + X ^ 2 : ℝ) ≠ 0)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hX).resolve_left hden)

private lemma memLp_conj {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun x => starRingEnd ℂ (f x)) 2 volume := by
  have hae : AEStronglyMeasurable (fun x => starRingEnd ℂ (f x)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  have hint := hf.integrable_norm_pow (by norm_num)
  simpa [Complex.norm_conj] using hint

private lemma fourierInv_conj_eq_conj_fourier_ae {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
        ((memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x))) : ℝ → ℂ) =ᵐ[volume]
      fun v => starRingEnd ℂ
        (((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) v) := by
  set L : Lp ℂ 2 volume :=
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm ((memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x)))
  set F : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f)
  set R : Lp ℂ 2 volume := (memLp_conj (Lp.memLp F)).toLp (fun v => starRingEnd ℂ ((F : ℝ → ℂ) v))
  have hLR : L = R := by
    have htest : ∀ ψ : SchwartzMap ℝ ℂ, ⟪ψ.toLp 2 volume, L⟫ = ⟪ψ.toLp 2 volume, R⟫ := by
      intro ψ
      have h1 : ⟪ψ.toLp 2 volume, L⟫ =
          ⟪(𝓕 ψ).toLp 2 volume, (memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x))⟫ := by
        have hstep := (MeasureTheory.Lp.inner_fourier_eq (ψ.toLp 2 volume) L).symm
        have hL_fourier : 𝓕 L = (memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x)) :=
          (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
        rw [SchwartzMap.toLp_fourier_eq, hL_fourier] at hstep
        exact hstep
      have h2 : ⟪(𝓕 ψ).toLp 2 volume, (memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x))⟫ =
          starRingEnd ℂ (∫ x : ℝ, (𝓕 ψ : SchwartzMap ℝ ℂ) x * f x) := by
        rw [MeasureTheory.L2.inner_def, ← integral_conj]
        refine integral_congr_ae ?_
        filter_upwards [(𝓕 ψ).coeFn_toLp 2 volume, (memLp_conj hf).coeFn_toLp] with x hx1 hx2
        rw [hx1, hx2, RCLike.inner_apply, map_mul]
        ring
      have h3 : (∫ x : ℝ, (𝓕 ψ : SchwartzMap ℝ ℂ) x * f x) =
          ⟪(𝓕⁻ (conjSchwartz ψ)).toLp 2 volume, hf.toLp f⟫ := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [(𝓕⁻ (conjSchwartz ψ)).coeFn_toLp 2 volume, hf.coeFn_toLp] with x hx1 hx2
        rw [hx1, hx2, RCLike.inner_apply]
        have hconj : starRingEnd ℂ ((𝓕⁻ (conjSchwartz ψ) : SchwartzMap ℝ ℂ) x) =
            (𝓕 ψ : SchwartzMap ℝ ℂ) x := by
          have hinv : ((𝓕⁻ (conjSchwartz ψ) : SchwartzMap ℝ ℂ) x) =
              ∫ ξ : ℝ, Complex.exp (2 * π * Complex.I * ((x * ξ : ℝ) : ℂ)) * starRingEnd ℂ (ψ ξ) := by
            change (𝓕 (⇑(conjSchwartz ψ))) (-x) = _
            rw [Real.fourier_real_eq_integral_exp_smul]
            congr 1; funext ξ
            rw [smul_eq_mul, conjSchwartz_apply]
            congr 2; push_cast; ring
          rw [hinv, ← integral_conj]
          change _ = (𝓕 (⇑ψ)) x
          rw [Real.fourier_real_eq_integral_exp_smul]
          congr 1; funext ξ
          rw [map_mul, Complex.conj_conj, smul_eq_mul, ← Complex.exp_conj]
          have hconj_arg : starRingEnd ℂ (2 * π * Complex.I * ((x * ξ : ℝ) : ℂ)) =
              (↑(-2 * π * ξ * x) : ℂ) * Complex.I := by
            simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
            push_cast; ring
          rw [hconj_arg, mul_comm]
        rw [hconj, mul_comm]
      have h4 : ⟪(𝓕⁻ (conjSchwartz ψ)).toLp 2 volume, hf.toLp f⟫ =
          ∫ v : ℝ, ψ v * (F : ℝ → ℂ) v := by
        calc ⟪(𝓕⁻ (conjSchwartz ψ)).toLp 2 volume, hf.toLp f⟫
            = ⟪𝓕⁻ ((conjSchwartz ψ).toLp 2 volume), hf.toLp f⟫ := by
                rw [SchwartzMap.toLp_fourierInv_eq]
          _ = ⟪(conjSchwartz ψ).toLp 2 volume, F⟫ := by
                have hstep := (MeasureTheory.Lp.inner_fourier_eq
                  (𝓕⁻ ((conjSchwartz ψ).toLp 2 volume)) (hf.toLp f)).symm
                have hl : 𝓕 (𝓕⁻ ((conjSchwartz ψ).toLp 2 volume)) = (conjSchwartz ψ).toLp 2 volume :=
                  FourierInvPair.fourier_fourierInv_eq _
                have hr : 𝓕 (hf.toLp f) = F := rfl
                rw [hl, hr] at hstep
                exact hstep
          _ = ∫ v : ℝ, ψ v * (F : ℝ → ℂ) v := by
                rw [MeasureTheory.L2.inner_def]
                refine integral_congr_ae ?_
                filter_upwards [(conjSchwartz ψ).coeFn_toLp 2 volume] with v hv
                rw [hv, conjSchwartz_apply, RCLike.inner_apply, Complex.conj_conj]
                ring
      have h5 : starRingEnd ℂ (∫ v : ℝ, ψ v * (F : ℝ → ℂ) v) = ⟪ψ.toLp 2 volume, R⟫ := by
        rw [← integral_conj, MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [ψ.coeFn_toLp 2 volume, (memLp_conj (Lp.memLp F)).coeFn_toLp] with v hv1 hv2
        rw [hv1, hv2, RCLike.inner_apply, map_mul]
        ring
      rw [h1, h2, h3, h4, h5]
    have hdiff : ∀ ψ : SchwartzMap ℝ ℂ, ⟪ψ.toLp 2 volume, L - R⟫ = 0 := fun ψ => by
      rw [inner_sub_right, htest ψ, sub_self]
    have h0 : ∀ v : Lp ℂ 2 volume, ⟪v, L - R⟫ = 0 := fun v =>
      congrFun ((SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).equalizer
        (continuous_id.inner continuous_const) continuous_const (funext hdiff)) v
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (h0 (L - R)))
  filter_upwards [(memLp_conj (Lp.memLp F)).coeFn_toLp] with v hv
  rw [hLR, hv]

private lemma l2_parseval_bilinear {f h : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hh1 : Integrable h) (hh2 : MemLp h 2 volume) :
    ∫ X : ℝ, f X * (𝓕 h) X =
      ∫ v : ℝ, ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) v * h v := by
  have hFeq := fourier_toLp_eq_integral_ae hh1 hh2
  have hinv := fourierInv_conj_eq_conj_fourier_ae hf
  have h1 : ∫ X : ℝ, f X * (𝓕 h) X =
      ⟪(memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x)),
        MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hh2.toLp h)⟫ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_conj hf).coeFn_toLp, hFeq] with X hX1 hX2
    rw [hX1, hX2, RCLike.inner_apply, Complex.conj_conj]
    ring
  have h2 : ⟪(memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x)),
        MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hh2.toLp h)⟫ =
      ⟪(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
        ((memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x))), hh2.toLp h⟫ := by
    have hstep := MeasureTheory.Lp.inner_fourier_eq
      (𝓕⁻ ((memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x)))) (hh2.toLp h)
    rw [FourierInvPair.fourier_fourierInv_eq] at hstep
    exact hstep
  have h3 : ⟪(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
        ((memLp_conj hf).toLp (fun x => starRingEnd ℂ (f x))), hh2.toLp h⟫ =
      ∫ v : ℝ, ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hf.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) v * h v := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hinv, hh2.coeFn_toLp] with v hv1 hv2
    rw [hv1, hv2, RCLike.inner_apply, Complex.conj_conj]
    ring
  rw [h1, h2, h3]

/-- **Exact multiplier representation `(FG.3b)`** for `f ∈ H¹(ℝ)` (`WeakDerivL2 f f'`):
for `c > 0`, `cs ≠ 0`, `a ∈ L¹(ℝ)` bounded (`‖a τ‖ ≤ M`), and `R` measurable,
`(T_c f)(L) = (1 / (2π)) ∫ a(w/c) e^{ic R(w/c)} f̂(cs w) e^{i L w} dw`. -/
theorem opT_eq_fourier_multiplier {a : ℝ → ℂ} {R : ℝ → ℝ} {c cs M : ℝ}
    (hc : 0 < c) (hcs : cs ≠ 0) (ha1 : Integrable a) (haM : ∀ τ : ℝ, ‖a τ‖ ≤ M)
    (hR : Measurable R) {f f' : ℝ → ℂ} (h : WeakDerivL2 f f') (L : ℝ) :
    opT a R c cs f L =
      (1 / (2 * π) : ℝ) • ∫ w : ℝ,
        a (w / c) * Complex.exp (Complex.I * ((c * R (w / c) : ℝ) : ℂ)) *
          fourierPaperL2 h (cs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
  have hcne : c ≠ 0 := hc.ne'
  set α : ℝ := 2 * π / (c * cs) with hα_def
  have hα_ne : α ≠ 0 := div_ne_zero (by positivity) (mul_ne_zero hcne hcs)
  set hL : ℝ → ℂ := fun v =>
    a (α * v) * Complex.exp (Complex.I * ((c * R (α * v) + 2 * π * L * v / cs : ℝ) : ℂ))
  have hhL1 : Integrable hL := by
    have ha_comp : Integrable (fun v => a (α * v)) :=
      (integrable_comp_mul_left_iff a hα_ne).mpr ha1
    have hphase : AEStronglyMeasurable
        (fun v : ℝ => Complex.exp (Complex.I * ((c * R (α * v) + 2 * π * L * v / cs : ℝ) : ℂ)))
        volume := by
      refine Measurable.aestronglyMeasurable ?_
      refine Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.continuous_ofReal.measurable.comp ?_))
      exact (measurable_const.mul (hR.comp (measurable_const.mul measurable_id))).add
        ((measurable_const.mul measurable_id).div_const cs)
    have hi : Integrable (fun v => ‖a (α * v)‖) := ha_comp.norm
    refine hi.mono' ?_ (ae_of_all _ fun v => ?_)
    · exact ha_comp.aestronglyMeasurable.mul hphase
    · have hexp : Complex.I * ((c * R (α * v) + 2 * π * L * v / cs : ℝ) : ℂ) =
          ((c * R (α * v) + 2 * π * L * v / cs : ℝ) : ℂ) * Complex.I := by ring
      rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hhLM : ∀ v : ℝ, ‖hL v‖ ≤ M := fun v => by
    have : Complex.I * ((c * R (α * v) + 2 * π * L * v / cs : ℝ) : ℂ) =
        ((c * R (α * v) + 2 * π * L * v / cs : ℝ) : ℂ) * Complex.I := by ring
    rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact haM (α * v)
  have hhL2 : MemLp hL 2 volume := memLp_two_of_integrable_bdd hhL1 hhLM
  have hK : ∀ X : ℝ, kernelPaper a R c (L - cs * X) =
      ((2 * π / (c * |cs|) : ℝ) : ℂ) * (𝓕 hL) X := by
    intro X
    unfold kernelPaper
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hcov := Measure.integral_comp_mul_left
      (fun τ : ℝ => a τ * Complex.exp (Complex.I * ((c * ((L - cs * X) * τ + R τ) : ℝ) : ℂ))) α
    have heq : (fun v : ℝ => a (α * v) * Complex.exp (Complex.I * ((c * ((L - cs * X) * (α * v) + R (α * v)) : ℝ) : ℂ))) =
        fun v : ℝ => Complex.exp ((↑(-2 * π * v * X) : ℂ) * Complex.I) • hL v := by
      funext v
      rw [smul_eq_mul]
      have hreal : c * ((L - cs * X) * (α * v) + R (α * v)) =
          -(2 * π * v * X) + (c * R (α * v) + 2 * π * L * v / cs) := by
        rw [hα_def]; field_simp; ring
      have hexp : Complex.exp (Complex.I * ((c * ((L - cs * X) * (α * v) + R (α * v)) : ℝ) : ℂ)) =
          Complex.exp ((↑(-2 * π * v * X) : ℂ) * Complex.I) *
            Complex.exp (Complex.I * ((c * R (α * v) + 2 * π * L * v / cs : ℝ) : ℂ)) := by
        rw [hreal, ← Complex.exp_add]
        apply congr_arg Complex.exp
        push_cast
        ring
      rw [hexp]
      dsimp [hL]
      ring
    rw [heq] at hcov
    have hI : (∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * ((L - cs * X) * τ + R τ) : ℝ) : ℂ))) =
        ((|α| : ℝ) : ℂ) * ∫ v : ℝ, Complex.exp ((↑(-2 * π * v * X) : ℂ) * Complex.I) • hL v := by
      have hsc : ((|α| : ℝ) : ℂ) * ((|α⁻¹| : ℝ) : ℂ) = 1 := by
        exact_mod_cast by rw [abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hα_ne)]
      calc _ = ((|α| : ℝ) : ℂ) * ((|α⁻¹| : ℝ) : ℂ) * _ := by rw [hsc, one_mul]
        _ = ((|α| : ℝ) : ℂ) * ((|α⁻¹| : ℝ) • _) := by rw [mul_assoc, Complex.real_smul]
        _ = ((|α| : ℝ) : ℂ) * ∫ v : ℝ, _ := by rw [← hcov]
    rw [hI]
    congr 1
    exact_mod_cast by
      rw [hα_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_mul, abs_of_pos hc]
  unfold opT
  simp_rw [hK]
  have hfac : ∀ X : ℝ, f X * (((2 * π / (c * |cs|) : ℝ) : ℂ) * (𝓕 hL) X) =
      ((2 * π / (c * |cs|) : ℝ) : ℂ) * (f X * (𝓕 hL) X) := fun X => by ring
  simp_rw [hfac, integral_const_mul]
  rw [← mul_assoc, show ((c / (2 * π) : ℝ) : ℂ) * ((2 * π / (c * |cs|) : ℝ) : ℂ) = ((|cs|⁻¹ : ℝ) : ℂ) by
    exact_mod_cast by field_simp, l2_parseval_bilinear h.memLp hhL1 hhL2]
  set F : ℝ → ℂ := ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ)
  set β : ℝ := cs / (2 * π) with hβ_def
  have hβ_ne : β ≠ 0 := div_ne_zero hcs (by positivity)
  have hcov2 := Measure.integral_comp_mul_left (fun v : ℝ => F v * hL v) β
  have heq2 : (fun w : ℝ => F (β * w) * hL (β * w)) = fun w : ℝ =>
      a (w / c) * Complex.exp (Complex.I * ((c * R (w / c) : ℝ) : ℂ)) *
        fourierPaperL2 h (cs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
    funext w
    have hv1 : α * (β * w) = w / c := by simp [hα_def, hβ_def]; field_simp
    have hv2 : β * w = (2 * π)⁻¹ * (cs * w) := by simp [hβ_def]; ring
    have hv3 : 2 * π * L * (β * w) / cs = L * w := by simp [hβ_def]; field_simp
    dsimp [hL, fourierPaperL2, F]
    rw [hv1, hv3, hv2, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [heq2] at hcov2
  have hsc2 : ((|cs|⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, F v * hL v =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ w : ℝ, a (w / c) * Complex.exp (Complex.I * ((c * R (w / c) : ℝ) : ℂ)) *
        fourierPaperL2 h (cs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ)) := by
    have hβabs : |β| = |cs| / (2 * π) := by
      rw [hβ_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    calc ((|cs|⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, F v * hL v
        = ((|cs|⁻¹ : ℝ) : ℂ) * (((|β| : ℝ) : ℂ) * ((|β⁻¹| : ℝ) • ∫ v : ℝ, F v * hL v)) := by
            congr 1
            rw [Complex.real_smul, ← mul_assoc]
            have h1 : ((|β| : ℝ) : ℂ) * ((|β⁻¹| : ℝ) : ℂ) = 1 := by
              exact_mod_cast by rw [abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hβ_ne)]
            rw [h1, one_mul]
      _ = ((|cs|⁻¹ * |β| : ℝ) : ℂ) * ∫ w : ℝ, _ := by
            rw [← hcov2, ← mul_assoc, Complex.ofReal_mul]
      _ = ((1 / (2 * π) : ℝ) : ℂ) * ∫ w : ℝ, _ := by
            congr 1
            exact_mod_cast by
              have habs : |cs| ≠ 0 := abs_ne_zero.mpr hcs
              rw [hβabs]; field_simp
  rw [hsc2, Complex.real_smul]

/-- **Lemma FG.3 (`cepf:FG3`, eq. `(FG.3)`):** for `f ∈ H¹(ℝ)` (`WeakDerivL2 f f'`), `c > 0`, `c_s ≠ 0`,
`a ∈ L¹(ℝ)` with `‖a τ‖ ≤ M`, and measurable `R : ℝ → ℝ`,
`‖(T_c f)(L)‖ ≤ (M / |c_s|) (‖f‖₂ ‖f'‖₂)^{1/2}` uniformly in `L` and `c`. -/
theorem Tc_sup_bound {a : ℝ → ℂ} {R : ℝ → ℝ} {c cs M : ℝ}
    (hc : 0 < c) (hcs : cs ≠ 0) (ha1 : Integrable a) (haM : ∀ τ : ℝ, ‖a τ‖ ≤ M)
    (hR : Measurable R) {f f' : ℝ → ℂ} (h : WeakDerivL2 f f') (L : ℝ) :
    ‖opT a R c cs f L‖ ≤ M / |cs| * Real.sqrt (l2norm f * l2norm f') := by
  have hM0 : 0 ≤ M := (norm_nonneg (a 0)).trans (haM 0)
  rw [opT_eq_fourier_multiplier hc hcs ha1 haM hR h L, Complex.real_smul]
  obtain ⟨hfL1, hfbd⟩ := fourier_L1_le_sqrt_mul_H1 h
  set g : ℝ → ℂ := fun w =>
    a (w / c) * Complex.exp (Complex.I * ((c * R (w / c) : ℝ) : ℂ)) *
      fourierPaperL2 h (cs * w) * Complex.exp (Complex.I * ((L * w : ℝ) : ℂ))
  have hg_norm : ∀ w : ℝ, ‖g w‖ ≤ M * ‖fourierPaperL2 h (cs * w)‖ := by
    intro w
    dsimp [g]
    have h1 : Complex.I * ((c * R (w / c) : ℝ) : ℂ) = ((c * R (w / c) : ℝ) : ℂ) * Complex.I := by ring
    have h2 : Complex.I * ((L * w : ℝ) : ℂ) = ((L * w : ℝ) : ℂ) * Complex.I := by ring
    rw [norm_mul, norm_mul, norm_mul, h1, h2, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_exp_ofReal_mul_I, mul_one, mul_one]
    exact mul_le_mul_of_nonneg_right (haM (w / c)) (norm_nonneg _)
  have hint_rhs : Integrable (fun w : ℝ => M * ‖fourierPaperL2 h (cs * w)‖) :=
    ((integrable_comp_mul_left_iff (fun ξ => ‖fourierPaperL2 h ξ‖) hcs).mpr hfL1.norm).const_mul M
  have hcov : ∫ w : ℝ, M * ‖fourierPaperL2 h (cs * w)‖ =
      (M / |cs|) * ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖ := by
    rw [integral_const_mul]
    have h2 := Measure.integral_comp_mul_left (fun ξ => ‖fourierPaperL2 h ξ‖) cs
    rw [smul_eq_mul] at h2
    have habs : |cs| ≠ 0 := abs_ne_zero.mpr hcs
    have h2' : |cs| * ∫ w : ℝ, ‖fourierPaperL2 h (cs * w)‖ = ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖ := by
      have hi : |cs| * (|cs⁻¹| * ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖) = ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖ := by
        rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ habs, one_mul]
      calc |cs| * ∫ w : ℝ, ‖fourierPaperL2 h (cs * w)‖
          = |cs| * (|cs⁻¹| * ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖) := by rw [h2]
        _ = ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖ := hi
    calc M * ∫ w : ℝ, ‖fourierPaperL2 h (cs * w)‖
        = M / |cs| * (|cs| * ∫ w : ℝ, ‖fourierPaperL2 h (cs * w)‖) := by
            rw [← mul_assoc, div_mul_cancel₀ _ habs]
      _ = M / |cs| * ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖ := by rw [h2']
  calc ‖((1 / (2 * π) : ℝ) : ℂ) * ∫ w : ℝ, g w‖
      = (1 / (2 * π)) * ‖∫ w : ℝ, g w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ (1 / (2 * π)) * ∫ w : ℝ, ‖g w‖ := by
          gcongr; exact norm_integral_le_integral_norm _
    _ ≤ (1 / (2 * π)) * ∫ w : ℝ, M * ‖fourierPaperL2 h (cs * w)‖ :=
          mul_le_mul_of_nonneg_left
            (integral_mono_of_nonneg (ae_of_all _ fun w => norm_nonneg (g w)) hint_rhs
              (ae_of_all _ fun w => hg_norm w))
            (by positivity)
    _ = (1 / (2 * π)) * ((M / |cs|) * ∫ ξ : ℝ, ‖fourierPaperL2 h ξ‖) := by rw [hcov]
    _ ≤ (1 / (2 * π)) * ((M / |cs|) * (2 * π * Real.sqrt (l2norm f * l2norm f'))) := by
          gcongr
    _ = M / |cs| * Real.sqrt (l2norm f * l2norm f') := by field_simp

/-- info: 'FormalResearch.CohnElkies.fourierL2Deriv_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourierL2Deriv_ae

/-- info: 'FormalResearch.CohnElkies.fourier_L1_le_sqrt_mul_H1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_L1_le_sqrt_mul_H1

/-- info: 'FormalResearch.CohnElkies.opT_eq_fourier_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms opT_eq_fourier_multiplier

/-- info: 'FormalResearch.CohnElkies.Tc_sup_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Tc_sup_bound

end H1Extension

end FormalResearch.CohnElkies
