module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The `L¹` norm of a Fourier transform by the geometric mean of two `L²` norms (FG.3, PF.2)

Source: `CFT/notes/ce_physical_log_far.tex`, Lemma FG.3 (its proof's step `‖f̂‖₁ ≲ ‖f‖₂^{1/2} ‖f'‖₂^{1/2}`), and
the `L¹` Fourier interpolation used in PF.2 and PF.2L; queue row CEQ20 of
`CFT/modular_bootstrap/notes/CE_MISSING_QUEUE.md`.

Normalisation: `f̂(ξ) = ∫ f(X) e^{-iXξ} dX` (`fourierPaper`), the convention of FG.3. `l2norm f = (∫ |f|²)^{1/2}`.

**Statement proved** (`fourier_L1_le_sqrt_mul`, proved, for Schwartz `g : ℝ → ℂ`):
`∫ ξ, ‖f̂ ξ‖ ≤ 2 π · (‖g‖₂ · ‖g'‖₂)^{1/2}`, i.e. the constant is `C = 2π` in this normalisation.

**Proof.** Pointwise AM–GM with the weight `1 + κ² ξ²`, integrated against `|ĝ|` (Mathlib's transform, with `2π` in the
exponent), gives `c² ≤ π (N/κ + κ Y)` for every `κ > 0`, where `c = ∫|ĝ|`, `N = ‖g‖₂²`, `Y = ∫ ξ² |ĝ|²`; the
optimum over `κ` gives `c² ≤ 2π √(N Y)`. Plancherel and `ĝ' = 2πi ξ ĝ` (Mathlib's `Real.fourier_deriv`) give
`4π² Y = ‖g'‖₂²`. The change of variables to the paper's `f̂` costs the factor `2π`.

**Not covered.** `g` is a Schwartz function: FG.3 in the paper is stated for `f ∈ H¹(ℝ)`, and the extension to `H¹`
by density is not formalised. The paper's multiplier bound `‖T_c f‖_∞` (with the kernel `K_c`) is not formalised;
only the `L¹` Fourier bound that it uses is.
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
  · -- `Y = 0`: take `κ = π (N+1)/c²`, which makes `π N / κ = c² N/(N+1) < c²`.
    subst hY0
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
    · -- `N = 0`: take `κ = c²/(2π Y)`, which makes `π κ Y = c²/2 < c²`.
      subst hN0
      have hYne : Y ≠ 0 := hYpos.ne'
      have hκ : 0 < c ^ 2 / (2 * π * Y) := div_pos hc2 (mul_pos (mul_pos two_pos hpi) hYpos)
      have h1 := h _ hκ
      have e : π * (0 / (c ^ 2 / (2 * π * Y)) + c ^ 2 / (2 * π * Y) * Y) = c ^ 2 / 2 := by
        rw [zero_div, zero_add]
        field_simp
      rw [e] at h1
      linarith
    · -- `N, Y > 0`: take `κ = √(N/Y)`; then `N/κ = κ Y = √(N Y)` and the bound reads `2π √(N Y) < c²`.
      obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.sqrt (N / Y) := ⟨_, rfl⟩
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

end FormalResearch.CohnElkies
