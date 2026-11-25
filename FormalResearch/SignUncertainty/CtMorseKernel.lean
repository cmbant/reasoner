module

public import FormalResearch.SignUncertainty.CtMorseFresnel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The base case of the Morse expansion: a Hadamard-type average against `e^{iλX²/2}`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:morse-expansion` (the case `r = 1`).  **Proved.**

For `k` continuous and integrable with `|k| ≤ M`, the function `G(X) = ∫₀¹ t k(tX) dt` (which is `(h/X)'` for `k = h''`,
`h(0)=0`) satisfies `|∫ G(X) e^{iλX²/2} dX| ≤ 2√2 π M / √|λ|`.

Proof: Fubini turns the integral into `∫ k(Y) K(Y) dY` with `K(Y) = ∫₀¹ e^{iλY²/(2t²)} dt`, and
`|K(Y)| ≤ min(1, 2/(|λ|Y²)) ≤ 2/(1 + |λ|Y²/2)` by one integration by parts in `t` (against `t³ ∂_t`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtMorse

/-- `K_β = ∫₀¹ e^{iβ/t²} dt`. -/
noncomputable def kerB (β : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * (β : ℂ) / (t : ℂ) ^ 2)

lemma norm_cexp_I_mul (a : ℝ) : ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := Complex.norm_exp_I_mul_ofReal a

lemma norm_exp_kern (β t : ℝ) : ‖Complex.exp (Complex.I * (β : ℂ) / (t : ℂ) ^ 2)‖ = 1 := by
  have : Complex.I * (β : ℂ) / (t : ℂ) ^ 2 = Complex.I * ((β / t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]; exact norm_cexp_I_mul _

lemma norm_kerB_le_one (β : ℝ) : ‖kerB β‖ ≤ 1 := by
  unfold kerB
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => Complex.exp (Complex.I * (β : ℂ) / (t : ℂ) ^ 2)) (C := 1) (fun t _ => (norm_exp_kern β t).le)
  simpa using this

lemma measurable_kern (β : ℝ) : Measurable fun t : ℝ => Complex.exp (Complex.I * (β : ℂ) / (t : ℂ) ^ 2) := by
  fun_prop

/-- `|K_β| ≤ 1/|β|`. -/
lemma norm_kerB_le_inv {β : ℝ} (hβ : β ≠ 0) : ‖kerB β‖ ≤ 1 / |β| := by
  set e : ℝ → ℂ := fun t => Complex.exp (Complex.I * (β : ℂ) / (t : ℂ) ^ 2) with he
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ 3 * e t with hF
  set F' : ℝ → ℂ := fun t => (3 * (t : ℂ) ^ 2 - 2 * Complex.I * β) * e t with hF'
  have hnorm : ∀ t, ‖e t‖ = 1 := norm_exp_kern β
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' t) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    have h1 : HasDerivAt (fun z : ℂ => z ^ 3 * Complex.exp (Complex.I * β / z ^ 2))
        (3 * (t : ℂ) ^ 2 * Complex.exp (Complex.I * β / (t : ℂ) ^ 2) +
          (t : ℂ) ^ 3 * (Complex.exp (Complex.I * β / (t : ℂ) ^ 2) *
            ((0 * (t : ℂ) ^ 2 - Complex.I * β * (2 * (t : ℂ))) / ((t : ℂ) ^ 2) ^ 2))) (t : ℂ) := by
      have hp : HasDerivAt (fun z : ℂ => z ^ 3) (3 * (t : ℂ) ^ 2) (t : ℂ) := by
        simpa using hasDerivAt_pow 3 (t : ℂ)
      have hq : HasDerivAt (fun z : ℂ => Complex.I * β / z ^ 2)
          ((0 * (t : ℂ) ^ 2 - Complex.I * β * (2 * (t : ℂ))) / ((t : ℂ) ^ 2) ^ 2) (t : ℂ) := by
        have h2 : HasDerivAt (fun z : ℂ => z ^ 2) (2 * (t : ℂ)) (t : ℂ) := by
          simpa using hasDerivAt_pow 2 (t : ℂ)
        exact (hasDerivAt_const (t : ℂ) (Complex.I * (β : ℂ))).div h2 (pow_ne_zero 2 ht0)
      exact hp.mul hq.cexp
    have h2 := h1.comp_ofReal
    refine h2.congr_deriv ?_
    simp only [hF', he]
    field_simp
    ring
  have hcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · subst h0
      have hF0 : F 0 = 0 := by simp [hF]
      rw [ContinuousWithinAt, hF0]
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      have hb : ∀ s : ℝ, ‖F s‖ = |s| ^ 3 := by
        intro s; simp only [hF, norm_mul, hnorm, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      simp only [hb]
      have hc3 : Continuous fun s : ℝ => |s| ^ 3 := by fun_prop
      have h3 : Tendsto (fun s : ℝ => |s| ^ 3) (𝓝 0) (𝓝 (|(0 : ℝ)| ^ 3)) := hc3.tendsto 0
      rw [show |(0 : ℝ)| ^ 3 = 0 by simp] at h3
      exact h3.mono_left nhdsWithin_le_nhds
    · by_cases h1 : t < 1
      · exact (hd t ⟨hpos, h1⟩).continuousAt.continuousWithinAt
      · have : t = 1 := le_antisymm ht.2 (not_lt.mp h1)
        subst this
        have hc : ContinuousAt F 1 := by
          have ht0 : ((1 : ℝ) : ℂ) ≠ 0 := by norm_num
          simp only [hF, he]
          refine ContinuousAt.mul (by fun_prop) ?_
          refine Complex.continuous_exp.continuousAt.comp ?_
          refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
          simp
        exact hc.continuousWithinAt
  have hmeasE : Measurable e := measurable_kern β
  have hbE : ∀ t, ‖e t‖ ≤ 1 := fun t => (hnorm t).le
  have hint : IntervalIntegrable F' volume 0 1 := by
    refine (intervalIntegrable_const (c := 3 + 2 * |β|)).mono_fun'
      ((((by fun_prop : Measurable fun t : ℝ => (3 * (t : ℂ) ^ 2 - 2 * Complex.I * β))).mul hmeasE).aestronglyMeasurable)
      ?_
    rw [uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [hF', norm_mul, hnorm, mul_one]
    calc ‖3 * (t : ℂ) ^ 2 - 2 * Complex.I * β‖ ≤ ‖3 * (t : ℂ) ^ 2‖ + ‖2 * Complex.I * (β : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 + 2 * |β| := by
          have h1 : ‖3 * (t : ℂ) ^ 2‖ ≤ 3 := by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            have : |t| ≤ 1 := by rw [abs_of_pos ht.1]; exact ht.2
            have : |t| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg t) this
            norm_num; linarith
          have h2 : ‖2 * Complex.I * (β : ℂ)‖ = 2 * |β| := by
            simp [norm_mul, Complex.norm_real]
          linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (zero_le_one) hcont hd hint
  have hF1 : F 1 = e 1 := by simp [hF]
  have hF0 : F 0 = 0 := by simp [hF]
  have hi1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ 2 * e t) volume 0 1 := by
    refine (intervalIntegrable_const (c := 1)).mono_fun'
      ((((by fun_prop : Measurable fun t : ℝ => (t : ℂ) ^ 2)).mul hmeasE).aestronglyMeasurable) ?_
    rw [uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, hnorm, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have : |t| ≤ 1 := by rw [abs_of_pos ht.1]; exact ht.2
    exact pow_le_one₀ (abs_nonneg t) this
  have hi2 : IntervalIntegrable e volume 0 1 := by
    refine (intervalIntegrable_const (c := 1)).mono_fun' hmeasE.aestronglyMeasurable ?_
    filter_upwards with t using hbE t
  have hsplit : ∫ t in (0 : ℝ)..1, F' t =
      3 * (∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ 2 * e t) - 2 * Complex.I * β * kerB β := by
    have : (fun t : ℝ => F' t) = fun t : ℝ => 3 * (((t : ℝ) : ℂ) ^ 2 * e t) - (2 * Complex.I * β) * e t := by
      funext t; simp only [hF']; ring
    rw [this, intervalIntegral.integral_sub (hi1.const_mul 3) (hi2.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    rfl
  rw [hsplit, hF1, hF0, sub_zero] at hftc
  have hA : ‖∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ 2 * e t‖ ≤ 1 / 3 := by
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (zero_le_one) (g := fun t : ℝ => t ^ 2)
      (f := fun t : ℝ => ((t : ℝ) : ℂ) ^ 2 * e t)
      (Eventually.of_forall fun t ht => by
        rw [norm_mul, hnorm, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs])
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
    rw [integral_pow] at this
    norm_num at this
    exact this
  have hK : 2 * |β| * ‖kerB β‖ ≤ 2 := by
    have h1 : 2 * Complex.I * (β : ℂ) * kerB β = 3 * (∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ 2 * e t) - e 1 := by
      linear_combination -hftc
    have h2 : ‖2 * Complex.I * (β : ℂ) * kerB β‖ = 2 * |β| * ‖kerB β‖ := by
      simp [norm_mul, Complex.norm_real]
    rw [← h2, h1]
    calc ‖3 * (∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ 2 * e t) - e 1‖
        ≤ ‖3 * (∫ t in (0 : ℝ)..1, ((t : ℝ) : ℂ) ^ 2 * e t)‖ + ‖e 1‖ := norm_sub_le _ _
      _ ≤ 3 * (1 / 3) + 1 := by
          rw [norm_mul, hnorm]
          have : ‖(3 : ℂ)‖ = 3 := by simp
          rw [this]
          nlinarith only [hA]
      _ = 2 := by norm_num
  have hβpos : 0 < |β| := abs_pos.mpr hβ
  rw [le_div_iff₀ hβpos]
  nlinarith only [hK]

/-- `|K_β| ≤ 2/(1+|β|)`. -/
lemma norm_kerB_le (β : ℝ) : ‖kerB β‖ ≤ 2 / (1 + |β|) := by
  have hpos : 0 < 1 + |β| := by positivity
  rw [le_div_iff₀ hpos]
  by_cases h : |β| ≤ 1
  · have := norm_kerB_le_one β
    nlinarith only [this, h, abs_nonneg β, norm_nonneg (kerB β)]
  · have hβ : β ≠ 0 := by intro h0; rw [h0] at h; simp at h
    have h1 := norm_kerB_le_inv hβ
    have hβpos : 0 < |β| := abs_pos.mpr hβ
    rw [le_div_iff₀ hβpos] at h1
    nlinarith only [h1, not_le.mp h, norm_nonneg (kerB β)]

/-- `K(Y) = ∫₀¹ e^{iλY²/(2t²)} dt`. -/
noncomputable def kerK (lam Y : ℝ) : ℂ := kerB (lam * Y ^ 2 / 2)

lemma kerK_eq (lam Y : ℝ) :
    kerK lam Y = ∫ t in Ioc (0 : ℝ) 1, Complex.exp (Complex.I * (lam : ℂ) * (Y : ℂ) ^ 2 / (2 * (t : ℂ) ^ 2)) := by
  unfold kerK kerB
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  congr 1
  by_cases ht : (t : ℂ) = 0
  · simp [ht]
  · push_cast; field_simp

lemma norm_kerK_le (lam Y : ℝ) : ‖kerK lam Y‖ ≤ 2 / (1 + |lam| * Y ^ 2 / 2) := by
  have h := norm_kerB_le (lam * Y ^ 2 / 2)
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg Y)] at h
  unfold kerK
  simpa [abs_two] using h

section Fubini

variable {k : ℝ → ℂ}

/-- The oscillatory factor. -/
noncomputable def osc (lam : ℝ) (X : ℝ) : ℂ := Complex.exp (Complex.I * (lam : ℂ) * (X : ℂ) ^ 2 / 2)

lemma norm_osc (lam X : ℝ) : ‖osc lam X‖ = 1 := by
  unfold osc
  have : Complex.I * (lam : ℂ) * (X : ℂ) ^ 2 / 2 = Complex.I * ((lam * X ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]; exact norm_cexp_I_mul _

lemma continuous_osc (lam : ℝ) : Continuous (osc lam) := by unfold osc; fun_prop

/-- Scaling: `∫ t k(tX) e^{iλX²/2} dX = ∫ k(Y) e^{iλY²/(2t²)} dY` for `t > 0`. -/
lemma scaling_step {t : ℝ} (ht : 0 < t) (lam : ℝ) :
    ∫ X : ℝ, (t : ℂ) * k (t * X) * osc lam X =
      ∫ Y : ℝ, k Y * Complex.exp (Complex.I * (lam : ℂ) * (Y : ℂ) ^ 2 / (2 * (t : ℂ) ^ 2)) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  set g : ℝ → ℂ := fun Y => k Y * Complex.exp (Complex.I * (lam : ℂ) * (Y : ℂ) ^ 2 / (2 * (t : ℂ) ^ 2)) with hg
  have h1 : ∀ X : ℝ, (t : ℂ) * k (t * X) * osc lam X = (t : ℂ) * g (t * X) := by
    intro X
    simp only [hg, osc]
    have e : Complex.I * (lam : ℂ) * ((t * X : ℝ) : ℂ) ^ 2 / (2 * (t : ℂ) ^ 2) =
        Complex.I * (lam : ℂ) * (X : ℂ) ^ 2 / 2 := by
      push_cast; field_simp
    rw [e]; ring
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_mul_left g t, abs_inv, abs_of_pos ht, Complex.real_smul]
  push_cast
  field_simp

/-- **Fubini identity**: `∫ (∫₀¹ t k(tX) dt) e^{iλX²/2} dX = ∫ k(Y) K(Y) dY`. -/
theorem hadamard_fubini (hk : Continuous k) (hki : Integrable k) (lam : ℝ) :
    ∫ X : ℝ, (∫ t in (0 : ℝ)..1, (t : ℂ) * k (t * X)) * osc lam X = ∫ Y : ℝ, k Y * kerK lam Y := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  set fA : ℝ → ℝ → ℂ := fun X t => (t : ℂ) * k (t * X) * osc lam X with hfA
  set fB : ℝ → ℝ → ℂ := fun t Y => k Y * Complex.exp (Complex.I * (lam : ℂ) * (Y : ℂ) ^ 2 / (2 * (t : ℂ) ^ 2)) with hfB
  set L : ℝ := ∫ Y, ‖k Y‖ with hL
  -- integrability for the first swap
  have hAmeas : AEStronglyMeasurable (Function.uncurry fA) (volume.prod ν) := by
    have : Continuous (Function.uncurry fA) := by
      have h1 : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) := Complex.continuous_ofReal.comp continuous_snd
      have h2 : Continuous fun p : ℝ × ℝ => k (p.2 * p.1) := hk.comp (continuous_snd.mul continuous_fst)
      have h3 : Continuous fun p : ℝ × ℝ => osc lam p.1 := (continuous_osc lam).comp continuous_fst
      exact (h1.mul h2).mul h3
    exact this.aestronglyMeasurable
  have hA : Integrable (Function.uncurry fA) (volume.prod ν) := by
    refine (integrable_prod_iff' hAmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hmaj : Integrable fun X : ℝ => t * ‖k (t * X)‖ := ((hki.norm).comp_mul_left' ht.1.ne').const_mul t
      refine hmaj.mono' ?_ (Eventually.of_forall fun X => ?_)
      · have h1 := hk
        have h2 := continuous_osc lam
        have : Continuous fun X : ℝ => (t : ℂ) * k (t * X) * osc lam X := by fun_prop
        exact this.aestronglyMeasurable
      · show ‖(t : ℂ) * k (t * X) * osc lam X‖ ≤ t * ‖k (t * X)‖
        rw [norm_mul, norm_mul, norm_osc, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    · have hconst : (fun t : ℝ => ∫ X : ℝ, ‖fA X t‖) =ᵐ[ν] fun _ => L := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [hfA, norm_mul, norm_osc, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        rw [integral_const_mul]
        have := Measure.integral_comp_mul_left (fun Y : ℝ => ‖k Y‖) t
        rw [this, abs_inv, abs_of_pos ht.1, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht.1.ne', one_mul]
      exact (integrable_const L).congr hconst.symm
  -- integrability for the second swap
  have hBmeas : AEStronglyMeasurable (Function.uncurry fB) (ν.prod volume) := by
    have : Measurable (Function.uncurry fB) := by
      simp only [hfB, Function.uncurry]
      have := hk.measurable
      fun_prop
    exact this.aestronglyMeasurable
  have hB : Integrable (Function.uncurry fB) (ν.prod volume) := by
    have hmaj : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * ‖k z.2‖) (ν.prod volume) :=
      Integrable.mul_prod (integrable_const 1) hki.norm
    refine hmaj.mono' hBmeas (Eventually.of_forall fun z => ?_)
    simp only [hfB, Function.uncurry, norm_mul, one_mul]
    have : ‖Complex.exp (Complex.I * (lam : ℂ) * (z.2 : ℂ) ^ 2 / (2 * (z.1 : ℂ) ^ 2))‖ = 1 := by
      have : Complex.I * (lam : ℂ) * (z.2 : ℂ) ^ 2 / (2 * (z.1 : ℂ) ^ 2) =
          Complex.I * ((lam * z.2 ^ 2 / (2 * z.1 ^ 2) : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact norm_cexp_I_mul _
    rw [this, mul_one]
  calc ∫ X : ℝ, (∫ t in (0 : ℝ)..1, (t : ℂ) * k (t * X)) * osc lam X
      = ∫ X : ℝ, (∫ t, fA X t ∂ν) := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        show (∫ t in (0 : ℝ)..1, (t : ℂ) * k (t * X)) * osc lam X = ∫ t, fA X t ∂ν
        rw [intervalIntegral.integral_of_le zero_le_one, ← integral_mul_const]
    _ = ∫ t, (∫ X : ℝ, fA X t) ∂ν := integral_integral_swap hA
    _ = ∫ t, (∫ Y : ℝ, fB t Y) ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact scaling_step ht.1 lam
    _ = ∫ Y : ℝ, (∫ t, fB t Y ∂ν) := integral_integral_swap hB
    _ = ∫ Y : ℝ, k Y * kerK lam Y := by
        refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
        simp only [hfB]
        rw [integral_const_mul, kerK_eq]

/-- **Base case of the Morse expansion** (`ct:morse-expansion`, `r = 1`): for `k` continuous, integrable, `|k| ≤ M`,
`|∫ (∫₀¹ t k(tX) dt) e^{iλX²/2} dX| ≤ 2√2 π M / √|λ|`. -/
theorem hadamard_bound (hk : Continuous k) (hki : Integrable k) {M : ℝ} (hM : ∀ x, ‖k x‖ ≤ M) {lam : ℝ}
    (hlam : lam ≠ 0) :
    ‖∫ X : ℝ, (∫ t in (0 : ℝ)..1, (t : ℂ) * k (t * X)) * osc lam X‖ ≤
      2 * Real.sqrt 2 * π * M / Real.sqrt |lam| := by
  rw [hadamard_fubini hk hki lam]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hlam' : 0 < |lam| := abs_pos.mpr hlam
  set b : ℝ := Real.sqrt (|lam| / 2) with hb
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hb2 : b ^ 2 = |lam| / 2 := Real.sq_sqrt (by positivity)
  have hint : Integrable fun Y : ℝ => (2 * M) * (1 + (b * Y) ^ 2)⁻¹ :=
    (integrable_inv_one_add_mul_sq hbpos.ne').const_mul _
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun Y => ?_)).trans ?_
  · rw [norm_mul]
    have h1 := norm_kerK_le lam Y
    have e : 2 / (1 + |lam| * Y ^ 2 / 2) = 2 * (1 + (b * Y) ^ 2)⁻¹ := by
      rw [mul_pow, hb2]; field_simp
    calc ‖k Y‖ * ‖kerK lam Y‖ ≤ M * (2 * (1 + (b * Y) ^ 2)⁻¹) := by
          rw [← e]
          exact mul_le_mul (hM Y) h1 (norm_nonneg _) hM0
      _ = (2 * M) * (1 + (b * Y) ^ 2)⁻¹ := by ring
  · rw [integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos hbpos]
    have : b = Real.sqrt |lam| / Real.sqrt 2 := by rw [hb, Real.sqrt_div (abs_nonneg _)]
    rw [this]
    have h2 : 0 < Real.sqrt 2 := by positivity
    have h3 : 0 < Real.sqrt |lam| := Real.sqrt_pos.mpr hlam'
    field_simp
    exact le_rfl

/-- info: 'FormalResearch.SignUncertainty.CtMorse.hadamard_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hadamard_bound

end Fubini

end FormalResearch.SignUncertainty.CtMorse
