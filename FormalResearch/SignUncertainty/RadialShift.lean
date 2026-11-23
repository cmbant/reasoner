module

public import FormalResearch.SignUncertainty.RadialXiEntire

/-!
# Contour independence of the line integral (`lem:radial-compactness`, Step 4)

For `W` holomorphic and bounded on `Re w > 0`, `u ↦ ∫ limInt W u v s dv` is constant on `u > 0`
(`limInt_integral_shift`): Cauchy on the rectangle `[u₁,u₂] × [-V,V]` and Gaussian decay of the
horizontal sides as `V → ∞`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped Real Interval

namespace FormalResearch.SignUncertainty

/-- The integrand as a function of `w`. -/
noncomputable def gfun (W : ℂ → ℂ) (s w : ℂ) : ℂ :=
  Complex.exp ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3 + (Real.pi ^ 2 : ℂ) * s * w) * W w

lemma limInt_eq_gfun (W : ℂ → ℂ) (u v : ℝ) (s : ℂ) :
    limInt W u v s = gfun W s ((u : ℂ) + (v : ℂ) * Complex.I) := rfl

lemma continuous_limInt_line {W : ℂ → ℂ} (hWd : DifferentiableOn ℂ W {w | 0 < w.re}) {u : ℝ}
    (hu : 0 < u) (s : ℂ) : Continuous fun v : ℝ => limInt W u v s := by
  unfold limInt
  have hl : Continuous fun v : ℝ => (((u : ℝ) : ℂ) + (v : ℂ) * Complex.I) := by fun_prop
  refine Continuous.mul (by fun_prop) ?_
  exact hWd.continuousOn.comp_continuous hl (fun v => by simpa using hu)

lemma norm_limInt_le_gauss {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀) {u : ℝ}
    (hu : 0 < u) (v : ℝ) (s : ℂ) :
    ‖limInt W u v s‖ ≤ M₀ * Real.exp (Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u) *
      Real.exp (-(Real.pi ^ 2 * u / 12) * v ^ 2 + (-(Real.pi ^ 2 * s.im)) * v) := by
  refine (norm_limInt_le hW hu v s).trans (le_of_eq ?_)
  rw [mul_assoc M₀, ← Real.exp_add]; congr 2; ring

lemma integrable_limInt_line {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀)
    (hWd : DifferentiableOn ℂ W {w | 0 < w.re}) {u : ℝ} (hu : 0 < u) (s : ℂ) :
    Integrable fun v : ℝ => limInt W u v s := by
  have hc : 0 < Real.pi ^ 2 * u / 12 := by positivity
  have := (gauss_lin_integrable (d := -(Real.pi ^ 2 * s.im)) hc).const_mul
    (M₀ * Real.exp (Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u))
  exact this.mono' (continuous_limInt_line hWd hu s).aestronglyMeasurable
    (ae_of_all _ fun v => norm_limInt_le_gauss hW hu v s)

lemma horiz_bound {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀) {m Mx x : ℝ}
    (hm : 0 < m) (hx : x ∈ Icc m Mx) (v : ℝ) (s : ℂ) :
    ‖limInt W x v s‖ ≤ M₀ * Real.exp (Real.pi ^ 2 * Mx ^ 3 / 36 + Real.pi ^ 2 * |s.re| * Mx) *
      Real.exp (-(Real.pi ^ 2 * m / 12) * v ^ 2 + Real.pi ^ 2 * |s.im| * |v|) := by
  obtain ⟨hmx, hxM⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le hm hmx
  have hM0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hW 1 (by simp))
  refine (norm_limInt_le hW hx0 v s).trans ?_
  rw [mul_assoc M₀, ← Real.exp_add]
  gcongr
  have p2 := sq_nonneg Real.pi
  have h1 : x ^ 3 ≤ Mx ^ 3 := pow_le_pow_left₀ hx0.le hxM 3
  have h2 : s.re * x ≤ |s.re| * Mx :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hx0.le).trans
      (mul_le_mul_of_nonneg_left hxM (abs_nonneg _))
  have h3 : -s.im * v ≤ |s.im| * |v| := by
    calc -s.im * v ≤ |-s.im * v| := le_abs_self _
      _ = |s.im| * |v| := by rw [abs_mul, abs_neg]
  have h4 : x * v ^ 2 ≥ m * v ^ 2 := mul_le_mul_of_nonneg_right hmx (sq_nonneg v)
  nlinarith [mul_le_mul_of_nonneg_left h1 p2, mul_le_mul_of_nonneg_left h2 p2,
    mul_le_mul_of_nonneg_left h3 p2, mul_le_mul_of_nonneg_left h4 p2]

lemma tendsto_gauss_zero {c d : ℝ} (hc : 0 < c) :
    Tendsto (fun V : ℝ => Real.exp (-c * V ^ 2 + d * V)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have h : Tendsto (fun V : ℝ => c * V ^ 2 - d * V) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop ((d + 1) / c), eventually_ge_atTop 0] with V h1 h2
    have : c * V ≥ d + 1 := by
      have := (div_le_iff₀ hc).mp h1; linarith
    simp only [id]; nlinarith
  have := tendsto_neg_atTop_atBot.comp h
  refine this.congr (fun V => ?_)
  simp only [Function.comp]; ring

theorem limInt_integral_shift {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀)
    (hWd : DifferentiableOn ℂ W {w | 0 < w.re}) {u₁ u₂ : ℝ} (h₁ : 0 < u₁) (h₂ : 0 < u₂) (s : ℂ) :
    ∫ v : ℝ, limInt W u₂ v s = ∫ v : ℝ, limInt W u₁ v s := by
  set m := min u₁ u₂ with hmdef
  set Mx := max u₁ u₂ with hMdef
  have hm : 0 < m := lt_min h₁ h₂
  have hdiff : DifferentiableOn ℂ (gfun W s) {w | 0 < w.re} := by
    unfold gfun
    refine DifferentiableOn.mul (Differentiable.differentiableOn (by fun_prop)) hWd
  -- rectangle relation
  have rect : ∀ V : ℝ, (∫ x : ℝ in u₁..u₂, limInt W x (-V) s) - (∫ x : ℝ in u₁..u₂, limInt W x V s) +
      Complex.I • (∫ y : ℝ in (-V)..V, limInt W u₂ y s) -
      Complex.I • (∫ y : ℝ in (-V)..V, limInt W u₁ y s) = 0 := by
    intro V
    have H : DifferentiableOn ℂ (gfun W s)
        ([[(⟨u₁, -V⟩ : ℂ).re, (⟨u₂, V⟩ : ℂ).re]] ×ℂ [[(⟨u₁, -V⟩ : ℂ).im, (⟨u₂, V⟩ : ℂ).im]]) := by
      refine hdiff.mono ?_
      intro w hw
      have : w.re ∈ [[u₁, u₂]] := hw.1
      rw [Set.mem_uIcc] at this
      show 0 < w.re
      rcases this with ⟨a, _⟩ | ⟨a, _⟩ <;> linarith
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (gfun W s) ⟨u₁, -V⟩ ⟨u₂, V⟩ H
    exact this
  have hI₂ := intervalIntegral_tendsto_integral (integrable_limInt_line hW hWd h₂ s)
    (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot) tendsto_id
  have hI₁ := intervalIntegral_tendsto_integral (integrable_limInt_line hW hWd h₁ s)
    (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot) tendsto_id
  have hc : 0 < Real.pi ^ 2 * m / 12 := by positivity
  set K := M₀ * Real.exp (Real.pi ^ 2 * Mx ^ 3 / 36 + Real.pi ^ 2 * |s.re| * Mx) with hK
  have hhor : ∀ e : ℝ, |e| = 1 → Tendsto (fun V : ℝ => ∫ x : ℝ in u₁..u₂, limInt W x (e * V) s) atTop (𝓝 0) := by
    intro e he
    have hg := tendsto_gauss_zero (c := Real.pi ^ 2 * m / 12) (d := Real.pi ^ 2 * |s.im|) hc
    have hg' := (hg.const_mul (K * |u₂ - u₁|))
    rw [mul_zero] at hg'
    refine squeeze_zero_norm' ?_ hg'
    filter_upwards [eventually_ge_atTop 0] with V hV
    have hb : ∀ x ∈ Ι u₁ u₂, ‖limInt W x (e * V) s‖ ≤ K * Real.exp (-(Real.pi ^ 2 * m / 12) * V ^ 2 +
        Real.pi ^ 2 * |s.im| * V) := by
      intro x hx
      have hxI : x ∈ Icc m Mx := by
        exact Set.uIoc_subset_uIcc hx
      have := horiz_bound hW hm hxI (e * V) s
      have h1 : |e * V| = V := by rw [abs_mul, he, one_mul, abs_of_nonneg hV]
      have h2 : (e * V) ^ 2 = V ^ 2 := by
        have : e ^ 2 = 1 := by rw [← sq_abs, he]; norm_num
        rw [mul_pow, this, one_mul]
      rw [h1, h2] at this
      exact this
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    calc ‖∫ x : ℝ in u₁..u₂, limInt W x (e * V) s‖
        ≤ K * Real.exp (-(Real.pi ^ 2 * m / 12) * V ^ 2 + Real.pi ^ 2 * |s.im| * V) * |u₂ - u₁| := this
      _ = _ := by ring
  have h3 := hhor (-1) (by simp)
  have h4 := hhor 1 (by simp)
  have hlim : Tendsto (fun V : ℝ => (∫ x : ℝ in u₁..u₂, limInt W x (-V) s) - (∫ x : ℝ in u₁..u₂, limInt W x V s)
      + Complex.I • (∫ y : ℝ in (-V)..V, limInt W u₂ y s) -
      Complex.I • (∫ y : ℝ in (-V)..V, limInt W u₁ y s)) atTop
      (𝓝 (0 - 0 + Complex.I • (∫ v : ℝ, limInt W u₂ v s) - Complex.I • (∫ v : ℝ, limInt W u₁ v s))) := by
    refine (((h3.congr (fun V => by simp)).sub (h4.congr (fun V => by simp))).add
      (hI₂.const_smul Complex.I)).sub (hI₁.const_smul Complex.I)
  have h0 : Tendsto (fun V : ℝ => (∫ x : ℝ in u₁..u₂, limInt W x (-V) s) - (∫ x : ℝ in u₁..u₂, limInt W x V s)
      + Complex.I • (∫ y : ℝ in (-V)..V, limInt W u₂ y s) -
      Complex.I • (∫ y : ℝ in (-V)..V, limInt W u₁ y s)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun V => (rect V).symm)
  have := tendsto_nhds_unique hlim h0
  rw [sub_zero, zero_add, sub_eq_zero] at this
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact smul_right_injective ℂ hI this

end FormalResearch.SignUncertainty
