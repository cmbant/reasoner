module

public import Mathlib

/-!
# Shifting a horizontal line integral inside a strip

A generic Cauchy rectangle argument used in the proof of Lemma `SD_H`
(`CFT/modular_bootstrap/paper/edge_transform_sd.tex`, `esd:hankel`: "Cauchy's theorem permits raising
the contour"): if `F` is continuous on the closed strip `y₁ ≤ Im b ≤ y₂`, holomorphic in the open
strip, and `‖F b‖ ≤ G (Re b)` with `G` integrable and tending to `0` at infinity, then
`∫_ℝ F(v + i y₁) dv = ∫_ℝ F(v + i y₂) dv` (`integral_horizontal_shift`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

lemma integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) : Integrable (fun v : ℝ => Real.exp (-c * |v|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have := integrableOn_exp_mul_Iic hc 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Iic
    simp only [mem_Iic] at hv
    rw [abs_of_nonpos hv]; ring_nf
  · have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hv)]

lemma tendsto_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Tendsto (fun v : ℝ => Real.exp (-c * |v|)) (cocompact ℝ) (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have h1 : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
    exact tendsto_norm_cocompact_atTop (E := ℝ)
  exact (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hc)).congr (fun v => by simp)

lemma im_line (v y : ℝ) : ((v : ℂ) + (y : ℂ) * I).im = y := by simp

lemma re_line (v y : ℝ) : ((v : ℂ) + (y : ℂ) * I).re = v := by simp

/-- Shifting a horizontal line integral inside a strip (Cauchy on the rectangle `[-R, R] × [y₁, y₂]`
and `R → ∞`). -/
theorem integral_horizontal_shift {F : ℂ → ℂ} {y₁ y₂ : ℝ} (h12 : y₁ ≤ y₂)
    (hc : ContinuousOn F {b : ℂ | y₁ ≤ b.im ∧ b.im ≤ y₂})
    (hd : DifferentiableOn ℂ F {b : ℂ | y₁ < b.im ∧ b.im < y₂})
    {G : ℝ → ℝ} (hG : Integrable G) (hG0 : Tendsto G (cocompact ℝ) (𝓝 0))
    (hb : ∀ b : ℂ, y₁ ≤ b.im → b.im ≤ y₂ → ‖F b‖ ≤ G b.re) :
    ∫ v : ℝ, F ((v : ℂ) + (y₁ : ℂ) * I) = ∫ v : ℝ, F ((v : ℂ) + (y₂ : ℂ) * I) := by
  -- the lines are integrable
  have hline : ∀ y : ℝ, y₁ ≤ y → y ≤ y₂ → Integrable (fun v : ℝ => F ((v : ℂ) + (y : ℂ) * I)) := by
    intro y hy1 hy2
    have hcont : Continuous fun v : ℝ => F ((v : ℂ) + (y : ℂ) * I) := by
      refine hc.comp_continuous (by fun_prop) fun v => ?_
      show y₁ ≤ _ ∧ _ ≤ y₂
      rw [im_line]
      exact ⟨hy1, hy2⟩
    refine Integrable.mono' hG hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    have := hb ((v : ℂ) + (y : ℂ) * I) (by rw [im_line]; exact hy1) (by rw [im_line]; exact hy2)
    rwa [re_line] at this
  have hrect : ∀ R : ℝ,
      (∫ x in (-R)..R, F ((x : ℂ) + (y₁ : ℂ) * I)) - (∫ x in (-R)..R, F ((x : ℂ) + (y₂ : ℂ) * I)) +
        I * (∫ y in y₁..y₂, F ((R : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in y₁..y₂, F (((-R : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
    intro R
    have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F
      ⟨-R, y₁⟩ ⟨R, y₂⟩
      (hc.mono (by
        intro b hb'
        have := hb'.2
        dsimp only at this
        rw [Set.uIcc_of_le h12] at this
        exact this))
      (hd.mono (by
        intro b hb'
        have := hb'.2
        dsimp only at this
        rw [min_eq_left h12, max_eq_right h12] at this
        exact this))
    simpa using h
  have hGtop : Tendsto G atTop (𝓝 0) := hG0.mono_left atTop_le_cocompact
  have hGbot : Tendsto G atBot (𝓝 0) := hG0.mono_left atBot_le_cocompact
  have hA : Tendsto (fun R : ℝ => ∫ x in (-R)..R, F ((x : ℂ) + (y₁ : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, F ((v : ℂ) + (y₁ : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (hline y₁ le_rfl h12) tendsto_neg_atTop_atBot tendsto_id
  have hB : Tendsto (fun R : ℝ => ∫ x in (-R)..R, F ((x : ℂ) + (y₂ : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, F ((v : ℂ) + (y₂ : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (hline y₂ h12 le_rfl) tendsto_neg_atTop_atBot tendsto_id
  have hside : ∀ x : ℝ, ‖∫ y in y₁..y₂, F ((x : ℂ) + (y : ℂ) * I)‖ ≤ G x * |y₂ - y₁| := by
    intro x
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    rw [Set.uIoc_of_le h12] at hy
    have := hb ((x : ℂ) + (y : ℂ) * I) (by rw [im_line]; exact hy.1.le) (by rw [im_line]; exact hy.2)
    rwa [re_line] at this
  have hS1 : Tendsto (fun R : ℝ => ∫ y in y₁..y₂, F ((R : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hside (by simpa using hGtop.mul_const |y₂ - y₁|)
  have hS2 : Tendsto (fun R : ℝ => ∫ y in y₁..y₂, F (((-R : ℝ) : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun R => hside (-R)) ?_
    simpa using (hGbot.comp tendsto_neg_atTop_atBot).mul_const |y₂ - y₁|
  have hlim := ((hA.sub hB).add (hS1.const_mul I)).sub (hS2.const_mul I)
  have hzero : Tendsto (fun R : ℝ =>
      (∫ x in (-R)..R, F ((x : ℂ) + (y₁ : ℂ) * I)) - (∫ x in (-R)..R, F ((x : ℂ) + (y₂ : ℂ) * I)) +
        I * (∫ y in y₁..y₂, F ((R : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in y₁..y₂, F (((-R : ℝ) : ℂ) + (y : ℂ) * I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun R => (hrect R).symm
  have := tendsto_nhds_unique hlim hzero
  simp only [mul_zero, add_zero, sub_zero] at this
  exact sub_eq_zero.mp this

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.integral_horizontal_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_horizontal_shift

end FormalResearch.ModularBootstrap.Upper.Hankel
