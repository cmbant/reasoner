module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Contour shift between two vertical lines

A function continuous on a closed vertical strip, holomorphic inside, and dominated there by an
integrable `g(Im w)` with `g → 0` at `±∞`, has the same integral over the two boundary lines
(`strip_shift`): Cauchy on the rectangle `[a, b] × [-V, V]`, and the horizontal sides vanish as `V → ∞`.
This is the shift used in the proof of `u1co:O5`(1) (`I_main` to `Re w = 1`).

Status: proved, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped Real Interval

namespace FormalResearch.CohnElkies

theorem strip_shift {H : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn H {w : ℂ | a ≤ w.re ∧ w.re ≤ b})
    (hd : DifferentiableOn ℂ H {w : ℂ | a < w.re ∧ w.re < b}) {g : ℝ → ℝ} (hg : Integrable g)
    (hbd : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖H w‖ ≤ g w.im)
    (hg_top : Tendsto g atTop (𝓝 0)) (hg_bot : Tendsto g atBot (𝓝 0)) :
    ∫ v : ℝ, H ((b : ℂ) + (v : ℂ) * Complex.I) = ∫ v : ℝ, H ((a : ℂ) + (v : ℂ) * Complex.I) := by
  have hline : ∀ x : ℝ, a ≤ x → x ≤ b → Continuous fun v : ℝ => H ((x : ℂ) + (v : ℂ) * Complex.I) := fun x h1 h2 => by
    have : Continuous fun v : ℝ => ((x : ℂ) + (v : ℂ) * Complex.I) := by fun_prop
    exact hc.comp_continuous this fun v => by simpa using ⟨h1, h2⟩
  have hint : ∀ x : ℝ, a ≤ x → x ≤ b → Integrable fun v : ℝ => H ((x : ℂ) + (v : ℂ) * Complex.I) := fun x h1 h2 =>
    hg.mono' (hline x h1 h2).aestronglyMeasurable (ae_of_all _ fun v => by
      have := hbd ((x : ℂ) + (v : ℂ) * Complex.I) (by simpa using h1) (by simpa using h2)
      simpa using this)
  have rect : ∀ V : ℝ, (∫ x : ℝ in a..b, H ((x : ℂ) + (-V : ℝ) * Complex.I)) -
      (∫ x : ℝ in a..b, H ((x : ℂ) + (V : ℝ) * Complex.I)) +
      Complex.I • (∫ y : ℝ in (-V)..V, H ((b : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y : ℝ in (-V)..V, H ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro V
    have hV : -V ≤ V ∨ V < -V := le_or_gt _ _
    have H1 : ContinuousOn H ([[(⟨a, -V⟩ : ℂ).re, (⟨b, V⟩ : ℂ).re]] ×ℂ [[(⟨a, -V⟩ : ℂ).im, (⟨b, V⟩ : ℂ).im]]) := by
      refine hc.mono ?_
      intro w hw
      have : w.re ∈ [[a, b]] := hw.1
      rw [Set.uIcc_of_le hab] at this
      exact this
    have H2 : DifferentiableOn ℂ H (Ioo (min (⟨a, -V⟩ : ℂ).re (⟨b, V⟩ : ℂ).re) (max (⟨a, -V⟩ : ℂ).re (⟨b, V⟩ : ℂ).re) ×ℂ
        Ioo (min (⟨a, -V⟩ : ℂ).im (⟨b, V⟩ : ℂ).im) (max (⟨a, -V⟩ : ℂ).im (⟨b, V⟩ : ℂ).im)) := by
      refine hd.mono ?_
      intro w hw
      have h1 := hw.1
      simp only [min_eq_left hab, max_eq_right hab] at h1
      exact h1
    exact Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn H ⟨a, -V⟩ ⟨b, V⟩ H1 H2
  have hI₁ := intervalIntegral_tendsto_integral (hint a le_rfl hab)
    (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot) tendsto_id
  have hI₂ := intervalIntegral_tendsto_integral (hint b hab le_rfl)
    (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot) tendsto_id
  have hhor : ∀ e : ℝ, (Tendsto (fun V : ℝ => g (e * V)) atTop (𝓝 0)) →
      Tendsto (fun V : ℝ => ∫ x : ℝ in a..b, H ((x : ℂ) + ((e * V : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    intro e he
    have hg' := he.const_mul (b - a)
    rw [mul_zero] at hg'
    refine squeeze_zero_norm' ?_ hg'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
    have hb : ∀ x ∈ Ι a b, ‖H ((x : ℂ) + ((e * V : ℝ) : ℂ) * Complex.I)‖ ≤ g (e * V) := fun x hx => by
      have hx' : x ∈ Icc a b := by rw [uIoc_of_le hab] at hx; exact Ioc_subset_Icc_self hx
      have := hbd ((x : ℂ) + ((e * V : ℝ) : ℂ) * Complex.I) (by simpa using hx'.1) (by simpa using hx'.2)
      simpa using this
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) hb
    calc _ ≤ g (e * V) * |b - a| := this
      _ = (b - a) * g (e * V) := by rw [abs_of_nonneg (by linarith)]; ring
  have h3 := hhor (-1) ((hg_bot.comp (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot)).congr (fun V => by simp))
  have h4 := hhor 1 (hg_top.congr (fun V => by simp))
  have hlim : Tendsto (fun V : ℝ => (∫ x : ℝ in a..b, H ((x : ℂ) + (-V : ℝ) * Complex.I)) -
      (∫ x : ℝ in a..b, H ((x : ℂ) + (V : ℝ) * Complex.I)) +
      Complex.I • (∫ y : ℝ in (-V)..V, H ((b : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y : ℝ in (-V)..V, H ((a : ℂ) + (y : ℂ) * Complex.I))) atTop
      (𝓝 (0 - 0 + Complex.I • (∫ v : ℝ, H ((b : ℂ) + (v : ℂ) * Complex.I)) -
        Complex.I • (∫ v : ℝ, H ((a : ℂ) + (v : ℂ) * Complex.I)))) := by
    refine (((h3.congr (fun V => by simp)).sub (h4.congr (fun V => by simp))).add
      (hI₂.const_smul Complex.I)).sub (hI₁.const_smul Complex.I)
  have h0 : Tendsto (fun V : ℝ => (∫ x : ℝ in a..b, H ((x : ℂ) + (-V : ℝ) * Complex.I)) -
      (∫ x : ℝ in a..b, H ((x : ℂ) + (V : ℝ) * Complex.I)) +
      Complex.I • (∫ y : ℝ in (-V)..V, H ((b : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y : ℝ in (-V)..V, H ((a : ℂ) + (y : ℂ) * Complex.I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun V => (rect V).symm)
  have := tendsto_nhds_unique hlim h0
  rw [sub_zero, zero_add, sub_eq_zero] at this
  exact smul_right_injective ℂ Complex.I_ne_zero this

/-- info: 'FormalResearch.CohnElkies.strip_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms strip_shift

end FormalResearch.CohnElkies
