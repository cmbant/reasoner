module

public import FormalResearch.SignUncertainty.BinetVertical
public import FormalResearch.SignUncertainty.CtChartTaylor

/-!
# Complex small-argument bound for the shifted Binet remainder (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (Binet factor, `ct:binet-small`, used on the contour
where `τ = T(s;a)` is complex).  **Proved.**  For `c > 0` and complex `|ζ| ≤ 1/2`: `|B_c(ζ)| ≤ 4|ζ|/c`, hence
`|e^{-B_c(ζ)} - 1| ≤ 8|ζ|/c` for `c ≥ 2`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty.BinetDecay

lemma norm_one_sub_ge {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 / 2 ≤ ‖1 - (t : ℂ) * ζ‖ := by
  have h1 : ‖(t : ℂ) * ζ‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg ζ, ht.2]
  have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * ζ)
  rw [norm_one] at this
  linarith [norm_sub_norm_le (1 : ℂ) ((t : ℂ) * ζ)]

lemma re_pos_c_one_sub {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < ((c : ℂ) * (1 - (t : ℂ) * ζ)).re := by
  have h1 : ‖(t : ℂ) * ζ‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg ζ, ht.2]
  have h2 : |((t : ℂ) * ζ).re| ≤ 1 / 2 := (Complex.abs_re_le_norm _).trans h1
  have : ((c : ℂ) * (1 - (t : ℂ) * ζ)).re = c * (1 - ((t : ℂ) * ζ).re) := by simp
  rw [this]
  exact mul_pos hc (by linarith [(abs_le.mp h2).2])

theorem norm_binetDiff_complex_le {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖binetDiff c ζ‖ ≤ 4 * ‖ζ‖ / c := by
  unfold binetDiff
  have hT := CtChart.taylor1_seg (p := binetRem) (p1 := deriv binetRem) (z := (c : ℂ) * (1 - ζ)) (β := (c : ℂ))
    (fun t ht => by
      have hre : 0 < ((c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ))).re := by
        have := re_pos_c_one_sub hc hζ ht
        have e : (c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ)) = (c : ℂ) * (1 - (t : ℂ) * ζ) := by ring
        rw [e]; exact this
      exact ((binetRem_differentiableOn _ hre).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre)).hasDerivAt)
    (by
      have hcont : ContinuousOn (deriv binetRem) {w : ℂ | 0 < w.re} :=
        (analyticOnNhd_binetRem.deriv).continuousOn
      have hcc : ContinuousOn (fun t : ℝ => (c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ))) (Icc 0 1) := by fun_prop
      refine hcont.comp hcc (fun t ht => ?_)
      have := re_pos_c_one_sub hc hζ ht
      have e : (c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ)) = (c : ℂ) * (1 - (t : ℂ) * ζ) := by ring
      simpa [e] using this)
  rw [hT, norm_mul]
  have hz : ‖(c : ℂ) * (1 - ζ) - (c : ℂ)‖ = c * ‖ζ‖ := by
    have : (c : ℂ) * (1 - ζ) - (c : ℂ) = -((c : ℂ) * ζ) := by ring
    rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [hz]
  have hint : ‖∫ t in (0 : ℝ)..1, deriv binetRem ((c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ)))‖ ≤ 4 / c ^ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun t : ℝ => deriv binetRem ((c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ)))) (C := 4 / c ^ 2) (by
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        have e : (c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ)) = (c : ℂ) * (1 - (t : ℂ) * ζ) := by ring
        rw [e]
        have hre := re_pos_c_one_sub hc hζ ht'
        have hb := binetRem_iteratedDeriv_decay 1 hre
        rw [iteratedDeriv_one] at hb
        have hn : c / 2 ≤ ‖(c : ℂ) * (1 - (t : ℂ) * ζ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
          have := norm_one_sub_ge hζ ht'
          nlinarith
        have hpos : 0 < c / 2 := by positivity
        calc _ ≤ ((1 : ℕ).factorial : ℝ) * 2 ^ (1 + 2) / (8 * ‖(c : ℂ) * (1 - (t : ℂ) * ζ)‖ ^ (1 + 1)) := hb
          _ ≤ ((1 : ℕ).factorial : ℝ) * 2 ^ (1 + 2) / (8 * (c / 2) ^ (1 + 1)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity)
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hn _) (by norm_num))
          _ = 4 / c ^ 2 := by field_simp; norm_num; ring)
    simpa using this
  calc c * ‖ζ‖ * ‖∫ t in (0 : ℝ)..1, deriv binetRem ((c : ℂ) + (t : ℂ) * ((c : ℂ) * (1 - ζ) - (c : ℂ)))‖
      ≤ c * ‖ζ‖ * (4 / c ^ 2) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 4 * ‖ζ‖ / c := by field_simp

/-- For `c ≥ 2`: `|e^{-B_c(ζ)} - 1| ≤ 8|ζ|/c`. -/
theorem norm_exp_neg_binetDiff_sub_one {c : ℝ} (hc : 2 ≤ c) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖Complex.exp (-binetDiff c ζ) - 1‖ ≤ 8 * ‖ζ‖ / c := by
  have hc0 : 0 < c := by linarith
  have hB := norm_binetDiff_complex_le hc0 hζ
  have h1 : ‖-binetDiff c ζ‖ ≤ 1 := by
    rw [norm_neg]
    refine hB.trans ?_
    rw [div_le_one hc0]
    nlinarith [norm_nonneg ζ]
  have h := Complex.norm_exp_sub_one_le h1
  rw [norm_neg] at h
  calc ‖Complex.exp (-binetDiff c ζ) - 1‖ ≤ 2 * ‖binetDiff c ζ‖ := h
    _ ≤ 2 * (4 * ‖ζ‖ / c) := by gcongr
    _ = 8 * ‖ζ‖ / c := by ring

end FormalResearch.SignUncertainty.BinetDecay
