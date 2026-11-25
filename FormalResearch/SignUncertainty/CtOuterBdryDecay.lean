module

public import FormalResearch.SignUncertainty.CtOuterBdryEst

/-!
# Decay of the boundary functional

**Proved.**  If `b` is differentiable with `|b(t)|, |b'(t)| ≤ A (1+|t|) e^{-π|t|}`, then
`|F_b(τ)| ≤ C A (1+τ)² e^{-πτ}` for `τ ≥ 1`, with `C` absolute.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- Local mean-value bound near `τ ≥ 1`. -/
lemma near_shift {b b' : ℝ → ℝ} (hd : ∀ t, HasDerivAt b (b' t) t) {A : ℝ}
    (hb' : ∀ t, |b' t| ≤ A * ((1 + |t|) * Real.exp (-π * |t|))) {τ : ℝ} (hτ : 1 ≤ τ) {s : ℝ} (hs : |s| ≤ 1) :
    |b (τ + s) - b τ| ≤ (2 * A * Real.exp π * ((1 + τ) * Real.exp (-π * τ))) * |s| := by
  have hA : 0 ≤ A := by
    have := hb' 0
    simp at this
    exact (abs_nonneg _).trans this
  have hd' : ∀ x : ℝ, HasDerivAt (fun x : ℝ => b (τ + x)) (b' (τ + x)) x := fun x =>
    ((hd (τ + x)).comp x ((hasDerivAt_id x).const_add τ)).congr_deriv (by simp)
  have := abs_sub_le_of_deriv hd' (r := |s|) (K := 2 * A * Real.exp π * ((1 + τ) * Real.exp (-π * τ))) (x := s)
    (fun y hy => ?_) le_rfl
  · simpa using this
  · have hy1 : |y| ≤ 1 := (abs_le.mpr ⟨hy.1, hy.2⟩).trans hs
    have hy2 := abs_le.mp hy1
    have hx0 : 0 ≤ τ + y := by linarith
    refine (hb' (τ + y)).trans ?_
    rw [abs_of_nonneg hx0]
    have e1 : Real.exp (-π * (τ + y)) ≤ Real.exp π * Real.exp (-π * τ) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [Real.pi_pos, hy2.1]
    have e2 : 1 + (τ + y) ≤ 2 * (1 + τ) := by linarith
    have hE := (Real.exp_pos (-π * (τ + y))).le
    calc A * ((1 + (τ + y)) * Real.exp (-π * (τ + y))) ≤ A * ((2 * (1 + τ)) * (Real.exp π * Real.exp (-π * τ))) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact mul_le_mul e2 e1 hE (by positivity)
      _ = _ := by ring

theorem bdryF_decay : ∃ C : ℝ, ∀ {b b' : ℝ → ℝ} {A : ℝ}, (∀ t, HasDerivAt b (b' t) t) →
    (∀ t, |b t| ≤ A * ((1 + |t|) * Real.exp (-π * |t|))) → (∀ t, |b' t| ≤ A * ((1 + |t|) * Real.exp (-π * |t|))) →
    ∀ τ : ℝ, 1 ≤ τ → |bdryF b τ| ≤ C * A * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
  obtain ⟨C0, hC0⟩ := convJ_integral_le
  set cE : ℝ := ∫ s : ℝ, Real.exp (-π * |s|) with hcE
  have hcE0 : 0 ≤ cE := integral_nonneg (fun s => (Real.exp_pos _).le)
  have hC00 : 0 ≤ C0 := by
    have h1 := hC0 0 le_rfl
    have h2 : 0 ≤ ∫ s : ℝ, convJ 0 s := integral_nonneg (fun s => convJ_nonneg 0 s)
    by_contra hneg
    rw [not_le] at hneg
    simp at h1
    linarith
  refine ⟨4 * Real.exp π / π + 4 * C0 + 4 * cE, fun {b b'} {A} hd hb hb' τ hτ => ?_⟩
  have hA : 0 ≤ A := by
    have := hb 0
    simp at this
    exact (abs_nonneg _).trans this
  have hτ0 : 0 ≤ τ := by linarith
  set M1 : ℝ := 2 * A * Real.exp π / π * ((1 + τ) * Real.exp (-π * τ)) with hM1
  have hM10 : 0 ≤ M1 := by rw [hM1]; positivity
  have i1 : Integrable fun s : ℝ => M1 * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s :=
    ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).const_mul _
  have i2 : Integrable fun s : ℝ => (4 * A) * convJ τ s := (integrable_convJ τ hτ0).const_mul _
  have i3 : Integrable fun s : ℝ => (4 * |b τ|) * Real.exp (-π * |s|) :=
    (integrable_exp_neg_abs' Real.pi_pos).const_mul _
  have hg := (i1.add i2).add i3
  rw [bdryF_eq_shift]
  have hmain : ‖∫ s : ℝ, (b (τ + s) - b τ) / Real.sinh (π * s)‖ ≤
      ∫ s : ℝ, (M1 * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s + (4 * A) * convJ τ s +
        (4 * |b τ|) * Real.exp (-π * |s|)) := by
    refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs]
    have hE := (Real.exp_pos (-π * |s|)).le
    have hcj := convJ_nonneg τ s
    have hind : 0 ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s := indicator_nonneg (fun _ _ => zero_le_one) s
    have hbτ := abs_nonneg (b τ)
    by_cases hs : |s| ≤ 1
    · have hmem : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
      rw [indicator_of_mem hmem]
      by_cases h0 : s = 0
      · subst h0; simp
        positivity
      have h1 := near_shift hd hb' hτ hs
      have h2 := abs_div_sinh_le_near h0
      have hpos : 0 < |Real.sinh (π * s)| := by
        rw [abs_sinh_pi]; exact Real.sinh_pos_iff.mpr (by have := abs_pos.mpr h0; positivity)
      rw [abs_div]
      have hB0 : 0 ≤ 2 * A * Real.exp π * ((1 + τ) * Real.exp (-π * τ)) := by positivity
      calc |b (τ + s) - b τ| / |Real.sinh (π * s)|
          ≤ ((2 * A * Real.exp π * ((1 + τ) * Real.exp (-π * τ))) * |s|) / |Real.sinh (π * s)| :=
            div_le_div_of_nonneg_right h1 hpos.le
        _ = (2 * A * Real.exp π * ((1 + τ) * Real.exp (-π * τ))) * (|s| / |Real.sinh (π * s)|) := by ring
        _ ≤ (2 * A * Real.exp π * ((1 + τ) * Real.exp (-π * τ))) * (1 / π) := mul_le_mul_of_nonneg_left h2 hB0
        _ = M1 * 1 := by rw [hM1]; field_simp
        _ ≤ M1 * 1 + 4 * A * convJ τ s + 4 * |b τ| * Real.exp (-π * |s|) := by
            have : 0 ≤ 4 * A * convJ τ s := by positivity
            have : 0 ≤ 4 * |b τ| * Real.exp (-π * |s|) := by positivity
            linarith
    · have hfar := abs_inv_sinh_le_far (not_le.mp hs).le
      have hmem : s ∉ Icc (-1 : ℝ) 1 := fun h => hs (abs_le.mpr ⟨h.1, h.2⟩)
      rw [indicator_of_notMem hmem, mul_zero, zero_add]
      rw [abs_div]
      have hpos : 0 < |Real.sinh (π * s)| := by
        rw [abs_sinh_pi]; exact Real.sinh_pos_iff.mpr (by have := lt_trans one_pos (not_le.mp hs); positivity)
      have hsplit : |b (τ + s) - b τ| ≤ |b (τ + s)| + |b τ| := abs_sub _ _
      calc |b (τ + s) - b τ| / |Real.sinh (π * s)|
          ≤ (|b (τ + s)| + |b τ|) * (1 / |Real.sinh (π * s)|) := by
            rw [← div_eq_mul_one_div]; exact div_le_div_of_nonneg_right hsplit hpos.le
        _ ≤ (A * ((1 + |τ + s|) * Real.exp (-π * |τ + s|)) + |b τ|) * (4 * Real.exp (-π * |s|)) :=
            mul_le_mul (add_le_add (hb _) le_rfl) hfar (by positivity) (by positivity)
        _ = 4 * A * convJ τ s + 4 * |b τ| * Real.exp (-π * |s|) := by unfold convJ; ring
        _ = _ := by rfl
  have i12 : Integrable fun s : ℝ => M1 * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s + (4 * A) * convJ τ s :=
    i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator_const _ measurableSet_Icc] at hmain
  have hvol : (volume : Measure ℝ).real (Icc (-1 : ℝ) 1) = 2 := by
    rw [Measure.real, Real.volume_Icc]; norm_num
  rw [hvol, ← hcE] at hmain
  rw [Real.norm_eq_abs] at hmain
  refine hmain.trans ?_
  have hJ := hC0 τ hτ0
  have hbτ : |b τ| ≤ A * ((1 + τ) * Real.exp (-π * τ)) := by
    have := hb τ
    rwa [abs_of_nonneg hτ0] at this
  have hE := (Real.exp_pos (-π * τ)).le
  have hY : (1 + τ) * Real.exp (-π * τ) ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by
    apply mul_le_mul_of_nonneg_right _ hE; nlinarith only [hτ0]
  have hX : 0 ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by positivity
  have t1 : M1 * ((2 : ℝ) • (1 : ℝ)) ≤ 2 * (2 * Real.exp π / π) * (A * ((1 + τ) ^ 2 * Real.exp (-π * τ))) := by
    have : M1 * ((2 : ℝ) • (1 : ℝ)) = 2 * (2 * Real.exp π / π) * (A * ((1 + τ) * Real.exp (-π * τ))) := by
      rw [hM1]; simp; ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hY hA
  have t2 : 4 * A * ∫ s : ℝ, convJ τ s ≤ 4 * A * (C0 * ((1 + τ) ^ 2 * Real.exp (-π * τ))) := by
    apply mul_le_mul_of_nonneg_left hJ (by positivity)
  have t3 : 4 * |b τ| * cE ≤ 4 * cE * (A * ((1 + τ) ^ 2 * Real.exp (-π * τ))) := by
    have : 4 * |b τ| * cE = 4 * cE * |b τ| := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hbτ.trans (mul_le_mul_of_nonneg_left hY hA)
  calc _ ≤ 2 * (2 * Real.exp π / π) * (A * ((1 + τ) ^ 2 * Real.exp (-π * τ))) +
        4 * A * (C0 * ((1 + τ) ^ 2 * Real.exp (-π * τ))) + 4 * cE * (A * ((1 + τ) ^ 2 * Real.exp (-π * τ))) := by
          linarith only [t1, t2, t3]
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.bdryF_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bdryF_decay

end FormalResearch.SignUncertainty.CtOuter
