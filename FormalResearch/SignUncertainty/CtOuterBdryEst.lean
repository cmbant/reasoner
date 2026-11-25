module

public import FormalResearch.SignUncertainty.CtOuterBdryDeriv

/-!
# Decay estimate for the boundary functional

**Proved.**  If `|b(t)|, |b'(t)| ≤ A (1+|t|) e^{-π|t|}`, then `|F_b(τ)| ≤ C A (1+τ²) e^{-πτ}` for `τ ≥ 1`
(`C` absolute): near part by the mean-value theorem, far part by a convolution estimate
`∫ (1+|t|) e^{-π|t|} e^{-π|t-τ|} dt ≲ (1+τ)² e^{-πτ}`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The convolution integrand `(1+|τ+s|) e^{-π|τ+s|} e^{-π|s|}`. -/
noncomputable def convJ (τ s : ℝ) : ℝ := (1 + |τ + s|) * Real.exp (-π * |τ + s|) * Real.exp (-π * |s|)

lemma convJ_nonneg (τ s : ℝ) : 0 ≤ convJ τ s := by unfold convJ; positivity

lemma integrable_poly_exp2 : Integrable fun s : ℝ => (1 + |s|) * Real.exp (-(2 * π) * |s|) := by
  have h := (integrable_exp_neg_abs' (c := 2 * π) (by positivity)).add (integrable_abs_exp (c := 2 * π) (by positivity))
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply]; ring

lemma convJ_le (τ : ℝ) (hτ : 0 ≤ τ) (s : ℝ) :
    convJ τ s ≤ Real.exp (-π * τ) * ((1 + τ) * (Icc (-τ) 0).indicator (fun _ => (1 : ℝ)) s +
      (1 + τ) * ((1 + |s|) * Real.exp (-(2 * π) * |s|)) + (1 + |s + τ|) * Real.exp (-(2 * π) * |s + τ|)) := by
  unfold convJ
  have hE : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos x).le
  have hpi := Real.pi_pos
  have hI : 0 ≤ (Icc (-τ) 0).indicator (fun _ => (1 : ℝ)) s := indicator_nonneg (fun _ _ => zero_le_one) s
  have h2 : 0 ≤ (1 + τ) * ((1 + |s|) * Real.exp (-(2 * π) * |s|)) := by positivity
  have h3 : 0 ≤ (1 + |s + τ|) * Real.exp (-(2 * π) * |s + τ|) := by positivity
  have hm : 0 ≤ (1 + τ) * (Icc (-τ) 0).indicator (fun _ => (1 : ℝ)) s := by positivity
  have hE0 := hE (-π * τ)
  rcases le_or_gt 0 s with hs | hs
  · have h1 : |τ + s| = τ + s := abs_of_nonneg (by linarith)
    have h4 : |s| = s := abs_of_nonneg hs
    rw [h1, h4]
    have e : Real.exp (-π * (τ + s)) * Real.exp (-π * s) = Real.exp (-π * τ) * Real.exp (-(2 * π) * s) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hEs : 0 ≤ Real.exp (-(2 * π) * s) := hE _
    have hle : (1 + τ + s) * Real.exp (-(2 * π) * s) ≤ (1 + τ) * ((1 + s) * Real.exp (-(2 * π) * s)) := by
      nlinarith only [mul_nonneg (mul_nonneg hτ hs) hEs]
    calc (1 + (τ + s)) * Real.exp (-π * (τ + s)) * Real.exp (-π * s)
        = Real.exp (-π * τ) * ((1 + τ + s) * Real.exp (-(2 * π) * s)) := by rw [mul_assoc, e]; ring
      _ ≤ Real.exp (-π * τ) * ((1 + τ) * ((1 + s) * Real.exp (-(2 * π) * s))) :=
          mul_le_mul_of_nonneg_left hle hE0
      _ ≤ _ := by
          rw [h4] at h2
          nlinarith only [mul_nonneg hE0 hm, mul_nonneg hE0 h3, h2, hE0]
  · rcases le_or_gt (-τ) s with hs2 | hs2
    · have h1 : |τ + s| = τ + s := abs_of_nonneg (by linarith)
      have h4 : |s| = -s := abs_of_neg hs
      rw [h1, h4]
      have hmem : s ∈ Icc (-τ) 0 := ⟨hs2, hs.le⟩
      rw [indicator_of_mem hmem]
      have e : Real.exp (-π * (τ + s)) * Real.exp (-π * -s) = Real.exp (-π * τ) := by
        rw [← Real.exp_add]; ring_nf
      calc (1 + (τ + s)) * Real.exp (-π * (τ + s)) * Real.exp (-π * -s)
          = (1 + (τ + s)) * Real.exp (-π * τ) := by rw [mul_assoc, e]
        _ ≤ Real.exp (-π * τ) * ((1 + τ) * 1) := by nlinarith only [hE0, hs]
        _ ≤ _ := by
            rw [h4] at h2
            nlinarith only [mul_nonneg hE0 h2, mul_nonneg hE0 h3, hE0]
    · have h1 : |τ + s| = -(τ + s) := abs_of_neg (by linarith)
      have h4 : |s| = -s := abs_of_neg hs
      have h5 : |s + τ| = -(τ + s) := by rw [add_comm]; exact h1
      rw [h1, h4]
      have hnm : s ∉ Icc (-τ) 0 := fun h => by linarith [h.1]
      rw [indicator_of_notMem hnm] at hm ⊢
      rw [h5] at h3 ⊢
      have e : Real.exp (-π * -(τ + s)) * Real.exp (-π * -s) = Real.exp (-π * τ) * Real.exp (-(2 * π) * -(τ + s)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      calc (1 + -(τ + s)) * Real.exp (-π * -(τ + s)) * Real.exp (-π * -s)
          = Real.exp (-π * τ) * ((1 + -(τ + s)) * Real.exp (-(2 * π) * -(τ + s))) := by
            rw [mul_assoc, e]; ring
        _ ≤ _ := by
            have hnn : 0 ≤ (1 + τ) * ((1 + -s) * Real.exp (-(2 * π) * -s)) := by rw [h4] at h2; exact h2
            nlinarith only [mul_nonneg hE0 hnn, hE0, hm]


lemma integrable_convJ (τ : ℝ) (hτ : 0 ≤ τ) : Integrable (convJ τ) := by
  set P : ℝ → ℝ := fun s => (1 + |s|) * Real.exp (-(2 * π) * |s|) with hP
  have h1 : Integrable fun s : ℝ => (1 + τ) * (Icc (-τ) 0).indicator (fun _ => (1 : ℝ)) s :=
    ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).const_mul _
  have h2 : Integrable fun s : ℝ => (1 + τ) * P s := integrable_poly_exp2.const_mul _
  have h3 : Integrable fun s : ℝ => P (s + τ) := integrable_poly_exp2.comp_add_right τ
  have h := ((h1.add h2).add h3).const_mul (Real.exp (-π * τ))
  refine Integrable.mono' h ?_ (Eventually.of_forall fun s => ?_)
  · have : Continuous (convJ τ) := by unfold convJ; fun_prop
    exact this.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (convJ_nonneg τ s)]
    exact (convJ_le τ hτ s).trans (le_of_eq (by simp only [Pi.add_apply, hP]))

/-- **Convolution estimate**: `∫ (1+|t|) e^{-π|t|} e^{-π|t-τ|} dt ≲ (1+τ)² e^{-πτ}`. -/
theorem convJ_integral_le : ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∫ s : ℝ, convJ τ s ≤ C * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
  set P : ℝ → ℝ := fun s => (1 + |s|) * Real.exp (-(2 * π) * |s|) with hP
  set cP : ℝ := ∫ s : ℝ, P s with hcP
  have hcP0 : 0 ≤ cP := integral_nonneg (fun s => by simp only [hP]; positivity)
  refine ⟨1 + 2 * cP, fun τ hτ => ?_⟩
  have h1 : Integrable fun s : ℝ => (1 + τ) * (Icc (-τ) 0).indicator (fun _ => (1 : ℝ)) s :=
    ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).const_mul _
  have h2 : Integrable fun s : ℝ => (1 + τ) * P s := integrable_poly_exp2.const_mul _
  have h3 : Integrable fun s : ℝ => P (s + τ) := integrable_poly_exp2.comp_add_right τ
  have hmaj := ((h1.add h2).add h3).const_mul (Real.exp (-π * τ))
  have hle : ∫ s : ℝ, convJ τ s ≤ ∫ s : ℝ, Real.exp (-π * τ) *
      ((1 + τ) * (Icc (-τ) 0).indicator (fun _ => (1 : ℝ)) s + (1 + τ) * P s + P (s + τ)) :=
    integral_mono_of_nonneg (Eventually.of_forall fun s => convJ_nonneg τ s) hmaj
      (Eventually.of_forall fun s => convJ_le τ hτ s)
  refine hle.trans ?_
  have i12 : Integrable fun s : ℝ => (1 + τ) * (Icc (-τ) 0).indicator (fun _ => (1 : ℝ)) s + (1 + τ) * P s :=
    h1.add h2
  rw [integral_const_mul, integral_add i12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_indicator_const _ measurableSet_Icc]
  have hvol : (volume : Measure ℝ).real (Icc (-τ) 0) = τ := by
    rw [Measure.real, Real.volume_Icc]; simp [hτ]
  have hshift : ∫ s : ℝ, P (s + τ) = cP := integral_add_right_eq_self P τ
  rw [hvol, hshift]
  have hE := (Real.exp_pos (-π * τ)).le
  have e1 : (1 + τ) * (τ • (1 : ℝ)) = (1 + τ) * τ := by simp
  rw [e1]
  have hτ2 : (1 + τ) * τ ≤ (1 + τ) ^ 2 := by nlinarith only [hτ]
  have hc1 : (1 + τ) * cP ≤ (1 + τ) ^ 2 * cP := by
    apply mul_le_mul_of_nonneg_right _ hcP0; nlinarith only [hτ]
  have hc2 : cP ≤ (1 + τ) ^ 2 * cP := by
    have : (1 : ℝ) ≤ (1 + τ) ^ 2 := by nlinarith only [hτ]
    nlinarith only [this, hcP0]
  calc Real.exp (-π * τ) * ((1 + τ) * τ + (1 + τ) * cP + cP) ≤
      Real.exp (-π * τ) * ((1 + τ) ^ 2 + (1 + τ) ^ 2 * cP + (1 + τ) ^ 2 * cP) := by
        apply mul_le_mul_of_nonneg_left _ hE; linarith
    _ = (1 + 2 * cP) * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by ring

/-- info: 'FormalResearch.SignUncertainty.CtOuter.convJ_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convJ_integral_le

end FormalResearch.SignUncertainty.CtOuter
