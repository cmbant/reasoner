module

public import Mathlib

/-!
# The midpoint rule with a second-derivative remainder (phase-free)

`midpoint_remainder`: if `f` is `C²`-like on `[c - 1/2, c + 1/2]` (`f' = f1`, `f1' = f2`, `|f2| ≤ B`), then
`|f c - ∫_{c-1/2}^{c+1/2} f| ≤ B/12`.  Proved (the sharp constant is `B/24`; this form comes from two applications of the
mean value inequality).
-/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace FormalResearch.Asymptotics

theorem midpoint_remainder {f f1 f2 : ℝ → ℝ} {c B : ℝ}
    (hf : ∀ t ∈ Icc (c - 1 / 2) (c + 1 / 2), HasDerivAt f (f1 t) t)
    (hf1 : ∀ t ∈ Icc (c - 1 / 2) (c + 1 / 2), HasDerivAt f1 (f2 t) t)
    (hB : ∀ t ∈ Icc (c - 1 / 2) (c + 1 / 2), |f2 t| ≤ B) :
    |f c - ∫ t in (c - 1 / 2)..(c + 1 / 2), f t| ≤ B / 12 := by
  set I : Set ℝ := Icc (c - 1 / 2) (c + 1 / 2) with hI
  have hcI : c ∈ I := ⟨by linarith, by linarith⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB c hcI)
  have hconv : Convex ℝ I := convex_Icc _ _
  -- Step a: |f1 t - f1 c| ≤ B |t - c|
  have stepa : ∀ t ∈ I, |f1 t - f1 c| ≤ B * |t - c| := by
    intro t ht
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f1) (f' := f2) (C := B)
      (fun x hx => (hf1 x hx).hasDerivWithinAt) (fun x hx => by simpa using hB x hx) hcI ht
    simpa [Real.norm_eq_abs] using this
  -- Step b: Taylor remainder
  set R : ℝ → ℝ := fun t => f t - f c - f1 c * (t - c) with hR
  have hRd : ∀ t ∈ I, HasDerivAt R (f1 t - f1 c) t := by
    intro t ht
    have := ((hf t ht).sub_const (f c)).sub (((hasDerivAt_id t).sub_const c).const_mul (f1 c))
    refine this.congr_deriv ?_
    simp
  have stepb : ∀ t ∈ I, |R t| ≤ B * (t - c) ^ 2 := by
    intro t ht
    have hseg : uIcc c t ⊆ I := uIcc_subset_Icc hcI ht
    have := (convex_uIcc c t).norm_image_sub_le_of_norm_hasDerivWithin_le (f := R)
      (f' := fun x => f1 x - f1 c) (C := B * |t - c|)
      (fun x hx => (hRd x (hseg hx)).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        refine (stepa x (hseg hx)).trans ?_
        apply mul_le_mul_of_nonneg_left _ hB0
        have := Set.abs_sub_left_of_mem_uIcc hx
        exact this)
      (left_mem_uIcc) (right_mem_uIcc)
    have hRc : R c = 0 := by simp [hR]
    rw [hRc, Real.norm_eq_abs] at this
    simpa [Real.norm_eq_abs, sq, mul_assoc, abs_mul_abs_self] using this
  -- integrals
  have hfc : ContinuousOn f I := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume (c - 1 / 2) (c + 1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le (by linarith)]
  have hRi : IntervalIntegrable R volume (c - 1 / 2) (c + 1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    intro t ht
    exact (hRd t ht).continuousAt.continuousWithinAt
  have hint : ∫ t in (c - 1 / 2)..(c + 1 / 2), R t = (∫ t in (c - 1 / 2)..(c + 1 / 2), f t) - f c := by
    have h1 : ∫ t in (c - 1 / 2)..(c + 1 / 2), R t =
        (∫ t in (c - 1 / 2)..(c + 1 / 2), (f t - f c)) - ∫ t in (c - 1 / 2)..(c + 1 / 2), f1 c * (t - c) := by
      rw [← integral_sub (hfi.sub (intervalIntegrable_const)) ((intervalIntegral.intervalIntegrable_id.sub
        intervalIntegrable_const).const_mul _)]
    rw [h1, integral_sub hfi intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_sub
      intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
    simp [integral_id]
    ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (a := c - 1 / 2) (b := c + 1 / 2)
    (μ := volume) (f := R) (g := fun t => B * (t - c) ^ 2) (by linarith)
    (Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs]; exact stepb t ⟨ht.1.le, ht.2⟩))
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hval : ∫ t in (c - 1 / 2)..(c + 1 / 2), B * (t - c) ^ 2 = B / 12 := by
    rw [intervalIntegral.integral_const_mul]
    have : ∫ t in (c - 1 / 2)..(c + 1 / 2), (t - c) ^ 2 = 1 / 12 := by
      rw [intervalIntegral.integral_comp_sub_right (fun t => t ^ 2)]
      simp [integral_pow]
      norm_num
    rw [this]; ring
  rw [hval, hint, Real.norm_eq_abs] at hbound
  rw [abs_sub_comm]
  exact hbound

/-- info: 'FormalResearch.Asymptotics.midpoint_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms midpoint_remainder

end FormalResearch.Asymptotics
