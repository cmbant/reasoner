module

public import FormalResearch.SignUncertainty.HankelBessel
public import FormalResearch.Special.BesselSeries

/-!
# Calculus of the Hankel kernel in the variable `w = Δ s`

For `c > 0` and `w > 0`: `(φ_c)'(w) = -(4π²/c) φ_{c+1}(w)` (`hasDerivAt_hankelPhi`), the recurrence
`φ_c = φ_{c+1} - 4π² w/(c(c+1)) φ_{c+2}` (`hankelPhi_recurrence`), and the integration-by-parts
identity (`integral_rpow_mul_hankelPhi`)
`∫_0^X w^{c/2-1} φ_c(w) dw = (1/c) X^{c/2} φ_{c+1}(X) + (1/2) ∫_0^X w^{c/2-1} φ_{c+1}(w) dw`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

lemma hankelPhi_succ (c w : ℝ) : hankelPhi (c + 1) w = besselNorm c (4 * π * √w) := by
  unfold hankelPhi; rw [add_sub_cancel_right]

/-- `φ_c'(w) = -(4π²/c) φ_{c+1}(w)` for `w > 0`, `c > 0`. -/
theorem hasDerivAt_hankelPhi {c : ℝ} (hc : 0 < c) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (hankelPhi c) (-(4 * π ^ 2 / c) * hankelPhi (c + 1) w) w := by
  have hs : HasDerivAt (fun w : ℝ => 4 * π * √w) (4 * π * (1 / (2 * √w))) w :=
    (Real.hasDerivAt_sqrt hw.ne').const_mul (4 * π)
  have h := (hasDerivAt_besselNorm (by linarith : -1 < c - 1) (4 * π * √w)).comp w hs
  unfold hankelPhi
  refine h.congr_deriv ?_
  rw [add_sub_cancel_right, sub_add_cancel]
  have hsq : 0 < √w := Real.sqrt_pos.mpr hw
  have : c ≠ 0 := hc.ne'
  have h2 : (√w) ^ 2 = w := Real.sq_sqrt hw.le
  field_simp
  ring

/-- `φ_c = φ_{c+1} - 4π² w/(c(c+1)) φ_{c+2}` for `w ≥ 0`, `c > 0`. -/
theorem hankelPhi_recurrence {c : ℝ} (hc : 0 < c) {w : ℝ} (hw : 0 ≤ w) :
    hankelPhi c w = hankelPhi (c + 1) w - 4 * π ^ 2 * w / (c * (c + 1)) * hankelPhi (c + 2) w := by
  have h := besselNorm_recurrence (by linarith : -1 < c - 1) (4 * π * √w)
  unfold hankelPhi
  rw [show c + 2 - 1 = c - 1 + 2 by ring, show c + 1 - 1 = c - 1 + 1 by ring]
  rw [h]
  have h2 : (√w) ^ 2 = w := Real.sq_sqrt hw
  have h3 : c - 1 + 1 = c := by ring
  have h4 : c - 1 + 2 = c + 1 := by ring
  rw [h3, h4]
  have : c ≠ 0 := hc.ne'
  have : c + 1 ≠ 0 := by linarith
  congr 1
  field_simp
  rw [h2]
  ring


lemma intervalIntegrable_rpow_mul_hankelPhi {c : ℝ} (hc : 0 < c) (c' : ℝ) (X : ℝ) :
    IntervalIntegrable (fun w : ℝ => w ^ (c / 2 - 1) * hankelPhi c' w) volume 0 X :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1)).mul_continuousOn
    (hankelPhi_continuous c').continuousOn

/-- **Integration by parts.** For `c > 0`, `X ≥ 0`:
`∫_0^X w^{c/2-1} φ_c = (1/c) X^{c/2} φ_{c+1}(X) + (1/2) ∫_0^X w^{c/2-1} φ_{c+1}`. -/
theorem integral_rpow_mul_hankelPhi {c : ℝ} (hc : 0 < c) {X : ℝ} (hX : 0 ≤ X) :
    ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi c w =
      (1 / c) * (X ^ (c / 2) * hankelPhi (c + 1) X) +
        (1 / 2) * ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi (c + 1) w := by
  rcases hX.eq_or_lt with rfl | hX0
  · simp [Real.zero_rpow (by positivity : c / 2 ≠ 0)]
  set g : ℝ → ℝ := fun w => w ^ (c / 2) * hankelPhi (c + 1) w with hg
  set g' : ℝ → ℝ := fun w => c * (w ^ (c / 2 - 1) * hankelPhi c w) -
    (c / 2) * (w ^ (c / 2 - 1) * hankelPhi (c + 1) w) with hg'
  have hcont : ContinuousOn g (Icc 0 X) :=
    ((Real.continuous_rpow_const (by positivity : 0 ≤ c / 2)).mul
      (hankelPhi_continuous (c + 1))).continuousOn
  have hderiv : ∀ w ∈ Ioo 0 X, HasDerivAt g (g' w) w := by
    intro w hw
    have hw0 : 0 < w := hw.1
    have h1 := (Real.hasDerivAt_rpow_const (x := w) (p := c / 2) (Or.inl hw0.ne')).mul
      (hasDerivAt_hankelPhi (by linarith : 0 < c + 1) hw0)
    refine h1.congr_deriv ?_
    have hrec := hankelPhi_recurrence hc hw0.le
    have hw1 : w ^ (c / 2) = w ^ (c / 2 - 1) * w := by
      rw [Real.rpow_sub_one hw0.ne']; field_simp
    simp only [hg']
    rw [hrec, hw1]
    have : c ≠ 0 := hc.ne'
    have : c + 1 ≠ 0 := by linarith
    field_simp
    ring_nf
  have hint : IntervalIntegrable g' volume 0 X :=
    ((intervalIntegrable_rpow_mul_hankelPhi hc c X).const_mul c).sub
      ((intervalIntegrable_rpow_mul_hankelPhi hc (c + 1) X).const_mul (c / 2))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX0.le hcont hderiv hint
  have hg0 : g 0 = 0 := by simp [hg, Real.zero_rpow (by positivity : c / 2 ≠ 0)]
  rw [hg0, sub_zero] at hftc
  simp only [hg'] at hftc
  rw [intervalIntegral.integral_sub ((intervalIntegrable_rpow_mul_hankelPhi hc c X).const_mul c)
    ((intervalIntegrable_rpow_mul_hankelPhi hc (c + 1) X).const_mul (c / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hX0.le, intervalIntegral.integral_of_le hX0.le] at hftc
  simp only [hg] at hftc
  have hcne : c ≠ 0 := hc.ne'
  generalize ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi c w = A at *
  generalize ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi (c + 1) w = B at *
  generalize X ^ (c / 2) * hankelPhi (c + 1) X = T at *
  field_simp
  linarith

end FormalResearch.SignUncertainty
