module

public import FormalResearch.SignUncertainty.CtOuterMain

/-!
# `ct:outer` (2): the boundary phase `θ_ε`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Proposition `ct:outer` (2) and eq. `ct:theta-form`.
**Proved** for the structural clauses (the phase identity, oddness, smoothness, holomorphy on `|τ| < 1/2`).

`outerTheta ε τ = Im h̄(iτ) - arctan τ` for `ε = -1` and `Im h̄(iτ) - arctan τ - 2 arctan(tanh(πτ/2))` for `ε = +1`
(`ct:theta-form`), with `h̄ = outerHbar` the boundary extension of `h`.

* `phase_identity`: for `τ > 0`, `G_ε(iτ)(1 - iτ)^{1/2} = √((6/π²) m'(τ)) exp(i(π/4 + θ_ε(τ)))`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The boundary phase `θ_ε(τ)` of `ct:theta-form` (`ε = ±1`). -/
noncomputable def outerTheta (ε : ℝ) (τ : ℝ) : ℝ :=
  (outerHbar (Complex.I * τ)).im - Real.arctan τ -
    (if ε = 1 then 2 * Real.arctan (Real.tanh (π * τ / 2)) else 0)

lemma cpow_half_I_mul {τ : ℝ} (hτ : 0 < τ) :
    (Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt τ : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by
  have hne : Complex.I * (τ : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hτ.ne')
  rw [Complex.cpow_def_of_ne_zero hne, mul_comm Complex.I (τ : ℂ), Complex.log_ofReal_mul hτ Complex.I_ne_zero,
    Complex.log_I]
  rw [show ((Real.log τ : ℝ) + (π : ℂ) / 2 * Complex.I) * (1 / 2) =
      ((Real.log τ / 2 : ℝ) : ℂ) + Complex.I * ((π / 4 : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp]
  congr 2
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hτ]
  congr 1; ring

lemma cpow_half_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  have := Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
  simpa [one_div] using this

lemma one_sub_I_mul_eq {τ : ℝ} :
    1 - Complex.I * (τ : ℂ) = (Real.sqrt (1 + τ ^ 2) : ℂ) * Complex.exp (-(Complex.I * (Real.arctan τ : ℝ))) := by
  have hs : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have e : -(Complex.I * ((Real.arctan τ : ℝ) : ℂ)) = ((-Real.arctan τ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_arctan, Real.sin_arctan]
  have hsC : (Real.sqrt (1 + τ ^ 2) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  ring

lemma exp_eq_re_im (z : ℂ) : Complex.exp z = (Real.exp z.re : ℂ) * Complex.exp (Complex.I * (z.im : ℝ)) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.exp_add, ← Complex.ofReal_exp, mul_comm (z.im : ℂ) Complex.I]

lemma exp_uR_mul {τ : ℝ} (hτ : 0 < τ) :
    Real.sqrt τ * Real.sqrt (1 + τ ^ 2) * Real.exp (uR τ) = Real.sqrt (6 / π ^ 2 * mPrime τ) := by
  have hF := Freal_pos hτ.ne'
  have hexp : Real.exp (uR τ) = Real.sqrt (Freal τ) := by
    rw [uR_eq hτ.ne', Real.sqrt_eq_rpow, Real.rpow_def_of_pos hF]
    congr 1; ring
  rw [hexp, ← Real.sqrt_mul hτ.le, ← Real.sqrt_mul (by positivity)]
  congr 1
  unfold Freal
  have h1 : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hs : Real.sqrt (1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := Real.sq_sqrt h1.le
  have hs0 : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.mpr h1
  field_simp

/-- **`ct:outer` (2), the phase identity.** For `τ > 0`,
`G_ε(iτ)(1 - iτ)^{1/2} = √((6/π²) m'(τ)) e^{i(π/4 + θ_ε(τ))}`. -/
theorem phase_identity {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {τ : ℝ} (hτ : 0 < τ) :
    outerGbar ε (Complex.I * (τ : ℂ)) * (1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (6 / π ^ 2 * mPrime τ) : ℂ) *
        Complex.exp (Complex.I * ((π / 4 + outerTheta ε τ : ℝ) : ℂ)) := by
  have hs0 : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  set X : ℝ := Real.arctan (Real.tanh (π * τ / 2)) with hX
  set hb : ℂ := outerHbar (Complex.I * (τ : ℂ)) with hhb
  have hre : hb.re = uR τ := re_outerHbar_left τ
  -- the common factor
  have hexpsplit : Complex.exp (Complex.I * ((π / 4 + (hb.im - Real.arctan τ) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (π / 4 : ℝ)) * Complex.exp (-(Complex.I * (Real.arctan τ : ℝ))) *
        Complex.exp (Complex.I * (hb.im : ℝ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have hcore : outerGm outerHbar (Complex.I * (τ : ℂ)) * (1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (6 / π ^ 2 * mPrime τ) : ℂ) *
        Complex.exp (Complex.I * ((π / 4 + (hb.im - Real.arctan τ) : ℝ) : ℂ)) := by
    unfold outerGm
    rw [← hhb]
    have e1 : (Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * (1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp hb *
        (1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) =
        (Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ((1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 2 * Complex.exp hb := by ring
    rw [e1, cpow_half_sq, cpow_half_I_mul hτ, exp_eq_re_im hb, hexpsplit]
    nth_rewrite 1 [one_sub_I_mul_eq (τ := τ)]
    rw [hre, ← exp_uR_mul hτ]
    push_cast
    ring
  unfold outerGbar
  rcases hε with rfl | rfl
  · simp only [↓reduceIte]
    rw [mul_assoc, hcore, bHalf_I_mul τ]
    have hθr : (π / 4 + outerTheta 1 τ : ℝ) = (π / 4 + (hb.im - Real.arctan τ)) - 2 * X := by
      simp only [outerTheta, ↓reduceIte, hhb, hX]; ring
    have hexp : Complex.exp (Complex.I * (((π / 4 + (hb.im - Real.arctan τ)) - 2 * X : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((π / 4 + (hb.im - Real.arctan τ) : ℝ) : ℂ)) *
          Complex.exp (-(2 * Complex.I * (X : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hθr, hexp]
    ring
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simp only [hne, ↓reduceIte, one_mul]
    rw [hcore]
    unfold outerTheta
    simp only [hne, ↓reduceIte, sub_zero]
    rfl

end FormalResearch.SignUncertainty.CtOuter
