module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Integration by parts for oscillatory integrals `∫ B e^{iλϕ}` (non-stationary phase)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (the "double integration by parts" pieces).  **Proved.**

For real `ϕ` with `ϕ' ≠ 0` on `[a,b]` and complex `B`:
`∫ B e^{iλϕ} = (iλ)⁻¹[B/ϕ' e^{iλϕ}] - (iλ)⁻¹ ∫ (B/ϕ')' e^{iλϕ}` (`ibp_once`), and twice
(`ibp_twice`): the error is `λ⁻¹ Σ |B/ϕ'| + λ⁻² Σ |(B/ϕ')'/ϕ'| + λ⁻² ∫ |Q|` with
`Q = B''/ϕ'² - 3B'ϕ''/ϕ'³ - Bϕ'''/ϕ'³ + 3Bϕ''²/ϕ'⁴`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOsc

/-- One integration by parts against `e^{iλϕ}`. -/
lemma ibp_once {a b lam : ℝ} (hab : a ≤ b) (hlam : lam ≠ 0)
    {ϕ ϕ1 ϕ2 : ℝ → ℝ} {h h1 : ℝ → ℂ}
    (hϕ : ∀ x ∈ Icc a b, HasDerivAt ϕ (ϕ1 x) x) (hϕ1 : ∀ x ∈ Icc a b, HasDerivAt ϕ1 (ϕ2 x) x)
    (hne : ∀ x ∈ Icc a b, ϕ1 x ≠ 0) (hh : ∀ x ∈ Icc a b, HasDerivAt h (h1 x) x)
    (hc1 : ContinuousOn h1 (Icc a b)) (hc2 : ContinuousOn ϕ2 (Icc a b)) :
    ∫ x in a..b, h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
      (1 / (Complex.I * lam)) * (h b / (ϕ1 b : ℂ) * Complex.exp (Complex.I * lam * (ϕ b : ℂ)) -
          h a / (ϕ1 a : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ))) -
        (1 / (Complex.I * lam)) * ∫ x in a..b,
          ((h1 x * (ϕ1 x : ℂ) - h x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2) * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := by
  have hlamC : (Complex.I * (lam : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hlam)
  have hF : ∀ x ∈ Icc a b, HasDerivAt (fun y => h y / (ϕ1 y : ℂ) * Complex.exp (Complex.I * lam * (ϕ y : ℂ)))
      (((h1 x * (ϕ1 x : ℂ) - h x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2) * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) +
        Complex.I * lam * (h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)))) x := by
    intro x hx
    have hne' : (ϕ1 x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    have h1' : HasDerivAt (fun y => (ϕ1 y : ℂ)) (ϕ2 x : ℂ) x := (hϕ1 x hx).ofReal_comp
    have h2' : HasDerivAt (fun y => h y / (ϕ1 y : ℂ)) ((h1 x * (ϕ1 x : ℂ) - h x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2) x :=
      (hh x hx).div h1' hne'
    have h3 : HasDerivAt (fun y => Complex.exp (Complex.I * lam * (ϕ y : ℂ)))
        (Complex.exp (Complex.I * lam * (ϕ x : ℂ)) * (Complex.I * lam * (ϕ1 x : ℂ))) x := by
      have := ((hϕ x hx).ofReal_comp.const_mul (Complex.I * lam)).cexp
      exact this
    have := h2'.mul h3
    refine this.congr_deriv ?_
    field_simp
  -- continuity of the pieces
  have hcont_h : ContinuousOn h (Icc a b) := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  have hcont_ϕ : ContinuousOn ϕ (Icc a b) := fun x hx => (hϕ x hx).continuousAt.continuousWithinAt
  have hcont_ϕ1 : ContinuousOn ϕ1 (Icc a b) := fun x hx => (hϕ1 x hx).continuousAt.continuousWithinAt
  have hcexp : ContinuousOn (fun x => Complex.exp (Complex.I * lam * (ϕ x : ℂ))) (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont_ϕ))
  have hϕ1C : ContinuousOn (fun x => (ϕ1 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hcont_ϕ1
  have hϕ2C : ContinuousOn (fun x => (ϕ2 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hc2
  have hneC : ∀ x ∈ Icc a b, (ϕ1 x : ℂ) ^ 2 ≠ 0 := fun x hx => pow_ne_zero 2 (by exact_mod_cast hne x hx)
  have hG : ContinuousOn (fun x => ((h1 x * (ϕ1 x : ℂ) - h x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2) *
      Complex.exp (Complex.I * lam * (ϕ x : ℂ))) (Icc a b) :=
    ((((hc1.mul hϕ1C).sub (hcont_h.mul hϕ2C)).div (hϕ1C.pow 2) hneC).mul hcexp)
  have hH : ContinuousOn (fun x => Complex.I * lam * (h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)))) (Icc a b) :=
    continuousOn_const.mul (hcont_h.mul hcexp)
  have hFtc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun y => h y / (ϕ1 y : ℂ) * Complex.exp (Complex.I * lam * (ϕ y : ℂ)))
    (f' := fun x => ((h1 x * (ϕ1 x : ℂ) - h x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2) * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) +
        Complex.I * lam * (h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))))
    (by rw [uIcc_of_le hab]; exact hF) ((hG.add hH).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_add (hG.intervalIntegrable_of_Icc hab) (hH.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_const_mul] at hFtc
  have e : ∀ X Y Z : ℂ, X - Y = Z + (Complex.I * lam) * ∫ x in a..b, h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) →
      ∫ x in a..b, h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) = 1 / (Complex.I * lam) * (X - Y) - 1 / (Complex.I * lam) * Z := by
    intro X Y Z hXYZ
    have h1 : (Complex.I * lam) * ∫ x in a..b, h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) = X - Y - Z := by
      linear_combination -hXYZ
    calc ∫ x in a..b, h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))
        = (Complex.I * lam)⁻¹ * ((Complex.I * lam) * ∫ x in a..b, h x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))) :=
          (inv_mul_cancel_left₀ hlamC _).symm
      _ = _ := by rw [h1]; field_simp
  exact e _ _ _ hFtc.symm

/-- `(B/ϕ')' = (B'ϕ' - Bϕ'')/ϕ'²`. -/
noncomputable def ibpH (B B1 : ℝ → ℂ) (ϕ1 ϕ2 : ℝ → ℝ) (x : ℝ) : ℂ :=
  (B1 x * (ϕ1 x : ℂ) - B x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2

/-- The second-order integrand `Q = B''/ϕ'² - 3B'ϕ''/ϕ'^3 - Bϕ^(3)/ϕ'^3 + 3Bϕ''²/ϕ'^4`. -/
noncomputable def ibpQ (B B1 B2 : ℝ → ℂ) (ϕ1 ϕ2 ϕ3 : ℝ → ℝ) (x : ℝ) : ℂ :=
  B2 x / (ϕ1 x : ℂ) ^ 2 - 3 * B1 x * (ϕ2 x : ℂ) / (ϕ1 x : ℂ) ^ 3 - B x * (ϕ3 x : ℂ) / (ϕ1 x : ℂ) ^ 3 +
    3 * B x * (ϕ2 x : ℂ) ^ 2 / (ϕ1 x : ℂ) ^ 4

/-- Two integrations by parts. -/
lemma ibp_twice {a b lam : ℝ} (hab : a ≤ b) (hlam : lam ≠ 0)
    {ϕ ϕ1 ϕ2 ϕ3 : ℝ → ℝ} {B B1 B2 : ℝ → ℂ}
    (hϕ : ∀ x ∈ Icc a b, HasDerivAt ϕ (ϕ1 x) x) (hϕ1 : ∀ x ∈ Icc a b, HasDerivAt ϕ1 (ϕ2 x) x)
    (hϕ2 : ∀ x ∈ Icc a b, HasDerivAt ϕ2 (ϕ3 x) x) (hne : ∀ x ∈ Icc a b, ϕ1 x ≠ 0)
    (hB : ∀ x ∈ Icc a b, HasDerivAt B (B1 x) x) (hB1 : ∀ x ∈ Icc a b, HasDerivAt B1 (B2 x) x)
    (hc2 : ContinuousOn B2 (Icc a b)) (hc3 : ContinuousOn ϕ3 (Icc a b)) :
    ∫ x in a..b, B x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
      (1 / (Complex.I * lam)) * (B b / (ϕ1 b : ℂ) * Complex.exp (Complex.I * lam * (ϕ b : ℂ)) -
          B a / (ϕ1 a : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ))) -
        (1 / (Complex.I * lam)) ^ 2 * (ibpH B B1 ϕ1 ϕ2 b / (ϕ1 b : ℂ) * Complex.exp (Complex.I * lam * (ϕ b : ℂ)) -
          ibpH B B1 ϕ1 ϕ2 a / (ϕ1 a : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ))) +
        (1 / (Complex.I * lam)) ^ 2 * ∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := by
  have hcB1 : ContinuousOn B1 (Icc a b) := fun x hx => (hB1 x hx).continuousAt.continuousWithinAt
  have hcB : ContinuousOn B (Icc a b) := fun x hx => (hB x hx).continuousAt.continuousWithinAt
  have hcϕ1 : ContinuousOn ϕ1 (Icc a b) := fun x hx => (hϕ1 x hx).continuousAt.continuousWithinAt
  have hcϕ2 : ContinuousOn ϕ2 (Icc a b) := fun x hx => (hϕ2 x hx).continuousAt.continuousWithinAt
  have h1 := ibp_once hab hlam hϕ hϕ1 hne hB (fun x hx => hcB1 x hx) hcϕ2
  -- derivative of `ibpH`
  have hH : ∀ x ∈ Icc a b, HasDerivAt (ibpH B B1 ϕ1 ϕ2)
      (B2 x / (ϕ1 x : ℂ) - 2 * B1 x * (ϕ2 x : ℂ) / (ϕ1 x : ℂ) ^ 2 - B x * (ϕ3 x : ℂ) / (ϕ1 x : ℂ) ^ 2 +
        2 * B x * (ϕ2 x : ℂ) ^ 2 / (ϕ1 x : ℂ) ^ 3) x := by
    intro x hx
    have hne' : (ϕ1 x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    have e1 : HasDerivAt (fun y => (ϕ1 y : ℂ)) (ϕ2 x : ℂ) x := (hϕ1 x hx).ofReal_comp
    have e2 : HasDerivAt (fun y => (ϕ2 y : ℂ)) (ϕ3 x : ℂ) x := (hϕ2 x hx).ofReal_comp
    have num : HasDerivAt (fun y => B1 y * (ϕ1 y : ℂ) - B y * (ϕ2 y : ℂ))
        (B2 x * (ϕ1 x : ℂ) + B1 x * (ϕ2 x : ℂ) - (B1 x * (ϕ2 x : ℂ) + B x * (ϕ3 x : ℂ))) x :=
      ((hB1 x hx).mul e1).sub ((hB x hx).mul e2)
    have := num.div (e1.pow 2) (pow_ne_zero 2 hne')
    unfold ibpH
    refine this.congr_deriv ?_
    norm_num
    field_simp
    ring
  have hϕ1C : ContinuousOn (fun x => (ϕ1 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hcϕ1
  have hϕ2C : ContinuousOn (fun x => (ϕ2 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hcϕ2
  have hϕ3C : ContinuousOn (fun x => (ϕ3 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hc3
  have hnC : ∀ n : ℕ, ∀ x ∈ Icc a b, (ϕ1 x : ℂ) ^ n ≠ 0 := fun n x hx => pow_ne_zero n (by exact_mod_cast hne x hx)
  have hc1' : ContinuousOn (fun x => B2 x / (ϕ1 x : ℂ) - 2 * B1 x * (ϕ2 x : ℂ) / (ϕ1 x : ℂ) ^ 2 -
      B x * (ϕ3 x : ℂ) / (ϕ1 x : ℂ) ^ 2 + 2 * B x * (ϕ2 x : ℂ) ^ 2 / (ϕ1 x : ℂ) ^ 3) (Icc a b) := by
    have n1 : ∀ x ∈ Icc a b, (ϕ1 x : ℂ) ≠ 0 := fun x hx => by exact_mod_cast hne x hx
    refine ((((hc2.div hϕ1C n1).sub (((continuousOn_const.mul hcB1).mul hϕ2C).div (hϕ1C.pow 2) (hnC 2))).sub
      ((hcB.mul hϕ3C).div (hϕ1C.pow 2) (hnC 2))).add ?_)
    exact ((continuousOn_const.mul hcB).mul (hϕ2C.pow 2)).div (hϕ1C.pow 3) (hnC 3)
  have h2 := ibp_once hab hlam hϕ hϕ1 hne hH hc1' hcϕ2
  have hint : ∫ x in a..b, ((B2 x / (ϕ1 x : ℂ) - 2 * B1 x * (ϕ2 x : ℂ) / (ϕ1 x : ℂ) ^ 2 - B x * (ϕ3 x : ℂ) / (ϕ1 x : ℂ) ^ 2 +
        2 * B x * (ϕ2 x : ℂ) ^ 2 / (ϕ1 x : ℂ) ^ 3) * (ϕ1 x : ℂ) - ibpH B B1 ϕ1 ϕ2 x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2 *
        Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
      ∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hab] at hx
    have hne' : (ϕ1 x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    show _ = ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * _
    unfold ibpQ ibpH
    field_simp
    ring
  rw [hint] at h2
  have e2 : ∫ x in a..b, ibpH B B1 ϕ1 ϕ2 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
      ∫ x in a..b, (B1 x * (ϕ1 x : ℂ) - B x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2 * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := rfl
  rw [h1, ← e2, h2]
  ring

lemma norm_cexp_phase (lam y : ℝ) : ‖Complex.exp (Complex.I * lam * (y : ℂ))‖ = 1 := by
  have : Complex.I * (lam : ℂ) * (y : ℂ) = Complex.I * ((lam * y : ℝ) : ℂ) := by push_cast; ring
  rw [this]; exact Complex.norm_exp_I_mul_ofReal _

/-- The bound from two integrations by parts. -/
lemma ibp_twice_bound {a b lam : ℝ} (hab : a ≤ b) (hlam : lam ≠ 0)
    {ϕ ϕ1 ϕ2 ϕ3 : ℝ → ℝ} {B B1 B2 : ℝ → ℂ}
    (hϕ : ∀ x ∈ Icc a b, HasDerivAt ϕ (ϕ1 x) x) (hϕ1 : ∀ x ∈ Icc a b, HasDerivAt ϕ1 (ϕ2 x) x)
    (hϕ2 : ∀ x ∈ Icc a b, HasDerivAt ϕ2 (ϕ3 x) x) (hne : ∀ x ∈ Icc a b, ϕ1 x ≠ 0)
    (hB : ∀ x ∈ Icc a b, HasDerivAt B (B1 x) x) (hB1 : ∀ x ∈ Icc a b, HasDerivAt B1 (B2 x) x)
    (hc2 : ContinuousOn B2 (Icc a b)) (hc3 : ContinuousOn ϕ3 (Icc a b)) :
    ‖∫ x in a..b, B x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))‖ ≤
      (‖B b‖ / |ϕ1 b| + ‖B a‖ / |ϕ1 a|) / |lam| +
      (‖ibpH B B1 ϕ1 ϕ2 b‖ / |ϕ1 b| + ‖ibpH B B1 ϕ1 ϕ2 a‖ / |ϕ1 a|) / lam ^ 2 +
      (∫ x in a..b, ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x‖) / lam ^ 2 := by
  rw [ibp_twice hab hlam hϕ hϕ1 hϕ2 hne hB hB1 hc2 hc3]
  have hc : ‖(1 / (Complex.I * (lam : ℂ)))‖ = 1 / |lam| := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc2' : ‖(1 / (Complex.I * (lam : ℂ))) ^ 2‖ = 1 / lam ^ 2 := by
    rw [norm_pow, hc, div_pow, one_pow, sq_abs]
  have hne1 : (ϕ1 b : ℝ) ≠ 0 := hne b ⟨hab, le_rfl⟩
  have hne2 : (ϕ1 a : ℝ) ≠ 0 := hne a ⟨le_rfl, hab⟩
  set Ea := Complex.exp (Complex.I * lam * (ϕ a : ℂ))
  set Eb := Complex.exp (Complex.I * lam * (ϕ b : ℂ))
  have nEa : ‖Ea‖ = 1 := norm_cexp_phase _ _
  have nEb : ‖Eb‖ = 1 := norm_cexp_phase _ _
  have t1 : ‖B b / (ϕ1 b : ℂ) * Eb - B a / (ϕ1 a : ℂ) * Ea‖ ≤ ‖B b‖ / |ϕ1 b| + ‖B a‖ / |ϕ1 a| := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_div, norm_div, nEa, nEb, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    ring
  have t2 : ‖ibpH B B1 ϕ1 ϕ2 b / (ϕ1 b : ℂ) * Eb - ibpH B B1 ϕ1 ϕ2 a / (ϕ1 a : ℂ) * Ea‖ ≤
      ‖ibpH B B1 ϕ1 ϕ2 b‖ / |ϕ1 b| + ‖ibpH B B1 ϕ1 ϕ2 a‖ / |ϕ1 a| := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_div, norm_div, nEa, nEb, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    ring
  have t3 : ‖∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))‖ ≤
      ∫ x in a..b, ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun x _ => ?_
    show ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))‖ = ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x‖
    rw [norm_mul, norm_cexp_phase, mul_one]
  calc _ ≤ ‖1 / (Complex.I * (lam : ℂ)) * (B b / (ϕ1 b : ℂ) * Eb - B a / (ϕ1 a : ℂ) * Ea)‖ +
        ‖(1 / (Complex.I * (lam : ℂ))) ^ 2 * (ibpH B B1 ϕ1 ϕ2 b / (ϕ1 b : ℂ) * Eb - ibpH B B1 ϕ1 ϕ2 a / (ϕ1 a : ℂ) * Ea)‖ +
        ‖(1 / (Complex.I * (lam : ℂ))) ^ 2 * ∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))‖ := by
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by
        rw [norm_mul, norm_mul, norm_mul, hc, hc2']
        have hl : 0 < |lam| := abs_pos.mpr hlam
        have hl2 : 0 < lam ^ 2 := by positivity
        have a1 : 1 / |lam| * ‖B b / (ϕ1 b : ℂ) * Eb - B a / (ϕ1 a : ℂ) * Ea‖ ≤ (‖B b‖ / |ϕ1 b| + ‖B a‖ / |ϕ1 a|) / |lam| := by
          rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right t1 hl.le
        have a2 : 1 / lam ^ 2 * ‖ibpH B B1 ϕ1 ϕ2 b / (ϕ1 b : ℂ) * Eb - ibpH B B1 ϕ1 ϕ2 a / (ϕ1 a : ℂ) * Ea‖ ≤
            (‖ibpH B B1 ϕ1 ϕ2 b‖ / |ϕ1 b| + ‖ibpH B B1 ϕ1 ϕ2 a‖ / |ϕ1 a|) / lam ^ 2 := by
          rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right t2 hl2.le
        have a3 : 1 / lam ^ 2 * ‖∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))‖ ≤
            (∫ x in a..b, ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x‖) / lam ^ 2 := by
          rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right t3 hl2.le
        linarith

/-- info: 'FormalResearch.SignUncertainty.CtOsc.ibp_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ibp_once

/-- info: 'FormalResearch.SignUncertainty.CtOsc.ibp_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ibp_twice

/-- info: 'FormalResearch.SignUncertainty.CtOsc.ibp_twice_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ibp_twice_bound

end FormalResearch.SignUncertainty.CtOsc
