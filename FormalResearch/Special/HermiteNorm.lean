module

public import FormalResearch.Special.HermiteFunction

/-!
# Hermite functions: `L²` normalisation and a polynomial sup bound

For the orthonormal Hermite functions `hermitePhi` of `HermiteFunction`:

* `integral_hermitePhi_sq`: `∫_ℝ φ_n² = 1` (so the normalisation `(π^{1/4} √(n!))⁻¹` is the right one).  Proof: with
  `u_n(x) = He_n(√2 x)`, `(u_n e^{-x²})' = -√2 u_{n+1} e^{-x²}` and `u_{n+1}' = √2 (n+1) u_n`, one integration by parts gives
  `∫ u_{n+1}² e^{-x²} = (n+1) ∫ u_n² e^{-x²}` and `∫ e^{-x²} = √π`.
* `hermitePhi_sq_le`, `abs_hermitePhi_le`: **sup bound** `φ_n(x)² ≤ 2n + 2` for all real `x`.  Proof:
  `φ_n(x)² = ∫_{-∞}^x 2 φ_n φ_n'`, `2φφ' ≤ φ² + φ'²`, `φ'² ≤ n φ_{n-1}² + (n+1) φ_{n+1}²` (the ladder relation of
  `hasDerivAt_hermitePsi`) and the normalisation.  This is the cheap substitute for Cramér's bound `|φ_n| ≤ π^{-1/4}`
  (polynomial, not uniform, but enough for the exponentially small dominant coefficient in `HermiteAiryEdge`).

**Claim class: proved.**  Not formalised: orthogonality `∫ φ_n φ_m = 0` for `n ≠ m` (not needed), completeness,
Cramér's bound.
-/

@[expose] public section

open Polynomial Real MeasureTheory Filter Topology

namespace FormalResearch.Special

/-- Polynomial times Gaussian is integrable. -/
lemma pg_integrable (p : ℝ[X]) : Integrable (fun x : ℝ => p.eval x * Real.exp (-1 * x ^ 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : (fun x : ℝ => (p + q).eval x * Real.exp (-1 * x ^ 2)) =
        fun x => p.eval x * Real.exp (-1 * x ^ 2) + q.eval x * Real.exp (-1 * x ^ 2) := by
      funext x; simp [add_mul]
    rw [e]; exact hp.add hq
  | monomial n a =>
    have h := (integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (n : ℝ)) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)).const_mul a
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.rpow_natCast, mul_assoc]

/-- Polynomial times Gaussian tends to `0` at `+∞`. -/
lemma pg_tendsto_atTop (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-1 * x ^ 2)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : (fun x : ℝ => (p + q).eval x * Real.exp (-1 * x ^ 2)) =
        fun x => p.eval x * Real.exp (-1 * x ^ 2) + q.eval x * Real.exp (-1 * x ^ 2) := by
      funext x; simp [add_mul]
    rw [e]; simpa using hp.add hq
  | monomial n a =>
    have h1 := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (b := 1) one_pos (n : ℝ)
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp
        (Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)))
      refine this.congr (fun x => ?_)
      simp only [Function.comp, id]; congr 1; ring
    have h3 := h1.tendsto_zero_of_tendsto h2
    have h4 := h3.const_mul a
    simpa [Real.rpow_natCast, mul_assoc] using h4

/-- Polynomial times Gaussian tends to `0` at `-∞`. -/
lemma pg_tendsto_atBot (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * Real.exp (-1 * x ^ 2)) atBot (𝓝 0) := by
  have h := (pg_tendsto_atTop (p.comp (-X))).comp tendsto_neg_atBot_atTop
  refine h.congr (fun x => ?_)
  simp [Polynomial.eval_comp]

/-- `u_n(x) = He_n(√2 x)` as a polynomial in `x`. -/
noncomputable def hq (n : ℕ) : ℝ[X] := (heR n).comp (C √2 * X)

lemma eval_hq (n : ℕ) (x : ℝ) : (hq n).eval x = (heR n).eval (√2 * x) := by
  simp [hq, Polynomial.eval_comp]

/-- `φ_n = K_n · u_n · e^{-x²/2}` with the normalising constant `K_n`. -/
noncomputable def hermiteK (n : ℕ) : ℝ := ((π ^ (1 / 4 : ℝ)) * √(n.factorial : ℝ))⁻¹

lemma hermitePhi_eq (n : ℕ) (x : ℝ) :
    hermitePhi n x = hermiteK n * (hq n).eval x * Real.exp (-(x ^ 2 / 2)) := by
  simp [hermitePhi, hermiteK, eval_hq]

lemma hermitePhi_mul (a b : ℕ) (x : ℝ) :
    hermitePhi a x * hermitePhi b x =
      hermiteK a * hermiteK b * ((hq a * hq b).eval x * Real.exp (-1 * x ^ 2)) := by
  rw [hermitePhi_eq, hermitePhi_eq, Polynomial.eval_mul]
  have : Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) = Real.exp (-1 * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ = hermiteK a * hermiteK b * ((hq a).eval x * (hq b).eval x) *
        (Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2))) := by ring
    _ = _ := by rw [this]; ring

lemma integrable_hermitePhi_mul (a b : ℕ) : Integrable (fun x => hermitePhi a x * hermitePhi b x) := by
  have := (pg_integrable (hq a * hq b)).const_mul (hermiteK a * hermiteK b)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [hermitePhi_mul]

/-- Integrable products of the integer-indexed family. -/
lemma integrable_hermitePsi_mul (a b : ℤ) : Integrable (fun x => hermitePsi a x * hermitePsi b x) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb
      simpa [hermitePsi_natCast] using integrable_hermitePhi_mul m k
    · have : (fun x => hermitePsi a x * hermitePsi b x) = fun _ => 0 := by
        funext x; rw [hermitePsi_neg (not_le.1 hb), mul_zero]
      rw [this]; exact integrable_zero _ _ _
  · have : (fun x => hermitePsi a x * hermitePsi b x) = fun _ => 0 := by
      funext x; rw [hermitePsi_neg (not_le.1 ha), zero_mul]
    rw [this]; exact integrable_zero _ _ _

/-- The Gaussian-weighted derivative identity `(u_n e^{-x²})' = -√2 u_{n+1} e^{-x²}`. -/
lemma hasDerivAt_hq_gauss (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (heR n).eval (√2 * y) * Real.exp (-1 * y ^ 2))
      (-√2 * (heR (n + 1)).eval (√2 * x) * Real.exp (-1 * x ^ 2)) x := by
  have hp : HasDerivAt (fun y : ℝ => (heR n).eval (√2 * y)) ((derivative (heR n)).eval (√2 * x) * √2) x := by
    have h1 := (heR n).hasDerivAt (√2 * x)
    have h2 : HasDerivAt (fun y : ℝ => √2 * y) √2 x := by simpa using (hasDerivAt_id x).const_mul √2
    exact h1.comp x h2
  have hg : HasDerivAt (fun y : ℝ => Real.exp (-1 * y ^ 2)) (Real.exp (-1 * x ^ 2) * (-1 * (2 * x))) x := by
    have h := (((hasDerivAt_pow 2 x).const_mul (-1 : ℝ)).exp)
    refine h.congr_deriv ?_
    norm_num
  refine (hp.mul hg).congr_deriv ?_
  rw [heR_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (Real.exp (-1 * x ^ 2) * (heR n).eval (√2 * x) * x) * h2

lemma integrable_heR_mul (a b : ℕ) :
    Integrable (fun x : ℝ => (heR a).eval (√2 * x) * (heR b).eval (√2 * x) * Real.exp (-1 * x ^ 2)) := by
  refine (pg_integrable (hq a * hq b)).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [eval_hq]

lemma hasDerivAt_heR_succ_comp (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (heR (n + 1)).eval (√2 * y)) (√2 * ((n : ℝ) + 1) * (heR n).eval (√2 * x)) x := by
  have h1 := (heR (n + 1)).hasDerivAt (√2 * x)
  have h2 : HasDerivAt (fun y : ℝ => √2 * y) √2 x := by simpa using (hasDerivAt_id x).const_mul √2
  refine (h1.comp x h2).congr_deriv ?_
  rw [derivative_heR_succ]; simp; ring

/-- `∫ He_{n+1}(√2x)² e^{-x²} = (n+1) ∫ He_n(√2x)² e^{-x²}`. -/
lemma integral_heR_sq_succ (n : ℕ) :
    ∫ x : ℝ, (heR (n + 1)).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2) =
      ((n : ℝ) + 1) * ∫ x : ℝ, (heR n).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2) := by
  set u : ℝ → ℝ := fun x => (heR (n + 1)).eval (√2 * x) with hu
  set v : ℝ → ℝ := fun y => (heR n).eval (√2 * y) * Real.exp (-1 * y ^ 2) with hv
  set u' : ℝ → ℝ := fun x => √2 * ((n : ℝ) + 1) * (heR n).eval (√2 * x) with hu'
  set v' : ℝ → ℝ := fun x => -√2 * (heR (n + 1)).eval (√2 * x) * Real.exp (-1 * x ^ 2) with hv'
  have hpar := integral_mul_deriv_eq_deriv_mul_of_integrable (u := u) (v := v) (u' := u') (v' := v')
    (fun x _ => hasDerivAt_heR_succ_comp n x) (fun x _ => hasDerivAt_hq_gauss n x)
    (by
      have := (integrable_heR_mul (n + 1) (n + 1)).const_mul (-√2)
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [hu, hv', Pi.mul_apply]; ring)
    (by
      have := (integrable_heR_mul n n).const_mul (√2 * ((n : ℝ) + 1))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [hu', hv, Pi.mul_apply]; ring)
    (by
      have := integrable_heR_mul (n + 1) n
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [hu, hv, Pi.mul_apply]; ring)
  have e1 : ∫ x, u x * v' x = -√2 * ∫ x : ℝ, (heR (n + 1)).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2) := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [hu, hv']; ring
  have e2 : ∫ x, u' x * v x =
      √2 * ((n : ℝ) + 1) * ∫ x : ℝ, (heR n).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2) := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [hu', hv]; ring
  rw [e1, e2] at hpar
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have : √2 * ∫ x : ℝ, (heR (n + 1)).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2) =
      √2 * (((n : ℝ) + 1) * ∫ x : ℝ, (heR n).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2)) := by
    linarith
  exact mul_left_cancel₀ h2.ne' this

lemma integral_heR_sq (n : ℕ) :
    ∫ x : ℝ, (heR n).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2) = (n.factorial : ℝ) * √π := by
  induction n with
  | zero =>
    have h := integral_gaussian 1
    simp only [heR_zero]
    simpa using h
  | succ n ih =>
    rw [integral_heR_sq_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- **`L²` normalisation**: `∫_ℝ φ_n² = 1`. -/
theorem integral_hermitePhi_sq (n : ℕ) : ∫ x : ℝ, hermitePhi n x ^ 2 = 1 := by
  have e : ∀ x, hermitePhi n x ^ 2 =
      hermiteK n ^ 2 * ((heR n).eval (√2 * x) ^ 2 * Real.exp (-1 * x ^ 2)) := by
    intro x
    rw [hermitePhi_eq, eval_hq]
    have : Real.exp (-(x ^ 2 / 2)) ^ 2 = Real.exp (-1 * x ^ 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc _ = hermiteK n ^ 2 * (heR n).eval (√2 * x) ^ 2 * Real.exp (-(x ^ 2 / 2)) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_heR_sq]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hpi : (π ^ (1 / 4 : ℝ)) ^ 2 = √π := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, Real.sqrt_eq_rpow]; norm_num
  have hK : hermiteK n ^ 2 = (√π * n.factorial)⁻¹ := by
    unfold hermiteK
    rw [inv_pow, mul_pow, hpi, Real.sq_sqrt hf.le]
  rw [hK]
  have : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  field_simp

lemma integrable_hermitePsi_sq (m : ℤ) : Integrable (fun x => hermitePsi m x ^ 2) := by
  simpa [sq] using integrable_hermitePsi_mul m m

lemma integral_hermitePsi_sq_le (m : ℤ) : ∫ x : ℝ, hermitePsi m x ^ 2 ≤ 1 := by
  by_cases hm : 0 ≤ m
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    simp only [hermitePsi_natCast]
    exact (integral_hermitePhi_sq k).le
  · have : (fun x => hermitePsi m x ^ 2) = fun _ => 0 := by
      funext x; rw [hermitePsi_neg (not_le.1 hm)]; norm_num
    rw [this]; simp

/-- **Sup bound**: `φ_n(x)² ≤ 2n + 2` for all real `x` (polynomial substitute for Cramér's `|φ_n| ≤ π^{-1/4}`). -/
theorem hermitePhi_sq_le (n : ℕ) (x : ℝ) : hermitePhi n x ^ 2 ≤ 2 * n + 2 := by
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hm : hermitePsi (n : ℤ) = hermitePhi n := funext (hermitePsi_natCast n)
  set D : ℝ → ℝ := fun y => √((n : ℝ) / 2) * hermitePsi ((n : ℤ) - 1) y -
    √(((n : ℝ) + 1) / 2) * hermitePsi ((n : ℤ) + 1) y with hD
  set G : ℝ → ℝ := fun y => hermitePhi n y ^ 2 + (n : ℝ) * hermitePsi ((n : ℤ) - 1) y ^ 2 +
    ((n : ℝ) + 1) * hermitePsi ((n : ℤ) + 1) y ^ 2 with hG
  have hder : ∀ y, HasDerivAt (fun y => hermitePhi n y ^ 2) (2 * hermitePhi n y * D y) y := by
    intro y
    have h := hasDerivAt_hermitePsi (n : ℤ) hn y
    rw [hm] at h
    have := h.pow 2
    refine this.congr_deriv ?_
    simp only [hD]; push_cast; ring
  have hGint : Integrable G := by
    have h1 : Integrable (fun y => hermitePhi n y ^ 2) := by
      simpa [hm] using integrable_hermitePsi_sq (n : ℤ)
    exact (h1.add ((integrable_hermitePsi_sq ((n : ℤ) - 1)).const_mul (n : ℝ))).add
      ((integrable_hermitePsi_sq ((n : ℤ) + 1)).const_mul ((n : ℝ) + 1))
  have hGint_val : ∫ y, G y ≤ 2 * n + 2 := by
    have h1 : Integrable (fun y => hermitePhi n y ^ 2) := by
      simpa [hm] using integrable_hermitePsi_sq (n : ℤ)
    have i2 := (integrable_hermitePsi_sq ((n : ℤ) - 1)).const_mul (n : ℝ)
    have i3 := (integrable_hermitePsi_sq ((n : ℤ) + 1)).const_mul ((n : ℝ) + 1)
    have e : ∫ y, G y = (∫ y, hermitePhi n y ^ 2) + (n : ℝ) * (∫ y, hermitePsi ((n : ℤ) - 1) y ^ 2) +
        ((n : ℝ) + 1) * (∫ y, hermitePsi ((n : ℤ) + 1) y ^ 2) := by
      simp only [hG]
      rw [integral_add (f := fun y => hermitePhi n y ^ 2 + (n : ℝ) * hermitePsi ((n : ℤ) - 1) y ^ 2)
        (g := fun y => ((n : ℝ) + 1) * hermitePsi ((n : ℤ) + 1) y ^ 2) (h1.add i2) i3,
        integral_add (f := fun y => hermitePhi n y ^ 2) (g := fun y => (n : ℝ) * hermitePsi ((n : ℤ) - 1) y ^ 2) h1 i2,
        integral_const_mul (n : ℝ), integral_const_mul ((n : ℝ) + 1)]
    rw [e, integral_hermitePhi_sq]
    have a2 := integral_hermitePsi_sq_le ((n : ℤ) - 1)
    have a3 := integral_hermitePsi_sq_le ((n : ℤ) + 1)
    have n0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have b2 := mul_le_mul_of_nonneg_left a2 n0
    have b3 := mul_le_mul_of_nonneg_left a3 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    linarith
  have hpt : ∀ y, |2 * hermitePhi n y * D y| ≤ G y := by
    intro y
    have hA := sq_nonneg (√((n : ℝ) / 2) * hermitePsi ((n : ℤ) - 1) y +
      √(((n : ℝ) + 1) / 2) * hermitePsi ((n : ℤ) + 1) y)
    have s1 : √((n : ℝ) / 2) ^ 2 = (n : ℝ) / 2 := Real.sq_sqrt (by positivity)
    have s2 : √(((n : ℝ) + 1) / 2) ^ 2 = ((n : ℝ) + 1) / 2 := Real.sq_sqrt (by positivity)
    have hD2 : D y ^ 2 ≤ (n : ℝ) * hermitePsi ((n : ℤ) - 1) y ^ 2 +
        ((n : ℝ) + 1) * hermitePsi ((n : ℤ) + 1) y ^ 2 := by
      simp only [hD]
      nlinarith [hA, s1, s2]
    have h3 : |2 * hermitePhi n y * D y| ≤ hermitePhi n y ^ 2 + D y ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (hermitePhi n y + D y), sq_nonneg (hermitePhi n y - D y)]
    simp only [hG]; linarith
  have hfint : Integrable (fun y => 2 * hermitePhi n y * D y) := by
    refine hGint.mono' ?_ (Filter.Eventually.of_forall hpt)
    have h1 := (integrable_hermitePsi_mul (n : ℤ) ((n : ℤ) - 1)).const_mul (2 * √((n : ℝ) / 2))
    have h2 := (integrable_hermitePsi_mul (n : ℤ) ((n : ℤ) + 1)).const_mul (2 * √(((n : ℝ) + 1) / 2))
    have := (h1.sub h2).aestronglyMeasurable
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hD, Pi.sub_apply, hm]; ring
  have hlim : Tendsto (fun y => hermitePhi n y ^ 2) atBot (𝓝 0) := by
    have := (pg_tendsto_atBot (hq n * hq n)).const_mul (hermiteK n * hermiteK n)
    simp only [mul_zero] at this
    refine this.congr (fun y => ?_)
    rw [← hermitePhi_mul, sq]
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (f := fun y => hermitePhi n y ^ 2)
    (f' := fun y => 2 * hermitePhi n y * D y) (fun y _ => hder y) hfint.integrableOn hlim
  rw [sub_zero] at hFTC
  have h1 : ∫ y in Set.Iic x, 2 * hermitePhi n y * D y ≤ ∫ y in Set.Iic x, G y :=
    setIntegral_mono hfint.integrableOn hGint.integrableOn (fun y => (le_abs_self _).trans (hpt y))
  have h2 : ∫ y in Set.Iic x, G y ≤ ∫ y, G y := by
    refine setIntegral_le_integral hGint (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.zero_apply, hG]; positivity
  linarith

theorem abs_hermitePhi_le (n : ℕ) (x : ℝ) : |hermitePhi n x| ≤ √(2 * n + 2) :=
  Real.abs_le_sqrt (hermitePhi_sq_le n x)

/-- info: 'FormalResearch.Special.integral_hermitePhi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_hermitePhi_sq

/-- info: 'FormalResearch.Special.hermitePhi_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermitePhi_sq_le

/-- info: 'FormalResearch.Special.abs_hermitePhi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_hermitePhi_le

end FormalResearch.Special
