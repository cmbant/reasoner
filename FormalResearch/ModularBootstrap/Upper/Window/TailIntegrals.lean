module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration lemmas for Lemma `T` (`ut:T`)

The substitution `t = c' x²/3` (`dt = (2/3) c' x dx`) on a compact band `[a, b]` and on `[a, ∞)`,
the power integral `∫_{a}^{∞} (x - ξ)^{-p} dx ≤ (a - ξ)^{1-p}/(p - 1)` (`p > 1`), and the tail constant
`∫_{x ≥ x₀} √x e^{-πx} dx ≤ ∫_0^∞ √x e^{-πx} dx` (`farConst`).

All results are proved unconditionally.
-/

@[expose] public section

open Real MeasureTheory Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Window.Tail

private lemma sq_hasDerivWithinAt (c' x : ℝ) (s : Set ℝ) :
    HasDerivWithinAt (fun y : ℝ => c' * y ^ 2 / 3) (2 * c' * x / 3) s x := by
  have := ((hasDerivAt_pow 2 x).const_mul c').div_const 3
  exact (this.congr_deriv (by simp only [Nat.cast_ofNat]; ring)).hasDerivWithinAt

private lemma sq_injOn {c' : ℝ} (hc' : 0 < c') {a : ℝ} (ha : 0 ≤ a) :
    InjOn (fun y : ℝ => c' * y ^ 2 / 3) (Ici a) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := ha.trans hx
  have hy0 : 0 ≤ y := ha.trans hy
  have h1 : x ^ 2 = y ^ 2 := by
    have : c' * x ^ 2 = c' * y ^ 2 := by simp only at hxy; linarith
    exact mul_left_cancel₀ hc'.ne' this
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- Substitution `t = c' x²/3` on a compact band. -/
lemma integral_Icc_comp_sq {c' a b : ℝ} (hc' : 0 < c') (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ t in Icc (c' * a ^ 2 / 3) (c' * b ^ 2 / 3), g t =
      ∫ x in Icc a b, (2 * c' * x / 3) * g (c' * x ^ 2 / 3) := by
  have himg : (fun y : ℝ => c' * y ^ 2 / 3) '' Icc a b = Icc (c' * a ^ 2 / 3) (c' * b ^ 2 / 3) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : 0 ≤ x := ha.le.trans hx.1
      refine ⟨?_, ?_⟩
      · have : a ^ 2 ≤ x ^ 2 := by nlinarith [hx.1]
        have := mul_le_mul_of_nonneg_left this hc'.le
        linarith
      · have : x ^ 2 ≤ b ^ 2 := by nlinarith [hx.2]
        have := mul_le_mul_of_nonneg_left this hc'.le
        linarith
    · intro hy
      have hy0 : 0 ≤ 3 * y / c' := by
        have h1 : 0 ≤ c' * a ^ 2 / 3 := by positivity
        have h2 := hy.1
        exact div_nonneg (by linarith) hc'.le
      refine ⟨Real.sqrt (3 * y / c'), ⟨?_, ?_⟩, ?_⟩
      · refine Real.le_sqrt_of_sq_le ?_
        have := hy.1
        rw [le_div_iff₀ hc']
        nlinarith
      · refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
        have := hy.2
        rw [div_le_iff₀ hc']
        nlinarith
      · show c' * Real.sqrt (3 * y / c') ^ 2 / 3 = y
        rw [Real.sq_sqrt hy0]
        field_simp
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Icc (a := a) (b := b))
    (f := fun y : ℝ => c' * y ^ 2 / 3) (f' := fun x => 2 * c' * x / 3)
    (fun x _ => sq_hasDerivWithinAt c' x _)
    ((sq_injOn hc' ha.le).mono Icc_subset_Ici_self) g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  have hx0 : 0 ≤ x := ha.le.trans hx.1
  simp only [smul_eq_mul]
  rw [abs_of_nonneg (by positivity)]

/-- Substitution `t = c' x²/3` on a half line. -/
lemma integral_Ici_comp_sq {c' a : ℝ} (hc' : 0 < c') (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ t in Ici (c' * a ^ 2 / 3), g t = ∫ x in Ici a, (2 * c' * x / 3) * g (c' * x ^ 2 / 3) := by
  have himg : (fun y : ℝ => c' * y ^ 2 / 3) '' Ici a = Ici (c' * a ^ 2 / 3) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxa : a ≤ x := hx
      have hx0 : 0 ≤ x := ha.le.trans hxa
      have : a ^ 2 ≤ x ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this hc'.le
      show c' * a ^ 2 / 3 ≤ c' * x ^ 2 / 3
      linarith
    · intro hy
      have hy' : c' * a ^ 2 / 3 ≤ y := hy
      have hy0 : 0 ≤ 3 * y / c' := by
        have h1 : 0 ≤ c' * a ^ 2 / 3 := by positivity
        exact div_nonneg (by linarith) hc'.le
      refine ⟨Real.sqrt (3 * y / c'), ?_, ?_⟩
      · refine Real.le_sqrt_of_sq_le ?_
        rw [le_div_iff₀ hc']
        nlinarith
      · show c' * Real.sqrt (3 * y / c') ^ 2 / 3 = y
        rw [Real.sq_sqrt hy0]
        field_simp
  have h := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ici (a := a))
    (f := fun y : ℝ => c' * y ^ 2 / 3) (f' := fun x => 2 * c' * x / 3)
    (fun x _ => sq_hasDerivWithinAt c' x _) (sq_injOn hc' ha.le) g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
  have hx0 : 0 ≤ x := ha.le.trans hx
  simp only [smul_eq_mul]
  rw [abs_of_nonneg (by positivity)]

/-- `∫_{a}^{b} (x - ξ)^{-p} dx ≤ (a - ξ)^{1-p}/(p - 1)` for `p > 1` and `ξ < a ≤ b`. -/
lemma integral_Icc_rpow_neg_le {ξ a b p : ℝ} (hp : 1 < p) (hξa : ξ < a) (hab : a ≤ b) :
    ∫ x in Icc a b, (x - ξ) ^ (-p) ≤ (a - ξ) ^ (1 - p) / (p - 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_right (fun y : ℝ => y ^ (-p)) ξ,
    integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith⟩)]
  have hb : 0 < b - ξ := by linarith
  have h1 : 0 ≤ (b - ξ) ^ (-p + 1) := (Real.rpow_pos_of_pos hb _).le
  have hp1 : 0 < p - 1 := by linarith
  rw [show -p + 1 = 1 - p by ring] at h1 ⊢
  generalize (b - ξ) ^ (1 - p) = X at h1 ⊢
  generalize (a - ξ) ^ (1 - p) = Y at h1 ⊢
  rw [show (1 - p) = -(p - 1) by ring, div_neg, ← neg_div, neg_sub]
  exact div_le_div_of_nonneg_right (by linarith) hp1.le

/-- The tail constant `∫_0^∞ √x e^{-πx} dx`. -/
noncomputable def farConst : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (1 / 2 : ℝ) * exp (-π * x)

lemma integrableOn_sqrt_exp :
    IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) * exp (-π * x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1 / 2) (p := 1) (b := π)
    (by norm_num) one_pos Real.pi_pos
  simpa [Real.rpow_one] using h

lemma farConst_nonneg : 0 ≤ farConst :=
  setIntegral_nonneg measurableSet_Ioi fun x hx => by
    have : 0 < x := hx
    positivity

lemma integrableOn_Ici_sqrt_exp {x₀ : ℝ} (hx₀ : 0 < x₀) :
    IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) * exp (-π * x)) (Ici x₀) :=
  integrableOn_sqrt_exp.mono_set (Ici_subset_Ioi.mpr hx₀)

lemma integral_Ici_sqrt_exp_le {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∫ x in Ici x₀, x ^ (1 / 2 : ℝ) * exp (-π * x) ≤ farConst := by
  refine setIntegral_mono_set integrableOn_sqrt_exp ?_ (Ici_subset_Ioi.mpr hx₀).eventuallySubset
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have : 0 < x := hx
  positivity

/-- The order-`p` tail constant `∫_0^∞ √x (1+x)^p e^{-πx} dx` (`farConstP 0 = farConst`). -/
noncomputable def farConstP (p : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x)

lemma one_add_pow_le (p : ℕ) {x : ℝ} (hx : 0 ≤ x) : (1 + x) ^ p ≤ 2 ^ p * (1 + x ^ p) := by
  rcases le_total x 1 with h | h
  · have h1 : (1 + x) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
    have h2 : 0 ≤ x ^ p := pow_nonneg hx p
    have h3 : (0 : ℝ) ≤ 2 ^ p := by positivity
    nlinarith
  · have h1 : (1 + x) ^ p ≤ (2 * x) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
    rw [mul_pow] at h1
    have h2 : (0 : ℝ) ≤ 2 ^ p := by positivity
    have h3 : 0 ≤ x ^ p := pow_nonneg hx p
    nlinarith

lemma integrableOn_sqrt_pow_exp (p : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x)) (Ioi 0) := by
  have h2 : IntegrableOn (fun x : ℝ => x ^ ((p : ℝ) + 1 / 2) * exp (-π * x)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p : ℝ) + 1 / 2) (p := 1) (b := π)
      (by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith) one_pos Real.pi_pos
    simpa [Real.rpow_one] using h
  have hdom : IntegrableOn (fun x : ℝ => 2 ^ p * (x ^ (1 / 2 : ℝ) * exp (-π * x) +
      x ^ ((p : ℝ) + 1 / 2) * exp (-π * x))) (Ioi 0) :=
    (integrableOn_sqrt_exp.add h2).const_mul _
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ((ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt hx)).mul
      ((continuous_const.add continuous_id).pow p).continuousOn).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hx
    have hp := one_add_pow_le p hx0.le
    have hpos : 0 ≤ x ^ (1 / 2 : ℝ) * exp (-π * x) := by positivity
    have hxp : x ^ ((p : ℝ) + 1 / 2) = x ^ (1 / 2 : ℝ) * x ^ p := by
      rw [Real.rpow_add hx0, mul_comm, Real.rpow_natCast]
    rw [Real.norm_of_nonneg (by positivity)]
    calc x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x)
        = (1 + x) ^ p * (x ^ (1 / 2 : ℝ) * exp (-π * x)) := by ring
      _ ≤ (2 ^ p * (1 + x ^ p)) * (x ^ (1 / 2 : ℝ) * exp (-π * x)) :=
          mul_le_mul_of_nonneg_right hp hpos
      _ = _ := by rw [hxp]; ring

lemma farConstP_nonneg (p : ℕ) : 0 ≤ farConstP p :=
  setIntegral_nonneg measurableSet_Ioi fun x hx => by
    have : 0 < x := hx
    positivity

lemma integrableOn_Ici_sqrt_pow_exp (p : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x)) (Ici x₀) :=
  (integrableOn_sqrt_pow_exp p).mono_set (Ici_subset_Ioi.mpr hx₀)

lemma integral_Ici_sqrt_pow_exp_le (p : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∫ x in Ici x₀, x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x) ≤ farConstP p := by
  refine setIntegral_mono_set (integrableOn_sqrt_pow_exp p) ?_ (Ici_subset_Ioi.mpr hx₀).eventuallySubset
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have : 0 < x := hx
  positivity

/-- The constant algebra of the intermediate band: with `u₀ ≥ κ λ N₁^{2/3}` (`K0`(c)),
`Kc u₀^{1-p}/(p-1) ≤ FK_c C_T N₁^{-(2/3)(p-1)}`, `Kc = 2 C_R C_A (D/π)^p FV/λ`, `FK = FV (2√2/(πλ))^p`. -/
lemma band_final_algebra {p lam κ W CR CA D N1 u0 : ℝ} (hp : 1 < p) (hlam : 0 < lam) (hκ : 0 < κ)
    (hN1 : 0 < N1) (hW : 0 ≤ W) (hCR : 0 ≤ CR) (hCA : 0 ≤ CA) (hD : 0 < D)
    (hu0 : κ * lam * N1 ^ (2 / 3 : ℝ) ≤ u0) :
    2 * CR * CA * (D / π) ^ p * W / lam * (u0 ^ (1 - p) / (p - 1)) ≤
      W * (2 * √2 / (π * lam)) ^ p *
        (2 * CR * CA * (D / (2 * √2)) ^ p * κ ^ (1 - p) / (p - 1)) * N1 ^ ((2 / 3 : ℝ) * (1 - p)) := by
  have hpi := Real.pi_pos
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hN23 : 0 < N1 ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hN1 _
  have hpos : 0 < κ * lam * N1 ^ (2 / 3 : ℝ) := by positivity
  have h1 : u0 ^ (1 - p) ≤ (κ * lam * N1 ^ (2 / 3 : ℝ)) ^ (1 - p) :=
    Real.rpow_le_rpow_of_nonpos hpos hu0 (by linarith)
  have h2 : (κ * lam * N1 ^ (2 / 3 : ℝ)) ^ (1 - p) =
      κ ^ (1 - p) * lam ^ (1 - p) * N1 ^ ((2 / 3 : ℝ) * (1 - p)) := by
    rw [Real.mul_rpow (by positivity) hN23.le, Real.mul_rpow hκ.le hlam.le,
      ← Real.rpow_mul hN1.le]
  have h3 : (2 * √2 / (π * lam)) ^ p = (2 * √2 / π) ^ p * lam ^ (-p) := by
    rw [show 2 * √2 / (π * lam) = (2 * √2 / π) * lam⁻¹ by field_simp,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hlam.le, ← Real.rpow_neg hlam.le]
  have h4 : (D / π) ^ p = (D / (2 * √2)) ^ p * (2 * √2 / π) ^ p := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  have h5 : lam ^ (1 - p) / lam = lam ^ (-p) := by
    rw [show 1 - p = -p + 1 by ring, Real.rpow_add_one hlam.ne']
    field_simp
  have hp1 : 0 < p - 1 := by linarith
  calc 2 * CR * CA * (D / π) ^ p * W / lam * (u0 ^ (1 - p) / (p - 1))
      ≤ 2 * CR * CA * (D / π) ^ p * W / lam *
        ((κ ^ (1 - p) * lam ^ (1 - p) * N1 ^ ((2 / 3 : ℝ) * (1 - p))) / (p - 1)) := by
        rw [← h2]
        gcongr
    _ = W * ((2 * √2 / π) ^ p * (lam ^ (1 - p) / lam)) *
        (2 * CR * CA * (D / (2 * √2)) ^ p * κ ^ (1 - p) / (p - 1)) *
          N1 ^ ((2 / 3 : ℝ) * (1 - p)) := by
        rw [h4]; field_simp
    _ = _ := by rw [h5, h3]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.integral_Icc_comp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Icc_comp_sq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.integral_Ici_comp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Ici_comp_sq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.integral_Icc_rpow_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Icc_rpow_neg_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.integral_Ici_sqrt_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Ici_sqrt_exp_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.band_final_algebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms band_final_algebra

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Tail.integral_Ici_sqrt_pow_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Ici_sqrt_pow_exp_le

end FormalResearch.ModularBootstrap.Upper.Window.Tail
