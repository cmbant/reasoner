module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterTheta

/-!
# The chain rule `x ↦ θ_out(y(x))` (FIVE-S, S2)

With `τ(x) = (2/π) arcosh(cosh(πx)/√2)` (`cosh πτ = sinh²(πx)`, `x_T(τ(x)) = x`), `D = √(cosh²πx - 2) = √(sinh²πx - 1)`:
`τ' = 2 sinh πx / D`, `τ'' = -2π cosh πx / D³`, and `D² ≥ 2√2 π r`, `τ ≤ √2 D/π`, `r = x - ξ*`.
Hence `θ_x = Θ'(τ) τ'`, `θ_xx = Θ''(τ) τ'² + Θ'(τ) τ''` with `Θ = thetaOutT`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

lemma sinh_pi_xiStar : Real.sinh (π * xiStar) = 1 := by
  have : π * xiStar = Real.arsinh 1 := by unfold xiStar; field_simp
  rw [this, Real.sinh_arsinh]

lemma cosh_pi_xiStar : Real.cosh (π * xiStar) = √2 := by
  have : π * xiStar = Real.arsinh 1 := by unfold xiStar; field_simp
  rw [this, Real.cosh_arsinh]; norm_num

lemma one_lt_sinh_of_gt {x : ℝ} (hx : xiStar < x) : 1 < Real.sinh (π * x) := by
  rw [← sinh_pi_xiStar]
  exact Real.sinh_lt_sinh.mpr (by nlinarith [Real.pi_pos])

/-- `D(x) = √(cosh²πx - 2)`. -/
noncomputable def Dx (x : ℝ) : ℝ := √(Real.cosh (π * x) ^ 2 - 2)

lemma Dx_sq {x : ℝ} (hx : xiStar < x) : Dx x ^ 2 = Real.sinh (π * x) ^ 2 - 1 := by
  have h1 := one_lt_sinh_of_gt hx
  unfold Dx
  rw [Real.sq_sqrt (by nlinarith [Real.cosh_sq (π * x)])]
  nlinarith [Real.cosh_sq (π * x)]

lemma Dx_pos {x : ℝ} (hx : xiStar < x) : 0 < Dx x := by
  have h1 := one_lt_sinh_of_gt hx
  unfold Dx
  apply Real.sqrt_pos.mpr
  nlinarith [Real.cosh_sq (π * x)]

/-- `τ'(x) = 2 sinh πx / D`. -/
noncomputable def tx (x : ℝ) : ℝ := 2 * Real.sinh (π * x) / Dx x

/-- `τ''(x) = -2π cosh πx / D³`. -/
noncomputable def txx (x : ℝ) : ℝ := -(2 * π * Real.cosh (π * x)) / Dx x ^ 3

lemma hasDerivAt_Dx {x : ℝ} (hx : xiStar < x) :
    HasDerivAt Dx (π * Real.cosh (π * x) * Real.sinh (π * x) / Dx x) x := by
  have hD := Dx_pos hx
  have h1 : HasDerivAt (fun x : ℝ => Real.cosh (π * x) ^ 2 - 2)
      (2 * Real.cosh (π * x) * (Real.sinh (π * x) * π)) x := by
    have := ((hasDerivAt_cosh_arg 1 x).pow 2).sub_const 2
    simpa using this
  have hpos : Real.cosh (π * x) ^ 2 - 2 ≠ 0 := by
    have := Dx_sq hx
    have h2 := one_lt_sinh_of_gt hx
    nlinarith [Real.cosh_sq (π * x)]
  have h := h1.sqrt hpos
  unfold Dx
  refine h.congr_deriv ?_
  have : √(Real.cosh (π * x) ^ 2 - 2) = Dx x := rfl
  rw [this]
  field_simp

lemma hasDerivAt_tx {x : ℝ} (hx : xiStar < x) : HasDerivAt tx (txx x) x := by
  have hD := Dx_pos hx
  have hs : HasDerivAt (fun x : ℝ => Real.sinh (π * x)) (Real.cosh (π * x) * π) x := by
    simpa using hasDerivAt_sinh_arg 1 x
  have h := (hs.const_mul 2).div (hasDerivAt_Dx hx) hD.ne'
  unfold tx txx
  refine h.congr_deriv ?_
  have hsq := Dx_sq hx
  field_simp
  nlinarith [hsq, Real.cosh_sq (π * x)]


lemma cosh_div_sqrt_two_gt_one {x : ℝ} (hx : xiStar < x) : 1 < Real.cosh (π * x) / √2 := by
  have h1 := one_lt_sinh_of_gt hx
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  rw [lt_div_iff₀ hs2, one_mul]
  have hc : 0 < Real.cosh (π * x) := Real.cosh_pos _
  have : √2 ^ 2 < Real.cosh (π * x) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num)]; nlinarith [Real.cosh_sq (π * x)]
  exact lt_of_pow_lt_pow_left₀ 2 hc.le this

lemma tauOfX_nonneg {x : ℝ} (hx : xiStar < x) : 0 ≤ tauOfX x := by
  unfold tauOfX
  exact mul_nonneg (by positivity) (Real.arcosh_nonneg (cosh_div_sqrt_two_gt_one hx).le)

lemma cosh_tauOfX_half {x : ℝ} (hx : xiStar < x) : Real.cosh (π * tauOfX x / 2) = Real.cosh (π * x) / √2 := by
  have hpi := Real.pi_pos
  have : π * tauOfX x / 2 = Real.arcosh (Real.cosh (π * x) / √2) := by
    unfold tauOfX; field_simp
  rw [this, Real.cosh_arcosh (cosh_div_sqrt_two_gt_one hx).le]

lemma cosh_tauOfX {x : ℝ} (hx : xiStar < x) : Real.cosh (π * tauOfX x) = Real.sinh (π * x) ^ 2 := by
  have h := cosh_tauOfX_half hx
  have e : π * tauOfX x = 2 * (π * tauOfX x / 2) := by ring
  rw [e, Real.cosh_two_mul]
  have : Real.cosh (π * tauOfX x / 2) ^ 2 + Real.sinh (π * tauOfX x / 2) ^ 2 =
      2 * Real.cosh (π * tauOfX x / 2) ^ 2 - 1 := by nlinarith [Real.cosh_sq (π * tauOfX x / 2)]
  rw [this, h, div_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [Real.cosh_sq (π * x)]

lemma xT_tauOfX {x : ℝ} (hx : xiStar < x) : xT (tauOfX x) = x := by
  have hpi := Real.pi_pos
  have h1 := one_lt_sinh_of_gt hx
  unfold xT
  rw [cosh_tauOfX hx, Real.sqrt_sq (by linarith), Real.arsinh_sinh]
  field_simp

lemma tauOfX_le {x : ℝ} (hx : xiStar < x) : tauOfX x ≤ √2 * Dx x / π := by
  have hpi := Real.pi_pos
  have hg := cosh_div_sqrt_two_gt_one hx
  have h1 : Real.arcosh (Real.cosh (π * x) / √2) ≤ √((Real.cosh (π * x) / √2) ^ 2 - 1) := by
    have := (Real.self_le_sinh_iff.mpr (Real.arcosh_nonneg hg.le))
    rwa [Real.sinh_arcosh hg.le] at this
  have h2 : √((Real.cosh (π * x) / √2) ^ 2 - 1) = Dx x / √2 := by
    have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    unfold Dx
    rw [show (Real.cosh (π * x) / √2) ^ 2 - 1 = (Real.cosh (π * x) ^ 2 - 2) / (√2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; ring, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs2.le]
  unfold tauOfX
  rw [h2] at h1
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  calc 2 / π * Real.arcosh (Real.cosh (π * x) / √2) ≤ 2 / π * (Dx x / √2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = √2 * Dx x / π := by
        field_simp
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring

lemma hasDerivAt_tauOfX {x : ℝ} (hx : xiStar < x) : HasDerivAt tauOfX (tx x) x := by
  have hpi := Real.pi_pos
  have hg := cosh_div_sqrt_two_gt_one hx
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hc : HasDerivAt (fun x : ℝ => Real.cosh (π * x) / √2) (Real.sinh (π * x) * π / √2) x := by
    have := (hasDerivAt_cosh_arg 1 x).div_const √2
    simpa using this
  have h := (Real.hasDerivAt_arcosh (x := Real.cosh (π * x) / √2) hg).comp x hc
  have h2 := h.const_mul (2 / π)
  have hD := Dx_pos hx
  have e : √((Real.cosh (π * x) / √2) ^ 2 - 1) = Dx x / √2 := by
    unfold Dx
    rw [show (Real.cosh (π * x) / √2) ^ 2 - 1 = (Real.cosh (π * x) ^ 2 - 2) / (√2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; ring, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs2.le]
  unfold tauOfX tx
  refine h2.congr_deriv ?_
  simp only [e]
  field_simp


/-- `S₁ = sinh(π(ξ*+1))`, `C₁ = cosh(π(ξ*+1))`. -/
noncomputable def S1c : ℝ := Real.sinh (π * (xiStar + 1))
noncomputable def C1c : ℝ := Real.cosh (π * (xiStar + 1))

lemma one_lt_S1c : 1 < S1c := one_lt_sinh_of_gt (by linarith)

lemma sinh_sub_one_ge {x : ℝ} (hx : xiStar < x) : √2 * π * (x - xiStar) ≤ Real.sinh (π * x) - 1 := by
  have hpi := Real.pi_pos
  have e : π * x = π * xiStar + π * (x - xiStar) := by ring
  rw [e, Real.sinh_add, sinh_pi_xiStar, cosh_pi_xiStar]
  have h1 : 0 ≤ π * (x - xiStar) := by nlinarith
  have h2 := Real.self_le_sinh_iff.mpr h1
  have h3 := Real.one_le_cosh (π * (x - xiStar))
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left h2 hs2.le, Real.sinh_nonneg_iff.mpr h1]

lemma Dx_sq_ge {x : ℝ} (hx : xiStar < x) : 2 * √2 * π * (x - xiStar) ≤ Dx x ^ 2 := by
  have h := sinh_sub_one_ge hx
  have h1 := one_lt_sinh_of_gt hx
  rw [Dx_sq hx]
  nlinarith

lemma sinh_le_S1 {x : ℝ} (hr : x - xiStar ≤ 1) : Real.sinh (π * x) ≤ S1c := by
  unfold S1c
  exact Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos])

lemma cosh_le_C1 {x : ℝ} (hx : xiStar < x) (hr : x - xiStar ≤ 1) : Real.cosh (π * x) ≤ C1c := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  unfold C1c
  have h1 : |π * x| ≤ |π * (xiStar + 1)| := by
    rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]; nlinarith
  exact Real.cosh_le_cosh.mpr h1

lemma S1c_le_sinh {x : ℝ} (hr : 1 ≤ x - xiStar) : S1c ≤ Real.sinh (π * x) := by
  unfold S1c
  exact Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos])

lemma sinh_sub_one_le {x : ℝ} (hx : xiStar < x) (hr : x - xiStar ≤ 1) :
    Real.sinh (π * x) - 1 ≤ C1c * π * (x - xiStar) := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  -- mean value theorem for sinh on [π ξ*, π x]
  have hconv : Convex ℝ (Icc (π * xiStar) (π * x)) := convex_Icc _ _
  have hb : ∀ y ∈ Icc (π * xiStar) (π * x), ‖Real.cosh y‖ ≤ C1c := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    unfold C1c
    have h1 : |y| ≤ |π * (xiStar + 1)| := by
      rw [abs_of_pos (by nlinarith : 0 < π * (xiStar + 1))]
      rw [abs_le]; constructor <;> nlinarith [hy.1, hy.2]
    exact Real.cosh_le_cosh.mpr h1
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.sinh) (f' := Real.cosh)
    (fun y _ => (Real.hasDerivAt_sinh y).hasDerivWithinAt) hb
    (show π * xiStar ∈ Icc (π * xiStar) (π * x) from ⟨le_rfl, by nlinarith⟩)
    (show π * x ∈ Icc (π * xiStar) (π * x) from ⟨by nlinarith, le_rfl⟩)
  have h1 : 0 ≤ Real.sinh (π * x) - 1 := by
    have := one_lt_sinh_of_gt hx
    linarith
  have h2 : 0 ≤ π * x - π * xiStar := by nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sinh_pi_xiStar, abs_of_nonneg h1, abs_of_nonneg h2] at h
  nlinarith


/-- `Dlow = √(2√2π)`. -/
noncomputable def Dlow : ℝ := √(2 * √2 * π)

lemma Dlow_pos : 0 < Dlow := by
  unfold Dlow; apply Real.sqrt_pos.mpr
  have := Real.pi_pos; have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2); positivity

lemma Dx_ge {x : ℝ} (hx : xiStar < x) : Dlow * √(x - xiStar) ≤ Dx x := by
  have h := Dx_sq_ge hx
  have hD := Dx_pos hx
  unfold Dlow
  rw [← Real.sqrt_mul (by have := Real.pi_pos; have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2); positivity)]
  calc √(2 * √2 * π * (x - xiStar)) ≤ √(Dx x ^ 2) := Real.sqrt_le_sqrt (by
        have := Dx_sq_ge hx; nlinarith)
    _ = Dx x := Real.sqrt_sq hD.le

/-- `k = √(1 - 1/S₁²)`. -/
noncomputable def kc : ℝ := √(1 - 1 / S1c ^ 2)

lemma kc_pos : 0 < kc := by
  unfold kc
  apply Real.sqrt_pos.mpr
  have h := one_lt_S1c
  have : 1 / S1c ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  linarith

lemma Dx_ge_large {x : ℝ} (hx : xiStar < x) (hr : 1 ≤ x - xiStar) : kc * Real.sinh (π * x) ≤ Dx x := by
  have hs := S1c_le_sinh hr
  have h1 := one_lt_S1c
  have hs1 : 1 < Real.sinh (π * x) := one_lt_sinh_of_gt hx
  have hD := Dx_pos hx
  unfold kc
  have hq : 1 - 1 / S1c ^ 2 ≤ 1 - 1 / Real.sinh (π * x) ^ 2 := by
    have : 1 / Real.sinh (π * x) ^ 2 ≤ 1 / S1c ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) hs 2)
    linarith
  have hD2 : Dx x ^ 2 = Real.sinh (π * x) ^ 2 * (1 - 1 / Real.sinh (π * x) ^ 2) := by
    rw [Dx_sq hx]; field_simp
  calc √(1 - 1 / S1c ^ 2) * Real.sinh (π * x) ≤ √(1 - 1 / Real.sinh (π * x) ^ 2) * Real.sinh (π * x) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq) (by linarith)
    _ = √(Real.sinh (π * x) ^ 2 * (1 - 1 / Real.sinh (π * x) ^ 2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]; ring
    _ = Dx x := by rw [← hD2, Real.sqrt_sq hD.le]

/-- Constants for `τ'` and `τ''`. -/
noncomputable def KA : ℝ := 2 * S1c / Dlow + 2 / kc
noncomputable def KB : ℝ := 2 * π * C1c / Dlow ^ 3 + 4 * π / kc ^ 3

lemma KA_pos : 0 < KA := by
  unfold KA
  have := Dlow_pos; have := kc_pos; have := one_lt_S1c
  positivity

lemma KB_pos : 0 < KB := by
  unfold KB
  have := Dlow_pos; have := kc_pos
  have : 0 < C1c := Real.cosh_pos _
  have := Real.pi_pos
  positivity

lemma tx_nonneg {x : ℝ} (hx : xiStar < x) : 0 ≤ tx x := by
  unfold tx
  have := one_lt_sinh_of_gt hx; have := Dx_pos hx
  positivity

lemma tx_le {x : ℝ} (hx : xiStar < x) : tx x ≤ KA / √(min (x - xiStar) 1) := by
  have hr0 : 0 < x - xiStar := sub_pos.mpr hx
  have hs1 : 1 < Real.sinh (π * x) := one_lt_sinh_of_gt hx
  have hD := Dx_pos hx
  have hKA := KA_pos
  by_cases hr : x - xiStar ≤ 1
  · rw [min_eq_left hr]
    have hlow := Dx_ge hx
    have hS := sinh_le_S1 hr
    have hsq : 0 < √(x - xiStar) := Real.sqrt_pos.mpr hr0
    have hDl := Dlow_pos
    unfold tx
    have h1 : 2 * Real.sinh (π * x) / Dx x ≤ 2 * S1c / (Dlow * √(x - xiStar)) := by
      apply div_le_div₀ (by have := one_lt_S1c; linarith) (by linarith) (by positivity) hlow
    refine h1.trans ?_
    unfold KA
    rw [div_mul_eq_div_div]
    have : 0 ≤ 2 / kc := by have := kc_pos; positivity
    have hh : 2 * S1c / Dlow / √(x - xiStar) ≤ (2 * S1c / Dlow + 2 / kc) / √(x - xiStar) :=
      div_le_div_of_nonneg_right (by linarith) hsq.le
    exact hh
  · push Not at hr
    rw [min_eq_right hr.le, Real.sqrt_one, div_one]
    have hlarge := Dx_ge_large hx hr.le
    have hk := kc_pos
    unfold tx
    have h1 : 2 * Real.sinh (π * x) / Dx x ≤ 2 / kc := by
      rw [div_le_div_iff₀ hD hk]
      nlinarith
    unfold KA
    have : 0 ≤ 2 * S1c / Dlow := by have := Dlow_pos; have := one_lt_S1c; positivity
    linarith

lemma abs_txx_le {x : ℝ} (hx : xiStar < x) :
    |txx x| ≤ KB / (min (x - xiStar) 1 * √(min (x - xiStar) 1)) := by
  have hr0 : 0 < x - xiStar := sub_pos.mpr hx
  have hs1 : 1 < Real.sinh (π * x) := one_lt_sinh_of_gt hx
  have hD := Dx_pos hx
  have hc : 0 < Real.cosh (π * x) := Real.cosh_pos _
  have hpi := Real.pi_pos
  have hKB := KB_pos
  unfold txx
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * π * Real.cosh (π * x)),
    abs_of_pos (by positivity : 0 < Dx x ^ 3)]
  by_cases hr : x - xiStar ≤ 1
  · rw [min_eq_left hr]
    have hlow := Dx_ge hx
    have hC := cosh_le_C1 hx hr
    have hsq : 0 < √(x - xiStar) := Real.sqrt_pos.mpr hr0
    have hDl := Dlow_pos
    have hr32 : (Dlow * √(x - xiStar)) ^ 3 = Dlow ^ 3 * ((x - xiStar) * √(x - xiStar)) := by
      rw [mul_pow]
      have : √(x - xiStar) ^ 3 = (x - xiStar) * √(x - xiStar) := by
        rw [pow_succ, Real.sq_sqrt hr0.le]
      rw [this]
    have h1 : 2 * π * Real.cosh (π * x) / Dx x ^ 3 ≤
        2 * π * C1c / (Dlow * √(x - xiStar)) ^ 3 := by
      apply div_le_div₀ (by have : 0 < C1c := Real.cosh_pos _; positivity) (by nlinarith) (by positivity)
        (pow_le_pow_left₀ (by positivity) hlow 3)
    refine h1.trans ?_
    rw [hr32]
    unfold KB
    rw [show 2 * π * C1c / (Dlow ^ 3 * ((x - xiStar) * √(x - xiStar))) =
      (2 * π * C1c / Dlow ^ 3) / ((x - xiStar) * √(x - xiStar)) by field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ 4 * π / kc ^ 3 := by have := kc_pos; positivity
    linarith
  · push Not at hr
    rw [min_eq_right hr.le, Real.sqrt_one, mul_one, div_one]
    have hlarge := Dx_ge_large hx hr.le
    have hk := kc_pos
    have hc2 : Real.cosh (π * x) ≤ 2 * Real.sinh (π * x) := by
      have : Real.cosh (π * x) ^ 2 = Real.sinh (π * x) ^ 2 + 1 := by nlinarith [Real.cosh_sq (π * x)]
      nlinarith
    have h1 : 2 * π * Real.cosh (π * x) / Dx x ^ 3 ≤ 4 * π / kc ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : (kc * Real.sinh (π * x)) ^ 3 ≤ Dx x ^ 3 := pow_le_pow_left₀ (by positivity) hlarge 3
      have h4 : 2 * π * Real.cosh (π * x) ≤ 4 * π * Real.sinh (π * x) := by nlinarith
      have h5 : Real.sinh (π * x) ≤ Real.sinh (π * x) ^ 3 := by
        have : 1 ≤ Real.sinh (π * x) ^ 2 := by nlinarith
        nlinarith
      calc 2 * π * Real.cosh (π * x) * kc ^ 3 ≤ 4 * π * Real.sinh (π * x) * kc ^ 3 :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
        _ ≤ 4 * π * Real.sinh (π * x) ^ 3 * kc ^ 3 := by
            have : 0 ≤ 4 * π * kc ^ 3 := by positivity
            nlinarith
        _ = 4 * π * (kc * Real.sinh (π * x)) ^ 3 := by ring
        _ ≤ 4 * π * Dx x ^ 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
    unfold KB
    have : 0 ≤ 2 * π * C1c / Dlow ^ 3 := by
      have : 0 < C1c := Real.cosh_pos _
      have := Dlow_pos; positivity
    linarith


lemma Dx_sq_le {x : ℝ} (hx : xiStar < x) (hr : x - xiStar ≤ 1) :
    Dx x ^ 2 ≤ C1c * π * (S1c + 1) * (x - xiStar) := by
  have h1 := sinh_sub_one_le hx hr
  have h2 := sinh_le_S1 hr
  have h3 := one_lt_sinh_of_gt hx
  rw [Dx_sq hx]
  have hC : 0 < C1c := Real.cosh_pos _
  have hpi := Real.pi_pos
  have hr0 : 0 < x - xiStar := sub_pos.mpr hx
  have h4 : 0 ≤ C1c * π * (x - xiStar) := by positivity
  calc Real.sinh (π * x) ^ 2 - 1 = (Real.sinh (π * x) - 1) * (Real.sinh (π * x) + 1) := by ring
    _ ≤ (C1c * π * (x - xiStar)) * (S1c + 1) :=
        mul_le_mul h1 (by linarith) (by linarith) h4
    _ = _ := by ring

lemma Dx_le_sqrt {x : ℝ} (hx : xiStar < x) (hr : x - xiStar ≤ 1) :
    Dx x ≤ √(C1c * π * (S1c + 1)) * √(x - xiStar) := by
  rw [← Real.sqrt_mul (by have : 0 < C1c := Real.cosh_pos _
                          have := Real.pi_pos; have := one_lt_S1c; positivity)]
  calc Dx x = √(Dx x ^ 2) := (Real.sqrt_sq (Dx_pos hx).le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Dx_sq_le hx hr)

lemma exp_tau_le {x : ℝ} (hx : xiStar < x) :
    Real.exp (-((π / 2) * tauOfX x)) ≤ 3 * Real.exp (-(π * x)) := by
  have h := xT_le (tauOfX x)
  rw [xT_tauOfX hx, abs_of_nonneg (tauOfX_nonneg hx)] at h
  have hpi := Real.pi_pos
  have h2 : π * x ≤ Real.log 3 + (π / 2) * tauOfX x := by
    have := mul_le_mul_of_nonneg_left h hpi.le
    have e : π * (Real.log 3 / π + tauOfX x / 2) = Real.log 3 + (π / 2) * tauOfX x := by
      field_simp
    linarith
  calc Real.exp (-((π / 2) * tauOfX x)) = Real.exp (-(π * x)) * Real.exp (π * x - (π / 2) * tauOfX x) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(π * x)) * 3 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        calc Real.exp (π * x - (π / 2) * tauOfX x) ≤ Real.exp (Real.log 3) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = 3 := Real.exp_log (by norm_num)
    _ = _ := by ring

lemma rpow_neg_half (m : ℝ) (hm : 0 < m) : m ^ (-(1 : ℝ) / 2) = 1 / √m := by
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hm.le]; congr 1; ring

lemma rpow_neg_three_half (m : ℝ) (hm : 0 < m) : m ^ (-(3 : ℝ) / 2) = 1 / (m * √m) := by
  have : m * √m = m ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hm, Real.rpow_one]
  rw [this, one_div, ← Real.rpow_neg hm.le]; congr 1; ring

/-- `|thetaOutT τ| ≤ C τ` on `τ ≥ 0` from the derivative bound. -/
lemma abs_thetaOutT_le {C : ℝ} {Θ1 : ℝ → ℝ} (hd : ∀ τ, HasDerivAt thetaOutT (Θ1 τ) τ)
    (hb : ∀ τ : ℝ, 0 ≤ τ → |Θ1 τ| ≤ C) (h0 : thetaOutT 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    |thetaOutT τ| ≤ C * τ := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le (f := thetaOutT) (C := C)
    (fun y _ => (hd y).differentiableAt) (fun y hy => by
      rw [(hd y).deriv, Real.norm_eq_abs]; exact hb y hy) (show (0 : ℝ) ∈ Ici 0 from le_rfl)
    (show τ ∈ Ici (0 : ℝ) from hτ)
  rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hτ] at h
  exact h

/-- **`outerS2`** (`cts:cauchy-dual` Step 2, eq. `cts:theta-deriv`; `cts:smooth-env` (3), first bullet):
the strip bounds on `x ↦ θ_out(y(x))`, `x > ξ_*`, in the combined form `C min(r,1)^{1/2-j} e^{-πx}`.
Class: proved. -/
theorem outerS2 : OuterS2 := by
  obtain ⟨C, hCpos, Θ1, Θ2, hd1, hd2, hb, h0, -, L, hL⟩ := thetaOutT_data
  have hKA := KA_pos
  have hKB := KB_pos
  have hpi := Real.pi_pos
  have hexpb : ∀ τ : ℝ, 0 ≤ τ → Real.exp (-((π / 2) * τ)) ≤ 1 := fun τ hτ =>
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hb1 : ∀ τ : ℝ, 0 ≤ τ → |Θ1 τ| ≤ C := fun τ hτ =>
    (hb τ hτ).1.trans (by nlinarith [hexpb τ hτ])
  set Ds := √(C1c * π * (S1c + 1)) with hDs
  have hDs0 : 0 ≤ Ds := Real.sqrt_nonneg _
  have hth : ∀ y, xiStar < y → HasDerivAt thetaOutX (Θ1 (tauOfX y) * tx y) y := fun y hy =>
    (hd1 (tauOfX y)).scomp y (hasDerivAt_tauOfX hy) |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hth' : ∀ y, xiStar < y → HasDerivAt (deriv thetaOutX)
      (Θ2 (tauOfX y) * tx y ^ 2 + Θ1 (tauOfX y) * txx y) y := by
    intro y hy
    have hev' : ∀ᶠ w in 𝓝 y, xiStar < w := Ioi_mem_nhds hy
    have heq : deriv thetaOutX =ᶠ[𝓝 y] fun w => Θ1 (tauOfX w) * tx w :=
      hev'.mono fun w hw => (hth w hw).deriv
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    have h1 : HasDerivAt (fun w => Θ1 (tauOfX w)) (Θ2 (tauOfX y) * tx y) y :=
      (hd2 (tauOfX y)).scomp y (hasDerivAt_tauOfX hy) |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
    exact (h1.mul (hasDerivAt_tx hy)).congr_deriv (by ring)
  refine ⟨C * (√2 * Ds / π) + 3 * C * KA + 3 * C * (KA ^ 2 + KB) + 3 * C + 1, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hr
    have hr0 : 0 < x - xiStar := sub_pos.mpr hx
    have hτ0 := tauOfX_nonneg hx
    have h1 := abs_thetaOutT_le hd1 hb1 h0 hτ0
    have h2 := tauOfX_le hx
    have h3 := Dx_le_sqrt hx (by linarith)
    have hsq : (x - xiStar) ^ ((1 : ℝ) / 2) = √(x - xiStar) := by
      rw [Real.sqrt_eq_rpow]
    rw [hsq]
    show |thetaOutT (tauOfX x)| ≤ _
    have h4 : tauOfX x ≤ √2 * Ds / π * √(x - xiStar) := by
      calc tauOfX x ≤ √2 * Dx x / π := h2
        _ ≤ √2 * (Ds * √(x - xiStar)) / π := by
            apply div_le_div_of_nonneg_right _ hpi.le
            exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
        _ = _ := by ring
    have hsq0 : 0 ≤ √(x - xiStar) := Real.sqrt_nonneg _
    have hc1 : 0 ≤ C * (√2 * Ds / π) := by positivity
    calc |thetaOutT (tauOfX x)| ≤ C * tauOfX x := h1
      _ ≤ C * (√2 * Ds / π * √(x - xiStar)) := mul_le_mul_of_nonneg_left h4 hCpos.le
      _ = C * (√2 * Ds / π) * √(x - xiStar) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hsq0
        have : 0 ≤ 3 * C * KA := by positivity
        have : 0 ≤ 3 * C * (KA ^ 2 + KB) := by positivity
        linarith
  · intro x hx
    exact ⟨(hth x hx).differentiableAt, (hth' x hx).differentiableAt⟩
  · intro x hx
    have hr0 : 0 < x - xiStar := sub_pos.mpr hx
    have hm : 0 < min (x - xiStar) 1 := lt_min hr0 one_pos
    have hτ0 := tauOfX_nonneg hx
    rw [(hth x hx).deriv, rpow_neg_half _ hm, abs_mul]
    have h1 := (hb _ hτ0).1
    have h2 := exp_tau_le hx
    have h3 := tx_le hx
    have h4 := tx_nonneg hx
    rw [abs_of_nonneg h4]
    have hsm : 0 < √(min (x - xiStar) 1) := Real.sqrt_pos.mpr hm
    have hE := (Real.exp_pos (-(π * x)))
    calc |Θ1 (tauOfX x)| * tx x ≤ (C * (3 * Real.exp (-(π * x)))) * (KA / √(min (x - xiStar) 1)) := by
          apply mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hCpos.le)) h3 h4 (by positivity)
      _ = 3 * C * KA * (1 / √(min (x - xiStar) 1)) * Real.exp (-(π * x)) := by ring
      _ ≤ _ := by
        have : 0 ≤ 1 / √(min (x - xiStar) 1) * Real.exp (-(π * x)) := by positivity
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 3 * C * KA) this,
          mul_nonneg (by positivity : (0:ℝ) ≤ C * (√2 * Ds / π) + 3 * C * (KA ^ 2 + KB) + 3 * C + 1) this]
  · intro x hx
    have hr0 : 0 < x - xiStar := sub_pos.mpr hx
    have hm : 0 < min (x - xiStar) 1 := lt_min hr0 one_pos
    have hm1 : min (x - xiStar) 1 ≤ 1 := min_le_right _ _
    have hτ0 := tauOfX_nonneg hx
    have hD : deriv (deriv thetaOutX) x = Θ2 (tauOfX x) * tx x ^ 2 + Θ1 (tauOfX x) * txx x :=
      (hth' x hx).deriv
    rw [hD, rpow_neg_three_half _ hm]
    have hbb := hb _ hτ0
    have h2 := exp_tau_le hx
    have h3 := tx_le hx
    have h4 := tx_nonneg hx
    have h5 := abs_txx_le hx
    set m := min (x - xiStar) 1 with hmdef
    have hsm : 0 < √m := Real.sqrt_pos.mpr hm
    have hsm1 : √m ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hm1
    have hE := Real.exp_pos (-(π * x))
    have hCe : C * Real.exp (-((π / 2) * tauOfX x)) ≤ C * (3 * Real.exp (-(π * x))) :=
      mul_le_mul_of_nonneg_left h2 hCpos.le
    have htx2 : tx x ^ 2 ≤ KA ^ 2 / (m * √m) := by
      have : tx x ^ 2 ≤ (KA / √m) ^ 2 := pow_le_pow_left₀ h4 h3 2
      refine this.trans ?_
      rw [div_pow, Real.sq_sqrt hm.le, div_le_div_iff₀ hm (by positivity)]
      have : 0 ≤ KA ^ 2 * m := by positivity
      nlinarith
    have hA : |Θ2 (tauOfX x) * tx x ^ 2| ≤ (C * (3 * Real.exp (-(π * x)))) * (KA ^ 2 / (m * √m)) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ tx x ^ 2)]
      exact mul_le_mul (hbb.2.trans hCe) htx2 (by positivity) (by positivity)
    have hB : |Θ1 (tauOfX x) * txx x| ≤ (C * (3 * Real.exp (-(π * x)))) * (KB / (m * √m)) := by
      rw [abs_mul]
      exact mul_le_mul (hbb.1.trans hCe) h5 (abs_nonneg _) (by positivity)
    have hsum := (abs_add_le _ _).trans (add_le_add hA hB)
    refine hsum.trans ?_
    have hq : 0 ≤ 1 / (m * √m) * Real.exp (-(π * x)) := by positivity
    have e : (C * (3 * Real.exp (-(π * x)))) * (KA ^ 2 / (m * √m)) +
        (C * (3 * Real.exp (-(π * x)))) * (KB / (m * √m)) =
        3 * C * (KA ^ 2 + KB) * (1 / (m * √m) * Real.exp (-(π * x))) := by ring
    rw [e]
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 3 * C * (KA ^ 2 + KB)) hq,
      mul_nonneg (by positivity : (0:ℝ) ≤ C * (√2 * Ds / π) + 3 * C * KA + 3 * C + 1) hq]
  · refine ⟨L, fun x hx => ?_⟩
    have hτ0 := tauOfX_nonneg hx
    have h1 := hL _ hτ0
    have h2 := exp_tau_le hx
    show |thetaOutT (tauOfX x) - L| ≤ _
    have hE := Real.exp_pos (-(π * x))
    have hCe : C * Real.exp (-((π / 2) * tauOfX x)) ≤ C * (3 * Real.exp (-(π * x))) :=
      mul_le_mul_of_nonneg_left h2 hCpos.le
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ C * (√2 * Ds / π) + 3 * C * KA + 3 * C * (KA ^ 2 + KB) + 1) hE.le]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerS2

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
