module

public import FormalResearch.ModularBootstrap.FiveTerm.SchwarzS

/-!
# Boundary values of `S(u) = ∫_0^1 (1 + u t²)^{-1/2} dt` on the cut (FIVE-0 slice 2b)

Real integrals `∫ (1 - c t²)^{-1/2}`, `∫ (c t² - 1)^{-1/2}`, `∫ (1 + c t²)^{-1/2}` by the fundamental theorem of
calculus, hence the exact values of `S` on the positive real axis and on the cut `(-∞,-1)` (with the principal
branch of the integrand there):

* `sInt_pos_real`: `S(c) = arsinh(√c)/√c` for real `c > 0`;
* `sInt_oncut`: `S(-c) = (π/2 - i arsinh √(c-1))/√c` for real `c > 1`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- An interval-integrable derivative from a nonnegative derivative (singular endpoints allowed). -/
lemma intervalIntegrable_of_deriv_nonneg {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ g' x) : IntervalIntegrable g' volume a b := by
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := g) ?_ ?_ ?_
  · simpa [uIcc_of_le hab] using hcont
  · simpa [min_eq_left hab, max_eq_right hab] using hderiv
  · simpa [min_eq_left hab, max_eq_right hab] using hpos

/-- `∫_0^r (1 - c t²)^{-1/2} dt = arcsin(√c r)/√c` for `√c r ≤ 1`. -/
lemma integral_inv_sqrt_one_sub {c : ℝ} (hc : 0 < c) {r : ℝ} (hr0 : 0 ≤ r) (hr : √c * r ≤ 1) :
    (∫ t in (0 : ℝ)..r, 1 / √(1 - c * t ^ 2)) = Real.arcsin (√c * r) / √c ∧
    IntervalIntegrable (fun t : ℝ => 1 / √(1 - c * t ^ 2)) volume 0 r := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  have hcont : ContinuousOn (fun t : ℝ => Real.arcsin (√c * t) / √c) (Icc 0 r) :=
    ((Real.continuous_arcsin.comp (by fun_prop : Continuous fun t : ℝ => √c * t)).div_const _).continuousOn
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) r, HasDerivAt (fun t : ℝ => Real.arcsin (√c * t) / √c)
      (1 / √(1 - c * x ^ 2)) x := by
    intro x hx
    have hw : √c * x < 1 := by nlinarith [hx.2, hsc]
    have hw0 : 0 < √c * x := mul_pos hsc hx.1
    have h1 : HasDerivAt (fun t : ℝ => √c * t) (√c) x := by
      simpa using (hasDerivAt_id x).const_mul (√c)
    have h2 := (Real.hasDerivAt_arcsin (x := √c * x) (by linarith) (by linarith)).comp x h1
    have h3 := h2.div_const (√c)
    refine h3.congr_deriv ?_
    have : (√c * x) ^ 2 = c * x ^ 2 := by rw [mul_pow, Real.sq_sqrt hc.le]
    rw [this]
    field_simp
  have hpos : ∀ x ∈ Ioo (0 : ℝ) r, 0 ≤ 1 / √(1 - c * x ^ 2) := fun x _ => by positivity
  have hint := intervalIntegrable_of_deriv_nonneg hr0 hcont hderiv hpos
  refine ⟨?_, hint⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr0 hcont hderiv hint]
  simp

/-- `∫_{1/√c}^1 (c t² - 1)^{-1/2} dt = arsinh(√(c-1))/√c` for `c > 1`. -/
lemma integral_inv_sqrt_sub_one {c : ℝ} (hc : 1 < c) :
    (∫ t in (1 / √c)..1, 1 / √(c * t ^ 2 - 1)) = Real.arsinh (√(c - 1)) / √c ∧
    IntervalIntegrable (fun t : ℝ => 1 / √(c * t ^ 2 - 1)) volume (1 / √c) 1 := by
  have hc0 : 0 < c := by linarith
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc0
  have hsq : √c * √c = c := Real.mul_self_sqrt hc0.le
  have hle : 1 / √c ≤ 1 := by
    rw [div_le_one hsc]; rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc.le
  have ht0 : c * (1 / √c) ^ 2 - 1 = 0 := by field_simp; nlinarith [hsq]
  have hcont0 : Continuous fun t : ℝ => Real.arsinh (√(c * t ^ 2 - 1)) / √c :=
    (Real.continuous_arsinh.comp (Real.continuous_sqrt.comp
      (by fun_prop : Continuous fun t : ℝ => c * t ^ 2 - 1))).div_const _
  have hcont : ContinuousOn (fun t : ℝ => Real.arsinh (√(c * t ^ 2 - 1)) / √c) (Icc (1 / √c) 1) :=
    hcont0.continuousOn
  have hderiv : ∀ x ∈ Ioo (1 / √c) 1, HasDerivAt (fun t : ℝ => Real.arsinh (√(c * t ^ 2 - 1)) / √c)
      (1 / √(c * x ^ 2 - 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans (by positivity) hx.1
    have hxx : 1 < √c * x := by
      have := hx.1
      rw [div_lt_iff₀ hsc] at this
      linarith
    have hq : 0 < c * x ^ 2 - 1 := by nlinarith [hsq]
    have h1 : HasDerivAt (fun t : ℝ => c * t ^ 2 - 1) (c * (2 * x)) x := by
      have := ((hasDerivAt_pow 2 x).const_mul c).sub_const 1
      simpa using this
    have h2 := h1.sqrt hq.ne'
    have h3 := (Real.hasDerivAt_arsinh (√(c * x ^ 2 - 1))).comp x h2
    have h4 := h3.div_const (√c)
    refine h4.congr_deriv ?_
    have hqq : √(c * x ^ 2 - 1) ^ 2 = c * x ^ 2 - 1 := Real.sq_sqrt hq.le
    have : 1 + √(c * x ^ 2 - 1) ^ 2 = (√c * x) ^ 2 := by
      rw [hqq, mul_pow, Real.sq_sqrt hc0.le]; ring
    rw [this, Real.sqrt_sq (by positivity)]
    have hs : 0 < √(c * x ^ 2 - 1) := Real.sqrt_pos.mpr hq
    field_simp
    rw [Real.sq_sqrt hc0.le]
  have hpos : ∀ x ∈ Ioo (1 / √c) 1, 0 ≤ 1 / √(c * x ^ 2 - 1) := fun x _ => by positivity
  have hint := intervalIntegrable_of_deriv_nonneg hle hcont hderiv hpos
  refine ⟨?_, hint⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont hderiv hint]
  have : √(c * 1 ^ 2 - 1) = √(c - 1) := by ring_nf
  rw [ht0]; simp

/-- `∫_0^1 (1 + c t²)^{-1/2} dt = arsinh(√c)/√c` for `c > 0`. -/
lemma integral_inv_sqrt_one_add {c : ℝ} (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1, 1 / √(1 + c * t ^ 2)) = Real.arsinh (√c) / √c := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  have hderiv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => Real.arsinh (√c * t) / √c)
      (1 / √(1 + c * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => √c * t) (√c) x := by
      simpa using (hasDerivAt_id x).const_mul (√c)
    have h2 := (Real.hasDerivAt_arsinh (√c * x)).comp x h1
    have h3 := h2.div_const (√c)
    refine h3.congr_deriv ?_
    have : 1 + (√c * x) ^ 2 = 1 + c * x ^ 2 := by rw [mul_pow, Real.sq_sqrt hc.le]
    rw [this]
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => 1 / √(1 + c * t ^ 2)) volume 0 1 := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun t _ => ?_)
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x (by
    rwa [uIcc_of_le zero_le_one] at hx)) hint]
  simp

lemma intervalIntegrable_ofReal' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IntervalIntegrable f volume a b) : IntervalIntegrable (fun t => (f t : ℂ)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at h ⊢
  exact h.ofReal

lemma cpow_neg_half_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((1 / √x : ℝ) : ℂ) := by
  have h := Complex.ofReal_cpow hx (-(1 / 2 : ℝ))
  push_cast at h
  rw [← h, Real.rpow_neg hx, ← Real.sqrt_eq_rpow, one_div]

lemma cpow_neg_half_ofReal_nonpos {x : ℝ} (hx : x ≤ 0) :
    (x : ℂ) ^ (-(1 / 2 : ℂ)) = -Complex.I * ((1 / √(-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow_of_nonpos hx]
  have h1 : ((-x : ℂ)) = ((-x : ℝ) : ℂ) := by push_cast; ring
  rw [h1, cpow_neg_half_ofReal_nonneg (by linarith)]
  have h2 : Complex.exp (π * Complex.I * (-(1 / 2 : ℂ))) = -Complex.I := by
    have : (π : ℂ) * Complex.I * (-(1 / 2 : ℂ)) = ((-(π / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [Real.cos_neg, Real.sin_neg]
  rw [h2]; ring

/-- `S(c) = arsinh(√c)/√c` for real `c > 0`. -/
lemma sInt_pos_real {c : ℝ} (hc : 0 < c) : sInt (c : ℂ) = ((Real.arsinh (√c) / √c : ℝ) : ℂ) := by
  unfold sInt
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have : ∀ t ∈ uIcc (0 : ℝ) 1, (1 + (c : ℂ) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      ((1 / √(1 + c * t ^ 2) : ℝ) : ℂ) := by
    intro t _
    have : (1 + (c : ℂ) * (t : ℂ) ^ 2) = ((1 + c * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact cpow_neg_half_ofReal_nonneg (by positivity)
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_ofReal, integral_inv_sqrt_one_add hc]

/-- `S(-c) = (π/2 - i arsinh √(c-1))/√c` for real `c > 1` (principal branch on the cut). -/
lemma sInt_oncut {c : ℝ} (hc : 1 < c) :
    sInt (-(c : ℂ)) = ((π / 2 / √c : ℝ) : ℂ) - Complex.I * ((Real.arsinh (√(c - 1)) / √c : ℝ) : ℂ) := by
  have hc0 : 0 < c := by linarith
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc0
  have hsq : √c * √c = c := Real.mul_self_sqrt hc0.le
  set t0 : ℝ := 1 / √c with ht0
  have ht0pos : 0 < t0 := by positivity
  have hle : t0 ≤ 1 := by
    rw [ht0, div_le_one hsc]; rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc.le
  have h1 := integral_inv_sqrt_one_sub (c := c) hc0 (r := t0) ht0pos.le (by rw [ht0]; field_simp; exact le_refl _)
  have h2 := integral_inv_sqrt_sub_one hc
  unfold sInt
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have e1 : ∀ t ∈ uIcc (0 : ℝ) t0, (1 + (-(c : ℂ)) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      ((1 / √(1 - c * t ^ 2) : ℝ) : ℂ) := by
    intro t ht
    rw [uIcc_of_le ht0pos.le] at ht
    have hnn : 0 ≤ 1 - c * t ^ 2 := by
      have : c * t ^ 2 ≤ c * t0 ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hc0.le
        exact pow_le_pow_left₀ ht.1 ht.2 2
      have : c * t0 ^ 2 = 1 := by rw [ht0]; field_simp; nlinarith [hsq]
      linarith
    have : (1 + (-(c : ℂ)) * (t : ℂ) ^ 2) = ((1 - c * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact cpow_neg_half_ofReal_nonneg hnn
  have e2 : ∀ t ∈ uIcc t0 1, (1 + (-(c : ℂ)) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      -Complex.I * ((1 / √(c * t ^ 2 - 1) : ℝ) : ℂ) := by
    intro t ht
    rw [uIcc_of_le hle] at ht
    have hnp : 1 - c * t ^ 2 ≤ 0 := by
      have : c * t0 ^ 2 ≤ c * t ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hc0.le
        exact pow_le_pow_left₀ ht0pos.le ht.1 2
      have : c * t0 ^ 2 = 1 := by rw [ht0]; field_simp; nlinarith [hsq]
      linarith
    have : (1 + (-(c : ℂ)) * (t : ℂ) ^ 2) = ((1 - c * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, cpow_neg_half_ofReal_nonpos hnp]
    have : -(1 - c * t ^ 2) = c * t ^ 2 - 1 := by ring
    rw [this]
  have hI1 : IntervalIntegrable (fun t : ℝ => (((1 / √(1 - c * t ^ 2) : ℝ) : ℂ))) volume 0 t0 :=
    intervalIntegrable_ofReal' ht0pos.le h1.2
  have hI2 : IntervalIntegrable (fun t : ℝ => (-Complex.I * ((1 / √(c * t ^ 2 - 1) : ℝ) : ℂ))) volume t0 1 :=
    (intervalIntegrable_ofReal' hle h2.2).const_mul _
  set F : ℝ → ℂ := fun t => (1 + (-(c : ℂ)) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hF
  have hF1 : IntervalIntegrable F volume 0 t0 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0pos.le]
    exact IntegrableOn.congr_fun ((intervalIntegrable_iff_integrableOn_Icc_of_le ht0pos.le).mp hI1)
      (fun t ht => (e1 t (by rwa [uIcc_of_le ht0pos.le])).symm) measurableSet_Icc
  have hF2 : IntervalIntegrable F volume t0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact IntegrableOn.congr_fun ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hI2)
      (fun t ht => (e2 t (by rwa [uIcc_of_le hle])).symm) measurableSet_Icc
  rw [← intervalIntegral.integral_add_adjacent_intervals hF1 hF2,
    intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, h1.1, h2.1]
  have hsct : √c * t0 = 1 := by rw [ht0]; field_simp
  rw [hsct, Real.arcsin_one]
  push_cast
  ring

/-! ### Uniform integrability near the cut -/

/-- `∫_{r-h}^{r+h} |t - r|^{-1/2} dt = 4 √h`, and the integrand is interval integrable. -/
lemma integral_abs_rpow (r : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    IntervalIntegrable (fun t : ℝ => |t - r| ^ (-(1 / 2 : ℝ))) volume (r - h) (r + h) ∧
    (∫ t in (r - h)..(r + h), |t - r| ^ (-(1 / 2 : ℝ))) = 4 * √h := by
  have hI : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 h :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hval : (∫ x in (0 : ℝ)..h, x ^ (-(1 / 2 : ℝ))) = 2 * √h := by
    rw [integral_rpow (Or.inl (by norm_num))]
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
    ring
  have hR1 : IntervalIntegrable (fun t : ℝ => (t - r) ^ (-(1 / 2 : ℝ))) volume r (r + h) := by
    have := hI.comp_sub_right r
    simpa [add_comm] using this
  have hL1 : IntervalIntegrable (fun t : ℝ => (r - t) ^ (-(1 / 2 : ℝ))) volume (r - h) r := by
    have := hI.comp_sub_left r
    simpa using this.symm
  have eR : ∀ t ∈ uIcc r (r + h), |t - r| ^ (-(1 / 2 : ℝ)) = (t - r) ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    rw [abs_of_nonneg (by linarith [ht.1])]
  have eL : ∀ t ∈ uIcc (r - h) r, |t - r| ^ (-(1 / 2 : ℝ)) = (r - t) ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
  have hR : IntervalIntegrable (fun t : ℝ => |t - r| ^ (-(1 / 2 : ℝ))) volume r (r + h) :=
    hR1.congr (fun t ht => (eR t (uIoc_subset_uIcc ht)).symm)
  have hL : IntervalIntegrable (fun t : ℝ => |t - r| ^ (-(1 / 2 : ℝ))) volume (r - h) r :=
    hL1.congr (fun t ht => (eL t (uIoc_subset_uIcc ht)).symm)
  refine ⟨hL.trans hR, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hL hR,
    intervalIntegral.integral_congr eL, intervalIntegral.integral_congr eR]
  have h1 : (∫ t in (r - h)..r, (r - t) ^ (-(1 / 2 : ℝ))) = 2 * √h := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) r]
    simpa using hval
  have h2 : (∫ t in r..(r + h), (t - r) ^ (-(1 / 2 : ℝ))) = 2 * √h := by
    rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) r]
    simpa using hval
  rw [h1, h2]; ring

/-- Pointwise majorant `‖(1 + v t²)^{-1/2}‖ ≤ c^{-1/4} |t - c^{-1/2}|^{-1/2}`, `c = -Re v`, for (`Re v < 0`). -/
lemma norm_sIntegrand_le {v : ℂ} (hc : 0 < -v.re) {t : ℝ} (ht : 0 ≤ t)
    (htr : t ≠ 1 / √(-v.re)) :
    ‖(1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤
      (-v.re) ^ (-(1 / 4 : ℝ)) * |t - 1 / √(-v.re)| ^ (-(1 / 2 : ℝ)) := by
  set c : ℝ := -v.re with hcdef
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  have hsq : √c * √c = c := Real.mul_self_sqrt hc.le
  set r : ℝ := 1 / √c with hr
  have hrpos : 0 < r := by positivity
  have hr2 : c * r ^ 2 = 1 := by rw [hr]; field_simp; nlinarith [hsq]
  have hre : (1 + v * (t : ℂ) ^ 2).re = 1 - c * t ^ 2 := by
    simp [Complex.mul_re, pow_two, hcdef]
  have hfac : 1 - c * t ^ 2 = c * (r - t) * (r + t) := by nlinarith [hr2]
  have htr' : 0 < |t - r| := abs_pos.mpr (sub_ne_zero.mpr htr)
  have hlow : √c * |t - r| ≤ |1 - c * t ^ 2| := by
    rw [hfac, abs_mul, abs_mul, abs_of_pos hc, abs_of_nonneg (by linarith : 0 ≤ r + t), abs_sub_comm r t]
    have : √c * |t - r| = c * r * |t - r| := by
      have : c * r = √c := by rw [hr]; field_simp; nlinarith [hsq]
      rw [this]
    rw [this]
    have h1 : c * r * |t - r| ≤ c * |t - r| * (r + t) := by nlinarith [mul_nonneg hc.le htr'.le, mul_nonneg (mul_nonneg hc.le htr'.le) ht]
    nlinarith [h1]
  have hpos : 0 < √c * |t - r| := mul_pos hsc htr'
  have hnorm : |1 - c * t ^ 2| ≤ ‖1 + v * (t : ℂ) ^ 2‖ := by
    rw [← hre]; exact Complex.abs_re_le_norm _
  have hz : 1 + v * (t : ℂ) ^ 2 ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith [hlow, hpos, abs_nonneg (1 - c * t ^ 2)]
  have e1 : ‖(1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ = ‖1 + v * (t : ℂ) ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
    have := Complex.norm_cpow_of_ne_zero hz (-(1 / 2 : ℂ))
    simpa using this
  rw [e1]
  calc ‖1 + v * (t : ℂ) ^ 2‖ ^ (-(1 / 2 : ℝ)) ≤ (√c * |t - r|) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos (hlow.trans hnorm) (by norm_num)
    _ = c ^ (-(1 / 4 : ℝ)) * |t - r| ^ (-(1 / 2 : ℝ)) := by
        rw [Real.mul_rpow hsc.le htr'.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hc.le]
        norm_num

/-- The principal `w ↦ w^{-1/2}` is continuous on the closed upper half plane at negative reals. -/
lemma continuousWithinAt_cpow_neg_half {w₀ : ℂ} (hre : w₀.re < 0) (him : w₀.im = 0) :
    ContinuousWithinAt (fun w : ℂ => w ^ (-(1 / 2 : ℂ))) {w : ℂ | 0 ≤ w.im} w₀ := by
  have hw0 : w₀ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hlog : ContinuousWithinAt (fun w : ℂ => Complex.log w) {w : ℂ | 0 ≤ w.im} w₀ := by
    have h1 : ContinuousWithinAt (fun w : ℂ => ((Real.log ‖w‖ : ℝ) : ℂ)) {w : ℂ | 0 ≤ w.im} w₀ :=
      (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        ((Real.continuousAt_log (norm_ne_zero_iff.mpr hw0)).comp_continuousWithinAt
          continuous_norm.continuousWithinAt))
    have h2 : ContinuousWithinAt (fun w : ℂ => ((Complex.arg w : ℝ) : ℂ) * Complex.I)
        {w : ℂ | 0 ≤ w.im} w₀ :=
      ((Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (Complex.continuousWithinAt_arg_of_re_neg_of_im_zero hre him))).mul continuousWithinAt_const
    refine (h1.add h2).congr (fun w _ => ?_) ?_
    · rw [Complex.log]; rfl
    · rw [Complex.log]; rfl
  have hne : ∀ᶠ w in 𝓝[{w : ℂ | 0 ≤ w.im}] w₀, w ≠ 0 := by
    have : ∀ᶠ w in 𝓝 w₀, w ≠ 0 := isOpen_ne.mem_nhds hw0
    exact mem_nhdsWithin_of_mem_nhds this
  have hexp : ContinuousWithinAt (fun w : ℂ => Complex.exp (Complex.log w * (-(1 / 2 : ℂ))))
      {w : ℂ | 0 ≤ w.im} w₀ :=
    (Complex.continuous_exp.continuousAt.comp_continuousWithinAt (hlog.mul continuousWithinAt_const))
  refine hexp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hne] with w hw
    exact Complex.cpow_def_of_ne_zero hw _
  · exact Complex.cpow_def_of_ne_zero hw0 _

lemma measurable_sIntegrand (v : ℂ) :
    Measurable fun t : ℝ => (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
  have : Measurable fun t : ℝ => 1 + v * (t : ℂ) ^ 2 := by fun_prop
  exact this.pow_const _

/-- The integrand of `S(v)` is integrable on `[0,1]` as soon as `Re v < 0`. -/
lemma integrableOn_sIntegrand {v : ℂ} (hc : 0 < -v.re) :
    IntegrableOn (fun t : ℝ => (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) (Icc (0 : ℝ) 1) := by
  set c : ℝ := -v.re with hcdef
  set r : ℝ := 1 / √c with hr
  have hrpos : 0 < r := by positivity
  have hI := (integral_abs_rpow r (h := r + 1) (by linarith)).1
  have hI' : IntegrableOn (fun t : ℝ => c ^ (-(1 / 4 : ℝ)) * |t - r| ^ (-(1 / 2 : ℝ)))
      (Icc (r - (r + 1)) (r + (r + 1))) := by
    have := hI.const_mul (c ^ (-(1 / 4 : ℝ)))
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp this
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (r - (r + 1)) (r + (r + 1)) := by
    intro t ht; constructor <;> linarith [ht.1, ht.2]
  refine Integrable.mono' (hI'.mono_set hsub) (measurable_sIntegrand v).aestronglyMeasurable ?_
  have hne : ∀ᵐ t : ℝ ∂(volume.restrict (Icc (0 : ℝ) 1)), t ≠ r :=
    ae_restrict_of_ae ((Set.countable_singleton r).ae_notMem volume)
  filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t htr ht
  exact norm_sIntegrand_le hc ht.1 htr

/-- Inner (singular) part: the integral over a small set around the singular point is small. -/
lemma norm_setIntegral_sIntegrand_le {v : ℂ} (hc : 0 < -v.re) {t₀ η : ℝ} (hη : 0 ≤ η)
    (hr : |1 / √(-v.re) - t₀| ≤ η) {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Ioo (t₀ - η) (t₀ + η) ∩ Ici 0) :
    ‖∫ t in A, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤
      (-v.re) ^ (-(1 / 4 : ℝ)) * (4 * √(2 * η)) := by
  set c : ℝ := -v.re with hcdef
  set r : ℝ := 1 / √c with hr'
  have hη2 : 0 ≤ 2 * η := by linarith
  have hI := integral_abs_rpow r hη2
  set β : ℝ → ℝ := fun t => c ^ (-(1 / 4 : ℝ)) * |t - r| ^ (-(1 / 2 : ℝ)) with hβ
  have hβint : IntegrableOn β (Ioc (r - 2 * η) (r + 2 * η)) := by
    have := hI.1.const_mul (c ^ (-(1 / 4 : ℝ)))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp this)
  have hsubA : A ⊆ Ioc (r - 2 * η) (r + 2 * η) := by
    intro t ht
    have h1 := (hAsub ht).1
    have h2 := abs_le.mp hr
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hne : ∀ᵐ t : ℝ ∂(volume.restrict A), t ≠ r :=
    ae_restrict_of_ae ((Set.countable_singleton r).ae_notMem volume)
  have hbd : ∀ᵐ t : ℝ ∂(volume.restrict A),
      ‖(1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ β t := by
    filter_upwards [hne, ae_restrict_mem hA] with t htr ht
    exact norm_sIntegrand_le hc (hAsub ht).2 htr
  calc ‖∫ t in A, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ ∫ t in A, β t :=
        norm_integral_le_of_norm_le (hβint.mono_set hsubA) hbd
    _ ≤ ∫ t in Ioc (r - 2 * η) (r + 2 * η), β t :=
        setIntegral_mono_set hβint (Eventually.of_forall (fun t => by simp only [hβ]; positivity))
          (Eventually.of_forall hsubA)
    _ = c ^ (-(1 / 4 : ℝ)) * (4 * √(2 * η)) := by
        rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul]
        have := hI.2
        rw [show r - 2 * η = r - 2 * η from rfl] at this
        rw [this]

/-- **Continuity of `S` up to the cut.**  `S` is continuous within the closed upper half plane at every real
`v₀ < 0` (in particular on the cut `(-∞,-1]`, where `S(v₀)` is the principal-branch integral). -/
theorem continuousWithinAt_sInt_cut {v₀ : ℂ} (him : v₀.im = 0) (hre : v₀.re < 0) :
    ContinuousWithinAt sInt {v : ℂ | 0 ≤ v.im} v₀ := by
  set S : Set ℂ := {v : ℂ | 0 ≤ v.im} with hS
  set c₀ : ℝ := -v₀.re with hc₀
  have hc₀pos : 0 < c₀ := by rw [hc₀]; linarith
  set t₀ : ℝ := 1 / √c₀ with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  set r : ℂ → ℝ := fun v => 1 / √(-v.re) with hrdef
  have hr_cont : ContinuousAt r v₀ := by
    refine ContinuousAt.div continuousAt_const ?_ ?_
    · exact (Real.continuous_sqrt.continuousAt).comp
        ((continuous_neg.comp Complex.continuous_re).continuousAt)
    · exact (Real.sqrt_pos.mpr hc₀pos).ne'
  unfold ContinuousWithinAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K : ℝ := (c₀ / 2) ^ (-(1 / 4 : ℝ)) with hK
  have hKpos : 0 < K := by positivity
  set η : ℝ := (ε / (32 * K)) ^ 2 / 2 with hη
  have hηpos : 0 < η := by positivity
  have hsqη : √(2 * η) = ε / (32 * K) := by
    rw [show 2 * η = (ε / (32 * K)) ^ 2 by rw [hη]; ring]
    exact Real.sqrt_sq (by positivity)
  -- neighbourhood of `v₀` on which all the bounds hold
  have hnbhd : ∀ᶠ v in 𝓝 v₀, c₀ / 2 < -v.re ∧ |r v - t₀| < η / 2 := by
    have h1 : ∀ᶠ v in 𝓝 v₀, c₀ / 2 < -v.re := by
      have : ContinuousAt (fun v : ℂ => -v.re) v₀ := (continuous_neg.comp Complex.continuous_re).continuousAt
      exact this.eventually (lt_mem_nhds (by show c₀ / 2 < -v₀.re; rw [← hc₀]; linarith))
    have h2 : ∀ᶠ v in 𝓝 v₀, |r v - t₀| < η / 2 := by
      have : ContinuousAt (fun v => |r v - t₀|) v₀ := (hr_cont.sub continuousAt_const).abs
      have h0 : |r v₀ - t₀| < η / 2 := by
        have : r v₀ = t₀ := rfl
        rw [this]; simp; linarith
      exact this.eventually (gt_mem_nhds h0)
    exact h1.and h2
  have hnbhd' : ∀ᶠ v in 𝓝[S] v₀, c₀ / 2 < -v.re ∧ |r v - t₀| < η / 2 :=
    mem_nhdsWithin_of_mem_nhds hnbhd
  -- the splitting sets
  set J : Set ℝ := Ioo (t₀ - η) (t₀ + η) with hJ
  set B : Set ℝ := Icc (0 : ℝ) 1 \ J with hB
  have hJmeas : MeasurableSet J := measurableSet_Ioo
  have hBmeas : MeasurableSet B := measurableSet_Icc.diff hJmeas
  -- outer part: dominated convergence
  set M : ℝ := K * (η / 2) ^ (-(1 / 2 : ℝ)) with hM
  have hBfin : volume B ≠ ⊤ := by
    refine ne_top_of_le_ne_top (by simp) (measure_mono (sdiff_subset : B ⊆ Icc (0 : ℝ) 1))
  have hOuter : Tendsto (fun v : ℂ => ∫ t in B, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) (𝓝[S] v₀)
      (𝓝 (∫ t in B, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict B) (fun _ => M)
      (Eventually.of_forall (fun v => (measurable_sIntegrand v).aestronglyMeasurable)) ?_ ?_ ?_
    · filter_upwards [hnbhd'] with v hv
      refine ae_restrict_of_forall_mem hBmeas (fun t ht => ?_)
      have hc : 0 < -v.re := by linarith [hv.1]
      have ht0 : 0 ≤ t := ht.1.1
      have htJ : ¬ (t₀ - η < t ∧ t < t₀ + η) := fun h => ht.2 h
      have hdist : η / 2 ≤ |t - r v| := by
        have h1 := abs_lt.mp hv.2
        rcases le_or_gt t (t₀ - η) with h | h
        · rw [abs_of_nonpos (by linarith [h1.1, h1.2])]; linarith [h1.1, h1.2]
        · have : t₀ + η ≤ t := by
            by_contra hh; push Not at hh; exact htJ ⟨h, hh⟩
          rw [abs_of_nonneg (by linarith [h1.1, h1.2])]; linarith [h1.1, h1.2]
      have htr : t ≠ 1 / √(-v.re) := by
        intro h
        have h' : t = r v := h
        rw [h', sub_self, abs_zero] at hdist
        linarith
      refine (norm_sIntegrand_le hc ht0 htr).trans ?_
      have hK1 : (-v.re) ^ (-(1 / 4 : ℝ)) ≤ K :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hv.1.le (by norm_num)
      have hK2 : |t - 1 / √(-v.re)| ^ (-(1 / 2 : ℝ)) ≤ (η / 2) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hdist (by norm_num)
      calc (-v.re) ^ (-(1 / 4 : ℝ)) * |t - 1 / √(-v.re)| ^ (-(1 / 2 : ℝ))
          ≤ K * (η / 2) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul hK1 hK2 (by positivity) hKpos.le
        _ = M := rfl
    · exact integrableOn_const hBfin
    · refine ae_restrict_of_forall_mem hBmeas (fun t ht => ?_)
      have ht0 : 0 ≤ t := ht.1.1
      have htne : t ≠ t₀ := by
        intro h; apply ht.2; rw [h]; exact ⟨by linarith, by linarith⟩
      have hcts : ContinuousWithinAt (fun v : ℂ => 1 + v * (t : ℂ) ^ 2) S v₀ := by fun_prop
      have hmaps : Set.MapsTo (fun v : ℂ => 1 + v * (t : ℂ) ^ 2) S {w : ℂ | 0 ≤ w.im} := by
        intro v hv
        simp only [hS, Set.mem_ofPred_eq] at hv ⊢
        simp [Complex.mul_im, pow_two]
        nlinarith [mul_nonneg hv (mul_self_nonneg t)]
      have hre1 : (1 + v₀ * (t : ℂ) ^ 2).re = 1 - c₀ * t ^ 2 := by
        simp [Complex.mul_re, pow_two, hc₀, him]
      have him1 : (1 + v₀ * (t : ℂ) ^ 2).im = 0 := by
        simp [Complex.mul_im, pow_two, him]
      have hne0 : 1 - c₀ * t ^ 2 ≠ 0 := by
        intro h
        have : t ^ 2 = t₀ ^ 2 := by
          rw [ht₀]; field_simp; nlinarith [Real.mul_self_sqrt hc₀pos.le]
        exact htne ((pow_left_inj₀ ht0 ht₀pos.le two_ne_zero).mp this)
      rcases lt_or_gt_of_ne hne0 with hneg | hpos
      · have hP := continuousWithinAt_cpow_neg_half (w₀ := 1 + v₀ * (t : ℂ) ^ 2)
          (by rw [hre1]; exact hneg) him1
        exact (ContinuousWithinAt.comp (f := fun v : ℂ => 1 + v * (t : ℂ) ^ 2) hP hcts hmaps).tendsto
      · have hslit : 1 + v₀ * (t : ℂ) ^ 2 ∈ Complex.slitPlane := by
          rw [Complex.mem_slitPlane_iff]; left; rw [hre1]; exact hpos
        have : ContinuousAt (fun w : ℂ => w ^ (-(1 / 2 : ℂ))) (1 + v₀ * (t : ℂ) ^ 2) :=
          continuousAt_cpow_const hslit
        exact (ContinuousAt.comp_continuousWithinAt (f := fun v : ℂ => 1 + v * (t : ℂ) ^ 2)
          this hcts).tendsto
  -- assemble
  have hsplit : ∀ v : ℂ, 0 < -v.re → sInt v =
      (∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) +
      ∫ t in B, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by
    intro v hv
    unfold sInt
    exact (integral_inter_add_sdiff hJmeas (integrableOn_sIntegrand hv)).symm
  have hinner : ∀ v : ℂ, 0 < -v.re → |r v - t₀| ≤ η →
      ‖∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤
        (-v.re) ^ (-(1 / 4 : ℝ)) * (4 * √(2 * η)) := by
    intro v hv hrv
    refine norm_setIntegral_sIntegrand_le hv hηpos.le hrv (measurableSet_Icc.inter hJmeas) ?_
    intro t ht
    exact ⟨ht.2, ht.1.1⟩
  have hout := Metric.tendsto_nhds.mp hOuter (ε / 2) (by positivity)
  filter_upwards [hout, hnbhd'] with v hv1 hv2
  have hcv : 0 < -v.re := by linarith [hv2.1]
  have hrv : |r v - t₀| ≤ η := by linarith [hv2.2]
  have hbound_v : ‖∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ ε / 8 := by
    refine (hinner v hcv hrv).trans ?_
    have hK1 : (-v.re) ^ (-(1 / 4 : ℝ)) ≤ K :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hv2.1.le (by norm_num)
    calc (-v.re) ^ (-(1 / 4 : ℝ)) * (4 * √(2 * η)) ≤ K * (4 * √(2 * η)) :=
          mul_le_mul_of_nonneg_right hK1 (by positivity)
      _ = ε / 8 := by rw [hsqη]; field_simp; ring
  have hbound_0 : ‖∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ ε / 8 := by
    refine (hinner v₀ (by rw [← hc₀]; exact hc₀pos) (by
      have : r v₀ = t₀ := rfl
      rw [this]; simp; exact hηpos.le)).trans ?_
    have hK1 : (-v₀.re) ^ (-(1 / 4 : ℝ)) ≤ K :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [← hc₀]; linarith) (by norm_num)
    calc (-v₀.re) ^ (-(1 / 4 : ℝ)) * (4 * √(2 * η)) ≤ K * (4 * √(2 * η)) :=
          mul_le_mul_of_nonneg_right hK1 (by positivity)
      _ = ε / 8 := by rw [hsqη]; field_simp; ring
  rw [dist_eq_norm] at hv1 ⊢
  rw [hsplit v hcv, hsplit v₀ (by rw [← hc₀]; exact hc₀pos)]
  calc ‖(∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) +
          (∫ t in B, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) -
        ((∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) +
          ∫ t in B, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))‖
      = ‖(∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) -
          (∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) +
          ((∫ t in B, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) -
            ∫ t in B, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))‖ := by ring_nf
    _ ≤ ‖(∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) -
          (∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)))‖ +
        ‖(∫ t in B, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) -
            ∫ t in B, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ := norm_add_le _ _
    _ ≤ (‖∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ +
          ‖∫ t in Icc (0 : ℝ) 1 ∩ J, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖) +
        ‖(∫ t in B, (1 + v * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) -
            ∫ t in B, (1 + v₀ * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ :=
        add_le_add_left (norm_sub_le _ _) _
    _ < ε := by linarith [hbound_v, hbound_0, hv1]

end FormalResearch.ModularBootstrap.FiveTerm
