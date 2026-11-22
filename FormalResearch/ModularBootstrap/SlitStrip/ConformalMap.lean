module

public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The slit-strip conformal map `𝓑(z) = (2π)⁻¹ log((z-1)/(z(z+1)))`

Formalizes the geometry used in `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G
(`vlo:Gap`), paragraph "Slit-strip harmonic measure", and the tip expansion of
`blowup_limit.tex`, Lemma T1 (`bl:T1`).

* `confB`: the map, with the branch `(2π)⁻¹ (log(z-1) - log z - log(z+1))` (principal logarithms,
  so `|Im 𝓑| < 1/2` on the upper half-plane).
* `confB_zero_at_I`: `𝓑(i) = 0`.
* `confB_im_bounds`, `confB_mapsTo`, `confB_injOn`, `confB_surjOn`, `confB_bijOn`:
  `𝓑` is a bijection of the upper half-plane onto the slit strip `D_*`
  (`slitStrip = {|Im b| < 1/2} \ ((-∞,-ξ_*] ∪ [ξ_*,∞))`), and `hasDerivAt_confB`,
  `confBDeriv_ne_zero_of_im_pos` make it conformal.
* `confBDeriv`, `hasDerivAt_confBSlit`: the derivative formula, `confBDeriv_eq_zero_iff`: the critical
  points `1 ± √2`.
* Boundary behaviour (`confB_real_re`, `confB_real_im`, `confB_continuousWithinAt_real`):
  the real intervals map to the strip edges (`Im = ∓1/2`) and to the slits (`Im = 0`),
  and `slitBoundaryMap` is the real part of the boundary values.
* Agreement with the definitions of `EntropyAndDeficit`: `invJacobian_eq_inv_norm_confBDeriv`,
  `confE_fold`, `slitInv_eq_fold`, `poissonKernel_eq_im_inv`.
* Tip expansion `𝓑(σ_* + w) = ξ_* + q w² + o(w²)` with
  `q = √2/(2π σ_*(σ_*²-1))` (`confBSlit_tip_expansion`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap

/-! ### The map and its analytic continuation across the slit `(-1, 0)` -/

/-- The upper half-plane. -/
def upperHalfPlane' : Set ℂ := {z : ℂ | 0 < z.im}

/-- **The conformal map** `𝓑(z) = (2π)⁻¹ log((z-1)/(z(z+1)))` of Lemma G (`vlo:Gap`), with the branch
`(2π)⁻¹ (log(z-1) - log z - log(z+1))`, `log` the principal logarithm.  On the open upper half-plane
`z-1, z, z+1` all lie in the upper half-plane, so this is holomorphic there, and it extends
continuously to the real axis minus `{0, ±1}` (`confB_continuousWithinAt_real`). -/
noncomputable def confB (z : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * (Complex.log (z - 1) - Complex.log z - Complex.log (z + 1))

/-- The analytic continuation of `confB` across the slit `(-1, 0)`:
`(2π)⁻¹ (log(1-z) - log(-z) - log(1+z))`. It is holomorphic on `ℂ \ ((-∞,-1] ∪ [0,∞))`
and agrees with `confB` on the upper half-plane (`confB_eq_confBSlit`); on `(-1,0)` it is
`slitBoundaryMap` (`confBSlit_ofReal`). -/
noncomputable def confBSlit (z : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * (Complex.log (1 - z) - Complex.log (-z) - Complex.log (1 + z))

/-- The derivative `𝓑'(z) = -(z-1+√2)(z-1-√2) / (2π z (z²-1))` of Lemma G. -/
noncomputable def confBDeriv (z : ℂ) : ℂ :=
  -((z - 1 + (√2 : ℝ)) * (z - 1 - (√2 : ℝ))) / (2 * π * z * (z ^ 2 - 1))

/-- The rational function `(z-1)/(z(z+1))` whose logarithm is `2π 𝓑`. -/
noncomputable def confE (z : ℂ) : ℂ := (z - 1) / (z * (z + 1))

/-- The slit strip `D_*`: `{|Im b| < 1/2}` minus the two slits `(-∞,-ξ_*] ∪ [ξ_*,∞)`. -/
def slitStrip : Set ℂ :=
  {b : ℂ | |b.im| < 1 / 2} \ {b : ℂ | b.im = 0 ∧ xiStar ≤ |b.re|}

private lemma pi_ne_zero_C : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'

lemma confB_eq_confBSlit {z : ℂ} (hz : 0 < z.im) : confB z = confBSlit z := by
  unfold confB confBSlit
  have h1 : (z - 1).im = z.im := by simp
  have e1 : Complex.log (1 - z) = Complex.log (z - 1) - π * I := by
    have := arg_neg_eq_arg_sub_pi_of_im_pos (x := z - 1) (by simpa using hz)
    apply Complex.ext
    · rw [Complex.sub_re, Complex.log_re, Complex.log_re, norm_sub_rev]; simp
    · rw [Complex.sub_im, Complex.log_im, Complex.log_im, show 1 - z = -(z - 1) by ring, this]
      simp
  have e2 : Complex.log (-z) = Complex.log z - π * I := by
    have := arg_neg_eq_arg_sub_pi_of_im_pos hz
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, this]
  rw [e1, e2, add_comm 1 z]
  ring

/-! ### Derivative and critical points -/

private lemma sqrt2_sq_C : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- **Derivative formula** of Lemma G for the continuation `confBSlit`, valid wherever
`1-z`, `-z`, `1+z` avoid the closed negative real axis. -/
theorem hasDerivAt_confBSlit {z : ℂ} (h1 : 1 - z ∈ slitPlane) (h2 : -z ∈ slitPlane)
    (h3 : 1 + z ∈ slitPlane) : HasDerivAt confBSlit (confBDeriv z) z := by
  have hz1 : 1 - z ≠ 0 := slitPlane_ne_zero h1
  have hz0 : -z ≠ 0 := slitPlane_ne_zero h2
  have hz2 : 1 + z ≠ 0 := slitPlane_ne_zero h3
  have hz0' : z ≠ 0 := neg_ne_zero.mp hz0
  have hz1' : z - 1 ≠ 0 := by intro h; apply hz1; linear_combination -h
  have d1 : HasDerivAt (fun t : ℂ => Complex.log (1 - t)) ((-1) / (1 - z)) z :=
    ((hasDerivAt_id z).const_sub 1).clog h1
  have d2 : HasDerivAt (fun t : ℂ => Complex.log (-t)) ((-1) / (-z)) z :=
    (hasDerivAt_id z).neg.clog h2
  have d3 : HasDerivAt (fun t : ℂ => Complex.log (1 + t)) (1 / (1 + z)) z :=
    ((hasDerivAt_id z).const_add 1).clog h3
  have hd := (((d1.sub d2).sub d3).const_mul (2 * π : ℂ)⁻¹)
  refine hd.congr_deriv ?_
  unfold confBDeriv
  have hpi := pi_ne_zero_C
  have hzz : z ^ 2 - 1 ≠ 0 := by
    have : z ^ 2 - 1 = (z - 1) * (1 + z) := by ring
    rw [this]; exact mul_ne_zero hz1' hz2
  have hsq := sqrt2_sq_C
  field_simp
  linear_combination (-((1 - z) * (1 + z))) * hsq

/-- On the upper half-plane `confB` has the derivative `confBDeriv`. -/
theorem hasDerivAt_confB {z : ℂ} (hz : 0 < z.im) : HasDerivAt confB (confBDeriv z) z := by
  have hm : ∀ w ∈ upperHalfPlane', 1 - w ∈ slitPlane ∧ -w ∈ slitPlane ∧ 1 + w ∈ slitPlane := by
    intro w hw
    have hw' : 0 < w.im := hw
    refine ⟨?_, ?_, ?_⟩ <;> rw [mem_slitPlane_iff] <;> right <;> simp <;> linarith
  obtain ⟨h1, h2, h3⟩ := hm z hz
  refine (hasDerivAt_confBSlit h1 h2 h3).congr_of_eventuallyEq ?_
  have hopen : IsOpen upperHalfPlane' := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact confB_eq_confBSlit hw

lemma confBDeriv_eq_zero_iff {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ^ 2 - 1 ≠ 0) :
    confBDeriv z = 0 ↔ z = 1 + (√2 : ℝ) ∨ z = 1 - (√2 : ℝ) := by
  unfold confBDeriv
  have hpi := pi_ne_zero_C
  have hden : (2 * π : ℂ) * z * (z ^ 2 - 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hz0) hz1
  rw [div_eq_zero_iff, or_iff_left hden, neg_eq_zero, mul_eq_zero]
  constructor
  · rintro (h | h)
    · right; linear_combination h
    · left; linear_combination h
  · rintro (h | h)
    · right; linear_combination h
    · left; linear_combination h

/-- `confB` is conformal on the upper half-plane: its derivative never vanishes there. -/
lemma confBDeriv_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : confBDeriv z ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz1 : z ^ 2 - 1 ≠ 0 := by
    intro h
    have : (z - 1) * (z + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · have := congrArg Complex.im h; simp at this; linarith
    · have := congrArg Complex.im h; simp at this; linarith
  rw [Ne, confBDeriv_eq_zero_iff hz0 hz1]
  rintro (h | h) <;> (have := congrArg Complex.im h; simp at this; linarith)

/-! ### Branch bounds, `𝓑(i) = 0` and the inverse root -/

private lemma arg_eq_pi_div_two_sub_arctan {w : ℂ} (hw : 0 < w.im) :
    arg w = π / 2 - Real.arctan (w.re / w.im) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw)
  rw [arg_of_im_pos hw]
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : Real.cos (π / 2 - Real.arctan (w.re / w.im)) = w.re / ‖w‖ := by
    rw [Real.cos_pi_div_two_sub, Real.sin_arctan]
    have : 1 + (w.re / w.im) ^ 2 = (‖w‖ / w.im) ^ 2 := by
      rw [div_pow, div_pow, hsq]; field_simp; ring
    rw [this, Real.sqrt_sq (div_nonneg hn.le hw.le)]
    field_simp
  rw [← h1, Real.arccos_cos]
  · linarith [Real.arctan_lt_pi_div_two (w.re / w.im)]
  · linarith [Real.neg_pi_div_two_lt_arctan (w.re / w.im), Real.pi_pos]

lemma confB_im_eq (z : ℂ) :
    (confB z).im = (arg (z - 1) - arg z - arg (z + 1)) / (2 * π) := by
  unfold confB
  have h2pi : ((2 * π : ℂ)⁻¹) = (((2 * π)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [h2pi, Complex.im_ofReal_mul]
  simp only [Complex.sub_im, Complex.log_im]
  ring

/-- On the upper half-plane the imaginary part of `𝓑` lies in `(-1/2, 1/2)`. -/
theorem confB_im_bounds {z : ℂ} (hz : 0 < z.im) :
    -(1 / 2) < (confB z).im ∧ (confB z).im < 1 / 2 := by
  rw [confB_im_eq]
  have h1 : 0 < (z - 1).im := by simpa using hz
  have h3 : 0 < (z + 1).im := by simpa using hz
  rw [arg_eq_pi_div_two_sub_arctan h1, arg_eq_pi_div_two_sub_arctan hz,
    arg_eq_pi_div_two_sub_arctan h3]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im,
    Complex.add_im, sub_zero, add_zero]
  have hpi := Real.pi_pos
  have hmono : Real.arctan ((z.re - 1) / z.im) < Real.arctan (z.re / z.im) :=
    Real.arctan_strictMono (by gcongr; linarith)
  have a1 := Real.arctan_lt_pi_div_two ((z.re - 1) / z.im)
  have a2 := Real.neg_pi_div_two_lt_arctan ((z.re - 1) / z.im)
  have b1 := Real.arctan_lt_pi_div_two (z.re / z.im)
  have b2 := Real.neg_pi_div_two_lt_arctan (z.re / z.im)
  have c1 := Real.arctan_lt_pi_div_two ((z.re + 1) / z.im)
  have c2 := Real.neg_pi_div_two_lt_arctan ((z.re + 1) / z.im)
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

private lemma confE_ne_exp_aux {z : ℂ} (hz : 0 < z.im) : z ≠ 0 ∧ z - 1 ≠ 0 ∧ z + 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;> linarith

/-- `exp (2π 𝓑(z)) = (z-1)/(z(z+1))`. -/
theorem exp_two_pi_mul_confB {z : ℂ} (hz : 0 < z.im) :
    Complex.exp (2 * π * confB z) = confE z := by
  obtain ⟨h0, h1, h2⟩ := confE_ne_exp_aux hz
  have : (2 * π : ℂ) * confB z =
      Complex.log (z - 1) - Complex.log z - Complex.log (z + 1) := by
    unfold confB
    have : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero pi_ne_zero_C
    field_simp
  rw [this, Complex.exp_sub, Complex.exp_sub, Complex.exp_log h1, Complex.exp_log h0,
    Complex.exp_log h2]
  unfold confE; field_simp

/-- If `z` is in the upper half-plane and `exp(2π b) = confE z` with `|Im b| < 1/2`, then
`𝓑(z) = b`. -/
theorem confB_eq_of_confE {z b : ℂ} (hz : 0 < z.im) (hb : |b.im| < 1 / 2)
    (h : confE z = Complex.exp (2 * π * b)) : confB z = b := by
  have h1 : Complex.exp (2 * π * confB z) = Complex.exp (2 * π * b) := by
    rw [exp_two_pi_mul_confB hz, h]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have hpi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero pi_ne_zero_C
  have h2 : confB z = b + n * I := by
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  have h3 := congrArg Complex.im h2
  simp at h3
  have hB := confB_im_bounds hz
  have hn1 : (n : ℝ) < 1 := by
    rw [abs_lt] at hb; linarith [hB.2]
  have hn2 : (-1 : ℝ) < n := by
    rw [abs_lt] at hb; linarith [hB.1]
  have : n = 0 := by
    have a : n < 1 := by exact_mod_cast hn1
    have b : -1 < n := by exact_mod_cast hn2
    omega
  rw [h2, this]; simp

/-- **`𝓑(i) = 0`.** -/
theorem confB_zero_at_I : confB I = 0 := by
  have hI : (0 : ℝ) < I.im := by simp
  have h : confE I = Complex.exp (2 * π * 0) := by
    unfold confE
    have : (I - 1) ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
    have h2 : I * (I + 1) = I - 1 := by ring_nf; rw [Complex.I_sq]; ring
    rw [h2, div_self this]; simp
  exact confB_eq_of_confE hI (by simp) h

/-- `confE z = E` iff `E z² + (E-1) z + 1 = 0` (for `z ≠ 0, -1`). -/
lemma confE_eq_iff {z E : ℂ} (h0 : z ≠ 0) (h2 : z + 1 ≠ 0) :
    confE z = E ↔ E * z ^ 2 + (E - 1) * z + 1 = 0 := by
  unfold confE
  rw [div_eq_iff (mul_ne_zero h0 h2)]
  constructor <;> intro h <;> linear_combination (-1 : ℂ) * h

/-- **The inverse of `𝓑` is the upper-half-plane root of `e^{2πb} z² + (e^{2πb} - 1) z + 1 = 0`**
(Lemma G, "Slit-strip harmonic measure"): for `z` in the upper half-plane and `|Im b| < 1/2`,
`𝓑(z) = b` iff `z` solves that quadratic. -/
theorem confB_eq_iff_quadratic {z b : ℂ} (hz : 0 < z.im) (hb : |b.im| < 1 / 2) :
    confB z = b ↔
      Complex.exp (2 * π * b) * z ^ 2 + (Complex.exp (2 * π * b) - 1) * z + 1 = 0 := by
  obtain ⟨h0, -, h2⟩ := confE_ne_exp_aux hz
  rw [← confE_eq_iff h0 h2]
  constructor
  · intro h
    rw [← h, exp_two_pi_mul_confB hz]
  · intro h
    exact confB_eq_of_confE hz hb h

/-! ### `𝓑` is a bijection of the upper half-plane onto the slit strip -/

private lemma sqrt2_pos' : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt2_mul_self' : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- `e^{2π ξ_*} = 3 + 2√2 = (1+√2)²`. -/
lemma exp_two_pi_xiStar : Real.exp (2 * π * xiStar) = 3 + 2 * √2 := by
  have harsinh : Real.arsinh 1 = Real.log (1 + √2) := by
    unfold Real.arsinh; norm_num
  have h : 2 * π * xiStar = Real.log ((1 + √2) ^ 2) := by
    unfold xiStar
    rw [harsinh, Real.log_pow]; field_simp; norm_num; ring
  rw [h, Real.exp_log (by positivity)]
  have := sqrt2_mul_self'
  nlinarith

/-- `e^{-2π ξ_*} = 3 - 2√2`. -/
lemma exp_neg_two_pi_xiStar : Real.exp (-(2 * π * xiStar)) = 3 - 2 * √2 := by
  rw [Real.exp_neg, exp_two_pi_xiStar]
  have := sqrt2_mul_self'
  exact inv_eq_of_mul_eq_one_right (by nlinarith)

/-- For real `b`: `3 - 2√2 < e^{2πb} < 3 + 2√2` iff `|b| < ξ_*`. -/
lemma exp_two_pi_mem_Ioo_iff (b : ℝ) :
    (3 - 2 * √2 < Real.exp (2 * π * b) ∧ Real.exp (2 * π * b) < 3 + 2 * √2) ↔ |b| < xiStar := by
  rw [← exp_two_pi_xiStar, ← exp_neg_two_pi_xiStar, Real.exp_lt_exp, Real.exp_lt_exp, abs_lt]
  have := Real.pi_pos
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-- A real-coefficient quadratic with a root in the upper half-plane has negative discriminant:
`E² - 6E + 1 < 0`, i.e. `3 - 2√2 < E < 3 + 2√2`. -/
lemma quad_E_bounds {E x y : ℝ} (hE : 0 < E) (hy : 0 < y)
    (hre : E * (x ^ 2 - y ^ 2) + (E - 1) * x + 1 = 0) (him : 2 * E * x * y + (E - 1) * y = 0) :
    3 - 2 * √2 < E ∧ E < 3 + 2 * √2 := by
  have hx : 2 * E * x + (E - 1) = 0 := by
    have : y * (2 * E * x + (E - 1)) = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hy.ne'
    · exact h
  have hx' : x = (1 - E) / (2 * E) := by field_simp; linarith
  have hy2 : 4 * E ^ 2 * y ^ 2 = 6 * E - 1 - E ^ 2 := by
    rw [hx'] at hre
    field_simp at hre
    nlinarith [hre]
  have hpos : 0 < 6 * E - 1 - E ^ 2 := by rw [← hy2]; positivity
  have h8 : (E - 3) ^ 2 < (2 * √2) ^ 2 := by
    have := sqrt2_mul_self'; nlinarith
  have := abs_lt_of_sq_lt_sq h8 (by positivity)
  rw [abs_lt] at this
  constructor <;> linarith [this.1, this.2]

/-- The fold map `z ↦ (z+1)/(z-1)`. -/
noncomputable def confFold (z : ℂ) : ℂ := (z + 1) / (z - 1)

lemma confFold_eq_slitInv (σ : ℝ) : confFold (σ : ℂ) = ((slitInv σ : ℝ) : ℂ) := by
  unfold confFold slitInv; push_cast; ring

lemma slitInv_eq_leftSlitInv : slitInv = leftSlitInv := by
  funext σ; unfold slitInv leftSlitInv; rw [add_comm]

lemma confFold_im {z : ℂ} (hz : z ≠ 1) :
    (confFold z).im = -2 * z.im / Complex.normSq (z - 1) := by
  unfold confFold
  have hn : Complex.normSq (z - 1) ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero, sub_eq_zero]
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im, add_zero, sub_zero]
  field_simp
  ring

/-- **The fold is the deck transformation of `𝓑`:** `confE (confFold z) = confE z`. -/
theorem confE_fold {z : ℂ} (h0 : z ≠ 0) (h1 : z - 1 ≠ 0) (h2 : z + 1 ≠ 0) :
    confE (confFold z) = confE z := by
  unfold confE confFold
  have hz1 : z ≠ 1 := fun h => h1 (by rw [h]; ring)
  have hz2 : (z + 1) / (z - 1) - 1 = 2 / (z - 1) := by field_simp; ring
  have hz3 : (z + 1) / (z - 1) + 1 = 2 * z / (z - 1) := by field_simp; ring
  rw [hz2, hz3]
  field_simp

/-- `𝓑` maps the upper half-plane into the slit strip `D_*`. -/
theorem confB_mapsTo : MapsTo confB upperHalfPlane' slitStrip := by
  intro z hz
  have hz' : 0 < z.im := hz
  obtain ⟨hb1, hb2⟩ := confB_im_bounds hz'
  refine ⟨abs_lt.mpr ⟨hb1, hb2⟩, ?_⟩
  rintro ⟨him, hre⟩
  obtain ⟨h0, h1, h2⟩ := confE_ne_exp_aux hz'
  set b : ℝ := (confB z).re with hb
  have hBb : confB z = (b : ℂ) := Complex.ext (by simp [hb]) (by simpa using him)
  have hE : confE z = ((Real.exp (2 * π * b) : ℝ) : ℂ) := by
    rw [← exp_two_pi_mul_confB hz', hBb]
    rw [Complex.ofReal_exp]; push_cast; rfl
  have hq := (confE_eq_iff h0 h2).mp hE
  have hEpos : 0 < Real.exp (2 * π * b) := Real.exp_pos _
  set E := Real.exp (2 * π * b)
  have hre' := congrArg Complex.re hq
  have him' := congrArg Complex.im hq
  simp [pow_two] at hre' him'
  have hbd := quad_E_bounds (E := E) (x := z.re) (y := z.im) hEpos hz' (by linarith [hre'])
    (by linarith [him'])
  have := (exp_two_pi_mem_Ioo_iff b).mp hbd
  exact absurd hre (not_le.mpr this)

/-- `𝓑` is injective on the upper half-plane. -/
theorem confB_injOn : InjOn confB upperHalfPlane' := by
  intro z1 hz1 z2 hz2 h
  have hz1' : 0 < z1.im := hz1
  have hz2' : 0 < z2.im := hz2
  obtain ⟨a0, a1, a2⟩ := confE_ne_exp_aux hz1'
  obtain ⟨b0, b1, b2⟩ := confE_ne_exp_aux hz2'
  have hE : confE z1 = confE z2 := by
    rw [← exp_two_pi_mul_confB hz1', ← exp_two_pi_mul_confB hz2', h]
  unfold confE at hE
  rw [div_eq_div_iff (mul_ne_zero a0 a2) (mul_ne_zero b0 b2)] at hE
  have hprod : (z2 - z1) * ((z1 - 1) * (z2 - 1) - 2) = 0 := by linear_combination hE
  rcases mul_eq_zero.mp hprod with h' | h'
  · exact (sub_eq_zero.mp h').symm
  · exfalso
    have hz2e : z2 = confFold z1 := by
      unfold confFold; field_simp; linear_combination h'
    have := confFold_im (z := z1) (fun h => a1 (by rw [h]; ring))
    rw [← hz2e] at this
    have hn : 0 < Complex.normSq (z1 - 1) := Complex.normSq_pos.mpr a1
    have : z2.im < 0 := by rw [this]; exact div_neg_of_neg_of_pos (by linarith) hn
    linarith

/-- For `b ∈ D_*`, the quadratic `E z² + (E-1) z + 1 = 0` (`E = e^{2πb}`) has no real root. -/
private lemma no_real_root {b : ℂ} (hb : b ∈ slitStrip) (σ : ℝ) :
    Complex.exp (2 * π * b) * (σ : ℂ) ^ 2 + (Complex.exp (2 * π * b) - 1) * σ + 1 ≠ 0 := by
  intro h
  obtain ⟨hb1, hb2⟩ := hb
  set E := Complex.exp (2 * π * b) with hEdef
  have hσ : σ * (σ + 1) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rw [h0] at h; simp at h
    · have : σ = -1 := by linarith
      rw [this] at h; push_cast at h; ring_nf at h; simp at h
  have hE : E = (((σ - 1) / (σ * (σ + 1)) : ℝ) : ℂ) := by
    have hne : (σ : ℂ) * (σ + 1) ≠ 0 := by exact_mod_cast hσ
    have hmul : E * ((σ : ℂ) * (σ + 1)) = σ - 1 := by linear_combination h
    have := eq_div_of_mul_eq hne hmul
    rw [this]; push_cast; rfl
  -- `E` real, so `Im b = 0`
  have hEim : E.im = 0 := by rw [hE]; exact Complex.ofReal_im _
  have hbim : b.im = 0 := by
    have hexp : E.im = Real.exp (2 * π * b.re) * Real.sin (2 * π * b.im) := by
      rw [hEdef, Complex.exp_im]; simp
    rw [hexp] at hEim
    have hsin : Real.sin (2 * π * b.im) = 0 := by
      rcases mul_eq_zero.mp hEim with h' | h'
      · exact absurd h' (Real.exp_pos _).ne'
      · exact h'
    have hb1' : |b.im| < 1 / 2 := hb1
    rw [abs_lt] at hb1'
    have hpi := Real.pi_pos
    have := (Real.sin_eq_zero_iff_of_lt_of_lt (x := 2 * π * b.im) (by nlinarith [hb1'.1])
      (by nlinarith [hb1'.2])).mp hsin
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (by positivity)
    · exact h'
  have hb' : b = (b.re : ℂ) := Complex.ext (by simp) (by simpa using hbim)
  have hEre : E = ((Real.exp (2 * π * b.re) : ℝ) : ℂ) := by
    rw [hEdef, hb', Complex.ofReal_exp]; push_cast; rfl
  have hq : (Real.exp (2 * π * b.re) : ℝ) * σ ^ 2 + (Real.exp (2 * π * b.re) - 1) * σ + 1 = 0 := by
    rw [hEre] at h; exact_mod_cast h
  set e := Real.exp (2 * π * b.re)
  have hepos : 0 < e := Real.exp_pos _
  have hdisc : 0 ≤ e ^ 2 - 6 * e + 1 := by
    have : (2 * e * σ + (e - 1)) ^ 2 = e ^ 2 - 6 * e + 1 := by
      linear_combination (4 * e) * hq
    rw [← this]; positivity
  have hnot : ¬ (3 - 2 * √2 < e ∧ e < 3 + 2 * √2) := by
    rintro ⟨h1, h2⟩
    have := sqrt2_mul_self'
    nlinarith
  rw [exp_two_pi_mem_Ioo_iff, not_lt] at hnot
  exact hb2 ⟨hbim, hnot⟩

/-- `𝓑` maps the upper half-plane **onto** the slit strip `D_*`. -/
theorem confB_surjOn : SurjOn confB upperHalfPlane' slitStrip := by
  intro b hb
  have hbim : |b.im| < 1 / 2 := hb.1
  set E := Complex.exp (2 * π * b) with hEdef
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨w, hw⟩ := IsAlgClosed.isSquare ((E - 1) ^ 2 - 4 * E)
  set z1 : ℂ := (1 - E + w) / (2 * E) with hz1
  set z2 : ℂ := (1 - E - w) / (2 * E) with hz2
  have q1 : E * z1 ^ 2 + (E - 1) * z1 + 1 = 0 := by
    rw [hz1]; field_simp; linear_combination (-1 : ℂ) * hw
  have q2 : E * z2 ^ 2 + (E - 1) * z2 + 1 = 0 := by
    rw [hz2]; field_simp; linear_combination (-1 : ℂ) * hw
  have hvieta : (z1 - 1) * (z2 - 1) = 2 := by
    rw [hz1, hz2]; field_simp; linear_combination hw
  have hz1_ne : z1 - 1 ≠ 0 := by
    intro h; rw [h] at hvieta; simp at hvieta
  have hnoreal1 : z1.im ≠ 0 := by
    intro h
    have hz1r : z1 = (z1.re : ℂ) := Complex.ext (by simp) (by simpa using h)
    have := no_real_root hb z1.re
    rw [← hz1r] at this
    exact this q1
  rcases lt_or_gt_of_ne hnoreal1 with hneg | hpos
  · -- then `z2 = fold z1` has positive imaginary part
    have hz2e : z2 = confFold z1 := by
      unfold confFold
      rw [eq_div_iff hz1_ne]; linear_combination hvieta
    have hfold := confFold_im (z := z1) (fun h => hz1_ne (by rw [h]; ring))
    have hn : 0 < Complex.normSq (z1 - 1) := Complex.normSq_pos.mpr hz1_ne
    have : 0 < z2.im := by
      rw [hz2e, hfold]; exact div_pos (by linarith) hn
    refine ⟨z2, this, ?_⟩
    exact (confB_eq_iff_quadratic this hbim).mpr q2
  · exact ⟨z1, hpos, (confB_eq_iff_quadratic hpos hbim).mpr q1⟩

/-- **`𝓑` is a conformal bijection of the upper half-plane onto the slit strip** (Lemma G,
`vlo:Gap`, "Slit-strip harmonic measure"): bijective, holomorphic with nowhere-vanishing derivative. -/
theorem confB_bijOn : BijOn confB upperHalfPlane' slitStrip :=
  ⟨confB_mapsTo, confB_injOn, confB_surjOn⟩

/-! ### Boundary behaviour -/

private lemma log_re_ofReal (x : ℝ) : (Complex.log (x : ℂ)).re = Real.log |x| := by
  rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs]

/-- On the real axis, `Re 𝓑 = slitBoundaryMap` (the real boundary function of `EntropyAndDeficit`),
away from the poles `0, ±1`. -/
theorem confB_real_re {σ : ℝ} (h0 : σ ≠ 0) (h1 : σ ≠ 1) (h2 : σ ≠ -1) :
    (confB (σ : ℂ)).re = slitBoundaryMap σ := by
  have hs1 : σ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hs2 : σ + 1 ≠ 0 := fun h => h2 (by linarith)
  have e : (confB (σ : ℂ)).re = (2 * π)⁻¹ * (Real.log |σ - 1| - Real.log |σ| - Real.log |σ + 1|) := by
    unfold confB
    have h2pi : ((2 * π : ℂ)⁻¹) = (((2 * π)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2pi, Complex.re_ofReal_mul]
    simp only [Complex.sub_re]
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
      show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) by push_cast; rfl,
      log_re_ofReal, log_re_ofReal, log_re_ofReal]
  rw [e, slitBoundaryMap_eq_leftBranch, Real.log_div hs1 (mul_ne_zero h0 hs2),
    Real.log_mul h0 hs2, ← Real.log_abs (σ - 1), ← Real.log_abs σ, ← Real.log_abs (σ + 1)]
  ring

/-- Imaginary part of the boundary values of `𝓑`: the edges `(-∞,-1)` and `(0,1)` map to the lines
`Im b = -1/2` and `Im b = +1/2`, the slits `(-1,0)` and `(1,∞)` to the real axis. -/
theorem confB_real_im_of_lt_neg_one {σ : ℝ} (h : σ < -1) : (confB (σ : ℂ)).im = -(1 / 2) := by
  rw [confB_im_eq,
    show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
    show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) by push_cast; rfl,
    arg_ofReal_of_neg (by linarith), arg_ofReal_of_neg (by linarith),
    arg_ofReal_of_neg (by linarith)]
  field_simp; ring

theorem confB_real_im_of_mem_Ioo_neg_one_zero {σ : ℝ} (h : σ ∈ Ioo (-1 : ℝ) 0) :
    (confB (σ : ℂ)).im = 0 := by
  rw [confB_im_eq,
    show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
    show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) by push_cast; rfl,
    arg_ofReal_of_neg (by linarith [h.1, h.2]), arg_ofReal_of_neg h.2,
    arg_ofReal_of_nonneg (by linarith [h.1, h.2])]
  simp

theorem confB_real_im_of_mem_Ioo_zero_one {σ : ℝ} (h : σ ∈ Ioo (0 : ℝ) 1) :
    (confB (σ : ℂ)).im = 1 / 2 := by
  rw [confB_im_eq,
    show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
    show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) by push_cast; rfl,
    arg_ofReal_of_neg (by linarith [h.1, h.2]), arg_ofReal_of_nonneg h.1.le,
    arg_ofReal_of_nonneg (by linarith [h.1, h.2])]
  field_simp; ring

theorem confB_real_im_of_one_lt {σ : ℝ} (h : 1 < σ) : (confB (σ : ℂ)).im = 0 := by
  rw [confB_im_eq,
    show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
    show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) by push_cast; rfl,
    arg_ofReal_of_nonneg (by linarith), arg_ofReal_of_nonneg (by linarith),
    arg_ofReal_of_nonneg (by linarith)]
  simp

/-- `𝓑` (with the same formula) extends continuously from the closed upper half-plane to every real
point other than the poles `0, ±1`; its boundary values are those computed in `confB_real_re` and
`confB_real_im_of_*`. -/
theorem confB_continuousWithinAt_real {σ : ℝ} (h0 : σ ≠ 0) (h1 : σ ≠ 1) (h2 : σ ≠ -1) :
    ContinuousWithinAt confB {z : ℂ | 0 ≤ z.im} (σ : ℂ) := by
  have hlog : ∀ a : ℝ, σ - a ≠ 0 →
      ContinuousWithinAt (fun z : ℂ => Complex.log (z - a)) {z : ℂ | 0 ≤ z.im} (σ : ℂ) := by
    intro a ha
    have hmaps : MapsTo (fun z : ℂ => z - (a : ℂ)) {z : ℂ | 0 ≤ z.im} {z : ℂ | 0 ≤ z.im} := by
      intro z hz; simpa using hz
    have hc : ContinuousWithinAt (fun z : ℂ => z - (a : ℂ)) {z : ℂ | 0 ≤ z.im} (σ : ℂ) :=
      (continuous_id.sub continuous_const).continuousWithinAt
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have : ContinuousWithinAt Complex.log {z : ℂ | 0 ≤ z.im} ((σ : ℂ) - a) :=
        Complex.continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hneg) (by simp)
      exact ContinuousWithinAt.comp (f := fun z : ℂ => z - (a : ℂ)) this hc hmaps
    · have hmem : (σ : ℂ) - a ∈ slitPlane := by
        rw [mem_slitPlane_iff]; left; simpa using hpos
      exact (continuousAt_clog hmem).comp_continuousWithinAt (f := fun z : ℂ => z - (a : ℂ)) hc
  have a1 := hlog 1 (by simpa using sub_ne_zero.mpr h1)
  have a0 := hlog 0 (by simpa using h0)
  have a2 := hlog (-1) (by simpa using (fun h => h2 (by linarith) : σ + 1 ≠ 0))
  unfold confB
  simp only [Complex.ofReal_one, Complex.ofReal_zero, sub_zero, Complex.ofReal_neg, sub_neg_eq_add]
    at a1 a0 a2
  exact continuousWithinAt_const.mul ((a1.sub a0).sub a2)

/-! ### Agreement with the real-line definitions of `EntropyAndDeficit` -/

/-- On the slit `(-1,0)`, the continuation `confBSlit` is the real function `slitBoundaryMap`. -/
theorem confBSlit_ofReal {σ : ℝ} (hσ : σ ∈ Ioo (-1 : ℝ) 0) :
    confBSlit (σ : ℂ) = ((slitBoundaryMap σ : ℝ) : ℂ) := by
  have h1 : 0 < 1 - σ := by linarith [hσ.2]
  have h2 : 0 < -σ := by linarith [hσ.2]
  have h3 : 0 < 1 + σ := by linarith [hσ.1]
  unfold confBSlit slitBoundaryMap
  rw [Real.log_div h1.ne' (mul_pos h2 h3).ne', Real.log_mul h2.ne' h3.ne']
  push_cast
  rw [Complex.ofReal_log h1.le, Complex.ofReal_log h2.le, Complex.ofReal_log h3.le]
  push_cast; ring

/-- The right-slit tip `σ_* = 1 - √2` is a critical point and is mapped to `ξ_*`. -/
theorem confBSlit_sigmaStar : confBSlit (sigmaStar : ℂ) = (xiStar : ℂ) := by
  rw [confBSlit_ofReal ⟨by linarith [sigmaStar_gt_neg_half], sigmaStar_neg⟩,
    slitBoundaryMap_sigmaStar]

/-- The left-slit tip `σ_+ = 1 + √2` is mapped to `-ξ_*`. -/
theorem slitBoundaryMap_sigmaPlus : slitBoundaryMap sigmaPlus = -xiStar := by
  have hsq := sqrt2_mul_self'
  have hs := sqrt2_pos'
  have harg : (sigmaPlus - 1) / (sigmaPlus * (sigmaPlus + 1)) = ((√2 + 1) ^ 2)⁻¹ := by
    unfold sigmaPlus
    have : (1 + √2) * (1 + √2 + 1) = √2 * (√2 + 1) ^ 2 := by nlinarith
    rw [show 1 + √2 - 1 = √2 by ring, this]
    field_simp
  rw [slitBoundaryMap_eq_leftBranch, harg, Real.log_inv, Real.log_pow, mul_neg]
  have := slitBoundaryMap_sigmaStar
  unfold xiStar at *
  have harsinh : Real.arsinh 1 = Real.log (√2 + 1) := by
    unfold Real.arsinh; norm_num; rw [add_comm]
  rw [harsinh]
  field_simp
  norm_num

lemma confBDeriv_sigmaStar : confBDeriv (sigmaStar : ℂ) = 0 := by
  unfold confBDeriv sigmaStar
  push_cast
  ring_nf

lemma confBDeriv_sigmaPlus : confBDeriv (sigmaPlus : ℂ) = 0 := by
  unfold confBDeriv sigmaPlus
  push_cast
  ring_nf

lemma confBDeriv_ofReal (σ : ℝ) :
    confBDeriv (σ : ℂ) =
      ((-(σ - sigmaStar) * (σ - sigmaPlus) / (2 * π * σ * (σ ^ 2 - 1)) : ℝ) : ℂ) := by
  unfold confBDeriv sigmaStar sigmaPlus
  push_cast
  congr 1
  ring

/-- **The inverse Jacobian `J = 1/|𝓑'|`**: `invJacobian` of `EntropyAndDeficit` is the reciprocal of
the modulus of `confBDeriv` on the real line (including the conventions at the poles and tips). -/
theorem invJacobian_eq_inv_norm_confBDeriv (σ : ℝ) :
    invJacobian σ = ‖confBDeriv (σ : ℂ)‖⁻¹ := by
  rw [confBDeriv_ofReal, Complex.norm_real, Real.norm_eq_abs, ← abs_inv, inv_div, abs_div]
  unfold invJacobian
  have h1 : |2 * π * σ * (σ ^ 2 - 1)| = 2 * π * |σ * (σ ^ 2 - 1)| := by
    rw [mul_assoc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have h2 : |-(σ - sigmaStar) * (σ - sigmaPlus)| = |σ - sigmaStar| * |σ - sigmaPlus| := by
    rw [abs_mul, abs_neg]
  rw [h1, h2]

/-- `poissonKernel` is the upper-half-plane Poisson kernel `π⁻¹ Im (1/(σ - z))`, `z = x + iy`. -/
theorem poissonKernel_eq_im_inv (x y σ : ℝ) :
    poissonKernel x y σ = π⁻¹ * ((((σ : ℂ) - ((x : ℂ) + y * I)))⁻¹).im := by
  unfold poissonKernel
  rw [Complex.inv_im]
  have hn : Complex.normSq ((σ : ℂ) - ((x : ℂ) + y * I)) = (σ - x) ^ 2 + y ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have him : ((σ : ℂ) - ((x : ℂ) + y * I)).im = -y := by simp
  rw [hn, him, neg_neg]
  rcases eq_or_ne ((σ - x) ^ 2 + y ^ 2) 0 with h | h
  · rw [h]; simp
  · field_simp

/-! ### The tip expansion `𝓑(σ_* + w) = ξ_* + q w² + o(w²)` -/

/-- `q = ½ 𝓑''(σ_*) = √2 / (2π σ_*(σ_*² - 1))` (`bl:T1`, `≈ 0.6559`). -/
noncomputable def confTipQ : ℝ := √2 / (2 * π * sigmaStar * (sigmaStar ^ 2 - 1))

lemma confTipQ_pos : 0 < confTipQ := by
  unfold confTipQ
  have h1 := sigmaStar_neg
  have h2 := sigmaStar_gt_neg_half
  have : 0 < 2 * π * sigmaStar * (sigmaStar ^ 2 - 1) := by
    have : sigmaStar * (sigmaStar ^ 2 - 1) > 0 :=
      mul_pos_of_neg_of_neg h1 (by nlinarith)
    have := mul_pos (by positivity : (0 : ℝ) < 2 * π) this
    linarith
  exact div_pos sqrt2_pos' this

private lemma confBDeriv_eq_poly (z : ℂ) :
    confBDeriv z = -((z - 1) ^ 2 - 2) / (2 * π * z * (z ^ 2 - 1)) := by
  unfold confBDeriv
  have := sqrt2_sq_C
  congr 1
  linear_combination this

/-- `𝓑''(σ_*) = 2q`: the derivative of `confBDeriv` at the tip. -/
theorem hasDerivAt_confBDeriv_sigmaStar :
    HasDerivAt confBDeriv ((2 * confTipQ : ℝ) : ℂ) (sigmaStar : ℂ) := by
  have hpi := pi_ne_zero_C
  have hσ0 : (sigmaStar : ℂ) ≠ 0 := by exact_mod_cast sigmaStar_neg.ne
  have hσ1 : (sigmaStar : ℂ) ^ 2 - 1 ≠ 0 := by
    have : sigmaStar ^ 2 - 1 < 0 := by nlinarith [sigmaStar_neg, sigmaStar_gt_neg_half]
    exact_mod_cast this.ne
  have hD : (2 * π : ℂ) * sigmaStar * ((sigmaStar : ℂ) ^ 2 - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hσ0) hσ1
  have hN : HasDerivAt (fun z : ℂ => -((z - 1) ^ 2 - 2)) (-(2 * ((sigmaStar : ℂ) - 1))) sigmaStar := by
    have := ((((hasDerivAt_id (sigmaStar : ℂ)).sub_const 1).pow 2).sub_const 2).neg
    exact this.congr_deriv (by simp)
  have hDd : HasDerivAt (fun z : ℂ => 2 * π * z * (z ^ 2 - 1))
      (2 * π * ((sigmaStar : ℂ) ^ 2 - 1) + 2 * π * sigmaStar * (2 * (sigmaStar : ℂ)))
      (sigmaStar : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => 2 * π * z) (2 * π) (sigmaStar : ℂ) := by
      simpa using (hasDerivAt_id (sigmaStar : ℂ)).const_mul (2 * π : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => z ^ 2 - 1) (2 * (sigmaStar : ℂ)) (sigmaStar : ℂ) := by
      simpa using ((hasDerivAt_id (sigmaStar : ℂ)).pow 2).sub_const 1
    exact h1.mul h2
  have hdiv := hN.div hDd hD
  have hfun : confBDeriv = fun z : ℂ => -((z - 1) ^ 2 - 2) / (2 * π * z * (z ^ 2 - 1)) :=
    funext confBDeriv_eq_poly
  rw [hfun]
  refine hdiv.congr_deriv ?_
  -- numerator vanishes at `σ_*`
  have hnum : -(((sigmaStar : ℂ) - 1) ^ 2 - 2) = 0 := by
    unfold sigmaStar; push_cast
    have := sqrt2_sq_C
    linear_combination (-1 : ℂ) * this
  rw [hnum]
  unfold confTipQ
  have hs2 : (((sigmaStar : ℂ)) - 1) = -(√2 : ℝ) := by unfold sigmaStar; push_cast; ring
  rw [hs2]
  push_cast
  field_simp
  ring

/-- **Tip expansion** (`bl:T1`): `𝓑(σ_* + w) = ξ_* + q w² + o(w²)` as `w → 0` in `ℂ`, with
`q = √2/(2π σ_*(σ_*² - 1))`. -/
theorem confBSlit_tip_expansion :
    (fun w : ℂ => confBSlit ((sigmaStar : ℂ) + w) - xiStar - (confTipQ : ℂ) * w ^ 2)
      =o[𝓝 0] (fun w : ℂ => w ^ 2) := by
  -- the region where `confBSlit` is holomorphic
  have hsl : ∀ z : ℂ, z.re < 0 → z.re > -1 → 1 - z ∈ slitPlane ∧ -z ∈ slitPlane ∧ 1 + z ∈ slitPlane := by
    intro z h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> rw [mem_slitPlane_iff] <;> left <;> simp <;> linarith
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), (((sigmaStar : ℂ) + w).re < 0 ∧ ((sigmaStar : ℂ) + w).re > -1) := by
    have hc : Continuous fun w : ℂ => ((sigmaStar : ℂ) + w).re := by fun_prop
    have h0 : (((sigmaStar : ℂ) + 0).re < 0 ∧ ((sigmaStar : ℂ) + 0).re > -1) := by
      simp only [add_zero, Complex.ofReal_re]
      exact ⟨sigmaStar_neg, by linarith [sigmaStar_gt_neg_half]⟩
    exact (hc.continuousAt.eventually (Iio_mem_nhds h0.1)).and
      (hc.continuousAt.eventually (Ioi_mem_nhds h0.2))
  -- derivative of the remainder
  have hderiv : ∀ᶠ w in 𝓝 (0 : ℂ), HasDerivAt
      (fun u : ℂ => confBSlit ((sigmaStar : ℂ) + u) - xiStar - (confTipQ : ℂ) * u ^ 2)
      (confBDeriv ((sigmaStar : ℂ) + w) - 2 * confTipQ * w) w := by
    filter_upwards [hnear] with w hw
    obtain ⟨a, b, c⟩ := hsl _ hw.1 hw.2
    have h1 := (hasDerivAt_confBSlit a b c).comp_const_add (sigmaStar : ℂ) w
    have h2 : HasDerivAt (fun u : ℂ => (confTipQ : ℂ) * u ^ 2) (confTipQ * (2 * w)) w := by
      simpa using ((hasDerivAt_id w).pow 2).const_mul (confTipQ : ℂ)
    have := (h1.sub_const (xiStar : ℂ)).sub h2
    convert this using 1
    ring
  -- `confBDeriv (σ_* + w) = 2 q w + o(w)`
  have hlin := (hasDerivAt_iff_isLittleO_nhds_zero.mp hasDerivAt_confBDeriv_sigmaStar)
  rw [Asymptotics.isLittleO_iff] at hlin ⊢
  intro c hc
  have hc' : 0 < c / 2 := by linarith
  have hl := hlin hc'
  rw [Metric.eventually_nhds_iff] at hl
  rw [Metric.eventually_nhds_iff] at hderiv
  obtain ⟨r1, hr1, hl⟩ := hl
  obtain ⟨r2, hr2, hd⟩ := hderiv
  rw [Filter.Eventually, Metric.mem_nhds_iff]
  refine ⟨min r1 r2, lt_min hr1 hr2, fun w hw => ?_⟩
  have hwr1 : dist w 0 < r1 := lt_of_lt_of_le hw (min_le_left _ _)
  have hwr2 : dist w 0 < r2 := lt_of_lt_of_le hw (min_le_right _ _)
  set F : ℂ → ℂ := fun u => confBSlit ((sigmaStar : ℂ) + u) - xiStar - (confTipQ : ℂ) * u ^ 2 with hF
  have hmem : ∀ u ∈ Metric.closedBall (0 : ℂ) ‖w‖, dist u 0 < r1 ∧ dist u 0 < r2 := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    rw [dist_zero_right]
    rw [dist_zero_right] at hwr1 hwr2
    exact ⟨lt_of_le_of_lt hu hwr1, lt_of_le_of_lt hu hwr2⟩
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := F) (f' := fun u => confBDeriv ((sigmaStar : ℂ) + u) - 2 * confTipQ * u)
    (s := Metric.closedBall (0 : ℂ) ‖w‖) (C := c / 2 * ‖w‖) (x := 0) (y := w)
    (fun u hu => (hd (hmem u hu).2).hasDerivWithinAt)
    (fun u hu => by
      have h := hl (hmem u hu).1
      rw [Metric.mem_closedBall, dist_zero_right] at hu
      simp only [confBDeriv_sigmaStar, sub_zero, smul_eq_mul] at h
      have e : confBDeriv ((sigmaStar : ℂ) + u) - 2 * confTipQ * u =
          confBDeriv ((sigmaStar : ℂ) + u) - (((2 * confTipQ : ℝ) : ℂ)) * u := by push_cast; ring
      rw [e]
      have h' : ‖confBDeriv ((sigmaStar : ℂ) + u) - u * (((2 * confTipQ : ℝ) : ℂ))‖ ≤ c / 2 * ‖u‖ := by
        simpa [sub_zero] using h
      rw [mul_comm u] at h'
      calc _ ≤ c / 2 * ‖u‖ := h'
        _ ≤ c / 2 * ‖w‖ := by gcongr)
    (convex_closedBall _ _) (by simp) (by simp)
  have hF0 : F 0 = 0 := by
    simp only [hF, add_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero]
    rw [confBSlit_sigmaStar]; ring
  rw [hF0, sub_zero, sub_zero] at hbound
  show ‖F w‖ ≤ c * ‖w ^ 2‖
  rw [norm_pow]
  calc ‖F w‖ ≤ c / 2 * ‖w‖ * ‖w‖ := hbound
    _ ≤ c * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]

/-! ### The slits are folded at the tips: ranges of the boundary map on `(-1,0)` and `(1,∞)` -/

private lemma log_three_add_two_sqrt_two : Real.log (3 + 2 * √2) = 2 * π * xiStar := by
  rw [← exp_two_pi_xiStar, Real.log_exp]

/-- On the right slit preimage `(-1,0)` the boundary map takes values in `[ξ_*, ∞)`, with the
minimum `ξ_*` attained exactly at the fold tip `σ_*` (so the slit `[ξ_*,∞)` is covered twice,
the two sheets being exchanged by `slitInv`). -/
theorem xiStar_le_slitBoundaryMap {σ : ℝ} (hσ : σ ∈ Ioo (-1 : ℝ) 0) :
    xiStar ≤ slitBoundaryMap σ := by
  have h1 : 0 < 1 - σ := by linarith [hσ.2]
  have h2 : 0 < -σ := by linarith [hσ.2]
  have h3 : 0 < 1 + σ := by linarith [hσ.1]
  have hsq := sqrt2_mul_self'
  have hs := sqrt2_pos'
  unfold slitBoundaryMap
  have hpi := Real.pi_pos
  have hlog : 2 * π * xiStar ≤ Real.log ((1 - σ) / ((-σ) * (1 + σ))) := by
    rw [← log_three_add_two_sqrt_two]
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ (mul_pos h2 h3)]
    -- `(3+2√2)(-σ)(1+σ) ≤ 1 - σ`, i.e. `(3+2√2)(σ - σ_*)² ≥ 0`
    have : 1 - σ - (3 + 2 * √2) * ((-σ) * (1 + σ)) = (3 + 2 * √2) * (σ - (1 - √2)) ^ 2 := by
      nlinarith [hsq]
    nlinarith [sq_nonneg (σ - (1 - √2)), this]
  calc xiStar = (2 * π)⁻¹ * (2 * π * xiStar) := by field_simp
    _ ≤ _ := by gcongr

/-- On the left slit preimage `(1,∞)` the boundary map takes values in `(-∞, -ξ_*]`, with the
maximum `-ξ_*` attained exactly at the fold tip `σ_+`. -/
theorem slitBoundaryMap_le_neg_xiStar {σ : ℝ} (hσ : 1 < σ) : slitBoundaryMap σ ≤ -xiStar := by
  have h1 : 0 < σ - 1 := by linarith
  have h2 : 0 < σ := by linarith
  have h3 : 0 < σ + 1 := by linarith
  have hsq := sqrt2_mul_self'
  have hs := sqrt2_pos'
  have hpi := Real.pi_pos
  rw [slitBoundaryMap_eq_leftBranch]
  have hlog : Real.log ((σ - 1) / (σ * (σ + 1))) ≤ -(2 * π * xiStar) := by
    have hE : Real.log (3 - 2 * √2) = -(2 * π * xiStar) := by
      rw [← exp_neg_two_pi_xiStar, Real.log_exp]
    rw [← hE]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ (mul_pos h2 h3)]
    have : (3 - 2 * √2) * (σ * (σ + 1)) - (σ - 1) = (3 - 2 * √2) * (σ - (1 + √2)) ^ 2 := by
      nlinarith [hsq]
    have h4 : 0 ≤ 3 - 2 * √2 := by nlinarith [hsq, hs]
    nlinarith [mul_nonneg h4 (sq_nonneg (σ - (1 + √2)))]
  calc (2 * π)⁻¹ * Real.log ((σ - 1) / (σ * (σ + 1))) ≤ (2 * π)⁻¹ * (-(2 * π * xiStar)) := by gcongr
    _ = -xiStar := by field_simp

/-- **The branch of `𝓑`**: on the upper half-plane the sum-of-logarithms definition `confB` agrees
with the principal logarithm of the quotient, `𝓑(z) = (2π)⁻¹ Log((z-1)/(z(z+1)))`, as written in the
paper (Lemma G, `vlo:Gap`). -/
theorem confB_eq_log_confE {z : ℂ} (hz : 0 < z.im) :
    confB z = (2 * π : ℂ)⁻¹ * Complex.log (confE z) := by
  obtain ⟨hb1, hb2⟩ := confB_im_bounds hz
  have him : (2 * (π : ℂ) * confB z).im = 2 * π * (confB z).im := by
    rw [show (2 * (π : ℂ) * confB z) = (((2 * π : ℝ)) : ℂ) * confB z by push_cast; ring,
      Complex.im_ofReal_mul]
  have hpi := Real.pi_pos
  rw [← exp_two_pi_mul_confB hz, Complex.log_exp (by rw [him]; nlinarith)
    (by rw [him]; nlinarith)]
  have : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero pi_ne_zero_C
  field_simp

/-! ### Axiom checks for the headline theorems -/

/-- info: 'FormalResearch.ModularBootstrap.confB_eq_log_confE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_eq_log_confE

/-- info: 'FormalResearch.ModularBootstrap.confB_eq_confBSlit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_eq_confBSlit

/-- info: 'FormalResearch.ModularBootstrap.hasDerivAt_confBSlit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.hasDerivAt_confBSlit

/-- info: 'FormalResearch.ModularBootstrap.hasDerivAt_confB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.hasDerivAt_confB

/-- info: 'FormalResearch.ModularBootstrap.confBDeriv_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confBDeriv_eq_zero_iff

/-- info: 'FormalResearch.ModularBootstrap.confBDeriv_ne_zero_of_im_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confBDeriv_ne_zero_of_im_pos

/-- info: 'FormalResearch.ModularBootstrap.confB_im_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_im_bounds

/-- info: 'FormalResearch.ModularBootstrap.exp_two_pi_mul_confB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.exp_two_pi_mul_confB

/-- info: 'FormalResearch.ModularBootstrap.confB_zero_at_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_zero_at_I

/-- info: 'FormalResearch.ModularBootstrap.confB_eq_iff_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_eq_iff_quadratic

/-- info: 'FormalResearch.ModularBootstrap.confB_mapsTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_mapsTo

/-- info: 'FormalResearch.ModularBootstrap.confB_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_injOn

/-- info: 'FormalResearch.ModularBootstrap.confB_surjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_surjOn

/-- info: 'FormalResearch.ModularBootstrap.confB_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_bijOn

/-- info: 'FormalResearch.ModularBootstrap.confE_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confE_fold

/-- info: 'FormalResearch.ModularBootstrap.confB_real_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_real_re

/-- info: 'FormalResearch.ModularBootstrap.confB_real_im_of_lt_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_real_im_of_lt_neg_one

/-- info: 'FormalResearch.ModularBootstrap.confB_real_im_of_mem_Ioo_neg_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_real_im_of_mem_Ioo_neg_one_zero

/-- info: 'FormalResearch.ModularBootstrap.confB_real_im_of_mem_Ioo_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_real_im_of_mem_Ioo_zero_one

/-- info: 'FormalResearch.ModularBootstrap.confB_real_im_of_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_real_im_of_one_lt

/-- info: 'FormalResearch.ModularBootstrap.confB_continuousWithinAt_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_continuousWithinAt_real

/-- info: 'FormalResearch.ModularBootstrap.confBSlit_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confBSlit_ofReal

/-- info: 'FormalResearch.ModularBootstrap.confBSlit_sigmaStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confBSlit_sigmaStar

/-- info: 'FormalResearch.ModularBootstrap.slitBoundaryMap_sigmaPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitBoundaryMap_sigmaPlus

/-- info: 'FormalResearch.ModularBootstrap.invJacobian_eq_inv_norm_confBDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.invJacobian_eq_inv_norm_confBDeriv

/-- info: 'FormalResearch.ModularBootstrap.poissonKernel_eq_im_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.poissonKernel_eq_im_inv

/-- info: 'FormalResearch.ModularBootstrap.hasDerivAt_confBDeriv_sigmaStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.hasDerivAt_confBDeriv_sigmaStar

/-- info: 'FormalResearch.ModularBootstrap.confBSlit_tip_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confBSlit_tip_expansion

/-- info: 'FormalResearch.ModularBootstrap.xiStar_le_slitBoundaryMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.xiStar_le_slitBoundaryMap

/-- info: 'FormalResearch.ModularBootstrap.slitBoundaryMap_le_neg_xiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.slitBoundaryMap_le_neg_xiStar

end FormalResearch.ModularBootstrap
