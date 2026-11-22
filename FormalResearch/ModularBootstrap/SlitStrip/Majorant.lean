module

public import FormalResearch.ModularBootstrap.SlitStrip.RealSlice
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The harmonic majorant `U` on the real and imaginary axes, the (G-deficit) closed form

Formalizes the part of `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G (`vlo:Gap`),
paragraph "The harmonic majorant and the deficit", that is elementary calculus:

* `majorantU0` is `U_0 = -L(ξ_*) + (4/3) ∫_0^{ξ_*} arcsin(sinh πs) ds`; `majorantReal` is `U(x)` for
  real `x` (`U(x) = U_0 - (4/3) ∫_0^{|x|} arcsin(sinh πs) ds` for `|x| ≤ ξ_*`, `U = -L` on the slits).
* `majorant_add_L_eq_integral`: the closed form (G-deficit)
  `U(x) + L(x) = -(4/3) ∫_{|x|}^{ξ_*} [π/2 - arcsin(sinh πs)] ds`, `L(x) = 2π|x|/3`.
* `majorant_add_L_eq_neg_slitDeficit`: it equals `-slitDeficit(ξ_* - |x|)` (`π/2 - arcsin = arccos`).
* `inverse_area_identity`: `∫_0^{ξ_*} arcsin(sinh πx) dx + ∫_0^{1/2} arsinh(sin πy) dy = π ξ_*/2`.
* `majorantImag_half`: `U(i/2) = 0` on the upper edge (from the area identity).
* `pMap`: the paper's `p(b) = π⁻¹ arsinh(-i sinh πb)` with its values on the real segment and
  on the imaginary axis (`pMap_ofReal`, `pMap_mul_I`) which justify the two real formulas above.

The harmonic-measure identification `h = U` (maximum principle) is *not* proved here; see
`HarmonicMajorantIdentification` in `PoissonJensenInput.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap

/-! ### Definitions and the closed form on the real segment -/

/-- `A(s) = arcsin(sinh(π s))`. -/
noncomputable def arcsinSinh (s : ℝ) : ℝ := Real.arcsin (Real.sinh (π * s))

lemma continuous_arcsinSinh : Continuous arcsinSinh :=
  Real.continuous_arcsin.comp (Real.continuous_sinh.comp (continuous_const.mul continuous_id))

lemma intervalIntegrable_arcsinSinh (a b : ℝ) :
    IntervalIntegrable arcsinSinh volume a b := continuous_arcsinSinh.intervalIntegrable a b

/-- The linear function `L(x) = 2π|x|/3` of the paper. -/
noncomputable def slitL (x : ℝ) : ℝ := 2 * π * |x| / 3

/-- `U_0 = -L(ξ_*) + (4/3) ∫_0^{ξ_*} arcsin(sinh πs) ds` (Lemma G, `vlo:Gap`). -/
noncomputable def majorantU0 : ℝ :=
  -slitL xiStar + (4 / 3) * ∫ s in (0 : ℝ)..xiStar, arcsinSinh s

/-- The harmonic majorant `U` on the real axis: for `|x| ≤ ξ_*` it is
`U_0 - (4/3) ∫_0^{|x|} arcsin(sinh πs) ds`, i.e. `U_0 + (4π/3) Im ∫_0^x p`, see `pMap_ofReal`;
on the slits `|x| ≥ ξ_*` it is `-L(x)` ("`U = -L` by contact at the tip"; the two definitions agree
at `|x| = ξ_*`, see `majorantReal_xiStar`). -/
noncomputable def majorantReal (x : ℝ) : ℝ :=
  if |x| ≤ xiStar then majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..|x|, arcsinSinh s else -slitL x

lemma majorantReal_of_abs_le {x : ℝ} (hx : |x| ≤ xiStar) :
    majorantReal x = majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..|x|, arcsinSinh s := by
  unfold majorantReal; simp [hx]

lemma majorantReal_of_lt_abs {x : ℝ} (hx : xiStar < |x|) : majorantReal x = -slitL x := by
  unfold majorantReal; simp [not_le.mpr hx]

lemma majorantReal_xiStar : majorantReal xiStar = -slitL xiStar := by
  rw [majorantReal_of_abs_le (by rw [abs_of_pos xiStar_pos])]
  unfold majorantU0
  rw [abs_of_pos xiStar_pos]; ring

lemma majorantReal_neg (x : ℝ) : majorantReal (-x) = majorantReal x := by
  unfold majorantReal slitL; rw [abs_neg]

/-- **(G-deficit), closed form** (`vlo:eGapDeficit`): for `|x| ≤ ξ_*`,
`U(x) + L(x) = -(4/3) ∫_{|x|}^{ξ_*} [π/2 - arcsin(sinh πs)] ds`. -/
theorem majorant_add_L_eq_integral {x : ℝ} (hx : |x| ≤ xiStar) :
    majorantReal x + slitL x =
      -(4 / 3) * ∫ s in |x|..xiStar, (π / 2 - arcsinSinh s) := by
  rw [majorantReal_of_abs_le hx]
  have hint : ∀ a b : ℝ, IntervalIntegrable arcsinSinh volume a b := intervalIntegrable_arcsinSinh
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ _), intervalIntegral.integral_const,
    ← intervalIntegral.integral_interval_sub_left (hint 0 xiStar) (hint 0 |x|)]
  unfold majorantU0 slitL
  simp only [smul_eq_mul, abs_of_pos xiStar_pos]
  ring

/-- **(G-deficit) in terms of `slitDeficit`**: for `|x| ≤ ξ_*`,
`U(x) + L(x) = -slitDeficit(ξ_* - |x|)` (`π/2 - arcsin = arccos`). -/
theorem majorant_add_L_eq_neg_slitDeficit {x : ℝ} (hx : |x| ≤ xiStar) :
    majorantReal x + slitL x = -slitDeficit (xiStar - |x|) := by
  rw [majorant_add_L_eq_integral hx]
  unfold slitDeficit
  rw [sub_sub_cancel, neg_mul]
  congr 2

/-- **`g_deficit` of `PoissonJensenInput`, proved**: for `0 ≤ x < ξ_*`,
`U(x) + (2π/3) x ≤ -slitDeficit(ξ_* - x)` (with equality). -/
theorem majorantReal_g_deficit {x : ℝ} (hx : x ∈ Ico 0 xiStar) :
    majorantReal x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x) := by
  have habs : |x| = x := abs_of_nonneg hx.1
  have h := majorant_add_L_eq_neg_slitDeficit (x := x) (by rw [habs]; exact hx.2.le)
  rw [habs] at h
  unfold slitL at h
  rw [habs] at h
  linarith

/-! ### The inverse-area identity -/

/-- `y ↦ π⁻¹ arsinh(sin πy)`, the inverse of `x ↦ π⁻¹ arcsin(sinh πx)` on `[0, ξ_*]`. -/
private noncomputable def arsinhSin (y : ℝ) : ℝ := Real.arsinh (Real.sin (π * y)) / π

private lemma hasDerivAt_arsinhSin (y : ℝ) :
    HasDerivAt arsinhSin (Real.cos (π * y) / √(1 + Real.sin (π * y) ^ 2)) y := by
  have h1 : HasDerivAt (fun y : ℝ => Real.sin (π * y)) (Real.cos (π * y) * π) y := by
    simpa using ((hasDerivAt_id y).const_mul π).sin
  have h2 := ((Real.hasDerivAt_arsinh (Real.sin (π * y))).comp y h1).div_const π
  refine h2.congr_deriv ?_
  have hpi := Real.pi_pos.ne'
  field_simp

private lemma continuous_arsinhSin' : Continuous fun y : ℝ =>
    Real.cos (π * y) / √(1 + Real.sin (π * y) ^ 2) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun y => ?_
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

private lemma arsinhSin_zero : arsinhSin 0 = 0 := by simp [arsinhSin]

private lemma arsinhSin_half : arsinhSin (1 / 2) = xiStar := by
  unfold arsinhSin xiStar
  rw [show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two]

private lemma arcsinSinh_arsinhSin {y : ℝ} (hy : y ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    arcsinSinh (arsinhSin y) = π * y := by
  unfold arcsinSinh arsinhSin
  have hpi := Real.pi_pos
  rw [mul_div_cancel₀ _ hpi.ne', Real.sinh_arsinh]
  have := Real.arcsin_sin (x := π * y) (by nlinarith [hy.1]) (by nlinarith [hy.2])
  exact this

/-- **Inverse-area identity** (Lemma G, `vlo:Gap`):
`∫_0^{ξ_*} arcsin(sinh πx) dx + ∫_0^{1/2} arsinh(sin πy) dy = π ξ_*/2`. -/
theorem inverse_area_identity :
    (∫ x in (0 : ℝ)..xiStar, Real.arcsin (Real.sinh (π * x))) +
      (∫ y in (0 : ℝ)..(1 / 2), Real.arsinh (Real.sin (π * y))) = π * xiStar / 2 := by
  have hpi := Real.pi_pos
  -- substitution `x = arsinhSin y` in the first integral
  have hsub : ∫ y in (0 : ℝ)..(1 / 2),
      (arcsinSinh ∘ arsinhSin) y * (Real.cos (π * y) / √(1 + Real.sin (π * y) ^ 2)) =
      ∫ x in arsinhSin 0..arsinhSin (1 / 2), arcsinSinh x :=
    intervalIntegral.integral_comp_mul_deriv (f := arsinhSin)
      (fun y _ => hasDerivAt_arsinhSin y) continuous_arsinhSin'.continuousOn continuous_arcsinSinh
  rw [arsinhSin_zero, arsinhSin_half] at hsub
  have hcomp : ∀ y ∈ uIcc (0 : ℝ) (1 / 2),
      (arcsinSinh ∘ arsinhSin) y * (Real.cos (π * y) / √(1 + Real.sin (π * y) ^ 2)) =
        π * (y * (Real.cos (π * y) / √(1 + Real.sin (π * y) ^ 2))) := by
    intro y hy
    rw [uIcc_of_le (by norm_num)] at hy
    simp only [Function.comp]
    rw [arcsinSinh_arsinhSin ⟨by linarith [hy.1], hy.2⟩]; ring
  rw [intervalIntegral.integral_congr hcomp, intervalIntegral.integral_const_mul] at hsub
  -- integration by parts
  have hbp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1 / 2)
    (u := fun y : ℝ => y) (u' := fun _ => (1 : ℝ)) (v := arsinhSin)
    (v' := fun y => Real.cos (π * y) / √(1 + Real.sin (π * y) ^ 2))
    (fun y _ => hasDerivAt_id y) (fun y _ => hasDerivAt_arsinhSin y)
    intervalIntegrable_const (continuous_arsinhSin'.intervalIntegrable _ _)
  rw [arsinhSin_zero, arsinhSin_half] at hbp
  have hint : ∫ y in (0 : ℝ)..(1 / 2), (1 : ℝ) * arsinhSin y =
      (∫ y in (0 : ℝ)..(1 / 2), Real.arsinh (Real.sin (π * y))) / π := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp [arsinhSin]
  rw [hint] at hbp
  simp only [mul_zero, sub_zero] at hbp
  have hfirst : ∫ x in (0 : ℝ)..xiStar, Real.arcsin (Real.sinh (π * x)) =
      π * ((1 / 2) * xiStar - (∫ y in (0 : ℝ)..(1 / 2), Real.arsinh (Real.sin (π * y))) / π) := by
    have : ∫ x in (0 : ℝ)..xiStar, arcsinSinh x =
        π * ∫ y in (0 : ℝ)..(1 / 2), y * (Real.cos (π * y) / √(1 + Real.sin (π * y) ^ 2)) := hsub.symm
    simp only [arcsinSinh] at this
    rw [this, hbp]
  rw [hfirst]
  field_simp
  ring

/-- `U_0 = -(4/3) ∫_0^{1/2} arsinh(sin πy) dy` (consequence of `inverse_area_identity`). -/
theorem majorantU0_eq : majorantU0 = -(4 / 3) * ∫ y in (0 : ℝ)..(1 / 2), Real.arsinh (Real.sin (π * y)) := by
  have h := inverse_area_identity
  unfold majorantU0 slitL
  rw [abs_of_pos xiStar_pos]
  simp only [arcsinSinh]
  linarith

/-! ### The paper's `p(b) = π⁻¹ arsinh(-i sinh πb)` on the real and imaginary axes -/

/-- The principal complex `arsinh w = log(w + √(w² + 1))`. -/
noncomputable def complexArsinh (w : ℂ) : ℂ := Complex.log (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ))

/-- The paper's `p(b) = π⁻¹ arsinh(-i sinh πb)` (principal `arsinh`; the principal branch is the
continuation from `b = 0` on the slit strip). -/
noncomputable def pMap (b : ℂ) : ℂ := (π : ℂ)⁻¹ * complexArsinh (-I * Complex.sinh (π * b))

lemma complexArsinh_ofReal (u : ℝ) : complexArsinh (u : ℂ) = ((Real.arsinh u : ℝ) : ℂ) := by
  unfold complexArsinh Real.arsinh
  have h1 : ((u : ℂ) ^ 2 + 1) = ((1 + u ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, ← Complex.ofReal_add,
    ← Complex.ofReal_log]
  have : 0 < u + √(1 + u ^ 2) := by
    have h := Real.sqrt_nonneg (1 + u ^ 2)
    have h2 : |u| < √(1 + u ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
    linarith [neg_abs_le u]
  exact this.le

lemma complexArsinh_neg_I_mul {s : ℝ} (hs : |s| ≤ 1) :
    complexArsinh (-I * (s : ℂ)) = ((-Real.arcsin s : ℝ) : ℂ) * I := by
  unfold complexArsinh
  have hs2 : 0 ≤ 1 - s ^ 2 := by nlinarith [abs_le.mp hs]
  have h1 : (-I * (s : ℂ)) ^ 2 + 1 = ((1 - s ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [h1, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hs2, ← Real.sqrt_eq_rpow]
  set z : ℂ := -I * (s : ℂ) + ((√(1 - s ^ 2) : ℝ) : ℂ) with hz
  have hre : z.re = √(1 - s ^ 2) := by simp [hz]
  have him : z.im = -s := by simp [hz]
  have hnorm : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, him]
    have : √(1 - s ^ 2) * √(1 - s ^ 2) + -s * -s = 1 := by
      rw [Real.mul_self_sqrt hs2]; ring
    rw [this, Real.sqrt_one]
  apply Complex.ext
  · rw [Complex.log_re, hnorm]; simp
  · rw [Complex.log_im, Complex.arg_of_re_nonneg (by rw [hre]; exact Real.sqrt_nonneg _), hnorm, him]
    simp [Real.arcsin_neg]

private lemma abs_sinh_le_one {x : ℝ} (hx : |x| ≤ xiStar) : |Real.sinh (π * x)| ≤ 1 := by
  have h1 : Real.sinh (π * xiStar) = 1 := sinh_pi_mul_xiStar
  have hpi := Real.pi_pos
  rw [abs_le]
  constructor
  · have : Real.sinh (-(π * xiStar)) ≤ Real.sinh (π * x) :=
      Real.sinh_le_sinh.mpr (by nlinarith [(abs_le.mp hx).1])
    rw [Real.sinh_neg, h1] at this; exact this
  · have : Real.sinh (π * x) ≤ Real.sinh (π * xiStar) :=
      Real.sinh_le_sinh.mpr (by nlinarith [(abs_le.mp hx).2])
    rwa [h1] at this

/-- On the real segment `|x| ≤ ξ_*`, `p(x) = -(i/π) arcsin(sinh πx)` is purely imaginary. -/
theorem pMap_ofReal {x : ℝ} (hx : |x| ≤ xiStar) :
    pMap (x : ℂ) = ((-arcsinSinh x / π : ℝ) : ℂ) * I := by
  unfold pMap
  rw [show (π : ℂ) * (x : ℂ) = ((π * x : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sinh,
    complexArsinh_neg_I_mul (abs_sinh_le_one hx)]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  unfold arcsinSinh
  push_cast
  field_simp

/-- On the imaginary axis, `p(it) = π⁻¹ arsinh(sin πt)` is real. -/
theorem pMap_mul_I (t : ℝ) :
    pMap ((t : ℂ) * I) = ((Real.arsinh (Real.sin (π * t)) / π : ℝ) : ℂ) := by
  unfold pMap
  have h1 : Complex.sinh ((π : ℂ) * ((t : ℂ) * I)) = ((Real.sin (π * t) : ℝ) : ℂ) * I := by
    rw [← mul_assoc, show (π : ℂ) * (t : ℂ) = ((π * t : ℝ) : ℂ) by push_cast; rfl,
      Complex.sinh_mul_I, Complex.ofReal_sin]
  rw [h1, show -I * (((Real.sin (π * t) : ℝ) : ℂ) * I) = ((Real.sin (π * t) : ℝ) : ℂ) by
    rw [mul_comm (((Real.sin (π * t) : ℝ) : ℂ)) I, ← mul_assoc, neg_mul, Complex.I_mul_I]; ring,
    complexArsinh_ofReal]
  push_cast
  ring

/-! ### `U` along the real segment and the imaginary axis, `U(i/2) = 0` -/

/-- **`U` on the real segment through the paper's path-integral definition**:
`U(x) = U_0 + (4π/3) Im ∫_0^x p(w) dw` for `0 ≤ x ≤ ξ_*`. -/
theorem majorantReal_eq_path {x : ℝ} (hx : x ∈ Icc 0 xiStar) :
    majorantReal x = majorantU0 + (4 * π / 3) * (∫ s in (0 : ℝ)..x, pMap (s : ℂ)).im := by
  have habs : |x| = x := abs_of_nonneg hx.1
  rw [majorantReal_of_abs_le (by rw [habs]; exact hx.2), habs]
  have heq : ∀ s ∈ uIcc (0 : ℝ) x, pMap (s : ℂ) = ((-arcsinSinh s / π : ℝ) : ℂ) * I := by
    intro s hs
    rw [uIcc_of_le hx.1] at hs
    exact pMap_ofReal (by rw [abs_of_nonneg hs.1]; exact hs.2.trans hx.2)
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero]
  have : ∫ s in (0 : ℝ)..x, -arcsinSinh s / π = -(1 / π) * ∫ s in (0 : ℝ)..x, arcsinSinh s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show -arcsinSinh s / π = -(1 / π) * arcsinSinh s
    ring
  rw [this]
  have hpi := Real.pi_pos.ne'
  field_simp
  ring

/-- `U(iy) = U_0 + (4π/3) Im ∫_0^{iy} p(w) dw` (path `w = it`), explicitly `U_0 + (4/3) ∫_0^y
arsinh(sin πt) dt`. -/
noncomputable def majorantImag (y : ℝ) : ℝ :=
  majorantU0 + (4 * π / 3) * (Complex.I * ∫ t in (0 : ℝ)..y, pMap ((t : ℂ) * I)).im

theorem majorantImag_eq (y : ℝ) :
    majorantImag y = majorantU0 + (4 / 3) * ∫ t in (0 : ℝ)..y, Real.arsinh (Real.sin (π * t)) := by
  unfold majorantImag
  simp only [pMap_mul_I]
  rw [intervalIntegral.integral_ofReal, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, intervalIntegral.integral_div]
  have hpi := Real.pi_pos.ne'
  field_simp
  ring

theorem majorantImag_zero : majorantImag 0 = majorantU0 := by
  rw [majorantImag_eq]; simp

/-- **`U(i/2) = 0` on the upper strip edge** (Lemma G: "the inverse-area identity ... shows
`U(i/2) = 0`"). -/
theorem majorantImag_half : majorantImag (1 / 2) = 0 := by
  rw [majorantImag_eq, majorantU0_eq]; ring

/-- `U_0 ≤ 0`. -/
theorem majorantU0_nonpos : majorantU0 ≤ 0 := by
  rw [majorantU0_eq]
  have : 0 ≤ ∫ y in (0 : ℝ)..(1 / 2), Real.arsinh (Real.sin (π * y)) :=
    intervalIntegral.integral_nonneg (by norm_num) fun y hy => by
      have hpi := Real.pi_pos
      have : 0 ≤ Real.sin (π * y) := Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hy.1])
        (by nlinarith [hy.2])
      exact Real.arsinh_nonneg_iff.mpr this
  linarith

/-- `U ≤ 0` on the real axis. -/
theorem majorantReal_nonpos (x : ℝ) : majorantReal x ≤ 0 := by
  by_cases hx : |x| ≤ xiStar
  · rw [majorantReal_of_abs_le hx]
    have : 0 ≤ ∫ s in (0 : ℝ)..|x|, arcsinSinh s :=
      intervalIntegral.integral_nonneg (abs_nonneg x) fun s hs => by
        have hpi := Real.pi_pos
        exact Real.arcsin_nonneg.mpr (Real.sinh_nonneg_iff.mpr (by nlinarith [hs.1]))
    linarith [majorantU0_nonpos]
  · rw [majorantReal_of_lt_abs (not_le.mp hx)]
    unfold slitL; have := Real.pi_pos; have := abs_nonneg x
    have : 0 ≤ 2 * π * |x| / 3 := by positivity
    linarith

/-! ### Axiom checks for the headline theorems -/

/-- info: 'FormalResearch.ModularBootstrap.majorant_add_L_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorant_add_L_eq_integral

/-- info: 'FormalResearch.ModularBootstrap.majorant_add_L_eq_neg_slitDeficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorant_add_L_eq_neg_slitDeficit

/-- info: 'FormalResearch.ModularBootstrap.majorantReal_g_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorantReal_g_deficit

/-- info: 'FormalResearch.ModularBootstrap.inverse_area_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.inverse_area_identity

/-- info: 'FormalResearch.ModularBootstrap.majorantU0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorantU0_eq

/-- info: 'FormalResearch.ModularBootstrap.pMap_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.pMap_ofReal

/-- info: 'FormalResearch.ModularBootstrap.pMap_mul_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.pMap_mul_I

/-- info: 'FormalResearch.ModularBootstrap.majorantReal_eq_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorantReal_eq_path

/-- info: 'FormalResearch.ModularBootstrap.majorantImag_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorantImag_eq

/-- info: 'FormalResearch.ModularBootstrap.majorantImag_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorantImag_half

/-- info: 'FormalResearch.ModularBootstrap.majorantReal_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.majorantReal_nonpos

end FormalResearch.ModularBootstrap
