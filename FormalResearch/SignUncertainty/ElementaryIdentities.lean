module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Elementary Identities for Paper I (`u1co:O4`, `u1c:U1`)

Routine identities from `CFT/sign_uncertainty/paper/`, each as its own theorem:

* `O4_phase_increment`, `O4_square_increment`: the polynomial algebra in the contraction step
  of the proof of Lemma O.4(2) (`u1co:O4`, `u1c_estimate_proofs.tex`, step `[O4C (B)]`). Pure
  polynomial identities over a field of characteristic zero, with `p` standing for `π²`. The
  fixed-point argument itself is not formalised here.
* `u1c_U1_one_integral`: part (1) of Lemma U.1 (`u1c:U1`, `u1c_o1_upper.tex`) in the form
  `∫_{(0,∞)} (1 - e^{-x}) x^{-3/2} e^{-wx} dx = 2√π((1+w)^{1/2} - w^{1/2})` for `Re w > 0`, with
  principal branches (the boundary `Re w = 0` is not covered). Part (2) of Lemma U.1 is not
  formalised here.
(The Step 3 derivative of `lem:radial-compactness` is `hasDerivAt_xi_inv_radialKernel` in
`RadialCompactnessKernel`.)

Proof of U.1(1) in Lean: `(1 - e^{-x}) = ∫_0^1 x e^{-tx} dt` turns the integral into
`∫_0^1 ∫_{(0,∞)} x^{-1/2} e^{-(w+t)x} dx dt` (Fubini). The inner integral is the complex-rate
half-Gamma integral, obtained from Mathlib's complex Gaussian integral by the substitution
`u = x²`. The outer integral is elementary.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-! ### Section 1: The contraction algebra of Lemma O.4(2) (`u1co:O4`) -/

/-- **Algebra of the cubic normal form, first identity** (`u1co:O4`, proof step `[O4C (B)]` in
`CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`).

Let `p` stand for `π²`, `α = p θ₀² / 12` (the paper's `α̃ = (π²/12) θ₀²`) and `δ = θ (θ² - θ₀²) η`.
Then for `Φ(θ) = α θ - (p/36) θ³`,
`Φ(θ + δ) - Φ(θ) = -(p/36) θ (θ² - θ₀²)² (3η + 3θ²η² + θ²(θ² - θ₀²) η³)`.

Covered: this polynomial identity over any field of characteristic zero. Not covered: the
fixed-point argument that uses it. -/
theorem O4_phase_increment {K : Type*} [Field K] [CharZero K] (p θ θ₀ η α δ : K)
    (hα : α = p * θ₀ ^ 2 / 12) (hδ : δ = θ * (θ ^ 2 - θ₀ ^ 2) * η) :
    (α * (θ + δ) - p / 36 * (θ + δ) ^ 3) - (α * θ - p / 36 * θ ^ 3) =
      -(p / 36) * θ * (θ ^ 2 - θ₀ ^ 2) ^ 2 *
        (3 * η + 3 * θ ^ 2 * η ^ 2 + θ ^ 2 * (θ ^ 2 - θ₀ ^ 2) * η ^ 3) := by
  subst hα hδ
  ring

/-- The paper's `(π²/36)` case of `O4_phase_increment`, with `p = π²` in `ℂ`. -/
theorem O4_phase_increment_complex (θ θ₀ η α δ : ℂ)
    (hα : α = (Real.pi : ℂ) ^ 2 * θ₀ ^ 2 / 12) (hδ : δ = θ * (θ ^ 2 - θ₀ ^ 2) * η) :
    (α * (θ + δ) - (Real.pi : ℂ) ^ 2 / 36 * (θ + δ) ^ 3) -
        (α * θ - (Real.pi : ℂ) ^ 2 / 36 * θ ^ 3) =
      -((Real.pi : ℂ) ^ 2 / 36) * θ * (θ ^ 2 - θ₀ ^ 2) ^ 2 *
        (3 * η + 3 * θ ^ 2 * η ^ 2 + θ ^ 2 * (θ ^ 2 - θ₀ ^ 2) * η ^ 3) :=
  O4_phase_increment ((Real.pi : ℂ) ^ 2) θ θ₀ η α δ hα hδ

/-- **Algebra of the cubic normal form, second identity** (`u1co:O4`, proof step `[O4C (B)]` in
`CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`).

With `δ = θ (θ² - θ₀²) η` one has `(θ + δ)² - θ₀² = (θ² - θ₀²)(1 + 2θ²η + θ²(θ² - θ₀²) η²)`.

Covered: this polynomial identity over any field. Not covered: the fixed-point argument. -/
theorem O4_square_increment {K : Type*} [Field K] (θ θ₀ η δ : K)
    (hδ : δ = θ * (θ ^ 2 - θ₀ ^ 2) * η) :
    (θ + δ) ^ 2 - θ₀ ^ 2 =
      (θ ^ 2 - θ₀ ^ 2) * (1 + 2 * θ ^ 2 * η + θ ^ 2 * (θ ^ 2 - θ₀ ^ 2) * η ^ 2) := by
  subst hδ
  ring

/-- info: 'FormalResearch.SignUncertainty.O4_phase_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms O4_phase_increment

/-- info: 'FormalResearch.SignUncertainty.O4_phase_increment_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms O4_phase_increment_complex

/-- info: 'FormalResearch.SignUncertainty.O4_square_increment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms O4_square_increment

/-! ### Section 2: The Laplace-type integral of Lemma U.1(1) (`u1c:U1`) -/

lemma u1_ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    ((r : ℂ) * x) ^ s = (r : ℂ) ^ s * x ^ s := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hx), cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hx,
    log_ofReal_mul hr hx, add_mul, exp_add]
  simp only [Complex.ofReal_log hr.le]

lemma u1_div_cpow {r : ℝ} (hr : 0 < r) {b : ℂ} (hb : 0 < b.re) (s : ℂ) :
    ((r : ℂ) / b) ^ s = (r : ℂ) ^ s * b ^ (-s) := by
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hb; simp at hb
  have harg : b.arg ≠ π := by
    intro h; rw [arg_eq_pi_iff] at h; linarith [h.1]
  rw [div_eq_mul_inv, u1_ofReal_mul_cpow hr (inv_ne_zero hb0), inv_cpow _ _ harg, cpow_neg]

/-- The complex-rate half-Gamma integral `∫_{(0,∞)} x^{-1/2} e^{-bx} dx = √π b^{-1/2}` for
`Re b > 0`, principal branches. Derived from Mathlib's complex Gaussian integral
`integral_gaussian_complex_Ioi` by the substitution `u = x²` (`integral_comp_rpow_Ioi_of_pos`). -/
lemma u1_halfGamma_complex {b : ℂ} (hb : 0 < b.re) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-(b * x)) =
      (π : ℂ) ^ (1 / 2 : ℂ) * b ^ (-(1 / 2 : ℂ)) := by
  have hG := integral_gaussian_complex_Ioi hb
  have hsub : ∫ x in Ioi (0 : ℝ), ((1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1)) •
      cexp (-b * ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) ^ 2) = ∫ y in Ioi (0 : ℝ), cexp (-b * (y : ℂ) ^ 2) :=
    integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => cexp (-b * (y : ℂ) ^ 2)) (by norm_num)
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ((1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1)) •
      cexp (-b * ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) ^ 2) =
        (1 / 2 : ℂ) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-(b * x))) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h1 : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx'.le]; norm_num
    have h2 : ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) ^ 2 = (x : ℂ) := by exact_mod_cast h1
    have h3 : ((x ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) = (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num, Complex.ofReal_cpow hx'.le]
      congr 1; push_cast; ring
    rw [Complex.real_smul, h2, ← h3, neg_mul]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
  have hsol : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-(b * x))) =
      (π / b) ^ (1 / 2 : ℂ) := by
    rw [hG] at hsub
    linear_combination 2 * hsub
  rw [hsol, u1_div_cpow Real.pi_pos hb]

/-- `∫_0^1 (w + t)^{-1/2} dt = 2((1 + w)^{1/2} - w^{1/2})` for `Re w > 0`, principal branches. -/
lemma u1_integral_cpow_inv_sqrt {w : ℂ} (hw : 0 < w.re) :
    ∫ t in (0 : ℝ)..1, (w + (t : ℂ)) ^ (-(1 / 2 : ℂ)) =
      2 * ((1 + w) ^ (1 / 2 : ℂ) - w ^ (1 / 2 : ℂ)) := by
  have hslit : ∀ t ∈ uIcc (0 : ℝ) 1, w + (t : ℂ) ∈ slitPlane := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [mem_slitPlane_iff]
    left; simp only [add_re, ofReal_re]; linarith [ht.1, hw]
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => 2 * (w + (t : ℂ)) ^ (1 / 2 : ℂ))
      ((w + (t : ℂ)) ^ (-(1 / 2 : ℂ))) t := by
    intro t ht
    have hz : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ))
        ((1 / 2 : ℂ) * (w + (t : ℂ)) ^ ((1 / 2 : ℂ) - 1)) (w + (t : ℂ)) :=
      (Complex.hasStrictDerivAt_cpow_const (hslit t ht)).hasDerivAt
    have hl : HasDerivAt (fun t : ℝ => w + (t : ℂ)) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_add w
    have := (hz.comp t hl).const_mul 2
    refine this.congr_deriv ?_
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (w + (t : ℂ)) ^ (-(1 / 2 : ℂ))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hc : ContinuousAt (fun z : ℂ => z ^ (-(1 / 2 : ℂ))) (w + (t : ℂ)) :=
      continuousAt_cpow_const (hslit t ht)
    exact ContinuousAt.comp (f := fun t : ℝ => w + (t : ℂ)) hc (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [ofReal_zero, add_zero, ofReal_one]
  rw [add_comm w 1]
  ring

lemma u1_integrand_pointwise (w : ℂ) {x : ℝ} (hx : 0 < x) :
    ((1 - Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (-(3 / 2 : ℂ)) * cexp (-(w * x)) =
      ∫ t in (0 : ℝ)..1, (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + t) * x)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hne : -(x : ℂ) ≠ 0 := neg_ne_zero.mpr hx0
  have e1 : ∀ t : ℝ, (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + t) * x)) =
      ((x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-(w * x))) * cexp ((-(x : ℂ)) * t) := by
    intro t
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hne]
  have hxpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = (x : ℂ) ^ (-(3 / 2 : ℂ)) * x := by
    calc (x : ℂ) ^ (-(1 / 2 : ℂ)) = (x : ℂ) ^ (-(3 / 2 : ℂ) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  have hexp : cexp (-(x : ℂ) * ((1 : ℝ) : ℂ)) = ((Real.exp (-x) : ℝ) : ℂ) := by
    rw [ofReal_one, mul_one, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp, hxpow, ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  push_cast
  ring

lemma u1_norm_integrand_le (w : ℂ) {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    ‖(x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + t) * x))‖ ≤
      x ^ (-(1 / 2 : ℝ)) * Real.exp (-(w.re) * x) := by
  have h1 : ‖(x : ℂ) ^ (-(1 / 2 : ℂ))‖ = x ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; norm_num
  have h2 : ‖cexp (-((w + t) * x))‖ ≤ Real.exp (-(w.re) * x) := by
    rw [Complex.norm_exp, Real.exp_le_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [mul_nonneg ht hx.le]
  rw [norm_mul, h1]
  exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx.le _)

lemma u1_integrable_prod (w : ℂ) (hw : 0 < w.re) :
    Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + p.2) * p.1)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hint_h : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * Real.exp (-(w.re) * x))
      (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ)) (b := w.re)
      (by norm_num) one_pos hw
    simpa only [Real.rpow_one] using this
  have hint1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    integrable_const 1
  have hbig := hint_h.mul_prod hint1
  refine hbig.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    simp only [mul_one]
    exact u1_norm_integrand_le w hx (le_of_lt ht.1)

lemma u1_sqrt_pi_cpow : ((Real.sqrt π : ℝ) : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  norm_num

/-- **Lemma U.1(1)** (`u1c:U1`, `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`), at complex `w`:
for `Re w > 0`, with principal branches,
`∫_{(0,∞)} (1 - e^{-x}) x^{-3/2} e^{-wx} dx = 2√π ((1 + w)^{1/2} - w^{1/2})`.

The paper states `k ∫ F_lead(u) e^{w̃u} du = γ_* ((1+w̃)^{1/2} - w̃^{1/2})` with
`F_lead(u) = (β_∞(F_0)/2π) 1_{u<0} (1 - e^u)(-u)^{-3/2}` and `γ_* = k β_∞(F_0)/√π`. Dividing by
`k β_∞(F_0)/(2π)` and substituting `x = -u` gives the integral stated here. Covered: part (1)
only, and only for `Re w > 0`: the paper's closed half-plane `Re w ≥ 0` (boundary values,
e.g. `w = 0`, `∫ (1 - e^{-x}) x^{-3/2} dx = 2√π`) is not covered. Not covered: part (2) of
Lemma U.1 (the square-root expansion of `W̃_0` and the rational-Airy hypotheses). -/
theorem u1c_U1_one_integral {w : ℂ} (hw : 0 < w.re) :
    ∫ x in Ioi (0 : ℝ), ((1 - Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (-(3 / 2 : ℂ)) *
        cexp (-(w * x)) =
      2 * (Real.sqrt π : ℂ) * ((1 + w) ^ (1 / 2 : ℂ) - w ^ (1 / 2 : ℂ)) := by
  have step1 : ∫ x in Ioi (0 : ℝ), ((1 - Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (-(3 / 2 : ℂ)) *
      cexp (-(w * x)) = ∫ x in Ioi (0 : ℝ), ∫ t in Ioo (0 : ℝ) 1,
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + t) * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [u1_integrand_pointwise w hx, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  have step2 : ∫ x in Ioi (0 : ℝ), ∫ t in Ioo (0 : ℝ) 1,
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + t) * x)) =
      ∫ t in Ioo (0 : ℝ) 1, ∫ x in Ioi (0 : ℝ),
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + t) * x)) :=
    integral_integral_swap (u1_integrable_prod w hw)
  have step3 : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-((w + t) * x)) =
      (π : ℂ) ^ (1 / 2 : ℂ) * (w + (t : ℂ)) ^ (-(1 / 2 : ℂ)) := by
    intro t ht
    have hre : 0 < (w + (t : ℂ)).re := by
      simp only [add_re, ofReal_re]; linarith [ht.1, hw]
    exact u1_halfGamma_complex hre
  have hI : ∫ t in Ioo (0 : ℝ) 1, (w + (t : ℂ)) ^ (-(1 / 2 : ℂ)) =
      2 * ((1 + w) ^ (1 / 2 : ℂ) - w ^ (1 / 2 : ℂ)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact u1_integral_cpow_inv_sqrt hw
  rw [step1, step2, setIntegral_congr_fun measurableSet_Ioo step3, integral_const_mul, hI,
    u1_sqrt_pi_cpow]
  ring

/-- info: 'FormalResearch.SignUncertainty.u1c_U1_one_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms u1c_U1_one_integral

end FormalResearch.SignUncertainty
