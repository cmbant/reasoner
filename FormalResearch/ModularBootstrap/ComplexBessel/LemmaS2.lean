module

public import FormalResearch.ModularBootstrap.ComplexBessel.ComplexExpansion
public import FormalResearch.ModularBootstrap.ComplexBessel.StirlingOmega
public import FormalResearch.ModularBootstrap.Integration.HankelBounds
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Crude Legendre Bound (Lemma S2, `vlo:S2`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S2 (`vlo:S2`,
lines 370–407).

For `ω = μ + i ν` with `μ ≥ μ₀ > π ξ_* / 6`, `z = 1/2 + c' ω`, `g ∈ TestClass virasoroProblem (c'/12)`,
and all sufficiently large `c'`:
`|m_g(1/2 + c' ω)| ≤ C e^{c' B(ω)} M[g]`,
where `m_g(z) = (2π)^z Mg(z) / Γ(z)`, `Mg(z) = ∫₀^∞ g(t) t^{z-1} dt`, and
`B(ω) = μ log(6 μ² / (π |ω|)) - μ + ν arg ω`.

Proof follows the paper's concavity / one-point-derivative argument:
* On `x ≥ x_c = ξ_* / 2` (`t = c' x^2 / 3`), `besselV_comparison` bounds
  `A_2(x) = t^{-1/2} e^{c' L(x)} / V(t) ≤ 6π / √x_c`, and `D(x_*, x) ≥ 0`.
* On `0 < x ≤ x_c`, `f(s) = (Re z - 1) s - log V(e^s)` is concave (`(log V(e^s))'' ≥ 0` by
  Cauchy–Schwarz on the nonnegative Bessel series coefficients `v_k ≥ 0`), and differentiating
  `besselComplexExpansion {x_c}` gives `f'(s_c) = c'(μ - π x_c / 3) + O(1) > 0`, so
  `f(s) ≤ f(s_c)` for all `s ≤ s_c`.

## Main definitions and results
* `mellinTransformG`, `mellinMG`, `crudeExponentB`, `crudeDivergenceD`.
* `lemma_S2`: **Lemma S2** (`vlo:S2`), proving both convergence of `Mg(1/2 + c' ω)` and the
  uniform bound `‖m_g(1/2 + c' ω)‖ ≤ C exp(c' B(ω)) M[g]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.ComplexBessel

/-! ### Section 1: Mellin definitions and crude exponent algebra -/

/-- Mellin transform `Mg(z) = ∫₀^∞ g(t) t^{z - 1} dt` (`lower_o1_two_edge.tex`, §J2). -/
noncomputable def mellinTransformG (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)

/-- Symmetric Mellin density `m_g(z) = (2π)^z Mg(z) / Γ(z)` (`lower_o1_two_edge.tex`, §J2). -/
noncomputable def mellinMG (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ z * mellinTransformG g z / Complex.Gamma z

/-- Crude Legendre exponent `B(ω) = μ log(6 μ² / (π |ω|)) - μ + ν arg ω` (`μ = Re ω`,
`ν = Im ω`, `lower_o1_two_edge.tex`, §J2). -/
noncomputable def crudeExponentB (ω : ℂ) : ℝ :=
  ω.re * Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) - ω.re + ω.im * ω.arg

/-- Legendre Bregman divergence `D(y, x) = (2π/3)(x - y - y log(x/y))` (`lower_o1_two_edge.tex`,
Lemma S2 proof). -/
noncomputable def crudeDivergenceD (y x : ℝ) : ℝ :=
  (2 * Real.pi / 3) * (x - y - y * Real.log (x / y))

lemma crudeDivergenceD_nonneg {y x : ℝ} (hy : 0 < y) (hx : 0 < x) :
    0 ≤ crudeDivergenceD y x := by
  unfold crudeDivergenceD
  have hlog : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have hmul : y * Real.log (x / y) ≤ x - y := by
    have := mul_le_mul_of_nonneg_left hlog hy.le
    have hy0 : y ≠ 0 := hy.ne'
    calc y * Real.log (x / y) ≤ y * (x / y - 1) := this
      _ = x - y := by field_simp [hy0]
  have : 0 ≤ x - y - y * Real.log (x / y) := by linarith
  positivity

private lemma re_stirlingJ_ofReal {ω : ℂ} (_hω_re : 0 < ω.re) {x : ℝ} (hx : 0 < x) :
    (stirlingJ ω (x : ℂ)).re =
      ω.re * (Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x) -
        ω.im * ω.arg := by
  have hr_pos : 0 < 3 / (2 * Real.pi * Real.exp 1) := by positivity
  have harg_eq : (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))).arg = ω.arg := by
    rw [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) =
        ((3 / (2 * Real.pi * Real.exp 1) : ℝ) : ℂ) * ω by push_cast; ring]
    exact Complex.arg_real_mul ω hr_pos
  have hnorm_eq : ‖3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))‖ =
      3 * ‖ω‖ / (2 * Real.pi * Real.exp 1) := by
    simp only [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg (Real.exp_pos 1).le]
  have hlog1_re : (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)))).re =
      Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) := by
    rw [Complex.log_re, hnorm_eq]
  have hlog1_im : (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)))).im = ω.arg := by
    rw [Complex.log_im, harg_eq]
  have hlog2 : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
  unfold stirlingJ
  rw [Complex.mul_re, Complex.sub_re, Complex.sub_im, hlog1_re, hlog1_im, hlog2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero]

private lemma exponent_identity {ω : ℂ} (hω_re : 0 < ω.re) {x : ℝ} (hx : 0 < x) :
    crudeExponentB ω + (stirlingJ ω (x : ℂ)).re + Bessel.besselL x =
      crudeDivergenceD (3 * ω.re / Real.pi) x := by
  rw [re_stirlingJ_ofReal hω_re hx]
  unfold crudeExponentB Bessel.besselL crudeDivergenceD
  have hω_norm : 0 < ‖ω‖ := lt_of_lt_of_le hω_re (Complex.re_le_norm ω)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hlog_sum : Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) +
      Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x =
      2 * Real.log ((3 * ω.re / Real.pi) / x) - 1 := by
    have hprod : (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) * (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) =
        (3 * ω.re / Real.pi) ^ 2 / Real.exp 1 := by
      field_simp [hpi.ne', hω_norm.ne', hexp1.ne']
      ring
    rw [← Real.log_mul (by positivity) (by positivity), hprod,
      Real.log_div (by positivity) hexp1.ne', Real.log_exp,
      Real.log_pow, Real.log_div (by positivity) hx.ne']
    push_cast; ring
  have hlog_neg : Real.log (x / (3 * ω.re / Real.pi)) =
      -Real.log ((3 * ω.re / Real.pi) / x) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog_neg]
  calc ω.re * Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) - ω.re + ω.im * ω.arg +
        (ω.re * (Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x) -
          ω.im * ω.arg) + 2 * Real.pi * x / 3
      = ω.re * (Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) +
          Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x) - ω.re +
          2 * Real.pi * x / 3 := by ring
    _ = ω.re * (2 * Real.log ((3 * ω.re / Real.pi) / x) - 1) - ω.re +
          2 * Real.pi * x / 3 := by rw [hlog_sum]
    _ = (2 * Real.pi / 3) * (x - 3 * ω.re / Real.pi -
          3 * ω.re / Real.pi * -Real.log ((3 * ω.re / Real.pi) / x)) := by
        field_simp [hpi.ne']; ring

private lemma norm_kernel_eq {c' : ℝ} (hc' : 24 ≤ c') {ω : ℂ} (hω_re : 0 < ω.re)
    {t : ℝ} (ht : 0 < t) :
    let z : ℂ := 1 / 2 + (c' : ℂ) * ω
    let x : ℝ := √(3 * t / c')
    ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
        Bessel.besselV (c' / 12) t =
      ‖(stirlingS c' ω)⁻¹‖ *
        (1 / √t * Real.exp (c' * Bessel.besselL x) / Bessel.besselV (c' / 12) t) *
        Real.exp (c' * crudeExponentB ω) *
        Real.exp (-c' * crudeDivergenceD (3 * ω.re / Real.pi) x) := by
  intro z x
  have hc'_pos : 0 < c' := by linarith
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have ht_eq : t = c' * x ^ 2 / 3 := by
    dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
  have ht_c_eq : (t : ℂ) = (c' : ℂ) * (x : ℂ) ^ 2 / 3 := by exact_mod_cast ht_eq
  have hω_ne : ω ≠ 0 := by intro h; rw [h, Complex.zero_re] at hω_re; exact lt_irrefl 0 hω_re
  have hst := gamma_mul_two_pi_t_cpow_neg hc'_pos hω_re.le hω_ne
    (show 0 < (x : ℂ).re by simpa using hx_pos)
  dsimp only at hst
  rw [← ht_c_eq] at hst
  have hz_re : 0 < z.re := by
    simp only [z, Complex.add_re, Complex.re_ofReal_mul]
    norm_num
    linarith [mul_pos hc'_pos hω_re]
  have hgam_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero (fun n hn => by
      have : z.re = -(n : ℝ) := by rw [hn]; simp
      linarith [Nat.cast_nonneg (α := ℝ) n])
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hcpow_num : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) =
      (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z * (t : ℂ)⁻¹ := by
    have hmul : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z = (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ z := by
      simpa [Complex.ofReal_mul] using ofReal_mul_cpow (by positivity : (0 : ℝ) < 2 * Real.pi) (t : ℂ) z
    have hsub : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ z * (t : ℂ)⁻¹ := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ ht_ne, Complex.cpow_neg_one]
    rw [hmul, hsub]; ring
  have hcpow_neg : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-z) =
      ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹ :=
    Complex.cpow_neg _ _
  have hS_ne : stirlingS c' ω ≠ 0 := Complex.exp_ne_zero _
  have ht_half_ne : (t : ℂ) ^ (-(1 / 2 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl ht_ne)
  have hexp_J_ne : Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hratio : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z =
      (stirlingS c' ω)⁻¹ * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
    have hinv : Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹ =
        (t : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) * stirlingS c' ω := by
      rwa [hcpow_neg] at hst
    have hgam_eq : ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z) / Complex.Gamma z =
        (stirlingS c' ω)⁻¹ * ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
      rw [Complex.exp_neg]
      have h2pit_ne : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero h2pi_ne ht_ne))
      calc (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z / Complex.Gamma z
          = (Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹)⁻¹ := by
            field_simp [hgam_ne, h2pit_ne]
        _ = ((t : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) *
              stirlingS c' ω)⁻¹ := by rw [hinv]
        _ = (stirlingS c' ω)⁻¹ * ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
              (Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)))⁻¹ := by
            field_simp [hS_ne, ht_half_ne, hexp_J_ne]
    have hthalf_inv : ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹ = (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [← Complex.cpow_neg, neg_neg, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht_ne]
      congr 1; norm_num
    rw [hcpow_num, mul_div_right_comm, hgam_eq]
    calc (stirlingS c' ω)⁻¹ * ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) * (t : ℂ)⁻¹
        = (stirlingS c' ω)⁻¹ * (((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by ring
      _ = (stirlingS c' ω)⁻¹ * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by rw [hthalf_inv]
  have hthalf_norm : ‖(t : ℂ) ^ (-(1 / 2 : ℂ))‖ = 1 / √t := by
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow ht.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, Real.sqrt_eq_rpow, one_div]
    norm_num
  have hexp_J_norm : ‖Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ)))‖ =
      Real.exp (c' * crudeExponentB ω + c' * Bessel.besselL x -
        c' * crudeDivergenceD (3 * ω.re / Real.pi) x) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.neg_re, Complex.re_ofReal_mul]
    have hid := exponent_identity hω_re hx_pos
    calc -(c' * (stirlingJ ω (x : ℂ)).re)
        = c' * (crudeExponentB ω + Bessel.besselL x -
            (crudeExponentB ω + (stirlingJ ω (x : ℂ)).re + Bessel.besselL x)) := by ring
      _ = c' * crudeExponentB ω + c' * Bessel.besselL x -
            c' * crudeDivergenceD (3 * ω.re / Real.pi) x := by rw [hid]; ring
  rw [hratio, norm_mul, norm_mul, hthalf_norm, hexp_J_norm, Real.exp_sub, Real.exp_add]
  have hV_ne : Bessel.besselV (c' / 12) t ≠ 0 := by
    have := Bessel.besselV_ge (a := c' / 12) (by linarith) ht.le
    have hpi4 : 0 < 8 * Real.pi ^ 4 * t ^ 2 := by positivity
    linarith
  have hD_pos : 0 < Real.exp (c' * crudeDivergenceD (3 * ω.re / Real.pi) x) := Real.exp_pos _
  rw [show -c' * crudeDivergenceD (3 * ω.re / Real.pi) x =
      -(c' * crudeDivergenceD (3 * ω.re / Real.pi) x) by ring, Real.exp_neg]
  field_simp [hV_ne, hD_pos.ne']

/-! ### Section 2: Convexity of `s ↦ log V(e^s)` and derivative at `x_c = ξ_*/2` -/

private noncomputable def besselVDeriv1 (a t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * Bessel.besselVCoeff a k * t ^ k

private noncomputable def besselVDeriv2 (a t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * t ^ k

private lemma besselV_eq_re_besselVC {c' : ℝ} (hc' : 24 ≤ c') {t : ℝ} (ht : 0 ≤ t) :
    (Bessel.besselV (c' / 12) t : ℂ) = Bessel.besselVC (c' / 12) (t : ℂ) := by
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hs := Complex.ofRealCLM.hasSum (Bessel.besselV_hasSum ha ht)
  unfold Bessel.besselVC
  refine hs.tsum_eq.symm.trans ?_
  refine tsum_congr fun k => ?_
  simp

private lemma summable_besselVCoeff_mul_pow {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    Summable fun k : ℕ => Bessel.besselVCoeff a k * t ^ k :=
  (Bessel.besselV_hasSum ha ht).summable

private lemma nat_le_two_pow (k : ℕ) : (k : ℝ) ≤ (2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    push_cast
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by ring
    linarith

private lemma summable_besselVDeriv1 {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    Summable fun k : ℕ => (k : ℝ) * Bessel.besselVCoeff a k * t ^ k := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (Nat.cast_nonneg k)
      (Bessel.besselVCoeff_nonneg ha k)) (pow_nonneg ht k)) (fun k => ?_)
    (summable_besselVCoeff_mul_pow ha (by linarith : 0 ≤ 2 * t))
  calc (k : ℝ) * Bessel.besselVCoeff a k * t ^ k
      ≤ (2 : ℝ) ^ k * Bessel.besselVCoeff a k * t ^ k := by
        gcongr
        · exact Bessel.besselVCoeff_nonneg ha k
        · exact nat_le_two_pow k
    _ = Bessel.besselVCoeff a k * (2 * t) ^ k := by rw [mul_pow]; ring

private lemma summable_besselVDeriv2 {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    Summable fun k : ℕ => (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * t ^ k := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (sq_nonneg (k : ℝ))
      (Bessel.besselVCoeff_nonneg ha k)) (pow_nonneg ht k)) (fun k => ?_)
    (summable_besselVCoeff_mul_pow ha (by linarith : 0 ≤ 4 * t))
  have hk2 : (k : ℝ) ^ 2 ≤ (4 : ℝ) ^ k := by
    have h1 := nat_le_two_pow k
    have h2 : (k : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by gcongr
    rwa [← pow_mul, mul_comm, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num] at h2
  calc (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * t ^ k
      ≤ (4 : ℝ) ^ k * Bessel.besselVCoeff a k * t ^ k := by
        gcongr
        exact Bessel.besselVCoeff_nonneg ha k
    _ = Bessel.besselVCoeff a k * (4 * t) ^ k := by rw [mul_pow]; ring

private lemma hasDerivAt_besselV_exp {a : ℝ} (ha : 2 ≤ a) (s : ℝ) :
    HasDerivAt (fun u : ℝ => Bessel.besselV a (Real.exp u)) (besselVDeriv1 a (Real.exp s)) s := by
  let R : ℝ := s + 1
  have hsR : s ∈ Iio R := by change s < R; dsimp [R]; linarith
  have heq : (fun u : ℝ => Bessel.besselV a (Real.exp u)) =
      fun u : ℝ => ∑' k : ℕ, Bessel.besselVCoeff a k * (Real.exp u) ^ k := by
    ext u; exact (Bessel.besselV_hasSum ha (Real.exp_pos u).le).tsum_eq.symm
  rw [heq]
  have hu_sum : Summable fun k : ℕ => (k : ℝ) * Bessel.besselVCoeff a k * (Real.exp R) ^ k :=
    summable_besselVDeriv1 ha (Real.exp_pos R).le
  unfold besselVDeriv1
  refine hasDerivAt_tsum_of_isPreconnected
    (g' := fun (k : ℕ) (u : ℝ) => (k : ℝ) * Bessel.besselVCoeff a k * (Real.exp u) ^ k)
    hu_sum isOpen_Iio isPreconnected_Iio
    (fun k u _ => ?_) (fun k u hu => ?_) hsR (summable_besselVCoeff_mul_pow ha (Real.exp_pos s).le)
    hsR
  · have hd : HasDerivAt (fun x : ℝ => (Real.exp x) ^ k)
        ((k : ℝ) * (Real.exp u) ^ (k - 1) * Real.exp u) u :=
      (Real.hasDerivAt_exp u).pow k
    refine (hd.const_mul (Bessel.besselVCoeff a k)).congr_deriv ?_
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  · have hnn : 0 ≤ (k : ℝ) * Bessel.besselVCoeff a k * (Real.exp u) ^ k :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (Bessel.besselVCoeff_nonneg ha k))
        (pow_nonneg (Real.exp_pos u).le k)
    rw [Real.norm_of_nonneg hnn]
    have hle : Real.exp u ≤ Real.exp R := Real.exp_le_exp.mpr (mem_Iio.mp hu).le
    gcongr
    exact mul_nonneg (Nat.cast_nonneg k) (Bessel.besselVCoeff_nonneg ha k)

private lemma hasDerivAt_besselVDeriv1_exp {a : ℝ} (ha : 2 ≤ a) (s : ℝ) :
    HasDerivAt (fun u : ℝ => besselVDeriv1 a (Real.exp u)) (besselVDeriv2 a (Real.exp s)) s := by
  let R : ℝ := s + 1
  have hsR : s ∈ Iio R := by change s < R; dsimp [R]; linarith
  have hu_sum : Summable fun k : ℕ => (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * (Real.exp R) ^ k :=
    summable_besselVDeriv2 ha (Real.exp_pos R).le
  unfold besselVDeriv1 besselVDeriv2
  refine hasDerivAt_tsum_of_isPreconnected
    (g' := fun (k : ℕ) (u : ℝ) => (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * (Real.exp u) ^ k)
    hu_sum isOpen_Iio isPreconnected_Iio
    (fun k u _ => ?_) (fun k u hu => ?_) hsR (summable_besselVDeriv1 ha (Real.exp_pos s).le) hsR
  · have hd : HasDerivAt (fun x : ℝ => (Real.exp x) ^ k)
        ((k : ℝ) * (Real.exp u) ^ (k - 1) * Real.exp u) u :=
      (Real.hasDerivAt_exp u).pow k
    refine (hd.const_mul ((k : ℝ) * Bessel.besselVCoeff a k)).congr_deriv ?_
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  · have hnn : 0 ≤ (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * (Real.exp u) ^ k :=
      mul_nonneg (mul_nonneg (sq_nonneg (k : ℝ)) (Bessel.besselVCoeff_nonneg ha k))
        (pow_nonneg (Real.exp_pos u).le k)
    rw [Real.norm_of_nonneg hnn]
    have hle : Real.exp u ≤ Real.exp R := Real.exp_le_exp.mpr (mem_Iio.mp hu).le
    gcongr
    exact mul_nonneg (sq_nonneg (k : ℝ)) (Bessel.besselVCoeff_nonneg ha k)

private lemma besselVDeriv1_sq_le {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    besselVDeriv1 a t ^ 2 ≤ Bessel.besselV a t * besselVDeriv2 a t := by
  have hs0 := Bessel.besselV_hasSum ha ht
  have hs1 := (summable_besselVDeriv1 ha ht).hasSum
  have hs2 := (summable_besselVDeriv2 ha ht).hasSum
  have hfin : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (k : ℝ) * Bessel.besselVCoeff a k * t ^ k) ^ 2 ≤
        (∑ k ∈ Finset.range N, Bessel.besselVCoeff a k * t ^ k) *
          (∑ k ∈ Finset.range N, (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * t ^ k) := by
    intro N
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun k => √(Bessel.besselVCoeff a k * t ^ k))
      (fun k => (k : ℝ) * √(Bessel.besselVCoeff a k * t ^ k))
    have hlhs : (∑ k ∈ Finset.range N, √(Bessel.besselVCoeff a k * t ^ k) *
          ((k : ℝ) * √(Bessel.besselVCoeff a k * t ^ k))) =
        ∑ k ∈ Finset.range N, (k : ℝ) * Bessel.besselVCoeff a k * t ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hnn : 0 ≤ Bessel.besselVCoeff a k * t ^ k :=
        mul_nonneg (Bessel.besselVCoeff_nonneg ha k) (pow_nonneg ht k)
      calc √(Bessel.besselVCoeff a k * t ^ k) * ((k : ℝ) * √(Bessel.besselVCoeff a k * t ^ k))
          = (k : ℝ) * (√(Bessel.besselVCoeff a k * t ^ k) * √(Bessel.besselVCoeff a k * t ^ k)) := by ring
        _ = (k : ℝ) * (Bessel.besselVCoeff a k * t ^ k) := by rw [Real.mul_self_sqrt hnn]
        _ = (k : ℝ) * Bessel.besselVCoeff a k * t ^ k := by ring
    have hrhs1 : (∑ k ∈ Finset.range N, (√(Bessel.besselVCoeff a k * t ^ k)) ^ 2) =
        ∑ k ∈ Finset.range N, Bessel.besselVCoeff a k * t ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact Real.sq_sqrt (mul_nonneg (Bessel.besselVCoeff_nonneg ha k) (pow_nonneg ht k))
    have hrhs2 : (∑ k ∈ Finset.range N, ((k : ℝ) * √(Bessel.besselVCoeff a k * t ^ k)) ^ 2) =
        ∑ k ∈ Finset.range N, (k : ℝ) ^ 2 * Bessel.besselVCoeff a k * t ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (Bessel.besselVCoeff_nonneg ha k) (pow_nonneg ht k))]
      ring
    rwa [hlhs, hrhs1, hrhs2] at hcs
  have ht0 := hs0.tendsto_sum_nat
  have ht1 := (hs1.tendsto_sum_nat).pow 2
  have ht2 := ht0.mul hs2.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto ht1 ht2 (Eventually.of_forall hfin)

private lemma monotone_deriv_log_besselV_exp {a : ℝ} (ha : 2 ≤ a) :
    Monotone (fun s : ℝ => besselVDeriv1 a (Real.exp s) / Bessel.besselV a (Real.exp s)) := by
  refine monotone_of_deriv_nonneg ?_ ?_
  · intro s
    have hV_pos : 0 < Bessel.besselV a (Real.exp s) := by
      have := Bessel.besselV_ge ha (Real.exp_pos s).le
      have hpos : 0 < 8 * Real.pi ^ 4 * (Real.exp s) ^ 2 := by positivity
      linarith
    exact ((hasDerivAt_besselVDeriv1_exp ha s).div (hasDerivAt_besselV_exp ha s)
      hV_pos.ne').differentiableAt
  · intro s
    have hV_pos : 0 < Bessel.besselV a (Real.exp s) := by
      have := Bessel.besselV_ge ha (Real.exp_pos s).le
      have hpos : 0 < 8 * Real.pi ^ 4 * (Real.exp s) ^ 2 := by positivity
      linarith
    have hd := (hasDerivAt_besselVDeriv1_exp ha s).div (hasDerivAt_besselV_exp ha s) hV_pos.ne'
    rw [show (fun s : ℝ => besselVDeriv1 a (Real.exp s) / Bessel.besselV a (Real.exp s)) =
        (fun u : ℝ => besselVDeriv1 a (Real.exp u)) / (fun u : ℝ => Bessel.besselV a (Real.exp u))
        from rfl, hd.deriv]
    have hcs := besselVDeriv1_sq_le ha (Real.exp_pos s).le
    have hnum : 0 ≤ besselVDeriv2 a (Real.exp s) * Bessel.besselV a (Real.exp s) -
        besselVDeriv1 a (Real.exp s) * besselVDeriv1 a (Real.exp s) := by nlinarith [hcs]
    exact div_nonneg hnum (sq_nonneg _)

private lemma besselV_exp_concavity_le {c' α : ℝ} (hc' : 24 ≤ c') {s_c s : ℝ} (hs : s ≤ s_c)
    (hderiv_sc : besselVDeriv1 (c' / 12) (Real.exp s_c) /
      Bessel.besselV (c' / 12) (Real.exp s_c) ≤ α) :
    α * s - Real.log (Bessel.besselV (c' / 12) (Real.exp s)) ≤
      α * s_c - Real.log (Bessel.besselV (c' / 12) (Real.exp s_c)) := by
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  let f : ℝ → ℝ := fun u => α * u - Real.log (Bessel.besselV (c' / 12) (Real.exp u))
  let f' : ℝ → ℝ := fun u =>
    α - besselVDeriv1 (c' / 12) (Real.exp u) / Bessel.besselV (c' / 12) (Real.exp u)
  have hmono : MonotoneOn f (Iic s_c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic s_c) ?_ ?_ ?_
    · intro u _
      have hV_pos : 0 < Bessel.besselV (c' / 12) (Real.exp u) := by
        have := Bessel.besselV_ge ha (Real.exp_pos u).le
        have hpos : 0 < 8 * Real.pi ^ 4 * (Real.exp u) ^ 2 := by positivity
        linarith
      have h1 : HasDerivAt (fun v : ℝ => α * v) α u := by
        simpa using (hasDerivAt_id u).const_mul α
      have h2 : HasDerivAt (fun v : ℝ => Real.log (Bessel.besselV (c' / 12) (Real.exp v)))
          (besselVDeriv1 (c' / 12) (Real.exp u) / Bessel.besselV (c' / 12) (Real.exp u)) u :=
        (hasDerivAt_besselV_exp ha u).log hV_pos.ne'
      exact (h1.sub h2).continuousAt.continuousWithinAt
    · intro u _
      have hV_pos : 0 < Bessel.besselV (c' / 12) (Real.exp u) := by
        have := Bessel.besselV_ge ha (Real.exp_pos u).le
        have hpos : 0 < 8 * Real.pi ^ 4 * (Real.exp u) ^ 2 := by positivity
        linarith
      have h1 : HasDerivAt (fun v : ℝ => α * v) α u := by
        simpa using (hasDerivAt_id u).const_mul α
      have h2 : HasDerivAt (fun v : ℝ => Real.log (Bessel.besselV (c' / 12) (Real.exp v)))
          (besselVDeriv1 (c' / 12) (Real.exp u) / Bessel.besselV (c' / 12) (Real.exp u)) u :=
        (hasDerivAt_besselV_exp ha u).log hV_pos.ne'
      exact (h1.sub h2).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Iic] at hu
      have hV_pos : 0 < Bessel.besselV (c' / 12) (Real.exp u) := by
        have := Bessel.besselV_ge ha (Real.exp_pos u).le
        have hpos : 0 < 8 * Real.pi ^ 4 * (Real.exp u) ^ 2 := by positivity
        linarith
      have h1 : HasDerivAt (fun v : ℝ => α * v) α u := by
        simpa using (hasDerivAt_id u).const_mul α
      have h2 : HasDerivAt (fun v : ℝ => Real.log (Bessel.besselV (c' / 12) (Real.exp v)))
          (besselVDeriv1 (c' / 12) (Real.exp u) / Bessel.besselV (c' / 12) (Real.exp u)) u :=
        (hasDerivAt_besselV_exp ha u).log hV_pos.ne'
      dsimp only [f]
      rw [show (fun u : ℝ => α * u - Real.log (Bessel.besselV (c' / 12) (Real.exp u))) =
          (fun v : ℝ => α * v) - (fun v : ℝ => Real.log (Bessel.besselV (c' / 12) (Real.exp v)))
          from rfl, (h1.sub h2).deriv]
      have hm := monotone_deriv_log_besselV_exp ha hu.le
      linarith
  exact hmono hs (mem_Iic.mpr le_rfl) hs

/-! ### Section 3: Derivative of `log V(c' x^2 / 3)` at `x_c = ξ_* / 2` via `besselComplexExpansion` -/

private lemma deriv_log_besselV_at_xc :
    ∃ C_d c_d : ℝ, 0 ≤ C_d ∧ 24 ≤ c_d ∧
      ∀ {c' : ℝ}, c_d ≤ c' →
        let x_c : ℝ := xiStar / 2
        let t_c : ℝ := c' * x_c ^ 2 / 3
        besselVDeriv1 (c' / 12) t_c / Bessel.besselV (c' / 12) t_c ≤
          Real.pi * c' * x_c / 3 + C_d := by
  have hexp := besselComplexExpansion {xiStar / 2}
    isCompact_singleton (singleton_subset_iff.mpr (by simp [xiStar_pos]))
  obtain ⟨δ, hδ_pos, C₀, c₀, hbd0, hbd_deriv⟩ := hexp
  obtain ⟨C₁, hbd1⟩ := hbd_deriv 1
  let x_c : ℝ := xiStar / 2
  have hx_c_pos : 0 < x_c := by dsimp [x_c]; linarith [xiStar_pos]
  let q : ℝ := Real.exp (-4 * Real.pi * x_c)
  have hq_lt1 : q < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hx_c_pos]
  have hq_pos : 0 < q := Real.exp_pos _
  let br0 : ℝ := (1 - q) ^ 2
  have hbr0_pos : 0 < br0 := sq_pos_of_pos (sub_pos.mpr hq_lt1)
  -- Ensure c' ≥ max c₀ 24 and |C₀|/c' ≤ br0 / 2
  let c_d : ℝ := max (max c₀ 24) (2 * |C₀| / br0 + 1)
  have hc_d_24 : 24 ≤ c_d := (le_max_right c₀ 24).trans (le_max_left _ _)
  let C_d : ℝ := (x_c / 2) * (1 / (2 * x_c) + (2 / br0) * (8 * Real.pi * (1 - q) * q + |C₁| / 24))
  refine ⟨C_d, c_d, ?_, hc_d_24, fun {c'} hc' => ?_⟩
  · dsimp [C_d]; positivity
  · intro x_c' t_c
    change besselVDeriv1 (c' / 12) t_c / Bessel.besselV (c' / 12) t_c ≤
      Real.pi * c' * x_c / 3 + C_d
    have hc'_pos : 0 < c' := by linarith
    have hc'_24 : 24 ≤ c' := hc_d_24.trans hc'
    have hc'_c0 : c₀ ≤ c' := ((le_max_left c₀ 24).trans (le_max_left _ _)).trans hc'
    have hC0_bd : ‖Bessel.besselErrC c' (x_c : ℂ)‖ ≤ C₀ / c' :=
      hbd0 c' hc'_c0 (x_c : ℂ) ⟨x_c, mem_singleton x_c, by simp [hδ_pos]⟩
    have hC1_bd : ‖deriv (Bessel.besselErrC c') (x_c : ℂ)‖ ≤ C₁ / c' := by
      simpa using hbd1 c' hc'_c0 x_c (mem_singleton x_c)
    -- Differentiate t = c' * x^2 / 3 in x at x_c, and relate to besselVDeriv1 (c'/12) t_c!
    let s_c : ℝ := Real.log t_c
    have ht_c_pos : 0 < t_c := by dsimp [t_c]; positivity
    have h_exp_sc : Real.exp s_c = t_c := Real.exp_log ht_c_pos
    have hd_s : HasDerivAt (fun x : ℝ => Real.log (c' * x ^ 2 / 3)) (2 / x_c) x_c := by
      have h1 : HasDerivAt (fun x : ℝ => c' * x ^ 2 / 3) (2 * c' * x_c / 3) x_c := by
        simpa using ((((hasDerivAt_pow 2 x_c).const_mul c').div_const 3)).congr_deriv (by ring)
      refine (h1.log ht_c_pos.ne').congr_deriv ?_
      field_simp [hc'_pos.ne', hx_c_pos.ne']
    have hd_V_s : HasDerivAt (fun u : ℝ => Bessel.besselV (c' / 12) (Real.exp u))
        (besselVDeriv1 (c' / 12) t_c) (Real.log (c' * x_c ^ 2 / 3)) := by
      simpa [h_exp_sc] using hasDerivAt_besselV_exp (a := c' / 12) (by linarith) s_c
    have hd_V_x : HasDerivAt (fun x : ℝ => Bessel.besselV (c' / 12) (c' * x ^ 2 / 3))
        (besselVDeriv1 (c' / 12) t_c * (2 / x_c)) x_c := by
      have heq : (fun x : ℝ => Bessel.besselV (c' / 12) (c' * x ^ 2 / 3)) =ᶠ[𝓝 x_c]
          fun x : ℝ => Bessel.besselV (c' / 12) (Real.exp (Real.log (c' * x ^ 2 / 3))) := by
        filter_upwards [eventually_gt_nhds hx_c_pos] with x hx
        rw [Real.exp_log (by positivity)]
      have hcomp := hd_V_s.comp x_c hd_s
      exact hcomp.congr_of_eventuallyEq heq
    -- Now differentiate the complex formula `besselVC (c'/12) (c'*b^2/3) = asC(c'*L(b)) * ((1-e^{-4πb})^2 + E_{c'}(b))`!
    have hVC_eq : ∀ᶠ b in 𝓝 (x_c : ℂ),
        Bessel.besselVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) =
          Bessel.besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) *
            ((1 - Complex.exp (-(4 * (Real.pi : ℂ) * b))) ^ 2 + Bessel.besselErrC c' b) := by
      filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
        (show 0 < (x_c : ℂ).re by simpa using hx_c_pos)] with b hb_re
      have has_ne : Bessel.besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) ≠ 0 := by
        unfold Bessel.besselAsC
        have harg_re : 0 < (2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3))).re := by
          have heq : 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) =
              ((4 * Real.pi ^ 2 * c' / 3 : ℝ) : ℂ) * b := by push_cast; ring
          rw [heq, Complex.re_ofReal_mul]
          exact mul_pos (by positivity) hb_re
        have harg_ne : 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) ≠ 0 := by
          intro h0; rw [h0, Complex.zero_re] at harg_re; exact lt_irrefl 0 harg_re
        exact div_ne_zero (Complex.exp_ne_zero _) (Complex.cpow_ne_zero_iff.mpr (Or.inl harg_ne))
      unfold Bessel.besselErrC
      rw [add_sub_cancel, mul_div_cancel₀ _ has_ne]
    -- Compute HasDerivAt of RHS at (x_c : ℂ):
    let L₀ : ℂ := (c' : ℂ) * (2 * (Real.pi : ℂ) * (x_c : ℂ) / 3)
    have hL₀_pos : 0 < 2 * Real.pi * (c' * (2 * Real.pi * x_c / 3)) := by positivity
    have hd_arg : HasDerivAt (fun b : ℂ => (c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3))
        ((c' : ℂ) * (2 * (Real.pi : ℂ) / 3)) (x_c : ℂ) := by
      simpa using ((hasDerivAt_id (x_c : ℂ)).const_mul (2 * (Real.pi : ℂ)) |>.div_const 3).const_mul (c' : ℂ)
    have hd_2pi_arg : HasDerivAt (fun b : ℂ => 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)))
        (2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) / 3))) (x_c : ℂ) :=
      hd_arg.const_mul (2 * (Real.pi : ℂ))
    have h2piL₀_eq : 2 * (Real.pi : ℂ) * L₀ =
        ((2 * Real.pi * (c' * (2 * Real.pi * x_c / 3)) : ℝ) : ℂ) := by
      dsimp [L₀]; push_cast; ring
    have h_slit : 2 * (Real.pi : ℂ) * L₀ ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by
        rw [h2piL₀_eq, Complex.ofReal_re]
        exact hL₀_pos))
    have hd_sqrt : HasDerivAt
        (fun b : ℂ => (2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3))) ^ (1 / 2 : ℂ))
        ((1 / 2 : ℂ) * (2 * (Real.pi : ℂ) * L₀) ^ (1 / 2 - 1 : ℂ) *
          (2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) / 3)))) (x_c : ℂ) :=
      hd_2pi_arg.cpow_const h_slit
    have hd_exp : HasDerivAt (fun b : ℂ => Complex.exp ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)))
        (Complex.exp L₀ * ((c' : ℂ) * (2 * (Real.pi : ℂ) / 3))) (x_c : ℂ) :=
      hd_arg.cexp
    have hsqrt_ne : (2 * (Real.pi : ℂ) * L₀) ^ (1 / 2 : ℂ) ≠ 0 := by
      refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
      rw [h2piL₀_eq]
      exact Complex.ofReal_ne_zero.mpr hL₀_pos.ne'
    have hd_as : HasDerivAt (fun b : ℂ => Bessel.besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)))
        (Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))))
        (x_c : ℂ) := by
      refine (hd_exp.div hd_sqrt hsqrt_ne).congr_deriv ?_
      unfold Bessel.besselAsC
      have h2piL_ne : 2 * (Real.pi : ℂ) * L₀ ≠ 0 := by
        rw [h2piL₀_eq]; exact Complex.ofReal_ne_zero.mpr hL₀_pos.ne'
      have hcpow_diff : (2 * (Real.pi : ℂ) * L₀) ^ (1 / 2 - 1 : ℂ) =
          (2 * (Real.pi : ℂ) * L₀) ^ (1 / 2 : ℂ) / (2 * (Real.pi : ℂ) * L₀) := by
        rw [sub_eq_add_neg, Complex.cpow_add _ _ h2piL_ne, Complex.cpow_neg_one, ← div_eq_mul_inv]
      rw [hcpow_diff]
      have hx_c_ne : (x_c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_c_pos.ne'
      have hc'_c : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'_pos.ne'
      have hpi_c : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      dsimp [L₀]
      field_simp [hsqrt_ne, hx_c_ne, hc'_c, hpi_c]
    -- Derivative of bracket (1 - exp(-4πb))^2 + E(b) at x_c:
    have hd_E : HasDerivAt (Bessel.besselErrC c') (deriv (Bessel.besselErrC c') (x_c : ℂ)) (x_c : ℂ) := by
      have hopen : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const Complex.continuous_re
      have hdiff := (besselErrC_differentiableOn hc'_pos) (x_c : ℂ)
        (by change 0 < (x_c : ℂ).re; simpa using hx_c_pos)
      exact (hdiff.differentiableAt (hopen.mem_nhds (by change 0 < (x_c : ℂ).re; simpa using hx_c_pos))).hasDerivAt
    have hd_br : HasDerivAt (fun b : ℂ => (1 - Complex.exp (-(4 * (Real.pi : ℂ) * b))) ^ 2)
        (2 * (1 - Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) *
          (4 * (Real.pi : ℂ) * Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ))))) (x_c : ℂ) := by
      have h1 : HasDerivAt (fun b : ℂ => -(4 * (Real.pi : ℂ) * b)) (-(4 * (Real.pi : ℂ))) (x_c : ℂ) :=
        ((hasDerivAt_id (x_c : ℂ)).const_mul (4 * (Real.pi : ℂ))).congr_deriv (by ring) |>.neg
      have h2 : HasDerivAt (fun b : ℂ => 1 - Complex.exp (-(4 * (Real.pi : ℂ) * b)))
          (4 * (Real.pi : ℂ) * Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) (x_c : ℂ) :=
        (h1.cexp.const_sub (1 : ℂ)).congr_deriv (by ring)
      exact (h2.pow 2).congr_deriv (by push_cast; ring)
    let B₀ : ℂ := (1 - Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) ^ 2 + Bessel.besselErrC c' (x_c : ℂ)
    let B₀' : ℂ := 2 * (1 - Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) *
        (4 * (Real.pi : ℂ) * Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) +
      deriv (Bessel.besselErrC c') (x_c : ℂ)
    have hd_rhs : HasDerivAt
        (fun b : ℂ => Bessel.besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * b / 3)) *
          ((1 - Complex.exp (-(4 * (Real.pi : ℂ) * b))) ^ 2 + Bessel.besselErrC c' b))
        (Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
          Bessel.besselAsC L₀ * B₀') (x_c : ℂ) :=
      hd_as.mul (hd_br.add hd_E)
    have hd_VC : HasDerivAt (fun b : ℂ => Bessel.besselVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3))
        (Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
          Bessel.besselAsC L₀ * B₀') (x_c : ℂ) :=
      hd_rhs.congr_of_eventuallyEq hVC_eq
    -- Restrict to real x via comp_ofReal and take .re
    have hd_V_real_C : HasDerivAt
        (fun x : ℝ => (Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) : ℂ))
        (Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
          Bessel.besselAsC L₀ * B₀') x_c := by
      have hcomp := hd_VC.comp_ofReal
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [eventually_gt_nhds hx_c_pos] with x hx
      rw [show (c' : ℂ) * (x : ℂ) ^ 2 / 3 = ((c' * x ^ 2 / 3 : ℝ) : ℂ) by push_cast; ring]
      exact besselV_eq_re_besselVC hc'_24 (by positivity : 0 ≤ c' * x ^ 2 / 3)
    have hd_V_real : HasDerivAt
        (fun x : ℝ => Bessel.besselV (c' / 12) (c' * x ^ 2 / 3))
        ((Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
          Bessel.besselAsC L₀ * B₀').re) x_c :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x_c hd_V_real_C
    have hderiv_eq : besselVDeriv1 (c' / 12) t_c * (2 / x_c) =
        (Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
          Bessel.besselAsC L₀ * B₀').re :=
      hd_V_x.unique hd_V_real
    have hV_tc_eq : (Bessel.besselV (c' / 12) t_c : ℂ) = Bessel.besselAsC L₀ * B₀ := by
      rw [besselV_eq_re_besselVC hc'_24 ht_c_pos.le,
        show (t_c : ℂ) = (c' : ℂ) * (x_c : ℂ) ^ 2 / 3 by dsimp [t_c]; push_cast; ring]
      dsimp [B₀, L₀]
      have has_ne : Bessel.besselAsC ((c' : ℂ) * (2 * (Real.pi : ℂ) * (x_c : ℂ) / 3)) ≠ 0 := by
        unfold Bessel.besselAsC
        have harg_ne : 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * (x_c : ℂ) / 3)) ≠ 0 := by
          rw [show 2 * (Real.pi : ℂ) * ((c' : ℂ) * (2 * (Real.pi : ℂ) * (x_c : ℂ) / 3)) =
              ((2 * Real.pi * (c' * (2 * Real.pi * x_c / 3)) : ℝ) : ℂ) by push_cast; ring]
          exact Complex.ofReal_ne_zero.mpr hL₀_pos.ne'
        exact div_ne_zero (Complex.exp_ne_zero _) (Complex.cpow_ne_zero_iff.mpr (Or.inl harg_ne))
      unfold Bessel.besselErrC
      rw [add_sub_cancel, mul_div_cancel₀ _ has_ne]
    have hV_tc_pos : 0 < Bessel.besselV (c' / 12) t_c := by
      have := Bessel.besselV_ge (a := c' / 12) (by linarith) ht_c_pos.le
      have hpos : 0 < 8 * Real.pi ^ 4 * t_c ^ 2 := by positivity
      linarith
    have has_ne : Bessel.besselAsC L₀ ≠ 0 := by
      unfold Bessel.besselAsC
      exact div_ne_zero (Complex.exp_ne_zero _) hsqrt_ne
    have hB0_ne : B₀ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hV_tc_eq
      exact hV_tc_pos.ne' (Complex.ofReal_eq_zero.mp hV_tc_eq)
    have hquot_re : (besselVDeriv1 (c' / 12) t_c * (2 / x_c)) / Bessel.besselV (c' / 12) t_c =
        (((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) + B₀' / B₀).re := by
      have h1 : ((Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
            Bessel.besselAsC L₀ * B₀') / (Bessel.besselV (c' / 12) t_c : ℂ)) =
          ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) + B₀' / B₀ := by
        rw [hV_tc_eq]
        field_simp [has_ne, hB0_ne]
      have h2 := congrArg Complex.re h1
      have h4 : (Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
          Bessel.besselAsC L₀ * B₀').re / Bessel.besselV (c' / 12) t_c =
          ((Bessel.besselAsC L₀ * ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) * B₀ +
            Bessel.besselAsC L₀ * B₀') / (Bessel.besselV (c' / 12) t_c : ℂ)).re := by
        rw [Complex.div_ofReal_re]
      rw [← h4, ← hderiv_eq] at h2
      exact h2
    have hc_E : 2 * |C₀| / br0 + 1 ≤ c' := (le_max_right _ _).trans hc'
    have hE_le : ‖Bessel.besselErrC c' (x_c : ℂ)‖ ≤ br0 / 2 := by
      calc ‖Bessel.besselErrC c' (x_c : ℂ)‖ ≤ C₀ / c' := hC0_bd
        _ ≤ |C₀| / c' := div_le_div_of_nonneg_right (le_abs_self C₀) hc'_pos.le
        _ ≤ br0 / 2 := by
            rw [div_le_iff₀ hc'_pos]
            have h1 : 2 * |C₀| / br0 ≤ c' := by linarith
            have h2 := (div_le_iff₀ hbr0_pos).mp h1
            linarith
    have hB0_lb : br0 / 2 ≤ ‖B₀‖ := by
      have hbr0_eq : (1 - Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) ^ 2 = (br0 : ℂ) := by
        dsimp [br0, q]
        rw [show -(4 * (Real.pi : ℂ) * (x_c : ℂ)) = ((-4 * Real.pi * x_c : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp]
        push_cast; ring
      dsimp [B₀]
      rw [hbr0_eq]
      have htri := norm_sub_norm_le (br0 : ℂ) (-Bessel.besselErrC c' (x_c : ℂ))
      rw [sub_neg_eq_add, Complex.norm_real, Real.norm_of_nonneg hbr0_pos.le, norm_neg] at htri
      linarith
    have hB0'_ub : ‖B₀'‖ ≤ 8 * Real.pi * (1 - q) * q + |C₁| / 24 := by
      have h1 : (2 * (1 - Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) *
          (4 * (Real.pi : ℂ) * Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ))))) =
          ((8 * Real.pi * (1 - q) * q : ℝ) : ℂ) := by
        dsimp [q]
        rw [show -(4 * (Real.pi : ℂ) * (x_c : ℂ)) = ((-4 * Real.pi * x_c : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp]
        push_cast; ring
      have h2 : ‖deriv (Bessel.besselErrC c') (x_c : ℂ)‖ ≤ |C₁| / 24 := by
        calc ‖deriv (Bessel.besselErrC c') (x_c : ℂ)‖ ≤ C₁ / c' := hC1_bd
          _ ≤ |C₁| / c' := div_le_div_of_nonneg_right (le_abs_self C₁) hc'_pos.le
          _ ≤ |C₁| / 24 := div_le_div_of_nonneg_left (abs_nonneg C₁) (by norm_num) hc'_24
      dsimp [B₀']
      calc ‖2 * (1 - Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) *
              (4 * (Real.pi : ℂ) * Complex.exp (-(4 * (Real.pi : ℂ) * (x_c : ℂ)))) +
              deriv (Bessel.besselErrC c') (x_c : ℂ)‖
          ≤ ‖((8 * Real.pi * (1 - q) * q : ℝ) : ℂ)‖ +
              ‖deriv (Bessel.besselErrC c') (x_c : ℂ)‖ := by rw [h1]; exact norm_add_le _ _
        _ ≤ 8 * Real.pi * (1 - q) * q + |C₁| / 24 := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by have : 0 ≤ 1 - q := sub_nonneg.mpr hq_lt1.le; positivity)]
            linarith
    have hre_bound : (((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) + B₀' / B₀).re ≤
        2 * Real.pi * c' / 3 + (1 / (2 * x_c) + (2 / br0) * (8 * Real.pi * (1 - q) * q + |C₁| / 24)) := by
      have hre_lin : ((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))).re =
          2 * Real.pi * c' / 3 - 1 / (2 * x_c) := by
        rw [show (2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ)) =
            ((2 * Real.pi * c' / 3 - 1 / (2 * x_c) : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
      have hre_B : (B₀' / B₀).re ≤ (2 / br0) * (8 * Real.pi * (1 - q) * q + |C₁| / 24) := by
        calc (B₀' / B₀).re ≤ ‖B₀' / B₀‖ := Complex.re_le_norm _
          _ = ‖B₀'‖ / ‖B₀‖ := norm_div _ _
          _ ≤ (8 * Real.pi * (1 - q) * q + |C₁| / 24) / (br0 / 2) :=
              div_le_div₀ (by have : 0 ≤ 1 - q := sub_nonneg.mpr hq_lt1.le; positivity)
                hB0'_ub (by positivity) hB0_lb
          _ = (2 / br0) * (8 * Real.pi * (1 - q) * q + |C₁| / 24) := by ring
      rw [Complex.add_re, hre_lin]
      linarith [show 0 ≤ 1 / (2 * x_c) by positivity]
    have hmul_xc : besselVDeriv1 (c' / 12) t_c / Bessel.besselV (c' / 12) t_c =
        (x_c / 2) * ((besselVDeriv1 (c' / 12) t_c * (2 / x_c)) / Bessel.besselV (c' / 12) t_c) := by
      field_simp [hx_c_pos.ne']
    rw [hmul_xc, hquot_re]
    calc (x_c / 2) * (((2 * (Real.pi : ℂ) * (c' : ℂ) / 3) - 1 / (2 * (x_c : ℂ))) + B₀' / B₀).re
        ≤ (x_c / 2) * (2 * Real.pi * c' / 3 +
            (1 / (2 * x_c) + (2 / br0) * (8 * Real.pi * (1 - q) * q + |C₁| / 24))) :=
          mul_le_mul_of_nonneg_left hre_bound (by positivity)
      _ = Real.pi * c' * x_c / 3 + C_d := by dsimp [C_d]; ring

/-! ### Section 4: Lemma S2 (`vlo:S2`) -/

/-- **Lemma S2 (crude Legendre bound)** (`lower_o1_two_edge.tex`, `vlo:S2`):
for every fixed `μ₀ > π ξ_* / 6`, there exist `C > 0` and `c₀ ≥ 10000` such that for all
`c' ≥ c₀`, all `ω` with `Re ω ≥ μ₀`, and every `g ∈ TestClass virasoroProblem (c'/12)`,
the Mellin integral `Mg(1/2 + c' ω)` converges absolutely and
`‖m_g(1/2 + c' ω)‖ ≤ C exp(c' B(ω)) M[g]`. -/
theorem lemma_S2 {μ₀ : ℝ} (hμ₀ : Real.pi * xiStar / 6 < μ₀) :
    ∃ C c₀ : ℝ, 0 < C ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {ω : ℂ}, μ₀ ≤ ω.re → ∀ {g : ℝ → ℝ},
        Crossing.TestClass Crossing.virasoroProblem (c' / 12) g →
        IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ ((1 / 2 + (c' : ℂ) * ω) - 1)) (Ioi 0) ∧
          ‖mellinMG g (1 / 2 + (c' : ℂ) * ω)‖ ≤
            C * Real.exp (c' * crudeExponentB ω) *
              Crossing.virasoroProblem.cardyNorm (c' / 12) g := by
  obtain ⟨C_d, c_d, hCd_nn, hcd_24, hderiv_xc⟩ := deriv_log_besselV_at_xc
  let x_c : ℝ := xiStar / 2
  have hx_c_pos : 0 < x_c := by dsimp [x_c]; linarith [xiStar_pos]
  have hμ₀_pos : 0 < μ₀ := by nlinarith [Real.pi_pos, xiStar_pos]
  have hgap : 0 < μ₀ - Real.pi * x_c / 3 := by
    dsimp [x_c]; linarith
  -- Choose c₀ ≥ max 10000 (max c_d (max (48 / μ₀) ((C_d + 1/2) / (μ₀ - π x_c / 3))))
  let c₀ : ℝ := max 10000 (max c_d (max (48 / μ₀) ((C_d + 1 / 2) / (μ₀ - Real.pi * x_c / 3))))
  let C : ℝ := 12 * Real.pi / √x_c
  refine ⟨C, c₀, by positivity, le_max_left _ _, fun {c'} hc' {ω} hω_re {g} hg => ?_⟩
  have hc'_10000 : 10000 ≤ c' := (le_max_left _ _).trans hc'
  have hc'_cd : c_d ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_48 : 48 / μ₀ ≤ c' :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hc')
  have hc'_gap : (C_d + 1 / 2) / (μ₀ - Real.pi * x_c / 3) ≤ c' :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hc')
  have hc'_pos : 0 < c' := by linarith
  have hc'_24 : 24 ≤ c' := by linarith
  have hω_pos : 0 < ω.re := lt_of_lt_of_le hμ₀_pos hω_re
  have hω_norm_ge : μ₀ ≤ ‖ω‖ := hω_re.trans (Complex.re_le_norm ω)
  have hcω_48 : 48 ≤ c' * ‖ω‖ := by
    calc (48 : ℝ) ≤ c' * μ₀ := (div_le_iff₀ hμ₀_pos).mp hc'_48
      _ ≤ c' * ‖ω‖ := mul_le_mul_of_nonneg_left hω_norm_ge hc'_pos.le
  have hS_inv : ‖(stirlingS c' ω)⁻¹‖ ≤ 2 :=
    norm_stirlingS_inv_le hc'_pos hω_pos.le hcω_48
  set z : ℂ := 1 / 2 + (c' : ℂ) * ω
  have hz_re_ge : Real.pi * c' * x_c / 3 + C_d ≤ z.re - 1 := by
    have hz_re : z.re = 1 / 2 + c' * ω.re := by
      simp only [z, Complex.add_re, Complex.re_ofReal_mul]; norm_num
    have hgap_mul : C_d + 1 / 2 ≤ c' * (μ₀ - Real.pi * x_c / 3) :=
      (div_le_iff₀ hgap).mp hc'_gap
    have hμ_mul : c' * (μ₀ - Real.pi * x_c / 3) ≤ c' * (ω.re - Real.pi * x_c / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hc'_pos.le
    linarith
  -- Pointwise kernel bound for all t > 0:
  have hkernel_bd : ∀ t ∈ Ioi (0 : ℝ),
      ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖ ≤
        (C * Real.exp (c' * crudeExponentB ω)) * Bessel.besselV (c' / 12) t := by
    intro t ht
    rw [mem_Ioi] at ht
    have hV_pos : 0 < Bessel.besselV (c' / 12) t := by
      have := Bessel.besselV_ge (a := c' / 12) (by linarith) ht.le
      have hpos : 0 < 8 * Real.pi ^ 4 * t ^ 2 := by positivity
      linarith
    set x : ℝ := √(3 * t / c')
    have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
    have hxc_bd : ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
        Bessel.besselV (c' / 12) t ≤ C * Real.exp (c' * crudeExponentB ω) →
        ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖ ≤
          (C * Real.exp (c' * crudeExponentB ω)) * Bessel.besselV (c' / 12) t :=
      fun h => (div_le_iff₀ hV_pos).mp h
    refine hxc_bd ?_
    have hcomp_ge : ∀ y : ℝ, x_c ≤ y →
        let ty : ℝ := c' * y ^ 2 / 3
        ‖(2 * (Real.pi : ℂ)) ^ z * (ty : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
            Bessel.besselV (c' / 12) ty ≤
          C * Real.exp (c' * crudeExponentB ω) := by
      intro y hy ty
      have hty_pos : 0 < ty := by
        have hy_pos : 0 < y := lt_of_lt_of_le hx_c_pos hy
        dsimp [ty]; positivity
      have hy_sqrt : √(3 * ty / c') = y := by
        dsimp [ty]
        rw [show 3 * (c' * y ^ 2 / 3) / c' = y ^ 2 by field_simp [hc'_pos.ne'],
          Real.sqrt_sq (hx_c_pos.le.trans hy)]
      have hkeq := norm_kernel_eq hc'_24 hω_pos hty_pos
      dsimp only at hkeq
      rw [hy_sqrt] at hkeq
      rw [hkeq]
      have hcomp := (Bessel.besselV_comparison hc'_10000 hy).2
      have hA2_le : 1 / √ty * Real.exp (c' * Bessel.besselL y) / Bessel.besselV (c' / 12) ty ≤
          6 * Real.pi / √x_c := by
        calc 1 / √ty * Real.exp (c' * Bessel.besselL y) / Bessel.besselV (c' / 12) ty
            ≤ 6 * Real.pi / √y := hcomp
          _ ≤ 6 * Real.pi / √x_c := by gcongr
      have hD_nn : 0 ≤ crudeDivergenceD (3 * ω.re / Real.pi) y :=
        crudeDivergenceD_nonneg (by positivity) (hx_c_pos.trans_le hy)
      have hexp_D_le1 : Real.exp (-c' * crudeDivergenceD (3 * ω.re / Real.pi) y) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [hc'_pos]
      have hB_exp_nn : 0 ≤ Real.exp (c' * crudeExponentB ω) := (Real.exp_pos _).le
      have hA2_nn : 0 ≤ 1 / √ty * Real.exp (c' * Bessel.besselL y) / Bessel.besselV (c' / 12) ty := by
        have hVty_pos : 0 < Bessel.besselV (c' / 12) ty := by
          have := Bessel.besselV_ge (a := c' / 12) (by linarith) hty_pos.le
          have hpos : 0 < 8 * Real.pi ^ 4 * ty ^ 2 := by positivity
          linarith
        positivity
      calc ‖(stirlingS c' ω)⁻¹‖ *
            (1 / √ty * Real.exp (c' * Bessel.besselL y) / Bessel.besselV (c' / 12) ty) *
            Real.exp (c' * crudeExponentB ω) *
            Real.exp (-c' * crudeDivergenceD (3 * ω.re / Real.pi) y)
          ≤ 2 * (6 * Real.pi / √x_c) * Real.exp (c' * crudeExponentB ω) * 1 := by
            gcongr
        _ = C * Real.exp (c' * crudeExponentB ω) := by dsimp [C]; ring
    rcases le_or_gt x_c x with hge | hlt
    · have ht_eq : t = c' * x ^ 2 / 3 := by
        dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
      have h := hcomp_ge x hge
      dsimp only at h
      rwa [← ht_eq] at h
    · -- x < x_c: use concavity of f(s) = (z.re - 1) s - log V(e^s)
      let t_c : ℝ := c' * x_c ^ 2 / 3
      have ht_c_pos : 0 < t_c := by dsimp [t_c]; positivity
      have ht_le_tc : t ≤ t_c := by
        have ht_eq : t = c' * x ^ 2 / 3 := by
          dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
        rw [ht_eq]
        dsimp [t_c]
        gcongr
      have hs_le_sc : Real.log t ≤ Real.log t_c := Real.log_le_log ht ht_le_tc
      have hderiv_le : besselVDeriv1 (c' / 12) (Real.exp (Real.log t_c)) /
          Bessel.besselV (c' / 12) (Real.exp (Real.log t_c)) ≤ z.re - 1 := by
        rw [Real.exp_log ht_c_pos]
        exact (hderiv_xc hc'_cd).trans hz_re_ge
      have hconc := besselV_exp_concavity_le hc'_24 hs_le_sc hderiv_le
      rw [Real.exp_log ht, Real.exp_log ht_c_pos] at hconc
      have hVc_pos : 0 < Bessel.besselV (c' / 12) t_c := by
        have := Bessel.besselV_ge (a := c' / 12) (by linarith) ht_c_pos.le
        have hpos : 0 < 8 * Real.pi ^ 4 * t_c ^ 2 := by positivity
        linarith
      have hrpow_le : t ^ (z.re - 1) / Bessel.besselV (c' / 12) t ≤
          t_c ^ (z.re - 1) / Bessel.besselV (c' / 12) t_c := by
        have hexp_le : Real.exp ((z.re - 1) * Real.log t - Real.log (Bessel.besselV (c' / 12) t)) ≤
            Real.exp ((z.re - 1) * Real.log t_c - Real.log (Bessel.besselV (c' / 12) t_c)) :=
          Real.exp_le_exp.mpr hconc
        have hLHS : Real.exp ((z.re - 1) * Real.log t - Real.log (Bessel.besselV (c' / 12) t)) =
            t ^ (z.re - 1) / Bessel.besselV (c' / 12) t := by
          rw [Real.exp_sub, Real.exp_log hV_pos, mul_comm, Real.rpow_def_of_pos ht]
        have hRHS : Real.exp ((z.re - 1) * Real.log t_c - Real.log (Bessel.besselV (c' / 12) t_c)) =
            t_c ^ (z.re - 1) / Bessel.besselV (c' / 12) t_c := by
          rw [Real.exp_sub, Real.exp_log hVc_pos, mul_comm, Real.rpow_def_of_pos ht_c_pos]
        rwa [hLHS, hRHS] at hexp_le
      have hnorm_t : ∀ u : ℝ, 0 < u →
          ‖(2 * (Real.pi : ℂ)) ^ z * (u : ℂ) ^ (z - 1) / Complex.Gamma z‖ =
            (‖(2 * (Real.pi : ℂ)) ^ z‖ / ‖Complex.Gamma z‖) * u ^ (z.re - 1) := by
        intro u hu
        rw [norm_div, norm_mul]
        have hcpow : ‖(u : ℂ) ^ (z - 1)‖ = u ^ (z.re - 1) := by
          rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), Complex.norm_exp,
            (Complex.ofReal_log hu.le).symm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.sub_re, Complex.one_re, zero_mul, sub_zero, Real.rpow_def_of_pos hu, mul_comm]
        rw [hcpow]; ring
      rw [hnorm_t t ht]
      calc (‖(2 * (Real.pi : ℂ)) ^ z‖ / ‖Complex.Gamma z‖) * t ^ (z.re - 1) /
              Bessel.besselV (c' / 12) t
          = (‖(2 * (Real.pi : ℂ)) ^ z‖ / ‖Complex.Gamma z‖) *
              (t ^ (z.re - 1) / Bessel.besselV (c' / 12) t) := by ring
        _ ≤ (‖(2 * (Real.pi : ℂ)) ^ z‖ / ‖Complex.Gamma z‖) *
              (t_c ^ (z.re - 1) / Bessel.besselV (c' / 12) t_c) := by gcongr
        _ = ‖(2 * (Real.pi : ℂ)) ^ z * (t_c : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
              Bessel.besselV (c' / 12) t_c := by rw [hnorm_t t_c ht_c_pos]; ring
        _ ≤ C * Real.exp (c' * crudeExponentB ω) := hcomp_ge x_c le_rfl
  -- Now conclude integrability of `g(t) t^{z-1}` and the integral bound!
  have hz_re_pos : 0 < z.re := by
    simp only [z, Complex.add_re, Complex.re_ofReal_mul]
    norm_num
    linarith [mul_pos hc'_pos hω_pos]
  have hgam_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero (fun n hn => by
      have : z.re = -(n : ℝ) := by rw [hn]; simp
      linarith [Nat.cast_nonneg (α := ℝ) n])
  have h2piz_ne : (2 * (Real.pi : ℂ)) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hV_cardy : ∀ t : ℝ, 0 ≤ t →
      Bessel.besselV (c' / 12) t = Crossing.virasoroProblem.cardyV (c' / 12) t :=
    fun t ht => (Integration.virasoro_cardyV_eq_besselV ha ht).symm
  have hmeas_mg : AEStronglyMeasurable
      (fun t : ℝ => (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z))
      (volume.restrict (Ioi 0)) := by
    have hcont_g : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)
    have hcont_pow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) (Ioi 0) := by
      intro t ht
      have hne : (t : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using mem_Ioi.mp ht))
      exact ((Complex.continuous_ofReal.continuousAt.cpow continuousAt_const hne)).continuousWithinAt
    have hcont : ContinuousOn
        (fun t : ℝ => (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z))
        (Ioi 0) :=
      hcont_g.mul ((continuousOn_const.mul hcont_pow).div_const _)
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hint_mg : IntegrableOn
      (fun t : ℝ => (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z))
      (Ioi 0) := by
    refine Integrable.mono' (hg.int_cardy.const_mul (C * Real.exp (c' * crudeExponentB ω)))
      hmeas_mg ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hV_cardy t (mem_Ioi.mp ht).le]
    have hkb := hkernel_bd t ht
    calc |g t| * ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖
        ≤ |g t| * ((C * Real.exp (c' * crudeExponentB ω)) * Bessel.besselV (c' / 12) t) := by
          gcongr
      _ = C * Real.exp (c' * crudeExponentB ω) * (|g t| * Bessel.besselV (c' / 12) t) := by ring
  have hint_g : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) := by
    let fac : ℂ := Complex.Gamma z / (2 * (Real.pi : ℂ)) ^ z
    have heq : (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) =
        fun t : ℝ => fac *
          ((g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z)) := by
      ext t; dsimp [fac]; field_simp [hgam_ne, h2piz_ne]
    rw [heq]
    exact hint_mg.const_mul fac
  refine ⟨hint_g, ?_⟩
  have hMG_eq : mellinMG g z =
      ∫ t in Ioi (0 : ℝ),
        (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z) := by
    unfold mellinMG mellinTransformG
    rw [div_eq_mul_inv, mul_comm _ (Complex.Gamma z)⁻¹, ← mul_assoc,
      mul_comm (Complex.Gamma z)⁻¹ _, ← integral_const_mul]
    congr 1; ext t; ring
  rw [hMG_eq]
  calc ‖∫ t in Ioi (0 : ℝ),
          (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z)‖
      ≤ ∫ t in Ioi (0 : ℝ),
          ‖(g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ),
          (C * Real.exp (c' * crudeExponentB ω)) * (|g t| * Crossing.virasoroProblem.cardyV (c' / 12) t) := by
        refine setIntegral_mono_on hint_mg.norm
          (hg.int_cardy.const_mul (C * Real.exp (c' * crudeExponentB ω))) measurableSet_Ioi
          fun t ht => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hV_cardy t (mem_Ioi.mp ht).le]
        calc |g t| * ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖
            ≤ |g t| * ((C * Real.exp (c' * crudeExponentB ω)) * Bessel.besselV (c' / 12) t) := by
              gcongr; exact hkernel_bd t ht
          _ = C * Real.exp (c' * crudeExponentB ω) * (|g t| * Bessel.besselV (c' / 12) t) := by ring
    _ = C * Real.exp (c' * crudeExponentB ω) * Crossing.virasoroProblem.cardyNorm (c' / 12) g := by
        rw [integral_const_mul]; rfl

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.crudeDivergenceD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crudeDivergenceD_nonneg

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.lemma_S2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S2

end FormalResearch.ModularBootstrap.ComplexBessel