module

public import FormalResearch.ModularBootstrap.Bessel.LaplaceAux
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Laplace asymptotics of `I₀`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), proof of (c):
"the classical integral representation and Laplace's method give
`I₀(z) = e^z/√(2πz) · (1 + O(1/z))`" (real `z → ∞`).

With `as(z) = e^z/√(2πz)` (`besselAs`) we prove, by Laplace's method applied to
`I₀(z) = e^z π⁻¹ ∫₀^π e^{-z(1-cos θ)} dθ` (cosine bounds `1 - θ²/2 ≤ cos θ ≤ 1 - θ²/2 + θ⁴/16`
on `[0,1]` and Gaussian integrals), with explicit constants:

* `besselI0_lower`: `(1 - 1/z) as(z) ≤ I₀(z)` for `z > 0`;
* `besselI0_upper`: `I₀(z) ≤ (1 + 10/z) as(z)` for `z ≥ 4`;
* `besselI0_asymptotic`: `|I₀(z)/as(z) - 1| ≤ 10/z` for `z ≥ 4`.

The constants are not sharp (the sharp one is `1/8`); only the `O(1/z)` rate matters.
-/

@[expose] public section

open Real MeasureTheory Set intervalIntegral

namespace FormalResearch.ModularBootstrap.Bessel

/-- `as(z) = e^z/√(2πz)`, the leading Hankel asymptotic of `I₀`. -/
noncomputable def besselAs (z : ℝ) : ℝ := exp z / √(2 * π * z)

lemma besselAs_pos {z : ℝ} (hz : 0 < z) : 0 < besselAs z := by
  unfold besselAs; positivity

/-- `I₀(z) = (e^z/π) ∫₀^π e^{z (cos θ - 1)} dθ`. -/
lemma besselI0_eq_G (z : ℝ) :
    besselI0 z = exp z / π * ∫ θ in (0 : ℝ)..π, exp (z * (cos θ - 1)) := by
  rw [besselI0_integral, div_mul_eq_mul_div, ← intervalIntegral.integral_const_mul]
  congr 2; ext θ
  rw [← exp_add]; congr 1; ring

/-- `e^z g₀ / π = as(z)` for `g₀ = √(π/(2z))`. -/
lemma exp_mul_g0_div_pi {z : ℝ} (hz : 0 < z) : exp z / π * √(π / (2 * z)) = besselAs z := by
  unfold besselAs
  have h1 : √(π / (2 * z)) = π / √(2 * π * z) := by
    rw [Real.sqrt_div' _ (by positivity), eq_div_iff (by positivity)]
    have : √(2 * π * z) = √π * √(2 * z) := by
      rw [← Real.sqrt_mul pi_pos.le]; congr 1; ring
    rw [this]
    have hp : √π * √π = π := Real.mul_self_sqrt pi_pos.le
    have hs : 0 < √(2 * z) := by positivity
    field_simp
    nlinarith [hp]
  rw [h1]
  field_simp

/-- Lower bound: the Gaussian tail. -/
theorem besselI0_lower {z : ℝ} (hz : 0 < z) : (1 - 1 / z) * besselAs z ≤ besselI0 z := by
  set g0 := √(π / (2 * z)) with hg0
  have hg0pos : 0 < g0 := by positivity
  have hb : 0 < z / 2 := by positivity
  -- Gaussian part
  have hG : ∫ θ in (0 : ℝ)..π, exp (-(z / 2) * θ ^ 2) ≤ ∫ θ in (0 : ℝ)..π, exp (z * (cos θ - 1)) := by
    refine intervalIntegral.integral_mono_on pi_pos.le ?_ ?_ fun θ _ => ?_
    · exact (by fun_prop : Continuous fun θ : ℝ => exp (-(z / 2) * θ ^ 2)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ : ℝ => exp (z * (cos θ - 1))).intervalIntegrable _ _
    · refine exp_le_exp.mpr ?_
      have := Real.one_sub_sq_div_two_le_cos (x := θ)
      nlinarith
  have hsub := gauss_sub_interval_le hb
  have hsq : √(π / (z / 2)) / 2 = g0 := by
    rw [hg0]
    have : π / (z / 2) = 2 ^ 2 * (π / (2 * z)) := by field_simp
    rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  rw [hsq] at hsub
  -- tail bound
  have htail : exp (-(z / 2 * π ^ 2)) / (z / 2 * π) ≤ g0 / z := by
    have e1 : exp (-(z / 2 * π ^ 2)) / (z / 2 * π) = (2 * exp (-(z / 2 * π ^ 2)) / π) / z := by
      field_simp
    rw [e1]
    gcongr 1
    rw [hg0]
    apply Real.le_sqrt_of_sq_le
    have hp3 : (3 : ℝ) < π := Real.pi_gt_three
    have hpi2 : (9 : ℝ) < π ^ 2 := by nlinarith
    have hexp : exp (-(z / 2 * π ^ 2)) ≤ exp (-z) := by
      refine exp_le_exp.mpr ?_
      nlinarith [mul_pos hz (sub_pos.2 hpi2)]
    have hze : z * exp (-z) ≤ 1 := by
      have := Real.add_one_le_exp z
      have h2 : exp z * exp (-z) = 1 := by rw [← exp_add]; simp
      nlinarith [exp_pos (-z)]
    have hsq1 : exp (-(z / 2 * π ^ 2)) ^ 2 = exp (-(z * π ^ 2)) := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    have hsq2 : (2 * exp (-(z / 2 * π ^ 2)) / π) ^ 2 = 4 * exp (-(z * π ^ 2)) / π ^ 2 := by
      rw [div_pow, mul_pow, hsq1]; norm_num
    rw [hsq2]
    have hexp2 : exp (-(z * π ^ 2)) ≤ exp (-z) := by
      refine exp_le_exp.mpr ?_
      nlinarith [mul_pos hz (sub_pos.2 hpi2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 * exp (-(z * π ^ 2)) * (2 * z) ≤ 8 := by
      have := mul_le_mul_of_nonneg_left hexp2 (by positivity : (0 : ℝ) ≤ 8 * z)
      nlinarith
    nlinarith [pow_pos pi_pos 3, Real.pi_gt_three]
  -- combine
  have hI : exp z / π * (g0 - g0 / z) ≤ besselI0 z := by
    rw [besselI0_eq_G]
    gcongr 1
    linarith
  calc (1 - 1 / z) * besselAs z = exp z / π * (g0 - g0 / z) := by
        rw [← exp_mul_g0_div_pi hz]; ring
    _ ≤ besselI0 z := hI

/-- Pointwise bound on `[0,1]` behind the upper Laplace estimate. -/
lemma exp_cos_sub_one_le {z θ : ℝ} (hz : 0 ≤ z) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    exp (z * (cos θ - 1)) ≤
      exp (-(z / 2) * θ ^ 2) + z / 16 * (θ ^ 4 * exp (-(7 * z / 16) * θ ^ 2)) := by
  have hb := Real.cos_bound (x := θ) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at hb
  have hcos : cos θ ≤ 1 - θ ^ 2 / 2 + θ ^ 4 / 16 := by
    have := (abs_le.mp hb).2
    nlinarith [pow_nonneg h0 4]
  set x : ℝ := z * θ ^ 4 / 16 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ z * θ ^ 2 / 16 := by
    have : θ ^ 4 ≤ θ ^ 2 := by
      have : θ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg θ]
    rw [hx]; gcongr
  have h2 : z * (cos θ - 1) ≤ -(z / 2) * θ ^ 2 + x := by
    rw [hx]; nlinarith [mul_le_mul_of_nonneg_left hcos hz]
  have h3 : exp x ≤ 1 + x * exp x := by
    have := Real.add_one_le_exp (-x)
    have h4 : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos x, exp_pos (-x)]
  calc exp (z * (cos θ - 1)) ≤ exp (-(z / 2) * θ ^ 2 + x) := exp_le_exp.mpr h2
    _ = exp (-(z / 2) * θ ^ 2) * exp x := exp_add _ _
    _ ≤ exp (-(z / 2) * θ ^ 2) * (1 + x * exp x) := by gcongr
    _ ≤ exp (-(z / 2) * θ ^ 2) * (1 + x * exp (z * θ ^ 2 / 16)) := by
        gcongr
    _ = exp (-(z / 2) * θ ^ 2) + z / 16 * (θ ^ 4 * exp (-(7 * z / 16) * θ ^ 2)) := by
        have : exp (-(z / 2) * θ ^ 2) * exp (z * θ ^ 2 / 16) = exp (-(7 * z / 16) * θ ^ 2) := by
          rw [← exp_add]; congr 1; ring
        rw [hx]
        calc _ = exp (-(z / 2) * θ ^ 2) + z * θ ^ 4 / 16 *
              (exp (-(z / 2) * θ ^ 2) * exp (z * θ ^ 2 / 16)) := by ring
          _ = _ := by rw [this]; ring

/-- `(1 + c) √(π/b)` comparison: `√(π/b₁) ≤ (11/5) √(π/(2z))` for `b₁ = 7z/16`. -/
lemma sqrt_pi_div_b1_le {z : ℝ} (hz : 0 < z) :
    √(π / (7 * z / 16)) ≤ 11 / 5 * √(π / (2 * z)) := by
  have : 11 / 5 * √(π / (2 * z)) = √((11 / 5) ^ 2 * (π / (2 * z))) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [this]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ (by positivity)]
  have hp := pi_pos
  rw [show (11 / 5 : ℝ) ^ 2 * (π / (2 * z)) * (7 * z / 16) = (121 * 7 / (25 * 32)) * π by
    field_simp; ring]
  nlinarith

/-- Upper bound for the integral over `[0,1]`. -/
lemma G_upper_main {z : ℝ} (hz : 0 < z) :
    ∫ θ in (0 : ℝ)..1, exp (z * (cos θ - 1)) ≤ √(π / (2 * z)) * (1 + 66 / 245 / z) := by
  set g0 := √(π / (2 * z)) with hg0
  have hb0 : 0 < z / 2 := by positivity
  have hb1 : 0 < 7 * z / 16 := by positivity
  have hmono : ∫ θ in (0 : ℝ)..1, exp (z * (cos θ - 1)) ≤
      ∫ θ in (0 : ℝ)..1, (exp (-(z / 2) * θ ^ 2) +
        z / 16 * (θ ^ 4 * exp (-(7 * z / 16) * θ ^ 2))) := by
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun θ hθ =>
      exp_cos_sub_one_le hz.le hθ.1 hθ.2
    · exact (by fun_prop : Continuous fun θ : ℝ => exp (z * (cos θ - 1))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ : ℝ => exp (-(z / 2) * θ ^ 2) +
        z / 16 * (θ ^ 4 * exp (-(7 * z / 16) * θ ^ 2))).intervalIntegrable _ _
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous fun θ : ℝ => exp (-(z / 2) * θ ^ 2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => z / 16 * (θ ^ 4 * exp (-(7 * z / 16) * θ ^ 2))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  have h1 := gauss_interval_le hb0 zero_le_one
  have h2 := moment4_interval_le hb1
  have h3 := gauss_interval_le hb1 zero_le_one
  have hsq : √(π / (z / 2)) / 2 = g0 := by
    rw [hg0]
    have : π / (z / 2) = 2 ^ 2 * (π / (2 * z)) := by field_simp
    rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  rw [hsq] at h1
  have h4 := sqrt_pi_div_b1_le hz
  rw [← hg0] at h4
  have hg0pos : 0 < g0 := by positivity
  -- the error term
  have herr : z / 16 * ∫ θ in (0 : ℝ)..1, θ ^ 4 * exp (-(7 * z / 16) * θ ^ 2) ≤ 66 / 245 / z * g0 := by
    calc z / 16 * ∫ θ in (0 : ℝ)..1, θ ^ 4 * exp (-(7 * z / 16) * θ ^ 2)
        ≤ z / 16 * (3 / (4 * (7 * z / 16) ^ 2) * (∫ θ in (0 : ℝ)..1, exp (-(7 * z / 16) * θ ^ 2))) := by
          gcongr
      _ ≤ z / 16 * (3 / (4 * (7 * z / 16) ^ 2) * (√(π / (7 * z / 16)) / 2)) := by gcongr
      _ ≤ z / 16 * (3 / (4 * (7 * z / 16) ^ 2) * (11 / 5 * g0 / 2)) := by gcongr
      _ = 66 / 245 / z * g0 := by field_simp; ring
  linarith

/-- `cos 1 ≤ 53/96`. -/
lemma cos_one_le : cos 1 ≤ 53 / 96 := by
  have := Real.cos_bound (x := 1) (by simp)
  have h := (abs_le.mp this).2
  norm_num at h
  linarith

/-- Upper bound for the integral over `[1,π]`: `≤ (π-1) e^{-4z/9}`. -/
lemma G_upper_tail {z : ℝ} (hz : 0 < z) :
    ∫ θ in (1 : ℝ)..π, exp (z * (cos θ - 1)) ≤ (π - 1) * exp (-(4 * z / 9)) := by
  have hπ : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  calc ∫ θ in (1 : ℝ)..π, exp (z * (cos θ - 1)) ≤ ∫ θ in (1 : ℝ)..π, exp (-(4 * z / 9)) := by
        refine intervalIntegral.integral_mono_on hπ ?_ ?_ fun θ hθ => ?_
        · exact (by fun_prop : Continuous fun θ : ℝ => exp (z * (cos θ - 1))).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · refine exp_le_exp.mpr ?_
          have hc : cos θ ≤ cos 1 :=
            Real.cos_le_cos_of_nonneg_of_le_pi zero_le_one hθ.2 hθ.1
          have := cos_one_le
          nlinarith
    _ = (π - 1) * exp (-(4 * z / 9)) := by simp

/-- The tail contribution is `O(g₀ / z)` for `z ≥ 4`. -/
lemma G_tail_le_g0 {z : ℝ} (hz : 4 ≤ z) :
    (π - 1) * exp (-(4 * z / 9)) ≤ 97 / 10 * √(π / (2 * z)) / z := by
  have hz0 : 0 < z := by linarith
  set w := √z with hw
  have hw0 : 0 < w := by positivity
  have hwz : w ^ 2 = z := Real.sq_sqrt hz0.le
  have hw2 : 2 ≤ w := by
    rw [hw]; apply Real.le_sqrt_of_sq_le; linarith
  have hg : 6 / 5 / w ≤ √(π / (2 * z)) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), hwz]
    have := Real.pi_gt_three
    nlinarith
  have hexp : 8 * z ^ 2 / 81 ≤ exp (4 * z / 9) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 4 * z / 9) (by positivity)
    nlinarith [sq_nonneg z]
  have hpm : π - 1 ≤ 43 / 20 := by linarith [Real.pi_lt_d2]
  have hmain : (π - 1) * w ^ 3 * exp (-(4 * z / 9)) ≤ 11 := by
    have hw3 : w ^ 3 ≤ z ^ 2 / 2 := by
      rw [← hwz]; nlinarith [pow_pos hw0 3]
    have hinv : exp (-(4 * z / 9)) * exp (4 * z / 9) = 1 := by rw [← exp_add]; simp
    have hpos : 0 < exp (-(4 * z / 9)) := exp_pos _
    have : z ^ 2 * exp (-(4 * z / 9)) ≤ 81 / 8 := by
      have := mul_le_mul_of_nonneg_left hexp hpos.le
      nlinarith
    have hp1 : 0 ≤ π - 1 := by linarith [Real.pi_gt_three]
    calc (π - 1) * w ^ 3 * exp (-(4 * z / 9)) ≤ (π - 1) * (z ^ 2 / 2) * exp (-(4 * z / 9)) := by
          gcongr
      _ = (π - 1) / 2 * (z ^ 2 * exp (-(4 * z / 9))) := by ring
      _ ≤ (43 / 20) / 2 * (81 / 8) := by gcongr
      _ ≤ 11 := by norm_num
  have h1 : 97 / 10 * (6 / 5 / w) / z ≤ 97 / 10 * √(π / (2 * z)) / z := by gcongr
  refine le_trans ?_ h1
  have e : 97 / 10 * (6 / 5 / w) / z = (582 / 50) / w ^ 3 := by
    rw [← hwz]; field_simp; norm_num
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith [hmain]

/-- **Upper Laplace bound:** `I₀(z) ≤ (1 + 10/z) as(z)` for `z ≥ 4`. -/
theorem besselI0_upper {z : ℝ} (hz : 4 ≤ z) : besselI0 z ≤ (1 + 10 / z) * besselAs z := by
  have hz0 : 0 < z := by linarith
  set g0 := √(π / (2 * z)) with hg0
  have hsplit : ∫ θ in (0 : ℝ)..π, exp (z * (cos θ - 1)) =
      (∫ θ in (0 : ℝ)..1, exp (z * (cos θ - 1))) + ∫ θ in (1 : ℝ)..π, exp (z * (cos θ - 1)) := by
    have hc : Continuous fun θ : ℝ => exp (z * (cos θ - 1)) := by fun_prop
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have h1 := G_upper_main hz0
  have h2 := G_upper_tail hz0
  have h3 := G_tail_le_g0 hz
  rw [← hg0] at h1 h3
  have hG : ∫ θ in (0 : ℝ)..π, exp (z * (cos θ - 1)) ≤ g0 * (1 + 10 / z) := by
    rw [hsplit]
    have hg : 0 < g0 := by positivity
    have e1 : g0 * (1 + 66 / 245 / z) + 97 / 10 * g0 / z = g0 * (1 + (66 / 245 + 97 / 10) / z) := by
      field_simp; ring
    have e2 : (66 / 245 + 97 / 10 : ℝ) ≤ 10 := by norm_num
    have e3 : (66 / 245 + 97 / 10) / z ≤ 10 / z := by gcongr
    nlinarith
  rw [besselI0_eq_G, ← exp_mul_g0_div_pi hz0]
  calc exp z / π * ∫ θ in (0 : ℝ)..π, exp (z * (cos θ - 1)) ≤ exp z / π * (g0 * (1 + 10 / z)) := by
        gcongr
    _ = (1 + 10 / z) * (exp z / π * g0) := by ring

/-- **`I₀(z) = as(z) (1 + O(1/z))`** (`vlo:Bessel` (c), real `z`), with explicit constant:
`|I₀(z)/as(z) - 1| ≤ 10/z` for `z ≥ 4`. -/
theorem besselI0_asymptotic {z : ℝ} (hz : 4 ≤ z) : |besselI0 z / besselAs z - 1| ≤ 10 / z := by
  have hz0 : 0 < z := by linarith
  have hA := besselAs_pos hz0
  have hl := besselI0_lower hz0
  have hu := besselI0_upper hz
  have h1 : 1 / z ≤ 10 / z := by gcongr; norm_num
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hA]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hA]
    nlinarith

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI0_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0_lower

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI0_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0_upper

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselI0_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI0_asymptotic

end FormalResearch.ModularBootstrap.Bessel
