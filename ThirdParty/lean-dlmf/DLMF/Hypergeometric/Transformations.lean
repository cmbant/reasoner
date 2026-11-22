/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.EulerIntegral
public import ComplexAnalysis.Pow
-- PATCH: removed `public import Carlson.RPolynomial.GeneratingIdentities` (its only use, `Carlson.mul_cpow_of_re_pos`, is replaced by `Complex.mul_cpow_of_re_pos` from `ComplexAnalysis.Pow`)

/-!
# Euler's and Pfaff's transformations (AAR §2.2)

Euler's and Pfaff's linear transformations follow from Euler's integral by a change of
variables. The quadratic transformations of AAR §3.1 are in
`DLMF.Hypergeometric.FurtherTransformations.Quadratic`.

## Main results

* `pfaff_transformation`, `pfaff_transformation_symm`:
  `₂F₁(a,b;c;z) = (1-z)^{-a} ₂F₁(a, c-b; c; z/(z-1))`, DLMF 15.8.1.
* `euler_transformation`: `₂F₁(a,b;c;z) = (1-z)^{c-a-b} ₂F₁(c-a, c-b; c; z)`, DLMF 15.8.1.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §2.2.
-/

public section

open Complex
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- The factors in Pfaff's change of variable stay in the right half-plane. -/
theorem re_one_sub_mul_pos {z : ℂ} (hz : ‖z‖ < 1) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    0 < (1 - z * t).re := by
  have htn : ‖(t : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hn : ‖z * t‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg z, norm_nonneg (t : ℂ)]
  have hre := re_le_norm (z * t)
  simp only [sub_re, one_re]
  linarith

/-- Pfaff's transformation:
`₂F₁(a,b;c;z) = (1-z)^{-a} ₂F₁(a, c-b; c; z/(z-1))`. -/
@[dlmf 15.8.E1]
theorem pfaff_transformation {a b c z : ℂ}
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : ‖z‖ < 1) (hzt : ‖z / (z - 1)‖ < 1) :
    ₂F₁ a b c z = (1 - z) ^ (-a) * ₂F₁ a (c - b) c (z / (z - 1)) := by
  have hcc : c - (c - b) = b := by ring
  rw [ordinaryHypergeometric_eq_integral hb hcb hz,
    ordinaryHypergeometric_eq_integral hcb (by rwa [hcc]) hzt, hcc]
  have hz1 : z - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, norm_one] at hz
    exact (lt_irrefl 1) hz
  have hpos : 0 < (1 - z).re := by
    simpa using re_one_sub_mul_pos hz (t := 1) (by norm_num)
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (1 - z * t) ^ (-a)) (a := (0 : ℝ)) (b := 1) 1
  simp only [sub_self, sub_zero] at hsub
  rw [← hsub]
  have hi : (∫ t : ℝ in (0 : ℝ)..1,
      ((1 - t : ℝ) : ℂ) ^ (b - 1) * (1 - ((1 - t : ℝ) : ℂ)) ^ (c - b - 1) *
        (1 - z * ((1 - t : ℝ) : ℂ)) ^ (-a)) =
      (1 - z) ^ (-a) * ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (c - b - 1) * (1 - (t : ℂ)) ^ (b - 1) *
          (1 - z / (z - 1) * t) ^ (-a) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hfactor : 1 - z * (1 - (t : ℂ)) =
        (1 - z) * (1 - z / (z - 1) * t) := by field_simp; ring
    simp only [ofReal_sub, ofReal_one, sub_sub_cancel]
    -- PATCH: Carlson.mul_cpow_of_re_pos replaced by Complex.mul_cpow_of_re_pos (ComplexAnalysis/Pow.lean; same statement)
    rw [hfactor, Complex.mul_cpow_of_re_pos hpos (re_one_sub_mul_pos hzt ht)]
    ring
  rw [hi]
  ring

/-- The real fractional substitution used in Euler's transformation. -/
theorem euler_integrand_substitution (a b c : ℂ) {z u : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hu : u ∈ Set.Ioo 0 1) :
    ((-(1 - z) / (1 - z * u) ^ 2 : ℝ) : ℂ) *
      (((((1 - u) / (1 - z * u) : ℝ) : ℂ) ^ (b - 1) *
        (1 - (((1 - u) / (1 - z * u) : ℝ) : ℂ)) ^ (c - b - 1)) *
        (1 - (z : ℂ) * (((1 - u) / (1 - z * u) : ℝ) : ℂ)) ^ (-a)) =
      -(1 - (z : ℂ)) ^ (c - a - b) *
        ((u : ℂ) ^ (c - b - 1) * (1 - (u : ℂ)) ^ (b - 1) *
          (1 - (z : ℂ) * u) ^ (-(c - a))) := by
  have hK : 0 < 1 - z := sub_pos.mpr hz1
  have hD : 0 < 1 - z * u := by nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hu.2.le)]
  have hK0 : (1 - (z : ℂ)) ≠ 0 := by exact_mod_cast hK.ne'
  have hD0 : (1 - (z : ℂ) * u) ≠ 0 := by exact_mod_cast hD.ne'
  have hleft : 1 - ((1 - u) / (1 - z * u)) = (1 - z) * u / (1 - z * u) := by
    apply (eq_div_iff hD.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hD.ne']
    ring
  have hright : 1 - z * ((1 - u) / (1 - z * u)) = (1 - z) / (1 - z * u) := by
    field_simp [hD.ne']; ring
  have hleftC : 1 - (((1 - u) / (1 - z * u) : ℝ) : ℂ) =
      (((1 - z) * u / (1 - z * u) : ℝ) : ℂ) := by exact_mod_cast hleft
  have hrightC : 1 - (z : ℂ) * (((1 - u) / (1 - z * u) : ℝ) : ℂ) =
      (((1 - z) / (1 - z * u) : ℝ) : ℂ) := by exact_mod_cast hright
  rw [hleftC, hrightC]
  simp only [ofReal_div]
  rw [div_cpow_ofReal_nonneg (sub_nonneg.mpr hu.2.le) hD.le,
    div_cpow_ofReal_nonneg (mul_nonneg hK.le hu.1.le) hD.le,
    div_cpow_ofReal_nonneg hK.le hD.le]
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hK.le hu.1.le]
  push_cast
  simp only [cpow_sub _ _ hK0, cpow_sub _ _ hD0, cpow_neg, cpow_one]
  field [hK0, hD0, cpow_ne_zero_iff]

/-- Euler's transformation on the real interval, by a monotone fractional substitution. -/
theorem euler_transformation_real {a b c : ℂ} {z : ℝ}
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    ₂F₁ a b c (z : ℂ) =
      (1 - (z : ℂ)) ^ (c - a - b) * ₂F₁ (c - a) (c - b) c (z : ℂ) := by
  have hz : ‖(z : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz0] using hz1
  have hcc : c - (c - b) = b := by ring
  rw [ordinaryHypergeometric_eq_integral hb hcb hz,
    ordinaryHypergeometric_eq_integral hcb (by rwa [hcc]) hz, hcc]
  let T : ℝ → ℝ := fun u => (1 - u) / (1 - z * u)
  let J : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - (z : ℂ) * u) ^ (-a)
  let J' : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (c - b - 1) * (1 - (u : ℂ)) ^ (b - 1) *
      (1 - (z : ℂ) * u) ^ (-(c - a))
  have hD (u : ℝ) (hu : u ∈ Set.Icc 0 1) : 0 < 1 - z * u := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hu.2)]
  have hT : ContinuousOn T (Set.uIcc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    exact (hD u (by simpa using hu)).ne'
  have hd (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
      HasDerivAt T (-(1 - z) / (1 - z * u) ^ 2) u := by
    have h := ((hasDerivAt_const u 1).sub (hasDerivAt_id u)).div
      ((hasDerivAt_const u 1).sub ((hasDerivAt_id u).const_mul z))
      (hD u ⟨hu.1.le, hu.2.le⟩).ne'
    convert! h using 1
    simp only [zero_sub, mul_one, Pi.sub_apply, id_eq]
    ring
  have hn (u : ℝ) (hu : u ∈ Set.Ioo 0 1) : -(1 - z) / (1 - z * u) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (g := J) hT (fun u hu => hd u (by simpa using hu))
    (fun u hu => hn u (by simpa using hu))
  have hT0 : T 0 = 1 := by simp [T]
  have hT1 : T 1 = 0 := by simp [T]
  rw [hT0, hT1, intervalIntegral.integral_symm (f := J)] at hsub
  have hi : (∫ u : ℝ in (0 : ℝ)..1, (-(1 - z) / (1 - z * u) ^ 2) • (J ∘ T) u) =
      -(1 - (z : ℂ)) ^ (c - a - b) * ∫ u : ℝ in (0 : ℝ)..1, J' u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    simpa only [real_smul, Function.comp_apply, J, J', T] using
      euler_integrand_substitution a b c hz0 hz1 hu
  rw [hi] at hsub
  have hJ : (∫ u : ℝ in (0 : ℝ)..1, J u) =
      (1 - (z : ℂ)) ^ (c - a - b) * ∫ u : ℝ in (0 : ℝ)..1, J' u := by
    linear_combination hsub
  change _ * (∫ u : ℝ in (0 : ℝ)..1, J u) = _ * (_ * ∫ u : ℝ in (0 : ℝ)..1, J' u)
  rw [hJ]
  ring

/-- Euler's transformation:
`₂F₁(a,b;c;z) = (1-z)^{c-a-b} ₂F₁(c-a, c-b; c; z)`. -/
@[dlmf 15.8.E1]
theorem euler_transformation {a b c z : ℂ}
    (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : ‖z‖ < 1) :
    ₂F₁ a b c z = (1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) c z := by
  let f : ℂ → ℂ := ₂F₁ a b c
  let g := fun w : ℂ => (1 - w) ^ (c - a - b) * ₂F₁ (c - a) (c - b) c w
  have hf : AnalyticOnNhd ℂ f (Metric.ball 0 1) := by
    intro w hw
    exact (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one (by simpa using hw))
  have hg : AnalyticOnNhd ℂ g (Metric.ball 0 1) := by
    intro w hw
    have hn : ‖w‖ < 1 := by simpa using hw
    apply AnalyticAt.mul
    · apply AnalyticAt.cpow (by fun_prop) analyticAt_const
      apply Or.inl
      simpa using re_one_sub_mul_pos hn (t := 1) (by norm_num)
    · exact (hasFPowerSeriesOnBall_ordinaryHypergeometric (c - a) (c - b) c).analyticAt_of_mem
        (mem_eball_one_of_norm_lt_one hn)
  have hcl : (0 : ℂ) ∈ closure ({w | f w = g w} \ {0}) := by
    have ht : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (𝓝 (0 : ℂ)) := by
      exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    apply mem_closure_of_tendsto ht
    apply Filter.eventually_atTop.mpr
    refine ⟨1, fun n hn => ?_⟩
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : 1 / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    refine ⟨euler_transformation_real hb hcb hpos.le hlt, ?_⟩
    simpa only [Set.mem_singleton_iff, ofReal_eq_zero] using hpos.ne'
  exact hf.eqOn_of_preconnected_of_mem_closure hg (convex_ball (0 : ℂ) 1).isPreconnected
    (by simp) hcl (by simpa using hz)

/-- Pfaff's transformation in the other parameter (swap `a` and `b`). -/
@[dlmf 15.8.E1]
theorem pfaff_transformation_symm {a b c z : ℂ}
    (ha : 0 < a.re) (hca : 0 < (c - a).re) (hz : ‖z‖ < 1) (hzt : ‖z / (z - 1)‖ < 1) :
    ₂F₁ a b c z = (1 - z) ^ (-b) * ₂F₁ (c - a) b c (z / (z - 1)) := by
  have hsymm (u v w t : ℂ) : ₂F₁ u v w t = ₂F₁ v u w t := by
    unfold ordinaryHypergeometric
    rw [ordinaryHypergeometricSeries_symm]
  rw [hsymm a b, pfaff_transformation ha hca hz hzt, hsymm b (c - a)]

-- The same family is the four representations of Kummer's first solution.
attribute [dlmf 15.10.E11] euler_transformation pfaff_transformation pfaff_transformation_symm

end DLMF.Hypergeometric
