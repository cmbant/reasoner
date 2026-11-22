module

public import FormalResearch.ModularBootstrap.Chart.Upsilon
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Half-Strip Large-Height Asymptotics and Polynomial Bounds (§J7)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J7 (lines 623–634, eq. `vlo:large`).

Proves:
* Exact derivatives and algebraic square/second-derivative identities for `chartB`, `chartQ`,
  and `chartOmega` on `{0 ≤ Re ζ ≤ 1/2} \ {1/2}`.
* Large-height asymptotics (`τ ≥ 2`, `0 ≤ x ≤ 1/2`):
  - `b(x + iτ) = B_τ - i x / 2 + O(e^{-πτ})` and `b'(x + iτ) = -i/2 + O(e^{-πτ})`,
    where `B_τ = τ/2 + log 2 / (2π)`.
  - `q(x + iτ) = (1 - x)/2 - i B_τ + O(e^{-πτ})` and `q'(x + iτ) = -1/2 + O(e^{-πτ})`.
  - `ω'(x + iτ) = -(2π/3) B_τ - (π i / 3)(1/2 - x) + O((1 + τ) e^{-πτ})`.
  - `ω''(x + iτ) = π i / 3 + O((1 + τ) e^{-πτ})`, yielding the refined imaginary-part bound
    `|Im ω'(x + iτ) + (π/3)(1/2 - x)| ≤ (1/2 - x) C (1 + τ) e^{-πτ}`.
* Global strip bounds on `stripClosed = {0 ≤ Re ζ ≤ 1}` (used by S4):
  `‖chartLogBQ ζ‖ ≤ C`, `‖chartOmega ζ‖ ≤ C (1 + (Im ζ)^2)`,
  `‖deriv chartOmega ζ‖ ≤ C (1 + |Im ζ|)`, `‖chartUpsilon ζ‖ ≤ C (1 + (Im ζ)^2)`,
  and `chartOmega ζ = 0 ↔ ζ = 1/2` on `stripClosed`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ChartGeometry

open FormalResearch.ModularBootstrap.Chart

/-- Asymptotic real scale `B_τ = τ/2 + (log 2)/(2π)` (`lower_o1_two_edge.tex`, §J7, line 625). -/
noncomputable def chartBTau (τ : ℝ) : ℝ := τ / 2 + Real.log 2 / (2 * Real.pi)

/-! ### Section 1: Exact first and second derivatives on the left half-strip -/

private lemma one_add_cos_pi_mem_slitPlane {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2)
    (hne : ζ ≠ 1 / 2) :
    1 + Complex.cos ((Real.pi : ℂ) * ζ) ∈ Complex.slitPlane := by
  have h := (arsinh_cos_inner_slitPlane h0 h1 hne).1
  rwa [cpow_half_sq, add_comm] at h

private lemma hasDerivAt_chartB {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    HasDerivAt chartB
      (-Complex.sin ((Real.pi : ℂ) * ζ) /
        (2 * (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) *
          (1 + Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ))) ζ := by
  have hcos_slit := cos_pi_mem_slitPlane h0 h1 hne
  have h1cos_slit := one_add_cos_pi_mem_slitPlane h0 h1 hne
  obtain ⟨h1', h2'⟩ := arsinh_cos_inner_slitPlane h0 h1 hne
  have hcos_d : HasDerivAt (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z))
      (-Complex.sin ((Real.pi : ℂ) * ζ) * (Real.pi : ℂ)) ζ := by
    have hlin : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) ζ := by
      simpa using (hasDerivAt_id ζ).const_mul (Real.pi : ℂ)
    exact ((Complex.hasDerivAt_cos _).comp ζ hlin).congr_deriv (by ring)
  have hsqrt_d : HasDerivAt (fun z : ℂ => (Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (Complex.cos ((Real.pi : ℂ) * ζ)) ^ ((1 / 2 : ℂ) - 1) *
        (-Complex.sin ((Real.pi : ℂ) * ζ) * (Real.pi : ℂ))) ζ :=
    hcos_d.cpow_const hcos_slit
  have hcomp := ((hasDerivAt_arsinhC h1' h2').comp ζ hsqrt_d).const_mul (Real.pi : ℂ)⁻¹
  change HasDerivAt chartB _ ζ at hcomp
  refine hcomp.congr_deriv ?_
  set c := Complex.cos ((Real.pi : ℂ) * ζ)
  have hc_ne : c ≠ 0 := Complex.slitPlane_ne_zero hcos_slit
  have h1c_ne : 1 + c ≠ 0 := Complex.slitPlane_ne_zero h1cos_slit
  have hs1 : c ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h0'; have hsq := congrArg (· ^ 2) h0'; rw [cpow_half_sq, zero_pow two_ne_zero] at hsq
    exact hc_ne hsq
  have hs2 : (1 + c) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h0'; have hsq := congrArg (· ^ 2) h0'; rw [cpow_half_sq, zero_pow two_ne_zero] at hsq
    exact h1c_ne hsq
  have hpow1 : c ^ ((1 / 2 : ℂ) - 1) = (c ^ (1 / 2 : ℂ))⁻¹ := by
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num, Complex.cpow_neg]
  have hpow2 : ((((c ^ (1 / 2 : ℂ)) ^ 2 + 1) ^ (-(1 / 2 : ℂ)))) = ((1 + c) ^ (1 / 2 : ℂ))⁻¹ := by
    rw [cpow_half_sq, add_comm c 1, Complex.cpow_neg]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [hpow2, hpow1]
  field_simp [hpi, hs1, hs2]

private lemma hasDerivAt_chartQ {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    HasDerivAt chartQ
      (-Complex.cos ((Real.pi : ℂ) * ζ / 2) /
        ((√2 : ℂ) * (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ))) ζ := by
  have hcos_slit := cos_pi_mem_slitPlane h0 h1 hne
  obtain ⟨h1', h2'⟩ := arccos_sin_inner_slitPlane h0 h1 hne
  have hz_d : HasDerivAt (fun z : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2))
      ((√2 : ℂ) * (Complex.cos ((Real.pi : ℂ) * ζ / 2) * ((Real.pi : ℂ) / 2))) ζ := by
    have hlin : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z / 2) ((Real.pi : ℂ) / 2) ζ := by
      simpa using ((hasDerivAt_id ζ).const_mul (Real.pi : ℂ)).div_const 2
    exact ((Complex.hasDerivAt_sin _).comp ζ hlin).const_mul (√2 : ℂ)
  have hcomp := ((hasDerivAt_arccosC h1' h2').comp ζ hz_d).const_mul (Real.pi : ℂ)⁻¹
  change HasDerivAt chartQ _ ζ at hcomp
  refine hcomp.congr_deriv ?_
  have h1z : 1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2 =
      Complex.cos ((Real.pi : ℂ) * ζ) := by
    have hc := Complex.cos_two_mul ((Real.pi : ℂ) * ζ / 2)
    have hsq := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * ζ / 2)
    rw [show 2 * ((Real.pi : ℂ) * ζ / 2) = (Real.pi : ℂ) * ζ by ring] at hc
    have hsin2 : 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 =
        1 - Complex.cos ((Real.pi : ℂ) * ζ) := by linear_combination 2 * hsq + hc
    have h2 : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
    calc 1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2
        = 1 - (√2 : ℂ) ^ 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 := by ring
      _ = 1 - 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 := by rw [h2]
      _ = Complex.cos ((Real.pi : ℂ) * ζ) := by rw [hsin2]; ring
  rw [h1z, Complex.cpow_neg]
  have hc_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 := Complex.slitPlane_ne_zero hcos_slit
  have hs_ne : (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h0'; have hsq := congrArg (· ^ 2) h0'; rw [cpow_half_sq, zero_pow two_ne_zero] at hsq
    exact hc_ne hsq
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hsq2 : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  have hsq2_ne : (√2 : ℂ) ≠ 0 := by intro h0'; rw [h0', zero_pow two_ne_zero] at hsq2; norm_num at hsq2
  field_simp [hpi, hs_ne, hsq2_ne]
  rw [hsq2]

private lemma deriv_chartB_sq {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    (deriv chartB ζ) ^ 2 = (1 - Complex.cos ((Real.pi : ℂ) * ζ)) / (4 * Complex.cos ((Real.pi : ℂ) * ζ)) := by
  rw [(hasDerivAt_chartB h0 h1 hne).deriv]
  set c := Complex.cos ((Real.pi : ℂ) * ζ)
  have hc_ne : c ≠ 0 := Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane h0 h1 hne)
  have h1c_ne : 1 + c ≠ 0 := Complex.slitPlane_ne_zero (one_add_cos_pi_mem_slitPlane h0 h1 hne)
  have hsc := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * ζ)
  have hsin2 : Complex.sin ((Real.pi : ℂ) * ζ) ^ 2 = (1 - c) * (1 + c) := by
    linear_combination hsc
  rw [div_pow, neg_sq, mul_pow, mul_pow, cpow_half_sq, cpow_half_sq, hsin2]
  field_simp [hc_ne, h1c_ne]
  ring

private lemma deriv_chartQ_sq {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    (deriv chartQ ζ) ^ 2 = (1 + Complex.cos ((Real.pi : ℂ) * ζ)) / (4 * Complex.cos ((Real.pi : ℂ) * ζ)) := by
  rw [(hasDerivAt_chartQ h0 h1 hne).deriv]
  set c := Complex.cos ((Real.pi : ℂ) * ζ)
  have hc_ne : c ≠ 0 := Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane h0 h1 hne)
  have h2cos : 2 * Complex.cos ((Real.pi : ℂ) * ζ / 2) ^ 2 = 1 + c := by
    have hc2 := Complex.cos_two_mul ((Real.pi : ℂ) * ζ / 2)
    rw [show 2 * ((Real.pi : ℂ) * ζ / 2) = (Real.pi : ℂ) * ζ by ring] at hc2
    linear_combination -hc2
  have hsq2 : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  rw [div_pow, neg_sq, mul_pow, hsq2, cpow_half_sq]
  field_simp [hc_ne]
  linear_combination 2 * h2cos

lemma deriv_chartOmega_eq_leftHalf {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    deriv chartOmega ζ = deriv chartOmegaHalf ζ := by
  by_cases hlt : ζ.re < 1 / 2
  · have hev : chartOmega =ᶠ[𝓝 ζ] chartOmegaHalf := by
      filter_upwards [Complex.continuous_re.continuousAt.eventually (gt_mem_nhds hlt)] with w hw
      unfold chartOmega; simp only [hw.le, ↓reduceIte]
    exact hev.deriv_eq
  · have hre : ζ.re = 1 / 2 := le_antisymm h1 (not_lt.mp hlt)
    have hd1 : HasDerivAt chartOmega (deriv chartOmega ζ) ζ :=
      (analyticAt_chartOmega h0 (by linarith)).differentiableAt.hasDerivAt
    have hd2 : HasDerivAt chartOmegaHalf (deriv chartOmegaHalf ζ) ζ :=
      (analyticAt_chartOmegaHalf h0 h1 hne).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun t : ℝ => ζ + Complex.I * (t : ℂ)) Complex.I 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul Complex.I).const_add ζ
    have hc1 := hd1.comp_of_eq (0 : ℝ) hline (by simp)
    have hc2 := hd2.comp_of_eq (0 : ℝ) hline (by simp)
    have heq : (fun t : ℝ => chartOmega (ζ + Complex.I * (t : ℂ))) =
        (fun t : ℝ => chartOmegaHalf (ζ + Complex.I * (t : ℂ))) := by
      ext t
      have hre_t : (ζ + Complex.I * (t : ℂ)).re ≤ 1 / 2 := by simp [hre]
      unfold chartOmega; simp only [hre_t, ↓reduceIte]
    change HasDerivAt (fun t : ℝ => chartOmega (ζ + Complex.I * (t : ℂ))) _ 0 at hc1
    change HasDerivAt (fun t : ℝ => chartOmegaHalf (ζ + Complex.I * (t : ℂ))) _ 0 at hc2
    rw [heq] at hc1
    have hu := hc1.unique hc2
    exact mul_right_cancel₀ Complex.I_ne_zero hu

lemma deriv_chartOmegaHalf_eq {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    deriv chartOmegaHalf ζ =
      (2 * (Real.pi : ℂ) / 3) * (deriv chartB ζ * chartQ ζ + chartB ζ * deriv chartQ ζ) := by
  have hdB := (analyticAt_chartB h0 h1 hne).differentiableAt.hasDerivAt
  have hdQ := (analyticAt_chartQ h0 h1 hne).differentiableAt.hasDerivAt
  have hprod : HasDerivAt chartOmegaHalf
      ((2 * (Real.pi : ℂ) / 3) * (deriv chartB ζ * chartQ ζ + chartB ζ * deriv chartQ ζ)) ζ := by
    have heq : chartOmegaHalf = fun z => (2 * (Real.pi : ℂ) / 3) * (chartB z * chartQ z) := by
      ext z; unfold chartOmegaHalf; ring
    rw [heq]
    exact (hdB.mul hdQ).const_mul (2 * (Real.pi : ℂ) / 3)
  exact hprod.deriv

lemma deriv_chartOmega_eq {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    deriv chartOmega ζ =
      (2 * (Real.pi : ℂ) / 3) * (deriv chartB ζ * chartQ ζ + chartB ζ * deriv chartQ ζ) := by
  rw [deriv_chartOmega_eq_leftHalf h0 h1 hne, deriv_chartOmegaHalf_eq h0 h1 hne]

private lemma deriv2_chartB_eq {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2) :
    2 * deriv chartB ζ * deriv (deriv chartB) ζ =
      ((Real.pi : ℂ) / 4) * Complex.sin ((Real.pi : ℂ) * ζ) /
        Complex.cos ((Real.pi : ℂ) * ζ) ^ 2 := by
  have hne : ζ ≠ 1 / 2 := fun h => by rw [h] at h1; simp at h1
  let r : ℝ := min ζ.re (1 / 2 - ζ.re)
  have hr_pos : 0 < r := lt_min h0 (sub_pos.mpr h1)
  have hev_sq : (fun z => (4 * Complex.cos ((Real.pi : ℂ) * z))⁻¹ - 1 / 4) =ᶠ[𝓝 ζ]
      (fun z => (deriv chartB z) ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre_le : |z.re - ζ.re| ≤ ‖z - ζ‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - ζ)
    have hlt := abs_lt.mp (lt_of_le_of_lt hre_le hz)
    have hz0 : 0 ≤ z.re := by linarith [min_le_left ζ.re (1 / 2 - ζ.re)]
    have hz1 : z.re ≤ 1 / 2 := by linarith [min_le_right ζ.re (1 / 2 - ζ.re)]
    have hzne : z ≠ 1 / 2 := by
      intro h0z
      have hre0 : z.re = 1 / 2 := by simp [h0z]
      linarith [min_le_right ζ.re (1 / 2 - ζ.re)]
    rw [deriv_chartB_sq hz0 hz1 hzne]
    have hc_ne : Complex.cos ((Real.pi : ℂ) * z) ≠ 0 :=
      Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane hz0 hz1 hzne)
    field_simp [hc_ne]
  have hd_b' : HasDerivAt (deriv chartB) (deriv (deriv chartB) ζ) ζ :=
    (analyticAt_chartB h0.le h1.le hne).deriv.differentiableAt.hasDerivAt
  have hd_lhs : HasDerivAt (fun z => (deriv chartB z) ^ 2)
      (2 * deriv chartB ζ * deriv (deriv chartB) ζ) ζ :=
    (hd_b'.fun_pow 2).congr_deriv (by ring)
  have hc_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 :=
    Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane h0.le h1.le hne)
  have hd_cos : HasDerivAt (fun z => 4 * Complex.cos ((Real.pi : ℂ) * z))
      (4 * (-Complex.sin ((Real.pi : ℂ) * ζ) * (Real.pi : ℂ))) ζ := by
    have hlin : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) ζ := by
      simpa using (hasDerivAt_id ζ).const_mul (Real.pi : ℂ)
    exact (((Complex.hasDerivAt_cos _).comp ζ hlin).congr_deriv (by ring)).const_mul 4
  have hd_rhs : HasDerivAt (fun z => (4 * Complex.cos ((Real.pi : ℂ) * z))⁻¹ - 1 / 4)
      ((Real.pi : ℂ) / 4 * Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ) ^ 2) ζ := by
    have hinv := (hd_cos.fun_inv (mul_ne_zero (by norm_num) hc_ne)).sub_const (1 / 4 : ℂ)
    refine hinv.congr_deriv ?_
    field_simp [hc_ne]
  exact hd_lhs.unique (hd_rhs.congr_of_eventuallyEq hev_sq.symm)

private lemma deriv2_chartQ_eq {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2) :
    2 * deriv chartQ ζ * deriv (deriv chartQ) ζ =
      ((Real.pi : ℂ) / 4) * Complex.sin ((Real.pi : ℂ) * ζ) /
        Complex.cos ((Real.pi : ℂ) * ζ) ^ 2 := by
  have hne : ζ ≠ 1 / 2 := fun h => by rw [h] at h1; simp at h1
  let r : ℝ := min ζ.re (1 / 2 - ζ.re)
  have hr_pos : 0 < r := lt_min h0 (sub_pos.mpr h1)
  have hev_sq : (fun z => (4 * Complex.cos ((Real.pi : ℂ) * z))⁻¹ + 1 / 4) =ᶠ[𝓝 ζ]
      (fun z => (deriv chartQ z) ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre_le : |z.re - ζ.re| ≤ ‖z - ζ‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - ζ)
    have hlt := abs_lt.mp (lt_of_le_of_lt hre_le hz)
    have hz0 : 0 ≤ z.re := by linarith [min_le_left ζ.re (1 / 2 - ζ.re)]
    have hz1 : z.re ≤ 1 / 2 := by linarith [min_le_right ζ.re (1 / 2 - ζ.re)]
    have hzne : z ≠ 1 / 2 := by
      intro h0z
      have hre0 : z.re = 1 / 2 := by simp [h0z]
      linarith [min_le_right ζ.re (1 / 2 - ζ.re)]
    rw [deriv_chartQ_sq hz0 hz1 hzne]
    have hc_ne : Complex.cos ((Real.pi : ℂ) * z) ≠ 0 :=
      Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane hz0 hz1 hzne)
    field_simp [hc_ne]
  have hd_q' : HasDerivAt (deriv chartQ) (deriv (deriv chartQ) ζ) ζ :=
    (analyticAt_chartQ h0.le h1.le hne).deriv.differentiableAt.hasDerivAt
  have hd_lhs : HasDerivAt (fun z => (deriv chartQ z) ^ 2)
      (2 * deriv chartQ ζ * deriv (deriv chartQ) ζ) ζ :=
    (hd_q'.fun_pow 2).congr_deriv (by ring)
  have hc_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 :=
    Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane h0.le h1.le hne)
  have hd_cos : HasDerivAt (fun z => 4 * Complex.cos ((Real.pi : ℂ) * z))
      (4 * (-Complex.sin ((Real.pi : ℂ) * ζ) * (Real.pi : ℂ))) ζ := by
    have hlin : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) (Real.pi : ℂ) ζ := by
      simpa using (hasDerivAt_id ζ).const_mul (Real.pi : ℂ)
    exact (((Complex.hasDerivAt_cos _).comp ζ hlin).congr_deriv (by ring)).const_mul 4
  have hd_rhs : HasDerivAt (fun z => (4 * Complex.cos ((Real.pi : ℂ) * z))⁻¹ + 1 / 4)
      (((Real.pi : ℂ) / 4) * Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ) ^ 2) ζ := by
    have hinv := (hd_cos.fun_inv (mul_ne_zero (by norm_num) hc_ne)).add_const (1 / 4 : ℂ)
    refine hinv.congr_deriv ?_
    field_simp [hc_ne]
  exact hd_lhs.unique (hd_rhs.congr_of_eventuallyEq hev_sq.symm)

private lemma deriv2_chartOmega_eq {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2) :
    deriv (deriv chartOmega) ζ =
      (2 * (Real.pi : ℂ) / 3) *
        (deriv (deriv chartB) ζ * chartQ ζ +
          2 * deriv chartB ζ * deriv chartQ ζ +
          chartB ζ * deriv (deriv chartQ) ζ) := by
  have hne : ζ ≠ 1 / 2 := fun h => by rw [h] at h1; simp at h1
  let r : ℝ := min ζ.re (1 / 2 - ζ.re)
  have hr_pos : 0 < r := lt_min h0 (sub_pos.mpr h1)
  have hev : deriv chartOmega =ᶠ[𝓝 ζ]
      fun z => (2 * (Real.pi : ℂ) / 3) * (deriv chartB z * chartQ z + chartB z * deriv chartQ z) := by
    filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre_le : |z.re - ζ.re| ≤ ‖z - ζ‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - ζ)
    have hlt := abs_lt.mp (lt_of_le_of_lt hre_le hz)
    have hz0 : 0 ≤ z.re := by linarith [min_le_left ζ.re (1 / 2 - ζ.re)]
    have hz1 : z.re ≤ 1 / 2 := by linarith [min_le_right ζ.re (1 / 2 - ζ.re)]
    have hzne : z ≠ 1 / 2 := by
      intro h0z
      have hre0 : z.re = 1 / 2 := by simp [h0z]
      linarith [min_le_right ζ.re (1 / 2 - ζ.re)]
    exact deriv_chartOmega_eq hz0 hz1 hzne
  have hdB := (analyticAt_chartB h0.le h1.le hne).differentiableAt.hasDerivAt
  have hdQ := (analyticAt_chartQ h0.le h1.le hne).differentiableAt.hasDerivAt
  have hdB' := (analyticAt_chartB h0.le h1.le hne).deriv.differentiableAt.hasDerivAt
  have hdQ' := (analyticAt_chartQ h0.le h1.le hne).deriv.differentiableAt.hasDerivAt
  have hprod' : HasDerivAt
      (fun z => (2 * (Real.pi : ℂ) / 3) * (deriv chartB z * chartQ z + chartB z * deriv chartQ z))
      ((2 * (Real.pi : ℂ) / 3) *
        (deriv (deriv chartB) ζ * chartQ ζ + 2 * deriv chartB ζ * deriv chartQ ζ +
          chartB ζ * deriv (deriv chartQ) ζ)) ζ :=
    (((hdB'.mul hdQ).add (hdB.mul hdQ')).const_mul (2 * (Real.pi : ℂ) / 3)).congr_deriv (by ring)
  exact (hev.deriv_eq).trans hprod'.deriv

/-! ### Section 2: Large-height asymptotics (`τ ≥ 2`, `0 ≤ x ≤ 1/2`) (`vlo:large`) -/

private lemma exp_pi_gt_twenty : (20 : ℝ) < Real.exp Real.pi := by
  have h1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h3 : (20 : ℝ) < Real.exp 3 := by
    calc (20 : ℝ) < (2.718 : ℝ) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := by gcongr
      _ = Real.exp (((3 : ℕ) : ℝ) * 1) := (Real.exp_nat_mul 1 3).symm
      _ = Real.exp 3 := by norm_num
  exact lt_of_lt_of_le h3 (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))

private lemma exp_neg_pi_tau_le {τ : ℝ} (hτ : 2 ≤ τ) :
    Real.exp (-Real.pi * τ) ≤ 1 / 400 := by
  have h1 : Real.exp (2 * Real.pi) = (Real.exp Real.pi) ^ 2 := by
    simpa using Real.exp_nat_mul Real.pi 2
  have h2 : (400 : ℝ) < Real.exp (2 * Real.pi) := by
    rw [h1]; have hp := exp_pi_gt_twenty; nlinarith only [hp]
  have h3 : (400 : ℝ) ≤ Real.exp (Real.pi * τ) :=
    h2.le.trans (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ]))
  rw [show -Real.pi * τ = -(Real.pi * τ) by ring, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h3

private lemma norm_one_add_cpow_half_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖(1 + u) ^ (1 / 2 : ℂ) - 1‖ ≤ ‖u‖ := by
  have hre : 0 < (1 + u).re := by
    have := Complex.abs_re_le_norm u
    rw [Complex.add_re, Complex.one_re]
    linarith [neg_abs_le u.re]
  have hslit : 1 + u ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hs_re : 0 < ((1 + u) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hslit
  have hden_ge : 1 ≤ ‖(1 + u) ^ (1 / 2 : ℂ) + 1‖ := by
    have hre1 : 1 ≤ ((1 + u) ^ (1 / 2 : ℂ) + 1).re := by
      rw [Complex.add_re, Complex.one_re]; linarith
    exact hre1.trans (Complex.re_le_norm _)
  have hsq : ((1 + u) ^ (1 / 2 : ℂ) - 1) * ((1 + u) ^ (1 / 2 : ℂ) + 1) = u := by
    have h1 := cpow_half_sq (1 + u)
    linear_combination h1
  have hne : (1 + u) ^ (1 / 2 : ℂ) + 1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hden_ge; linarith
  have hdiv : (1 + u) ^ (1 / 2 : ℂ) - 1 = u / ((1 + u) ^ (1 / 2 : ℂ) + 1) :=
    eq_div_of_mul_eq hne hsq
  rw [hdiv, norm_div]
  exact div_le_self (norm_nonneg u) hden_ge

private lemma norm_log_one_add_le_two_mul {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w)‖ ≤ 2 * ‖w‖ := by
  have h := Complex.norm_log_one_add_le (z := w) (by linarith)
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hsq : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ := by
    calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖w‖ * ‖w‖ := by ring
      _ ≤ (1 / 2) * ‖w‖ := by gcongr
      _ ≤ ‖w‖ := by linarith [norm_nonneg w]
  linarith

private lemma cpow_half_eq_of_re_pos' {Z z : ℂ} (hz : z ∈ Complex.slitPlane) (hZ : Z ^ 2 = z)
    (hre : 0 < Z.re) : Z = z ^ (1 / 2 : ℂ) := by
  set s := z ^ (1 / 2 : ℂ)
  have hs_re : 0 < s.re := cpow_half_re_pos hz
  have hs2 : s ^ 2 = z := cpow_half_sq z
  have hprod : (Z - s) * (Z + s) = 0 := by linear_combination hZ - hs2
  have hne : Z + s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [Complex.add_re, Complex.zero_re] at this
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hne)

private lemma norm_exp_pi_tau_sub_x {τ x : ℝ} :
    ‖Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))‖ =
      Real.exp (Real.pi * τ / 2) := by
  rw [Complex.norm_exp]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_self, sub_zero]

private lemma cos_pi_large_height_factor (x τ : ℝ) :
    let ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
    let u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
    Complex.cos ((Real.pi : ℂ) * ζ) =
      (1 / 2 : ℂ) * Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) * (1 + u) := by
  intro ζ u
  rw [Complex.cos]
  have h1 : Complex.exp ((Real.pi : ℂ) * ζ * Complex.I) =
      Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    congr 1; dsimp [ζ]; apply Complex.ext <;> simp
  have h2 : Complex.exp (-((Real.pi : ℂ) * ζ * Complex.I)) =
      Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    congr 1; dsimp [ζ]; apply Complex.ext <;> simp
  have hprod : Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) * u =
      Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    dsimp [u]
    rw [← Complex.exp_add]
    congr 1; apply Complex.ext <;> simp <;> ring
  rw [neg_mul, h1, h2, ← hprod]
  ring

private lemma sin_pi_large_height_factor (x τ : ℝ) :
    let ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
    let u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
    Complex.sin ((Real.pi : ℂ) * ζ) =
      (Complex.I / 2) * Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) * (1 - u) := by
  intro ζ u
  rw [Complex.sin]
  have h1 : Complex.exp (-((Real.pi : ℂ) * ζ * Complex.I)) =
      Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    congr 1; dsimp [ζ]; apply Complex.ext <;> simp
  have h2 : Complex.exp ((Real.pi : ℂ) * ζ * Complex.I) =
      Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    congr 1; dsimp [ζ]; apply Complex.ext <;> simp
  have hprod : Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) * u =
      Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    dsimp [u]
    rw [← Complex.exp_add]
    congr 1; apply Complex.ext <;> simp <;> ring
  rw [neg_mul, h1, h2, ← hprod]
  ring

private lemma w1_re_im_bounds {x τ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    let w₁ : ℂ := ((1 / √2 : ℝ) : ℂ) *
      Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
    (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) ≤ w₁.re ∧
      |w₁.im| ≤ (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) ∧
      ‖w₁‖ = (1 / √2) * Real.exp (Real.pi * τ / 2) := by
  intro w₁
  have hexp_split : Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) =
      (Real.exp (Real.pi * τ / 2) : ℂ) *
        ((Real.cos (Real.pi * x / 2) : ℂ) - Complex.I * (Real.sin (Real.pi * x / 2) : ℂ)) := by
    rw [sub_eq_add_neg, Complex.exp_add, ← Complex.ofReal_exp,
      show -(Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) =
        ((-(Real.pi * x / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hre_eq : w₁.re = (1 / √2) * Real.exp (Real.pi * τ / 2) * Real.cos (Real.pi * x / 2) := by
    dsimp [w₁]; rw [hexp_split]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul]
    ring
  have him_eq : w₁.im = -((1 / √2) * Real.exp (Real.pi * τ / 2) * Real.sin (Real.pi * x / 2)) := by
    dsimp [w₁]; rw [hexp_split]
    simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero,
      zero_sub]
    ring
  have hsq2 : (1 / √2 : ℝ) * (√2 / 2) = 1 / 2 := by
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hre_eq]
    have hcos_ge : √2 / 2 ≤ Real.cos (Real.pi * x / 2) := by
      rw [← Real.cos_pi_div_four]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity [Real.pi_pos])
        (by linarith [Real.pi_pos]) (by nlinarith only [Real.pi_pos, hx1])
    calc (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2)
        = (1 / √2) * Real.exp (Real.pi * τ / 2) * (√2 / 2) := by rw [mul_right_comm, hsq2]
      _ ≤ (1 / √2) * Real.exp (Real.pi * τ / 2) * Real.cos (Real.pi * x / 2) := by gcongr
  · rw [him_eq, abs_neg]
    have hsin_nn : 0 ≤ Real.sin (Real.pi * x / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith only [Real.pi_pos, hx0]) (by nlinarith only [Real.pi_pos, hx1])
    have hexp_nn : 0 ≤ Real.exp (Real.pi * τ / 2) := (Real.exp_pos _).le
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hexp_nn) hsin_nn)]
    have hsin_le : Real.sin (Real.pi * x / 2) ≤ √2 / 2 := by
      rw [← Real.sin_pi_div_four]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith only [Real.pi_pos, hx0])
        (by linarith [Real.pi_pos]) (by nlinarith only [Real.pi_pos, hx1])
    calc (1 / √2) * Real.exp (Real.pi * τ / 2) * Real.sin (Real.pi * x / 2)
        ≤ (1 / √2) * Real.exp (Real.pi * τ / 2) * (√2 / 2) := by gcongr
      _ = (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) := by rw [mul_right_comm, hsq2]
  · dsimp [w₁]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_exp_pi_tau_sub_x]

private lemma sqrt_cos_pi_large_height {x τ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hτ : 2 ≤ τ) :
    let ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
    let u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
    let w₁ : ℂ := ((1 / √2 : ℝ) : ℂ) *
      Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
    let w₂ : ℂ := (1 + u) ^ (1 / 2 : ℂ)
    (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) = w₁ * w₂ := by
  intro ζ u w₁ w₂
  have hne : ζ ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp [ζ] at this; linarith
  have hcos_slit : Complex.cos ((Real.pi : ℂ) * ζ) ∈ Complex.slitPlane :=
    cos_pi_mem_slitPlane (by simp [ζ]; exact hx0) (by simp [ζ]; linarith) hne
  have hu_norm : ‖u‖ ≤ 1 / 400 := by
    dsimp [u]; rw [Complex.norm_exp]
    have hre : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
        -(2 * Real.pi * τ) := by simp
    rw [hre]
    calc Real.exp (-(2 * Real.pi * τ))
        ≤ Real.exp (-Real.pi * τ) := Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])
      _ ≤ 1 / 400 := exp_neg_pi_tau_le hτ
  have hw2_sub : ‖w₂ - 1‖ ≤ 1 / 400 :=
    (norm_one_add_cpow_half_sub_one_le (by linarith)).trans hu_norm
  have hw2_re : 399 / 400 ≤ w₂.re := by
    have := Complex.abs_re_le_norm (w₂ - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [abs_le.mp this]
  have hw2_im : |w₂.im| ≤ 1 / 400 := by
    have := Complex.abs_im_le_norm (w₂ - 1)
    simpa [Complex.sub_im, Complex.one_im] using this.trans hw2_sub
  obtain ⟨hw1_re, hw1_im, _⟩ := w1_re_im_bounds hx0 hx1 (τ := τ)
  have hprod_re : 0 < (w₁ * w₂).re := by
    rw [Complex.mul_re]
    have hexp_pos : 0 < Real.exp (Real.pi * τ / 2) := Real.exp_pos _
    have h1 : (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) * (399 / 400) ≤ w₁.re * w₂.re :=
      mul_le_mul hw1_re hw2_re (by norm_num) (by linarith [hw1_re, hexp_pos])
    have h2 : |w₁.im * w₂.im| ≤ (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) * (1 / 400) := by
      rw [abs_mul]; exact mul_le_mul hw1_im hw2_im (abs_nonneg _) (by positivity)
    linarith [(abs_le.mp h2).2]
  have hprod_sq : (w₁ * w₂) ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := by
    rw [mul_pow, cpow_half_sq]
    have hw1_sq : w₁ ^ 2 =
        (1 / 2 : ℂ) * Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
      dsimp [w₁]
      rw [mul_pow, ← Complex.exp_nat_mul]
      have hsq2 : ((1 / √2 : ℝ) : ℂ) ^ 2 = (1 / 2 : ℂ) := by
        rw [← Complex.ofReal_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)]; norm_num
      rw [hsq2]
      congr 2; apply Complex.ext <;> simp <;> ring
    rw [hw1_sq, ← cos_pi_large_height_factor x τ]
  exact (cpow_half_eq_of_re_pos' hcos_slit hprod_sq hprod_re).symm

private lemma cos_pi_large_height_norm_lb {x τ : ℝ} (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1 / 2) (hτ : 2 ≤ τ) :
    (1 / 4 : ℝ) * Real.exp (Real.pi * τ) ≤ ‖Complex.cos ((Real.pi : ℂ) * ((x : ℂ) + Complex.I * (τ : ℂ)))‖ := by
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  set u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
  have hu_norm : ‖u‖ ≤ 1 / 400 := by
    dsimp [u]; rw [Complex.norm_exp]
    have hre : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
        -(2 * Real.pi * τ) := by simp
    rw [hre]
    exact (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])).trans (exp_neg_pi_tau_le hτ)
  rw [cos_pi_large_height_factor x τ, norm_mul, norm_mul,
    show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num, Complex.norm_exp]
  have hre : (((Real.pi * τ : ℝ) : ℂ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)).re = Real.pi * τ := by
    simp
  rw [hre]
  have h1u : (1 / 2 : ℝ) ≤ ‖1 + u‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (-u)
    rw [sub_neg_eq_add, norm_one, norm_neg] at htri
    linarith
  have hexp_pos : 0 < Real.exp (Real.pi * τ) := Real.exp_pos _
  nlinarith only [h1u, hexp_pos]

private lemma chartBTau_le_one_add {τ : ℝ} (hτ : 0 ≤ τ) : chartBTau τ ≤ 1 + τ := by
  unfold chartBTau
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hdiv : Real.log 2 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity [Real.pi_pos])]; linarith [Real.pi_gt_three]
  linarith

private lemma chartBTau_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ chartBTau τ := by
  unfold chartBTau; positivity [Real.pi_pos, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

/-- Large-height asymptotics for `b(x + iτ)` (`lower_o1_two_edge.tex`, §J7, eq. `vlo:large`). -/
theorem chartB_large_height {x τ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hτ : 2 ≤ τ) :
    ‖chartB ((x : ℂ) + Complex.I * (τ : ℂ)) -
        ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))‖ ≤
      (12 / Real.pi) * Real.exp (-Real.pi * τ) := by
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  set u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
  set w₁ : ℂ := ((1 / √2 : ℝ) : ℂ) *
    Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
  set w₂ : ℂ := (1 + u) ^ (1 / 2 : ℂ)
  set X : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  have hX_eq : X = w₁ * w₂ := sqrt_cos_pi_large_height hx0 hx1 hτ
  have hu_norm : ‖u‖ ≤ Real.exp (-2 * Real.pi * τ) := by
    dsimp [u]; rw [Complex.norm_exp]
    have hre : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
        -2 * Real.pi * τ := by simp
    rw [hre]
  have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le hτ
  have hu_le_400 : ‖u‖ ≤ 1 / 400 :=
    hu_norm.trans ((Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])).trans hexp_le)
  have hw2_sub : ‖w₂ - 1‖ ≤ ‖u‖ := norm_one_add_cpow_half_sub_one_le (by linarith)
  have hw2_norm : ‖w₂‖ ≤ 2 := by
    calc ‖w₂‖ = ‖(1 : ℂ) + (w₂ - 1)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖w₂ - 1‖ := norm_add_le (1 : ℂ) (w₂ - 1)
      _ ≤ 1 + 1 / 400 := by rw [norm_one]; linarith
      _ ≤ 2 := by norm_num
  have hcos_norm := cos_pi_large_height_norm_lb hx0 hx1 hτ
  set v : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ))⁻¹
  have hv_norm : ‖v‖ ≤ 4 * Real.exp (-Real.pi * τ) := by
    dsimp [v]
    rw [norm_inv, inv_eq_one_div, show -Real.pi * τ = -(Real.pi * τ) by ring, Real.exp_neg, ← one_div]
    rw [show (4 : ℝ) * (1 / Real.exp (Real.pi * τ)) = 4 / Real.exp (Real.pi * τ) by ring,
      div_le_div_iff₀ (by linarith [hcos_norm, Real.exp_pos (Real.pi * τ)]) (Real.exp_pos _)]
    linarith
  have hv_le_5 : ‖v‖ ≤ 1 / 100 := hv_norm.trans (by linarith)
  set w₃ : ℂ := (1 + v) ^ (1 / 2 : ℂ)
  have hw3_sub : ‖w₃ - 1‖ ≤ ‖v‖ := norm_one_add_cpow_half_sub_one_le (by linarith)
  have hne : ζ ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp [ζ] at this; linarith
  have hX2_slit : X ^ 2 + 1 ∈ Complex.slitPlane :=
    (arsinh_cos_inner_slitPlane (by simp [ζ]; exact hx0) (by simp [ζ]; linarith) hne).1
  obtain ⟨hw1_re, hw1_im, hw1_norm⟩ := w1_re_im_bounds hx0 hx1 (τ := τ)
  have hXw3_re : 0 < (X * w₃).re := by
    have hre_X : (199 / 800 : ℝ) * Real.exp (Real.pi * τ / 2) ≤ X.re := by
      rw [hX_eq, Complex.mul_re]
      have hw2_re : 399 / 400 ≤ w₂.re := by
        have := Complex.abs_re_le_norm (w₂ - 1)
        rw [Complex.sub_re, Complex.one_re] at this; linarith [abs_le.mp this]
      have hw2_im : |w₂.im| ≤ 1 / 400 := by
        have := Complex.abs_im_le_norm (w₂ - 1)
        simpa [Complex.sub_im, Complex.one_im] using this.trans (hw2_sub.trans hu_le_400)
      have hexp_pos : 0 < Real.exp (Real.pi * τ / 2) := Real.exp_pos _
      have h1 : (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) * (399 / 400) ≤ w₁.re * w₂.re :=
        mul_le_mul hw1_re hw2_re (by norm_num) (by linarith [hw1_re, hexp_pos])
      have h2 : |w₁.im * w₂.im| ≤ (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) * (1 / 400) := by
        rw [abs_mul]; exact mul_le_mul hw1_im hw2_im (abs_nonneg _) (by positivity)
      linarith [(abs_le.mp h2).2]
    have him_X : |X.im| ≤ 2 * Real.exp (Real.pi * τ / 2) := by
      have h12 : (1 / √2 : ℝ) ≤ 1 := by
        rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]; exact Real.one_le_sqrt.mpr (by norm_num)
      have hnorm_X : ‖X‖ ≤ 2 * Real.exp (Real.pi * τ / 2) := by
        rw [hX_eq, norm_mul, hw1_norm]
        have hexp_nn : 0 ≤ Real.exp (Real.pi * τ / 2) := (Real.exp_pos _).le
        calc (1 / √2) * Real.exp (Real.pi * τ / 2) * ‖w₂‖
            ≤ 1 * Real.exp (Real.pi * τ / 2) * 2 := by gcongr
          _ = 2 * Real.exp (Real.pi * τ / 2) := by ring
      exact (Complex.abs_im_le_norm X).trans hnorm_X
    have hw3_re : 99 / 100 ≤ w₃.re := by
      have := Complex.abs_re_le_norm (w₃ - 1)
      rw [Complex.sub_re, Complex.one_re] at this; linarith [abs_le.mp this]
    have hw3_im : |w₃.im| ≤ 1 / 100 := by
      have := Complex.abs_im_le_norm (w₃ - 1)
      simpa [Complex.sub_im, Complex.one_im] using this.trans (hw3_sub.trans hv_le_5)
    rw [Complex.mul_re]
    have hexp_pos : 0 < Real.exp (Real.pi * τ / 2) := Real.exp_pos _
    have h1 : (199 / 800 * Real.exp (Real.pi * τ / 2)) * (99 / 100) ≤ X.re * w₃.re :=
      mul_le_mul hre_X hw3_re (by norm_num) (by linarith [hre_X, hexp_pos])
    have h2 : |X.im * w₃.im| ≤ (2 * Real.exp (Real.pi * τ / 2)) * (1 / 100) := by
      rw [abs_mul]; exact mul_le_mul him_X hw3_im (abs_nonneg _) (by positivity)
    linarith [(abs_le.mp h2).2]
  have hXw3_sq : (X * w₃) ^ 2 = X ^ 2 + 1 := by
    rw [mul_pow, cpow_half_sq, cpow_half_sq]
    have hc_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 :=
      Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane (by simp [ζ]; exact hx0)
        (by simp [ζ]; linarith) hne)
    dsimp [v]
    field_simp [hc_ne]
  have hrt_eq : (X ^ 2 + 1) ^ (1 / 2 : ℂ) = X * w₃ :=
    (cpow_half_eq_of_re_pos' hX2_slit hXw3_sq hXw3_re).symm
  set E₀ : ℂ := Complex.exp (((Real.pi * τ + Real.log 2) / 2 : ℝ) -
    Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
  set η : ℂ := w₂ * (1 + (w₃ - 1) / 2) - 1
  have hE0_eq : 2 * w₁ = E₀ := by
    dsimp [w₁, E₀]
    have hsq2_eq : (2 : ℂ) * ((1 / √2 : ℝ) : ℂ) = (Real.exp (Real.log 2 / 2) : ℂ) := by
      have h1 : 2 * (1 / √2 : ℝ) = √2 := by
        field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
        rw [Real.sq_sqrt (by norm_num)]
      have h2 : √2 = Real.exp (Real.log 2 / 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; ring_nf
      exact_mod_cast h1.trans h2
    rw [← mul_assoc, hsq2_eq, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; apply Complex.ext <;> simp <;> ring
  have hinner_eq : X + (X ^ 2 + 1) ^ (1 / 2 : ℂ) = E₀ * (1 + η) := by
    rw [hrt_eq]
    calc X + X * w₃ = 2 * X * (1 + (w₃ - 1) / 2) := by ring
      _ = (2 * w₁) * (w₂ * (1 + (w₃ - 1) / 2)) := by rw [hX_eq]; ring
      _ = E₀ * (1 + η) := by rw [hE0_eq]; dsimp [η]; ring
  have hη_norm : ‖η‖ ≤ 6 * Real.exp (-Real.pi * τ) := by
    have heq : η = (w₂ - 1) + w₂ * ((w₃ - 1) / 2) := by dsimp [η]; ring
    rw [heq]
    have h1 : ‖w₂ - 1‖ ≤ Real.exp (-Real.pi * τ) :=
      hw2_sub.trans (hu_norm.trans (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])))
    have h2 : ‖w₂ * ((w₃ - 1) / 2)‖ ≤ 4 * Real.exp (-Real.pi * τ) := by
      rw [norm_mul, norm_div, Complex.norm_ofNat]
      have : ‖w₃ - 1‖ ≤ 4 * Real.exp (-Real.pi * τ) := hw3_sub.trans hv_norm
      nlinarith only [hw2_norm, this, norm_nonneg (w₃ - 1)]
    exact (norm_add_le _ _).trans (by linarith [Real.exp_pos (-Real.pi * τ)])
  have hη_le_half : ‖η‖ ≤ 1 / 2 := hη_norm.trans (by linarith)
  have hE0_ne : E₀ ≠ 0 := Complex.exp_ne_zero _
  have h1η_re : 1 / 2 ≤ (1 + η).re := by
    have := Complex.abs_re_le_norm η
    rw [Complex.add_re, Complex.one_re]
    linarith [abs_le.mp this]
  have h1η_ne : 1 + η ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at h1η_re; linarith
  have hlog_E0 : Complex.log E₀ =
      (((Real.pi * τ + Real.log 2) / 2 : ℝ) : ℂ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ) := by
    dsimp [E₀]
    rw [Complex.log_exp]
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
      nlinarith only [Real.pi_pos, hx1]
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
      nlinarith only [Real.pi_pos, hx0]
  have hE0_arg : E₀.arg ∈ Icc (-(Real.pi / 4)) 0 := by
    have harg_eq : E₀.arg = -(Real.pi * x / 2) := by
      rw [← Complex.log_im, hlog_E0]
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
    rw [harg_eq]
    exact ⟨by nlinarith only [Real.pi_pos, hx1], by nlinarith only [Real.pi_pos, hx0]⟩
  have h1η_arg : |(1 + η).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
  have harg_mem : E₀.arg + (1 + η).arg ∈ Ioc (-Real.pi) Real.pi := by
    have h1 := abs_lt.mp h1η_arg
    exact ⟨by linarith [hE0_arg.1, Real.pi_pos], by linarith [hE0_arg.2, Real.pi_pos]⟩
  have hchartB : chartB ζ =
      ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)) +
        (Real.pi : ℂ)⁻¹ * Complex.log (1 + η) := by
    unfold chartB arsinhC chartBTau
    change (Real.pi : ℂ)⁻¹ * Complex.log (X + (X ^ 2 + 1) ^ (1 / 2 : ℂ)) = _
    rw [hinner_eq, Complex.log_mul hE0_ne h1η_ne harg_mem, hlog_E0, mul_add]
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    congr 1
    push_cast
    field_simp [hpi_ne]
  rw [hchartB, add_sub_cancel_left]
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc Real.pi⁻¹ * ‖Complex.log (1 + η)‖
      ≤ Real.pi⁻¹ * (2 * ‖η‖) := mul_le_mul_of_nonneg_left (norm_log_one_add_le_two_mul hη_le_half)
        (inv_nonneg.mpr Real.pi_pos.le)
    _ ≤ Real.pi⁻¹ * (2 * (6 * Real.exp (-Real.pi * τ))) := by gcongr
    _ = (12 / Real.pi) * Real.exp (-Real.pi * τ) := by ring

/-- Large-height asymptotics for `q(x + iτ)` (`lower_o1_two_edge.tex`, §J7, eq. `vlo:large`). -/
theorem chartQ_large_height {x τ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hτ : 2 ≤ τ) :
    ‖chartQ ((x : ℂ) + Complex.I * (τ : ℂ)) -
        (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖ ≤
      (2 / Real.pi) * Real.exp (-Real.pi * τ) := by
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  set u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
  set w₁ : ℂ := ((1 / √2 : ℝ) : ℂ) *
    Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
  set w₂ : ℂ := (1 + u) ^ (1 / 2 : ℂ)
  set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)
  have hcos_sq : (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) = w₁ * w₂ :=
    sqrt_cos_pi_large_height hx0 hx1 hτ
  have h1z : 1 - Z ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := by
    have hc := Complex.cos_two_mul ((Real.pi : ℂ) * ζ / 2)
    have hsq := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * ζ / 2)
    rw [show 2 * ((Real.pi : ℂ) * ζ / 2) = (Real.pi : ℂ) * ζ by ring] at hc
    have hsin2 : 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 =
        1 - Complex.cos ((Real.pi : ℂ) * ζ) := by linear_combination 2 * hsq + hc
    have h2 : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
    dsimp [Z]
    calc 1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2
        = 1 - (√2 : ℂ) ^ 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 := by ring
      _ = 1 - 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 := by rw [h2]
      _ = Complex.cos ((Real.pi : ℂ) * ζ) := by rw [hsin2]; ring
  set v₁ : ℂ := Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ))
  have hZ_eq : Z = Complex.I * w₁ * (1 - v₁) := by
    dsimp [Z, w₁, v₁]
    rw [Complex.sin]
    have h1 : Complex.exp (-((Real.pi : ℂ) * ζ / 2 * Complex.I)) =
        Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by
      congr 1; dsimp [ζ]; apply Complex.ext <;> simp
    have h2 : Complex.exp ((Real.pi : ℂ) * ζ / 2 * Complex.I) =
        Complex.exp (-(Real.pi * τ / 2 : ℝ) + Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by
      congr 1; dsimp [ζ]; apply Complex.ext <;> simp
    have hprod : Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) *
        Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ)) =
        Complex.exp (-(Real.pi * τ / 2 : ℝ) + Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; apply Complex.ext <;> simp <;> ring
    rw [neg_mul, h1, h2]
    have hhalf : (√2 : ℂ) / 2 = ((1 / √2 : ℝ) : ℂ) := by
      have : √2 / 2 = 1 / √2 := by
        field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
        rw [Real.sq_sqrt (by norm_num)]
      exact_mod_cast this
    calc (√2 : ℂ) * ((Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) -
            Complex.exp (-(Real.pi * τ / 2 : ℝ) + Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))) * Complex.I / 2)
        = Complex.I * ((√2 : ℂ) / 2) *
            (Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) -
              Complex.exp (-(Real.pi * τ / 2 : ℝ) + Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))) := by
            ring
      _ = Complex.I * (((1 / √2 : ℝ) : ℂ) *
            Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))) *
            (1 - Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ))) := by
          rw [hhalf, mul_sub, ← hprod]; ring
  set E₁ : ℂ := Complex.exp (((Real.pi * τ + Real.log 2) / 2 : ℝ) +
    Complex.I * ((Real.pi * (1 - x) / 2 : ℝ) : ℂ))
  set η : ℂ := ((w₂ - 1) - v₁) / 2
  have hE1_eq : 2 * Complex.I * w₁ = E₁ := by
    dsimp [w₁, E₁]
    have hsq2_eq : (2 : ℂ) * ((1 / √2 : ℝ) : ℂ) = (Real.exp (Real.log 2 / 2) : ℂ) := by
      have h1 : 2 * (1 / √2 : ℝ) = √2 := by
        field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
        rw [Real.sq_sqrt (by norm_num)]
      have h2 : √2 = Real.exp (Real.log 2 / 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; ring_nf
      exact_mod_cast h1.trans h2
    have hI_exp : Complex.I = Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
      rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    calc 2 * Complex.I * (((1 / √2 : ℝ) : ℂ) *
          Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)))
        = (2 * ((1 / √2 : ℝ) : ℂ)) * Complex.I *
            Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by ring
      _ = (Real.exp (Real.log 2 / 2) : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) *
            Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by
          rw [hsq2_eq, ← hI_exp]
      _ = Complex.exp (((Real.pi * τ + Real.log 2) / 2 : ℝ) +
            Complex.I * ((Real.pi * (1 - x) / 2 : ℝ) : ℂ)) := by
          rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
          congr 1; apply Complex.ext <;> simp <;> ring
  have hinner_eq : Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) = E₁ * (1 + η) := by
    rw [h1z, hcos_sq, hZ_eq]
    calc Complex.I * w₁ * (1 - v₁) + Complex.I * (w₁ * w₂)
        = (2 * Complex.I * w₁) * (1 + ((w₂ - 1) - v₁) / 2) := by ring
      _ = E₁ * (1 + η) := by rw [hE1_eq]
  have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le hτ
  have hu_norm : ‖u‖ ≤ 1 / 400 := by
    dsimp [u]; rw [Complex.norm_exp]
    have hre : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
        -2 * Real.pi * τ := by simp
    rw [hre]
    exact (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])).trans hexp_le
  have hv1_norm : ‖v₁‖ = Real.exp (-Real.pi * τ) := by
    dsimp [v₁]; rw [Complex.norm_exp]; simp
  have hw2_sub : ‖w₂ - 1‖ ≤ Real.exp (-Real.pi * τ) := by
    refine (norm_one_add_cpow_half_sub_one_le (by linarith)).trans ?_
    dsimp [u]; rw [Complex.norm_exp]
    have hre : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
        -2 * Real.pi * τ := by simp
    rw [hre]
    exact Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])
  have hη_norm : ‖η‖ ≤ Real.exp (-Real.pi * τ) := by
    dsimp [η]; rw [norm_div, Complex.norm_ofNat]
    have h1 := norm_sub_le (w₂ - 1) v₁
    rw [hv1_norm] at h1; linarith
  have hη_le_half : ‖η‖ ≤ 1 / 2 := hη_norm.trans (by linarith)
  have hE1_ne : E₁ ≠ 0 := Complex.exp_ne_zero _
  have h1η_re : 1 / 2 ≤ (1 + η).re := by
    have := Complex.abs_re_le_norm η; rw [Complex.add_re, Complex.one_re]; linarith [abs_le.mp this]
  have h1η_ne : 1 + η ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at h1η_re; linarith
  have hlog_E1 : Complex.log E₁ =
      (((Real.pi * τ + Real.log 2) / 2 : ℝ) : ℂ) + Complex.I * ((Real.pi * (1 - x) / 2 : ℝ) : ℂ) := by
    dsimp [E₁]
    rw [Complex.log_exp]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add]
      nlinarith only [Real.pi_pos, hx0, hx1]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add]
      nlinarith only [Real.pi_pos, hx0, hx1]
  have hE1_arg : E₁.arg ∈ Icc (Real.pi / 4) (Real.pi / 2) := by
    have harg_eq : E₁.arg = Real.pi * (1 - x) / 2 := by
      rw [← Complex.log_im, hlog_E1]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add]
    rw [harg_eq]
    exact ⟨by nlinarith only [Real.pi_pos, hx1], by nlinarith only [Real.pi_pos, hx0]⟩
  have h1η_arg : |(1 + η).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
  have harg_mem : E₁.arg + (1 + η).arg ∈ Ioc (-Real.pi) Real.pi := by
    have h1 := abs_lt.mp h1η_arg
    exact ⟨by linarith [hE1_arg.1, Real.pi_pos], by linarith [hE1_arg.2, Real.pi_pos]⟩
  have hchartQ : chartQ ζ =
      (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ)) +
        (-Complex.I * (Real.pi : ℂ)⁻¹) * Complex.log (1 + η) := by
    unfold chartQ arccosC chartBTau
    change (Real.pi : ℂ)⁻¹ * (-Complex.I * Complex.log (Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ))) = _
    rw [hinner_eq, Complex.log_mul hE1_ne h1η_ne harg_mem, hlog_E1]
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    push_cast
    field_simp [hpi_ne]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hchartQ, add_sub_cancel_left]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc Real.pi⁻¹ * ‖Complex.log (1 + η)‖
      ≤ Real.pi⁻¹ * (2 * ‖η‖) := mul_le_mul_of_nonneg_left (norm_log_one_add_le_two_mul hη_le_half)
        (inv_nonneg.mpr Real.pi_pos.le)
    _ ≤ Real.pi⁻¹ * (2 * Real.exp (-Real.pi * τ)) := by gcongr
    _ = (2 / Real.pi) * Real.exp (-Real.pi * τ) := by ring

/-- Large-height asymptotic for `b'(x + iτ)` (`lower_o1_two_edge.tex`, §J7, line 630). -/
theorem deriv_chartB_large_height {x τ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hτ : 2 ≤ τ) :
    ‖deriv chartB ((x : ℂ) + Complex.I * (τ : ℂ)) + Complex.I / 2‖ ≤
      10 * Real.exp (-Real.pi * τ) := by
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  set u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
  set w₁ : ℂ := ((1 / √2 : ℝ) : ℂ) *
    Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
  set w₂ : ℂ := (1 + u) ^ (1 / 2 : ℂ)
  set X : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  set v : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ))⁻¹
  set w₃ : ℂ := (1 + v) ^ (1 / 2 : ℂ)
  have hne : ζ ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp [ζ] at this; linarith
  have hX_eq : X = w₁ * w₂ := sqrt_cos_pi_large_height hx0 hx1 hτ
  have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le hτ
  have hu_norm : ‖u‖ ≤ Real.exp (-2 * Real.pi * τ) := by
    dsimp [u]; rw [Complex.norm_exp]
    have hre : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
        -2 * Real.pi * τ := by simp
    rw [hre]
  have hu_le_400 : ‖u‖ ≤ 1 / 400 :=
    hu_norm.trans ((Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])).trans hexp_le)
  have hcos_norm := cos_pi_large_height_norm_lb hx0 hx1 hτ
  have hv_norm : ‖v‖ ≤ 4 * Real.exp (-Real.pi * τ) := by
    dsimp [v]
    rw [norm_inv, inv_eq_one_div, show -Real.pi * τ = -(Real.pi * τ) by ring, Real.exp_neg, ← one_div]
    rw [show (4 : ℝ) * (1 / Real.exp (Real.pi * τ)) = 4 / Real.exp (Real.pi * τ) by ring,
      div_le_div_iff₀ (by linarith [hcos_norm, Real.exp_pos (Real.pi * τ)]) (Real.exp_pos _)]
    linarith
  have hv_le : ‖v‖ ≤ 1 / 100 := hv_norm.trans (by linarith)
  have hw3_sub : ‖w₃ - 1‖ ≤ ‖v‖ := norm_one_add_cpow_half_sub_one_le (by linarith)
  obtain ⟨hw1_re, hw1_im, hw1_norm⟩ := w1_re_im_bounds hx0 hx1 (τ := τ)
  have hw2_sub : ‖w₂ - 1‖ ≤ 1 / 400 :=
    (norm_one_add_cpow_half_sub_one_le (by linarith)).trans hu_le_400
  have hw2_norm : ‖w₂‖ ≤ 2 := by
    calc ‖w₂‖ = ‖(1 : ℂ) + (w₂ - 1)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖w₂ - 1‖ := norm_add_le (1 : ℂ) (w₂ - 1)
      _ ≤ 1 + 1 / 400 := by rw [norm_one]; linarith
      _ ≤ 2 := by norm_num
  have hw3_eq : (1 + Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) = X * w₃ := by
    have hX2_slit : 1 + Complex.cos ((Real.pi : ℂ) * ζ) ∈ Complex.slitPlane :=
      one_add_cos_pi_mem_slitPlane (by simp [ζ]; exact hx0) (by simp [ζ]; linarith) hne
    have hc_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 :=
      Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane (by simp [ζ]; exact hx0)
        (by simp [ζ]; linarith) hne)
    have hsq : (X * w₃) ^ 2 = 1 + Complex.cos ((Real.pi : ℂ) * ζ) := by
      rw [mul_pow, cpow_half_sq, cpow_half_sq]; dsimp [v]; field_simp [hc_ne]; ring
    have hre_X : (199 / 800 : ℝ) * Real.exp (Real.pi * τ / 2) ≤ X.re := by
      rw [hX_eq, Complex.mul_re]
      have hw2_re : 399 / 400 ≤ w₂.re := by
        have := Complex.abs_re_le_norm (w₂ - 1)
        rw [Complex.sub_re, Complex.one_re] at this; linarith [abs_le.mp this]
      have hw2_im : |w₂.im| ≤ 1 / 400 := by
        have := Complex.abs_im_le_norm (w₂ - 1)
        simpa [Complex.sub_im, Complex.one_im] using this.trans hw2_sub
      have hexp_pos : 0 < Real.exp (Real.pi * τ / 2) := Real.exp_pos _
      have h1 : (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) * (399 / 400) ≤ w₁.re * w₂.re :=
        mul_le_mul hw1_re hw2_re (by norm_num) (by linarith [hw1_re, hexp_pos])
      have h2 : |w₁.im * w₂.im| ≤ (1 / 2 : ℝ) * Real.exp (Real.pi * τ / 2) * (1 / 400) := by
        rw [abs_mul]; exact mul_le_mul hw1_im hw2_im (abs_nonneg _) (by positivity)
      linarith [(abs_le.mp h2).2]
    have him_X : |X.im| ≤ 2 * Real.exp (Real.pi * τ / 2) := by
      have h12 : (1 / √2 : ℝ) ≤ 1 := by
        rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]; exact Real.one_le_sqrt.mpr (by norm_num)
      have hnorm_X : ‖X‖ ≤ 2 * Real.exp (Real.pi * τ / 2) := by
        rw [hX_eq, norm_mul, hw1_norm]
        have hexp_nn : 0 ≤ Real.exp (Real.pi * τ / 2) := (Real.exp_pos _).le
        calc (1 / √2) * Real.exp (Real.pi * τ / 2) * ‖w₂‖
            ≤ 1 * Real.exp (Real.pi * τ / 2) * 2 := by gcongr
          _ = 2 * Real.exp (Real.pi * τ / 2) := by ring
      exact (Complex.abs_im_le_norm X).trans hnorm_X
    have hw3_re : 99 / 100 ≤ w₃.re := by
      have := Complex.abs_re_le_norm (w₃ - 1)
      rw [Complex.sub_re, Complex.one_re] at this; linarith [abs_le.mp this]
    have hw3_im : |w₃.im| ≤ 1 / 100 := by
      have := Complex.abs_im_le_norm (w₃ - 1)
      simpa [Complex.sub_im, Complex.one_im] using this.trans (hw3_sub.trans hv_le)
    have hre_prod : 0 < (X * w₃).re := by
      rw [Complex.mul_re]
      have hexp_pos : 0 < Real.exp (Real.pi * τ / 2) := Real.exp_pos _
      have h1 : (199 / 800 * Real.exp (Real.pi * τ / 2)) * (99 / 100) ≤ X.re * w₃.re :=
        mul_le_mul hre_X hw3_re (by norm_num) (by linarith [hre_X, hexp_pos])
      have h2 : |X.im * w₃.im| ≤ (2 * Real.exp (Real.pi * τ / 2)) * (1 / 100) := by
        rw [abs_mul]; exact mul_le_mul him_X hw3_im (abs_nonneg _) (by positivity)
      linarith [(abs_le.mp h2).2]
    exact (cpow_half_eq_of_re_pos' hX2_slit hsq hre_prod).symm
  have hd_eq : deriv chartB ζ = -(Complex.I / 2) * (1 - u) / ((1 + u) * w₃) := by
    rw [(hasDerivAt_chartB (by simp [ζ]; exact hx0) (by simp [ζ]; linarith) hne).deriv, hw3_eq]
    have hcs := cos_pi_large_height_factor x τ
    have hsn := sin_pi_large_height_factor x τ
    have hX2 : X * X = Complex.cos ((Real.pi : ℂ) * ζ) := by rw [← sq, cpow_half_sq]
    have hden : 2 * X * (X * w₃) = 2 * Complex.cos ((Real.pi : ℂ) * ζ) * w₃ := by
      linear_combination 2 * w₃ * hX2
    have hexp_ne : Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    rw [hden, hsn, hcs]
    dsimp only at *
    set E := Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ))
    calc -(Complex.I / 2 * E * (1 - u)) / (2 * ((1 / 2 : ℂ) * E * (1 + u)) * w₃)
        = (E * (-(Complex.I / 2) * (1 - u))) / (E * ((1 + u) * w₃)) := by ring
      _ = -(Complex.I / 2) * (1 - u) / ((1 + u) * w₃) := mul_div_mul_left _ _ hexp_ne
  have h1u_ge' : 399 / 400 ≤ ‖1 + u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-u)
    rw [sub_neg_eq_add, norm_one, norm_neg] at h; linarith
  have hw3_ge' : 99 / 100 ≤ ‖w₃‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (1 - w₃)
    rw [show (1 : ℂ) - (1 - w₃) = w₃ by ring, norm_one, norm_sub_rev] at h; linarith
  have hden_ge' : 9 / 10 ≤ ‖(1 + u) * w₃‖ := by
    rw [norm_mul]; exact le_trans (by norm_num) (mul_le_mul h1u_ge' hw3_ge' (by norm_num) (by positivity))
  have h1u_ne : 1 + u ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1u_ge'; linarith
  have hw3_ne : w₃ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw3_ge'; linarith
  have hdiff_eq : deriv chartB ζ + Complex.I / 2 =
      (Complex.I / 2) * (2 * u + (1 + u) * (w₃ - 1)) / ((1 + u) * w₃) := by
    rw [hd_eq]; field_simp [h1u_ne, hw3_ne]; ring
  rw [hdiff_eq, norm_div, norm_mul, norm_div, Complex.norm_I, Complex.norm_ofNat]
  have h1u_ub : ‖1 + u‖ ≤ 401 / 400 :=
    (norm_add_le (1 : ℂ) u).trans (by rw [norm_one]; linarith)
  have hnum_le' : ‖2 * u + (1 + u) * (w₃ - 1)‖ ≤ 7 * Real.exp (-Real.pi * τ) := by
    have h1 : ‖u‖ ≤ Real.exp (-Real.pi * τ) :=
      hu_norm.trans (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ]))
    have h3 : ‖w₃ - 1‖ ≤ 4 * Real.exp (-Real.pi * τ) := hw3_sub.trans hv_norm
    calc ‖2 * u + (1 + u) * (w₃ - 1)‖
        ≤ ‖2 * u‖ + ‖(1 + u) * (w₃ - 1)‖ := norm_add_le _ _
      _ = 2 * ‖u‖ + ‖1 + u‖ * ‖w₃ - 1‖ := by rw [norm_mul, Complex.norm_ofNat, norm_mul]
      _ ≤ 2 * Real.exp (-Real.pi * τ) + (401 / 400) * (4 * Real.exp (-Real.pi * τ)) := by gcongr
      _ ≤ 7 * Real.exp (-Real.pi * τ) := by linarith [Real.exp_pos (-Real.pi * τ)]
  calc (1 / 2 : ℝ) * ‖2 * u + (1 + u) * (w₃ - 1)‖ / ‖(1 + u) * w₃‖
      ≤ (1 / 2) * (7 * Real.exp (-Real.pi * τ)) / (9 / 10) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum_le' (by norm_num))
          (by norm_num) hden_ge'
    _ ≤ 10 * Real.exp (-Real.pi * τ) := by linarith [Real.exp_pos (-Real.pi * τ)]

/-- Large-height asymptotic for `q'(x + iτ)` (`lower_o1_two_edge.tex`, §J7, line 630). -/
theorem deriv_chartQ_large_height {x τ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hτ : 2 ≤ τ) :
    ‖deriv chartQ ((x : ℂ) + Complex.I * (τ : ℂ)) + 1 / 2‖ ≤
      2 * Real.exp (-Real.pi * τ) := by
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  set u : ℂ := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
  set w₁ : ℂ := ((1 / √2 : ℝ) : ℂ) *
    Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
  set w₂ : ℂ := (1 + u) ^ (1 / 2 : ℂ)
  set v₁ : ℂ := Complex.exp (-(Real.pi * τ : ℝ) + Complex.I * ((Real.pi * x : ℝ) : ℂ))
  have hne : ζ ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp [ζ] at this; linarith
  have hX_eq := sqrt_cos_pi_large_height hx0 hx1 hτ
  have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le hτ
  have hu_norm : ‖u‖ ≤ Real.exp (-2 * Real.pi * τ) := by
    dsimp [u]; rw [Complex.norm_exp]
    have hre : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
        -2 * Real.pi * τ := by simp
    rw [hre]
  have hu_le_400 : ‖u‖ ≤ 1 / 400 :=
    hu_norm.trans ((Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])).trans hexp_le)
  have hw2_sub : ‖w₂ - 1‖ ≤ Real.exp (-Real.pi * τ) :=
    (norm_one_add_cpow_half_sub_one_le (by linarith)).trans
      (hu_norm.trans (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])))
  have hw2_ge : 399 / 400 ≤ ‖w₂‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (1 - w₂)
    rw [show (1 : ℂ) - (1 - w₂) = w₂ by ring, norm_one, norm_sub_rev] at h
    linarith [hw2_sub.trans hexp_le]
  have hw2_ne : w₂ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw2_ge; linarith
  have hcos_half : Complex.cos ((Real.pi : ℂ) * ζ / 2) =
      (1 / 2 : ℂ) * Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) *
        (1 + v₁) := by
    rw [Complex.cos]
    have h1 : Complex.exp (-((Real.pi : ℂ) * ζ / 2 * Complex.I)) =
        Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by
      congr 1; dsimp [ζ]; apply Complex.ext <;> simp
    have h2 : Complex.exp ((Real.pi : ℂ) * ζ / 2 * Complex.I) =
        Complex.exp (-(Real.pi * τ / 2 : ℝ) + Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by
      congr 1; dsimp [ζ]; apply Complex.ext <;> simp
    have hprod : Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) * v₁ =
        Complex.exp (-(Real.pi * τ / 2 : ℝ) + Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) := by
      dsimp [v₁]; rw [← Complex.exp_add]; congr 1; apply Complex.ext <;> simp <;> ring
    rw [neg_mul, h1, h2, ← hprod]; ring
  have hd_eq : deriv chartQ ζ = -(1 / 2 : ℂ) * (1 + v₁) / w₂ := by
    rw [(hasDerivAt_chartQ (by simp [ζ]; exact hx0) (by simp [ζ]; linarith) hne).deriv,
      hX_eq, hcos_half]
    have hsq2 : (√2 : ℂ) * ((1 / √2 : ℝ) : ℂ) = 1 := by
      exact_mod_cast mul_one_div_cancel (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
    have hexp_ne : Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    set E := Complex.exp ((Real.pi * τ / 2 : ℝ) - Complex.I * ((Real.pi * x / 2 : ℝ) : ℂ))
    dsimp only at *
    have heq_l : -(1 / 2 * E * (1 + v₁)) =
        ((√2 : ℂ) * ((1 / √2 : ℝ) : ℂ)) * (E * (-(1 / 2 : ℂ) * (1 + v₁))) := by
      rw [hsq2]; ring
    have heq_r : (√2 : ℂ) * (((1 / √2 : ℝ) : ℂ) * E * (1 + u) ^ (1 / 2 : ℂ)) =
        ((√2 : ℂ) * ((1 / √2 : ℝ) : ℂ)) * (E * (1 + u) ^ (1 / 2 : ℂ)) := by
      ring
    rw [heq_l, heq_r, hsq2, one_mul, one_mul]
    exact mul_div_mul_left _ _ hexp_ne
  have hdiff_eq : deriv chartQ ζ + 1 / 2 = (1 / 2 : ℂ) * ((w₂ - 1) - v₁) / w₂ := by
    rw [hd_eq]; field_simp [hw2_ne]; ring
  have hv1_norm : ‖v₁‖ = Real.exp (-Real.pi * τ) := by
    dsimp [v₁]; rw [Complex.norm_exp]; simp
  rw [hdiff_eq, norm_div, norm_mul, norm_div, norm_one, Complex.norm_ofNat]
  calc (1 / 2 : ℝ) * ‖(w₂ - 1) - v₁‖ / ‖w₂‖
      ≤ (1 / 2) * (‖w₂ - 1‖ + ‖v₁‖) / (399 / 400) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num))
          (by norm_num) hw2_ge
    _ ≤ (1 / 2) * (Real.exp (-Real.pi * τ) + Real.exp (-Real.pi * τ)) / (399 / 400) := by
        gcongr; rw [hv1_norm]
    _ ≤ 2 * Real.exp (-Real.pi * τ) := by linarith [Real.exp_pos (-Real.pi * τ)]

/-- Large-height asymptotic for `ω'(x + iτ)` (`lower_o1_two_edge.tex`, eq. `vlo:large` / line 679). -/
theorem deriv_chartOmega_large_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 2 ≤ τ →
      ‖deriv chartOmega ((x : ℂ) + Complex.I * (τ : ℂ)) -
          (-((2 * Real.pi / 3 * chartBTau τ : ℝ) : ℂ) -
            ((Real.pi / 3 * (1 / 2 - x) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (1 + τ) * Real.exp (-Real.pi * τ) := by
  refine ⟨100, by norm_num, fun {x τ} hx0 hx1 hτ => ?_⟩
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  have hne : ζ ≠ 1 / 2 := fun h => by
    have := congrArg Complex.im h; simp [ζ] at this; linarith
  have hdom := deriv_chartOmega_eq (by simp [ζ]; exact hx0) (by simp [ζ]; linarith) hne
  set b0 : ℂ := (chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)
  set q0 : ℂ := (((1 - x) / 2 : ℝ) : ℂ) - Complex.I * (chartBTau τ : ℂ)
  set db := deriv chartB ζ - (-Complex.I / 2)
  set dq := deriv chartQ ζ - (-1 / 2 : ℂ)
  set eb := chartB ζ - b0
  set eq := chartQ ζ - q0
  have heb : ‖eb‖ ≤ (12 / Real.pi) * Real.exp (-Real.pi * τ) := chartB_large_height hx0 hx1 hτ
  have heq : ‖eq‖ ≤ (2 / Real.pi) * Real.exp (-Real.pi * τ) := by
    simpa [ζ, q0, eq] using chartQ_large_height hx0 hx1 hτ
  have hdb : ‖db‖ ≤ 10 * Real.exp (-Real.pi * τ) := by
    simpa [db, neg_div] using deriv_chartB_large_height hx0 hx1 hτ
  have hdq : ‖dq‖ ≤ 2 * Real.exp (-Real.pi * τ) := by
    simpa [dq, neg_div] using deriv_chartQ_large_height hx0 hx1 hτ
  have hBtau_le : chartBTau τ ≤ 1 + τ := chartBTau_le_one_add (by linarith)
  have hBtau_nn : 0 ≤ chartBTau τ := chartBTau_nonneg (by linarith)
  have hb0_norm : ‖b0‖ ≤ 2 * (1 + τ) := by
    dsimp [b0]
    have hx_le : ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]; linarith
    have hB_norm : ‖(chartBTau τ : ℂ)‖ = chartBTau τ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
    calc ‖(chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)‖
        ≤ ‖(chartBTau τ : ℂ)‖ + ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ (1 + τ) + 1 := by linarith
      _ ≤ 2 * (1 + τ) := by linarith
  have hq0_norm : ‖q0‖ ≤ 2 * (1 + τ) := by
    dsimp [q0]
    have hx_le : ‖(((1 - x) / 2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have hB_norm : ‖Complex.I * (chartBTau τ : ℂ)‖ = chartBTau τ := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
    calc ‖(((1 - x) / 2 : ℝ) : ℂ) - Complex.I * (chartBTau τ : ℂ)‖
        ≤ ‖(((1 - x) / 2 : ℝ) : ℂ)‖ + ‖Complex.I * (chartBTau τ : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + τ) := by linarith
      _ ≤ 2 * (1 + τ) := by linarith
  have hlead : (2 * (Real.pi : ℂ) / 3) * ((-Complex.I / 2) * q0 + b0 * (-1 / 2 : ℂ)) =
      -((2 * Real.pi / 3 * chartBTau τ : ℝ) : ℂ) -
        ((Real.pi / 3 * (1 / 2 - x) : ℝ) : ℂ) * Complex.I := by
    dsimp [b0, q0]; apply Complex.ext <;> simp <;> ring
  have hsplit : deriv chartOmega ζ -
      (-((2 * Real.pi / 3 * chartBTau τ : ℝ) : ℂ) -
        ((Real.pi / 3 * (1 / 2 - x) : ℝ) : ℂ) * Complex.I) =
      (2 * (Real.pi : ℂ) / 3) *
        (db * q0 + (-Complex.I / 2) * eq + db * eq +
          eb * (-1 / 2 : ℂ) + b0 * dq + eb * dq) := by
    rw [hdom, ← hlead]
    have hb_eq : chartB ζ = b0 + eb := by dsimp [eb]; ring
    have hq_eq : chartQ ζ = q0 + eq := by dsimp [eq]; ring
    have hdb_eq : deriv chartB ζ = -Complex.I / 2 + db := by dsimp [db]; ring
    have hdq_eq : deriv chartQ ζ = -1 / 2 + dq := by dsimp [dq]; ring
    rw [hb_eq, hq_eq, hdb_eq, hdq_eq]; ring
  rw [hsplit, norm_mul, show ‖(2 * (Real.pi : ℂ) / 3)‖ = 2 * Real.pi / 3 by
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_ofNat]]
  have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le hτ
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have h12pi : 12 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith
  have h2pi : 2 / Real.pi ≤ 1 := by rw [div_le_iff₀ Real.pi_pos]; linarith
  have heb4 : ‖eb‖ ≤ 4 * Real.exp (-Real.pi * τ) := heb.trans (by gcongr)
  have heq1 : ‖eq‖ ≤ Real.exp (-Real.pi * τ) :=
    heq.trans (mul_le_of_le_one_left (Real.exp_pos _).le h2pi)
  have h_e : 0 < Real.exp (-Real.pi * τ) := Real.exp_pos _
  have h_1t : 1 ≤ 1 + τ := by linarith
  have h_prod1 : ‖db * q0‖ ≤ 20 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]
    calc ‖db‖ * ‖q0‖ ≤ (10 * Real.exp (-Real.pi * τ)) * (2 * (1 + τ)) := by gcongr
      _ = 20 * (1 + τ) * Real.exp (-Real.pi * τ) := by ring
  have h_prod2 : ‖(-Complex.I / 2) * eq‖ ≤ (1 / 2) * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_ofNat]
    calc (1 / 2 : ℝ) * ‖eq‖ ≤ (1 / 2) * (1 * Real.exp (-Real.pi * τ)) := by gcongr; linarith
      _ ≤ (1 / 2) * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith only [h_e, h_1t]
  have h_prod3 : ‖db * eq‖ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]
    have h1 : ‖eq‖ ≤ 1 / 400 := heq1.trans hexp_le
    calc ‖db‖ * ‖eq‖ ≤ (10 * Real.exp (-Real.pi * τ)) * (1 / 400) := by gcongr
      _ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith only [h_e, h_1t]
  have h_prod4 : ‖eb * (-1 / 2 : ℂ)‖ ≤ 2 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul, norm_div, norm_neg, norm_one, Complex.norm_ofNat]
    calc ‖eb‖ * (1 / 2 : ℝ) ≤ (4 * Real.exp (-Real.pi * τ)) * (1 / 2) := by gcongr
      _ = 2 * 1 * Real.exp (-Real.pi * τ) := by ring
      _ ≤ 2 * (1 + τ) * Real.exp (-Real.pi * τ) := by gcongr
  have h_prod5 : ‖b0 * dq‖ ≤ 4 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]
    calc ‖b0‖ * ‖dq‖ ≤ (2 * (1 + τ)) * (2 * Real.exp (-Real.pi * τ)) := by gcongr
      _ = 4 * (1 + τ) * Real.exp (-Real.pi * τ) := by ring
  have h_prod6 : ‖eb * dq‖ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]
    have h1 : ‖eb‖ ≤ 4 / 400 := heb4.trans (by linarith)
    calc ‖eb‖ * ‖dq‖ ≤ (4 / 400) * (2 * Real.exp (-Real.pi * τ)) := by gcongr
      _ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith only [h_e, h_1t]
  have hsum_le : ‖db * q0 + (-Complex.I / 2) * eq + db * eq +
      eb * (-1 / 2 : ℂ) + b0 * dq + eb * dq‖ ≤ 29 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    have t1 := norm_add_le (db * q0 + (-Complex.I / 2) * eq + db * eq + eb * (-1 / 2 : ℂ) + b0 * dq) (eb * dq)
    have t2 := norm_add_le (db * q0 + (-Complex.I / 2) * eq + db * eq + eb * (-1 / 2 : ℂ)) (b0 * dq)
    have t3 := norm_add_le (db * q0 + (-Complex.I / 2) * eq + db * eq) (eb * (-1 / 2 : ℂ))
    have t4 := norm_add_le (db * q0 + (-Complex.I / 2) * eq) (db * eq)
    have t5 := norm_add_le (db * q0) ((-Complex.I / 2) * eq)
    have h_et : 0 ≤ (1 + τ) * Real.exp (-Real.pi * τ) := mul_nonneg (by linarith) h_e.le
    linarith [h_prod1, h_prod2, h_prod3, h_prod4, h_prod5, h_prod6, h_et]
  calc (2 * Real.pi / 3) * ‖db * q0 + (-Complex.I / 2) * eq + db * eq +
        eb * (-1 / 2 : ℂ) + b0 * dq + eb * dq‖
      ≤ (2 * 4 / 3) * (29 * (1 + τ) * Real.exp (-Real.pi * τ)) := by gcongr
    _ ≤ 100 * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith only [h_e, h_1t]

/-- Large-height asymptotic for `ω''(x + iτ)` on `0 < x < 1/2`, `τ ≥ 2`. -/
theorem deriv2_chartOmega_large_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {x τ : ℝ}, 0 < x → x < 1 / 2 → 2 ≤ τ →
      ‖deriv (deriv chartOmega) ((x : ℂ) + Complex.I * (τ : ℂ)) -
          ((Real.pi / 3 : ℝ) : ℂ) * Complex.I‖ ≤
        C * (1 + τ) * Real.exp (-Real.pi * τ) := by
  refine ⟨1500, by norm_num, fun {x τ} hx0 hx1 hτ => ?_⟩
  set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
  have hre0 : 0 < ζ.re := by simp [ζ]; exact hx0
  have hre1 : ζ.re < 1 / 2 := by simp [ζ]; linarith
  have hd2 := deriv2_chartOmega_eq hre0 hre1
  have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le hτ
  have hcos_norm := cos_pi_large_height_norm_lb hx0.le hx1.le hτ
  have hsin_cos_norm : ‖Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)‖ ≤ 2 := by
    set u := Complex.exp (-(2 * Real.pi * τ : ℝ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))
    have hu_norm : ‖u‖ ≤ 1 / 400 := by
      dsimp [u]; rw [Complex.norm_exp]
      have : ((-(2 * Real.pi * τ : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)).re =
          -2 * Real.pi * τ := by simp
      rw [this]
      exact (Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])).trans hexp_le
    have h1u_ge : 399 / 400 ≤ ‖1 + u‖ := by
      have htri := norm_sub_norm_le (1 : ℂ) (-u)
      rw [sub_neg_eq_add, norm_one, norm_neg] at htri; linarith
    have h1u_ne : 1 + u ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1u_ge; linarith
    have hexp_ne : Complex.exp ((Real.pi * τ : ℝ) - Complex.I * ((Real.pi * x : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    have hdiv : Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ) =
        Complex.I * (1 - u) / (1 + u) := by
      rw [sin_pi_large_height_factor x τ, cos_pi_large_height_factor x τ]
      dsimp [u]
      field_simp [hexp_ne, h1u_ne]
    rw [hdiv, norm_div, norm_mul, Complex.norm_I, one_mul]
    have hnum : ‖1 - u‖ ≤ 401 / 400 := by
      calc ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le (1 : ℂ) u
        _ ≤ 1 + 1 / 400 := by rw [norm_one]; linarith
        _ = 401 / 400 := by norm_num
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hinv_cos : ‖(Complex.cos ((Real.pi : ℂ) * ζ))⁻¹‖ ≤ 4 * Real.exp (-Real.pi * τ) := by
    rw [norm_inv, inv_eq_one_div, show -Real.pi * τ = -(Real.pi * τ) by ring, Real.exp_neg, ← one_div]
    rw [show (4 : ℝ) * (1 / Real.exp (Real.pi * τ)) = 4 / Real.exp (Real.pi * τ) by ring,
      div_le_div_iff₀ (by linarith [hcos_norm, Real.exp_pos (Real.pi * τ)]) (Real.exp_pos _)]
    linarith
  have hdb_norm : ‖deriv chartB ζ + Complex.I / 2‖ ≤ 10 * Real.exp (-Real.pi * τ) :=
    deriv_chartB_large_height hx0.le hx1.le hτ
  have hdq_norm : ‖deriv chartQ ζ + 1 / 2‖ ≤ 2 * Real.exp (-Real.pi * τ) :=
    deriv_chartQ_large_height hx0.le hx1.le hτ
  have hdb_ge : 1 / 4 ≤ ‖deriv chartB ζ‖ := by
    have h := norm_sub_norm_le (-Complex.I / 2) (-(deriv chartB ζ + Complex.I / 2))
    rw [show -Complex.I / 2 - -(deriv chartB ζ + Complex.I / 2) = deriv chartB ζ by ring,
      norm_neg, norm_div, norm_neg, Complex.norm_I, Complex.norm_ofNat] at h
    linarith [hdb_norm.trans (by linarith : 10 * Real.exp (-Real.pi * τ) ≤ 10 / 400)]
  have hdq_ge : 1 / 4 ≤ ‖deriv chartQ ζ‖ := by
    have h := norm_sub_norm_le (-1 / 2 : ℂ) (-(deriv chartQ ζ + 1 / 2))
    rw [show (-1 / 2 : ℂ) - -(deriv chartQ ζ + 1 / 2) = deriv chartQ ζ by ring,
      norm_neg, norm_div, norm_neg, norm_one, Complex.norm_ofNat] at h
    linarith [hdq_norm.trans (by linarith : 2 * Real.exp (-Real.pi * τ) ≤ 2 / 400)]
  have hdb_ne : deriv chartB ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hdb_ge; linarith
  have hdq_ne : deriv chartQ ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hdq_ge; linarith
  have hb2_norm : ‖deriv (deriv chartB) ζ‖ ≤ 16 * Real.pi * Real.exp (-Real.pi * τ) := by
    have h2 := deriv2_chartB_eq hre0 hre1
    have hdiv : deriv (deriv chartB) ζ =
        ((Real.pi : ℂ) / 8) * (Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)) *
          (Complex.cos ((Real.pi : ℂ) * ζ))⁻¹ / deriv chartB ζ := by
      have h_mul : deriv (deriv chartB) ζ =
          (2 * deriv chartB ζ * deriv (deriv chartB) ζ) / (2 * deriv chartB ζ) := by
        have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
        field_simp [h2ne, hdb_ne]
      rw [h_mul, h2]
      have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
      have h8ne : (8 : ℂ) ≠ 0 := by norm_num
      have h4ne : (4 : ℂ) ≠ 0 := by norm_num
      have hc_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 :=
        Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane hre0.le hre1.le
          (fun h => by rw [h] at hre1; simp at hre1))
      field_simp [h2ne, h4ne, h8ne, hdb_ne, hc_ne]; ring
    rw [hdiv, norm_div, norm_mul, norm_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_ofNat]
    have hnum_le : Real.pi / 8 * ‖Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)‖ *
        ‖(Complex.cos ((Real.pi : ℂ) * ζ))⁻¹‖ ≤ 4 * Real.pi * Real.exp (-Real.pi * τ) := by
      calc Real.pi / 8 * ‖Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)‖ *
            ‖(Complex.cos ((Real.pi : ℂ) * ζ))⁻¹‖
          ≤ Real.pi / 8 * 2 * (4 * Real.exp (-Real.pi * τ)) := by gcongr
        _ = Real.pi * Real.exp (-Real.pi * τ) := by ring
        _ ≤ 4 * Real.pi * Real.exp (-Real.pi * τ) := by nlinarith only [Real.pi_pos, Real.exp_pos (-Real.pi * τ)]
    rw [div_le_iff₀ (by linarith)]
    calc Real.pi / 8 * ‖Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)‖ *
          ‖(Complex.cos ((Real.pi : ℂ) * ζ))⁻¹‖
        ≤ 4 * Real.pi * Real.exp (-Real.pi * τ) := hnum_le
      _ = 16 * Real.pi * Real.exp (-Real.pi * τ) * (1 / 4) := by ring
      _ ≤ 16 * Real.pi * Real.exp (-Real.pi * τ) * ‖deriv chartB ζ‖ := by gcongr
  have hq2_norm : ‖deriv (deriv chartQ) ζ‖ ≤ 16 * Real.pi * Real.exp (-Real.pi * τ) := by
    have h2 := deriv2_chartQ_eq hre0 hre1
    have hdiv : deriv (deriv chartQ) ζ =
        ((Real.pi : ℂ) / 8) * (Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)) *
          (Complex.cos ((Real.pi : ℂ) * ζ))⁻¹ / deriv chartQ ζ := by
      have h_mul : deriv (deriv chartQ) ζ =
          (2 * deriv chartQ ζ * deriv (deriv chartQ) ζ) / (2 * deriv chartQ ζ) := by
        have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
        field_simp [h2ne, hdq_ne]
      rw [h_mul, h2]
      have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
      have h8ne : (8 : ℂ) ≠ 0 := by norm_num
      have h4ne : (4 : ℂ) ≠ 0 := by norm_num
      have hc_ne : Complex.cos ((Real.pi : ℂ) * ζ) ≠ 0 :=
        Complex.slitPlane_ne_zero (cos_pi_mem_slitPlane hre0.le hre1.le
          (fun h => by rw [h] at hre1; simp at hre1))
      field_simp [h2ne, h4ne, h8ne, hdq_ne, hc_ne]; ring
    rw [hdiv, norm_div, norm_mul, norm_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_ofNat]
    have hnum_le : Real.pi / 8 * ‖Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)‖ *
        ‖(Complex.cos ((Real.pi : ℂ) * ζ))⁻¹‖ ≤ 4 * Real.pi * Real.exp (-Real.pi * τ) := by
      calc Real.pi / 8 * ‖Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)‖ *
            ‖(Complex.cos ((Real.pi : ℂ) * ζ))⁻¹‖
          ≤ Real.pi / 8 * 2 * (4 * Real.exp (-Real.pi * τ)) := by gcongr
        _ = Real.pi * Real.exp (-Real.pi * τ) := by ring
        _ ≤ 4 * Real.pi * Real.exp (-Real.pi * τ) := by nlinarith only [Real.pi_pos, Real.exp_pos (-Real.pi * τ)]
    rw [div_le_iff₀ (by linarith)]
    calc Real.pi / 8 * ‖Complex.sin ((Real.pi : ℂ) * ζ) / Complex.cos ((Real.pi : ℂ) * ζ)‖ *
          ‖(Complex.cos ((Real.pi : ℂ) * ζ))⁻¹‖
        ≤ 4 * Real.pi * Real.exp (-Real.pi * τ) := hnum_le
      _ = 16 * Real.pi * Real.exp (-Real.pi * τ) * (1 / 4) := by ring
      _ ≤ 16 * Real.pi * Real.exp (-Real.pi * τ) * ‖deriv chartQ ζ‖ := by gcongr
  have hBtau_le : chartBTau τ ≤ 1 + τ := chartBTau_le_one_add (by linarith)
  have hBtau_nn : 0 ≤ chartBTau τ := chartBTau_nonneg (by linarith)
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hb_norm : ‖chartB ζ‖ ≤ 3 * (1 + τ) := by
    have h1 := chartB_large_height hx0.le hx1.le hτ
    have h2 : ‖(chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)‖ ≤ 2 * (1 + τ) := by
      have hx_le : ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]; linarith
      have hB_norm : ‖(chartBTau τ : ℂ)‖ = chartBTau τ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
      calc ‖(chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)‖
          ≤ ‖(chartBTau τ : ℂ)‖ + ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ (1 + τ) + 1 := by linarith
        _ ≤ 2 * (1 + τ) := by linarith
    have h12 : 12 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith
    have h3 : (12 / Real.pi) * Real.exp (-Real.pi * τ) ≤ 1 := by
      calc (12 / Real.pi) * Real.exp (-Real.pi * τ) ≤ 4 * (1 / 400) := by gcongr
        _ ≤ 1 := by norm_num
    have htri := norm_add_le ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))
      (chartB ζ - ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)))
    rw [add_sub_cancel] at htri
    linarith
  have hq_norm : ‖chartQ ζ‖ ≤ 3 * (1 + τ) := by
    have h1 := chartQ_large_height hx0.le hx1.le hτ
    have h2 : ‖(((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖ ≤ 2 * (1 + τ) := by
      have hx_le : ‖(((1 - x) / 2 : ℂ))‖ ≤ 1 := by
        rw [show (((1 - x) / 2 : ℂ)) = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
      have hB_norm : ‖Complex.I * (chartBTau τ : ℂ)‖ = chartBTau τ := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
      calc ‖(((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖
          ≤ ‖(((1 - x) / 2 : ℂ))‖ + ‖Complex.I * (chartBTau τ : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + (1 + τ) := by linarith
        _ ≤ 2 * (1 + τ) := by linarith
    have h2p : 2 / Real.pi ≤ 1 := by rw [div_le_iff₀ Real.pi_pos]; linarith
    have h3 : (2 / Real.pi) * Real.exp (-Real.pi * τ) ≤ 1 := by
      calc (2 / Real.pi) * Real.exp (-Real.pi * τ) ≤ 1 * (1 / 400) := by gcongr
        _ ≤ 1 := by norm_num
    have htri := norm_add_le (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))
      (chartQ ζ - (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ)))
    rw [add_sub_cancel] at htri
    linarith
  set db := deriv chartB ζ + Complex.I / 2
  set dq := deriv chartQ ζ + 1 / 2
  have hsplit : deriv (deriv chartOmega) ζ - ((Real.pi / 3 : ℝ) : ℂ) * Complex.I =
      (2 * (Real.pi : ℂ) / 3) *
        (deriv (deriv chartB) ζ * chartQ ζ + chartB ζ * deriv (deriv chartQ) ζ +
          2 * db * (-1 / 2 : ℂ) + 2 * (-Complex.I / 2) * dq + 2 * db * dq) := by
    rw [hd2]
    have hdb_eq : deriv chartB ζ = -Complex.I / 2 + db := by dsimp [db]; ring
    have hdq_eq : deriv chartQ ζ = -1 / 2 + dq := by dsimp [dq]; ring
    rw [hdb_eq, hdq_eq]; push_cast; ring
  rw [hsplit, norm_mul, show ‖(2 * (Real.pi : ℂ) / 3)‖ = 2 * Real.pi / 3 by
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_ofNat]]
  have h_e : 0 < Real.exp (-Real.pi * τ) := Real.exp_pos _
  have h_1t : 1 ≤ 1 + τ := by linarith
  have h_t1 : ‖deriv (deriv chartB) ζ * chartQ ζ‖ ≤ 200 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]
    calc ‖deriv (deriv chartB) ζ‖ * ‖chartQ ζ‖
        ≤ (16 * Real.pi * Real.exp (-Real.pi * τ)) * (3 * (1 + τ)) := by gcongr
      _ = 48 * Real.pi * (1 + τ) * Real.exp (-Real.pi * τ) := by ring
      _ ≤ 200 * (1 + τ) * Real.exp (-Real.pi * τ) := by
          have : 48 * Real.pi ≤ 200 := by linarith
          gcongr
  have h_t2 : ‖chartB ζ * deriv (deriv chartQ) ζ‖ ≤ 200 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul]
    calc ‖chartB ζ‖ * ‖deriv (deriv chartQ) ζ‖
        ≤ (3 * (1 + τ)) * (16 * Real.pi * Real.exp (-Real.pi * τ)) := by gcongr
      _ = 48 * Real.pi * (1 + τ) * Real.exp (-Real.pi * τ) := by ring
      _ ≤ 200 * (1 + τ) * Real.exp (-Real.pi * τ) := by
          have : 48 * Real.pi ≤ 200 := by linarith
          gcongr
  have h_t3 : ‖2 * db * (-1 / 2 : ℂ)‖ ≤ 10 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_div, norm_neg, norm_one, Complex.norm_ofNat]
    calc 2 * ‖db‖ * (1 / 2 : ℝ) = 1 * ‖db‖ := by ring
      _ ≤ 10 * 1 * Real.exp (-Real.pi * τ) := by linarith
      _ ≤ 10 * (1 + τ) * Real.exp (-Real.pi * τ) := by gcongr
  have h_t4 : ‖2 * (-Complex.I / 2) * dq‖ ≤ 2 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_div, norm_neg, Complex.norm_I, Complex.norm_ofNat]
    calc 2 * (1 / 2 : ℝ) * ‖dq‖ = 1 * ‖dq‖ := by ring
      _ ≤ 2 * 1 * Real.exp (-Real.pi * τ) := by linarith
      _ ≤ 2 * (1 + τ) * Real.exp (-Real.pi * τ) := by gcongr
  have h_t5 : ‖2 * db * dq‖ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h1 : ‖db‖ ≤ 10 / 400 := hdb_norm.trans (by linarith)
    calc 2 * ‖db‖ * ‖dq‖ ≤ 2 * (10 / 400) * (2 * Real.exp (-Real.pi * τ)) := by gcongr
      _ = (1 / 10) * Real.exp (-Real.pi * τ) := by ring
      _ ≤ 1 * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith only [h_e, h_1t]
  have hsum_le : ‖deriv (deriv chartB) ζ * chartQ ζ + chartB ζ * deriv (deriv chartQ) ζ +
      2 * db * (-1 / 2 : ℂ) + 2 * (-Complex.I / 2) * dq + 2 * db * dq‖ ≤
      413 * (1 + τ) * Real.exp (-Real.pi * τ) := by
    have t1 := norm_add_le (deriv (deriv chartB) ζ * chartQ ζ + chartB ζ * deriv (deriv chartQ) ζ +
      2 * db * (-1 / 2 : ℂ) + 2 * (-Complex.I / 2) * dq) (2 * db * dq)
    have t2 := norm_add_le (deriv (deriv chartB) ζ * chartQ ζ + chartB ζ * deriv (deriv chartQ) ζ +
      2 * db * (-1 / 2 : ℂ)) (2 * (-Complex.I / 2) * dq)
    have t3 := norm_add_le (deriv (deriv chartB) ζ * chartQ ζ + chartB ζ * deriv (deriv chartQ) ζ)
      (2 * db * (-1 / 2 : ℂ))
    have t4 := norm_add_le (deriv (deriv chartB) ζ * chartQ ζ) (chartB ζ * deriv (deriv chartQ) ζ)
    linarith
  calc (2 * Real.pi / 3) * ‖deriv (deriv chartB) ζ * chartQ ζ + chartB ζ * deriv (deriv chartQ) ζ +
        2 * db * (-1 / 2 : ℂ) + 2 * (-Complex.I / 2) * dq + 2 * db * dq‖
      ≤ (2 * 4 / 3) * (413 * (1 + τ) * Real.exp (-Real.pi * τ)) := by gcongr
    _ ≤ 1500 * (1 + τ) * Real.exp (-Real.pi * τ) := by nlinarith only [h_e, h_1t]

lemma im_deriv_chartOmega_midline_zero (τ : ℝ) :
    (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im = 0 := by
  have hd : HasDerivAt chartOmega (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)))
      ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) :=
    (analyticAt_chartOmega (by norm_num) (by norm_num)).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) Complex.I τ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul Complex.I).const_add (1 / 2 : ℂ)
  have hcomp := hd.comp τ hline
  have hre_d : HasDerivAt (fun t : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re)
      ((deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) * Complex.I).re) τ := by
    simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hcomp
  have hzero : (fun t : ℝ => (chartOmega ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re) = 0 := by
    ext t
    have hre : ((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re ≤ 1 / 2 := by simp
    unfold chartOmega
    simp only [hre, ↓reduceIte]
    by_cases ht : t = 0
    · subst ht
      have hB2 : chartB (2⁻¹ : ℂ) = 0 := by simpa using chartB_half
      simp [chartOmegaHalf, hB2]
    · exact chartOmegaHalf_midline_re_zero ht
  have h0_d : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 τ := hasDerivAt_const τ 0
  rw [hzero] at hre_d
  have hu := hre_d.unique h0_d
  simpa [Complex.mul_re] using hu

/-- Refined imaginary-part asymptotic for `ω'(x + iτ)` vanishing linearly at `x = 1/2`
(`lower_o1_two_edge.tex`, Lemma J7Q proof, lines 683–686). -/
theorem im_deriv_chartOmega_large_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 2 ≤ τ →
      |(deriv chartOmega ((x : ℂ) + Complex.I * (τ : ℂ))).im +
          (Real.pi / 3) * (1 / 2 - x)| ≤
        (1 / 2 - x) * C * (1 + τ) * Real.exp (-Real.pi * τ) := by
  obtain ⟨C, hC, hderiv2⟩ := deriv2_chartOmega_large_height
  refine ⟨C, hC, fun {x τ} hx0 hx1 hτ => ?_⟩
  rcases eq_or_lt_of_le hx1 with rfl | hx_lt
  · have h12 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (τ : ℂ)) = (1 / 2 : ℂ) + Complex.I * (τ : ℂ) := by
      push_cast; rfl
    rw [h12, im_deriv_chartOmega_midline_zero τ]
    simp
  let f : ℝ → ℝ := fun t => (deriv chartOmega ((t : ℂ) + Complex.I * (τ : ℂ))).im +
    (Real.pi / 3) * (1 / 2 - t)
  have hf_half : f (1 / 2) = 0 := by
    dsimp [f]
    have h12 : (((1 / 2 : ℝ) : ℂ) + Complex.I * (τ : ℂ)) = (1 / 2 : ℂ) + Complex.I * (τ : ℂ) := by
      push_cast; rfl
    rw [h12, im_deriv_chartOmega_midline_zero τ]
    ring
  have hbd_all : ∀ t ∈ Icc x (1 / 2),
      ‖(deriv (deriv chartOmega) ((t : ℂ) + Complex.I * (τ : ℂ))).im - Real.pi / 3‖ ≤
        C * (1 + τ) * Real.exp (-Real.pi * τ) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hx0 ht.1
    have ht1 : t ≤ 1 / 2 := ht.2
    have hcont : ContinuousAt (fun s : ℝ =>
        (deriv (deriv chartOmega) ((s : ℂ) + Complex.I * (τ : ℂ))).im - Real.pi / 3) t := by
      refine (Complex.continuous_im.continuousAt.comp ?_).sub continuousAt_const
      refine ((analyticAt_chartOmega (by simp; exact ht0) (by simp; linarith)).deriv.deriv.continuousAt).comp ?_
      fun_prop
    let s : ℕ → ℝ := fun n =>
      if t ≤ 0 then 1 / ((n : ℝ) + 4)
      else if 1 / 2 ≤ t then 1 / 2 - 1 / ((n : ℝ) + 4)
      else t
    have hs_mem : ∀ n : ℕ, 0 < s n ∧ s n < 1 / 2 := by
      intro n
      dsimp [s]
      split_ifs with h0 h1
      · have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith
        exact ⟨by positivity, by rw [div_lt_iff₀ (by positivity)]; linarith⟩
      · have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 4) := by positivity
        have hlt : 1 / ((n : ℝ) + 4) < 1 / 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
        exact ⟨by linarith, by linarith⟩
      · exact ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩
    have hs_tend : Tendsto s atTop (𝓝 t) := by
      dsimp [s]
      split_ifs with h0 h1
      · have ht_eq : t = 0 := le_antisymm h0 ht0
        subst ht_eq
        have h0' : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        refine (h0'.comp (tendsto_add_atTop_nat 3)).congr fun n => ?_
        dsimp [Function.comp_def]; push_cast; ring
      · have ht_eq : t = 1 / 2 := le_antisymm ht1 h1
        subst ht_eq
        have h0' : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 0) := by
          refine (h0'.comp (tendsto_add_atTop_nat 3)).congr fun n => ?_
          dsimp [Function.comp_def]; push_cast; ring
        simpa using tendsto_const_nhds.sub h1'
      · exact tendsto_const_nhds
    have hbd_s : ∀ n : ℕ,
        ‖(deriv (deriv chartOmega) ((s n : ℂ) + Complex.I * (τ : ℂ))).im - Real.pi / 3‖ ≤
          C * (1 + τ) * Real.exp (-Real.pi * τ) := by
      intro n
      have hnorm := hderiv2 (hs_mem n).1 (hs_mem n).2 hτ
      have him_eq : (deriv (deriv chartOmega) ((s n : ℂ) + Complex.I * (τ : ℂ)) -
          ((Real.pi / 3 : ℝ) : ℂ) * Complex.I).im =
          (deriv (deriv chartOmega) ((s n : ℂ) + Complex.I * (τ : ℂ))).im - Real.pi / 3 := by simp
      rw [Real.norm_eq_abs, ← him_eq]
      exact (Complex.abs_im_le_norm _).trans hnorm
    exact le_of_tendsto (hcont.norm.tendsto.comp hs_tend) (Filter.Eventually.of_forall hbd_s)
  have hf_diff : ∀ t ∈ Icc x (1 / 2), HasDerivWithinAt f
      ((deriv (deriv chartOmega) ((t : ℂ) + Complex.I * (τ : ℂ))).im - Real.pi / 3)
      (Icc x (1 / 2)) t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hx0 ht.1
    have hd_om' : HasDerivAt (deriv chartOmega)
        (deriv (deriv chartOmega) ((t : ℂ) + Complex.I * (τ : ℂ)))
        ((t : ℂ) + Complex.I * (τ : ℂ)) :=
      (analyticAt_chartOmega (by simp; exact ht0) (by simp; linarith [ht.2])).deriv.differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) + Complex.I * (τ : ℂ)) 1 t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const (Complex.I * (τ : ℂ))
    have him_d : HasDerivAt (fun s : ℝ => (deriv chartOmega ((s : ℂ) + Complex.I * (τ : ℂ))).im)
        (deriv (deriv chartOmega) ((t : ℂ) + Complex.I * (τ : ℂ))).im t := by
      simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd_om'.comp t hline)
    have hlin_d : HasDerivAt (fun s : ℝ => (Real.pi / 3) * (1 / 2 - s)) (-(Real.pi / 3)) t := by
      have : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 / 2 : ℝ)
      simpa using this.const_mul (Real.pi / 3)
    exact (him_d.add hlin_d).hasDerivWithinAt
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hf_diff
    (fun t ht => hbd_all t (Ico_subset_Icc_self ht)) (1 / 2) ⟨hx_lt.le, le_rfl⟩
  rw [hf_half, zero_sub, norm_neg, Real.norm_eq_abs] at hmvt
  exact hmvt.trans_eq (by ring)

/-! ### Section 3: Global strip bounds on `stripClosed` (`S4`, `§J7`) -/

lemma deriv_chartOmega_reflect' {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    deriv chartOmega (1 - ζ) = deriv chartOmega ζ := by
  have h10 : 0 ≤ (1 - ζ).re := by simp; linarith
  have h11 : (1 - ζ).re ≤ 1 := by simp; linarith
  have hd1 : HasDerivAt chartOmega (deriv chartOmega (1 - ζ)) (1 - ζ) :=
    (analyticAt_chartOmega h10 h11).differentiableAt.hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => 1 - w) (-1) ζ := by
    simpa using (hasDerivAt_id ζ).const_sub (1 : ℂ)
  have hcomp := hd1.comp ζ hlin
  have hcomp2 : HasDerivAt (fun w : ℂ => -chartOmega w) (-(deriv chartOmega ζ)) ζ :=
    (analyticAt_chartOmega h0 h1).differentiableAt.hasDerivAt.neg
  have heq : (fun w : ℂ => chartOmega (1 - w)) = (fun w : ℂ => -chartOmega w) :=
    funext chartOmega_reflect
  have hcomp' : HasDerivAt (fun w : ℂ => chartOmega (1 - w)) (deriv chartOmega (1 - ζ) * (-1)) ζ :=
    hcomp
  rw [heq] at hcomp'
  linear_combination -(hcomp'.unique hcomp2)

lemma deriv_chartOmega_conj' {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    deriv chartOmega (starRingEnd ℂ ζ) = starRingEnd ℂ (deriv chartOmega ζ) := by
  have h0c : 0 ≤ (starRingEnd ℂ ζ).re := by simpa using h0
  have h1c : (starRingEnd ℂ ζ).re ≤ 1 := by simpa using h1
  have hd1 : HasDerivAt chartOmega (deriv chartOmega (starRingEnd ℂ ζ)) (starRingEnd ℂ ζ) :=
    (analyticAt_chartOmega h0c h1c).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => starRingEnd ℂ ζ + Complex.I * (t : ℂ)) Complex.I 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul Complex.I).const_add
      (starRingEnd ℂ ζ)
  have hc1 := hd1.comp_of_eq (0 : ℝ) hline (by simp)
  have hd2 : HasDerivAt chartOmega (deriv chartOmega ζ) ζ :=
    (analyticAt_chartOmega h0 h1).differentiableAt.hasDerivAt
  have hline2 : HasDerivAt (fun t : ℝ => ζ - Complex.I * (t : ℂ)) (-Complex.I) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul Complex.I).const_sub ζ
  have hc2 := hd2.comp_of_eq (0 : ℝ) hline2 (by simp)
  have heq : (fun t : ℝ => chartOmega (starRingEnd ℂ ζ + Complex.I * (t : ℂ))) =
      (fun t : ℝ => starRingEnd ℂ (chartOmega (ζ - Complex.I * (t : ℂ)))) := by
    ext t
    have hconj_arg : starRingEnd ℂ ζ + Complex.I * (t : ℂ) =
        starRingEnd ℂ (ζ - Complex.I * (t : ℂ)) := by
      apply Complex.ext <;> simp
    have ht0 : 0 ≤ (ζ - Complex.I * (t : ℂ)).re := by simpa using h0
    have ht1 : (ζ - Complex.I * (t : ℂ)).re ≤ 1 := by simpa using h1
    rw [hconj_arg, chartOmega_conj ht0 ht1]
  have h_conj_lim : HasDerivAt (fun t : ℝ => starRingEnd ℂ (chartOmega (ζ - Complex.I * (t : ℂ))))
      (starRingEnd ℂ (deriv chartOmega ζ * (-Complex.I))) 0 :=
    hc2.star
  change HasDerivAt (fun t : ℝ => chartOmega (starRingEnd ℂ ζ + Complex.I * (t : ℂ))) _ 0 at hc1
  rw [heq] at hc1
  have hu := hc1.unique h_conj_lim
  have h_sim : starRingEnd ℂ (deriv chartOmega ζ * (-Complex.I)) =
      starRingEnd ℂ (deriv chartOmega ζ) * Complex.I := by
    rw [map_mul, map_neg, Complex.conj_I, neg_neg]
  rw [h_sim] at hu
  exact mul_right_cancel₀ Complex.I_ne_zero hu

private lemma compact_halfStrip_box_bound {f : ℂ → ℂ} (hf : ContinuousOn f stripClosed) (T : ℝ)
    (_hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 0 ≤ τ → τ ≤ T →
      ‖f ((x : ℂ) + Complex.I * (τ : ℂ))‖ ≤ M := by
  let K : Set ℂ := (Icc (0 : ℝ) (1 / 2)) ×ℂ (Icc (0 : ℝ) T)
  have hK_comp : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hK_sub : K ⊆ stripClosed := fun z hz => ⟨hz.1.1, by linarith [hz.1.2]⟩
  have hcont : ContinuousOn (fun z => ‖f z‖) K := (hf.mono hK_sub).norm
  obtain ⟨M, hM⟩ := (hK_comp.bddAbove_image hcont).exists_ge 0
  refine ⟨max M 0, le_max_right _ _, fun {x τ} hx0 hx1 hτ0 hτT => ?_⟩
  have hmem : (x : ℂ) + Complex.I * (τ : ℂ) ∈ K := by
    refine ⟨⟨by simpa using hx0, by simpa using hx1⟩, ⟨by simpa using hτ0, by simpa using hτT⟩⟩
  exact (hM.2 (‖f ((x : ℂ) + Complex.I * (τ : ℂ))‖) ⟨_, hmem, rfl⟩).trans (le_max_left _ _)

/-- Boundedness of `chartLogBQ` on the entire closed strip `0 ≤ Re ζ ≤ 1` (`lower_o1_two_edge.tex`,
§J7, line 633). -/
theorem chartLogBQ_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ ∈ stripClosed, ‖chartLogBQ ζ‖ ≤ C := by
  obtain ⟨M₀, hM₀_nn, hM₀⟩ := compact_halfStrip_box_bound
    (fun z hz => (analyticAt_chartLogBQ hz.1 hz.2).continuousAt.continuousWithinAt) 4 (by norm_num)
  have h_large : ∀ {x τ : ℝ}, 0 ≤ x → x ≤ 1 / 2 → 4 ≤ τ →
      ‖chartLogBQ ((x : ℂ) + Complex.I * (τ : ℂ))‖ ≤ Real.log 4 + Real.pi := by
    intro x τ hx0 hx1 hτ4
    have hτ2 : 2 ≤ τ := by linarith
    set ζ : ℂ := (x : ℂ) + Complex.I * (τ : ℂ)
    have hB_est := chartB_large_height hx0 hx1 hτ2
    have hQ_est := chartQ_large_height hx0 hx1 hτ2
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    have hexp_le : Real.exp (-Real.pi * τ) ≤ 1 / 400 := exp_neg_pi_tau_le hτ2
    have hB_err : ‖chartB ζ - ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))‖ ≤ 1 / 2 := by
      have h12 : 12 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith
      calc ‖chartB ζ - ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))‖
          ≤ (12 / Real.pi) * Real.exp (-Real.pi * τ) := hB_est
        _ ≤ 4 * (1 / 400) := by gcongr
        _ ≤ 1 / 2 := by norm_num
    have hQ_err : ‖chartQ ζ - (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖ ≤ 1 / 2 := by
      have h2 : 2 / Real.pi ≤ 1 := by rw [div_le_iff₀ Real.pi_pos]; linarith
      calc ‖chartQ ζ - (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖
          ≤ (2 / Real.pi) * Real.exp (-Real.pi * τ) := hQ_est
        _ ≤ 1 * (1 / 400) := by gcongr
        _ ≤ 1 / 2 := by norm_num
    have hBtau_ge : 2 ≤ chartBTau τ := by
      unfold chartBTau
      have hdiv : 0 ≤ Real.log 2 / (2 * Real.pi) :=
        div_nonneg (Real.log_nonneg (by norm_num)) (by positivity [Real.pi_pos])
      linarith
    have hB0_lb : chartBTau τ ≤ ‖(chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)‖ := by
      have hre : ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)).re = chartBTau τ := by simp
      nth_rw 1 [← hre]; exact Complex.re_le_norm _
    have hB0_ub : ‖(chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)‖ ≤ chartBTau τ + 1 / 2 := by
      have hx_le : ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]; linarith
      have hB_norm : ‖(chartBTau τ : ℂ)‖ = chartBTau τ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      calc ‖(chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)‖
          ≤ ‖(chartBTau τ : ℂ)‖ + ‖Complex.I * ((x / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ chartBTau τ + 1 / 2 := by linarith
    have hQ0_lb : chartBTau τ ≤ ‖(((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖ := by
      have him : |((((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ)).im)| = chartBTau τ := by
        simp [abs_of_nonneg (by linarith : 0 ≤ chartBTau τ)]
      nth_rw 1 [← him]; exact Complex.abs_im_le_norm _
    have hQ0_ub : ‖(((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖ ≤ chartBTau τ + 1 / 2 := by
      have hx_le : ‖(((1 - x) / 2 : ℂ))‖ ≤ 1 / 2 := by
        rw [show (((1 - x) / 2 : ℂ)) = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
      have hB_norm : ‖Complex.I * (chartBTau τ : ℂ)‖ = chartBTau τ := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      calc ‖(((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))‖
          ≤ ‖(((1 - x) / 2 : ℂ))‖ + ‖Complex.I * (chartBTau τ : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 / 2 + chartBTau τ := by linarith
        _ = chartBTau τ + 1 / 2 := by ring
    have hB_lb : chartBTau τ / 2 ≤ ‖chartB ζ‖ := by
      have htri := norm_sub_norm_le ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))
        (-((chartB ζ) - ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))))
      rw [sub_neg_eq_add, norm_neg, add_sub_cancel] at htri
      linarith
    have hB_ub : ‖chartB ζ‖ ≤ 2 * chartBTau τ := by
      have htri := norm_add_le ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ))
        ((chartB ζ) - ((chartBTau τ : ℂ) - Complex.I * ((x / 2 : ℝ) : ℂ)))
      rw [add_sub_cancel] at htri
      linarith
    have hQ_lb : chartBTau τ / 2 ≤ ‖chartQ ζ‖ := by
      have htri := norm_sub_norm_le (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))
        (-((chartQ ζ) - (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))))
      rw [sub_neg_eq_add, norm_neg, add_sub_cancel] at htri
      linarith
    have hQ_ub : ‖chartQ ζ‖ ≤ 2 * chartBTau τ := by
      have htri := norm_add_le (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ))
        ((chartQ ζ) - (((1 - x) / 2 : ℂ) - Complex.I * (chartBTau τ : ℂ)))
      rw [add_sub_cancel] at htri
      linarith
    have hratio_lb : 1 / 4 ≤ ‖chartB ζ / chartQ ζ‖ := by
      rw [norm_div, le_div_iff₀ (by linarith)]
      nlinarith only [hB_lb, hQ_ub, hBtau_ge]
    have hratio_ub : ‖chartB ζ / chartQ ζ‖ ≤ 4 := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      nlinarith only [hB_ub, hQ_lb, hBtau_ge]
    have hlog_eq : chartLogBQ ζ = Complex.log (chartB ζ / chartQ ζ) := by
      unfold chartLogBQ
      have hre : ζ.re ≤ 1 / 2 := by simp [ζ]; linarith
      simp only [hre, ↓reduceIte]
    rw [hlog_eq]
    have hnorm_le := Complex.norm_le_abs_re_add_abs_im (Complex.log (chartB ζ / chartQ ζ))
    rw [Complex.log_re, Complex.log_im] at hnorm_le
    have hlog_abs : |Real.log ‖chartB ζ / chartQ ζ‖| ≤ Real.log 4 := by
      have hrat_pos : 0 < ‖chartB ζ / chartQ ζ‖ := by linarith
      rw [abs_le]
      constructor
      · rw [← Real.log_inv]
        exact Real.log_le_log (by norm_num) (by linarith)
      · exact Real.log_le_log hrat_pos hratio_ub
    linarith [Complex.abs_arg_le_pi (chartB ζ / chartQ ζ)]
  let C := max M₀ (Real.log 4 + Real.pi)
  have hC_pos : 0 < C := lt_of_lt_of_le (by positivity [Real.pi_pos, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)])
    (le_max_right _ _)
  refine ⟨C, hC_pos, fun ζ hζ => ?_⟩
  have h_half_nonneg : ∀ {w : ℂ}, 0 ≤ w.re → w.re ≤ 1 / 2 → 0 ≤ w.im → ‖chartLogBQ w‖ ≤ C := by
    intro w hw0 hw1 hwim
    have hw_eq : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by apply Complex.ext <;> simp
    rw [hw_eq]
    by_cases h4 : w.im ≤ 4
    · exact (hM₀ hw0 hw1 hwim h4).trans (le_max_left _ _)
    · push Not at h4
      exact (h_large hw0 hw1 h4.le).trans (le_max_right _ _)
  have h_half : ∀ {w : ℂ}, 0 ≤ w.re → w.re ≤ 1 / 2 → ‖chartLogBQ w‖ ≤ C := by
    intro w hw0 hw1
    by_cases hwim : 0 ≤ w.im
    · exact h_half_nonneg hw0 hw1 hwim
    · push Not at hwim
      have hconj := chartLogBQ_conj hw0 (by linarith)
      have hnorm : ‖chartLogBQ w‖ = ‖chartLogBQ (starRingEnd ℂ w)‖ := by
        rw [hconj, Complex.norm_conj]
      rw [hnorm]
      exact h_half_nonneg (by simpa using hw0) (by simpa using hw1) (by simp; linarith)
  by_cases hle : ζ.re ≤ 1 / 2
  · exact h_half hζ.1 hle
  · push Not at hle
    have h1 := chartLogBQ_reflect ζ
    have hnorm : ‖chartLogBQ ζ‖ = ‖chartLogBQ (1 - ζ)‖ := by
      have : chartLogBQ ζ = -chartLogBQ (1 - ζ) := by rw [h1, neg_neg]
      rw [this, norm_neg]
    rw [hnorm]
    exact h_half (by simp; linarith [hζ.2]) (by simp; linarith)

/-- Global polynomial bound `‖ω(ζ)‖ ≤ C (1 + (Im ζ)^2)` on `stripClosed`
(`lower_o1_two_edge.tex`, §J7, line 633). -/
theorem chartOmega_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ ∈ stripClosed, ‖chartOmega ζ‖ ≤ C * (1 + ζ.im ^ 2) := by
  obtain ⟨M₀, hM₀_nn, hM₀⟩ := compact_halfStrip_box_bound continuousOn_chartOmega 2 (by norm_num)
  let C := max M₀ 48
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun ζ hζ => ?_⟩
  have h_half_nonneg : ∀ {w : ℂ}, 0 ≤ w.re → w.re ≤ 1 / 2 → 0 ≤ w.im →
      ‖chartOmega w‖ ≤ C * (1 + w.im ^ 2) := by
    intro w hw0 hw1 hwim
    have hw_eq : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by apply Complex.ext <;> simp
    by_cases h2 : w.im ≤ 2
    · have hle1 : 1 ≤ 1 + w.im ^ 2 := by linarith [sq_nonneg w.im]
      calc ‖chartOmega w‖ ≤ M₀ := by rw [hw_eq]; exact hM₀ hw0 hw1 hwim h2
        _ ≤ C := le_max_left _ _
        _ ≤ C * (1 + w.im ^ 2) := le_mul_of_one_le_right (le_trans (by norm_num) (le_max_right M₀ 48)) hle1
    · push Not at h2
      have hB := chartB_large_height hw0 hw1 h2.le
      have hQ := chartQ_large_height hw0 hw1 h2.le
      have hBtau_le : chartBTau w.im ≤ 1 + w.im := chartBTau_le_one_add hwim
      have hBtau_nn : 0 ≤ chartBTau w.im := chartBTau_nonneg hwim
      have hpi3 := Real.pi_gt_three
      have hpi4 := Real.pi_lt_four
      have hexp_le : Real.exp (-Real.pi * w.im) ≤ 1 / 400 := exp_neg_pi_tau_le h2.le
      have hB_norm : ‖chartB w‖ ≤ 3 * (1 + w.im) := by
        nth_rw 1 [hw_eq]
        have h12 : 12 / Real.pi ≤ 4 := by rw [div_le_iff₀ Real.pi_pos]; linarith
        have hB_err : ‖chartB ((w.re : ℂ) + Complex.I * (w.im : ℂ)) -
            ((chartBTau w.im : ℂ) - Complex.I * ((w.re / 2 : ℝ) : ℂ))‖ ≤ 1 := by
          calc ‖chartB ((w.re : ℂ) + Complex.I * (w.im : ℂ)) -
                ((chartBTau w.im : ℂ) - Complex.I * ((w.re / 2 : ℝ) : ℂ))‖
              ≤ (12 / Real.pi) * Real.exp (-Real.pi * w.im) := hB
            _ ≤ 4 * (1 / 400) := by gcongr
            _ ≤ 1 := by norm_num
        have hB0_norm : ‖(chartBTau w.im : ℂ) - Complex.I * ((w.re / 2 : ℝ) : ℂ)‖ ≤ 2 * (1 + w.im) := by
          have hx_le : ‖Complex.I * ((w.re / 2 : ℝ) : ℂ)‖ ≤ 1 := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith)]; linarith
          have hBn : ‖(chartBTau w.im : ℂ)‖ = chartBTau w.im := by
            rw [Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
          calc ‖(chartBTau w.im : ℂ) - Complex.I * ((w.re / 2 : ℝ) : ℂ)‖
              ≤ ‖(chartBTau w.im : ℂ)‖ + ‖Complex.I * ((w.re / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
            _ ≤ (1 + w.im) + 1 := by linarith
            _ ≤ 2 * (1 + w.im) := by linarith
        have htri := norm_add_le ((chartBTau w.im : ℂ) - Complex.I * ((w.re / 2 : ℝ) : ℂ))
          (chartB ((w.re : ℂ) + Complex.I * (w.im : ℂ)) -
            ((chartBTau w.im : ℂ) - Complex.I * ((w.re / 2 : ℝ) : ℂ)))
        rw [add_sub_cancel] at htri; linarith
      have hQ_norm : ‖chartQ w‖ ≤ 3 * (1 + w.im) := by
        nth_rw 1 [hw_eq]
        have h2p : 2 / Real.pi ≤ 1 := by rw [div_le_iff₀ Real.pi_pos]; linarith
        have hQ_err : ‖chartQ ((w.re : ℂ) + Complex.I * (w.im : ℂ)) -
            (((1 - w.re) / 2 : ℂ) - Complex.I * (chartBTau w.im : ℂ))‖ ≤ 1 := by
          calc ‖chartQ ((w.re : ℂ) + Complex.I * (w.im : ℂ)) -
                (((1 - w.re) / 2 : ℂ) - Complex.I * (chartBTau w.im : ℂ))‖
              ≤ (2 / Real.pi) * Real.exp (-Real.pi * w.im) := hQ
            _ ≤ 1 * (1 / 400) := by gcongr
            _ ≤ 1 := by norm_num
        have hQ0_norm : ‖(((1 - w.re) / 2 : ℂ) - Complex.I * (chartBTau w.im : ℂ))‖ ≤ 2 * (1 + w.im) := by
          have hx_le : ‖(((1 - w.re) / 2 : ℂ))‖ ≤ 1 := by
            rw [show (((1 - w.re) / 2 : ℂ)) = (((1 - w.re) / 2 : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
          have hBn : ‖Complex.I * (chartBTau w.im : ℂ)‖ = chartBTau w.im := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hBtau_nn]
          calc ‖(((1 - w.re) / 2 : ℂ) - Complex.I * (chartBTau w.im : ℂ))‖
              ≤ ‖(((1 - w.re) / 2 : ℂ))‖ + ‖Complex.I * (chartBTau w.im : ℂ)‖ := norm_sub_le _ _
            _ ≤ 1 + (1 + w.im) := by linarith
            _ ≤ 2 * (1 + w.im) := by linarith
        have htri := norm_add_le (((1 - w.re) / 2 : ℂ) - Complex.I * (chartBTau w.im : ℂ))
          (chartQ ((w.re : ℂ) + Complex.I * (w.im : ℂ)) -
            (((1 - w.re) / 2 : ℂ) - Complex.I * (chartBTau w.im : ℂ)))
        rw [add_sub_cancel] at htri; linarith
      have hOm_eq : chartOmega w = (2 * (Real.pi : ℂ) / 3) * chartB w * chartQ w := by
        unfold chartOmega chartOmegaHalf; simp only [hw1, ↓reduceIte]
      rw [hOm_eq, norm_mul, norm_mul, show ‖2 * (Real.pi : ℂ) / 3‖ = 2 * Real.pi / 3 by
        rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
          Complex.norm_ofNat]]
      have h1w2 : (1 + w.im) ^ 2 ≤ 2 * (1 + w.im ^ 2) := by nlinarith only [sq_nonneg (w.im - 1)]
      calc (2 * Real.pi / 3) * ‖chartB w‖ * ‖chartQ w‖
          ≤ (2 * 4 / 3) * (3 * (1 + w.im)) * (3 * (1 + w.im)) := by gcongr
        _ = 24 * (1 + w.im) ^ 2 := by ring
        _ ≤ 48 * (1 + w.im ^ 2) := by linarith
        _ ≤ C * (1 + w.im ^ 2) := by gcongr; exact le_max_right _ _
  have h_half : ∀ {w : ℂ}, 0 ≤ w.re → w.re ≤ 1 / 2 → ‖chartOmega w‖ ≤ C * (1 + w.im ^ 2) := by
    intro w hw0 hw1
    by_cases hwim : 0 ≤ w.im
    · exact h_half_nonneg hw0 hw1 hwim
    · push Not at hwim
      have hconj := chartOmega_conj hw0 (by linarith)
      have hnorm : ‖chartOmega w‖ = ‖chartOmega (starRingEnd ℂ w)‖ := by
        rw [hconj, Complex.norm_conj]
      rw [hnorm]
      have hbd := h_half_nonneg (w := starRingEnd ℂ w) (by simpa using hw0)
        (by simpa using hw1) (by simp; linarith)
      rw [Complex.conj_im, neg_sq] at hbd
      exact hbd
  by_cases hle : ζ.re ≤ 1 / 2
  · exact h_half hζ.1 hle
  · push Not at hle
    have h1 := chartOmega_reflect ζ
    have hnorm : ‖chartOmega ζ‖ = ‖chartOmega (1 - ζ)‖ := by
      have : chartOmega ζ = -chartOmega (1 - ζ) := by rw [h1, neg_neg]
      rw [this, norm_neg]
    rw [hnorm]
    have hbd := h_half (w := 1 - ζ) (by simp; linarith [hζ.2]) (by simp; linarith)
    simpa [Complex.sub_im, neg_sq] using hbd

/-- Global linear bound `‖ω'(ζ)‖ ≤ C (1 + |Im ζ|)` on `stripClosed`
(`lower_o1_two_edge.tex`, §J7, line 633). -/
theorem deriv_chartOmega_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ ∈ stripClosed, ‖deriv chartOmega ζ‖ ≤ C * (1 + |ζ.im|) := by
  obtain ⟨M₀, hM₀_nn, hM₀⟩ := compact_halfStrip_box_bound
    (fun z hz => (analyticAt_chartOmega hz.1 hz.2).deriv.continuousAt.continuousWithinAt) 2 (by norm_num)
  obtain ⟨C₀, hC₀, h_large⟩ := deriv_chartOmega_large_height
  let C := max M₀ (10 + C₀)
  refine ⟨C, lt_of_lt_of_le (by linarith) (le_max_right _ _), fun ζ hζ => ?_⟩
  have h_half_nonneg : ∀ {w : ℂ}, 0 ≤ w.re → w.re ≤ 1 / 2 → 0 ≤ w.im →
      ‖deriv chartOmega w‖ ≤ C * (1 + w.im) := by
    intro w hw0 hw1 hwim
    have hw_eq : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by apply Complex.ext <;> simp
    by_cases h2 : w.im ≤ 2
    · have hle1 : 1 ≤ 1 + w.im := by linarith
      calc ‖deriv chartOmega w‖ ≤ M₀ := by rw [hw_eq]; exact hM₀ hw0 hw1 hwim h2
        _ ≤ C := le_max_left _ _
        _ ≤ C * (1 + w.im) := le_mul_of_one_le_right (by linarith [le_max_right M₀ (10 + C₀)]) hle1
    · push Not at h2
      have hL := h_large hw0 hw1 h2.le
      rw [← hw_eq] at hL
      have hBtau_le : chartBTau w.im ≤ 1 + w.im := chartBTau_le_one_add hwim
      have hBtau_nn : 0 ≤ chartBTau w.im := chartBTau_nonneg hwim
      have hpi4 := Real.pi_lt_four
      have hexp_le : Real.exp (-Real.pi * w.im) ≤ 1 := (exp_neg_pi_tau_le h2.le).trans (by norm_num)
      have hlead_norm : ‖-((2 * Real.pi / 3 * chartBTau w.im : ℝ) : ℂ) -
          ((Real.pi / 3 * (1 / 2 - w.re) : ℝ) : ℂ) * Complex.I‖ ≤ 10 * (1 + w.im) := by
        have h1 : ‖-((2 * Real.pi / 3 * chartBTau w.im : ℝ) : ℂ)‖ ≤ (8 / 3) * (1 + w.im) := by
          rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (by positivity [Real.pi_pos]), abs_of_nonneg hBtau_nn]
          have : 2 * Real.pi / 3 ≤ 8 / 3 := by linarith
          exact mul_le_mul this hBtau_le hBtau_nn (by norm_num)
        have h2' : ‖((Real.pi / 3 * (1 / 2 - w.re) : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (by positivity [Real.pi_pos]), abs_of_nonneg (by linarith)]
          nlinarith only [hpi4, hw0, hw1]
        have htri := norm_sub_le (-((2 * Real.pi / 3 * chartBTau w.im : ℝ) : ℂ))
          (((Real.pi / 3 * (1 / 2 - w.re) : ℝ) : ℂ) * Complex.I)
        linarith
      have htri := norm_add_le (-((2 * Real.pi / 3 * chartBTau w.im : ℝ) : ℂ) -
          ((Real.pi / 3 * (1 / 2 - w.re) : ℝ) : ℂ) * Complex.I)
        (deriv chartOmega w - (-((2 * Real.pi / 3 * chartBTau w.im : ℝ) : ℂ) -
          ((Real.pi / 3 * (1 / 2 - w.re) : ℝ) : ℂ) * Complex.I))
      rw [add_sub_cancel] at htri
      have herr_le : C₀ * (1 + w.im) * Real.exp (-Real.pi * w.im) ≤ C₀ * (1 + w.im) :=
        mul_le_of_le_one_right (by positivity) hexp_le
      calc ‖deriv chartOmega w‖
          ≤ (10 + C₀) * (1 + w.im) := by linarith
        _ ≤ C * (1 + w.im) := by gcongr; exact le_max_right _ _
  have h_half : ∀ {w : ℂ}, 0 ≤ w.re → w.re ≤ 1 / 2 → ‖deriv chartOmega w‖ ≤ C * (1 + |w.im|) := by
    intro w hw0 hw1
    by_cases hwim : 0 ≤ w.im
    · rw [abs_of_nonneg hwim]; exact h_half_nonneg hw0 hw1 hwim
    · push Not at hwim
      rw [abs_of_neg hwim]
      have hconj := deriv_chartOmega_conj' hw0 (by linarith)
      have hnorm : ‖deriv chartOmega w‖ = ‖deriv chartOmega (starRingEnd ℂ w)‖ := by
        rw [hconj, Complex.norm_conj]
      rw [hnorm]
      have hbd := h_half_nonneg (w := starRingEnd ℂ w) (by simpa using hw0)
        (by simpa using hw1) (by simp; linarith)
      rw [Complex.conj_im] at hbd
      exact hbd
  by_cases hle : ζ.re ≤ 1 / 2
  · exact h_half hζ.1 hle
  · push Not at hle
    have h1 := deriv_chartOmega_reflect' hζ.1 hζ.2
    rw [← h1]
    have hbd := h_half (w := 1 - ζ) (by simp; linarith [hζ.2]) (by simp; linarith)
    simpa [Complex.sub_im, abs_neg] using hbd

/-- Global quadratic bound `‖Υ(ζ)‖ ≤ C (1 + (Im ζ)^2)` on `stripClosed`
(`lower_o1_two_edge.tex`, §J7, line 633; used by S4). -/
theorem chartUpsilon_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ ∈ stripClosed, ‖chartUpsilon ζ‖ ≤ C * (1 + ζ.im ^ 2) := by
  obtain ⟨C₁, hC₁, hlog⟩ := chartLogBQ_bounded
  obtain ⟨C₂, hC₂, hdom⟩ := deriv_chartOmega_strip_bound
  let B₀ := |ComplexBessel.crudeExponentB muStar|
  let C := B₀ + C₁ * C₂ + 2 * C₁ * C₂ + 1
  refine ⟨C, by positivity, fun ζ hζ => ?_⟩
  have hint_bd : ∀ w ∈ stripClosed, ‖chartIntegrand w‖ ≤ C₁ * C₂ * (1 + |w.im|) := by
    intro w hw
    unfold chartIntegrand
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hlog w hw) (hdom w hw) (norm_nonneg _) hC₁.le
  have h1 : ‖∫ x in (0 : ℝ)..ζ.re, chartIntegrand (x : ℂ)‖ ≤ C₁ * C₂ := by
    have h_ae : ∀ x ∈ Set.uIoc 0 ζ.re, ‖chartIntegrand (x : ℂ)‖ ≤ C₁ * C₂ := by
      intro x hx
      have hx_icc : x ∈ Icc (0 : ℝ) 1 := by
        have hx' := Set.uIoc_subset_uIcc hx
        exact Set.uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ hζ hx'
      have hx_strip : (x : ℂ) ∈ stripClosed := by simpa [stripClosed] using hx_icc
      simpa using hint_bd (x : ℂ) hx_strip
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := ζ.re)
      (f := fun x : ℝ => chartIntegrand (x : ℂ)) h_ae
    have hdist : |ζ.re - 0| ≤ 1 := by
      rw [sub_zero, abs_of_nonneg hζ.1]
      exact hζ.2
    exact hnorm.trans (mul_le_of_le_one_right (by positivity) hdist)
  have h2 : ‖∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      C₁ * C₂ * (1 + |ζ.im|) * |ζ.im| := by
    have h_ae : ∀ y ∈ Set.uIoc 0 ζ.im,
        ‖chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C₁ * C₂ * (1 + |ζ.im|) := by
      intro y hy
      have hy_icc : y ∈ Set.uIcc 0 ζ.im := Set.uIoc_subset_uIcc hy
      have hy_abs : |y| ≤ |ζ.im| := by
        rcases le_or_gt 0 ζ.im with him | him
        · rw [Set.uIcc_of_le him] at hy_icc
          rw [abs_of_nonneg hy_icc.1, abs_of_nonneg him]; exact hy_icc.2
        · rw [Set.uIcc_of_ge him.le] at hy_icc
          rw [abs_of_nonpos hy_icc.2, abs_of_neg him]; linarith [hy_icc.1]
      have hy_strip : ((ζ.re : ℂ) + (y : ℂ) * Complex.I) ∈ stripClosed := by
        simpa [stripClosed] using hζ
      have hbd := hint_bd ((ζ.re : ℂ) + (y : ℂ) * Complex.I) hy_strip
      have him_eq : ((ζ.re : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
      rw [him_eq] at hbd
      exact hbd.trans (by gcongr)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := ζ.im)
      (f := fun y : ℝ => chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)) h_ae
    simpa [sub_zero] using hnorm
  have h2' : ‖∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      2 * C₁ * C₂ * (1 + ζ.im ^ 2) := by
    have hlin : (1 + |ζ.im|) * |ζ.im| ≤ 2 * (1 + ζ.im ^ 2) := by
      nlinarith only [sq_nonneg (|ζ.im| - 1), sq_abs ζ.im]
    calc ‖∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ C₁ * C₂ * (1 + |ζ.im|) * |ζ.im| := h2
      _ = C₁ * C₂ * ((1 + |ζ.im|) * |ζ.im|) := by ring
      _ ≤ C₁ * C₂ * (2 * (1 + ζ.im ^ 2)) := by gcongr
      _ = 2 * C₁ * C₂ * (1 + ζ.im ^ 2) := by ring
  unfold chartUpsilon Complex.wedgeIntegral
  have hb0 : ‖(ComplexBessel.crudeExponentB muStar : ℂ)‖ = B₀ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hzero_im : (0 : ℂ).im = 0 := rfl
  have hnorm_sum : ‖(ComplexBessel.crudeExponentB muStar : ℂ) +
      ((∫ x in (0 : ℝ)..ζ.re, chartIntegrand ((x : ℂ) + ((0 : ℂ).im : ℂ) * Complex.I)) +
        Complex.I • ∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I))‖ ≤
      B₀ + C₁ * C₂ + 2 * C₁ * C₂ * (1 + ζ.im ^ 2) := by
    have hI_norm : ‖Complex.I • ∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)‖ =
        ‖∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have h1' : ‖∫ x in (0 : ℝ)..ζ.re, chartIntegrand ((x : ℂ) + ((0 : ℂ).im : ℂ) * Complex.I)‖ ≤
        C₁ * C₂ := by
      simpa [hzero_im] using h1
    have htri := norm_add_le (ComplexBessel.crudeExponentB muStar : ℂ)
      ((∫ x in (0 : ℝ)..ζ.re, chartIntegrand ((x : ℂ) + ((0 : ℂ).im : ℂ) * Complex.I)) +
        Complex.I • ∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I))
    have htri2 := norm_add_le
      (∫ x in (0 : ℝ)..ζ.re, chartIntegrand ((x : ℂ) + ((0 : ℂ).im : ℂ) * Complex.I))
      (Complex.I • ∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I))
    linarith
  have hsq_ge1 : 1 ≤ 1 + ζ.im ^ 2 := by linarith [sq_nonneg ζ.im]
  have hB0_nn : 0 ≤ B₀ := abs_nonneg _
  calc ‖(ComplexBessel.crudeExponentB muStar : ℂ) +
        ((∫ x in (0 : ℝ)..ζ.re, chartIntegrand ((x : ℂ) + ((0 : ℂ).im : ℂ) * Complex.I)) +
          Complex.I • ∫ y in (0 : ℝ)..ζ.im, chartIntegrand ((ζ.re : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ (B₀ + C₁ * C₂) + 2 * C₁ * C₂ * (1 + ζ.im ^ 2) := hnorm_sum
    _ ≤ (B₀ + C₁ * C₂) * (1 + ζ.im ^ 2) + 2 * C₁ * C₂ * (1 + ζ.im ^ 2) := by
        gcongr; exact le_mul_of_one_le_right (by positivity) hsq_ge1
    _ ≤ C * (1 + ζ.im ^ 2) := by
        dsimp [C]; nlinarith only [sq_nonneg ζ.im]

/-- On `stripClosed = {0 ≤ Re ζ ≤ 1}`, `ω(ζ) = 0` if and only if `ζ = 1/2`
(`lower_o1_two_edge.tex`, S3 & §J7, lines 618, 756, 1009). -/
theorem chartOmega_eq_zero_iff {ζ : ℂ} (hζ : ζ ∈ stripClosed) :
    chartOmega ζ = 0 ↔ ζ = 1 / 2 := by
  constructor
  · intro h0
    by_contra hne
    by_cases hle : ζ.re ≤ 1 / 2
    · have hb_re := re_chartB_pos hζ.1 hle hne
      have hq_re := (re_chartQ_Ioo hζ.1 hle hne).1
      have hb_ne : chartB ζ ≠ 0 := fun hb0 => by rw [hb0, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
      have hq_ne : chartQ ζ ≠ 0 := fun hq0 => by rw [hq0, Complex.zero_re] at hq_re; exact lt_irrefl 0 hq_re
      have hpi_ne : (2 * (Real.pi : ℂ) / 3) ≠ 0 :=
        div_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) three_ne_zero
      unfold chartOmega chartOmegaHalf at h0
      simp only [hle, ↓reduceIte] at h0
      rcases mul_eq_zero.mp h0 with hpi_b | hq0
      · rcases mul_eq_zero.mp hpi_b with hpi0 | hb0
        · exact hpi_ne hpi0
        · exact hb_ne hb0
      · exact hq_ne hq0
    · push Not at hle
      have h10 : 0 ≤ (1 - ζ).re := by simp; linarith [hζ.2]
      have h1le : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
      have h1ne : 1 - ζ ≠ 1 / 2 := fun h => hne (by linear_combination -h)
      have hb_re := re_chartB_pos h10 h1le h1ne
      have hq_re := (re_chartQ_Ioo h10 h1le h1ne).1
      have hb_ne : chartB (1 - ζ) ≠ 0 := fun hb0 => by rw [hb0, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
      have hq_ne : chartQ (1 - ζ) ≠ 0 := fun hq0 => by rw [hq0, Complex.zero_re] at hq_re; exact lt_irrefl 0 hq_re
      have hpi_ne : (2 * (Real.pi : ℂ) / 3) ≠ 0 :=
        div_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) three_ne_zero
      unfold chartOmega chartOmegaHalf at h0
      simp only [hle.not_ge, ↓reduceIte, neg_eq_zero] at h0
      rcases mul_eq_zero.mp h0 with hpi_b | hq0
      · rcases mul_eq_zero.mp hpi_b with hpi0 | hb0
        · exact hpi_ne hpi0
        · exact hb_ne hb0
      · exact hq_ne hq0
  · rintro rfl
    exact chartOmega_half

end FormalResearch.ModularBootstrap.ChartGeometry