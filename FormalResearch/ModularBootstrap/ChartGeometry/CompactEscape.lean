module

public import FormalResearch.ModularBootstrap.ChartGeometry.QuadrantMonotonicity
public import FormalResearch.ModularBootstrap.Chart.EvenAndFactorization
public import FormalResearch.ModularBootstrap.StripBand.BandReductionBV

/-!
# Analytic Three-Segment Compact Escape (Lemma J10, `vlo:J10escape`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J10, Lemma J10 (`vlo:J10escape`,
lines 932–1006).

For the fixed reference exponent `Φ*(w) = Φ_V(w; ξ_*)`, `H(w) = Re Φ*(w)`, and `δ₀ = 1/72`:
for every `0 < δ ≤ δ₀`, setting `p := δ exp(i π / 3)` and `y_δ := √3 δ / 2`, and for every
`T₀ ≥ 1/2` (in particular for every sufficiently large `T₀` as in §J7), the three straight segments
`p → y_δ (1 + i) → (1/2)(1 + i) → 1/2 + i T₀`
form a curve `γ_+` (`j10GammaPlus`) in the closed upper left half-strip satisfying
`H ≤ H(p) ≤ -(π² / 36) δ³` throughout (and `H ≤ -ε` for `ε := -H(p)/2 ≥ (π² / 72) δ³ > 0`),
with the reflected curve `γ_- = conj ∘ γ_+` (`j10GammaMinus`) enjoying the same property in the
closed lower left half-strip. Both curves have finite length (in both `ζ` and `ω`), bounded
`|ω'|`, avoid `ω = 0` uniformly, and stay in `Re ω ≥ 0`. No interval or numerical certificate
is required.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ChartGeometry

open FormalResearch.ModularBootstrap.Chart

/-- Cutoff radius `δ₀ = 1/72` (`lower_o1_two_edge.tex`, Lemma J10, line 934). -/
noncomputable def j10Delta0 : ℝ := 1 / 72

/-- Starting point `p(δ) = δ exp(i π / 3)` (`lower_o1_two_edge.tex`, Lemma J10, line 936). -/
noncomputable def j10P (δ : ℝ) : ℂ :=
  (δ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))

/-- Corner ordinate `y_δ = √3 δ / 2` (`lower_o1_two_edge.tex`, Lemma J10, line 936). -/
noncomputable def j10YDelta (δ : ℝ) : ℝ := √3 * δ / 2

/-- Reference real exponent `H(w) = Re Φ_V(w; ξ_*)` (`lower_o1_two_edge.tex`, Lemma J10, line 934). -/
noncomputable def j10H (w : ℂ) : ℝ := (chartPhiV w (xiStar : ℂ)).re

/-- Three-segment escape contour `γ_+ : [0, 3] → ℂ` from `p(δ)` to `y_δ (1 + i)`, then to
`(1/2)(1 + i)`, then to `1/2 + i T₀` (`lower_o1_two_edge.tex`, Lemma J10, lines 939–943). -/
noncomputable def j10GammaPlus (δ T₀ : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then
    ((1 - t : ℝ) : ℂ) * j10P δ + (t : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I))
  else if t ≤ 2 then
    ((2 - t : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
      ((t - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I))
  else
    (1 / 2 : ℂ) + Complex.I * ((((3 - t) * (1 / 2) + (t - 2) * T₀ : ℝ) : ℂ))

/-- Reflected escape contour `γ_- = conj ∘ γ_+` (`lower_o1_two_edge.tex`, Lemma J10, line 948). -/
noncomputable def j10GammaMinus (δ T₀ : ℝ) (t : ℝ) : ℂ :=
  starRingEnd ℂ (j10GammaPlus δ T₀ t)

/-! ### Section 1: Elementary hyperbolic/trigonometric bounds on `‖z‖ ≤ 1/4` -/

private lemma norm_cosh_le_cosh_norm (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh ‖z‖ := by
  change ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤ Real.cosh ‖z‖
  rw [norm_div, Complex.norm_ofNat]
  have hsum : Real.exp z.re + Real.exp (-z.re) = 2 * Real.cosh z.re := by rw [Real.cosh_eq]; ring
  have hcosh : Real.cosh z.re ≤ Real.cosh ‖z‖ := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (norm_nonneg z)]
    exact Complex.abs_re_le_norm z
  calc ‖Complex.exp z + Complex.exp (-z)‖ / 2
      ≤ (Real.exp z.re + Real.exp (-z.re)) / 2 := by
        gcongr; exact (norm_add_le _ _).trans_eq (by rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re])
    _ = Real.cosh z.re := by rw [hsum]; ring
    _ ≤ Real.cosh ‖z‖ := hcosh

private lemma norm_sinh_le_sinh_norm (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.sinh ‖z‖ := by
  let f : ℝ → ℂ := fun t => Complex.sinh ((t : ℂ) * z)
  have hf_d : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (z * Complex.cosh ((t : ℂ) * z)) t := by
    intro t _
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    exact ((Complex.hasDerivAt_sinh _).comp t hlin).congr_deriv (by ring)
  have hftc : Complex.sinh z = ∫ t in (0 : ℝ)..1, z * Complex.cosh ((t : ℂ) * z) := by
    have hc : Continuous (fun t : ℝ => z * Complex.cosh ((t : ℂ) * z)) := by fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hf_d t (by rwa [Set.uIcc_of_le zero_le_one] at ht)) (hc.intervalIntegrable 0 1)
    simpa [f] using hi.symm
  have hg_d : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.sinh (s * ‖z‖)) (‖z‖ * Real.cosh (t * ‖z‖)) t := by
    intro t _
    have hlin : HasDerivAt (fun s : ℝ => s * ‖z‖) ‖z‖ t := by
      simpa using (hasDerivAt_id t).mul_const ‖z‖
    exact ((Real.hasDerivAt_sinh _).comp t hlin).congr_deriv (by ring)
  have hftc_r : Real.sinh ‖z‖ = ∫ t in (0 : ℝ)..1, ‖z‖ * Real.cosh (t * ‖z‖) := by
    have hc : Continuous (fun t : ℝ => ‖z‖ * Real.cosh (t * ‖z‖)) := by fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hg_d t (by rwa [Set.uIcc_of_le zero_le_one] at ht)) (hc.intervalIntegrable 0 1)
    simpa using hi.symm
  rw [hftc, hftc_r]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ fun t ht => ?_) ?_
  · have ht0 : 0 ≤ t := ht.1.le
    rw [norm_mul]
    calc ‖z‖ * ‖Complex.cosh ((t : ℂ) * z)‖
        ≤ ‖z‖ * Real.cosh ‖(t : ℂ) * z‖ := by
          gcongr; exact norm_cosh_le_cosh_norm _
      _ = ‖z‖ * Real.cosh (t * ‖z‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
  · exact (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1

private lemma norm_sin_le_sinh_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := by
  have hsin : Complex.sin z = -Complex.I * Complex.sinh (Complex.I * z) := by
    rw [show Complex.I * z = z * Complex.I by ring, Complex.sinh_mul_I]
    calc Complex.sin z = -(Complex.I * Complex.I) * Complex.sin z := by rw [Complex.I_mul_I]; ring
      _ = -Complex.I * (Complex.sin z * Complex.I) := by ring
  rw [hsin, norm_mul, norm_neg, Complex.norm_I, one_mul]
  simpa [norm_mul, Complex.norm_I, one_mul] using norm_sinh_le_sinh_norm (Complex.I * z)

private lemma norm_one_sub_cos_le_cosh_sub_one (z : ℂ) :
    ‖1 - Complex.cos z‖ ≤ Real.cosh ‖z‖ - 1 := by
  let f : ℝ → ℂ := fun t => 1 - Complex.cos ((t : ℂ) * z)
  have hf_d : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (z * Complex.sin ((t : ℂ) * z)) t := by
    intro t _
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
    exact (((Complex.hasDerivAt_cos _).comp t hlin).const_sub 1).congr_deriv (by ring)
  have hftc : 1 - Complex.cos z = ∫ t in (0 : ℝ)..1, z * Complex.sin ((t : ℂ) * z) := by
    have hc : Continuous (fun t : ℝ => z * Complex.sin ((t : ℂ) * z)) := by fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hf_d t (by rwa [Set.uIcc_of_le zero_le_one] at ht)) (hc.intervalIntegrable 0 1)
    simpa [f] using hi.symm
  have hg_d : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.cosh (s * ‖z‖) - 1) (‖z‖ * Real.sinh (t * ‖z‖)) t := by
    intro t _
    have hlin : HasDerivAt (fun s : ℝ => s * ‖z‖) ‖z‖ t := by
      simpa using (hasDerivAt_id t).mul_const ‖z‖
    exact (((Real.hasDerivAt_cosh _).comp t hlin).sub_const 1).congr_deriv (by ring)
  have hftc_r : Real.cosh ‖z‖ - 1 = ∫ t in (0 : ℝ)..1, ‖z‖ * Real.sinh (t * ‖z‖) := by
    have hc : Continuous (fun t : ℝ => ‖z‖ * Real.sinh (t * ‖z‖)) := by fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hg_d t (by rwa [Set.uIcc_of_le zero_le_one] at ht)) (hc.intervalIntegrable 0 1)
    simpa using hi.symm
  rw [hftc, hftc_r]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ fun t ht => ?_) ?_
  · have ht0 : 0 ≤ t := ht.1.le
    rw [norm_mul]
    calc ‖z‖ * ‖Complex.sin ((t : ℂ) * z)‖
        ≤ ‖z‖ * Real.sinh ‖(t : ℂ) * z‖ := by gcongr; exact norm_sin_le_sinh_norm _
      _ = ‖z‖ * Real.sinh (t * ‖z‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
  · exact (continuous_const.mul (Real.continuous_sinh.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1

private lemma cosh_pi_div_four_lt : Real.cosh (Real.pi / 4) < 4 / 3 := by
  have hpi4 : Real.pi / 4 < 0.7855 := by linarith [Real.pi_lt_d4]
  have h1' : Real.cosh (Real.pi / 4) < Real.cosh 0.7855 := by
    rw [Real.cosh_lt_cosh, abs_of_pos (by positivity [Real.pi_pos]), abs_of_pos (by norm_num)]
    exact hpi4
  have hb1 := Real.exp_bound (x := (0.7855 : ℝ)) (n := 5) (by norm_num) (by norm_num)
  have hb2 := Real.exp_bound (x := (-0.7855 : ℝ)) (n := 5) (by norm_num) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hb1 hb2
  norm_num [Nat.factorial] at hb1 hb2
  have he1 := (abs_le.mp hb1).2
  have he2 := (abs_le.mp hb2).2
  have h2 : Real.cosh 0.7855 < 4 / 3 := by rw [Real.cosh_eq]; linarith
  exact h1'.trans h2

private lemma arsinh_one_bounds : (5 / 6 : ℝ) ≤ Real.arsinh 1 ∧ Real.arsinh 1 ≤ 1 := by
  constructor
  · rw [← Real.sinh_le_sinh, Real.sinh_arsinh, Real.sinh_eq]
    have hb1 := Real.exp_bound (x := (5 / 6 : ℝ)) (n := 5) (by norm_num) (by norm_num)
    have hb2 := Real.exp_bound (x := (-(5 / 6) : ℝ)) (n := 5) (by norm_num) (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hb1 hb2
    norm_num [Nat.factorial] at hb1 hb2
    linarith [(abs_le.mp hb1).2, (abs_le.mp hb2).1]
  · rw [← Real.sinh_le_sinh, Real.sinh_arsinh, Real.sinh_eq]
    have h1 : (2.71 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h2 : Real.exp (-1) < 0.37 := lt_trans Real.exp_neg_one_lt_d9 (by norm_num)
    linarith

private lemma norm_one_sub_cos_pi_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖1 - Complex.cos ((Real.pi : ℂ) * z)‖ < 1 / 3 := by
  have hnorm : ‖(Real.pi : ℂ) * z‖ ≤ Real.pi / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    nlinarith [Real.pi_pos]
  have hcosh : Real.cosh ‖(Real.pi : ℂ) * z‖ ≤ Real.cosh (Real.pi / 4) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity [Real.pi_pos])]
    exact hnorm
  calc ‖1 - Complex.cos ((Real.pi : ℂ) * z)‖
      ≤ Real.cosh ‖(Real.pi : ℂ) * z‖ - 1 := norm_one_sub_cos_le_cosh_sub_one _
    _ ≤ Real.cosh (Real.pi / 4) - 1 := by linarith
    _ < 1 / 3 := by linarith [cosh_pi_div_four_lt]

private lemma cos_pi_re_gt_two_thirds {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    2 / 3 < (Complex.cos ((Real.pi : ℂ) * z)).re := by
  have hu := norm_one_sub_cos_pi_lt hz
  have hre : (1 - Complex.cos ((Real.pi : ℂ) * z)).re ≤ ‖1 - Complex.cos ((Real.pi : ℂ) * z)‖ :=
    Complex.re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at hre
  linarith

private lemma norm_sin_pi_div_two_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖(√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)‖ < 3 / 5 := by
  have hnorm : ‖(Real.pi : ℂ) * z / 2‖ ≤ Real.pi / 8 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_ofNat]
    nlinarith [Real.pi_pos]
  have hsh_le : Real.sinh ‖(Real.pi : ℂ) * z / 2‖ ≤ Real.sinh (Real.pi / 8) :=
    Real.sinh_le_sinh.mpr hnorm
  have h2sh_sq : 2 * Real.sinh (Real.pi / 8) ^ 2 = Real.cosh (Real.pi / 4) - 1 := by
    have h1 := Real.cosh_two_mul (Real.pi / 8)
    have h2 := Real.cosh_sq_sub_sinh_sq (Real.pi / 8)
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring] at h1
    linarith
  have hprod_sq : (√2 * Real.sinh (Real.pi / 8)) ^ 2 < (3 / 5 : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), h2sh_sq]
    linarith [cosh_pi_div_four_lt]
  have hprod_lt : √2 * Real.sinh (Real.pi / 8) < 3 / 5 := by
    have hnn : 0 ≤ √2 * Real.sinh (Real.pi / 8) :=
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sinh_nonneg_iff.mpr (by positivity [Real.pi_pos]))
    nlinarith
  calc ‖(√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)‖
      = √2 * ‖Complex.sin ((Real.pi : ℂ) * z / 2)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
    _ ≤ √2 * Real.sinh ‖(Real.pi : ℂ) * z / 2‖ := by gcongr; exact norm_sin_le_sinh_norm _
    _ ≤ √2 * Real.sinh (Real.pi / 8) := by gcongr
    _ < 3 / 5 := hprod_lt

private lemma re_sqrt_cos_pi_gt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    (3 / 5 : ℝ) < ((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)).re := by
  set w := Complex.cos ((Real.pi : ℂ) * z)
  set s := w ^ (1 / 2 : ℂ)
  have hw_re : 2 / 3 < w.re := cos_pi_re_gt_two_thirds hz
  have hw_slit : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have hs_re : 0 < s.re := cpow_half_re_pos hw_slit
  have hs2 : s ^ 2 = w := cpow_half_sq w
  have hs2_re : s.re ^ 2 - s.im ^ 2 = w.re := by
    have := congrArg Complex.re hs2
    rw [sq, Complex.mul_re] at this
    linarith
  have hs_nsq : w.re ≤ s.re ^ 2 + s.im ^ 2 := by
    have hnsq : (s.re ^ 2 + s.im ^ 2) ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      have him2 : 2 * s.re * s.im = w.im := by
        have := congrArg Complex.im hs2
        rw [sq, Complex.mul_im] at this
        linarith
      calc (s.re ^ 2 + s.im ^ 2) ^ 2
          = (s.re ^ 2 - s.im ^ 2) ^ 2 + (2 * s.re * s.im) ^ 2 := by ring
        _ = w.re ^ 2 + w.im ^ 2 := by rw [hs2_re, him2]
    nlinarith [sq_nonneg w.im, sq_nonneg s.re, sq_nonneg s.im]
  have hs_sq_gt : (3 / 5 : ℝ) ^ 2 < s.re ^ 2 := by linarith
  nlinarith

private lemma arsinh_cos_inner_slitPlane_ball {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) ^ 2 + 1 ∈ Complex.slitPlane ∧
    (Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ) +
      (((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane := by
  have hw_re : 2 / 3 < (Complex.cos ((Real.pi : ℂ) * z)).re := cos_pi_re_gt_two_thirds hz
  have hw1_re : 5 / 3 < (Complex.cos ((Real.pi : ℂ) * z) + 1).re := by
    rw [Complex.add_re, Complex.one_re]; linarith
  have h1 : ((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) ^ 2 + 1 ∈ Complex.slitPlane := by
    rw [cpow_half_sq]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have hs_re : 0 < ((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)).re :=
    cpow_half_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)))
  have hr_re : 0 < ((((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) ^ 2 + 1) ^ (1 / 2 : ℂ)).re :=
    cpow_half_re_pos h1
  refine ⟨h1, Complex.mem_slitPlane_iff.mpr (Or.inl ?_)⟩
  rw [Complex.add_re]
  linarith

private lemma arccos_sin_inner_slitPlane_ball {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)) ^ 2 ∈ Complex.slitPlane ∧
    (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2) +
      Complex.I * (1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)) ^ 2) ^ (1 / 2 : ℂ) ∈
        Complex.slitPlane := by
  set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)
  have h1z : 1 - Z ^ 2 = Complex.cos ((Real.pi : ℂ) * z) := by
    have hc := Complex.cos_two_mul ((Real.pi : ℂ) * z / 2)
    have hsq := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z / 2)
    rw [show 2 * ((Real.pi : ℂ) * z / 2) = (Real.pi : ℂ) * z by ring] at hc
    have hsin2 : 2 * Complex.sin ((Real.pi : ℂ) * z / 2) ^ 2 = 1 - Complex.cos ((Real.pi : ℂ) * z) := by
      linear_combination 2 * hsq + hc
    have h2 : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
    calc 1 - Z ^ 2 = 1 - (√2 : ℂ) ^ 2 * Complex.sin ((Real.pi : ℂ) * z / 2) ^ 2 := by dsimp [Z]; ring
      _ = 1 - 2 * Complex.sin ((Real.pi : ℂ) * z / 2) ^ 2 := by rw [h2]
      _ = Complex.cos ((Real.pi : ℂ) * z) := by rw [hsin2]; ring
  have h1 : 1 - Z ^ 2 ∈ Complex.slitPlane := by
    rw [h1z]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [cos_pi_re_gt_two_thirds hz]))
  have him : 0 < (Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)).im := by
    rw [h1z, Complex.add_im]
    nth_rw 2 [Complex.mul_im]
    rw [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    have hZ_im : -‖Z‖ ≤ Z.im := neg_le_of_abs_le (Complex.abs_im_le_norm Z)
    have hZ_lt : ‖Z‖ < 3 / 5 := norm_sin_pi_div_two_lt hz
    have hs_gt : (3 / 5 : ℝ) < ((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)).re :=
      re_sqrt_cos_pi_gt hz
    linarith
  exact ⟨h1, Complex.mem_slitPlane_iff.mpr (Or.inr him.ne')⟩

private lemma analyticAt_chartB_ball {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) : AnalyticAt ℂ chartB z := by
  obtain ⟨h1, h2⟩ := arsinh_cos_inner_slitPlane_ball hz
  have hcos_slit : Complex.cos ((Real.pi : ℂ) * z) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [cos_pi_re_gt_two_thirds hz]))
  have hcos_an : AnalyticAt ℂ (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w)) z := by fun_prop
  have hsqrt_an : AnalyticAt ℂ (fun w : ℂ => (Complex.cos ((Real.pi : ℂ) * w)) ^ (1 / 2 : ℂ)) z :=
    hcos_an.cpow analyticAt_const hcos_slit
  exact analyticAt_const.mul ((analyticAt_arsinhC h1 h2).comp
    (f := fun w : ℂ => (Complex.cos ((Real.pi : ℂ) * w)) ^ (1 / 2 : ℂ)) hsqrt_an)

private lemma analyticAt_chartQ_ball {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) : AnalyticAt ℂ chartQ z := by
  obtain ⟨h1, h2⟩ := arccos_sin_inner_slitPlane_ball hz
  have hZ_an : AnalyticAt ℂ (fun w : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * w / 2)) z := by
    fun_prop
  exact analyticAt_const.mul ((analyticAt_arccosC h1 h2).comp
    (f := fun w : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * w / 2)) hZ_an)

private lemma analyticAt_chartOmega_ball {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    AnalyticAt ℂ chartOmega z := by
  have han_half : AnalyticAt ℂ chartOmegaHalf z :=
    (analyticAt_const.mul (analyticAt_chartB_ball hz)).mul (analyticAt_chartQ_ball hz)
  have hev : chartOmega =ᶠ[𝓝 z] chartOmegaHalf := by
    have hlt : z.re < 1 / 2 := lt_of_le_of_lt (Complex.re_le_norm z) (by linarith)
    filter_upwards [(Complex.continuous_re.isOpen_preimage (Iio (1 / 2 : ℝ)) isOpen_Iio).mem_nhds
      hlt] with w (hw : w.re < 1 / 2)
    unfold chartOmega
    simp only [hw.le, ↓reduceIte]
  exact han_half.congr hev.symm

/-! ### Section 2: Local cubic bound on `‖z‖ ≤ 1/4` and `H(p(δ)) ≤ -(π² / 36) δ³` -/

private lemma norm_pi_chartB_sub_arsinh_one_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖(Real.pi : ℂ) * chartB z - (Real.arsinh 1 : ℂ)‖ < 4 / 25 := by
  set u : ℂ := 1 - Complex.cos ((Real.pi : ℂ) * z)
  have hu_lt : ‖u‖ < 1 / 3 := norm_one_sub_cos_pi_lt hz
  let f : ℝ → ℂ := fun t => arsinhC ((1 - (t : ℂ) * u) ^ (1 / 2 : ℂ))
  have hf0 : f 0 = (Real.arsinh 1 : ℂ) := by
    dsimp [f]
    simp only [zero_mul, sub_zero, Complex.one_cpow]
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, arsinhC_ofReal]
  have hf1 : f 1 = (Real.pi : ℂ) * chartB z := by
    dsimp [f, chartB]
    have hcos : 1 - (1 : ℂ) * u = Complex.cos ((Real.pi : ℂ) * z) := by
      dsimp [u]; simp
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    simp only [hcos, mul_inv_cancel_left₀ hpi]
  have h1tu_re : ∀ t ∈ Icc (0 : ℝ) 1, 2 / 3 < (1 - (t : ℂ) * u).re := by
    intro t ht
    have htu_norm : ‖(t : ℂ) * u‖ < 1 / 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · norm_num
      · calc t * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ < 1 / 3 := by linarith
    have hre : ((t : ℂ) * u).re ≤ ‖(t : ℂ) * u‖ := Complex.re_le_norm _
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h2tu_re : ∀ t ∈ Icc (0 : ℝ) 1, 5 / 3 < (2 - (t : ℂ) * u).re := by
    intro t ht
    have h1 := h1tu_re t ht
    rw [Complex.sub_re, Complex.one_re] at h1
    rw [Complex.sub_re, Complex.re_ofNat]
    linarith
  have hf_d : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (-u / (2 * (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) *
        (2 - (t : ℂ) * u) ^ (1 / 2 : ℂ))) t := by
    intro t ht
    have h1_slit : 1 - (t : ℂ) * u ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [h1tu_re t ht]))
    have h2_slit : 2 - (t : ℂ) * u ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [h2tu_re t ht]))
    have hs_re : 0 < ((1 - (t : ℂ) * u) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos h1_slit
    have hr_re : 0 < ((2 - (t : ℂ) * u) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos h2_slit
    have hsq_eq : ((1 - (t : ℂ) * u) ^ (1 / 2 : ℂ)) ^ 2 + 1 = 2 - (t : ℂ) * u := by
      rw [cpow_half_sq]; ring
    have ha_slit1 : ((1 - (t : ℂ) * u) ^ (1 / 2 : ℂ)) ^ 2 + 1 ∈ Complex.slitPlane := by
      rw [hsq_eq]; exact h2_slit
    have ha_slit2 : (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) +
        (((1 - (t : ℂ) * u) ^ (1 / 2 : ℂ)) ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane := by
      rw [hsq_eq, Complex.mem_slitPlane_iff]
      left
      rw [Complex.add_re]
      linarith
    have hlin : HasDerivAt (fun s : ℝ => 1 - (s : ℂ) * u) (-u) t := by
      have hm := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const u
      exact (hm.const_sub 1).congr_deriv (by simp)
    have hsqrt_c : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ))
        ((1 / 2 : ℂ) * (1 - (t : ℂ) * u) ^ ((1 / 2 : ℂ) - 1)) (1 - (t : ℂ) * u) := by
      simpa using (hasDerivAt_id (1 - (t : ℂ) * u)).cpow_const (c := (1 / 2 : ℂ)) h1_slit
    have hsqrt : HasDerivAt (fun s : ℝ => (1 - (s : ℂ) * u) ^ (1 / 2 : ℂ))
        ((1 / 2 : ℂ) * (1 - (t : ℂ) * u) ^ ((1 / 2 : ℂ) - 1) * (-u)) t := by
      change HasDerivAt ((fun z : ℂ => z ^ (1 / 2 : ℂ)) ∘ (fun s : ℝ => 1 - (s : ℂ) * u)) _ t
      exact hsqrt_c.comp t hlin
    have har := (hasDerivAt_arsinhC ha_slit1 ha_slit2).comp t hsqrt
    refine har.congr_deriv ?_
    have h1_ne : 1 - (t : ℂ) * u ≠ 0 := Complex.slitPlane_ne_zero h1_slit
    have h1_half : (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) * (1 - (t : ℂ) * u) ^ ((1 / 2 : ℂ) - 1) = 1 := by
      rw [← Complex.cpow_add _ _ h1_ne]; norm_num
    have h2_pow : (2 - (t : ℂ) * u) ^ (-(1 / 2 : ℂ)) * (2 - (t : ℂ) * u) ^ (1 / 2 : ℂ) = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero h2_slit)]; norm_num
    have h1_sne : (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at h1_half; exact zero_ne_one h1_half
    have h2_sne : (2 - (t : ℂ) * u) ^ (1 / 2 : ℂ) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h2_pow; exact zero_ne_one h2_pow
    rw [hsq_eq]
    have hpow_neg : (1 - (t : ℂ) * u) ^ ((1 / 2 : ℂ) - 1) = ((1 - (t : ℂ) * u) ^ (1 / 2 : ℂ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      exact h1_half
    have hpow2_neg : (2 - (t : ℂ) * u) ^ (-(1 / 2 : ℂ)) = ((2 - (t : ℂ) * u) ^ (1 / 2 : ℂ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      exact h2_pow
    rw [hpow_neg, hpow2_neg]
    field_simp [h1_sne, h2_sne]
  have hf_cont : ContinuousOn (fun t : ℝ => -u / (2 * (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) *
      (2 - (t : ℂ) * u) ^ (1 / 2 : ℂ))) (Icc 0 1) := by
    intro t ht
    have h1_slit : 1 - (t : ℂ) * u ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [h1tu_re t ht]))
    have h2_slit : 2 - (t : ℂ) * u ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [h2tu_re t ht]))
    have h1_an : AnalyticAt ℂ (fun w : ℂ => (1 - w * u) ^ (1 / 2 : ℂ)) (t : ℂ) :=
      (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).cpow analyticAt_const h1_slit
    have h2_an : AnalyticAt ℂ (fun w : ℂ => (2 - w * u) ^ (1 / 2 : ℂ)) (t : ℂ) :=
      (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).cpow analyticAt_const h2_slit
    have hs_ne : (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) ≠ 0 := fun h0 => by
      have := cpow_half_re_pos h1_slit; rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
    have hr_ne : (2 - (t : ℂ) * u) ^ (1 / 2 : ℂ) ≠ 0 := fun h0 => by
      have := cpow_half_re_pos h2_slit; rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
    have hc1 : ContinuousAt (fun s : ℝ => (1 - (s : ℂ) * u) ^ (1 / 2 : ℂ)) t :=
      h1_an.continuousAt.comp Complex.continuous_ofReal.continuousAt
    have hc2 : ContinuousAt (fun s : ℝ => (2 - (s : ℂ) * u) ^ (1 / 2 : ℂ)) t :=
      h2_an.continuousAt.comp Complex.continuous_ofReal.continuousAt
    exact (continuousAt_const.div ((continuousAt_const.mul hc1).mul hc2)
      (mul_ne_zero (mul_ne_zero two_ne_zero hs_ne) hr_ne)).continuousWithinAt
  have hint_eq : (Real.pi : ℂ) * chartB z - (Real.arsinh 1 : ℂ) =
      ∫ t in (0 : ℝ)..1, -u / (2 * (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) *
        (2 - (t : ℂ) * u) ^ (1 / 2 : ℂ)) := by
    rw [← hf1, ← hf0]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hf_d t (by rwa [Set.uIcc_of_le zero_le_one] at ht))
      (hf_cont.intervalIntegrable_of_Icc zero_le_one)).symm
  have hnorm_bd : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖-u / (2 * (1 - (t : ℂ) * u) ^ (1 / 2 : ℂ) * (2 - (t : ℂ) * u) ^ (1 / 2 : ℂ))‖ ≤
        ‖u‖ * 3 / (2 * √10) := by
    intro t ht
    have h1_norm : √(2 / 3 : ℝ) < ‖(1 - (t : ℂ) * u) ^ (1 / 2 : ℂ)‖ := by
      have hsq : ‖(1 - (t : ℂ) * u) ^ (1 / 2 : ℂ)‖ ^ 2 = ‖1 - (t : ℂ) * u‖ := by
        rw [← norm_pow, cpow_half_sq]
      have hge : 2 / 3 < ‖1 - (t : ℂ) * u‖ := lt_of_lt_of_le (h1tu_re t ht) (Complex.re_le_norm _)
      rw [← Real.sqrt_sq (norm_nonneg _), hsq]
      exact Real.sqrt_lt_sqrt (by norm_num) hge
    have h2_norm : √(5 / 3 : ℝ) < ‖(2 - (t : ℂ) * u) ^ (1 / 2 : ℂ)‖ := by
      have hsq : ‖(2 - (t : ℂ) * u) ^ (1 / 2 : ℂ)‖ ^ 2 = ‖2 - (t : ℂ) * u‖ := by
        rw [← norm_pow, cpow_half_sq]
      have hge : 5 / 3 < ‖2 - (t : ℂ) * u‖ := lt_of_lt_of_le (h2tu_re t ht) (Complex.re_le_norm _)
      rw [← Real.sqrt_sq (norm_nonneg _), hsq]
      exact Real.sqrt_lt_sqrt (by norm_num) hge
    have hden_pos : 0 < 2 * √(2 / 3 : ℝ) * √(5 / 3 : ℝ) := by positivity
    have hden_eq : 2 * √(2 / 3 : ℝ) * √(5 / 3 : ℝ) = 2 * √10 / 3 := by
      have hmul : √(2 / 3 : ℝ) * √(5 / 3 : ℝ) = √10 / 3 := by
        rw [← Real.sqrt_mul (by norm_num), show (2 / 3 : ℝ) * (5 / 3) = 10 / 9 by norm_num,
          Real.sqrt_div (by norm_num), show √(9 : ℝ) = 3 by norm_num]
      rw [mul_assoc, hmul]; ring
    rw [norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_ofNat]
    calc ‖u‖ / (2 * ‖(1 - (t : ℂ) * u) ^ (1 / 2 : ℂ)‖ * ‖(2 - (t : ℂ) * u) ^ (1 / 2 : ℂ)‖)
        ≤ ‖u‖ / (2 * √(2 / 3 : ℝ) * √(5 / 3 : ℝ)) := by
          gcongr
      _ = ‖u‖ * 3 / (2 * √10) := by rw [hden_eq]; ring
  rw [hint_eq]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    fun t ht => hnorm_bd t (by simpa using Set.uIoc_subset_uIcc ht)
  simp only [sub_zero, abs_one, mul_one] at hle
  have hlt1 : ‖u‖ * 3 / (2 * √10) < 1 / (2 * √10) := by
    have h3 : ‖u‖ * 3 < 1 := by linarith
    exact div_lt_div_of_pos_right h3 (by positivity)
  have hlt2 : 1 / (2 * √10) < (4 / 25 : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num), one_mul]
    have h40 : (25 / 4 : ℝ) < √10 * 2 := by
      have hsq : (25 / 4 : ℝ) ^ 2 < (√10 * 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg 10]
    linarith
  linarith

private lemma re_chartB_ball_gt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    (67 / 100 : ℝ) < ((Real.pi : ℂ) * chartB z).re ∧ 0 < (chartB z).re := by
  have hdiff := norm_pi_chartB_sub_arsinh_one_lt hz
  have hsub : ((Real.arsinh 1 : ℂ) - (Real.pi : ℂ) * chartB z).re ≤
      ‖(Real.pi : ℂ) * chartB z - (Real.arsinh 1 : ℂ)‖ := by
    have hneg : ((Real.arsinh 1 : ℂ) - (Real.pi : ℂ) * chartB z).re =
        -((Real.pi : ℂ) * chartB z - (Real.arsinh 1 : ℂ)).re := by
      simp [Complex.sub_re]
    rw [hneg]
    exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, Complex.ofReal_re] at hsub
  have har := arsinh_one_bounds.1
  have hpi_re : (67 / 100 : ℝ) < ((Real.pi : ℂ) * chartB z).re := by linarith
  have hmul_re : ((Real.pi : ℂ) * chartB z).re = Real.pi * (chartB z).re := by
    rw [Complex.re_ofReal_mul]
  rw [hmul_re] at hpi_re
  exact ⟨by rwa [Complex.re_ofReal_mul],
    by nlinarith [Real.pi_pos]⟩

private lemma norm_chartB_ball_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) : ‖chartB z‖ < 3 / 8 := by
  have hdiff := norm_pi_chartB_sub_arsinh_one_lt hz
  have htri : ‖(Real.pi : ℂ) * chartB z‖ ≤ ‖(Real.arsinh 1 : ℂ)‖ +
      ‖(Real.pi : ℂ) * chartB z - (Real.arsinh 1 : ℂ)‖ := by
    calc ‖(Real.pi : ℂ) * chartB z‖
        = ‖(Real.arsinh 1 : ℂ) + ((Real.pi : ℂ) * chartB z - (Real.arsinh 1 : ℂ))‖ := by
          ring_nf
      _ ≤ ‖(Real.arsinh 1 : ℂ)‖ + ‖(Real.pi : ℂ) * chartB z - (Real.arsinh 1 : ℂ)‖ :=
          norm_add_le _ _
  have har_norm : ‖(Real.arsinh 1 : ℂ)‖ = Real.arsinh 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [arsinh_one_bounds.1])]
  have hpi_norm : ‖(Real.pi : ℂ) * chartB z‖ = Real.pi * ‖chartB z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [har_norm, hpi_norm] at htri
  have hlt : Real.pi * ‖chartB z‖ < 29 / 25 := by linarith [arsinh_one_bounds.2]
  have hpi314 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  nlinarith

private lemma norm_log_chartB_div_xiStar_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖Complex.log (chartB z / (xiStar : ℂ))‖ < 1 / 4 := by
  set w : ℂ := (Real.pi : ℂ) * chartB z
  set a0 : ℝ := Real.arsinh 1
  have ha0_ge : (5 / 6 : ℝ) ≤ a0 := arsinh_one_bounds.1
  have hw_diff : ‖w - (a0 : ℂ)‖ < 4 / 25 := norm_pi_chartB_sub_arsinh_one_lt hz
  have hdiv_eq : chartB z / (xiStar : ℂ) = w / (a0 : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hxi : (xiStar : ℂ) = (a0 : ℂ) / (Real.pi : ℂ) := by
      unfold xiStar a0; push_cast; rfl
    rw [hxi]; dsimp [w]; field_simp [hpi]
  have hw_re : 0 < w.re := by linarith [(re_chartB_ball_gt hz).1]
  have ha0_pos : (0 : ℝ) < a0 := by linarith
  have hlog_eq : Complex.log (chartB z / (xiStar : ℂ)) = Complex.log w - Complex.log (a0 : ℂ) := by
    rw [hdiv_eq, log_div_of_re_pos hw_re ha0_pos]
  let γ : ℝ → ℂ := fun t => (a0 : ℂ) + (t : ℂ) * (w - (a0 : ℂ))
  have hγ_re : ∀ t ∈ Icc (0 : ℝ) 1, (67 / 100 : ℝ) < (γ t).re := by
    intro t ht
    have hbd : ‖(t : ℂ) * (w - (a0 : ℂ))‖ < 4 / 25 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      calc t * ‖w - (a0 : ℂ)‖ ≤ 1 * ‖w - (a0 : ℂ)‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ < 4 / 25 := by linarith
    have hre : -((t : ℂ) * (w - (a0 : ℂ))).re ≤ ‖(t : ℂ) * (w - (a0 : ℂ))‖ :=
      (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    have hγ_re_eq : (γ t).re = a0 + ((t : ℂ) * (w - (a0 : ℂ))).re := by
      simp [γ]
    linarith
  have hγ_d : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => Complex.log (γ s)) ((w - (a0 : ℂ)) / γ t) t := by
    intro t ht
    have hslit : γ t ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [hγ_re t ht]))
    have hlin : HasDerivAt γ (w - (a0 : ℂ)) t := by
      simpa [γ] using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - (a0 : ℂ))).const_add (a0 : ℂ)
    exact ((Complex.hasDerivAt_log hslit).comp t hlin).congr_deriv (by ring)
  have hγ_cont : ContinuousOn (fun t : ℝ => (w - (a0 : ℂ)) / γ t) (Icc 0 1) := by
    intro t ht
    have hne : γ t ≠ 0 := fun h0 => by
      have := hγ_re t ht; rw [h0, Complex.zero_re] at this; linarith
    exact (continuousAt_const.div (by fun_prop) hne).continuousWithinAt
  have hint : Complex.log w - Complex.log (a0 : ℂ) = ∫ t in (0 : ℝ)..1, (w - (a0 : ℂ)) / γ t := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hγ_d t (by rwa [Set.uIcc_of_le zero_le_one] at ht))
      (hγ_cont.intervalIntegrable_of_Icc zero_le_one)
    have hγ0 : γ 0 = (a0 : ℂ) := by dsimp [γ]; simp
    have hγ1 : γ 1 = w := by dsimp [γ]; simp
    rw [hγ0, hγ1] at hi
    exact hi.symm
  rw [hlog_eq, hint]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => (w - (a0 : ℂ)) / γ t) (C := ‖w - (a0 : ℂ)‖ / (67 / 100)) fun t ht => by
      have ht_icc := Set.uIoc_subset_uIcc ht
      simp only [Set.uIcc_of_le zero_le_one] at ht_icc
      have hre := hγ_re t ht_icc
      have hnorm : (67 / 100 : ℝ) < ‖γ t‖ := lt_of_lt_of_le hre (Complex.re_le_norm _)
      rw [norm_div]
      gcongr
  simp only [sub_zero, abs_one, mul_one] at hle
  have hlt : ‖w - (a0 : ℂ)‖ / (67 / 100 : ℝ) < 1 / 4 := by linarith
  linarith

private lemma norm_deriv_chartB_ball_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖deriv chartB z‖ < 1 / 2 := by
  obtain ⟨ha_slit1, ha_slit2⟩ := arsinh_cos_inner_slitPlane_ball hz
  have hcos_slit : Complex.cos ((Real.pi : ℂ) * z) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [cos_pi_re_gt_two_thirds hz]))
  have hcos_d : HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w))
      (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z := by
    have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
    exact ((Complex.hasDerivAt_cos _).comp z hlin).congr_deriv (by ring)
  have hsqrt_d : HasDerivAt (fun w : ℂ => (Complex.cos ((Real.pi : ℂ) * w)) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (Complex.cos ((Real.pi : ℂ) * z)) ^ ((1 / 2 : ℂ) - 1) *
        (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) z :=
    hcos_d.cpow_const hcos_slit
  have har_d := (hasDerivAt_arsinhC ha_slit1 ha_slit2).comp z hsqrt_d
  have hB_d : HasDerivAt chartB _ z := har_d.const_mul (Real.pi : ℂ)⁻¹
  set c := Complex.cos ((Real.pi : ℂ) * z)
  set s := c ^ (1 / 2 : ℂ)
  set r := (s ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hc_ne : c ≠ 0 := Complex.slitPlane_ne_zero hcos_slit
  have hs2 : s ^ 2 = c := cpow_half_sq c
  have hs_inv : c ^ ((1 / 2 : ℂ) - 1) = s⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    change c ^ (1 / 2 : ℂ) * c ^ ((1 / 2 : ℂ) - 1) = 1
    rw [← Complex.cpow_add _ _ hc_ne]; norm_num
  have hr_inv : (s ^ 2 + 1) ^ (-(1 / 2 : ℂ)) = r⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    change r * (s ^ 2 + 1) ^ (-(1 / 2 : ℂ)) = 1
    rw [← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero ha_slit1)]; norm_num
  have hs_ne : s ≠ 0 := fun h0 => by
    have := cpow_half_re_pos hcos_slit; change 0 < s.re at this; rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hr_ne : r ≠ 0 := fun h0 => by
    have := cpow_half_re_pos ha_slit1; change 0 < r.re at this; rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hderiv_eq : deriv chartB z = -Complex.sin ((Real.pi : ℂ) * z) / (2 * s * r) := by
    rw [hB_d.deriv]
    rw [show ((1 / 2 : ℂ) * c ^ ((1 / 2 : ℂ) - 1) * (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) =
        ((1 / 2 : ℂ) * s⁻¹ * (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) by rw [hs_inv],
      show (s ^ 2 + 1) ^ (-(1 / 2 : ℂ)) = r⁻¹ from hr_inv]
    field_simp [hpi_ne, hs_ne, hr_ne]
  rw [hderiv_eq, norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_ofNat]
  have hsin_lt : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ^ 2 < 7 / 9 := by
    have hnorm : ‖(Real.pi : ℂ) * z‖ ≤ Real.pi / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      nlinarith [Real.pi_pos]
    have h1 : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.sinh (Real.pi / 4) :=
      (norm_sin_le_sinh_norm _).trans (Real.sinh_le_sinh.mpr hnorm)
    have hsh2 : Real.sinh (Real.pi / 4) ^ 2 < 7 / 9 := by
      have hsq := Real.cosh_sq_sub_sinh_sq (Real.pi / 4)
      have hch := cosh_pi_div_four_lt
      have hch_nn : 0 ≤ Real.cosh (Real.pi / 4) := (Real.cosh_pos _).le
      nlinarith
    have hnn : 0 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := norm_nonneg _
    nlinarith
  have hs_sq : 2 / 3 < ‖s‖ ^ 2 := by
    rw [← norm_pow, hs2]
    exact lt_of_lt_of_le (cos_pi_re_gt_two_thirds hz) (Complex.re_le_norm _)
  have hr_sq : 5 / 3 < ‖r‖ ^ 2 := by
    rw [← norm_pow, cpow_half_sq, hs2]
    have hre : 5 / 3 < (c + 1).re := by
      rw [Complex.add_re, Complex.one_re]; linarith [cos_pi_re_gt_two_thirds hz]
    exact lt_of_lt_of_le hre (Complex.re_le_norm _)
  have hden_sq : (2 * ‖s‖ * ‖r‖) ^ 2 > 4 * (2 / 3) * (5 / 3) := by
    have : ‖s‖ ^ 2 * ‖r‖ ^ 2 > (2 / 3) * (5 / 3) := by nlinarith [sq_nonneg ‖s‖, sq_nonneg ‖r‖]
    nlinarith
  have hquot_sq : (‖Complex.sin ((Real.pi : ℂ) * z)‖ / (2 * ‖s‖ * ‖r‖)) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [div_pow]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hq_nn : 0 ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ / (2 * ‖s‖ * ‖r‖) := by positivity
  nlinarith

private lemma norm_deriv_chartQ_ball_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖deriv chartQ z‖ < 1 := by
  obtain ⟨h1, h2⟩ := arccos_sin_inner_slitPlane_ball hz
  set Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)
  have hZ_d : HasDerivAt (fun w : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * w / 2))
      ((√2 : ℂ) * (Complex.cos ((Real.pi : ℂ) * z / 2) * ((Real.pi : ℂ) / 2))) z := by
    have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w / 2) ((Real.pi : ℂ) / 2) z := by
      simpa using ((hasDerivAt_id z).const_mul (Real.pi : ℂ)).div_const 2
    exact (((Complex.hasDerivAt_sin _).comp z hlin).const_mul (√2 : ℂ))
  have har_d := (hasDerivAt_arccosC h1 h2).comp z hZ_d
  have hQ_d : HasDerivAt chartQ _ z := har_d.const_mul (Real.pi : ℂ)⁻¹
  have h1z_eq : 1 - Z ^ 2 = Complex.cos ((Real.pi : ℂ) * z) := by
    have hc := Complex.cos_two_mul ((Real.pi : ℂ) * z / 2)
    have hsq := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z / 2)
    rw [show 2 * ((Real.pi : ℂ) * z / 2) = (Real.pi : ℂ) * z by ring] at hc
    have hsin2 : 2 * Complex.sin ((Real.pi : ℂ) * z / 2) ^ 2 = 1 - Complex.cos ((Real.pi : ℂ) * z) := by
      linear_combination 2 * hsq + hc
    have h2' : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
    calc 1 - Z ^ 2 = 1 - (√2 : ℂ) ^ 2 * Complex.sin ((Real.pi : ℂ) * z / 2) ^ 2 := by dsimp [Z]; ring
      _ = 1 - 2 * Complex.sin ((Real.pi : ℂ) * z / 2) ^ 2 := by rw [h2']
      _ = Complex.cos ((Real.pi : ℂ) * z) := by rw [hsin2]; ring
  set s := (Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)
  have hcos_slit : Complex.cos ((Real.pi : ℂ) * z) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [cos_pi_re_gt_two_thirds hz]))
  have hs_ne : s ≠ 0 := fun h0 => by
    have := cpow_half_re_pos hcos_slit; change 0 < s.re at this; rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hs_inv : (1 - Z ^ 2) ^ (-(1 / 2 : ℂ)) = s⁻¹ := by
    rw [h1z_eq]
    apply eq_inv_of_mul_eq_one_right
    change s * (Complex.cos ((Real.pi : ℂ) * z)) ^ (-(1 / 2 : ℂ)) = 1
    rw [← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero hcos_slit)]; norm_num
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hsq2_sq : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  have hsq2_ne : (√2 : ℂ) ≠ 0 := by
    intro h0; rw [h0] at hsq2_sq; norm_num at hsq2_sq
  have hderiv_eq : deriv chartQ z = -Complex.cos ((Real.pi : ℂ) * z / 2) / ((√2 : ℂ) * s) := by
    rw [hQ_d.deriv, hs_inv]
    change (Real.pi : ℂ)⁻¹ * (-s⁻¹ * ((√2 : ℂ) * (Complex.cos ((Real.pi : ℂ) * z / 2) * ((Real.pi : ℂ) / 2)))) = _
    have h2 : (2 : ℂ) = (√2 : ℂ) * (√2 : ℂ) := by rw [← sq, hsq2_sq]
    rw [h2]
    field_simp [hpi_ne, hs_ne, hsq2_ne]
  rw [hderiv_eq, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have hcos_lt : ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ ^ 2 < 7 / 6 := by
    have hnorm : ‖(Real.pi : ℂ) * z / 2‖ ≤ Real.pi / 8 := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_ofNat]
      nlinarith [Real.pi_pos]
    have h1' : ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ ≤ Real.cosh (Real.pi / 8) := by
      refine (norm_cosh_le_cosh_norm (Complex.I * ((Real.pi : ℂ) * z / 2))).trans_eq' ?_ |>.trans ?_
      · rw [show Complex.I * ((Real.pi : ℂ) * z / 2) = ((Real.pi : ℂ) * z / 2) * Complex.I by ring,
          Complex.cosh_mul_I]
      · rw [Real.cosh_le_cosh, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity [Real.pi_pos])]
        rw [norm_mul, Complex.norm_I, one_mul]; exact hnorm
    have hch2 : Real.cosh (Real.pi / 8) ^ 2 < 7 / 6 := by
      have h1_eq : Real.cosh (Real.pi / 8) ^ 2 = (Real.cosh (Real.pi / 4) + 1) / 2 := by
        have h1_mul := Real.cosh_two_mul (Real.pi / 8)
        have h2_sq := Real.cosh_sq_sub_sinh_sq (Real.pi / 8)
        rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring] at h1_mul
        linarith
      rw [h1_eq]; linarith [cosh_pi_div_four_lt]
    have hnn : 0 ≤ ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ := norm_nonneg _
    nlinarith
  have hs_sq : 2 / 3 < ‖s‖ ^ 2 := by
    rw [← norm_pow, cpow_half_sq]
    exact lt_of_lt_of_le (cos_pi_re_gt_two_thirds hz) (Complex.re_le_norm _)
  have hden_sq : (√2 * ‖s‖) ^ 2 > 2 * (2 / 3) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    linarith
  have hquot_sq : (‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ / (√2 * ‖s‖)) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    linarith
  have hq_nn : 0 ≤ ‖Complex.cos ((Real.pi : ℂ) * z / 2)‖ / (√2 * ‖s‖) := by positivity
  nlinarith

private lemma norm_chartQ_ball_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) : ‖chartQ z‖ < 3 / 4 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [chartQ_zero]; norm_num
  · have hdiff : DifferentiableOn ℂ chartQ (closedBall (0 : ℂ) ‖z‖) := fun w hw =>
      (analyticAt_chartQ_ball ((mem_closedBall_zero_iff.mp hw).trans hz)).differentiableAt.differentiableWithinAt
    have hbd : ∀ w ∈ closedBall (0 : ℂ) ‖z‖, ‖deriv chartQ w‖ < 1 := fun w hw =>
      norm_deriv_chartQ_ball_lt ((mem_closedBall_zero_iff.mp hw).trans hz)
    -- Obtain a strict supremum bound by compactness on `closedBall 0 ‖z‖`.
    have hcont : ContinuousOn (fun w => ‖deriv chartQ w‖) (closedBall (0 : ℂ) ‖z‖) := by
      refine continuous_norm.comp_continuousOn fun w hw => ?_
      exact (analyticAt_chartQ_ball ((mem_closedBall_zero_iff.mp hw).trans hz)).deriv.continuousAt.continuousWithinAt
    obtain ⟨w₀, hw₀_mem, hw₀_max⟩ := (isCompact_closedBall (0 : ℂ) ‖z‖).exists_isMaxOn
      ⟨0, mem_closedBall_self (norm_nonneg z)⟩ hcont
    set M := ‖deriv chartQ w₀‖
    have hM_lt : M < 1 := hbd w₀ hw₀_mem
    have hM_nn : 0 ≤ M := norm_nonneg _
    have hmvt : ‖chartQ z - chartQ 0‖ ≤ M * ‖z - 0‖ :=
      (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_deriv_le
        (fun w hw => (analyticAt_chartQ_ball ((mem_closedBall_zero_iff.mp hw).trans hz)).differentiableAt)
        (fun w hw => hw₀_max hw) (mem_closedBall_self (norm_nonneg z)) (mem_closedBall_zero_iff.mpr le_rfl)
    rw [chartQ_zero, sub_zero] at hmvt
    have htri : ‖chartQ z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖chartQ z - 1 / 2‖ := by
      calc ‖chartQ z‖ = ‖(1 / 2 : ℂ) + (chartQ z - 1 / 2)‖ := by ring_nf
        _ ≤ ‖(1 / 2 : ℂ)‖ + ‖chartQ z - 1 / 2‖ := norm_add_le _ _
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hM_mul : M * ‖z‖ < 1 * (1 / 4 : ℝ) := by nlinarith
    linarith

private lemma norm_deriv_chartOmega_ball_lt {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖deriv chartOmega z‖ < Real.pi / 2 := by
  have hev : chartOmega =ᶠ[𝓝 z] chartOmegaHalf := by
    have hlt : z.re < 1 / 2 := lt_of_le_of_lt (Complex.re_le_norm z) (by linarith)
    filter_upwards [(Complex.continuous_re.isOpen_preimage (Iio (1 / 2 : ℝ)) isOpen_Iio).mem_nhds
      hlt] with w (hw : w.re < 1 / 2)
    unfold chartOmega
    simp only [hw.le, ↓reduceIte]
  have hB_d := (analyticAt_chartB_ball hz).differentiableAt.hasDerivAt
  have hQ_d := (analyticAt_chartQ_ball hz).differentiableAt.hasDerivAt
  have hOm_d : HasDerivAt chartOmegaHalf
      ((2 * (Real.pi : ℂ) / 3) * (deriv chartB z * chartQ z + chartB z * deriv chartQ z)) z := by
    have h_eq : chartOmegaHalf = fun w => (2 * (Real.pi : ℂ) / 3) * (chartB w * chartQ w) := by
      ext w; unfold chartOmegaHalf; ring
    rw [h_eq]
    exact (hB_d.fun_mul hQ_d).const_mul (2 * (Real.pi : ℂ) / 3)
  rw [hev.deriv_eq, hOm_d.deriv, norm_mul, norm_div, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_ofNat]
  have h1 := norm_deriv_chartB_ball_lt hz
  have h2 := norm_chartQ_ball_lt hz
  have h3 := norm_chartB_ball_lt hz
  have h4 := norm_deriv_chartQ_ball_lt hz
  have htri : ‖deriv chartB z * chartQ z + chartB z * deriv chartQ z‖ ≤
      ‖deriv chartB z‖ * ‖chartQ z‖ + ‖chartB z‖ * ‖deriv chartQ z‖ := by
    simpa [norm_mul] using norm_add_le (deriv chartB z * chartQ z) (chartB z * deriv chartQ z)
  have hsum_lt : ‖deriv chartB z‖ * ‖chartQ z‖ + ‖chartB z‖ * ‖deriv chartQ z‖ < 3 / 4 := by
    have hprod1 : ‖deriv chartB z‖ * ‖chartQ z‖ < (1 / 2) * (3 / 4) := by
      exact mul_lt_mul' h1.le h2 (norm_nonneg _) (by norm_num)
    have hprod2 : ‖chartB z‖ * ‖deriv chartQ z‖ < (3 / 8) * 1 := by
      exact mul_lt_mul' h3.le h4 (norm_nonneg _) (by norm_num)
    linarith
  have hpi_pos : 0 < 2 * Real.pi / 3 := by positivity [Real.pi_pos]
  nlinarith

private noncomputable def j10G (z : ℂ) : ℂ :=
  if z = 0 then 1
  else 2 * Complex.log (chartB z / (xiStar : ℂ)) * deriv chartOmega z /
    (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * z ^ 2)

private lemma j10G_analytic_and_bound :
    (∃ r₀ > (1 / 4 : ℝ), AnalyticOnNhd ℂ j10G (ball 0 r₀)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 / 4 → ‖j10G z - 1‖ ≤ 36 * ‖z‖) := by
  -- Extend analyticity of `j10G` to a neighborhood of `closedBall 0 (1/4)`.
  have han_cl : ∀ z ∈ closedBall (0 : ℂ) (1 / 4),
      AnalyticAt ℂ chartB z ∧ 0 < (chartB z).re ∧ AnalyticAt ℂ chartOmega z := fun z hz =>
    ⟨analyticAt_chartB_ball (mem_closedBall_zero_iff.mp hz),
      (re_chartB_ball_gt (mem_closedBall_zero_iff.mp hz)).2,
      analyticAt_chartOmega_ball (mem_closedBall_zero_iff.mp hz)⟩
  -- Use `lemma_F` near 0 to get analyticity of `j10G` at 0.
  obtain ⟨η, ρ, hρ_pos, Cη, _, hη_an, hη_sep, hη_fac, hη_mvt⟩ := lemma_F
  have han_near : ∀ z ∈ closedBall (0 : ℂ) (1 / 4), AnalyticAt ℂ j10G z := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · have hev : j10G =ᶠ[𝓝 (0 : ℂ)] (fun w => 1 + η w 0) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ_pos] with w hw
        rcases eq_or_ne w 0 with rfl | hw0
        · have h00 : ‖η 0 0‖ ≤ Cη * (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) :=
            hη_mvt 0 (mem_ball_self hρ_pos) 0 (mem_ball_self hρ_pos)
          simp only [norm_zero, add_zero, mul_zero, norm_le_zero_iff] at h00
          simp [j10G, h00]
        · have hfac := hη_fac w hw 0 (mem_ball_self hρ_pos)
          rw [chartB_zero, zero_pow two_ne_zero, sub_zero] at hfac
          have hpi_ne : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
          have hw2_ne : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
          simp only [j10G, hw0, ↓reduceIte]
          rw [hfac]
          field_simp [hpi_ne, hw2_ne]
      exact (analyticAt_const.add (hη_sep 0 (mem_ball_self hρ_pos) 0 (mem_ball_self hρ_pos)).1).congr
        hev.symm
    · obtain ⟨hb_an, hb_re, hom_an⟩ := han_cl z hz
      have hdiv_slit : chartB z / (xiStar : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        left
        rw [show chartB z / (xiStar : ℂ) = ((xiStar⁻¹ : ℝ) : ℂ) * chartB z by push_cast; ring,
          Complex.re_ofReal_mul]
        exact mul_pos (inv_pos.mpr xiStar_pos) hb_re
      have hlog_an : AnalyticAt ℂ (fun w => Complex.log (chartB w / (xiStar : ℂ))) z :=
        (hb_an.div analyticAt_const (Complex.ofReal_ne_zero.mpr xiStar_pos.ne')).clog hdiv_slit
      have hnum_an : AnalyticAt ℂ (fun w => 2 * Complex.log (chartB w / (xiStar : ℂ)) * deriv chartOmega w) z :=
        (analyticAt_const.mul hlog_an).mul hom_an.deriv
      have hden_ne : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * z ^ 2 ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (pow_ne_zero 2 hz0)
      have hq_an : AnalyticAt ℂ (fun w => 2 * Complex.log (chartB w / (xiStar : ℂ)) * deriv chartOmega w /
          (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * w ^ 2)) z :=
        hnum_an.div (analyticAt_const.mul (analyticAt_id.pow 2)) hden_ne
      have hev : j10G =ᶠ[𝓝 z] (fun w => 2 * Complex.log (chartB w / (xiStar : ℂ)) * deriv chartOmega w /
          (((Real.pi ^ 2 / 6 : ℝ) : ℂ) * w ^ 2)) := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        simp [j10G, hw]
      exact hq_an.congr hev.symm
  -- Compactness of `closedBall 0 (1/4)` gives an open ball `ball 0 r₀` with `r₀ > 1/4`
  -- on which `j10G` is analytic.
  have hopen_set : ∃ U : Set ℂ, IsOpen U ∧ closedBall (0 : ℂ) (1 / 4) ⊆ U ∧ AnalyticOnNhd ℂ j10G U := by
    let U : Set ℂ := {w : ℂ | AnalyticAt ℂ j10G w}
    refine ⟨U, ?_, han_near, fun _ hw => hw⟩
    rw [isOpen_iff_mem_nhds]
    intro w hw
    exact hw.eventually_analyticAt
  obtain ⟨U, hU_open, hU_sub, hU_an⟩ := hopen_set
  have hdist : ∃ r₀ > (1 / 4 : ℝ), ball (0 : ℂ) r₀ ⊆ U := by
    by_cases hUc : Uᶜ = ∅
    · refine ⟨1, by norm_num, fun w _ => ?_⟩
      by_contra hw; exact Set.eq_empty_iff_forall_notMem.mp hUc w hw
    · have hne : Uᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hUc
      have hdisj : Disjoint (closedBall (0 : ℂ) (1 / 4)) Uᶜ :=
        Set.disjoint_compl_right_iff_subset.mpr hU_sub
      obtain ⟨z_min, hz_min_mem, hz_min⟩ := (isCompact_closedBall (0 : ℂ) (1 / 4)).exists_isMinOn
        ⟨0, mem_closedBall_self (by norm_num)⟩ (Metric.continuous_infDist_pt Uᶜ).continuousOn
      have h_inf_pos : 0 < Metric.infDist z_min Uᶜ := by
        rw [← hU_open.isClosed_compl.notMem_iff_infDist_pos hne]
        exact fun hmem => (Set.disjoint_left.mp hdisj hz_min_mem) hmem
      refine ⟨1 / 4 + Metric.infDist z_min Uᶜ, by linarith, fun w hw => ?_⟩
      rw [mem_ball_zero_iff] at hw
      by_cases hw_le : ‖w‖ ≤ 1 / 4
      · exact hU_sub (mem_closedBall_zero_iff.mpr hw_le)
      · push Not at hw_le
        let w0 : ℂ := ((1 / 4 / ‖w‖ : ℝ) : ℂ) * w
        have hw0_norm : ‖w0‖ = 1 / 4 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          have hwn : ‖w‖ ≠ 0 := by linarith
          field_simp [hwn]
        have hw0_mem : w0 ∈ closedBall (0 : ℂ) (1 / 4) := mem_closedBall_zero_iff.mpr hw0_norm.le
        have hw_dist : dist w w0 < Metric.infDist w0 Uᶜ := by
          rw [dist_eq_norm]
          have hsub : w - w0 = (((1 - 1 / 4 / ‖w‖ : ℝ) : ℂ)) * w := by
            dsimp [w0]; push_cast; ring
          rw [hsub, norm_mul, Complex.norm_real]
          have hwn : 0 < ‖w‖ := by linarith
          have hnn : 0 ≤ 1 - 1 / 4 / ‖w‖ := by rw [sub_nonneg, div_le_one hwn]; linarith
          rw [Real.norm_of_nonneg hnn]
          have heq : (1 - 1 / 4 / ‖w‖) * ‖w‖ = ‖w‖ - 1 / 4 := by field_simp [hwn.ne']
          have hmin_le : Metric.infDist z_min Uᶜ ≤ Metric.infDist w0 Uᶜ := hz_min hw0_mem
          linarith
        by_contra hwU
        have hinf_le : Metric.infDist w0 Uᶜ ≤ dist w0 w :=
          Metric.infDist_le_dist_of_mem (by simpa using hwU)
        rw [dist_comm] at hinf_le
        linarith
  obtain ⟨r₀, hr₀_gt, hr₀_sub⟩ := hdist
  have hG_an : AnalyticOnNhd ℂ j10G (ball 0 r₀) := hU_an.mono hr₀_sub
  refine ⟨⟨r₀, hr₀_gt, hG_an⟩, fun z hz => ?_⟩
  let h : ℂ → ℂ := dslope j10G 0
  have hh_diff : DifferentiableOn ℂ h (ball 0 r₀) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self (by linarith : 0 < r₀)))).mpr
      hG_an.differentiableOn
  have hcl_sub : closedBall (0 : ℂ) (1 / 4) ⊆ ball (0 : ℂ) r₀ := closedBall_subset_ball hr₀_gt
  have hh_dc : DiffContOnCl ℂ h (ball (0 : ℂ) (1 / 4)) := by
    have hcl_eq : closure (ball (0 : ℂ) (1 / 4)) = closedBall 0 (1 / 4) :=
      closure_ball 0 (by norm_num)
    exact ⟨hh_diff.mono (ball_subset_ball hr₀_gt.le),
      by rw [hcl_eq]; exact (hh_diff.continuousOn).mono hcl_sub⟩
  have hh_bdy : ∀ w ∈ frontier (ball (0 : ℂ) (1 / 4)), ‖h w‖ ≤ 36 := by
    intro w hw
    rw [frontier_ball 0 (by norm_num)] at hw
    have hw_norm : ‖w‖ = 1 / 4 := mem_sphere_zero_iff_norm.mp hw
    have hw_ne : w ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw_norm; norm_num at hw_norm
    have hj_lt : ‖j10G w‖ < 8 := by
      simp only [j10G, hw_ne, ↓reduceIte, norm_div, norm_mul, Complex.norm_ofNat, norm_pow]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ Real.pi ^ 2 / 6), hw_norm]
      have hlog_lt := norm_log_chartB_div_xiStar_lt hw_norm.le
      have hom_lt := norm_deriv_chartOmega_ball_lt hw_norm.le
      have hnum : 2 * ‖Complex.log (chartB w / (xiStar : ℂ))‖ * ‖deriv chartOmega w‖ <
          2 * (1 / 4) * (Real.pi / 2) := by
        have h1 : 2 * ‖Complex.log (chartB w / (xiStar : ℂ))‖ < 2 * (1 / 4) := by linarith
        exact mul_lt_mul' h1.le hom_lt (norm_nonneg _) (by positivity)
      have hden : Real.pi ^ 2 / 6 * (1 / 4 : ℝ) ^ 2 > 0 := by positivity [Real.pi_pos]
      have hdiv : 2 * ‖Complex.log (chartB w / (xiStar : ℂ))‖ * ‖deriv chartOmega w‖ /
          (Real.pi ^ 2 / 6 * (1 / 4 : ℝ) ^ 2) <
          (2 * (1 / 4) * (Real.pi / 2)) / (Real.pi ^ 2 / 6 * (1 / 4 : ℝ) ^ 2) :=
        div_lt_div_of_pos_right hnum hden
      have h24 : (2 * (1 / 4 : ℝ) * (Real.pi / 2)) / (Real.pi ^ 2 / 6 * (1 / 4 : ℝ) ^ 2) =
          24 / Real.pi := by
        field_simp [Real.pi_pos.ne']; ring
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have h24_lt : 24 / Real.pi < 8 := by rw [div_lt_iff₀ Real.pi_pos]; linarith
      linarith
    have hh_eq : h w = (j10G w - 1) / w := by
      dsimp [h]
      rw [dslope_of_ne j10G hw_ne, slope_def_field, sub_zero, show j10G 0 = 1 by simp [j10G]]
    rw [hh_eq, norm_div, hw_norm]
    have htri : ‖j10G w - 1‖ ≤ ‖j10G w‖ + 1 := by
      simpa using norm_sub_le (j10G w) 1
    linarith
  have hh_max := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hh_dc hh_bdy
    (by rw [closure_ball 0 (by norm_num)]; exact mem_closedBall_zero_iff.mpr hz)
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [j10G]
  · have hh_eq : h z = (j10G z - 1) / z := by
      dsimp [h]
      rw [dslope_of_ne j10G hz0, slope_def_field, sub_zero, show j10G 0 = 1 by simp [j10G]]
    rw [hh_eq, norm_div] at hh_max
    exact (div_le_iff₀ (norm_pos_iff.mpr hz0)).mp hh_max

private lemma j10H_zero : j10H 0 = 0 := by
  unfold j10H
  have h0 : ((0 : ℂ)) = Complex.I * ((0 : ℝ) : ℂ) := by simp
  rw [h0, re_chartPhiV_edge_eq_Ec, show Complex.I * ((0 : ℝ) : ℂ) = 0 by simp, chartOmega_zero]
  have hmin := crudeExponentEc_on_min_line (b := (xiStar : ℂ))
    (Complex.ofReal_ne_zero.mpr xiStar_pos.ne') 0
  have hnorm : ‖(xiStar : ℂ)‖ = xiStar := by
    rw [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le]
  have harg : ((xiStar : ℂ)).arg = 0 := Complex.arg_ofReal_of_nonneg xiStar_pos.le
  rw [hnorm, harg] at hmin
  unfold muStar
  simpa [Complex.ofReal_div, Complex.ofReal_mul] using hmin

theorem j10H_p_le {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ j10Delta0) :
    j10H (j10P δ) ≤ -(Real.pi ^ 2 / 36) * δ ^ 3 := by
  let dir : ℂ := Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))
  have hdir_norm : ‖dir‖ = 1 := by
    dsimp [dir]
    rw [show Complex.I * ((Real.pi / 3 : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I]
  have hdir_re : dir.re = 1 / 2 := by
    dsimp [dir]
    rw [show Complex.I * ((Real.pi / 3 : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_mul_I, Complex.add_re, Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.I_re, Complex.I_im]
    simp [Real.cos_pi_div_three]
  let w : ℝ → ℂ := fun t => (t : ℂ) * dir
  let f : ℝ → ℝ := fun t => j10H (w t) + (Real.pi ^ 2 / 36) * t ^ 3
  have hw_mem_left : ∀ t ∈ Icc (0 : ℝ) δ, 0 ≤ (w t).re ∧ (w t).re ≤ 1 / 2 := by
    intro t ht
    have hre : (w t).re = t / 2 := by
      dsimp [w]; rw [Complex.re_ofReal_mul, hdir_re]; ring
    rw [hre]
    have hδ_144 : δ ≤ 1 / 72 := hδ_le
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hf_cont : ContinuousOn f (Icc 0 δ) := by
    refine ContinuousOn.add ?_ (by fun_prop)
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · have hw_ne : w 0 ≠ 1 / 2 := by simp [w]
      have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.2
        (w 0) (hw_mem_left 0 ht).1 (hw_mem_left 0 ht).2 hw_ne
      have hcont_w : ContinuousAt w 0 := by dsimp [w]; fun_prop
      have hmaps : MapsTo w (Icc (0 : ℝ) δ) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} :=
        fun s hs => hw_mem_left s hs
      have hcw := hd.continuousWithinAt.comp (hcont_w.continuousWithinAt (s := Icc 0 δ)) hmaps
      exact (Complex.continuous_re.continuousAt.comp_continuousWithinAt hcw).mono
        (fun _ => id)
    · have h0 : 0 < (w t).re := by
        dsimp [w]; rw [Complex.re_ofReal_mul, hdir_re]; linarith
      have h1 : (w t).re < 1 / 2 := by
        dsimp [w]; rw [Complex.re_ofReal_mul, hdir_re]
        have hδ_144 : δ ≤ 1 / 72 := hδ_le
        linarith [ht.2]
      have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1 (w t) h0 h1
      have hw_cont : ContinuousAt w t := by dsimp [w]; fun_prop
      exact (Complex.continuous_re.continuousAt.comp (hd.continuousAt.comp hw_cont)).continuousWithinAt
  have hf_diff : DifferentiableOn ℝ f (interior (Icc 0 δ)) := by
    rw [interior_Icc]
    intro t ht
    have h0 : 0 < (w t).re := by dsimp [w]; rw [Complex.re_ofReal_mul, hdir_re]; linarith [ht.1]
    have h1 : (w t).re < 1 / 2 := by
      dsimp [w]; rw [Complex.re_ofReal_mul, hdir_re]
      have hδ_144 : δ ≤ 1 / 72 := hδ_le
      linarith [ht.2]
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1 (w t) h0 h1
    have hline : HasDerivAt w dir t := by
      simpa [w] using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const dir
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd.comp t hline)
    have hcub : HasDerivAt (fun s : ℝ => (Real.pi ^ 2 / 36) * s ^ 3)
        ((Real.pi ^ 2 / 12) * t ^ 2) t := by
      simpa using ((hasDerivAt_pow 3 t).const_mul (Real.pi ^ 2 / 36)).congr_deriv (by ring)
    exact (hre.add hcub).differentiableAt.differentiableWithinAt
  have hf_deriv : ∀ t ∈ interior (Icc 0 δ), deriv f t ≤ 0 := by
    rw [interior_Icc]
    intro t ht
    have h0 : 0 < (w t).re := by dsimp [w]; rw [Complex.re_ofReal_mul, hdir_re]; linarith [ht.1]
    have h1 : (w t).re < 1 / 2 := by
      dsimp [w]; rw [Complex.re_ofReal_mul, hdir_re]
      have hδ_144 : δ ≤ 1 / 72 := hδ_le
      linarith [ht.2]
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1 (w t) h0 h1
    have hline : HasDerivAt w dir t := by
      simpa [w] using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const dir
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd.comp t hline)
    have hcub : HasDerivAt (fun s : ℝ => (Real.pi ^ 2 / 36) * s ^ 3)
        ((Real.pi ^ 2 / 12) * t ^ 2) t := by
      simpa using ((hasDerivAt_pow 3 t).const_mul (Real.pi ^ 2 / 36)).congr_deriv (by ring)
    have hf_d : HasDerivAt f
        (Complex.reCLM (2 * Complex.log (chartB (w t) / (xiStar : ℂ)) * deriv chartOmega (w t) * dir) +
          (Real.pi ^ 2 / 12) * t ^ 2) t := hre.add hcub
    rw [hf_d.deriv]
    have hw_ne : w t ≠ 0 := by
      intro h0'; have := congrArg Complex.re h0'; simp at this; linarith
    have hw_norm : ‖w t‖ ≤ 1 / 4 := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le, hdir_norm, mul_one]
      have hδ_144 : δ ≤ 1 / 72 := hδ_le
      linarith [ht.2]
    have hG_bd := j10G_analytic_and_bound.2 (w t) hw_norm
    have hG_re : 1 / 2 ≤ (j10G (w t)).re := by
      have h1' : ‖j10G (w t) - 1‖ ≤ 36 * ‖w t‖ := hG_bd
      have hnorm_wt : ‖w t‖ ≤ 1 / 72 := by
        dsimp [w]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le, hdir_norm, mul_one]
        exact ht.2.le.trans hδ_le
      have hsub : 1 - (j10G (w t)).re ≤ ‖j10G (w t) - 1‖ := by
        calc 1 - (j10G (w t)).re = -(j10G (w t) - 1).re := by simp
          _ ≤ |(j10G (w t) - 1).re| := neg_le_abs _
          _ ≤ ‖j10G (w t) - 1‖ := Complex.abs_re_le_norm _
      linarith
    have hdir3 : dir ^ 3 = -1 := by
      dsimp [dir]
      rw [← Complex.exp_nat_mul]
      push_cast
      rw [show (3 : ℂ) * (Complex.I * ((Real.pi : ℂ) / 3)) = ((Real.pi : ℝ) : ℂ) * Complex.I by
        ring, Complex.exp_pi_mul_I]
    have hprod_eq : 2 * Complex.log (chartB (w t) / (xiStar : ℂ)) * deriv chartOmega (w t) * dir =
        -((Real.pi ^ 2 / 6 : ℝ) : ℂ) * ((t : ℂ) ^ 2) * j10G (w t) := by
      simp only [j10G, hw_ne, ↓reduceIte]
      have hpi_ne : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      have hw2_ne : (w t) ^ 2 ≠ 0 := pow_ne_zero 2 hw_ne
      field_simp [hpi_ne, hw2_ne]
      calc Complex.log (chartB (w t) / (xiStar : ℂ)) * deriv chartOmega (w t) * dir * (w t) ^ 2
          = Complex.log (chartB (w t) / (xiStar : ℂ)) * deriv chartOmega (w t) * (t : ℂ) ^ 2 * dir ^ 3 := by
            dsimp [w]; ring
        _ = -(Complex.log (chartB (w t) / (xiStar : ℂ)) * deriv chartOmega (w t) * (t : ℂ) ^ 2) := by
            rw [hdir3]; ring
    have hre_eq : (Complex.reCLM (2 * Complex.log (chartB (w t) / (xiStar : ℂ)) *
        deriv chartOmega (w t) * dir)) = -(Real.pi ^ 2 / 6) * t ^ 2 * (j10G (w t)).re := by
      simp only [Complex.reCLM_apply]
      rw [hprod_eq]
      rw [show -((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (t : ℂ) ^ 2 * j10G (w t) =
          ((-(Real.pi ^ 2 / 6) * t ^ 2 : ℝ) : ℂ) * j10G (w t) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [hre_eq]
    have hmul : (Real.pi ^ 2 / 6) * t ^ 2 * (1 / 2 : ℝ) ≤ (Real.pi ^ 2 / 6) * t ^ 2 * (j10G (w t)).re := by
      exact mul_le_mul_of_nonneg_left hG_re (by positivity)
    linarith
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 δ) hf_cont hf_diff hf_deriv
  have hdiff := hanti ⟨le_rfl, hδ_pos.le⟩ ⟨hδ_pos.le, le_rfl⟩ hδ_pos.le
  have hf0 : f 0 = 0 := by
    dsimp [f, w]
    simp [j10H_zero]
  have hfδ : f δ = j10H (j10P δ) + (Real.pi ^ 2 / 36) * δ ^ 3 := by
    dsimp [f, w, j10P, dir]
  rw [hf0, hfδ] at hdiff
  linarith

/-! ### Section 3: Wedge estimates (`|b(w)| ≥ ξ_*`, `Im b(w) ≤ 0`, quadrant of `log(b(w)/ξ_*)`) -/

private lemma norm_cos_pi_ge_one {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    1 ≤ ‖Complex.cos ((Real.pi : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)))‖ := by
  have hpi_z : (Real.pi : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)) =
      ((Real.pi * x : ℝ) : ℂ) + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hre : (Complex.cos ((Real.pi : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)))).re =
      Real.cos (Real.pi * x) * Real.cosh (Real.pi * y) := by
    rw [hpi_z, Complex.cos_add_mul_I,
      show Complex.cos ((Real.pi * x : ℝ) : ℂ) = (Real.cos (Real.pi * x) : ℂ) from (Complex.ofReal_cos _).symm,
      show Complex.cosh ((Real.pi * y : ℝ) : ℂ) = (Real.cosh (Real.pi * y) : ℂ) from (Complex.ofReal_cosh _).symm,
      show Complex.sin ((Real.pi * x : ℝ) : ℂ) = (Real.sin (Real.pi * x) : ℂ) from (Complex.ofReal_sin _).symm,
      show Complex.sinh ((Real.pi * y : ℝ) : ℂ) = (Real.sinh (Real.pi * y) : ℂ) from (Complex.ofReal_sinh _).symm,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero]
    ring
  have him : (Complex.cos ((Real.pi : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)))).im =
      -Real.sin (Real.pi * x) * Real.sinh (Real.pi * y) := by
    rw [hpi_z, Complex.cos_add_mul_I,
      show Complex.cos ((Real.pi * x : ℝ) : ℂ) = (Real.cos (Real.pi * x) : ℂ) from (Complex.ofReal_cos _).symm,
      show Complex.cosh ((Real.pi * y : ℝ) : ℂ) = (Real.cosh (Real.pi * y) : ℂ) from (Complex.ofReal_cosh _).symm,
      show Complex.sin ((Real.pi * x : ℝ) : ℂ) = (Real.sin (Real.pi * x) : ℂ) from (Complex.ofReal_sin _).symm,
      show Complex.sinh ((Real.pi * y : ℝ) : ℂ) = (Real.sinh (Real.pi * y) : ℂ) from (Complex.ofReal_sinh _).symm,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_sub]
    ring
  have hnorm_sq : ‖Complex.cos ((Real.pi : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)))‖ ^ 2 =
      Real.cos (Real.pi * x) ^ 2 + Real.sinh (Real.pi * y) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have hch : Real.cosh (Real.pi * y) ^ 2 = 1 + Real.sinh (Real.pi * y) ^ 2 := by
      linarith [Real.cosh_sq_sub_sinh_sq (Real.pi * y)]
    have hsc : Real.cos (Real.pi * x) ^ 2 + Real.sin (Real.pi * x) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    calc (Real.cos (Real.pi * x) * Real.cosh (Real.pi * y)) *
          (Real.cos (Real.pi * x) * Real.cosh (Real.pi * y)) +
          (-Real.sin (Real.pi * x) * Real.sinh (Real.pi * y)) *
          (-Real.sin (Real.pi * x) * Real.sinh (Real.pi * y))
        = Real.cos (Real.pi * x) ^ 2 * Real.cosh (Real.pi * y) ^ 2 +
          Real.sin (Real.pi * x) ^ 2 * Real.sinh (Real.pi * y) ^ 2 := by ring
      _ = Real.cos (Real.pi * x) ^ 2 * (1 + Real.sinh (Real.pi * y) ^ 2) +
          Real.sin (Real.pi * x) ^ 2 * Real.sinh (Real.pi * y) ^ 2 := by rw [hch]
      _ = Real.cos (Real.pi * x) ^ 2 +
          (Real.cos (Real.pi * x) ^ 2 + Real.sin (Real.pi * x) ^ 2) * Real.sinh (Real.pi * y) ^ 2 := by ring
      _ = Real.cos (Real.pi * x) ^ 2 + Real.sinh (Real.pi * y) ^ 2 := by rw [hsc, one_mul]
  have hsin_le : |Real.sin (Real.pi * x)| ≤ Real.pi * x := Real.abs_sin_le_abs.trans_eq
    (abs_of_nonneg (mul_nonneg Real.pi_pos.le hx0))
  have hsh_ge : Real.pi * y ≤ Real.sinh (Real.pi * y) := by
    have hmono : MonotoneOn (fun u : ℝ => Real.sinh u - u) (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) fun u _ => ?_
      have hd : HasDerivAt (fun s : ℝ => Real.sinh s - s) (Real.cosh u - 1) u :=
        (Real.hasDerivAt_sinh u).sub (hasDerivAt_id u)
      rw [hd.deriv]
      linarith [Real.one_le_cosh u]
    have h0 := hmono (by simp : (0 : ℝ) ∈ Ici 0) (mul_nonneg Real.pi_pos.le (hx0.trans hxy))
      (mul_nonneg Real.pi_pos.le (hx0.trans hxy))
    simp only [Real.sinh_zero, sub_zero] at h0
    linarith
  have hsin_sq : Real.sin (Real.pi * x) ^ 2 ≤ Real.sinh (Real.pi * y) ^ 2 := by
    have habs : |Real.sin (Real.pi * x)| ≤ Real.sinh (Real.pi * y) := by
      linarith [mul_le_mul_of_nonneg_left hxy Real.pi_pos.le]
    rw [← sq_abs (Real.sin (Real.pi * x))]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hge1 : 1 ≤ ‖Complex.cos ((Real.pi : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ)))‖ ^ 2 := by
    rw [hnorm_sq]
    linarith [Real.cos_sq_add_sin_sq (Real.pi * x)]
  nlinarith [norm_nonneg (Complex.cos ((Real.pi : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ))))]

private lemma xiStar_le_norm_chartB {w : ℂ} (hx0 : 0 ≤ w.re) (hxy : w.re ≤ w.im) :
    xiStar ≤ ‖chartB w‖ := by
  have hw_eq : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by apply Complex.ext <;> simp
  have hcos_ge : 1 ≤ ‖Complex.cos ((Real.pi : ℂ) * w)‖ := by
    rw [hw_eq]; exact norm_cos_pi_ge_one hx0 hxy
  have hsh_sq : ‖Complex.sinh ((Real.pi : ℂ) * chartB w)‖ ^ 2 = ‖Complex.cos ((Real.pi : ℂ) * w)‖ := by
    rw [sinh_pi_chartB, ← norm_pow, cpow_half_sq]
  have hsh_ge1 : 1 ≤ ‖Complex.sinh ((Real.pi : ℂ) * chartB w)‖ := by
    nlinarith [norm_nonneg (Complex.sinh ((Real.pi : ℂ) * chartB w))]
  have hsh_le : ‖Complex.sinh ((Real.pi : ℂ) * chartB w)‖ ≤ Real.sinh (Real.pi * ‖chartB w‖) := by
    calc ‖Complex.sinh ((Real.pi : ℂ) * chartB w)‖
        ≤ Real.sinh ‖(Real.pi : ℂ) * chartB w‖ := norm_sinh_le_sinh_norm _
      _ = Real.sinh (Real.pi * ‖chartB w‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hsh_xi : Real.sinh (Real.pi * xiStar) ≤ Real.sinh (Real.pi * ‖chartB w‖) := by
    rw [sinh_pi_mul_xiStar]; linarith
  have hmul : Real.pi * xiStar ≤ Real.pi * ‖chartB w‖ := Real.sinh_le_sinh.mp hsh_xi
  exact (mul_le_mul_iff_right₀ Real.pi_pos).mp hmul

private lemma im_chartB_nonpos {w : ℂ} (hx0 : 0 ≤ w.re) (hx1 : w.re ≤ 1 / 2)
    (hy0 : 0 ≤ w.im) (hne : w ≠ 1 / 2) : (chartB w).im ≤ 0 := by
  have hw_eq : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by apply Complex.ext <;> simp
  have hpi_z : (Real.pi : ℂ) * w =
      ((Real.pi * w.re : ℝ) : ℂ) + ((Real.pi * w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hcos_re : 0 ≤ (Complex.cos ((Real.pi : ℂ) * w)).re := by
    rw [hpi_z, Complex.cos_add_mul_I,
      show Complex.cos ((Real.pi * w.re : ℝ) : ℂ) = (Real.cos (Real.pi * w.re) : ℂ) from (Complex.ofReal_cos _).symm,
      show Complex.cosh ((Real.pi * w.im : ℝ) : ℂ) = (Real.cosh (Real.pi * w.im) : ℂ) from (Complex.ofReal_cosh _).symm,
      show Complex.sin ((Real.pi * w.re : ℝ) : ℂ) = (Real.sin (Real.pi * w.re) : ℂ) from (Complex.ofReal_sin _).symm,
      show Complex.sinh ((Real.pi * w.im : ℝ) : ℂ) = (Real.sinh (Real.pi * w.im) : ℂ) from (Complex.ofReal_sinh _).symm,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero]
    have hcos : 0 ≤ Real.cos (Real.pi * w.re) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have hmul := mul_nonneg hcos (Real.cosh_pos (Real.pi * w.im)).le
    linarith
  have hcos_im : (Complex.cos ((Real.pi : ℂ) * w)).im ≤ 0 := by
    rw [hpi_z, Complex.cos_add_mul_I,
      show Complex.cos ((Real.pi * w.re : ℝ) : ℂ) = (Real.cos (Real.pi * w.re) : ℂ) from (Complex.ofReal_cos _).symm,
      show Complex.cosh ((Real.pi * w.im : ℝ) : ℂ) = (Real.cosh (Real.pi * w.im) : ℂ) from (Complex.ofReal_cosh _).symm,
      show Complex.sin ((Real.pi * w.re : ℝ) : ℂ) = (Real.sin (Real.pi * w.re) : ℂ) from (Complex.ofReal_sin _).symm,
      show Complex.sinh ((Real.pi * w.im : ℝ) : ℂ) = (Real.sinh (Real.pi * w.im) : ℂ) from (Complex.ofReal_sinh _).symm,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_sub]
    have hsin : 0 ≤ Real.sin (Real.pi * w.re) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    have hsh : 0 ≤ Real.sinh (Real.pi * w.im) := Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le hy0)
    nlinarith
  set c := Complex.cos ((Real.pi : ℂ) * w)
  have hc_slit : c ∈ Complex.slitPlane := cos_pi_mem_slitPlane hx0 hx1 hne
  set s := c ^ (1 / 2 : ℂ)
  have hs_re : 0 < s.re := cpow_half_re_pos hc_slit
  have hs2_im : 2 * s.re * s.im = c.im := by
    have := congrArg Complex.im (cpow_half_sq c)
    change (s ^ 2).im = c.im at this
    rw [sq, Complex.mul_im] at this
    linarith
  have hs_im : s.im ≤ 0 := by nlinarith
  have hc1_slit : c + 1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [Complex.add_re, Complex.one_re]
    linarith
  set r := (c + 1) ^ (1 / 2 : ℂ)
  have hr_re : 0 < r.re := cpow_half_re_pos hc1_slit
  have hr2_im : 2 * r.re * r.im = c.im := by
    have := congrArg Complex.im (cpow_half_sq (c + 1))
    change (r ^ 2).im = (c + 1).im at this
    rw [sq, Complex.mul_im, Complex.add_im, Complex.one_im, add_zero] at this
    linarith
  have hr_im : r.im ≤ 0 := by nlinarith
  set u := s + r
  have hu_re : 0 < u.re := by show 0 < s.re + r.re; linarith
  have hu_im : u.im ≤ 0 := by show s.im + r.im ≤ 0; linarith
  have hu_ne : u ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hu_re; exact lt_irrefl 0 hu_re
  have hu_arg : u.arg ≤ 0 := by
    have harg_lt : |u.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu_re)
    have hsin : Real.sin u.arg ≤ 0 := by
      rw [Complex.sin_arg]
      exact div_nonpos_of_nonpos_of_nonneg hu_im (norm_nonneg u)
    by_contra hpos
    push Not at hpos
    have hsin_pos : 0 < Real.sin u.arg :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [(abs_lt.mp harg_lt).2, Real.pi_pos])
    linarith
  unfold chartB arsinhC
  have hs2_eq : s ^ 2 + 1 = c + 1 := by rw [cpow_half_sq]
  rw [show s + (s ^ 2 + 1) ^ (1 / 2 : ℂ) = u by dsimp [u, r, s]; rw [hs2_eq]]
  rw [show (Real.pi : ℂ)⁻¹ = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.im_ofReal_mul, Complex.log_im]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr Real.pi_pos).le hu_arg

private lemma log_chartB_div_xiStar_quadrant {w : ℂ} (hx0 : 0 ≤ w.re) (hx1 : w.re ≤ 1 / 2)
    (hxy : w.re ≤ w.im) (hne : w ≠ 1 / 2) :
    0 ≤ (Complex.log (chartB w / (xiStar : ℂ))).re ∧
      (Complex.log (chartB w / (xiStar : ℂ))).im ≤ 0 := by
  have hb_re : 0 < (chartB w).re := re_chartB_pos hx0 hx1 hne
  have hb_im : (chartB w).im ≤ 0 := im_chartB_nonpos hx0 hx1 (hx0.trans hxy) hne
  have hnorm_ge : xiStar ≤ ‖chartB w‖ := xiStar_le_norm_chartB hx0 hxy
  have hre : 0 ≤ (Complex.log (chartB w / (xiStar : ℂ))).re := by
    rw [Complex.log_re, norm_div, Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le]
    exact Real.log_nonneg ((one_le_div xiStar_pos).mpr hnorm_ge)
  have him : (Complex.log (chartB w / (xiStar : ℂ))).im ≤ 0 := by
    rw [log_div_of_re_pos hb_re xiStar_pos, Complex.sub_im, ← Complex.ofReal_log xiStar_pos.le,
      Complex.ofReal_im, sub_zero, Complex.log_im]
    have harg_lt : |(chartB w).arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb_re)
    have hb_ne : chartB w ≠ 0 := fun h0 => by
      rw [h0, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
    have hsin : Real.sin (chartB w).arg ≤ 0 := by
      rw [Complex.sin_arg]
      exact div_nonpos_of_nonpos_of_nonneg hb_im (norm_nonneg _)
    by_contra hpos
    push Not at hpos
    have hsin_pos : 0 < Real.sin (chartB w).arg :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [(abs_lt.mp harg_lt).2, Real.pi_pos])
    linarith
  exact ⟨hre, him⟩

/-! ### Section 4: Monotone descent along the three segments of `γ_+` -/

private lemma j10P_eq (δ : ℝ) :
    j10P δ = ((δ / 2 : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ) := by
  unfold j10P j10YDelta
  rw [show Complex.I * ((Real.pi / 3 : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I by ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

private lemma j10YDelta_bounds {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ j10Delta0) :
    δ / 2 < j10YDelta δ ∧ j10YDelta δ < 1 / 2 := by
  unfold j10YDelta
  have h1 : 1 < √3 := by
    have : (1 : ℝ) ^ 2 < (√3) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 3]
  have h2 : √3 < 2 := by
    have : (√3) ^ 2 < (2 : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 3]
  have hδ72 : δ ≤ 1 / 72 := hδ_le
  constructor <;> nlinarith

private lemma j10H_seg1_antitone {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ j10Delta0) :
    AntitoneOn (fun x : ℝ => j10H ((x : ℂ) + Complex.I * (j10YDelta δ : ℂ)))
      (Icc (δ / 2) (j10YDelta δ)) := by
  obtain ⟨hxy, hy_half⟩ := j10YDelta_bounds hδ_pos hδ_le
  let y := j10YDelta δ
  let f : ℝ → ℝ := fun x => j10H ((x : ℂ) + Complex.I * (y : ℂ))
  refine antitoneOn_of_deriv_nonpos (convex_Icc (δ / 2) y) ?_ ?_ ?_
  · intro x hx
    have h0 : 0 < x := by linarith [hx.1]
    have h1 : x < 1 / 2 := by linarith [hx.2]
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1
      ((x : ℂ) + Complex.I * (y : ℂ)) (by simpa using h0) (by simpa using h1)
    have hline : ContinuousAt (fun s : ℝ => (s : ℂ) + Complex.I * (y : ℂ)) x := by fun_prop
    exact (Complex.continuous_re.continuousAt.comp
      (hd.continuousAt.comp (f := fun s : ℝ => (s : ℂ) + Complex.I * (y : ℂ)) hline)).continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have h0 : 0 < x := by linarith [hx.1]
    have h1 : x < 1 / 2 := by linarith [hx.2]
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1
      ((x : ℂ) + Complex.I * (y : ℂ)) (by simpa using h0) (by simpa using h1)
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) + Complex.I * (y : ℂ)) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (Complex.I * (y : ℂ))
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd.comp x hline)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have h0 : 0 < x := by linarith [hx.1]
    have h1 : x < 1 / 2 := by linarith [hx.2]
    set z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1
      z (by simp [z]; exact h0) (by simp [z]; linarith)
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) + Complex.I * (y : ℂ)) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (Complex.I * (y : ℂ))
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd.comp x hline)
    have hf_d : HasDerivAt f (Complex.reCLM (2 * Complex.log (chartB z / (xiStar : ℂ)) *
        deriv chartOmega z * 1)) x := hre
    rw [hf_d.deriv]
    simp only [Complex.reCLM_apply, mul_one]
    have hne : z ≠ 1 / 2 := fun h0' => by
      have := congrArg Complex.im h0'; simp [z] at this; linarith
    obtain ⟨hA, hB'⟩ := log_chartB_div_xiStar_quadrant (by simp [z]; exact h0.le)
      (by simp [z]; linarith) (by simp [z]; exact hx.2.le) hne
    have hJ7Q := lemma_J7Q.1 x y h0.le h1.le (by linarith)
    set L := Complex.log (chartB z / (xiStar : ℂ))
    set Om' := deriv chartOmega z
    have hre_eq : (2 * L * Om').re = -2 * (L.re * (-Om'.re) + (-L.im) * (-Om'.im)) := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
      ring
    rw [hre_eq]
    have hAC : 0 ≤ L.re * (-Om'.re) := mul_nonneg hA (by linarith [hJ7Q.1])
    have hBD : 0 ≤ (-L.im) * (-Om'.im) := mul_nonneg (by linarith) (by linarith [hJ7Q.2.1])
    linarith

private lemma j10H_seg2_antitone {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ j10Delta0) :
    AntitoneOn (fun s : ℝ => j10H ((s : ℂ) * (1 + Complex.I))) (Icc (j10YDelta δ) (1 / 2)) := by
  obtain ⟨hxy, hy_half⟩ := j10YDelta_bounds hδ_pos hδ_le
  have hy_pos : 0 < j10YDelta δ := by linarith
  let w : ℝ → ℂ := fun s => (s : ℂ) * (1 + Complex.I)
  refine antitoneOn_of_deriv_nonpos (convex_Icc (j10YDelta δ) (1 / 2)) ?_ ?_ ?_
  · intro s hs
    have h0 : 0 ≤ (w s).re := by dsimp [w]; simp; linarith [hs.1]
    have h1 : (w s).re ≤ 1 / 2 := by dsimp [w]; simp; linarith [hs.2]
    have hne : w s ≠ 1 / 2 := fun h0' => by
      have := congrArg Complex.im h0'; simp [w] at this; linarith [hs.1]
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.2
      (w s) h0 h1 hne
    have hcont_w : ContinuousAt w s := by dsimp [w]; fun_prop
    have hmaps : MapsTo w (Icc (j10YDelta δ) (1 / 2)) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2} :=
      fun u hu => ⟨by dsimp [w]; simp; linarith [hu.1], by dsimp [w]; simp; linarith [hu.2]⟩
    have hcw := hd.continuousWithinAt.comp (hcont_w.continuousWithinAt (s := Icc (j10YDelta δ) (1 / 2))) hmaps
    exact (Complex.continuous_re.continuousAt.comp_continuousWithinAt hcw).mono (fun _ => id)
  · intro s hs
    rw [interior_Icc] at hs
    have h0 : 0 < (w s).re := by dsimp [w]; simp; linarith [hs.1]
    have h1 : (w s).re < 1 / 2 := by dsimp [w]; simp; linarith [hs.2]
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1 (w s) h0 h1
    have hline : HasDerivAt w (1 + Complex.I) s := by
      simpa [w] using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (1 + Complex.I)
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hd.comp s hline)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have h0 : 0 < (w s).re := by dsimp [w]; simp; linarith [hs.1]
    have h1 : (w s).re < 1 / 2 := by dsimp [w]; simp; linarith [hs.2]
    have hd := (lemma_S5_deriv (b := (xiStar : ℂ)) (by simpa using xiStar_pos)).2.1 (w s) h0 h1
    have hline : HasDerivAt w (1 + Complex.I) s := by
      simpa [w] using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (1 + Complex.I)
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hd.comp s hline)
    have hf_d : HasDerivAt (fun u : ℝ => j10H ((u : ℂ) * (1 + Complex.I)))
        (Complex.reCLM (2 * Complex.log (chartB (w s) / (xiStar : ℂ)) *
          deriv chartOmega (w s) * (1 + Complex.I))) s := hre
    rw [hf_d.deriv]
    simp only [Complex.reCLM_apply]
    have hne : w s ≠ 1 / 2 := fun h0' => by
      have := congrArg Complex.im h0'; simp [w] at this; linarith [hs.1]
    have hw_re : (w s).re = s := by dsimp [w]; simp
    have hw_im : (w s).im = s := by dsimp [w]; simp
    obtain ⟨hA, hB'⟩ := log_chartB_div_xiStar_quadrant (by rw [hw_re]; linarith [hs.1])
      (by rw [hw_re]; exact hs.2.le) (by rw [hw_re, hw_im]) hne
    have hw_eq : w s = (s : ℂ) + Complex.I * (s : ℂ) := by apply Complex.ext <;> simp [w]
    have hJ7Q := lemma_J7Q.1 s s (by linarith [hs.1]) hs.2.le (by linarith [hs.1])
    rw [← hw_eq] at hJ7Q
    set L := Complex.log (chartB (w s) / (xiStar : ℂ))
    set Om' := deriv chartOmega (w s)
    have hre_eq : (2 * L * Om' * (1 + Complex.I)).re =
        -2 * (L.re * ((-Om'.re) - (-Om'.im)) + (-L.im) * ((-Om'.re) + (-Om'.im))) := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        Complex.re_ofNat, Complex.im_ofNat]
      ring
    rw [hre_eq]
    have hCD : 0 ≤ (-Om'.re) - (-Om'.im) := by linarith [hJ7Q.2.2.2]
    have hCpD : 0 ≤ (-Om'.re) + (-Om'.im) := by linarith [hJ7Q.1, hJ7Q.2.2.1]
    have h1' : 0 ≤ L.re * ((-Om'.re) - (-Om'.im)) := mul_nonneg hA hCD
    have h2' : 0 ≤ (-L.im) * ((-Om'.re) + (-Om'.im)) := mul_nonneg (by linarith) hCpD
    linarith

/-! ### Section 5: Geometric properties of `γ_+` and `γ_-`, and Headline Theorem (Lemma J10) -/

private lemma j10GammaPlus_mem_upperLeftHalfStrip {δ T₀ t : ℝ}
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ j10Delta0) (hT₀ : 1 / 2 ≤ T₀) (ht : t ∈ Icc 0 3) :
    0 ≤ (j10GammaPlus δ T₀ t).re ∧ (j10GammaPlus δ T₀ t).re ≤ 1 / 2 ∧
      j10YDelta δ ≤ (j10GammaPlus δ T₀ t).im ∧ (j10GammaPlus δ T₀ t).im ≤ T₀ := by
  obtain ⟨hxy, hy_half⟩ := j10YDelta_bounds hδ_pos hδ_le
  have hy_pos : 0 < j10YDelta δ := by linarith
  unfold j10GammaPlus
  by_cases ht1 : t ≤ 1
  · simp only [ht1, ↓reduceIte, j10P_eq]
    have hre : (((1 - t : ℝ) : ℂ) * (((δ / 2 : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ)) +
        (t : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I))).re =
        (1 - t) * (δ / 2) + t * j10YDelta δ := by
      simp [Complex.add_re, Complex.mul_re]
    have him : (((1 - t : ℝ) : ℂ) * (((δ / 2 : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ)) +
        (t : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I))).im = j10YDelta δ := by
      simp [Complex.add_im, Complex.mul_im]; ring
    rw [hre, him]
    refine ⟨?_, ?_, le_rfl, hy_half.le.trans hT₀⟩
    · nlinarith [ht.1]
    · nlinarith [ht.1]
  · push Not at ht1
    by_cases ht2 : t ≤ 2
    · simp only [ht1.not_ge, ↓reduceIte, ht2]
      have hre : (((2 - t : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
          ((t - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I))).re =
          (2 - t) * j10YDelta δ + (t - 1) * (1 / 2) := by
        simp [Complex.add_re, Complex.mul_re]
      have him : (((2 - t : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
          ((t - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I))).im =
          (2 - t) * j10YDelta δ + (t - 1) * (1 / 2) := by
        simp [Complex.add_im, Complex.mul_im]
      rw [hre, him]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [ht1.le]
    · push Not at ht2
      simp only [ht1.not_ge, ht2.not_ge, ↓reduceIte]
      have hre : ((1 / 2 : ℂ) + Complex.I * ((((3 - t) * (1 / 2) + (t - 2) * T₀ : ℝ) : ℂ))).re =
          1 / 2 := by simp
      have him : ((1 / 2 : ℂ) + Complex.I * ((((3 - t) * (1 / 2) + (t - 2) * T₀ : ℝ) : ℂ))).im =
          (3 - t) * (1 / 2) + (t - 2) * T₀ := by simp
      rw [hre, him]
      refine ⟨by norm_num, le_rfl, ?_, ?_⟩
      · nlinarith [ht2.le, ht.2]
      · nlinarith [ht2.le, ht.2]

private lemma j10GammaPlus_continuousOn (δ T₀ : ℝ) : ContinuousOn (j10GammaPlus δ T₀) (Icc 0 3) := by
  have hcont_all : Continuous (j10GammaPlus δ T₀) := by
    let g1 : ℝ → ℂ := fun t =>
      ((1 - t : ℝ) : ℂ) * j10P δ + (t : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I))
    let g2 : ℝ → ℂ := fun t =>
      ((2 - t : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
        ((t - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I))
    let g3 : ℝ → ℂ := fun t =>
      (1 / 2 : ℂ) + Complex.I * ((((3 - t) * (1 / 2) + (t - 2) * T₀ : ℝ) : ℂ))
    have h23 : Continuous (fun t => if t ≤ 2 then g2 t else g3 t) := by
      refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const fun a ha => ?_
      rw [ha]
      dsimp [g2, g3]
      apply Complex.ext <;> simp <;> norm_num
    have h123 : Continuous (fun t => if t ≤ 1 then g1 t else if t ≤ 2 then g2 t else g3 t) := by
      refine Continuous.if_le (by fun_prop) h23 continuous_id continuous_const fun a ha => ?_
      rw [ha]
      dsimp [g1, g2]
      apply Complex.ext <;> simp <;> ring
    exact h123
  exact hcont_all.continuousOn

private lemma eVariationOn_j10GammaPlus_lt_top (δ T₀ : ℝ) :
    eVariationOn (j10GammaPlus δ T₀) (Icc 0 3) < ⊤ := by
  let v₁ : ℂ := (j10YDelta δ : ℂ) * (1 + Complex.I) - j10P δ
  let v₂ : ℂ := (1 / 2 : ℂ) * (1 + Complex.I) - (j10YDelta δ : ℂ) * (1 + Complex.I)
  let v₃ : ℂ := Complex.I * ((T₀ - 1 / 2 : ℝ) : ℂ)
  let g1 : ℝ → ℂ := fun s =>
    ((1 - s : ℝ) : ℂ) * j10P δ + (s : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I))
  let g2 : ℝ → ℂ := fun s =>
    ((2 - s : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
      ((s - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I))
  let g3 : ℝ → ℂ := fun s =>
    (1 / 2 : ℂ) + Complex.I * ((((3 - s) * (1 / 2) + (s - 2) * T₀ : ℝ) : ℂ))
  have hg1 : ∀ t, HasDerivAt g1 v₁ t := fun t => by
    have h_a : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ) * j10P δ) (-j10P δ) t := by
      have hs : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      exact (hs.ofReal_comp.mul_const (j10P δ)).congr_deriv (by simp)
    have h_b : HasDerivAt (fun s : ℝ => (s : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)))
        ((j10YDelta δ : ℂ) * (1 + Complex.I)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const
        ((j10YDelta δ : ℂ) * (1 + Complex.I))
    exact (h_a.add h_b).congr_deriv (by dsimp [v₁]; ring)
  have hg2 : ∀ t, HasDerivAt g2 v₂ t := fun t => by
    have h_a : HasDerivAt (fun s : ℝ => ((2 - s : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)))
        (-((j10YDelta δ : ℂ) * (1 + Complex.I))) t := by
      have hs : HasDerivAt (fun s : ℝ => 2 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (2 : ℝ)
      exact (hs.ofReal_comp.mul_const ((j10YDelta δ : ℂ) * (1 + Complex.I))).congr_deriv
        (by simp)
    have h_b : HasDerivAt (fun s : ℝ => ((s - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I)))
        ((1 / 2 : ℂ) * (1 + Complex.I)) t := by
      have hs : HasDerivAt (fun s : ℝ => s - 1) 1 t := by
        simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
      exact (hs.ofReal_comp.mul_const ((1 / 2 : ℂ) * (1 + Complex.I))).congr_deriv (by simp)
    exact (h_a.add h_b).congr_deriv (by dsimp [v₂]; ring)
  have hg3 : ∀ t, HasDerivAt g3 v₃ t := fun t => by
    have hs : HasDerivAt (fun s : ℝ => (3 - s) * (1 / 2) + (s - 2) * T₀) (T₀ - 1 / 2) t := by
      have h1' := ((hasDerivAt_id t).const_sub (3 : ℝ)).mul_const (1 / 2 : ℝ)
      have h2' := ((hasDerivAt_id t).sub_const (2 : ℝ)).mul_const T₀
      exact (h1'.add h2').congr_deriv (by ring)
    exact ((hs.ofReal_comp.const_mul Complex.I).const_add (1 / 2 : ℂ)).congr_deriv rfl
  have h1 : eVariationOn (j10GammaPlus δ T₀) (Icc 0 1) ≤ ENNReal.ofReal (‖v₁‖ * (1 - 0)) := by
    have hcongr : EqOn (j10GammaPlus δ T₀) g1 (Icc 0 1) := fun s hs => by
      unfold j10GammaPlus; simp only [hs.2, ↓reduceIte]; rfl
    rw [eVariationOn.eq_of_eqOn hcongr]
    exact StripBand.eVariationOn_le_of_hasDerivAt_le (by norm_num) (norm_nonneg v₁)
      (fun t _ => hg1 t) (fun _ _ => le_rfl)
  have h2 : eVariationOn (j10GammaPlus δ T₀) (Icc 1 2) ≤ ENNReal.ofReal (‖v₂‖ * (2 - 1)) := by
    have hcongr : EqOn (j10GammaPlus δ T₀) g2 (Icc 1 2) := fun s hs => by
      rcases eq_or_lt_of_le hs.1 with rfl | hs1
      · unfold j10GammaPlus; dsimp [g2]; simp; ring
      · unfold j10GammaPlus; dsimp [g2]; simp [hs1.not_ge, hs.2]
    rw [eVariationOn.eq_of_eqOn hcongr]
    exact StripBand.eVariationOn_le_of_hasDerivAt_le (by norm_num) (norm_nonneg v₂)
      (fun t _ => hg2 t) (fun _ _ => le_rfl)
  have h3 : eVariationOn (j10GammaPlus δ T₀) (Icc 2 3) ≤ ENNReal.ofReal (‖v₃‖ * (3 - 2)) := by
    have hcongr : EqOn (j10GammaPlus δ T₀) g3 (Icc 2 3) := fun s hs => by
      rcases eq_or_lt_of_le hs.1 with rfl | hs2
      · unfold j10GammaPlus; dsimp [g3]; simp; apply Complex.ext <;> simp <;> norm_num
      · unfold j10GammaPlus; dsimp [g3]; simp [show ¬ s ≤ 1 by linarith, hs2.not_ge]
    rw [eVariationOn.eq_of_eqOn hcongr]
    exact StripBand.eVariationOn_le_of_hasDerivAt_le (by norm_num) (norm_nonneg v₃)
      (fun t _ => hg3 t) (fun _ _ => le_rfl)
  have h12 : eVariationOn (j10GammaPlus δ T₀) (Icc 0 2) =
      eVariationOn (j10GammaPlus δ T₀) (Icc 0 1) + eVariationOn (j10GammaPlus δ T₀) (Icc 1 2) := by
    have hsp := eVariationOn.Icc_add_Icc (j10GammaPlus δ T₀) (s := Icc 0 2) (a := 0) (b := 1) (c := 2)
      (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    have hI0 : Icc (0 : ℝ) 2 ∩ Icc 0 2 = Icc 0 2 := inter_self _
    have hI1 : Icc (0 : ℝ) 2 ∩ Icc 0 1 = Icc 0 1 := inter_eq_right.mpr (Icc_subset_Icc_right (by norm_num))
    have hI2 : Icc (0 : ℝ) 2 ∩ Icc 1 2 = Icc 1 2 := inter_eq_right.mpr (Icc_subset_Icc_left (by norm_num))
    rw [hI0, hI1, hI2] at hsp
    exact hsp.symm
  have h123 : eVariationOn (j10GammaPlus δ T₀) (Icc 0 3) =
      eVariationOn (j10GammaPlus δ T₀) (Icc 0 2) + eVariationOn (j10GammaPlus δ T₀) (Icc 2 3) := by
    have hsp := eVariationOn.Icc_add_Icc (j10GammaPlus δ T₀) (s := Icc 0 3) (a := 0) (b := 2) (c := 3)
      (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    have hI0 : Icc (0 : ℝ) 3 ∩ Icc 0 3 = Icc 0 3 := inter_self _
    have hI1 : Icc (0 : ℝ) 3 ∩ Icc 0 2 = Icc 0 2 := inter_eq_right.mpr (Icc_subset_Icc_right (by norm_num))
    have hI2 : Icc (0 : ℝ) 3 ∩ Icc 2 3 = Icc 2 3 := inter_eq_right.mpr (Icc_subset_Icc_left (by norm_num))
    rw [hI0, hI1, hI2] at hsp
    exact hsp.symm
  rw [h123, h12]
  have hf1 : eVariationOn (j10GammaPlus δ T₀) (Icc 0 1) < ⊤ :=
    lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have hf2 : eVariationOn (j10GammaPlus δ T₀) (Icc 1 2) < ⊤ :=
    lt_of_le_of_lt h2 ENNReal.ofReal_lt_top
  have hf3 : eVariationOn (j10GammaPlus δ T₀) (Icc 2 3) < ⊤ :=
    lt_of_le_of_lt h3 ENNReal.ofReal_lt_top
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hf1, hf2⟩, hf3⟩

private lemma eVariationOn_comp_conj (f : ℝ → ℂ) (S : Set ℝ) :
    eVariationOn (fun t => starRingEnd ℂ (f t)) S = eVariationOn f S := by
  simp only [eVariationOn, edist_dist, Complex.dist_eq, ← map_sub, Complex.norm_conj]

private lemma eVariationOn_chartOmega_comp_lt_top {δ T₀ M : ℝ} (hM : 0 ≤ M)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ j10Delta0) (hT₀ : 1 / 2 ≤ T₀)
    (hbd : ∀ t ∈ Icc (0 : ℝ) 3, ‖deriv chartOmega (j10GammaPlus δ T₀ t)‖ ≤ M) :
    eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 3) < ⊤ := by
  have h_om_d : ∀ t ∈ Icc (0 : ℝ) 3,
      HasDerivAt chartOmega (deriv chartOmega (j10GammaPlus δ T₀ t)) (j10GammaPlus δ T₀ t) := by
    intro t ht
    have hm := j10GammaPlus_mem_upperLeftHalfStrip hδ_pos hδ_le hT₀ ht
    exact (analyticAt_chartOmega hm.1 (by linarith [hm.2.1])).differentiableAt.hasDerivAt
  let v₁ : ℂ := (j10YDelta δ : ℂ) * (1 + Complex.I) - j10P δ
  let v₂ : ℂ := (1 / 2 : ℂ) * (1 + Complex.I) - (j10YDelta δ : ℂ) * (1 + Complex.I)
  let v₃ : ℂ := Complex.I * ((T₀ - 1 / 2 : ℝ) : ℂ)
  let g1 : ℝ → ℂ := fun s =>
    ((1 - s : ℝ) : ℂ) * j10P δ + (s : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I))
  let g2 : ℝ → ℂ := fun s =>
    ((2 - s : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
      ((s - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I))
  let g3 : ℝ → ℂ := fun s =>
    (1 / 2 : ℂ) + Complex.I * ((((3 - s) * (1 / 2) + (s - 2) * T₀ : ℝ) : ℂ))
  have hg1 : ∀ t, HasDerivAt g1 v₁ t := fun t => by
    have h_a : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ) * j10P δ) (-j10P δ) t := by
      have hs : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      exact (hs.ofReal_comp.mul_const (j10P δ)).congr_deriv (by simp)
    have h_b : HasDerivAt (fun s : ℝ => (s : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)))
        ((j10YDelta δ : ℂ) * (1 + Complex.I)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const
        ((j10YDelta δ : ℂ) * (1 + Complex.I))
    exact (h_a.add h_b).congr_deriv (by dsimp [v₁]; ring)
  have hg2 : ∀ t, HasDerivAt g2 v₂ t := fun t => by
    have h_a : HasDerivAt (fun s : ℝ => ((2 - s : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)))
        (-((j10YDelta δ : ℂ) * (1 + Complex.I))) t := by
      have hs : HasDerivAt (fun s : ℝ => 2 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (2 : ℝ)
      exact (hs.ofReal_comp.mul_const ((j10YDelta δ : ℂ) * (1 + Complex.I))).congr_deriv
        (by simp)
    have h_b : HasDerivAt (fun s : ℝ => ((s - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I)))
        ((1 / 2 : ℂ) * (1 + Complex.I)) t := by
      have hs : HasDerivAt (fun s : ℝ => s - 1) 1 t := by
        simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
      exact (hs.ofReal_comp.mul_const ((1 / 2 : ℂ) * (1 + Complex.I))).congr_deriv (by simp)
    exact (h_a.add h_b).congr_deriv (by dsimp [v₂]; ring)
  have hg3 : ∀ t, HasDerivAt g3 v₃ t := fun t => by
    have hs : HasDerivAt (fun s : ℝ => (3 - s) * (1 / 2) + (s - 2) * T₀) (T₀ - 1 / 2) t := by
      have h1' := ((hasDerivAt_id t).const_sub (3 : ℝ)).mul_const (1 / 2 : ℝ)
      have h2' := ((hasDerivAt_id t).sub_const (2 : ℝ)).mul_const T₀
      exact (h1'.add h2').congr_deriv (by ring)
    exact ((hs.ofReal_comp.const_mul Complex.I).const_add (1 / 2 : ℂ)).congr_deriv rfl
  have h1 : eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 1) ≤
      ENNReal.ofReal (M * ‖v₁‖ * (1 - 0)) := by
    have hcongr1 : EqOn (j10GammaPlus δ T₀) g1 (Icc 0 1) := fun s hs => by
      unfold j10GammaPlus; simp only [hs.2, ↓reduceIte]; rfl
    have hcongr : EqOn (chartOmega ∘ j10GammaPlus δ T₀) (chartOmega ∘ g1) (Icc 0 1) :=
      fun s hs => by simp [hcongr1 hs]
    rw [eVariationOn.eq_of_eqOn hcongr]
    refine StripBand.eVariationOn_le_of_hasDerivAt_le (by norm_num) (by positivity)
      (f' := fun t => deriv chartOmega (g1 t) * v₁) (fun t ht => ?_) (fun t ht => ?_)
    · have h_eq : g1 t = j10GammaPlus δ T₀ t := (hcongr1 ht).symm
      have hom : HasDerivAt chartOmega (deriv chartOmega (g1 t)) (g1 t) := by
        rw [h_eq]; exact h_om_d t ⟨ht.1, ht.2.trans (by norm_num)⟩
      exact hom.comp t (hg1 t)
    · rw [norm_mul, ← hcongr1 ht]
      exact mul_le_mul_of_nonneg_right (hbd t ⟨ht.1, ht.2.trans (by norm_num)⟩) (norm_nonneg _)
  have h2 : eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 1 2) ≤
      ENNReal.ofReal (M * ‖v₂‖ * (2 - 1)) := by
    have hcongr1 : EqOn (j10GammaPlus δ T₀) g2 (Icc 1 2) := fun s hs => by
      rcases eq_or_lt_of_le hs.1 with rfl | hs1
      · unfold j10GammaPlus; dsimp [g2]; simp; ring
      · unfold j10GammaPlus; dsimp [g2]; simp [hs1.not_ge, hs.2]
    have hcongr : EqOn (chartOmega ∘ j10GammaPlus δ T₀) (chartOmega ∘ g2) (Icc 1 2) :=
      fun s hs => by simp [hcongr1 hs]
    rw [eVariationOn.eq_of_eqOn hcongr]
    refine StripBand.eVariationOn_le_of_hasDerivAt_le (by norm_num) (by positivity)
      (f' := fun t => deriv chartOmega (g2 t) * v₂) (fun t ht => ?_) (fun t ht => ?_)
    · have h_eq : g2 t = j10GammaPlus δ T₀ t := (hcongr1 ht).symm
      have hom : HasDerivAt chartOmega (deriv chartOmega (g2 t)) (g2 t) := by
        rw [h_eq]; exact h_om_d t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact hom.comp t (hg2 t)
    · rw [norm_mul, ← hcongr1 ht]
      exact mul_le_mul_of_nonneg_right (hbd t ⟨by linarith [ht.1], by linarith [ht.2]⟩) (norm_nonneg _)
  have h3 : eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 2 3) ≤
      ENNReal.ofReal (M * ‖v₃‖ * (3 - 2)) := by
    have hcongr1 : EqOn (j10GammaPlus δ T₀) g3 (Icc 2 3) := fun s hs => by
      rcases eq_or_lt_of_le hs.1 with rfl | hs2
      · unfold j10GammaPlus; dsimp [g3]; simp; apply Complex.ext <;> simp <;> norm_num
      · unfold j10GammaPlus; dsimp [g3]; simp [show ¬ s ≤ 1 by linarith, hs2.not_ge]
    have hcongr : EqOn (chartOmega ∘ j10GammaPlus δ T₀) (chartOmega ∘ g3) (Icc 2 3) :=
      fun s hs => by simp [hcongr1 hs]
    rw [eVariationOn.eq_of_eqOn hcongr]
    refine StripBand.eVariationOn_le_of_hasDerivAt_le (by norm_num) (by positivity)
      (f' := fun t => deriv chartOmega (g3 t) * v₃) (fun t ht => ?_) (fun t ht => ?_)
    · have h_eq : g3 t = j10GammaPlus δ T₀ t := (hcongr1 ht).symm
      have hom : HasDerivAt chartOmega (deriv chartOmega (g3 t)) (g3 t) := by
        rw [h_eq]; exact h_om_d t ⟨by linarith [ht.1], ht.2⟩
      exact hom.comp t (hg3 t)
    · rw [norm_mul, ← hcongr1 ht]
      exact mul_le_mul_of_nonneg_right (hbd t ⟨by linarith [ht.1], ht.2⟩) (norm_nonneg _)
  have h12 : eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 2) =
      eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 1) +
        eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 1 2) := by
    have hsp := eVariationOn.Icc_add_Icc (chartOmega ∘ j10GammaPlus δ T₀) (s := Icc 0 2)
      (a := 0) (b := 1) (c := 2) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    have hI0 : Icc (0 : ℝ) 2 ∩ Icc 0 2 = Icc 0 2 := inter_self _
    have hI1 : Icc (0 : ℝ) 2 ∩ Icc 0 1 = Icc 0 1 := inter_eq_right.mpr (Icc_subset_Icc_right (by norm_num))
    have hI2 : Icc (0 : ℝ) 2 ∩ Icc 1 2 = Icc 1 2 := inter_eq_right.mpr (Icc_subset_Icc_left (by norm_num))
    rw [hI0, hI1, hI2] at hsp
    exact hsp.symm
  have h123 : eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 3) =
      eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 2) +
        eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 2 3) := by
    have hsp := eVariationOn.Icc_add_Icc (chartOmega ∘ j10GammaPlus δ T₀) (s := Icc 0 3)
      (a := 0) (b := 2) (c := 3) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    have hI0 : Icc (0 : ℝ) 3 ∩ Icc 0 3 = Icc 0 3 := inter_self _
    have hI1 : Icc (0 : ℝ) 3 ∩ Icc 0 2 = Icc 0 2 := inter_eq_right.mpr (Icc_subset_Icc_right (by norm_num))
    have hI2 : Icc (0 : ℝ) 3 ∩ Icc 2 3 = Icc 2 3 := inter_eq_right.mpr (Icc_subset_Icc_left (by norm_num))
    rw [hI0, hI1, hI2] at hsp
    exact hsp.symm
  rw [h123, h12]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨lt_of_le_of_lt h1 ENNReal.ofReal_lt_top, lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩,
    lt_of_le_of_lt h3 ENNReal.ofReal_lt_top⟩

/-- **Lemma J10 (`vlo:J10escape`, `lower_o1_two_edge.tex`, lines 932–1006)**:
Explicit three-segment compact escape contour `γ_+` (`p → y_δ(1 + i) → ½(1 + i) → ½ + i T₀`,
parameterized by `j10GammaPlus δ T₀` on `[0, 3]`) and its reflection `γ_- = conj ∘ γ_+`
(`j10GammaMinus δ T₀`), valid for every `0 < δ ≤ δ₀ = 1/72` and every `T₀ ≥ 1/2` (in particular
for every sufficiently large `T₀` as in §J7):
1. `γ_+` stays in the closed upper left half-strip `{0 ≤ Re ζ ≤ 1/2, Im ζ ≥ 0}` (with endpoints
   `γ_+(0) = p(δ)`, `γ_+(1) = y_δ(1 + i)`, `γ_+(2) = (1/2)(1 + i)`, `γ_+(3) = 1/2 + i T₀`) and
   `γ_-` stays in the closed lower left half-strip `{0 ≤ Re ζ ≤ 1/2, Im ζ ≤ 0}`.
2. Along both `γ_+` and `γ_-`, `H ≤ H(p) ≤ -(π² / 36) δ³`, and hence `H ≤ -ε` for
   `ε := -H(p) / 2 ≥ (π² / 72) δ³ > 0`.
3. Both curves are continuous with finite length (in `ζ` and in `ω`), bounded `|ω'|`, avoid
   `ω = 0` uniformly (`c ≤ ‖ω(γ_± t)‖` for some `c > 0`), and stay in `Re ω ≥ 0`. -/
theorem lemma_J10_compact_escape {δ T₀ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ j10Delta0)
    (hT₀ : 1 / 2 ≤ T₀) :
    let ε : ℝ := -j10H (j10P δ) / 2
    -- Endpoint matching
    j10GammaPlus δ T₀ 0 = j10P δ ∧
    j10GammaPlus δ T₀ 1 = (j10YDelta δ : ℂ) * (1 + Complex.I) ∧
    j10GammaPlus δ T₀ 2 = (1 / 2 : ℂ) * (1 + Complex.I) ∧
    j10GammaPlus δ T₀ 3 = (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ) ∧
    -- Margin inequalities
    j10H (j10P δ) ≤ -(Real.pi ^ 2 / 36) * δ ^ 3 ∧
    (Real.pi ^ 2 / 72) * δ ^ 3 ≤ ε ∧ 0 < ε ∧
    -- Closed half-strip containment and H bounds along γ_+ and γ_-
    (∀ t ∈ Icc (0 : ℝ) 3,
      0 ≤ (j10GammaPlus δ T₀ t).re ∧ (j10GammaPlus δ T₀ t).re ≤ 1 / 2 ∧
        0 ≤ (j10GammaPlus δ T₀ t).im ∧
      0 ≤ (j10GammaMinus δ T₀ t).re ∧ (j10GammaMinus δ T₀ t).re ≤ 1 / 2 ∧
        (j10GammaMinus δ T₀ t).im ≤ 0 ∧
      j10H (j10GammaPlus δ T₀ t) ≤ j10H (j10P δ) ∧
      j10H (j10GammaPlus δ T₀ t) ≤ -ε ∧
      j10H (j10GammaMinus δ T₀ t) ≤ j10H (j10P δ) ∧
      j10H (j10GammaMinus δ T₀ t) ≤ -ε ∧
      0 ≤ (chartOmega (j10GammaPlus δ T₀ t)).re ∧
      0 ≤ (chartOmega (j10GammaMinus δ T₀ t)).re) ∧
    -- Continuity, finite length (in ζ and ω), bounded |ω'|, and uniform avoidance of ω = 0
    ContinuousOn (j10GammaPlus δ T₀) (Icc 0 3) ∧
    ContinuousOn (j10GammaMinus δ T₀) (Icc 0 3) ∧
    eVariationOn (j10GammaPlus δ T₀) (Icc 0 3) < ⊤ ∧
    eVariationOn (j10GammaMinus δ T₀) (Icc 0 3) < ⊤ ∧
    (∃ M > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 3,
      ‖deriv chartOmega (j10GammaPlus δ T₀ t)‖ ≤ M ∧
      ‖deriv chartOmega (j10GammaMinus δ T₀ t)‖ ≤ M) ∧
    eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 3) < ⊤ ∧
    eVariationOn (chartOmega ∘ j10GammaMinus δ T₀) (Icc 0 3) < ⊤ ∧
    (∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 3,
      c ≤ ‖chartOmega (j10GammaPlus δ T₀ t)‖ ∧
      c ≤ ‖chartOmega (j10GammaMinus δ T₀ t)‖) := by
  intro ε
  have hp_le : j10H (j10P δ) ≤ -(Real.pi ^ 2 / 36) * δ ^ 3 := j10H_p_le hδ_pos hδ_le
  have hε_ge : (Real.pi ^ 2 / 72) * δ ^ 3 ≤ ε := by dsimp [ε]; linarith
  have hε_pos : 0 < ε := lt_of_lt_of_le (by positivity [Real.pi_pos]) hε_ge
  have hseg1 := j10H_seg1_antitone hδ_pos hδ_le
  have hseg2 := j10H_seg2_antitone hδ_pos hδ_le
  have hseg3 := re_chartPhiV_midline_strictAnti
  obtain ⟨hxy, hy_half⟩ := j10YDelta_bounds hδ_pos hδ_le
  have hy_pos : 0 < j10YDelta δ := by linarith
  have hCorner1 : j10H ((j10YDelta δ : ℂ) * (1 + Complex.I)) ≤ j10H (j10P δ) := by
    have hp_mem : δ / 2 ∈ Icc (δ / 2) (j10YDelta δ) := ⟨le_rfl, hxy.le⟩
    have hy_mem : j10YDelta δ ∈ Icc (δ / 2) (j10YDelta δ) := ⟨hxy.le, le_rfl⟩
    have h1 := hseg1 hp_mem hy_mem hxy.le
    have heq1 : (j10YDelta δ : ℂ) + Complex.I * (j10YDelta δ : ℂ) =
        (j10YDelta δ : ℂ) * (1 + Complex.I) := by ring
    have heq2 : ((δ / 2 : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ) = j10P δ := (j10P_eq δ).symm
    change j10H ((j10YDelta δ : ℂ) + Complex.I * (j10YDelta δ : ℂ)) ≤
      j10H (((δ / 2 : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ)) at h1
    rwa [heq1, heq2] at h1
  have hCorner2 : j10H ((1 / 2 : ℂ) * (1 + Complex.I)) ≤ j10H (j10P δ) := by
    have h1 := hseg2 ⟨le_rfl, hy_half.le⟩ ⟨hy_half.le, le_rfl⟩ hy_half.le
    change j10H (((1 / 2 : ℝ) : ℂ) * (1 + Complex.I)) ≤
      j10H ((j10YDelta δ : ℂ) * (1 + Complex.I)) at h1
    push_cast at h1
    exact h1.trans hCorner1
  have hH_plus : ∀ t ∈ Icc (0 : ℝ) 3, j10H (j10GammaPlus δ T₀ t) ≤ j10H (j10P δ) := by
    intro t ht
    unfold j10GammaPlus
    by_cases ht1 : t ≤ 1
    · simp only [ht1, ↓reduceIte]
      have hx_val : (((1 - t : ℝ) : ℂ) * j10P δ + (t : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I))) =
          ((((1 - t) * (δ / 2) + t * j10YDelta δ : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ)) := by
        rw [j10P_eq]; apply Complex.ext <;> (simp; try ring)
      rw [hx_val]
      set x := (1 - t) * (δ / 2) + t * j10YDelta δ
      have hx_mem : x ∈ Icc (δ / 2) (j10YDelta δ) := by
        have hlo : 0 ≤ t * (j10YDelta δ - δ / 2) := mul_nonneg ht.1 (by linarith)
        have hhi : 0 ≤ (1 - t) * (j10YDelta δ - δ / 2) := mul_nonneg (by linarith) (by linarith)
        dsimp [x]
        exact ⟨by linarith, by linarith⟩
      have h1 := hseg1 ⟨le_rfl, hxy.le⟩ hx_mem hx_mem.1
      change j10H ((x : ℂ) + Complex.I * (j10YDelta δ : ℂ)) ≤
        j10H (((δ / 2 : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ)) at h1
      rwa [show ((δ / 2 : ℝ) : ℂ) + Complex.I * (j10YDelta δ : ℂ) = j10P δ from (j10P_eq δ).symm] at h1
    · push Not at ht1
      by_cases ht2 : t ≤ 2
      · simp only [ht1.not_ge, ↓reduceIte, ht2]
        have hs_val : (((2 - t : ℝ) : ℂ) * ((j10YDelta δ : ℂ) * (1 + Complex.I)) +
            ((t - 1 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (1 + Complex.I))) =
            (((2 - t) * j10YDelta δ + (t - 1) * (1 / 2) : ℝ) : ℂ) * (1 + Complex.I) := by
          apply Complex.ext <;> simp
        rw [hs_val]
        set s := (2 - t) * j10YDelta δ + (t - 1) * (1 / 2)
        have hs_mem : s ∈ Icc (j10YDelta δ) (1 / 2) := by
          have hlo : 0 ≤ (t - 1) * (1 / 2 - j10YDelta δ) := mul_nonneg (by linarith) (by linarith)
          have hhi : 0 ≤ (2 - t) * (1 / 2 - j10YDelta δ) := mul_nonneg (by linarith) (by linarith)
          dsimp [s]
          exact ⟨by linarith, by linarith⟩
        have h1 := hseg2 ⟨le_rfl, hy_half.le⟩ hs_mem hs_mem.1
        exact h1.trans hCorner1
      · push Not at ht2
        simp only [ht1.not_ge, ht2.not_ge, ↓reduceIte]
        set τ := (3 - t) * (1 / 2) + (t - 2) * T₀
        have hτ_ge : 1 / 2 ≤ τ := by
          have hlo : 0 ≤ (t - 2) * (T₀ - 1 / 2) := mul_nonneg (by linarith) (by linarith)
          dsimp [τ]; linarith
        have h1 := hseg3.antitoneOn (by simp : (1 / 2 : ℝ) ∈ Ici 0) (by simp; linarith) hτ_ge
        have heq_half : ((1 / 2 : ℂ) + Complex.I * (((1 / 2 : ℝ) : ℂ))) =
            (1 / 2 : ℂ) * (1 + Complex.I) := by push_cast; ring
        change j10H ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) ≤ j10H (j10P δ)
        have h1' : j10H ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) ≤
            j10H ((1 / 2 : ℂ) + Complex.I * (((1 / 2 : ℝ) : ℂ))) := by
          simpa [j10H] using h1
        rw [heq_half] at h1'
        exact h1'.trans hCorner2
  have hep0 : j10GammaPlus δ T₀ 0 = j10P δ := by unfold j10GammaPlus; simp
  have hep1 : j10GammaPlus δ T₀ 1 = (j10YDelta δ : ℂ) * (1 + Complex.I) := by
    unfold j10GammaPlus; simp
  have hep2 : j10GammaPlus δ T₀ 2 = (1 / 2 : ℂ) * (1 + Complex.I) := by
    unfold j10GammaPlus; simp; ring
  have hep3 : j10GammaPlus δ T₀ 3 = (1 / 2 : ℂ) + Complex.I * (T₀ : ℂ) := by
    unfold j10GammaPlus
    simp [show ¬ (3 : ℝ) ≤ 1 by norm_num, show ¬ (3 : ℝ) ≤ 2 by norm_num]
    ring
  have hcont_p := j10GammaPlus_continuousOn δ T₀
  have hcont_m : ContinuousOn (j10GammaMinus δ T₀) (Icc 0 3) :=
    Complex.continuous_conj.comp_continuousOn hcont_p
  -- Bounded `|ω'|` on `γ_+` and `γ_-` via `deriv_chartOmega_strip_bound`.
  obtain ⟨Cω, hCω_pos, hCω⟩ := deriv_chartOmega_strip_bound
  let M : ℝ := Cω * (1 + T₀)
  have hM_pos : 0 < M := mul_pos hCω_pos (by linarith)
  have hM_bd : ∀ t ∈ Icc (0 : ℝ) 3,
      ‖deriv chartOmega (j10GammaPlus δ T₀ t)‖ ≤ M ∧
      ‖deriv chartOmega (j10GammaMinus δ T₀ t)‖ ≤ M := by
    intro t ht
    have hm := j10GammaPlus_mem_upperLeftHalfStrip hδ_pos hδ_le hT₀ ht
    have hstrip : j10GammaPlus δ T₀ t ∈ stripClosed := ⟨hm.1, by linarith [hm.2.1]⟩
    have hbp := hCω (j10GammaPlus δ T₀ t) hstrip
    have habs : |(j10GammaPlus δ T₀ t).im| ≤ T₀ := by
      rw [abs_of_nonneg (by linarith [hm.2.2.1])]; exact hm.2.2.2
    have hbp' : ‖deriv chartOmega (j10GammaPlus δ T₀ t)‖ ≤ M :=
      hbp.trans (mul_le_mul_of_nonneg_left (by linarith) hCω_pos.le)
    have hconj := deriv_chartOmega_conj' hstrip.1 hstrip.2
    have hnorm_m : ‖deriv chartOmega (j10GammaMinus δ T₀ t)‖ =
        ‖deriv chartOmega (j10GammaPlus δ T₀ t)‖ := by
      unfold j10GammaMinus
      rw [hconj, Complex.norm_conj]
    exact ⟨hbp', hnorm_m.le.trans hbp'⟩
  -- Uniform lower bound on `‖ω‖` via compactness of `[0, 3]`.
  have h_om_cont : ContinuousOn (fun t => ‖chartOmega (j10GammaPlus δ T₀ t)‖) (Icc 0 3) := by
    refine continuous_norm.comp_continuousOn (continuousOn_chartOmega.comp hcont_p fun t ht => ?_)
    have hm := j10GammaPlus_mem_upperLeftHalfStrip hδ_pos hδ_le hT₀ ht
    exact ⟨hm.1, by linarith [hm.2.1]⟩
  obtain ⟨t_min, ht_min_mem, ht_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, left_mem_Icc.mpr (by norm_num)⟩ h_om_cont
  let c : ℝ := ‖chartOmega (j10GammaPlus δ T₀ t_min)‖
  have hc_pos : 0 < c := by
    have hm := j10GammaPlus_mem_upperLeftHalfStrip hδ_pos hδ_le hT₀ ht_min_mem
    have hstrip : j10GammaPlus δ T₀ t_min ∈ stripClosed := ⟨hm.1, by linarith [hm.2.1]⟩
    have hne_half : j10GammaPlus δ T₀ t_min ≠ 1 / 2 := fun h0 => by
      have := congrArg Complex.im h0; simp at this; linarith [hm.2.2.1]
    have hom_ne : chartOmega (j10GammaPlus δ T₀ t_min) ≠ 0 := by
      intro h0
      exact hne_half ((chartOmega_eq_zero_iff hstrip).mp h0)
    exact norm_pos_iff.mpr hom_ne
  have hc_bd : ∀ t ∈ Icc (0 : ℝ) 3,
      c ≤ ‖chartOmega (j10GammaPlus δ T₀ t)‖ ∧ c ≤ ‖chartOmega (j10GammaMinus δ T₀ t)‖ := by
    intro t ht
    have h1 : c ≤ ‖chartOmega (j10GammaPlus δ T₀ t)‖ := ht_min ht
    have hm := j10GammaPlus_mem_upperLeftHalfStrip hδ_pos hδ_le hT₀ ht
    have hconj : chartOmega (j10GammaMinus δ T₀ t) =
        starRingEnd ℂ (chartOmega (j10GammaPlus δ T₀ t)) := by
      unfold j10GammaMinus
      exact chartOmega_conj hm.1 (by linarith [hm.2.1])
    have hnorm_m : ‖chartOmega (j10GammaMinus δ T₀ t)‖ = ‖chartOmega (j10GammaPlus δ T₀ t)‖ := by
      rw [hconj, Complex.norm_conj]
    exact ⟨h1, hnorm_m ▸ h1⟩
  have htv_zeta_p : eVariationOn (j10GammaPlus δ T₀) (Icc 0 3) < ⊤ :=
    eVariationOn_j10GammaPlus_lt_top δ T₀
  have htv_zeta_m : eVariationOn (j10GammaMinus δ T₀) (Icc 0 3) < ⊤ := by
    unfold j10GammaMinus
    rwa [eVariationOn_comp_conj]
  have htv_om_p : eVariationOn (chartOmega ∘ j10GammaPlus δ T₀) (Icc 0 3) < ⊤ :=
    eVariationOn_chartOmega_comp_lt_top hM_pos.le hδ_pos hδ_le hT₀ (fun t ht => (hM_bd t ht).1)
  have htv_om_m : eVariationOn (chartOmega ∘ j10GammaMinus δ T₀) (Icc 0 3) < ⊤ := by
    have hcongr : EqOn (chartOmega ∘ j10GammaMinus δ T₀)
        (fun t => starRingEnd ℂ (chartOmega (j10GammaPlus δ T₀ t))) (Icc 0 3) := by
      intro t ht
      have hm := j10GammaPlus_mem_upperLeftHalfStrip hδ_pos hδ_le hT₀ ht
      dsimp [Function.comp_def, j10GammaMinus]
      exact chartOmega_conj hm.1 (by linarith [hm.2.1])
    rw [eVariationOn.eq_of_eqOn hcongr, eVariationOn_comp_conj]
    exact htv_om_p
  refine ⟨hep0, hep1, hep2, hep3, hp_le, hε_ge, hε_pos, ?_,
    hcont_p, hcont_m, htv_zeta_p, htv_zeta_m, ⟨M, hM_pos, hM_bd⟩, htv_om_p, htv_om_m, ⟨c, hc_pos, hc_bd⟩⟩
  intro t ht
  have hm := j10GammaPlus_mem_upperLeftHalfStrip hδ_pos hδ_le hT₀ ht
  have h_om_re_p : 0 ≤ (chartOmega (j10GammaPlus δ T₀ t)).re := lemma_J7Q.2 _ hm.1 hm.2.1
  have h_om_re_m : 0 ≤ (chartOmega (j10GammaMinus δ T₀ t)).re := by
    unfold j10GammaMinus
    rw [chartOmega_conj hm.1 (by linarith [hm.2.1]), Complex.conj_re]
    exact h_om_re_p
  have hHp := hH_plus t ht
  have hHm : j10H (j10GammaMinus δ T₀ t) = j10H (j10GammaPlus δ T₀ t) := by
    unfold j10H j10GammaMinus
    rw [chartPhiV_conj hm.1 (by linarith [hm.2.1]) h_om_re_p xiStar_pos, Complex.conj_re]
  refine ⟨hm.1, hm.2.1, by linarith [hm.2.2.1], ?_, ?_, ?_, hHp, ?_, ?_, ?_, h_om_re_p, h_om_re_m⟩
  · simpa [j10GammaMinus] using hm.1
  · simpa [j10GammaMinus] using hm.2.1
  · simp [j10GammaMinus]; linarith [hm.2.2.1]
  · have : j10H (j10P δ) = -2 * ε := by dsimp [ε]; ring
    linarith
  · linarith
  · have : j10H (j10P δ) = -2 * ε := by dsimp [ε]; ring
    linarith

/-- info: 'FormalResearch.ModularBootstrap.ChartGeometry.j10H_p_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ChartGeometry.j10H_p_le

/-- info: 'FormalResearch.ModularBootstrap.ChartGeometry.lemma_J10_compact_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ChartGeometry.lemma_J10_compact_escape

end FormalResearch.ModularBootstrap.ChartGeometry
