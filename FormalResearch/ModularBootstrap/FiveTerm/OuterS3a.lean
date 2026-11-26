module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS1
public import FormalResearch.ModularBootstrap.FiveTerm.OuterDphi

/-!
# FIVE-S, S3 (slit boundary values of `F_δ`): `arg F_δ(iy(x)) = δφ_δ(x)` and the factorisation of `F_δ`

Two S1-only facts about the smoothed minimiser `F_δ = m_δ (1+z²)/G_outer` (`fDelta Gout δ`) used by `cts:smooth-env` (2):

* `fDelta_slit_polar`: on the slit `z = iy`, `F_δ(iy) = ρ_δ(y) e^{iδφ}` with explicit `ρ_δ > 0` and phase
  `-θ_out(y) + ½(arctan((1-δ)y) - arctan y)`; with `y = y(x)` the phase is `dphi δ x` (`fDelta_slit_dphi`), which is the
  definition of `δφ_δ` in `OuterStripStatements` (so that definition is the boundary argument of `F_δ`);
* `fDelta_factor`: `F_δ(z) = (1 - (1-δ)z)^{-1/2} (1+z²)² R4(z)⁻¹ Ĝ(z)⁻¹`, `Ĝ = (1-z)^{-1/2} G̃`, `z ∈ Ω` (the factorisation
  of `cts:smooth-env` proof (2)-(3)).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

lemma log_polar {r φ : ℝ} (hr : 0 < r) (hφ : -π < φ) (hφ' : φ ≤ π) :
    Complex.log ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = ((Real.log r : ℝ) : ℂ) + (φ : ℂ) * Complex.I := by
  have harg : Complex.arg ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = φ := by
    rw [Complex.arg_real_mul _ hr, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨hφ, hφ'⟩
  have hnorm : ‖(r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  apply Complex.ext
  · rw [Complex.log_re, hnorm]; simp
  · rw [Complex.log_im, harg]; simp

/-- `log(1 - i t) = ½ log(1+t²) - i arctan t`. -/
lemma log_one_sub_I_mul (t : ℝ) :
    Complex.log (1 - Complex.I * (t : ℂ)) =
      ((1 / 2 * Real.log (1 + t ^ 2) : ℝ) : ℂ) + ((-Real.arctan t : ℝ) : ℂ) * Complex.I := by
  have h := polar_re_pos (a := 1) one_pos (-t)
  rw [div_one, Real.arctan_neg] at h
  have e : (1 : ℂ) - Complex.I * (t : ℂ) = ((1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hpos : (0 : ℝ) < √(1 ^ 2 + (-t) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [e, h, log_polar hpos (by linarith [Real.arctan_lt_pi_div_two t, Real.pi_pos] : -π < -Real.arctan t)
    (by linarith [Real.neg_pi_div_two_lt_arctan t, Real.pi_pos])]
  congr 2
  rw [Real.log_sqrt (by positivity)]
  ring_nf

lemma mEps_slit {δ y : ℝ} :
    mEps δ (Complex.I * (y : ℂ)) =
      (((((1 + y ^ 2) / (1 + (1 - δ) ^ 2 * y ^ 2)) ^ (1 / 4 : ℝ) : ℝ)) : ℂ) *
        Complex.exp (((1 / 2 * (Real.arctan ((1 - δ) * y) - Real.arctan y) : ℝ) : ℂ) * Complex.I) := by
  unfold mEps
  have e2 : (1 : ℂ) - (((1 - δ : ℝ)) : ℂ) * (Complex.I * (y : ℂ)) = 1 - Complex.I * (((1 - δ) * y : ℝ) : ℂ) := by
    push_cast; ring
  rw [e2, log_one_sub_I_mul, log_one_sub_I_mul]
  have hA : 0 < 1 + y ^ 2 := by positivity
  have hB : 0 < 1 + ((1 - δ) * y) ^ 2 := by positivity
  have hAB : 0 < (1 + y ^ 2) / (1 + (1 - δ) ^ 2 * y ^ 2) := by
    have : 0 < 1 + (1 - δ) ^ 2 * y ^ 2 := by positivity
    positivity
  have hexp : (((((1 + y ^ 2) / (1 + (1 - δ) ^ 2 * y ^ 2)) ^ (1 / 4 : ℝ) : ℝ)) : ℂ) =
      Complex.exp (((1 / 4 * (Real.log (1 + y ^ 2) - Real.log (1 + ((1 - δ) * y) ^ 2)) : ℝ) : ℂ)) := by
    rw [Real.rpow_def_of_pos hAB, Complex.ofReal_exp]
    congr 1
    have : (1 + (1 - δ) ^ 2 * y ^ 2) = 1 + ((1 - δ) * y) ^ 2 := by ring
    rw [this, Real.log_div hA.ne' hB.ne']
    ring_nf
  rw [hexp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma Wslit_pos' {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < Wslit y := by
  have h1 := gout_modulus hy
  have h2 := gout_ne_zero (slit_mem_diff hy)
  have : 0 < ‖Gout (Complex.I * (y : ℂ))‖ := norm_pos_iff.mpr h2
  rwa [h1] at this

/-- **`F_δ` on the slit** (S1-only step of `cts:smooth-env` (2)): `F_δ(iy) = ρ e^{iφ}`, `φ = -θ_out(y) + ½(arctan((1-δ)y) - arctan y)`,
`ρ = (1-y²)/W_slit(y) · ((1+y²)/(1+(1-δ)²y²))^{1/4} > 0`.  Class: proved. -/
theorem fDelta_slit_polar {δ y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    fDelta Gout δ (Complex.I * (y : ℂ)) =
      ((((1 - y ^ 2) / Wslit y * ((1 + y ^ 2) / (1 + (1 - δ) ^ 2 * y ^ 2)) ^ (1 / 4 : ℝ) : ℝ)) : ℂ) *
        Complex.exp (Complex.I * ((-thetaOut y + 1 / 2 * (Real.arctan ((1 - δ) * y) - Real.arctan y) : ℝ) : ℂ)) := by
  have hW := Wslit_pos' hy
  have hw : (Wslit y : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  unfold fDelta fStar
  rw [mEps_slit, gout_polar hy]
  have e1 : (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  rw [e1]
  have hexp : Complex.exp (Complex.I * ((-thetaOut y + 1 / 2 * (Real.arctan ((1 - δ) * y) - Real.arctan y) : ℝ) : ℂ)) =
      Complex.exp (((1 / 2 * (Real.arctan ((1 - δ) * y) - Real.arctan y) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * (thetaOut y : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [hexp]
  push_cast
  field_simp

lemma yOfX_mem {x : ℝ} (hx : xiStar < x) : yOfX x ∈ Ioo (0 : ℝ) 1 := by
  rw [yOfX_eq hx]
  have hτ := tauOfX_nonneg hx
  have hτ0 : 0 < tauOfX x := by
    unfold tauOfX
    have := cosh_div_sqrt_two_gt_one hx
    have h2 : 0 < Real.arcosh (Real.cosh (π * x) / √2) := Real.arcosh_pos this
    positivity
  have : 0 < tt (tauOfX x) := by
    unfold tt
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  exact ⟨this, tt_lt_one _⟩

lemma thetaOut_yOfX {x : ℝ} (hx : xiStar < x) : thetaOut (yOfX x) = thetaOutX x := by
  have hy := yOfX_mem hx
  unfold thetaOut thetaOutX
  rw [yOfX_eq hx]
  congr 1
  unfold tt
  have : π * tauOfX x / 4 = π * tauOfX x / 4 := rfl
  rw [Real.artanh_tanh]
  field_simp

/-- **`δφ_δ` is the boundary argument of `F_δ`**: `F_δ(i y(x)) = ρ_δ(x) e^{i δφ_δ(x)}`, `x > ξ_*`.  Class: proved. -/
theorem fDelta_slit_dphi {δ x : ℝ} (hx : xiStar < x) :
    ∃ ρ : ℝ, 0 < ρ ∧ fDelta Gout δ (Complex.I * (yOfX x : ℂ)) =
      (ρ : ℂ) * Complex.exp (Complex.I * (dphi δ x : ℂ)) := by
  have hy := yOfX_mem hx
  have hW := Wslit_pos' hy
  refine ⟨(1 - yOfX x ^ 2) / Wslit (yOfX x) * ((1 + yOfX x ^ 2) / (1 + (1 - δ) ^ 2 * yOfX x ^ 2)) ^ (1 / 4 : ℝ),
    ?_, ?_⟩
  · have : 0 < 1 - yOfX x ^ 2 := by nlinarith [hy.1, hy.2]
    have h2 : 0 < 1 + (1 - δ) ^ 2 * yOfX x ^ 2 := by positivity
    positivity
  · rw [fDelta_slit_polar hy]
    unfold dphi
    rw [thetaOut_yOfX hx]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.fDelta_slit_dphi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fDelta_slit_dphi

/-- **The factorisation of `F_δ`** (`cts:smooth-env` proof, (2)-(3)): for `z ∈ Ω`,
`F_δ(z) = (1 - (1-δ)z)^{-1/2} (1+z²)² / (R4(z) Ĝ(z))`, `Ĝ(z) = (1-z)^{-1/2} G̃(z)`.  Class: proved. -/
theorem fDelta_factor {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {z : ℂ} (hz : z ∈ halfDisc) :
    fDelta Gout δ z =
      (1 - (((1 - δ : ℝ)) : ℂ) * z) ^ (-(1 / 2 : ℂ)) * (1 + z ^ 2) ^ 2 /
        (R4c z * ((1 - z) ^ (-(1 / 2 : ℂ)) * Gtilde R4c z)) := by
  have hz1 : ‖z‖ < 1 := hz.1
  have h1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz1; simp at hz1
  have h2 : (1 : ℂ) - (((1 - δ : ℝ)) : ℂ) * z ≠ 0 := by
    intro h
    have hn : ‖(((1 - δ : ℝ)) : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      nlinarith [norm_nonneg z]
    have : (((1 - δ : ℝ)) : ℂ) * z = 1 := by linear_combination -h
    rw [this] at hn; simp at hn
  have hG := gout_ne_zero (halfDisc_mem_diff hz)
  have hR := R4c_ne_zero hz
  have hsq := one_add_sq_ne_zero_of_halfDisc hz
  unfold fDelta mEps fStar Gtilde
  rw [Complex.cpow_def_of_ne_zero h2, Complex.cpow_def_of_ne_zero h1]
  have hm : Complex.exp (1 / 2 * (Complex.log (1 - z) - Complex.log (1 - (((1 - δ : ℝ)) : ℂ) * z))) =
      Complex.exp (Complex.log (1 - (((1 - δ : ℝ)) : ℂ) * z) * -(1 / 2)) /
        Complex.exp (Complex.log (1 - z) * -(1 / 2)) := by
    rw [← Complex.exp_sub]; congr 1; ring
  rw [hm]
  have e1 := Complex.exp_ne_zero (Complex.log (1 - (((1 - δ : ℝ)) : ℂ) * z) * -(1 / 2))
  have e2 := Complex.exp_ne_zero (Complex.log (1 - z) * -(1 / 2))
  field_simp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.fDelta_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fDelta_factor

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
