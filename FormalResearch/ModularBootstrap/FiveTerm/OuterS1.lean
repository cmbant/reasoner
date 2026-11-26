module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterH3

/-!
# FIVE-S, S1 (assembly): `G_outer = (1+z²)⁻¹ H₃^{1/4} G̃` and the modulus of `G̃` on the slit

`G̃ = (1+z²) G_outer / R4` is holomorphic and zero-free on `Ω`, and on the slit
`|G̃(iy)| = ((1 - e^{-4πx})/(1 - e^{-4πξ_*}))² / √(1 + 6y² + y⁴)`, which is the stated `log` formula
(`Ũ(u) - Ũ₀` of `cts:cauchy-dual` Step 2 at `u = ρ²`, `ρ = (1-y)/(1+y)`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

lemma halfDisc_mem_diff {z : ℂ} (hz : z ∈ halfDisc) : z ∈ closure halfDisc \ singPts := by
  refine ⟨subset_closure hz, fun h => ?_⟩
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have h3 : z ≠ 1 := by
    intro h; have := hz.1; rw [h] at this; simp at this
  simp only [singPts, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  tauto

lemma gtilde_diff : DifferentiableOn ℂ (Gtilde R4c) halfDisc := by
  unfold Gtilde
  refine DifferentiableOn.div (((by fun_prop : Differentiable ℂ fun z : ℂ => 1 + z ^ 2).differentiableOn).mul
    gout_diff) differentiableOn_R4c (fun z hz => R4c_ne_zero hz)

lemma gtilde_ne_zero {z : ℂ} (hz : z ∈ halfDisc) : Gtilde R4c z ≠ 0 := by
  unfold Gtilde
  exact div_ne_zero (mul_ne_zero (one_add_sq_ne_zero_of_halfDisc hz) (gout_ne_zero (halfDisc_mem_diff hz)))
    (R4c_ne_zero hz)

lemma norm_one_add_sq_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖(1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2‖ = 1 - y ^ 2 := by
  have : (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith [hy.1, hy.2])]

/-- The modulus of `G̃` on the slit. -/
lemma norm_gtilde_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖Gtilde R4c (Complex.I * (y : ℂ))‖ =
      ((1 - Real.exp (-(4 * π * xOf y))) / (1 - Real.exp (-(4 * π * xiStar)))) ^ 2 /
        √(1 + 6 * y ^ 2 + y ^ 4) := by
  have hx := xOf_pos hy
  have hxi := xiStar_pos
  have hq : 0 < xOf y / xiStar := div_pos hx hxi
  have hsq : 0 < √(xOf y / xiStar) := Real.sqrt_pos.mpr hq
  have hw : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hP : 0 < √(1 + 6 * y ^ 2 + y ^ 4) := Real.sqrt_pos.mpr (by positivity)
  unfold Gtilde
  rw [norm_div, norm_mul, norm_one_add_sq_slit hy, gout_modulus hy, norm_R4c_slit hy]
  unfold Wslit
  field_simp

private lemma log_sub_exp_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-(4 * π * t)) := by
  rw [sub_pos, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have := Real.pi_pos; nlinarith

lemma log_gtilde_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Real.log ‖Gtilde R4c (Complex.I * (y : ℂ))‖ =
      Utilde0 + 2 * Real.log (1 + (1 - y) / (1 + y)) - (1 / 2) * Real.log (1 + ((1 - y) / (1 + y)) ^ 4) +
        2 * Real.log (1 - Real.exp (-(4 * π * xOf y))) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  have hx := xOf_pos hy'
  have hxi := xiStar_pos
  have h1 := log_sub_exp_pos hx
  have h2 := log_sub_exp_pos hxi
  have hP : 0 < 1 + 6 * y ^ 2 + y ^ 4 := by positivity
  have hy1' : 0 < 1 + y := by linarith
  rw [norm_gtilde_slit hy']
  have e1 : 1 + (1 - y) / (1 + y) = 2 / (1 + y) := by field_simp; ring
  have e2 : 1 + ((1 - y) / (1 + y)) ^ 4 = 2 * (1 + 6 * y ^ 2 + y ^ 4) / (1 + y) ^ 4 := by
    field_simp; ring
  rw [e1, e2]
  have hQ : 0 < (1 - Real.exp (-(4 * π * xOf y))) / (1 - Real.exp (-(4 * π * xiStar))) := div_pos h1 h2
  rw [Real.log_div (by positivity) (Real.sqrt_pos.mpr hP).ne', Real.log_pow, Real.log_div h1.ne' h2.ne',
    Real.log_sqrt hP.le, Real.log_div (by norm_num) hy1'.ne',
    Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hP.ne', Real.log_pow]
  unfold Utilde0
  push_cast
  linarith

/-- **`OuterS1`** (`cts:main` Piece 3; `cts:cauchy-dual` Step 2): bridge to `Gout` and the factorisation
`G_outer = (1+z²)⁻¹ H₃^{1/4} G̃`.  The fourth root is `R4c`.  Class: proved. -/
theorem outerS1 : OuterS1 := by
  obtain ⟨h0, hodd, hcont⟩ := thetaOut_soft
  refine ⟨fun y hy => gout_polar hy, h0, hodd, hcont, differentiableOn_H3, fun z hz => H3_ne_zero hz, H3_zero,
    fun r hr => H3_real_pos hr, fun y hy => norm_H3_slit hy, R4c, differentiableOn_R4c,
    fun z _ => R4c_pow_four, fun r hr => R4c_real_pos hr, gtilde_diff, fun z hz => gtilde_ne_zero hz,
    fun y hy => log_gtilde_slit hy⟩

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerS1

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
