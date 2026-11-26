module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs
public import FormalResearch.ModularBootstrap.TipFront.ComplexMajorant

/-!
# Exact Langer Bridge (`cts:langer`, `rem:s1`, `cts:phaselock`)

Proves `lowerLangerPhase_holds : LowerLangerPhase`, i.e., for sufficiently large `c` and all
`u ∈ [-(|a_1| + 1), 0)`:
`tauPhase (√(3 * virasoroDeltaChart c u / c)) = -u / (betaTip * c ^ (2 / 3 : ℝ))`.

Proof:
1. Both `Ψ(b) := tipL b - I * majorantHolomorphic b` and
   `Φ(b) := -KTip * (ξ_* - b)^{3/2} * pg.A (b - ξ_*)` (`pg := TipFront.lemmaGPotentialInput_virasoro`)
   are holomorphic on `OmegaPos = ball ξ_* r₀ ∩ {b | 0 < b.im}` and have the same real part
   `(tipL b).re + majorant2D b` (by `pg.U_add_L_near_tip` and `lemmaGPotentialInput_virasoro_U`).
   Hence `HasDerivAt Φ ((2π/3) * (1 - 2 I pMap b)) b` on `OmegaPos`.
2. Integrating from `ξ_* + δ + y I` to `x + y I` (`ξ_* < x < ξ_* + r₀`) and taking `y → 0⁺` then `δ → 0⁺`,
   the boundary limit `pMap (t + y I) → (3/4) rhoU t - I/2` yields
   `(x - ξ_*)^{3/2} * (pg.A (x - ξ_*)).re = cumulN x / kTip`, so
   `(x - ξ_*) * ((pg.A (x - ξ_*)).re)^{2/3} = tauPhase x`.
3. Substituting `x = √(3 * virasoroDeltaChart c u / c)` into `virasoroUInf (ξ_c(u)) = u c^{-2/3}`
   gives `tauPhase x = -u / (betaTip * c^{2/3})`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. Boundary limit of `pMap (t + y I)` as `y → 0⁺` for `t > ξ_*` -/

private lemma tendsto_pMap_slit_right_full {t : ℝ} (ht : xiStar < t) :
    Tendsto (fun y : ℝ => pMap ((t : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (((3 / 4 : ℝ) * rhoU t : ℂ) - (1 / 2 : ℂ) * Complex.I)) := by
  have him : Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (-(1 / 2 : ℝ))) := tendsto_pMap_slit_right ht
  have hpi := Real.pi_pos
  have hlim_z : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
    have h0 : (t : ℂ) = (t : ℂ) + (0 : ℂ) * Complex.I := by simp
    conv_rhs => rw [h0]
    exact tendsto_const_nhds.add
      ((Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        tendsto_const_nhds)
  let w : ℂ → ℂ := fun z => -Complex.I * Complex.sinh ((π : ℂ) * z)
  have hw_cont : Continuous w :=
    continuous_const.mul (Complex.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hw_val : w (t : ℂ) = -Complex.I * ((Real.sinh (π * t) : ℝ) : ℂ) := by
    dsimp [w]
    rw [show (π : ℂ) * (t : ℂ) = ((π * t : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sinh]
  have hw_tend : Tendsto (fun y : ℝ => w ((t : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (-Complex.I * ((Real.sinh (π * t) : ℝ) : ℂ))) := by
    rw [← hw_val]
    exact hw_cont.continuousAt.tendsto.comp hlim_z
  have hsinh_gt : 1 < Real.sinh (π * t) := by
    rw [← sinh_pi_mul_xiStar]
    exact Real.sinh_lt_sinh.mpr (mul_lt_mul_of_pos_left ht hpi)
  have hsq_pos : 0 < Real.sinh (π * t) ^ 2 - 1 := by nlinarith
  have hnz_tend : Tendsto (fun y : ℝ => -((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1))
      (𝓝[>] 0) (𝓝 ((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ)) := by
    have h1 := ((hw_tend.pow 2).add (tendsto_const_nhds (x := (1 : ℂ)))).neg
    convert h1 using 2
    rw [mul_pow, neg_sq, Complex.I_sq]; push_cast; ring
  have harg_nz : Tendsto (fun y : ℝ =>
      Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1))) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Complex.arg ((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ) = 0 :=
      Complex.arg_ofReal_of_nonneg hsq_pos.le
    have hcmp := (Complex.continuousAt_arg (Complex.ofReal_mem_slitPlane.mpr hsq_pos)).tendsto.comp
      hnz_tend
    rwa [h0] at hcmp
  have hnorm_tend : Tendsto (fun y : ℝ =>
      ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖) (𝓝[>] 0)
      (𝓝 (Real.sinh (π * t) ^ 2 - 1)) := by
    have h1 := (continuous_norm.tendsto _).comp hnz_tend
    have hnl : ‖((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ)‖ = Real.sinh (π * t) ^ 2 - 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hsq_pos.le]
    rw [hnl] at h1
    convert h1 using 1
    ext y; exact (norm_neg _).symm
  have him_neg_ev : ∀ᶠ y : ℝ in 𝓝[>] 0,
      ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1).im < 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
    have hri := neg_I_mul_sinh_pi_re_im ((t : ℂ) + (y : ℂ) * Complex.I)
    have hre0 : ((t : ℂ) + (y : ℂ) * Complex.I).re = t := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    have him0 : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
    rw [hre0, him0] at hri
    have hw_re_pos : 0 < (w ((t : ℂ) + (y : ℂ) * Complex.I)).re := by
      dsimp [w]; rw [hri.1]
      exact mul_pos (Real.cosh_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hy.1) (by nlinarith [hy.2]))
    have hw_im_neg : (w ((t : ℂ) + (y : ℂ) * Complex.I)).im < 0 := by
      dsimp [w]; rw [hri.2]
      have hsinh_pos : 0 < Real.sinh (π * t) := by linarith
      have hcos_pos : 0 < Real.cos (π * y) :=
        Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
      nlinarith
    have him_sq : ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1).im =
        2 * (w ((t : ℂ) + (y : ℂ) * Complex.I)).re *
          (w ((t : ℂ) + (y : ℂ) * Complex.I)).im := by
      simp [pow_two]; ring
    rw [him_sq]; nlinarith
  have hs_tend : Tendsto (fun y : ℝ =>
      ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (-Complex.I * ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ))) := by
    have hsqrt_tend : Tendsto (fun y : ℝ =>
        Real.sqrt ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖) (𝓝[>] 0)
        (𝓝 (Real.sqrt (Real.sinh (π * t) ^ 2 - 1))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hnorm_tend
    have hsin_tend : Tendsto (fun y : ℝ =>
        Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 0) := by
      have h1 := (Real.continuous_sin.continuousAt.tendsto.comp (harg_nz.div_const 2))
      have h0 : Real.sin ((0 : ℝ) / 2) = 0 := by norm_num
      rwa [h0] at h1
    have hcos_tend : Tendsto (fun y : ℝ =>
        Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 1) := by
      have h1 := (Real.continuous_cos.continuousAt.tendsto.comp (harg_nz.div_const 2))
      have h0 : Real.cos ((0 : ℝ) / 2) = 1 := by norm_num
      rwa [h0] at h1
    have hcomb : Tendsto (fun y : ℝ =>
        ((Real.sqrt ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖ : ℝ) : ℂ) *
          (((Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2) : ℝ) : ℂ) -
            Complex.I * ((Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2) : ℝ) : ℂ)))
        (𝓝[>] 0)
        (𝓝 (((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) *
          (((0 : ℝ) : ℂ) - Complex.I * ((1 : ℝ) : ℂ)))) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hsqrt_tend).mul
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp hsin_tend).sub
          (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hcos_tend)))
    have hlim_eq : ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) *
        (((0 : ℝ) : ℂ) - Complex.I * ((1 : ℝ) : ℂ)) =
        -Complex.I * ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hlim_eq] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [him_neg_ev] with y hy
    have hz0 : (w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1 ≠ 0 := by
      intro h0; rw [h0, Complex.zero_im] at hy; exact lt_irrefl _ hy
    set z := (w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1
    have harg_eq : Complex.arg z = Complex.arg (-z) - π := by
      rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hy]; ring
    have hlog_z : Complex.log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I :=
      Complex.ext (by simp [Complex.log_re]) (by simp [Complex.log_im])
    rw [Complex.cpow_def_of_ne_zero hz0, hlog_z, harg_eq]
    have h12 : (Real.log ‖z‖ + (Complex.arg (-z) - π : ℝ) * Complex.I : ℂ) * (1 / 2 : ℂ) =
        ((Real.log ‖z‖ / 2 : ℝ) : ℂ) +
          (((Complex.arg (-z) / 2 - π / 2 : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h12, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    have hsqrt : Real.exp (Real.log ‖z‖ / 2) = Real.sqrt ‖z‖ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hz0)]
      congr 1; ring
    rw [hsqrt]; push_cast; ring
  have hsum_tend : Tendsto (fun y : ℝ =>
      w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[>] 0)
      (𝓝 (-Complex.I * ((Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ))) := by
    have := hw_tend.add hs_tend
    convert this using 2
    push_cast; ring
  have hsum_norm : Tendsto (fun y : ℝ =>
      ‖w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)‖)
      (𝓝[>] 0) (𝓝 (Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1))) := by
    have h1 := (continuous_norm.tendsto _).comp hsum_tend
    have hpos : 0 < Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) := by positivity
    have hnl : ‖-Complex.I * ((Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ)‖ =
        Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    rwa [hnl] at h1
  have hpos_sum : Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) ≠ 0 := by positivity
  have hre : Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 ((3 / 4 : ℝ) * rhoU t)) := by
    have hlog := (Real.continuousAt_log hpos_sum).tendsto.comp hsum_norm
    have hdiv := hlog.div_const π
    have h_eq : ∀ y : ℝ, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re =
        Real.log ‖w ((t : ℂ) + (y : ℂ) * Complex.I) +
          ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)‖ / π := fun y => by
      unfold pMap complexArsinh
      have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hpi_inv, Complex.re_ofReal_mul, Complex.log_re]
      change π⁻¹ * Real.log ‖w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)‖ = _
      ring
    simp_rw [h_eq]
    have hval : Real.log (Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1)) / π =
        (3 / 4 : ℝ) * rhoU t := by
      rw [rhoU_eq_of_ge ht.le]
      unfold arccoshR
      ring
    rwa [hval] at hdiv
  have hcomb_lim := (Complex.continuous_ofReal.continuousAt.tendsto.comp hre).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul (tendsto_const_nhds (x := Complex.I)))
  have hcomb_lim' := hcomb_lim.congr (fun y => Complex.re_add_im _)
  rw [show ((3 / 4 : ℝ) : ℂ) * (rhoU t : ℂ) - (1 / 2 : ℂ) * Complex.I =
      (((3 / 4 : ℝ) * rhoU t : ℝ) : ℂ) + ((-(1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact hcomb_lim'

/-! ### 2. Derivative of `Φ` on the upper half-disc and boundary integral -/

private lemma hasDerivAt_zero_of_re_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hre : ∀ z ∈ U, (f z).re = 0) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt f 0 z := by
  have hdz : HasDerivAt f (deriv f z) z := (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => f (z + t)) (deriv f z) 0 := by
    have hc : HasDerivAt (fun t : ℝ => z + (t : ℂ)) (1 : ℂ) (0 : ℝ) := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z
    have hdz' : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) (z + (0 : ℂ)) := by
      simpa using hdz.hasFDerivAt
    have hcomp := (hdz'.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hc
    simpa [Function.comp_def] using hcomp
  have hre1 : HasDerivAt (fun t : ℝ => (f (z + t)).re) (deriv f z).re 0 := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have hre0_ev : (fun t : ℝ => (f (z + t)).re) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    have hcont : ContinuousAt (fun t : ℝ => z + (t : ℂ)) 0 := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds (by simpa using hU.mem_nhds hz)] with t ht
    exact hre _ ht
  have hd_re : (deriv f z).re = 0 :=
    hre1.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hre0_ev)
  have h2 : HasDerivAt (fun t : ℝ => f (z + t * Complex.I)) (Complex.I * deriv f z) 0 := by
    have hc : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Complex.I) Complex.I (0 : ℝ) := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).const_add z
    have hdz' : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) (z + (0 : ℂ) * Complex.I) := by
      simpa using hdz.hasFDerivAt
    have hcomp := (hdz'.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hc
    simpa [Function.comp_def] using hcomp
  have hre2 : HasDerivAt (fun t : ℝ => (f (z + t * Complex.I)).re) (Complex.I * deriv f z).re 0 := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    simpa [Function.comp_def] using h
  have hre2_ev : (fun t : ℝ => (f (z + t * Complex.I)).re) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    have hcont : ContinuousAt (fun t : ℝ => z + (t : ℂ) * Complex.I) 0 := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds (by simpa using hU.mem_nhds hz)] with t ht
    exact hre _ ht
  have hd_im : (deriv f z).im = 0 := by
    have h0 := hre2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hre2_ev)
    simpa [Complex.mul_re] using h0
  have hd0 : deriv f z = 0 := Complex.ext hd_re hd_im
  rwa [hd0] at hdz

private lemma cpow_three_halves_neg_sub_I_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun y : ℝ => ((-(r : ℂ)) - (y : ℂ) * Complex.I) ^ (3 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (Complex.I * ((r ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by
  have hnorm : Tendsto (fun y : ℝ => ‖-(r : ℂ) - (y : ℂ) * Complex.I‖) (𝓝[>] 0) (𝓝 r) := by
    have h1 : Tendsto (fun y : ℝ => -(r : ℂ) - (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (-(r : ℂ))) := by
      have h0 : -(r : ℂ) = -(r : ℂ) - (0 : ℂ) * Complex.I := by simp
      conv_rhs => rw [h0]
      exact tendsto_const_nhds.sub
        ((Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
          tendsto_const_nhds)
    have h2 := (continuous_norm.tendsto _).comp h1
    simpa [Function.comp_def, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr.le] using h2
  have harg : Tendsto (fun y : ℝ => Complex.arg (-(r : ℂ) - (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (-π)) := by
    have hev : ∀ᶠ y : ℝ in 𝓝[>] 0,
        Complex.arg (-(r : ℂ) - (y : ℂ) * Complex.I) =
          Real.arcsin (y / ‖-(r : ℂ) - (y : ℂ) * Complex.I‖) - π := by
      filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
      have hre_neg : (-(r : ℂ) - (y : ℂ) * Complex.I).re < 0 := by simp [hr]
      have him_neg : (-(r : ℂ) - (y : ℂ) * Complex.I).im < 0 := by simp [hy]
      rw [Complex.arg_of_re_neg_of_im_neg hre_neg him_neg]
      simp
    have hlim : Tendsto (fun y : ℝ => Real.arcsin (y / ‖-(r : ℂ) - (y : ℂ) * Complex.I‖) - π)
        (𝓝[>] 0) (𝓝 (-π)) := by
      have hdiv : Tendsto (fun y : ℝ => y / ‖-(r : ℂ) - (y : ℂ) * Complex.I‖) (𝓝[>] 0) (𝓝 (0 / r)) :=
        tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id.tendsto |>.div hnorm hr.ne'
      rw [zero_div] at hdiv
      have h2 := (Real.continuous_arcsin.continuousAt.tendsto.comp hdiv).sub_const π
      simpa [Real.arcsin_zero] using h2
    exact hlim.congr' (hev.mono fun y hy => hy.symm)
  have hpow : Tendsto (fun y : ℝ =>
      ((‖-(r : ℂ) - (y : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp ((3 / 2 : ℂ) * (Complex.arg (-(r : ℂ) - (y : ℂ) * Complex.I) : ℂ) * Complex.I))
      (𝓝[>] 0)
      (𝓝 (((r ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp ((3 / 2 : ℂ) * ((-π : ℝ) : ℂ) * Complex.I))) := by
    refine (Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inl hr.ne')).tendsto.comp hnorm)).mul ?_
    refine Complex.continuous_exp.continuousAt.tendsto.comp ?_
    exact (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp harg)).mul
      tendsto_const_nhds
  have hexp_eq : Complex.exp ((3 / 2 : ℂ) * ((-π : ℝ) : ℂ) * Complex.I) = Complex.I := by
    have h1 : (3 / 2 : ℂ) * ((-π : ℝ) : ℂ) * Complex.I = (((-(3 * π / 2) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hcos : Real.cos (-(3 * π / 2)) = 0 := by
      rw [Real.cos_neg, show (3 * π / 2 : ℝ) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
    have hsin : Real.sin (-(3 * π / 2)) = 1 := by
      rw [Real.sin_neg, show (3 * π / 2 : ℝ) = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two, neg_neg]
    rw [hcos, hsin]; simp
  rw [hexp_eq, mul_comm] at hpow
  refine hpow.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  have hne : -(r : ℂ) - (y : ℂ) * Complex.I ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hnorm_pos : 0 < ‖-(r : ℂ) - (y : ℂ) * Complex.I‖ := norm_pos_iff.mpr hne
  have hlog_z : Complex.log (-(r : ℂ) - (y : ℂ) * Complex.I) =
      (Real.log ‖-(r : ℂ) - (y : ℂ) * Complex.I‖ : ℂ) +
        (Complex.arg (-(r : ℂ) - (y : ℂ) * Complex.I) : ℂ) * Complex.I :=
    Complex.ext (by simp [Complex.log_re]) (by simp [Complex.log_im])
  have hlog_n : Complex.log (‖-(r : ℂ) - (y : ℂ) * Complex.I‖ : ℂ) =
      (Real.log ‖-(r : ℂ) - (y : ℂ) * Complex.I‖ : ℂ) :=
    Complex.ext (by simp [Complex.log_re])
      (by simp [Complex.log_im, Complex.arg_ofReal_of_nonneg hnorm_pos.le])
  rw [Complex.cpow_def_of_ne_zero hne, hlog_z, add_mul, Complex.exp_add,
    Complex.ofReal_cpow hnorm_pos.le,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hnorm_pos.ne'), hlog_n]
  congr 1
  · congr 1; push_cast; ring
  · congr 1; ring

private lemma tip_potential_cumulN_eq {x : ℝ}
    (hx_gt : xiStar < x)
    (hx_lt : x < xiStar + min (min TipFront.lemmaGPotentialInput_virasoro.r_A (1 / 2)) (xiStar / 2)) :
    (x - xiStar) ^ (3 / 2 : ℝ) *
        (TipFront.lemmaGPotentialInput_virasoro.A (((x - xiStar : ℝ) : ℂ))).re =
      cumulN x / kTip := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  let r₀ : ℝ := min (min pg.r_A (1 / 2)) (xiStar / 2)
  have hr₀_pos : 0 < r₀ := by
    have := pg.hr_A_pos; have := xiStar_pos; positivity
  let OmegaPos : Set ℂ := ball (xiStar : ℂ) r₀ ∩ {b : ℂ | 0 < b.im}
  have hΩ_open : IsOpen OmegaPos := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hΩ_slit : ∀ b ∈ OmegaPos, b ∈ slitStrip := by
    intro b hb
    refine ⟨?_, ?_⟩
    · have h1 : |b.im| ≤ ‖b - (xiStar : ℂ)‖ := by
        simpa [Complex.sub_im, Complex.ofReal_im] using Complex.abs_im_le_norm (b - (xiStar : ℂ))
      have h2 : ‖b - (xiStar : ℂ)‖ < r₀ := by simpa [mem_ball, dist_eq_norm] using hb.1
      have h3 : r₀ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
      have hbim : 0 < b.im := hb.2
      change |b.im| < 1 / 2
      rw [abs_of_pos hbim] at h1 ⊢
      linarith
    · intro ⟨him, _⟩; have hbim : 0 < b.im := hb.2; exact absurd him (ne_of_gt hbim)
  let Φ : ℂ → ℂ := fun b => -((KTip : ℂ) * ((xiStar : ℂ) - b) ^ (3 / 2 : ℂ) * pg.A (b - (xiStar : ℂ)))
  let Ψ : ℂ → ℂ := fun b => tipL b - Complex.I * majorantHolomorphic b
  have hΦ_diff : DifferentiableOn ℂ Φ OmegaPos := by
    intro b hb
    have hbim : 0 < b.im := hb.2
    have hsp : ((xiStar : ℂ) - b) ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right; simp [ne_of_gt hbim]
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((xiStar : ℂ) - z) ^ (3 / 2 : ℂ)) b :=
      (((differentiableAt_const _).sub differentiableAt_id).cpow (differentiableAt_const _) hsp)
    have hA_mem : b - (xiStar : ℂ) ∈ ball (0 : ℂ) pg.r_A := by
      have h2 : ‖b - (xiStar : ℂ)‖ < r₀ := by simpa [mem_ball, dist_eq_norm] using hb.1
      have h3 : r₀ ≤ pg.r_A := (min_le_left _ _).trans (min_le_left _ _)
      simpa [mem_ball, dist_zero_right] using h2.trans_le h3
    have h2 : DifferentiableAt ℂ (fun z : ℂ => pg.A (z - (xiStar : ℂ))) b :=
      (pg.hA_an _ hA_mem).differentiableAt.comp b (differentiableAt_id.sub (differentiableAt_const _))
    exact (((differentiableAt_const _).mul h1).mul h2).neg.differentiableWithinAt
  have hΨ_deriv : ∀ b ∈ OmegaPos,
      HasDerivAt Ψ (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap b)) b := by
    intro b hb
    have hb_slit := hΩ_slit b hb
    have hdL : HasDerivAt tipL ((2 * π / 3 : ℝ) : ℂ) b := by
      unfold tipL
      simpa using (hasDerivAt_id b).const_mul ((2 * π / 3 : ℝ) : ℂ)
    have hdM := (hasDerivAt_majorantHolomorphic hb_slit).const_mul Complex.I
    refine (hdL.sub hdM).congr_deriv ?_
    push_cast; ring
  have hΨ_diff : DifferentiableOn ℂ Ψ OmegaPos := fun b hb => (hΨ_deriv b hb).differentiableAt.differentiableWithinAt
  have hre_eq : ∀ b ∈ OmegaPos, (Ψ b - Φ b).re = 0 := by
    intro b hb
    have hb_rA : b ∈ ball (xiStar : ℂ) pg.r_A :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hb.1
    have hnot : ¬ (b.im = 0 ∧ xiStar ≤ b.re) := fun ⟨him, _⟩ => by
      have hbim : 0 < b.im := hb.2; exact absurd him (ne_of_gt hbim)
    have hU := pg.U_add_L_near_tip b hb_rA hnot
    rw [lemmaGPotentialInput_virasoro_U] at hU
    have hΨ_re : (Ψ b).re = (tipL b).re + majorant2D b := by
      dsimp [Ψ]; unfold majorant2D; simp [Complex.mul_re]
    have hΦ_re : (Φ b).re = majorant2D b + (tipL b).re := by
      dsimp [Φ]
      rw [← Complex.neg_re, show -((KTip : ℂ) * ((xiStar : ℂ) - b) ^ (3 / 2 : ℂ) * pg.A (b - (xiStar : ℂ))) =
          -(KTip : ℂ) * ((xiStar : ℂ) - b) ^ (3 / 2 : ℂ) * pg.A (b - (xiStar : ℂ)) by ring, ← hU]
    rw [Complex.sub_re, hΨ_re, hΦ_re]; ring
  have hΦ_deriv : ∀ b ∈ OmegaPos,
      HasDerivAt Φ (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap b)) b := by
    intro b hb
    have h0 := hasDerivAt_zero_of_re_zero hΩ_open (hΨ_diff.sub hΦ_diff) hre_eq hb
    have hΨb := hΨ_deriv b hb
    simpa using hΨb.sub h0
  -- Integrate on `[xiStar + δ, x]` at height `y > 0`
  have h_ftc : ∀ δ ∈ Ioo (0 : ℝ) (x - xiStar),
      -Complex.I * ((KTip : ℂ) * (((x - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          pg.A (((x - xiStar : ℝ) : ℂ))) -
        (-Complex.I * ((KTip : ℂ) * ((δ ^ (3 / 2 : ℝ) : ℝ) : ℂ) * pg.A ((δ : ℝ) : ℂ))) =
        -Complex.I * ((π * ∫ t in (xiStar + δ)..x, rhoU t : ℝ) : ℂ) := by
    intro δ hδ
    have hx_sub_pos : 0 < x - xiStar := by linarith
    have hx_sub_lt : x - xiStar < r₀ := by linarith
    let y₀ : ℝ := Real.sqrt (r₀ ^ 2 - (x - xiStar) ^ 2) / 2
    have hy₀_pos : 0 < y₀ := by
      have : (x - xiStar) ^ 2 < r₀ ^ 2 := sq_lt_sq' (by linarith) hx_sub_lt
      positivity
    have h_eq_y : ∀ y ∈ Ioo (0 : ℝ) y₀,
        Φ ((x : ℂ) + (y : ℂ) * Complex.I) - Φ (((xiStar + δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
          ∫ t in (xiStar + δ)..x,
            ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I)) := by
      intro y hy
      have hmem_seg : ∀ t ∈ uIcc (xiStar + δ) x, (t : ℂ) + (y : ℂ) * Complex.I ∈ OmegaPos := by
        intro t ht
        rw [uIcc_of_le (by linarith [hδ.2])] at ht
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_eq_norm, Complex.norm_def, Real.sqrt_lt' hr₀_pos]
          have hnormSq : Complex.normSq ((t : ℂ) + (y : ℂ) * Complex.I - (xiStar : ℂ)) =
              (t - xiStar) ^ 2 + y ^ 2 := by
            simp [Complex.normSq_apply]; ring
          rw [hnormSq]
          have ht1 : (t - xiStar) ^ 2 ≤ (x - xiStar) ^ 2 :=
            sq_le_sq' (by linarith [ht.1, hδ.1]) (by linarith [ht.2])
          have hy1 : y ^ 2 < r₀ ^ 2 - (x - xiStar) ^ 2 := by
            have hysq : y ^ 2 < y₀ ^ 2 := sq_lt_sq' (by linarith [hy.1]) hy.2
            have hy₀sq : y₀ ^ 2 = (r₀ ^ 2 - (x - xiStar) ^ 2) / 4 := by
              dsimp [y₀]; rw [div_pow, Real.sq_sqrt (by nlinarith [sq_lt_sq' (by linarith) hx_sub_lt])]; norm_num
            nlinarith [hy₀sq]
          linarith
        · simp [hy.1]
      have hderiv_seg : ∀ t ∈ uIcc (xiStar + δ) x,
          HasDerivAt (fun s : ℝ => Φ ((s : ℂ) + (y : ℂ) * Complex.I))
            (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I))) t := by
        intro t ht
        have hc : HasDerivAt (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) 1 t := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((y : ℂ) * Complex.I)
        have hΦ' := (hΦ_deriv _ (hmem_seg t ht)).hasFDerivAt.restrictScalars ℝ
        simpa [Function.comp_def] using hΦ'.comp_hasDerivAt t hc
      have hint_seg : IntervalIntegrable
          (fun t : ℝ => ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I)))
          volume (xiStar + δ) x := by
        refine ContinuousOn.intervalIntegrable ?_
        intro t ht
        have hbt := hmem_seg t ht
        have h_an : ContinuousAt pMap ((t : ℂ) + (y : ℂ) * Complex.I) :=
          differentiableOn_pMap_slitStrip.continuousOn.continuousAt
            (isOpen_slitStrip.mem_nhds (hΩ_slit _ hbt))
        have hdp : ContinuousAt (fun z : ℂ => ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap z))
            ((t : ℂ) + (y : ℂ) * Complex.I) :=
          continuousAt_const.mul (continuousAt_const.sub (continuousAt_const.mul h_an))
        exact (hdp.comp_of_eq (by fun_prop : Continuous fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I).continuousAt
          rfl).continuousWithinAt
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_seg hint_seg).symm
    -- Take `y → 0⁺` on LHS
    have hΦ_lim : ∀ t ∈ Ioo xiStar (xiStar + r₀),
        Tendsto (fun y : ℝ => Φ ((t : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
          (𝓝 (-Complex.I * ((KTip : ℂ) * (((t - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
            pg.A (((t - xiStar : ℝ) : ℂ))))) := by
      intro t ht
      have ht_pos : 0 < t - xiStar := by linarith [ht.1]
      have h1 : Tendsto (fun y : ℝ => ((xiStar : ℂ) - ((t : ℂ) + (y : ℂ) * Complex.I)) ^ (3 / 2 : ℂ))
          (𝓝[>] 0) (𝓝 (Complex.I * (((t - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by
        have h0 := cpow_three_halves_neg_sub_I_tendsto ht_pos
        refine h0.congr (fun y => ?_)
        congr 1; push_cast; ring
      have hA_mem : ((t - xiStar : ℝ) : ℂ) ∈ ball (0 : ℂ) pg.r_A := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
        exact (by linarith [ht.2] : t - xiStar < r₀).trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have h2 : Tendsto (fun y : ℝ => pg.A (((t : ℂ) + (y : ℂ) * Complex.I) - (xiStar : ℂ)))
          (𝓝[>] 0) (𝓝 (pg.A (((t - xiStar : ℝ) : ℂ)))) := by
        have hlim : Tendsto (fun y : ℝ => ((t : ℂ) + (y : ℂ) * Complex.I) - (xiStar : ℂ))
            (𝓝[>] 0) (𝓝 (((t - xiStar : ℝ) : ℂ))) := by
          have h0 : ((t - xiStar : ℝ) : ℂ) = ((t : ℂ) + (0 : ℂ) * Complex.I) - (xiStar : ℂ) := by
            push_cast; ring
          rw [h0]
          exact (tendsto_const_nhds.add ((Complex.continuous_ofReal.continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds).mul tendsto_const_nhds)).sub_const _
        exact (pg.hA_an _ hA_mem).continuousAt.tendsto.comp hlim
      have hcomb := ((tendsto_const_nhds (x := (KTip : ℂ))).mul h1).mul h2 |>.neg
      convert hcomb using 1
      ring
    have hLHS := (hΦ_lim x ⟨hx_gt, by linarith⟩).sub
      (hΦ_lim (xiStar + δ) ⟨by linarith [hδ.1], by linarith [hδ.2]⟩)
    -- Take `y → 0⁺` on RHS by dominated convergence
    have hRHS : Tendsto (fun y : ℝ => ∫ t in (xiStar + δ)..x,
          ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I)))
        (𝓝[>] 0) (𝓝 (-Complex.I * ((π * ∫ t in (xiStar + δ)..x, rhoU t : ℝ) : ℂ))) := by
      have h_eq_int : -Complex.I * ((π * ∫ t in (xiStar + δ)..x, rhoU t : ℝ) : ℂ) =
          ∫ t in (xiStar + δ)..x, -Complex.I * ((π * rhoU t : ℝ) : ℂ) := by
        rw [show -Complex.I * ((π * ∫ t in (xiStar + δ)..x, rhoU t : ℝ) : ℂ) =
            (-Complex.I * (π : ℂ)) * ((∫ t in (xiStar + δ)..x, rhoU t : ℝ) : ℂ) by push_cast; ring,
          ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
        congr 1; ext t; push_cast; ring
      rw [h_eq_int]
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (bound := fun _ => (2 * π / 3) * (1 + 2 * (|x| + 2))) ?_ ?_ ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hy₀_pos] with y hy
        refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_uIoc
        rw [uIoc_of_le (by linarith [hδ.2])] at ht
        have hbt : (t : ℂ) + (y : ℂ) * Complex.I ∈ slitStrip := by
          refine ⟨?_, ?_⟩
          · have hy_lt : y < 1 / 2 := hy.2.trans (by
              have : y₀ ≤ r₀ / 2 := by
                dsimp [y₀]
                have h1 : Real.sqrt (r₀ ^ 2 - (x - xiStar) ^ 2) ≤ r₀ :=
                  Real.sqrt_le_iff.mpr ⟨hr₀_pos.le, by nlinarith [sq_nonneg (x - xiStar)]⟩
                linarith
              have hr₀_half : r₀ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
              linarith)
            simpa [abs_of_pos hy.1] using hy_lt
          · intro ⟨him, _⟩; simp at him; linarith [hy.1]
        have h_an : ContinuousAt pMap ((t : ℂ) + (y : ℂ) * Complex.I) :=
          differentiableOn_pMap_slitStrip.continuousOn.continuousAt
            (isOpen_slitStrip.mem_nhds hbt)
        have hdp : ContinuousAt (fun z : ℂ => ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap z))
            ((t : ℂ) + (y : ℂ) * Complex.I) :=
          continuousAt_const.mul (continuousAt_const.sub (continuousAt_const.mul h_an))
        exact (hdp.comp_of_eq (by fun_prop : Continuous fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I).continuousAt
          rfl).continuousWithinAt
      · filter_upwards [Ioo_mem_nhdsGT hy₀_pos] with y hy
        refine ae_of_all _ fun t ht => ?_
        rw [uIoc_of_le (by linarith [hδ.2])] at ht
        have hbt : (t : ℂ) + (y : ℂ) * Complex.I ∈ slitStrip := by
          refine ⟨?_, ?_⟩
          · have hy_lt : y < 1 / 2 := hy.2.trans (by
              have : y₀ ≤ r₀ / 2 := by
                dsimp [y₀]
                have h1 : Real.sqrt (r₀ ^ 2 - (x - xiStar) ^ 2) ≤ r₀ :=
                  Real.sqrt_le_iff.mpr ⟨hr₀_pos.le, by nlinarith [sq_nonneg (x - xiStar)]⟩
                linarith
              have hr₀_half : r₀ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
              linarith)
            simpa [abs_of_pos hy.1] using hy_lt
          · intro ⟨him, _⟩; simp at him; linarith [hy.1]
        have hp_re := pMap_re_abs_le hbt
        have hp_im := pMap_im_abs_le_half hbt
        have ht_abs : |((t : ℂ) + (y : ℂ) * Complex.I).re| ≤ |x| := by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
          rw [abs_of_pos (by linarith [xiStar_pos, hδ.1, ht.1]), abs_of_pos (by linarith [xiStar_pos])]
          exact ht.2
        have hp_norm : ‖pMap ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ |x| + 2 := by
          have := Complex.norm_le_abs_re_add_abs_im (pMap ((t : ℂ) + (y : ℂ) * Complex.I))
          linarith
        calc ‖((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I))‖
            = (2 * π / 3) * ‖1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I)‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity [Real.pi_pos])]
          _ ≤ (2 * π / 3) * (1 + 2 * (|x| + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity [Real.pi_pos])
              calc ‖1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I)‖
                  ≤ ‖(1 : ℂ)‖ + ‖2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I)‖ := norm_sub_le _ _
                _ = 1 + 2 * ‖pMap ((t : ℂ) + (y : ℂ) * Complex.I)‖ := by
                    rw [norm_one, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
                _ ≤ 1 + 2 * (|x| + 2) := by linarith
      · exact intervalIntegrable_const
      · refine ae_of_all _ fun t ht => ?_
        rw [uIoc_of_le (by linarith [hδ.2])] at ht
        have ht_gt : xiStar < t := by linarith [hδ.1, ht.1]
        have hp_lim := tendsto_pMap_slit_right_full ht_gt
        have h1 := ((tendsto_const_nhds (x := (2 * Complex.I))).mul hp_lim)
        have h2 := (tendsto_const_nhds (x := (1 : ℂ))).sub h1
        have h3 := (tendsto_const_nhds (x := ((2 * π / 3 : ℝ) : ℂ))).mul h2
        rw [show -Complex.I * ((π * rhoU t : ℝ) : ℂ) =
            ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * (((3 / 4 : ℝ) : ℂ) * (rhoU t : ℂ) - (1 / 2 : ℂ) * Complex.I)) by
          push_cast; ring_nf; rw [Complex.I_sq]; ring]
        exact h3
    simp only [add_sub_cancel_left] at hLHS
    have hLHS_eq : Tendsto (fun y : ℝ => ∫ t in (xiStar + δ)..x,
          ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((t : ℂ) + (y : ℂ) * Complex.I)))
        (𝓝[>] 0)
        (𝓝 (-Complex.I * ((KTip : ℂ) * (((x - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
            pg.A (((x - xiStar : ℝ) : ℂ))) -
          (-Complex.I * ((KTip : ℂ) * ((δ ^ (3 / 2 : ℝ) : ℝ) : ℂ) * pg.A ((δ : ℝ) : ℂ))))) :=
      hLHS.congr' (by filter_upwards [Ioo_mem_nhdsGT hy₀_pos] with y hy; exact h_eq_y y hy)
    exact tendsto_nhds_unique hLHS_eq hRHS
  -- Take `δ → 0⁺`
  have hδ_lhs : Tendsto (fun δ : ℝ =>
      -Complex.I * ((KTip : ℂ) * (((x - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          pg.A (((x - xiStar : ℝ) : ℂ))) -
        (-Complex.I * ((KTip : ℂ) * ((δ ^ (3 / 2 : ℝ) : ℝ) : ℂ) * pg.A ((δ : ℝ) : ℂ))))
      (𝓝[>] 0)
      (𝓝 (-Complex.I * ((KTip : ℂ) * (((x - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          pg.A (((x - xiStar : ℝ) : ℂ))))) := by
    have h0 : Tendsto (fun δ : ℝ => ((δ ^ (3 / 2 : ℝ) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun δ : ℝ => δ ^ (3 / 2 : ℝ)) 0 :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).continuousAt
      have h0' : Tendsto (fun δ : ℝ => ((δ ^ (3 / 2 : ℝ) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (((0 ^ (3 / 2 : ℝ) : ℝ) : ℂ))) :=
        (Complex.continuous_ofReal.continuousAt.tendsto.comp (hc.tendsto.mono_left nhdsWithin_le_nhds))
      simpa using h0'
    have hA0 : Tendsto (fun δ : ℝ => pg.A ((δ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (pg.A 0)) :=
      (pg.hA_an 0 (mem_ball_self pg.hr_A_pos)).continuousAt.tendsto.comp
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hterm : Tendsto (fun δ : ℝ =>
        -Complex.I * ((KTip : ℂ) * ((δ ^ (3 / 2 : ℝ) : ℝ) : ℂ) * pg.A ((δ : ℝ) : ℂ)))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_const_nhds.mul h0).mul hA0).const_mul (-Complex.I)
    simpa using tendsto_const_nhds.sub hterm
  have hδ_rhs : Tendsto (fun δ : ℝ =>
      -Complex.I * ((π * ∫ t in (xiStar + δ)..x, rhoU t : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (-Complex.I * ((2 * π * cumulN x : ℝ) : ℂ))) := by
    have h_diff : ∀ δ ∈ Ioo (0 : ℝ) (x - xiStar),
        ∫ t in (xiStar + δ)..x, rhoU t =
          (∫ t in xiStar..x, rhoU t) - ∫ t in xiStar..(xiStar + δ), rhoU t := by
      intro δ hδ
      have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := xiStar) (b := xiStar + δ) (c := x)
        ((continuousOn_rhoU.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc (μ := volume)
          (by linarith [hδ.1]))
        ((continuousOn_rhoU.mono (Set.Subset.trans (Icc_subset_Icc_left (by linarith [hδ.1])) Icc_subset_Ici_self)).intervalIntegrable_of_Icc (μ := volume)
          (by linarith [hδ.2]))
      linarith
    have h_small : Tendsto (fun δ : ℝ => ∫ t in xiStar..(xiStar + δ), rhoU t) (𝓝[>] 0) (𝓝 0) := by
      have h_mul : Tendsto (fun δ : ℝ => δ * rhoU x) (𝓝 0) (𝓝 0) := by
        have hc : ContinuousAt (fun δ : ℝ => δ * rhoU x) 0 := by fun_prop
        simpa using hc.tendsto
      refine squeeze_zero' ?_ ?_ (tendsto_nhdsWithin_of_tendsto_nhds h_mul)
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - xiStar by linarith)] with δ hδ
        exact intervalIntegral.integral_nonneg (by linarith [hδ.1]) fun t _ => rhoU_nonneg t
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - xiStar by linarith)] with δ hδ
        have hle : ∀ t ∈ uIcc xiStar (xiStar + δ), rhoU t ≤ rhoU x := by
          intro t ht
          rw [uIcc_of_le (by linarith [hδ.1])] at ht
          exact rhoU_strictMonoOn.monotoneOn (Set.mem_Ici.mpr ht.1) (Set.mem_Ici.mpr hx_gt.le)
            (by linarith [ht.2, hδ.2])
        have hint : IntervalIntegrable rhoU volume xiStar (xiStar + δ) :=
          (continuousOn_rhoU.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc
            (by linarith [hδ.1])
        calc ∫ t in xiStar..(xiStar + δ), rhoU t
            ≤ ∫ _ in xiStar..(xiStar + δ), rhoU x :=
              intervalIntegral.integral_mono_on (by linarith [hδ.1]) hint intervalIntegrable_const
                fun t ht => hle t (by rwa [uIcc_of_le (by linarith [hδ.1])])
          _ = δ * rhoU x := by simp [intervalIntegral.integral_const]
    have hint_tend : Tendsto (fun δ : ℝ => ∫ t in (xiStar + δ)..x, rhoU t) (𝓝[>] 0)
        (𝓝 (2 * cumulN x)) := by
      have hsub := tendsto_const_nhds (x := ∫ t in xiStar..x, rhoU t) |>.sub h_small
      have hcum : ∫ t in xiStar..x, rhoU t = 2 * cumulN x := by unfold cumulN; ring
      rw [hcum, sub_zero] at hsub
      exact hsub.congr' (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - xiStar by linarith)] with δ hδ
        rw [← hcum]; exact (h_diff δ hδ).symm)
    have hlim := ((tendsto_const_nhds (x := π)).mul hint_tend)
    have hc_lim := (Complex.continuous_ofReal.continuousAt.tendsto.comp hlim).const_mul (-Complex.I)
    rw [show -Complex.I * ((2 * π * cumulN x : ℝ) : ℂ) =
        -Complex.I * ((π * (2 * cumulN x) : ℝ) : ℂ) by push_cast; ring]
    exact hc_lim
  have hδ_lhs' : Tendsto (fun δ : ℝ => -Complex.I * ((π * ∫ t in (xiStar + δ)..x, rhoU t : ℝ) : ℂ))
      (𝓝[>] 0)
      (𝓝 (-Complex.I * ((KTip : ℂ) * (((x - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        pg.A (((x - xiStar : ℝ) : ℂ))))) :=
    hδ_lhs.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - xiStar by linarith)] with δ hδ
      exact h_ftc δ hδ)
  have heq_c := tendsto_nhds_unique hδ_lhs' hδ_rhs
  have hmul_I := congrArg (fun z : ℂ => Complex.I * z) heq_c
  have hre := congrArg Complex.re hmul_I
  have hK_eq : KTip = 2 * π * kTip := rfl
  have hx_abs : |x - xiStar| < pg.r_A := by
    rw [abs_of_pos (by linarith)]
    exact (by linarith : x - xiStar < r₀).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hA_im : (pg.A (((x - xiStar : ℝ) : ℂ))).im = 0 := pg.hA_real _ hx_abs
  have hA_eq : pg.A (((x - xiStar : ℝ) : ℂ)) = ((pg.A (((x - xiStar : ℝ) : ℂ))).re : ℂ) :=
    Complex.ext rfl hA_im
  have hre_l : (Complex.I * (-Complex.I * ((KTip : ℂ) * (((x - xiStar) ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      pg.A (((x - xiStar : ℝ) : ℂ))))).re =
      KTip * ((x - xiStar) ^ (3 / 2 : ℝ) * (pg.A (((x - xiStar : ℝ) : ℂ))).re) := by
    rw [hA_eq, ← mul_assoc, show Complex.I * -Complex.I = (1 : ℂ) by rw [mul_neg, Complex.I_mul_I, neg_neg],
      one_mul]
    push_cast; simp; ring
  have hre_r : (Complex.I * (-Complex.I * ((2 * π * cumulN x : ℝ) : ℂ))).re = 2 * π * cumulN x := by
    rw [← mul_assoc, show Complex.I * -Complex.I = (1 : ℂ) by rw [mul_neg, Complex.I_mul_I, neg_neg],
      one_mul, Complex.ofReal_re]
  rw [hre_l, hre_r, hK_eq] at hre
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity [Real.pi_pos]
  have hk_ne : kTip ≠ 0 := kTip_pos.ne'
  have hre' : (2 * π * kTip) * ((x - xiStar) ^ (3 / 2 : ℝ) * (pg.A (((x - xiStar : ℝ) : ℂ))).re) =
      (2 * π * kTip) * (cumulN x / kTip) := by
    calc (2 * π * kTip) * ((x - xiStar) ^ (3 / 2 : ℝ) * (pg.A (((x - xiStar : ℝ) : ℂ))).re)
        = (2 * π * kTip) * ((x - xiStar) ^ (3 / 2 : ℝ) * (pg.A (((x - xiStar : ℝ) : ℂ))).re) := rfl
      _ = 2 * π * cumulN x := hre
      _ = (2 * π * kTip) * (cumulN x / kTip) := by field_simp [hk_ne]
  exact mul_left_cancel₀ (mul_ne_zero h2pi hk_ne) hre'

/-! ### 3. Main theorem: `LowerLangerPhase` holds unconditionally -/

/-- **Exact Langer bridge (`cts:langer`, `rem:s1`, `cts:phaselock`):**
for all sufficiently large `c` and all `u ∈ [-(|a_1| + 1), 0)`,
`tauPhase (√(3 * virasoroDeltaChart c u / c)) = -u / (betaTip * c ^ (2 / 3 : ℝ))`. -/
theorem lowerLangerPhase_holds : LowerLangerPhase := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  let r₀ : ℝ := min (min pg.r_A (1 / 2)) (xiStar / 2)
  have hr₀_pos : 0 < r₀ := by have := pg.hr_A_pos; have := xiStar_pos; positivity
  let r_ξ : ℝ := min virasoroRXiInf ((xiStar + r₀) ^ 2 / 3 - xiBar)
  have hr_ξ_pos : 0 < r_ξ := by
    have h1 : 0 < virasoroRXiInf := virasoroRXiInf_pos
    have h2 : xiBar < (xiStar + r₀) ^ 2 / 3 := by
      unfold xiBar
      have : xiStar ^ 2 < (xiStar + r₀) ^ 2 := sq_lt_sq' (by linarith [xiStar_pos]) (by linarith)
      linarith
    exact lt_min h1 (by linarith)
  have hcont_xi : ContinuousAt virasoroXiInf 0 :=
    (langerCore.hxiInf_an 0 (mem_ball_self virasoroRUInf_pos)).continuousAt
  obtain ⟨δ_u, hδ_u_pos, hδ_u⟩ := Metric.continuousAt_iff.mp hcont_xi r_ξ hr_ξ_pos
  let δ : ℝ := min δ_u virasoroRUInf
  have hδ_pos : 0 < δ := lt_min hδ_u_pos virasoroRUInf_pos
  have hBV := virasoroBV_pos
  have hev : ∀ᶠ c : ℝ in atTop,
      0 < c ∧
      (|airyZero 1| + 1) * c ^ (-(2 / 3 : ℝ)) < δ ∧
      |airyZero 1| + 1 ≤ 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := by
    have hcm : Tendsto (fun c : ℝ => (|airyZero 1| + 1) * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul (|airyZero 1| + 1)
    have hc23 : Tendsto (fun c : ℝ => 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (by positivity)
    filter_upwards [eventually_gt_atTop (0 : ℝ), hcm.eventually (gt_mem_nhds hδ_pos),
      hc23.eventually_ge_atTop (|airyZero 1| + 1)] with c hc0 h1 h2
    exact ⟨hc0, h1, h2⟩
  obtain ⟨cb, hcb⟩ := eventually_atTop.1 hev
  refine ⟨cb, fun c hc u hu1 hu2 => ?_⟩
  obtain ⟨hc0, hu_δ, hA2_ge⟩ := hcb c hc
  set w : ℝ := u * c ^ (-(2 / 3 : ℝ)) with hw_def
  have hw_abs : |w| < δ := by
    rw [hw_def, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    have hu_abs : |u| ≤ |airyZero 1| + 1 := abs_le.mpr ⟨hu1, by linarith [abs_nonneg (airyZero 1)]⟩
    exact (mul_le_mul_of_nonneg_right hu_abs (Real.rpow_nonneg hc0.le _)).trans_lt hu_δ
  have hw_ball : (w : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hw_abs.trans_le (min_le_right _ _)
  have hξ_im : (virasoroXiInf (w : ℂ)).im = 0 :=
    virasoroXiInf_ofReal_im (hw_abs.trans_le (min_le_right _ _))
  set ξ : ℝ := (virasoroXiInf (w : ℂ)).re with hξ_def
  have hξ_c : (ξ : ℂ) = virasoroXiInf (w : ℂ) := Complex.ext rfl hξ_im.symm
  have hΔ_eq : virasoroDeltaChart c u / c = ξ := by
    unfold virasoroDeltaChart virasoroXiChartC
    rw [← Complex.ofReal_mul, ← hw_def, ← hξ_def]
    field_simp [hc0.ne']
  rw [mul_div_assoc, hΔ_eq]
  have hu_inv : virasoroUInf (ξ : ℂ) = (w : ℂ) := by
    rw [hξ_c]; exact virasoroUInf_xiInf hw_ball
  -- `ξ > xiBar` since `virasoroDeltaChart c` is strictly antitone on `[-A2, A2]` and `u < 0`
  set A2 : ℝ := virasoroAC c ^ 2
  have hA2_eq : A2 = 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := virasoroAC_sq c hc0.le
  have hsA : StrictAntiOn (virasoroDeltaChart c) (Icc (-A2) A2) := virasoroDeltaChart_strictAnti hc0
  have hu_mem : u ∈ Icc (-A2) A2 := ⟨by linarith [hA2_eq], by linarith [sq_nonneg (virasoroAC c)]⟩
  have h0_mem : (0 : ℝ) ∈ Icc (-A2) A2 := ⟨by linarith [sq_nonneg (virasoroAC c)], by positivity⟩
  have hΔ_gt : virasoroDeltaChart c 0 < virasoroDeltaChart c u := hsA hu_mem h0_mem hu2
  rw [virasoroDeltaChart_zero] at hΔ_gt
  have hξ_gt : xiBar < ξ := by
    rw [← hΔ_eq, lt_div_iff₀ hc0]
    exact hΔ_gt
  have hξ_dist : |ξ - xiBar| < r_ξ := by
    have hnorm : dist (virasoroXiInf (w : ℂ)) (xiBar : ℂ) < r_ξ := by
      rw [← virasoroXiInf_zero]
      refine hδ_u ?_
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact hw_abs.trans_le (min_le_left _ _)
    rw [← hξ_c, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  have hξ_pos : 0 < ξ := by
    have := xiStar_pos; unfold xiBar at hξ_gt
    nlinarith [sq_nonneg xiStar, hξ_gt]
  set x : ℝ := Real.sqrt (3 * ξ) with hx_def
  have hx_gt : xiStar < x := by
    rw [hx_def, Real.lt_sqrt xiStar_pos.le]
    unfold xiBar at hξ_gt
    linarith
  have hx_lt : x < xiStar + r₀ := by
    rw [hx_def, Real.sqrt_lt' (by positivity [xiStar_pos])]
    have h1 : ξ - xiBar < (xiStar + r₀) ^ 2 / 3 - xiBar :=
      (le_abs_self _).trans_lt (hξ_dist.trans_le (min_le_right _ _))
    linarith
  have hcum := tip_potential_cumulN_eq hx_gt hx_lt
  have hcum_pos : 0 < cumulN x := by
    have h1 := cumulN_strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx_gt.le) hx_gt
    rwa [cumulN_xiStar] at h1
  have hA_re_pos : 0 < (pg.A (((x - xiStar : ℝ) : ℂ))).re := by
    have hlhs_pos : 0 < (x - xiStar) ^ (3 / 2 : ℝ) * (pg.A (((x - xiStar : ℝ) : ℂ))).re := by
      rw [hcum]; exact div_pos hcum_pos kTip_pos
    exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos (by linarith) _)).mp hlhs_pos
  have hx_abs : |x - xiStar| < pg.r_A := by
    rw [abs_of_pos (by linarith)]
    exact (by linarith : x - xiStar < r₀).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hA_im : (pg.A (((x - xiStar : ℝ) : ℂ))).im = 0 := pg.hA_real _ hx_abs
  have hA_c : pg.A (((x - xiStar : ℝ) : ℂ)) = ((pg.A (((x - xiStar : ℝ) : ℂ))).re : ℂ) :=
    Complex.ext rfl hA_im
  have hA_cpow : (pg.A (((x - xiStar : ℝ) : ℂ))) ^ (2 / 3 : ℂ) =
      (((pg.A (((x - xiStar : ℝ) : ℂ))).re ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
    conv_lhs => rw [hA_c]
    rw [show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hA_re_pos.le]
  have hu_re := congrArg Complex.re hu_inv
  have hb_eq : virasoroBOfXi (ξ : ℂ) = (x : ℂ) := virasoroBOfXi_ofReal hξ_pos.le
  have hu_val : (virasoroUInf (ξ : ℂ)).re =
      -betaTip * ((x - xiStar) * (pg.A (((x - xiStar : ℝ) : ℂ))).re ^ (2 / 3 : ℝ)) := by
    unfold virasoroUInf
    dsimp only
    simp_rw [hb_eq, ← Complex.ofReal_sub]
    dsimp only [pg] at hA_cpow
    rw [hA_cpow]
    push_cast; simp; ring
  rw [hu_val, Complex.ofReal_re] at hu_re
  have htau_eq : (x - xiStar) * (pg.A (((x - xiStar : ℝ) : ℂ))).re ^ (2 / 3 : ℝ) = tauPhase x := by
    unfold tauPhase
    rw [← hcum, Real.mul_rpow (Real.rpow_nonneg (by linarith) _) hA_re_pos.le,
      ← Real.rpow_mul (by linarith)]
    norm_num
  rw [htau_eq] at hu_re
  have hβ := betaTip_pos
  have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 (2 / 3)
  have hc23_eq : c ^ (-(2 / 3 : ℝ)) = (c ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hc0.le (2 / 3)
  rw [hw_def, hc23_eq] at hu_re
  rw [eq_div_iff (mul_ne_zero hβ.ne' hc23_pos.ne')]
  have hmul : tauPhase x * (betaTip * c ^ (2 / 3 : ℝ)) = -((-betaTip * tauPhase x) * c ^ (2 / 3 : ℝ)) := by ring
  rw [hmul, hu_re]
  field_simp [hc23_pos.ne']

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerLangerPhase_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerLangerPhase_holds

