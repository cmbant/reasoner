module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualIdRight

/-!
# The Cauchy Dual Identity (`cts:dual-id`, `cts:cauchy-dual` Step 1)

Unwraps the `η = 0` Cauchy strip identity `lowerDual_contour_eq` (`LowerDualContour`)
into `virasoro_dual_id` (`cts:dual-id`): for `c' ≥ c₀`, `ε ∈ (0, 1/2)`, and nonzero
`g ∈ TestClass virasoroProblem (c'/12)`:

  `∫_{t(ξ_*)}^∞ (g(t) V(t) / M[g]) (1 - V₁(x)/(c'(1 - e^{-4πx})²)) W̃_ε(y) sin(θ̃_ε(y) - 2π c' N(x)) dt`
  `+ ∫_{t(ξ_*/2)}^∞ (g(t') V(t') / M[g]) [(1 - V₁(x')/(c'(1 - e^{-4πx'})²)) K_edge^ε(x'; c')`
  `+ 3/(16π x' c') K_{edge,1}^ε(x'; c')] dt'`
  `= O(c'^{-2} + c'^{-3/2} log(2/ε))`.

Here `x = √(3 t / c')`, `x' = √(3 t' / c')`, `y = lowerY x`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

/-! ### 1. Elementary bounds & weighted `L¹` bound on `(ξ_*/2, ∞)` -/

private lemma one_sub_exp_sq_ge_quarter {x' : ℝ} (hx' : xiStar / 2 ≤ x') :
    1 / 4 ≤ (1 - Real.exp (-4 * π * x')) ^ 2 := by
  have hx'1 : (1 : ℝ) / 10 ≤ x' := by linarith [Bessel.one_fifth_le_xiStar]
  have h4x : 1 ≤ 4 * π * x' := by nlinarith [Real.pi_gt_three]
  have hexp_le : Real.exp (-4 * π * x') ≤ 1 / 2 := by
    rw [show -4 * π * x' = -(4 * π * x') by ring, Real.exp_neg]
    calc (Real.exp (4 * π * x'))⁻¹ ≤ (1 + 4 * π * x')⁻¹ :=
          inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (4 * π * x')])
      _ ≤ 2⁻¹ := inv_anti₀ zero_lt_two (by linarith)
      _ = 1 / 2 := by norm_num
  nlinarith

private lemma kedgeEpsIntegrand_vT_norm_le {c' ε x' τ : ℝ} (_hε : ε ∈ Ioo (0 : ℝ) (1 / 2))
    (hx' : xiStar / 2 ≤ x') (hτ : 0 ≤ τ) :
    ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ ≤
      4 * lowerWeps ε (Real.tanh (π * τ / 4)) := by
  rcases hτ.eq_or_lt with rfl | _
  · rw [vT_zero, show Real.tanh (π * 0 / 4) = 0 by simp]
    have hk0 : kedgeEpsIntegrand c' ε x' 0 = 0 := by
      unfold kedgeEpsIntegrand
      have hF'0 : edgeF' 0 = 0 := by unfold edgeF'; simp
      simp [hF'0]
    rw [hk0, zero_mul, norm_zero]
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  · have hq4' : 1 / 4 ≤ (1 - Real.exp (-(4 * π * x'))) ^ 2 := by
      rw [show -(4 * π * x') = -4 * π * x' by ring]; exact one_sub_exp_sq_ge_quarter hx'
    have hmt_n : ‖lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2‖ =
        lowerWeps ε (Real.tanh (π * τ / 4)) := by rw [norm_pow]; rfl
    have hF'_le1 : edgeF' (vT τ) ≤ 1 := by
      unfold edgeF'
      exact div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (by linarith [Real.cosh_sq (π * vT τ)])) (Real.sqrt_nonneg _)
    have hsub1 : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 ≤ 1 := by
      have : 0 ≤ Real.exp (-(4 * π * xT τ)) := (Real.exp_pos _).le
      have : Real.exp (-(4 * π * xT τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, xT_pos τ])
      nlinarith
    rw [kedgeEpsIntegrand_vT hτ, norm_mul, norm_mul, norm_mul, norm_mul, hmt_n,
      show Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ) =
        (thetaOut (Real.tanh (π * τ / 4)) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one,
      show Complex.I * ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ) =
        ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Complex.norm_real, Real.norm_of_nonneg (vD_pos τ).le]
    have hW_nn : 0 ≤ lowerWeps ε (Real.tanh (π * τ / 4)) := sq_nonneg _
    have hfac : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
        √(edgeF' (vT τ)) * vD τ ≤ 4 := by
      calc _ ≤ (1 / (1 / 4 : ℝ)) * 1 * 1 := mul_le_mul
            (mul_le_mul (div_le_div₀ zero_le_one hsub1 (by norm_num) hq4')
              (Real.sqrt_le_one.mpr hF'_le1) (Real.sqrt_nonneg _) (by norm_num))
            (vD_le_one τ) (vD_pos τ).le (by norm_num)
        _ = 4 := by norm_num
    nlinarith

private lemma norm_inv_one_sub_two_I_mul_le (v : ℝ) :
    ‖((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hge1 : 1 ≤ ‖(1 : ℂ) - 2 * Complex.I * (v : ℂ)‖ := by
    rw [show (1 : ℂ) - 2 * Complex.I * (v : ℂ) = (1 : ℝ) + ((-2 * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_add_mul_I]
    exact Real.one_le_sqrt.mpr (by nlinarith)
  exact inv_le_one_of_one_le₀ hge1

private lemma integrableOn_Ioi_half_abs {c' : ℝ} (hc' : 0 < c') (ha : 2 ≤ c' / 12)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g) :
    IntegrableOn (fun x' : ℝ =>
      |g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3))
      (Ioi (xiStar / 2)) ∧
    ∫ x' in Ioi (xiStar / 2),
      |g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3) ≤
        virasoroProblem.cardyNorm (c' / 12) g := by
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by rw [virasoroProblem_totalShift]; linarith
  have hV_int : IntegrableOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (Ioi 0) :=
    hg.int_cardy.congr_fun (fun t ht => by
      dsimp only; rw [Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]) measurableSet_Ioi
  have hM_eq : ∫ t in Ioi (0 : ℝ), |g t| * Bessel.besselV (c' / 12) t =
      virasoroProblem.cardyNorm (c' / 12) g := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
  have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
    (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
      (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
  let φ : ℝ → ℝ := fun x' => c' * x' ^ 2 / 3
  let φ' : ℝ → ℝ := fun x' => 2 * c' * x' / 3
  have hcont : Continuous fun x' => |g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x' := by
    have hφ_c : Continuous φ := (continuous_const.mul (continuous_id.pow 2)).div_const 3
    have hφ'_c : Continuous φ' := (continuous_const.mul continuous_id).div_const 3
    exact ((hg.cont.abs.comp_continuous hφ_c fun _ => show 0 ≤ φ _ by dsimp [φ]; positivity).mul
      (hV_cont.comp_continuous hφ_c fun _ => show 0 ≤ φ _ by dsimp [φ]; positivity)).mul hφ'_c
  have hcov_R : ∀ R : ℝ, xiStar / 2 ≤ R →
      ∫ x' in (xiStar / 2)..R, |g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x' =
        ∫ t' in (φ (xiStar / 2))..(φ R), |g t'| * Bessel.besselV (c' / 12) t' := fun R _ => by
    have hd : ∀ x' ∈ uIcc (xiStar / 2) R, HasDerivAt φ (φ' x') x' := fun x' _ => by
      dsimp [φ, φ']; exact ((((hasDerivAt_id' x').pow 2).const_mul c').div_const 3).congr_deriv (by ring)
    have hcont_t : ContinuousOn (fun t' => |g t'| * Bessel.besselV (c' / 12) t') (φ '' uIcc (xiStar / 2) R) := by
      refine (hg.cont.abs.mul hV_cont).mono ?_
      rintro t' ⟨x', _, rfl⟩; show 0 ≤ φ x'; dsimp [φ]; positivity
    exact intervalIntegral.integral_comp_mul_deriv' hd
      ((continuous_const.mul continuous_id).div_const 3).continuousOn hcont_t
  have h_nn : ∀ x' : ℝ, 0 ≤ x' → 0 ≤ |g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x' := fun x' hx' => by
    have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (φ x') := by
      rw [← Integration.virasoro_cardyV_eq_besselV ha (by dsimp [φ]; positivity)]
      exact virasoroProblem.cardyV_nonneg hshift (by dsimp [φ]; positivity)
    dsimp [φ']; positivity
  have h_le_M : ∀ R : ℝ, xiStar / 2 ≤ R →
      ∫ x' in (xiStar / 2)..R, |g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x' ≤
        virasoroProblem.cardyNorm (c' / 12) g := fun R hR => by
    rw [hcov_R R hR]
    have hφ_le : φ (xiStar / 2) ≤ φ R := by dsimp [φ]; gcongr; positivity [xiStar_pos]
    have hφ0 : 0 < φ (xiStar / 2) := by dsimp [φ]; positivity [xiStar_pos]
    rw [intervalIntegral.integral_of_le hφ_le, ← hM_eq]
    refine setIntegral_mono_set hV_int ?_
      ((Ioc_subset_Ioc_left hφ0.le).trans Ioc_subset_Ioi_self).eventuallySubset
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
        exact virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)
  have hint : IntegrableOn (fun x' => |g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x') (Ioi (xiStar / 2)) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (b := fun R => R)
      (virasoroProblem.cardyNorm (c' / 12) g) (xiStar / 2)
      (fun R => (hcont.intervalIntegrable (xiStar / 2) R).1) tendsto_id ?_
    refine eventually_atTop.mpr ⟨xiStar / 2, fun R hR => ?_⟩
    have heq : ∫ x' in (xiStar / 2)..R, ‖|g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x'‖ =
        ∫ x' in (xiStar / 2)..R, |g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x' := by
      refine intervalIntegral.integral_congr fun x' hx' => ?_
      rw [uIcc_of_le hR] at hx'
      rw [Real.norm_eq_abs, abs_of_nonneg (h_nn x' (by linarith [xiStar_pos, hx'.1]))]
    change ∫ x' in (xiStar / 2)..R, ‖|g (φ x')| * Bessel.besselV (c' / 12) (φ x') * φ' x'‖ ≤
      virasoroProblem.cardyNorm (c' / 12) g
    rw [heq]
    exact h_le_M R hR
  refine ⟨hint, ?_⟩
  have hT := intervalIntegral_tendsto_integral_Ioi (xiStar / 2) hint tendsto_id
  exact le_of_tendsto hT (eventually_atTop.mpr ⟨xiStar / 2, fun R hR => h_le_M R hR⟩)

/-! ### 2. Algebra, Fubini swap, and right-edge reduction -/

private def dualRightFubini (c' ε : ℝ) (g : ℝ → ℝ) (τ x' : ℝ) : ℂ :=
  ((virasoroDualPref c' * -(√(2 * c' / 3)) : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4) *
    ((g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3) : ℝ) : ℂ) *
    (kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ) *
      ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ) +
     kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ) *
      ((3 / (16 * π * x' * c') : ℝ) : ℂ))

private lemma dualRightFubini_eq_main {c' ε : ℝ} (hc' : 0 < c')
    (g : ℝ → ℝ) {τ x' : ℝ} (hτ : 0 < τ) (hx' : xiStar / 2 ≤ x') :
    dualRightFubini c' ε g τ x' =
      lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
        ((-(√2 * (π : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4)) /
            ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) *
          (((g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) : ℝ) : ℂ) *
            ((((1 - Real.exp (-4 * π * x')) ^ 2 : ℝ) : ℂ)⁻¹ +
              virasoroA1 x' / ((c' : ℂ) * ((vT τ : ℂ) + Complex.I / 2)) +
              ((virasoroA2 x' / c' : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ)) *
            ((2 * c' * x' / 3 : ℝ) : ℂ))) *
        Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have hx1 : (1 : ℝ) / 10 ≤ x' := by linarith [Bessel.one_fifth_le_xiStar]
  have hd_pos : 0 < (1 - Real.exp (-4 * π * x')) ^ 2 := by
    have hexp_lt : Real.exp (-4 * π * x') < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    exact sq_pos_of_pos (sub_pos.mpr hexp_lt)
  have hsub_ne : (1 - Real.exp (-(4 * π * x')) : ℝ) ≠ 0 := by
    have : (1 - Real.exp (-(4 * π * x'))) ^ 2 = (1 - Real.exp (-4 * π * x')) ^ 2 := by ring_nf
    intro h; rw [h, zero_pow two_ne_zero] at this; linarith
  have hdc : (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hsub_ne)
  have ha0 : (vT τ : ℂ) + Complex.I / 2 ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this
  have hcp_ne : ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl ha0)
  have hv_id : (vT τ : ℂ) + Complex.I / 2 = (Complex.I / 2) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ)) := by
    linear_combination (vT τ : ℂ) * Complex.I_sq
  have hv1_ne : (1 : ℂ) - 2 * Complex.I * (vT τ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hx'c : (x' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hc'c : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'.ne'
  have hbr : (((1 - Real.exp (-4 * π * x')) ^ 2 : ℝ) : ℂ)⁻¹ +
      virasoroA1 x' / ((c' : ℂ) * ((vT τ : ℂ) + Complex.I / 2)) + ((virasoroA2 x' / c' : ℝ) : ℂ) =
      (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ) +
          ((3 / (16 * π * x' * c') : ℝ) : ℂ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹) := by
    have h13_r : ((1 - Real.exp (-4 * π * x')) ^ 2)⁻¹ + virasoroA2 x' / c' =
        ((1 - Real.exp (-4 * π * x')) ^ 2)⁻¹ *
          (1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)) := by
      unfold virasoroA2
      field_simp [hd_pos.ne', hc'.ne']
      ring
    have h13 : (((1 - Real.exp (-4 * π * x')) ^ 2 : ℝ) : ℂ)⁻¹ + ((virasoroA2 x' / c' : ℝ) : ℂ) =
        (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹ *
          ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ) := by
      rw [show -4 * π * x' = -(4 * π * x') by ring] at h13_r ⊢
      exact_mod_cast h13_r
    have h2 : virasoroA1 x' / ((c' : ℂ) * ((vT τ : ℂ) + Complex.I / 2)) =
        (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹ *
          (((3 / (16 * π * x' * c') : ℝ) : ℂ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹) := by
      unfold virasoroA1
      rw [hv_id, show -4 * π * x' = -(4 * π * x') by ring]
      have hpic : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      push_cast
      rw [show (1 - Complex.exp (-(4 * (π : ℂ) * (x' : ℂ)))) ^ 2 =
          (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ) by push_cast; rfl]
      field_simp [hdc, hx'c, hc'c, hpic, hv1_ne, Complex.I_ne_zero]
      ring
    rw [add_right_comm, h13, h2, mul_add]
  have hphase : -Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ) +
      (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) =
      Complex.I * ((c' * phiDual (vT τ) x' : ℝ) : ℂ) := by
    have hx_gt : xiStar ≤ xT τ := (xT_gt_xiStar hτ).le
    have hv_tip : vTip (xT τ) = vT τ := vTip_xT hτ.le
    have hb_eq : bTip (xT τ) = (vT τ : ℂ) + Complex.I / 2 := by unfold bTip; rw [hv_tip]
    have hre0 : (edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2)).re = 0 := edgePhi0Blaschke_re_edge (vT τ)
    have hbl_eq : edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2) =
        Complex.I * ((edgePhi0Blaschke (bTip (xT τ))).im : ℂ) := by
      apply Complex.ext <;> simp [hre0, hb_eq]
    have hpl := phaseLock_identity hx_gt
    rw [hv_tip] at hpl
    rw [hbl_eq, phiDual_eq (vT_nonneg hτ.le), edgeF_vT τ]
    have him_eq : (edgePhi0Blaschke (bTip (xT τ))).im = 2 * π * cumulN (xT τ) - 4 * π / 3 * xT τ * vT τ := by
      linarith
    rw [him_eq]
    push_cast; ring
  have hpref : (((virasoroDualPref c' * -(√(2 * c' / 3)) : ℝ) : ℂ)) =
      (((π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2) : ℝ) : ℂ)) *
        ((-(√2 * π) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    unfold virasoroDualPref
    have hs2 : (√2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
    have hs3 : √3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsc : √c' ≠ 0 := (Real.sqrt_pos.mpr hc').ne'
    have hsx : √xiStar ≠ 0 := (Real.sqrt_pos.mpr hxi).ne'
    have hs_xi : 1 - Real.exp (-(4 * π * xiStar)) ≠ 0 := by
      have : Real.exp (-(4 * π * xiStar)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
      linarith
    have hsq23 : √(2 * c' / 3) = √2 * √c' / √3 := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul zero_le_two]
    rw [hsq23]
    field_simp
  have hexp_split : Complex.exp (-Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ)) *
      Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) =
      Complex.exp (Complex.I * ((c' * phiDual (vT τ) x' : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, hphase]
  have hcancel : ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
      ((-(√2 * (π : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4))) /
        ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) =
      -((√2 * π : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4) := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hcp_ne]
    push_cast; ring
  dsimp [dualRightFubini, kedgeEpsIntegrand, lowerDualRightCore]
  rw [hbr, edgeF_vT τ, lowerY_xT hτ.le, hpref]
  set p0 : ℂ := ((π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2) : ℝ) : ℂ)
  set ctau : ℂ := (((1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ : ℝ) : ℂ)
  set mt : ℂ := lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2 *
    Complex.exp (Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ))
  set gx : ℂ := ((g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) : ℝ) : ℂ)
  set den : ℂ := (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹
  set rbr : ℂ := ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ) +
    ((3 / (16 * π * x' * c') : ℝ) : ℂ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹
  set ephi : ℂ := Complex.exp (Complex.I * ((c' * phiDual (vT τ) x' : ℝ) : ℂ))
  have hL_eq :
      p0 * ((-(√2 * π) : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        ((g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3) : ℝ) : ℂ) *
        (mt * ((((1 - Real.exp (-(4 * π * xT τ))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
            √(edgeF' (vT τ)) : ℝ)) : ℂ) * ephi * (vD τ : ℂ) *
            ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ) +
          mt * ((((1 - Real.exp (-(4 * π * xT τ))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
            √(edgeF' (vT τ)) : ℝ)) : ℂ) * ephi * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ *
            (vD τ : ℂ) * ((3 / (16 * π * x' * c') : ℝ) : ℂ)) =
      (p0 * ctau * mt) * (-((√2 * π : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4)) *
        (gx * (den * rbr) * ephi * ((2 * c' * x' / 3 : ℝ) : ℂ)) := by
    dsimp [ctau, gx, den, rbr]; push_cast; ring
  have hR_eq :
      (p0 * ctau * mt) *
        (((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
          ((-(√2 * (π : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4))) /
            ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ))) *
        (gx * (den * rbr) *
          (Complex.exp (-Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ)) *
            Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2)))) *
          ((2 * c' * x' / 3 : ℝ) : ℂ)) =
      (((π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2) *
          (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ : ℝ) : ℂ) *
          lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2 *
          Complex.exp (Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ))) *
        ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
        ((-(√2 * (π : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4)) /
            ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) *
          (gx * (den * rbr) * Complex.exp (-Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ)) *
            ((2 * c' * x' / 3 : ℝ) : ℂ))) *
        Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) := by
    dsimp [p0, ctau, mt]; push_cast; ring
  calc _ = (p0 * ctau * mt) * (-((√2 * π : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4)) *
        (gx * (den * rbr) * ephi * ((2 * c' * x' / 3 : ℝ) : ℂ)) := hL_eq
    _ = (p0 * ctau * mt) *
        (((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
          ((-(√2 * (π : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4))) /
            ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ))) *
        (gx * (den * rbr) *
          (Complex.exp (-Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ)) *
            Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2)))) *
          ((2 * c' * x' / 3 : ℝ) : ℂ)) := by rw [← hcancel, ← hexp_split]
    _ = _ := hR_eq

private lemma continuousOn_dualRightFubini {c' ε : ℝ} (hc' : 10000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) :
    ContinuousOn (fun p : ℝ × ℝ => dualRightFubini c' ε g p.1 p.2)
      (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
    (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
      (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
  have hgV_cont : ContinuousOn (fun p : ℝ × ℝ =>
      ((g (c' * p.2 ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * p.2 ^ 2 / 3) *
        (2 * c' * p.2 / 3) : ℝ) : ℂ)) (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
    have hφ2 : Continuous fun p : ℝ × ℝ => c' * p.2 ^ 2 / 3 := by fun_prop
    have hg2 : Continuous fun p : ℝ × ℝ => g (c' * p.2 ^ 2 / 3) :=
      hg.cont.comp_continuous hφ2 fun _ => show 0 ≤ c' * _ ^ 2 / 3 by positivity
    have hV2 : Continuous fun p : ℝ × ℝ => Bessel.besselV (c' / 12) (c' * p.2 ^ 2 / 3) :=
      hV_cont.comp_continuous hφ2 fun _ => show 0 ≤ c' * _ ^ 2 / 3 by positivity
    exact (Complex.continuous_ofReal.comp ((hg2.mul hV2).mul (by fun_prop))).continuousOn
  have hr1_cont : ContinuousOn (fun p : ℝ × ℝ =>
      ((1 - virasoroV1 p.2 / (c' * (1 - Real.exp (-4 * π * p.2)) ^ 2) : ℝ) : ℂ))
      (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
    refine Complex.continuous_ofReal.continuousOn.comp (continuousOn_const.sub ?_) fun _ _ => mem_univ _
    have hv1 : ContinuousOn (fun p : ℝ × ℝ => virasoroV1 p.2) (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
      unfold virasoroV1
      have hden_cont : ContinuousOn (fun p : ℝ × ℝ => (1 - Real.exp (-4 * π * p.2)) ^ 2)
          (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by fun_prop
      have hr : ContinuousOn (fun p : ℝ × ℝ => 3 / (16 * π * p.2)) (Ioi 0 ×ˢ Ioi (xiStar / 2)) :=
        continuousOn_const.div (continuous_const.mul continuous_snd).continuousOn fun p hp =>
          mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne') (by linarith [xiStar_pos, mem_Ioi.mp hp.2])
      exact ((hr.mul hden_cont).sub (by fun_prop)).add (by fun_prop)
    exact hv1.div (continuous_const.mul (by fun_prop)).continuousOn fun p hp =>
      mul_ne_zero hc0.ne' (by linarith [one_sub_exp_sq_ge_quarter (mem_Ioi.mp hp.2).le])
  have hr2_cont : ContinuousOn (fun p : ℝ × ℝ => ((3 / (16 * π * p.2 * c') : ℝ) : ℂ))
      (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
    refine Complex.continuous_ofReal.continuousOn.comp (continuousOn_const.div ?_ fun p hp => ?_) fun _ _ => mem_univ _
    · fun_prop
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne')
        (by linarith [xiStar_pos, mem_Ioi.mp hp.2])) hc0.ne'
  have hk_cont : ContinuousOn (fun p : ℝ × ℝ => kedgeEpsIntegrand c' ε p.2 (vT p.1) * (vD p.1 : ℂ))
      (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
    have hk_eq : ∀ p ∈ Ioi 0 ×ˢ Ioi (xiStar / 2),
        kedgeEpsIntegrand c' ε p.2 (vT p.1) * (vD p.1 : ℂ) =
          lowerMt ε (Complex.I * (Real.tanh (π * p.1 / 4) : ℂ)) ^ 2 *
            Complex.exp (Complex.I * (thetaOut (Real.tanh (π * p.1 / 4)) : ℂ)) *
            (((1 - Real.exp (-(4 * π * xT p.1))) ^ 2 * √(edgeF' (vT p.1)) * vD p.1 : ℝ) : ℂ) *
            (((1 - Real.exp (-(4 * π * p.2))) ^ 2 : ℝ) : ℂ)⁻¹ *
            Complex.exp (Complex.I * ((c' * (4 * π / 3 * (xT p.1 - p.2) * vT p.1 -
              2 * π * cumulN (xT p.1)) : ℝ) : ℂ)) := fun p hp => by
      rw [kedgeEpsIntegrand_vT (mem_Ioi.mp hp.1).le]
      push_cast; ring
    have htanh_c : Continuous fun τ : ℝ => Real.tanh (π * τ / 4) := by
      have : (fun τ : ℝ => Real.tanh (π * τ / 4)) =
          fun τ => Real.sinh (π * τ / 4) / Real.cosh (π * τ / 4) :=
        funext fun τ => Real.tanh_eq_sinh_div_cosh _
      rw [this]
      exact (Real.continuous_sinh.comp (by fun_prop)).div (Real.continuous_cosh.comp (by fun_prop))
        fun τ => (Real.cosh_pos _).ne'
    have hmt_c : Continuous fun τ : ℝ => lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2 := by
      refine Continuous.pow ?_ 2
      unfold lowerMt
      refine (continuous_const.mul (continuous_const.add ((continuous_const.mul
        (Complex.continuous_ofReal.comp htanh_c)).pow 2))).div
        ((continuous_const.add ((continuous_const.mul (Complex.continuous_ofReal.comp htanh_c)).pow 2)).add
          (continuous_const.mul (continuous_const.add (continuous_const.mul
            (Complex.continuous_ofReal.comp htanh_c))))) fun τ => by
          intro h
          set y := Real.tanh (π * τ / 4)
          rw [show (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)) =
            ((1 - y ^ 2 + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ) by
            rw [mul_pow, Complex.I_sq]; push_cast; ring] at h
          have hre := congrArg Complex.re h
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hre
          have hy2 : y ^ 2 < 1 := tanh_sq_lt_one _
          nlinarith [hε.1]
    have hth_c : Continuous fun τ : ℝ => Complex.exp (Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (thetaOut_soft.2.2.comp_continuous htanh_c fun τ => ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩)))
    have hxT_c : Continuous xT := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_xT t).continuousAt
    have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt
    have hxN_c : Continuous fun τ : ℝ => cumulN (xT τ) := by
      refine continuousOn_cumulN.comp_continuous hxT_c fun τ => ?_
      rw [← xT_zero]
      by_cases hτ : 0 ≤ τ
      · rcases hτ.eq_or_lt with rfl | hp; exact le_rfl
        exact (xT_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ) hp).le
      · have h_even : xT τ = xT (-τ) := by unfold xT; rw [mul_neg, Real.cosh_neg]
        rw [h_even]
        exact (xT_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)).le
    have h1_c : Continuous fun p : ℝ × ℝ => lowerMt ε (Complex.I * (Real.tanh (π * p.1 / 4) : ℂ)) ^ 2 :=
      hmt_c.comp continuous_fst
    have h2_c : Continuous fun p : ℝ × ℝ => Complex.exp (Complex.I * (thetaOut (Real.tanh (π * p.1 / 4)) : ℂ)) :=
      hth_c.comp continuous_fst
    have h3_c : Continuous fun p : ℝ × ℝ =>
        (((1 - Real.exp (-(4 * π * xT p.1))) ^ 2 * √(edgeF' (vT p.1)) * vD p.1 : ℝ) : ℂ) := by
      have hxT1 : Continuous fun p : ℝ × ℝ => xT p.1 := hxT_c.comp continuous_fst
      have hF'1 : Continuous fun p : ℝ × ℝ => edgeF' (vT p.1) := hF'_c.comp (continuous_vT.comp continuous_fst)
      have hvD1 : Continuous fun p : ℝ × ℝ => vD p.1 := continuous_vD.comp continuous_fst
      have hex1 : Continuous fun p : ℝ × ℝ => (1 - Real.exp (-(4 * π * xT p.1))) ^ 2 := by fun_prop
      have hsq1 : Continuous fun p : ℝ × ℝ => √(edgeF' (vT p.1)) := Real.continuous_sqrt.comp hF'1
      exact Complex.continuous_ofReal.comp ((hex1.mul hsq1).mul hvD1)
    have h4_c : ContinuousOn (fun p : ℝ × ℝ => (((1 - Real.exp (-(4 * π * p.2))) ^ 2 : ℝ) : ℂ)⁻¹)
        (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
      have h0 : Continuous fun p : ℝ × ℝ => (1 - Real.exp (-(4 * π * p.2))) ^ 2 := by fun_prop
      exact (Complex.continuous_ofReal.comp h0).continuousOn.inv₀ fun p hp => by
        dsimp only [Function.comp_def]
        rw [Complex.ofReal_ne_zero]
        have : (1 - Real.exp (-(4 * π * p.2))) ^ 2 = (1 - Real.exp (-4 * π * p.2)) ^ 2 := by ring_nf
        linarith [one_sub_exp_sq_ge_quarter (mem_Ioi.mp hp.2).le]
    have h5_c : Continuous fun p : ℝ × ℝ =>
        Complex.exp (Complex.I * ((c' * (4 * π / 3 * (xT p.1 - p.2) * vT p.1 -
          2 * π * cumulN (xT p.1)) : ℝ) : ℂ)) := by
      have hxT1 : Continuous fun p : ℝ × ℝ => xT p.1 := hxT_c.comp continuous_fst
      have hvT1 : Continuous fun p : ℝ × ℝ => vT p.1 := continuous_vT.comp continuous_fst
      have hxN1 : Continuous fun p : ℝ × ℝ => cumulN (xT p.1) := hxN_c.comp continuous_fst
      have harg : Continuous fun p : ℝ × ℝ =>
          c' * (4 * π / 3 * (xT p.1 - p.2) * vT p.1 - 2 * π * cumulN (xT p.1)) := by fun_prop
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp harg))
    exact ContinuousOn.congr
      ((((h1_c.mul h2_c).mul h3_c).continuousOn.mul h4_c).mul h5_c.continuousOn) hk_eq
  have hinv_c : ContinuousOn (fun p : ℝ × ℝ => ((1 : ℂ) - 2 * Complex.I * (vT p.1 : ℂ))⁻¹)
      (Ioi 0 ×ˢ Ioi (xiStar / 2)) :=
    (continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_vT.comp continuous_fst)))).continuousOn.inv₀ fun p _ => by
      intro h; have := congrArg Complex.re h; simp at this
  have hterm1 : ContinuousOn (fun p : ℝ × ℝ =>
      kedgeEpsIntegrand c' ε p.2 (vT p.1) * (vD p.1 : ℂ) *
        ((1 - virasoroV1 p.2 / (c' * (1 - Real.exp (-4 * π * p.2)) ^ 2) : ℝ) : ℂ))
      (Ioi 0 ×ˢ Ioi (xiStar / 2)) := hk_cont.mul hr1_cont
  have hterm2 : ContinuousOn (fun p : ℝ × ℝ =>
      kedgeEpsIntegrand c' ε p.2 (vT p.1) * ((1 : ℂ) - 2 * Complex.I * (vT p.1 : ℂ))⁻¹ *
        (vD p.1 : ℂ) * ((3 / (16 * π * p.2 * c') : ℝ) : ℂ))
      (Ioi 0 ×ˢ Ioi (xiStar / 2)) := by
    refine ContinuousOn.congr ((hk_cont.mul hinv_c).mul hr2_cont) fun p _ => by
      dsimp only [Pi.mul_apply]; ring
  let c0 : ℂ := ((virasoroDualPref c' * -(√(2 * c' / 3)) : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4)
  exact ((continuousOn_const (c := c0).mul hgV_cont).mul (hterm1.add hterm2)).congr fun p _ => by
    unfold dualRightFubini; dsimp only [Pi.mul_apply, Pi.add_apply, c0]

/-- Right-edge integral reduction of `cts:dual-id`. -/
lemma lowerDualPsi_right_integral_eq :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' : ℝ}, c₀ ≤ c' →
      ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
      ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) (1 / 2) →
      ∃ E : ℝ, |E| ≤ C * virasoroProblem.cardyNorm (c' / 12) g *
          (Real.log (2 / ε) / c' ^ (3 / 2 : ℝ)) ∧
        ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (1 - (τ : ℂ) * Complex.I)).re =
          virasoroDualPref c' *
            ((∫ t' in Ioi (c' * (xiStar / 2) ^ 2 / 3),
                g t' * Bessel.besselV (c' / 12) t' *
                  ((1 - virasoroV1 (√(3 * t' / c')) /
                      (c' * (1 - Real.exp (-4 * π * √(3 * t' / c'))) ^ 2)) *
                    virasoroKedgeEps c' ε (√(3 * t' / c')) +
                    (3 / (16 * π * √(3 * t' / c') * c')) *
                      virasoroKedge1Eps c' ε (√(3 * t' / c')))) + E) := by
  obtain ⟨c_e, C_e, _, hC_e0, h_edge⟩ := edge_hankel_two_virasoro
  refine ⟨max 10000 c_e, 7 * C_e / (π * √3), le_max_left _ _, by positivity [Real.pi_pos], ?_⟩
  intro c' hc' g hg ε hε
  have hc10k : 10000 ≤ c' := (le_max_left _ _).trans hc'
  have hc_e : c_e ≤ c' := (le_max_right _ _).trans hc'
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hpi := Real.pi_pos
  have hC₀ : 0 < virasoroDualPref c' := virasoroDualPref_pos hc0
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  have hM_nn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg (by rw [virasoroProblem_totalShift]; linarith) g
  obtain ⟨hW_int, hW_le⟩ := lowerWeps_tanh_Ioi_bound hε
  obtain ⟨hVx_int, _⟩ := integrableOn_Ioi_half_abs hc0 ha hg
  let μτ : Measure ℝ := volume.restrict (Ioi 0)
  let μx : Measure ℝ := volume.restrict (Ioi (xiStar / 2))
  let F2 : ℝ × ℝ → ℂ := fun p => dualRightFubini c' ε g p.1 p.2
  have hF2_cont : ContinuousOn F2 (Ioi 0 ×ˢ Ioi (xiStar / 2)) :=
    continuousOn_dualRightFubini hc10k hg hε
  let bτ : ℝ → ℝ := fun τ => 4 * lowerWeps ε (Real.tanh (π * τ / 4))
  let bx : ℝ → ℝ := fun x' => (virasoroDualPref c' * √(2 * c' / 3) * 3) *
    (|g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3))
  have hbτ_int : Integrable bτ μτ := hW_int.const_mul 4
  have hbx_int : Integrable bx μx := hVx_int.const_mul (virasoroDualPref c' * √(2 * c' / 3) * 3)
  have hF2_bd : ∀ τ ∈ Ioi (0 : ℝ), ∀ x' ∈ Ioi (xiStar / 2), ‖dualRightFubini c' ε g τ x'‖ ≤ bτ τ * bx x' := by
    intro τ hτ x' hx'
    have hτ_pos : 0 < τ := mem_Ioi.mp hτ
    have hx'_pos : xiStar / 2 < x' := mem_Ioi.mp hx'
    have hx'1 : (1 : ℝ) / 10 ≤ x' := by linarith [Bessel.one_fifth_le_xiStar]
    have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) := by
      rw [← Integration.virasoro_cardyV_eq_besselV ha (by positivity)]
      exact virasoroProblem.cardyV_nonneg (by rw [virasoroProblem_totalShift]; linarith) (by positivity)
    have hq4 : 1 / 4 ≤ (1 - Real.exp (-4 * π * x')) ^ 2 := one_sub_exp_sq_ge_quarter hx'_pos.le
    have hV1 : |virasoroV1 x'| ≤ 30 := virasoroV1_abs_le_30 hx'_pos.le
    have hr1_le : |1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| ≤ 2 := by
      have hsub : |virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| ≤ 1 := by
        rw [abs_div, abs_of_pos (mul_pos hc0 (by linarith))]
        calc |virasoroV1 x'| / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)
            ≤ 30 / (10000 * (1 / 4)) := div_le_div₀ (by norm_num) hV1 (by norm_num)
              (mul_le_mul hc10k hq4 (by norm_num) hc0.le)
          _ ≤ 1 := by norm_num
      calc |1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)|
          ≤ |1| + |virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| := abs_sub _ _
        _ ≤ 1 + 1 := by rw [abs_one]; linarith
        _ = 2 := by norm_num
    have hr2_le : |3 / (16 * π * x' * c')| ≤ 1 := by
      rw [abs_of_pos (by positivity [Real.pi_pos, (by linarith : 0 < x')])]
      have hpi3 : 3 ≤ π := by linarith [Real.pi_gt_three]
      calc 3 / (16 * π * x' * c') ≤ 3 / (16 * 3 * (1 / 10) * 10000) := by gcongr
        _ ≤ 1 := by norm_num
    have h1_bd : ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ ≤ bτ τ :=
      kedgeEpsIntegrand_vT_norm_le hε hx'_pos.le hτ_pos.le
    have h2_bd : ‖kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖ ≤ bτ τ := by
      calc _ = ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ * ‖((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹‖ := by
            rw [mul_assoc (kedgeEpsIntegrand c' ε x' (vT τ)), mul_comm _ (vD τ : ℂ), ← mul_assoc, norm_mul]
        _ ≤ bτ τ * 1 := mul_le_mul h1_bd (norm_inv_one_sub_two_I_mul_le _) (norm_nonneg _)
            (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = bτ τ := mul_one _
    have hsum_bd : ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ) *
          ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ) +
        kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ) *
          ((3 / (16 * π * x' * c') : ℝ) : ℂ)‖ ≤ bτ τ * 3 := by
      have hn1 : ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ) *
            ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ)‖ =
          ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ *
            |1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hn2 : ‖kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ) *
            ((3 / (16 * π * x' * c') : ℝ) : ℂ)‖ =
          ‖kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖ *
            |3 / (16 * π * x' * c')| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hbτ_nn : 0 ≤ bτ τ := mul_nonneg (by norm_num) (sq_nonneg _)
      calc _ ≤ ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ) *
              ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ)‖ +
            ‖kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ) *
              ((3 / (16 * π * x' * c') : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ *
              |1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| +
            ‖kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖ *
              |3 / (16 * π * x' * c')| := by rw [hn1, hn2]
        _ ≤ bτ τ * 2 + bτ τ * 1 := add_le_add
            (mul_le_mul h1_bd hr1_le (abs_nonneg _) hbτ_nn)
            (mul_le_mul h2_bd hr2_le (abs_nonneg _) hbτ_nn)
        _ = bτ τ * 3 := by ring
    dsimp [dualRightFubini]
    have hdx_nn : 0 ≤ 2 * c' * x' / 3 := by positivity [hx'_pos]
    have hgx_abs : |g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3)| =
        |g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hV_nn, abs_of_nonneg hdx_nn]
    rw [norm_mul, norm_mul, norm_mul,
      show Complex.I * (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_pos hC₀, abs_of_pos (Real.sqrt_pos.mpr (by positivity)),
      Complex.norm_real, Real.norm_eq_abs, hgx_abs]
    calc (virasoroDualPref c' * √(2 * c' / 3)) *
          (|g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3)) *
          ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ) *
            ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ) +
          kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ) *
            ((3 / (16 * π * x' * c') : ℝ) : ℂ)‖
        ≤ (virasoroDualPref c' * √(2 * c' / 3)) *
            (|g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3)) *
            (bτ τ * 3) := by gcongr
      _ = bτ τ * bx x' := by dsimp [bx]; ring
  have hF2_int : Integrable F2 (μτ.prod μx) := by
    refine (hbτ_int.mul_prod hbx_int).mono' ?_ ?_
    · have hae := hF2_cont.aestronglyMeasurable (μ := (volume : Measure (ℝ × ℝ)))
        (measurableSet_Ioi.prod measurableSet_Ioi)
      simpa only [μτ, μx, ← Measure.volume_eq_prod, Measure.prod_restrict] using hae
    · rw [show μτ.prod μx = (volume : Measure (ℝ × ℝ)).restrict (Ioi 0 ×ˢ Ioi (xiStar / 2)) by
        dsimp [μτ, μx]; rw [Measure.volume_eq_prod, Measure.prod_restrict]]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
      exact hF2_bd p.1 hp.1 p.2 hp.2
  have hswap := MeasureTheory.integral_integral_swap (μ := μτ) (ν := μx)
    (f := fun τ x' => F2 (τ, x')) hF2_int
  let Mainτ : ℝ → ℂ := fun τ => ∫ x' in Ioi (xiStar / 2), dualRightFubini c' ε g τ x'
  have hMain_int : IntegrableOn Mainτ (Ioi 0) := hF2_int.integral_prod_left
  let PsiR : ℝ → ℂ := fun τ => lowerDualPsi c' ε 0 g (1 - (τ : ℂ) * Complex.I)
  have hPsiR_cont : ContinuousOn PsiR (Ioi 0) := by
    refine (lowerDualPsi_continuousOn (by linarith) hg hε.1 le_rfl).comp
      (by fun_prop : Continuous fun τ : ℝ => 1 - (τ : ℂ) * Complex.I).continuousOn fun τ hτ => ?_
    exact ⟨⟨by simp, by norm_num, by simp; exact (mem_Ioi.mp hτ).le⟩, fun h => by
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h | h
      · have := congrArg Complex.re h; simp at this
      · have := congrArg Complex.im h; simp at this; linarith [mem_Ioi.mp hτ]⟩
  let C_core : ℝ := π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)
  have hC_core_pos : 0 < C_core := by
    have : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
      rw [sub_pos, Real.exp_lt_one_iff]; nlinarith [xiStar_pos]
    dsimp [C_core]; positivity [xiStar_pos]
  have hrem_bd : ∀ τ ∈ Ioi (0 : ℝ),
      ‖PsiR τ - Mainτ τ‖ ≤ C_core * (C_e * M / c' ^ 2) * lowerWeps ε (Real.tanh (π * τ / 4)) := by
    intro τ hτ
    have hτ_pos : 0 < τ := mem_Ioi.mp hτ
    let mH : ℂ := (-(√2 * (π : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4)) /
        ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) *
      ∫ x' in Ioi (xiStar / 2),
        ((g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) : ℝ) : ℂ) *
          ((((1 - Real.exp (-4 * π * x')) ^ 2 : ℝ) : ℂ)⁻¹ +
            virasoroA1 x' / ((c' : ℂ) * ((vT τ : ℂ) + Complex.I / 2)) +
            ((virasoroA2 x' / c' : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ)) *
          ((2 * c' * x' / 3 : ℝ) : ℂ)
    have hMain_eq : Mainτ τ = lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
        mH * Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) := by
      dsimp [Mainτ, mH]
      have heq_f : Set.EqOn (fun x' => dualRightFubini c' ε g τ x')
          (fun x' => (lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
              (-(√2 * (π : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4)) /
                ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) *
              Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2)))) *
            (((g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) : ℝ) : ℂ) *
              ((((1 - Real.exp (-4 * π * x')) ^ 2 : ℝ) : ℂ)⁻¹ +
                virasoroA1 x' / ((c' : ℂ) * ((vT τ : ℂ) + Complex.I / 2)) +
                ((virasoroA2 x' / c' : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * ((4 * π / 3 * c' * vT τ * x' : ℝ) : ℂ)) *
              ((2 * c' * x' / 3 : ℝ) : ℂ))) (Ioi (xiStar / 2)) := fun x' hx' => by
        dsimp only; rw [dualRightFubini_eq_main (ε := ε) hc0 g hτ_pos (mem_Ioi.mp hx').le]; ring
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq_f, MeasureTheory.integral_const_mul]
      ring
    rw [show PsiR τ = lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
        hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) *
        Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) by
      exact lowerDualPsi_right_factor_eq hε.1.le g hτ_pos, hMain_eq]
    have hdiff_fac : lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
          hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) *
          Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) -
        lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) * mH *
          Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) =
        lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
          Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) *
          (hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) - mH) := by ring
    rw [hdiff_fac, norm_mul, norm_mul, norm_mul]
    have hcore_n : ‖lowerDualRightCore ε τ‖ ≤ C_core * lowerWeps ε (Real.tanh (π * τ / 4)) := by
      have hmt_n : ‖lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2‖ =
          lowerWeps ε (Real.tanh (π * τ / 4)) := by rw [norm_pow]; rfl
      have hF'_le1 : edgeF' (vT τ) ≤ 1 := by
        unfold edgeF'
        exact div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (by linarith [Real.cosh_sq (π * vT τ)])) (Real.sqrt_nonneg _)
      have hsub1 : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 ≤ 1 := by
        have : 0 ≤ Real.exp (-(4 * π * xT τ)) := (Real.exp_pos _).le
        have : Real.exp (-(4 * π * xT τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [(xT_pos τ).le])
        nlinarith
      dsimp [lowerDualRightCore]
      rw [norm_mul, norm_mul, hmt_n,
        show Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ) =
          (thetaOut (Real.tanh (π * τ / 4)) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity [(vD_pos τ).le])]
      have hfac : C_core * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ ≤ C_core := by
        have h1 : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ ≤ 1 := by
          calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul hsub1 (Real.sqrt_le_one.mpr hF'_le1)
                (Real.sqrt_nonneg _) zero_le_one) (vD_le_one τ) (vD_pos τ).le (by norm_num)
            _ = 1 := by ring
        nlinarith [hC_core_pos]
      have hW_nn : 0 ≤ lowerWeps ε (Real.tanh (π * τ / 4)) := sq_nonneg _
      nlinarith
    have hcp_n := norm_cpow_half_v_add_half_I_le (vT_nonneg hτ_pos.le)
    have hexp_n : ‖Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2)))‖ = 1 := by
      rw [Complex.norm_exp]; simp [edgePhi0Blaschke_re_edge]
    have hedge_n := h_edge hc_e hg (vT_nonneg hτ_pos.le)
    have hsq1v : 0 < √(1 + vT τ) := Real.sqrt_pos.mpr (by linarith [vT_nonneg hτ_pos.le])
    calc ‖lowerDualRightCore ε τ‖ * ‖((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)‖ *
          ‖Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2)))‖ *
          ‖hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) - mH‖
        ≤ (C_core * lowerWeps ε (Real.tanh (π * τ / 4))) * √(1 + vT τ) * 1 *
            (C_e * M / (c' ^ 2 * √(1 + vT τ))) :=
          mul_le_mul
            (mul_le_mul
              (mul_le_mul hcore_n hcp_n (norm_nonneg _) (mul_nonneg hC_core_pos.le (sq_nonneg _)))
              hexp_n.le (norm_nonneg _) (mul_nonneg (mul_nonneg hC_core_pos.le (sq_nonneg _)) (Real.sqrt_nonneg _)))
            hedge_n (norm_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg hC_core_pos.le (sq_nonneg _)) (Real.sqrt_nonneg _)) zero_le_one)
      _ = C_core * (C_e * M / c' ^ 2) * lowerWeps ε (Real.tanh (π * τ / 4)) := by
          field_simp [hsq1v.ne']
  have hrem_int : IntegrableOn (fun τ : ℝ => (PsiR τ).re - (Mainτ τ).re) (Ioi 0) := by
    refine (hW_int.const_mul (C_core * (C_e * M / c' ^ 2))).mono' ?_ ?_
    · exact ((Complex.continuous_re.comp_continuousOn hPsiR_cont).aestronglyMeasurable measurableSet_Ioi).sub
        hMain_int.re.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      have hsub := (Complex.abs_re_le_norm (PsiR τ - Mainτ τ)).trans (hrem_bd τ hτ)
      simpa only [Real.norm_eq_abs, Complex.sub_re] using hsub
  have hrem_abs : |∫ τ in Ioi (0 : ℝ), ((PsiR τ).re - (Mainτ τ).re)| ≤
      C_core * (C_e * M / c' ^ 2) * (7 * Real.log (2 / ε)) := by
    calc |∫ τ in Ioi (0 : ℝ), ((PsiR τ).re - (Mainτ τ).re)|
        = ‖∫ τ in Ioi (0 : ℝ), ((PsiR τ).re - (Mainτ τ).re)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ τ in Ioi (0 : ℝ), ‖(PsiR τ).re - (Mainτ τ).re‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ τ in Ioi (0 : ℝ), (C_core * (C_e * M / c' ^ 2)) * lowerWeps ε (Real.tanh (π * τ / 4)) := by
          refine integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => norm_nonneg _)
            (hW_int.const_mul _) (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
          exact (Complex.abs_re_le_norm (PsiR τ - Mainτ τ)).trans (hrem_bd τ hτ)
      _ = C_core * (C_e * M / c' ^ 2) * ∫ τ in Ioi (0 : ℝ), lowerWeps ε (Real.tanh (π * τ / 4)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ C_core * (C_e * M / c' ^ 2) * (7 * Real.log (2 / ε)) := by
          gcongr
  let mainX : ℝ → ℝ := fun x' =>
    g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) *
      ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)) * virasoroKedgeEps c' ε x' +
        (3 / (16 * π * x' * c')) * virasoroKedge1Eps c' ε x')
  have hMain_eval : ∫ τ in Ioi (0 : ℝ), (Mainτ τ).re =
      virasoroDualPref c' * ∫ x' in Ioi (xiStar / 2), mainX x' * (2 * c' * x' / 3) := by
    have hτ_swap : ∫ τ in Ioi (0 : ℝ), Mainτ τ =
        ∫ x' in Ioi (xiStar / 2), ∫ τ in Ioi (0 : ℝ), dualRightFubini c' ε g τ x' := hswap
    have hre1 : ∫ τ in Ioi (0 : ℝ), (Mainτ τ).re = (∫ τ in Ioi (0 : ℝ), Mainτ τ).re :=
      integral_re hMain_int
    have hGx_int : IntegrableOn (fun x' : ℝ => ∫ τ in Ioi (0 : ℝ), dualRightFubini c' ε g τ x')
        (Ioi (xiStar / 2)) := hF2_int.integral_prod_right
    have hre2 : (∫ x' in Ioi (xiStar / 2), ∫ τ in Ioi (0 : ℝ), dualRightFubini c' ε g τ x').re =
        ∫ x' in Ioi (xiStar / 2), (∫ τ in Ioi (0 : ℝ), dualRightFubini c' ε g τ x').re :=
      (integral_re hGx_int).symm
    rw [hre1, hτ_swap, hre2, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x' hx' => ?_
    obtain ⟨_, _, hcov0, hcov1⟩ := kedgeEps_integrable_and_tau_eq c' hε (mem_Ici.mpr (mem_Ioi.mp hx').le)
    have h_τ0 : IntegrableOn (fun τ : ℝ => kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)) (Ioi 0) := by
      refine (hW_int.const_mul 4).mono' ?_ ?_
      · exact ((continuousOn_kedgeEpsIntegrand c' hε.1 x').comp continuous_vT.continuousOn
          (fun τ hτ => vT_nonneg (mem_Ioi.mp hτ).le) |>.mul
          (Complex.continuous_ofReal.comp continuous_vD).continuousOn).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
        exact kedgeEpsIntegrand_vT_norm_le hε (mem_Ioi.mp hx').le (mem_Ioi.mp hτ).le
    have h_τ1 : IntegrableOn (fun τ : ℝ =>
        kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)) (Ioi 0) := by
      have hc1 : ContinuousOn (fun τ : ℝ => ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹) (Ioi 0) :=
        (continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp continuous_vT))).continuousOn.inv₀
          fun τ _ => by intro h; have := congrArg Complex.re h; simp at this
      refine (h_τ0.norm).mono' ?_ ?_
      · exact ((continuousOn_kedgeEpsIntegrand c' hε.1 x').comp continuous_vT.continuousOn
          (fun τ hτ => vT_nonneg (mem_Ioi.mp hτ).le) |>.mul hc1 |>.mul
          (Complex.continuous_ofReal.comp continuous_vD).continuousOn).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
        rw [mul_assoc (kedgeEpsIntegrand c' ε x' (vT τ)), mul_comm _ (vD τ : ℂ), ← mul_assoc, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_inv_one_sub_two_I_mul_le _)
    have hτ_factor : ∫ τ in Ioi (0 : ℝ), dualRightFubini c' ε g τ x' =
        ((virasoroDualPref c' * -(√(2 * c' / 3)) : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4) *
          ((g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3) : ℝ) : ℂ) *
          (((∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)) *
              ((1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2) : ℝ) : ℂ)) +
            ((∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) *
                ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)) *
              ((3 / (16 * π * x' * c') : ℝ) : ℂ))) := by
      dsimp [dualRightFubini]
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (h_τ0.mul_const _) (h_τ1.mul_const _),
        MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
    rw [hτ_factor, ← hcov0, ← hcov1]
    set z0 : ℂ := Complex.exp (Complex.I * (π : ℂ) / 4) * ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v
    set z1 : ℂ := Complex.exp (Complex.I * (π : ℂ) / 4) *
      ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹
    set r1 : ℝ := 1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)
    set r2 : ℝ := 3 / (16 * π * x' * c')
    set gx : ℝ := g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * (2 * c' * x' / 3)
    have hre_id : (((virasoroDualPref c' * -(√(2 * c' / 3)) : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        (gx : ℂ) * ((∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v) * (r1 : ℂ) +
          (∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) * (r2 : ℂ))).re =
        virasoroDualPref c' * (gx * (r1 * (-(√(2 * c' / 3)) * z0.re) + r2 * (-(√(2 * c' / 3)) * z1.re))) := by
      have hid : ((virasoroDualPref c' * -(√(2 * c' / 3)) : ℝ) : ℂ) * Complex.exp (Complex.I * (π : ℂ) / 4) *
          (gx : ℂ) * ((∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v) * (r1 : ℂ) +
            (∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) * (r2 : ℂ)) =
          ((virasoroDualPref c' * gx * (-(√(2 * c' / 3))) : ℝ) : ℂ) * (z0 * (r1 : ℂ) + z1 * (r2 : ℂ)) := by
        dsimp [z0, z1]; push_cast; ring
      have hre_mul_r : ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).re = z.re * r := fun z r => by simp
      rw [hid, Complex.re_ofReal_mul, Complex.add_re, hre_mul_r, hre_mul_r]
      ring
    rw [hre_id]
    dsimp [mainX, gx, r1, r2, z0, z1]
    unfold virasoroKedgeEps virasoroKedge1Eps
    ring
  let F : ℝ → ℝ := fun x' =>
    (1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)) * virasoroKedgeEps c' ε x' +
      (3 / (16 * π * x' * c')) * virasoroKedge1Eps c' ε x'
  have hF_cont : ContinuousOn F (Ici (xiStar / 2)) := by
    have ⟨hk0, hk1⟩ := continuous_virasoroKedgeEps hc0 hε
    have hV1_c : ContinuousOn virasoroV1 (Ici (xiStar / 2)) := by
      unfold virasoroV1
      have hden_c : ContinuousOn (fun x' : ℝ => (1 - Real.exp (-4 * π * x')) ^ 2) (Ici (xiStar / 2)) := by fun_prop
      have hr : ContinuousOn (fun x' : ℝ => 3 / (16 * π * x')) (Ici (xiStar / 2)) :=
        continuousOn_const.div (continuous_const.mul continuous_id).continuousOn fun x' hx' =>
          mul_ne_zero (by norm_num [Real.pi_pos.ne']) (by linarith [xiStar_pos, mem_Ici.mp hx'])
      exact ((hr.mul hden_c).sub (by fun_prop)).add (by fun_prop)
    have hr1_c : ContinuousOn (fun x' : ℝ => 1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2))
        (Ici (xiStar / 2)) :=
      continuousOn_const.sub (hV1_c.div (continuous_const.mul (by fun_prop)).continuousOn fun x' hx' =>
        mul_ne_zero hc0.ne' (by linarith [one_sub_exp_sq_ge_quarter (mem_Ici.mp hx')]))
    have hr2_c : ContinuousOn (fun x' : ℝ => 3 / (16 * π * x' * c')) (Ici (xiStar / 2)) :=
      continuousOn_const.div (by fun_prop) fun x' hx' =>
        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi.ne')
          (by linarith [xiStar_pos, mem_Ici.mp hx'])) hc0.ne'
    exact (hr1_c.mul hk0).add (hr2_c.mul hk1)
  have hF_bd : ∃ B : ℝ, ∀ x' : ℝ, xiStar / 2 < x' → |F x'| ≤ B := by
    refine ⟨3 * (√(2 * c' / 3) * (28 * Real.log (2 / ε))), fun x' hx' => ?_⟩
    have hx'1 : (1 : ℝ) / 10 ≤ x' := by linarith [Bessel.one_fifth_le_xiStar]
    have hq4 : 1 / 4 ≤ (1 - Real.exp (-4 * π * x')) ^ 2 := one_sub_exp_sq_ge_quarter hx'.le
    have hV1 : |virasoroV1 x'| ≤ 30 := virasoroV1_abs_le_30 hx'.le
    have hr1_le : |1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| ≤ 2 := by
      have hsub : |virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| ≤ 1 := by
        rw [abs_div, abs_of_pos (mul_pos hc0 (by linarith))]
        calc |virasoroV1 x'| / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)
            ≤ 30 / (10000 * (1 / 4)) := div_le_div₀ (by norm_num) hV1 (by norm_num)
              (mul_le_mul hc10k hq4 (by norm_num) hc0.le)
          _ ≤ 1 := by norm_num
      calc |1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)|
          ≤ |1| + |virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| := abs_sub _ _
        _ ≤ 1 + 1 := by rw [abs_one]; linarith
        _ = 2 := by norm_num
    have hr2_le : |3 / (16 * π * x' * c')| ≤ 1 := by
      rw [abs_of_pos (by positivity [Real.pi_pos, (by linarith : 0 < x')])]
      have hpi3 : 3 ≤ π := by linarith [Real.pi_gt_three]
      calc 3 / (16 * π * x' * c') ≤ 3 / (16 * 3 * (1 / 10) * 10000) := by gcongr
        _ ≤ 1 := by norm_num
    obtain ⟨_, _, hcov0, hcov1⟩ := kedgeEps_integrable_and_tau_eq c' hε hx'.le
    have hk_bd : ∀ (H : ℝ → ℂ),
        (∀ τ : ℝ, 0 ≤ τ → ‖H τ‖ ≤ 4 * lowerWeps ε (Real.tanh (π * τ / 4))) →
        ContinuousOn H (Ici 0) →
        ‖∫ τ in Ioi (0 : ℝ), H τ‖ ≤ 28 * Real.log (2 / ε) := fun H hbd hHc => by
      have hHint : IntegrableOn H (Ioi 0) :=
        (hW_int.const_mul 4).mono' ((hHc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => hbd τ (mem_Ioi.mp hτ).le)
      calc ‖∫ τ in Ioi (0 : ℝ), H τ‖ ≤ ∫ τ in Ioi (0 : ℝ), ‖H τ‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ τ in Ioi (0 : ℝ), 4 * lowerWeps ε (Real.tanh (π * τ / 4)) :=
            integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => norm_nonneg _)
              (hW_int.const_mul 4) (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => hbd τ (mem_Ioi.mp hτ).le)
        _ = 4 * ∫ τ in Ioi (0 : ℝ), lowerWeps ε (Real.tanh (π * τ / 4)) :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ 4 * (7 * Real.log (2 / ε)) := by gcongr
        _ = 28 * Real.log (2 / ε) := by ring
    have hK0_bd : |virasoroKedgeEps c' ε x'| ≤ √(2 * c' / 3) * (28 * Real.log (2 / ε)) := by
      unfold virasoroKedgeEps
      rw [hcov0, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hre_n : |(Complex.exp (Complex.I * (π : ℂ) / 4) *
            ∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)).re| ≤
          28 * Real.log (2 / ε) := by
        calc _ ≤ ‖Complex.exp (Complex.I * (π : ℂ) / 4) *
              ∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ :=
            Complex.abs_re_le_norm _
          _ = ‖∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ := by
              rw [norm_mul, show Complex.I * (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, one_mul]
          _ ≤ 28 * Real.log (2 / ε) := hk_bd _ (fun τ hτ => kedgeEpsIntegrand_vT_norm_le hε hx'.le hτ)
              (((continuousOn_kedgeEpsIntegrand c' hε.1 x').comp continuous_vT.continuousOn
                fun τ hτ => vT_nonneg (mem_Ici.mp hτ)).mul
                (Complex.continuous_ofReal.comp continuous_vD).continuousOn)
      exact mul_le_mul_of_nonneg_left hre_n (Real.sqrt_nonneg _)
    have hK1_bd : |virasoroKedge1Eps c' ε x'| ≤ √(2 * c' / 3) * (28 * Real.log (2 / ε)) := by
      unfold virasoroKedge1Eps
      rw [hcov1, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hbd1 : ∀ τ : ℝ, 0 ≤ τ → ‖kedgeEpsIntegrand c' ε x' (vT τ) *
            ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖ ≤
          4 * lowerWeps ε (Real.tanh (π * τ / 4)) := fun τ hτ => by
        rw [mul_assoc (kedgeEpsIntegrand c' ε x' (vT τ)), mul_comm _ (vD τ : ℂ), ← mul_assoc, norm_mul]
        exact (mul_le_mul (kedgeEpsIntegrand_vT_norm_le hε hx'.le hτ) (norm_inv_one_sub_two_I_mul_le _)
          (norm_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))).trans_eq (mul_one _)
      have hc1 : ContinuousOn (fun τ : ℝ => ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹) (Ici 0) :=
        (continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp continuous_vT))).continuousOn.inv₀
          fun τ _ => by intro h; have := congrArg Complex.re h; simp at this
      have hre_n : |(Complex.exp (Complex.I * (π : ℂ) / 4) *
            ∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) *
              ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)).re| ≤
          28 * Real.log (2 / ε) := by
        calc _ ≤ ‖Complex.exp (Complex.I * (π : ℂ) / 4) *
              ∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) *
                ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖ :=
            Complex.abs_re_le_norm _
          _ = ‖∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) *
                ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖ := by
              rw [norm_mul, show Complex.I * (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I, one_mul]
          _ ≤ 28 * Real.log (2 / ε) := hk_bd _ hbd1
              ((((continuousOn_kedgeEpsIntegrand c' hε.1 x').comp continuous_vT.continuousOn
                fun τ hτ => vT_nonneg (mem_Ici.mp hτ)).mul hc1).mul
                (Complex.continuous_ofReal.comp continuous_vD).continuousOn)
      exact mul_le_mul_of_nonneg_left hre_n (Real.sqrt_nonneg _)
    have hlog_nn : 0 ≤ 28 * Real.log (2 / ε) := by
      have : 1 < 2 / ε := by rw [lt_div_iff₀ hε.1]; linarith [hε.2]
      exact mul_nonneg (by norm_num) (Real.log_pos this).le
    dsimp [F]
    calc _ ≤ |(1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)) * virasoroKedgeEps c' ε x'| +
            |(3 / (16 * π * x' * c')) * virasoroKedge1Eps c' ε x'| := abs_add_le _ _
      _ = |1 - virasoroV1 x' / (c' * (1 - Real.exp (-4 * π * x')) ^ 2)| * |virasoroKedgeEps c' ε x'| +
            |3 / (16 * π * x' * c')| * |virasoroKedge1Eps c' ε x'| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * (√(2 * c' / 3) * (28 * Real.log (2 / ε))) +
            1 * (√(2 * c' / 3) * (28 * Real.log (2 / ε))) :=
          add_le_add (mul_le_mul hr1_le hK0_bd (abs_nonneg _) (by positivity))
            (mul_le_mul hr2_le hK1_bd (abs_nonneg _) (by positivity))
      _ = _ := by ring
  obtain ⟨B, hB⟩ := hF_bd
  have hmainX_int : IntegrableOn (fun x' =>
      g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * F x' * (2 * c' * x' / 3))
      (Ioi (xiStar / 2)) := by
    refine (hVx_int.const_mul (max B 0)).mono' ?_ ?_
    · have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
        (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
          (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
      have hφ_c : Continuous fun x' : ℝ => c' * x' ^ 2 / 3 := by fun_prop
      have hg_c : Continuous fun x' : ℝ => g (c' * x' ^ 2 / 3) :=
        hg.cont.comp_continuous hφ_c fun _ => show 0 ≤ c' * _ ^ 2 / 3 by positivity
      have hV_cx : Continuous fun x' : ℝ => Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) :=
        hV_cont.comp_continuous hφ_c fun _ => show 0 ≤ c' * _ ^ 2 / 3 by positivity
      exact (((hg_c.continuousOn.mul hV_cx.continuousOn).mul
        hF_cont).mul (by fun_prop : Continuous fun x' : ℝ => 2 * c' * x' / 3).continuousOn).mono
        Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x' hx'
      have hx'_gt : xiStar / 2 < x' := mem_Ioi.mp hx'
      have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) := by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (by positivity)]
        exact virasoroProblem.cardyV_nonneg (by rw [virasoroProblem_totalShift]; linarith) (by positivity)
      have hdx_nn : 0 ≤ 2 * c' * x' / 3 := by nlinarith [xiStar_pos, hc0, hx'_gt]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hV_nn, abs_of_nonneg hdx_nn]
      calc |g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * |F x'| * (2 * c' * x' / 3)
          ≤ |g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) * max B 0 *
              (2 * c' * x' / 3) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              ((hB x' hx'_gt).trans (le_max_left _ _)) (mul_nonneg (abs_nonneg _) hV_nn)) hdx_nn
        _ = max B 0 * (|g (c' * x' ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) *
              (2 * c' * x' / 3)) := by ring
  obtain ⟨_, hcov_t⟩ := change_of_vars_Ioi_half hc0 ha g hg F hF_cont ⟨B, hB⟩ hmainX_int
  have hMain_t : ∫ τ in Ioi (0 : ℝ), (Mainτ τ).re =
      virasoroDualPref c' * ∫ t' in Ioi (c' * (xiStar / 2) ^ 2 / 3),
        g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c')) := by
    rw [hMain_eval]
    dsimp only [mainX]
    rw [hcov_t]
  let E : ℝ := (∫ τ in Ioi (0 : ℝ), ((PsiR τ).re - (Mainτ τ).re)) / virasoroDualPref c'
  refine ⟨E, ?_, ?_⟩
  · have hratio : C_core * 7 / virasoroDualPref c' = 7 * √c' / (π * √3) := by
      unfold C_core virasoroDualPref
      have hs2 : (√2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
      have hs3 : √3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      have hsc : √c' ≠ 0 := (Real.sqrt_pos.mpr hc0).ne'
      have hsx : √xiStar ≠ 0 := (Real.sqrt_pos.mpr xiStar_pos).ne'
      have hs_xi : 1 - Real.exp (-(4 * π * xiStar)) ≠ 0 := by
        have : Real.exp (-(4 * π * xiStar)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [xiStar_pos])
        linarith
      field_simp [hs2, hs3, hsc, hsx, hs_xi]
      rw [show -(π * 4 * xiStar) = -(4 * π * xiStar) by ring, div_self hs_xi]
    have hpow : √c' / c' ^ 2 = 1 / c' ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_two c', ← Real.rpow_sub hc0,
        show (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hc0.le, ← one_div]
    calc |E| = |∫ τ in Ioi (0 : ℝ), ((PsiR τ).re - (Mainτ τ).re)| / virasoroDualPref c' := by
          dsimp [E]; rw [abs_div, abs_of_pos hC₀]
      _ ≤ (C_core * (C_e * M / c' ^ 2) * (7 * Real.log (2 / ε))) / virasoroDualPref c' :=
          div_le_div_of_nonneg_right hrem_abs hC₀.le
      _ = (C_core * 7 / virasoroDualPref c') * (C_e * M * Real.log (2 / ε) / c' ^ 2) := by ring
      _ = (7 * √c' / (π * √3)) * (C_e * M * Real.log (2 / ε) / c' ^ 2) := by rw [hratio]
      _ = (7 * C_e / (π * √3)) * M * (Real.log (2 / ε) * (√c' / c' ^ 2)) := by ring
      _ = (7 * C_e / (π * √3)) * M * (Real.log (2 / ε) / c' ^ (3 / 2 : ℝ)) := by rw [hpow]; ring
  · have hsplit : ∫ τ in Ioi (0 : ℝ), (PsiR τ).re =
        ∫ τ in Ioi (0 : ℝ), ((Mainτ τ).re + ((PsiR τ).re - (Mainτ τ).re)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => by ring
    have hMain_re_int : IntegrableOn (fun τ : ℝ => (Mainτ τ).re) (Ioi 0) :=
      Complex.reCLM.integrable_comp hMain_int
    dsimp only [F] at hMain_t
    dsimp only [E]
    rw [show (∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (1 - (τ : ℂ) * Complex.I)).re) =
        ∫ τ in Ioi (0 : ℝ), (PsiR τ).re from rfl, hsplit,
      MeasureTheory.integral_add hMain_re_int hrem_int, hMain_t, mul_add,
      mul_div_cancel₀ _ hC₀.ne']

/-! ### 3. Unconditional Cauchy dual identity `virasoro_dual_id` (`cts:dual-id`) -/

/-- Un-normalized Cauchy dual identity (`cts:dual-id` before dividing by `M[g]`). -/
lemma virasoro_dual_id_unnorm :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' : ℝ}, c₀ ≤ c' →
      ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
      ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) (1 / 2) →
      |(∫ t in Ioi (c' * xiStar ^ 2 / 3),
          g t * Bessel.besselV (c' / 12) t *
            (1 - virasoroV1 (√(3 * t / c')) /
              (c' * (1 - Real.exp (-4 * π * √(3 * t / c'))) ^ 2)) *
            lowerWeps ε (lowerY (√(3 * t / c'))) *
            Real.sin (lowerThetaEps Gout ε (lowerY (√(3 * t / c'))) -
              2 * π * c' * cumulN (√(3 * t / c')))) +
       (∫ t' in Ioi (c' * (xiStar / 2) ^ 2 / 3),
          g t' * Bessel.besselV (c' / 12) t' *
            ((1 - virasoroV1 (√(3 * t' / c')) /
                (c' * (1 - Real.exp (-4 * π * √(3 * t' / c'))) ^ 2)) *
              virasoroKedgeEps c' ε (√(3 * t' / c')) +
              (3 / (16 * π * √(3 * t' / c') * c')) *
                virasoroKedge1Eps c' ε (√(3 * t' / c'))))| ≤
        C * virasoroProblem.cardyNorm (c' / 12) g *
          (c' ^ (-2 : ℝ) + c' ^ (-(3 / 2 : ℝ)) * Real.log (2 / ε)) := by
  obtain ⟨c₀R, CR, hc₀R, hCR, hR⟩ := lowerDualPsi_right_integral_eq
  refine ⟨c₀R, max 1260000 CR, hc₀R, by positivity, ?_⟩
  intro c' hc' g hg ε hε
  have hc10k : 10000 ≤ c' := hc₀R.trans hc'
  have hc0 : 0 < c' := by linarith
  have hC₀ : 0 < virasoroDualPref c' := virasoroDualPref_pos hc0
  obtain ⟨EL, hEL_bd, hEL_eq⟩ := lowerDualPsi_left_integral_eq hc10k hg hε.1
  obtain ⟨ER, hER_bd, hER_eq⟩ := hR hc' hg hε
  have hcontour := lowerDual_contour_eq hc10k hg hε.1
  rw [hEL_eq, hER_eq] at hcontour
  have hsum_eq :
      (∫ t in Ioi (c' * xiStar ^ 2 / 3),
          g t * Bessel.besselV (c' / 12) t *
            (1 - virasoroV1 (√(3 * t / c')) /
              (c' * (1 - Real.exp (-4 * π * √(3 * t / c'))) ^ 2)) *
            lowerWeps ε (lowerY (√(3 * t / c'))) *
            Real.sin (lowerThetaEps Gout ε (lowerY (√(3 * t / c'))) -
              2 * π * c' * cumulN (√(3 * t / c')))) +
       (∫ t' in Ioi (c' * (xiStar / 2) ^ 2 / 3),
          g t' * Bessel.besselV (c' / 12) t' *
            ((1 - virasoroV1 (√(3 * t' / c')) /
                (c' * (1 - Real.exp (-4 * π * √(3 * t' / c'))) ^ 2)) *
              virasoroKedgeEps c' ε (√(3 * t' / c')) +
              (3 / (16 * π * √(3 * t' / c') * c')) *
                virasoroKedge1Eps c' ε (√(3 * t' / c')))) = -(EL + ER) := by
    nlinarith [hC₀]
  rw [hsum_eq, abs_neg]
  have hc2 : (1 : ℝ) / c' ^ 2 = c' ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hc0.le, Real.rpow_two, one_div]
  have hc32 : Real.log (2 / ε) / c' ^ (3 / 2 : ℝ) = c' ^ (-(3 / 2 : ℝ)) * Real.log (2 / ε) := by
    rw [Real.rpow_neg hc0.le, div_eq_mul_inv, mul_comm]
  have hM_nn : 0 ≤ virasoroProblem.cardyNorm (c' / 12) g :=
    virasoroProblem.cardyNorm_nonneg (by rw [virasoroProblem_totalShift]; linarith) g
  have hlog_nn : 0 ≤ Real.log (2 / ε) := by
    have : 1 < 2 / ε := by rw [lt_div_iff₀ hε.1]; linarith [hε.2]
    exact (Real.log_pos this).le
  have ht1_nn : 0 ≤ c' ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
  have ht2_nn : 0 ≤ c' ^ (-(3 / 2 : ℝ)) * Real.log (2 / ε) :=
    mul_nonneg (Real.rpow_nonneg hc0.le _) hlog_nn
  calc |EL + ER| ≤ |EL| + |ER| := abs_add_le EL ER
    _ ≤ 1260000 * virasoroProblem.cardyNorm (c' / 12) g / c' ^ 2 +
          CR * virasoroProblem.cardyNorm (c' / 12) g * (Real.log (2 / ε) / c' ^ (3 / 2 : ℝ)) :=
        add_le_add hEL_bd hER_bd
    _ = 1260000 * virasoroProblem.cardyNorm (c' / 12) g * c' ^ (-2 : ℝ) +
          CR * virasoroProblem.cardyNorm (c' / 12) g * (c' ^ (-(3 / 2 : ℝ)) * Real.log (2 / ε)) := by
        rw [← hc2, hc32]; ring
    _ ≤ max 1260000 CR * virasoroProblem.cardyNorm (c' / 12) g * c' ^ (-2 : ℝ) +
          max 1260000 CR * virasoroProblem.cardyNorm (c' / 12) g *
            (c' ^ (-(3 / 2 : ℝ)) * Real.log (2 / ε)) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM_nn) ht1_nn)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM_nn) ht2_nn)
    _ = _ := by ring

/-- **Paper label `cts:dual-id`** (`cts:cauchy-dual`, Lemma C6):
Uniform-in-`ε ∈ (0, 1/2)` Cauchy dual identity on `[t(ξ_*), ∞)` and `[t(ξ_*/2), ∞)`. -/
theorem virasoro_dual_id :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' : ℝ}, c₀ ≤ c' →
      ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
      (∃ t : ℝ, 0 ≤ t ∧ g t ≠ 0) →
      ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) (1 / 2) →
      |(∫ t in Ioi (c' * xiStar ^ 2 / 3),
          (g t * Bessel.besselV (c' / 12) t / virasoroProblem.cardyNorm (c' / 12) g) *
            (1 - virasoroV1 (√(3 * t / c')) /
              (c' * (1 - Real.exp (-4 * π * √(3 * t / c'))) ^ 2)) *
            lowerWeps ε (lowerY (√(3 * t / c'))) *
            Real.sin (lowerThetaEps Gout ε (lowerY (√(3 * t / c'))) -
              2 * π * c' * cumulN (√(3 * t / c')))) +
       (∫ t' in Ioi (c' * (xiStar / 2) ^ 2 / 3),
          (g t' * Bessel.besselV (c' / 12) t' / virasoroProblem.cardyNorm (c' / 12) g) *
            ((1 - virasoroV1 (√(3 * t' / c')) /
                (c' * (1 - Real.exp (-4 * π * √(3 * t' / c'))) ^ 2)) *
              virasoroKedgeEps c' ε (√(3 * t' / c')) +
              (3 / (16 * π * √(3 * t' / c') * c')) *
                virasoroKedge1Eps c' ε (√(3 * t' / c'))))| ≤
        C * (c' ^ (-2 : ℝ) + c' ^ (-(3 / 2 : ℝ)) * Real.log (2 / ε)) := by
  obtain ⟨c₀, C, hc₀, hC, hu⟩ := virasoro_dual_id_unnorm
  refine ⟨c₀, C, hc₀, hC, ?_⟩
  intro c' hc' g hg hnz ε hε
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g := cardyNorm_pos_of_nonzero hshift hg hnz
  set M := virasoroProblem.cardyNorm (c' / 12) g
  have h1_congr : Set.EqOn
      (fun t : ℝ => (g t * Bessel.besselV (c' / 12) t / M) *
        (1 - virasoroV1 (√(3 * t / c')) /
          (c' * (1 - Real.exp (-4 * π * √(3 * t / c'))) ^ 2)) *
        lowerWeps ε (lowerY (√(3 * t / c'))) *
        Real.sin (lowerThetaEps Gout ε (lowerY (√(3 * t / c'))) -
          2 * π * c' * cumulN (√(3 * t / c'))))
      (fun t : ℝ => M⁻¹ * (g t * Bessel.besselV (c' / 12) t *
        (1 - virasoroV1 (√(3 * t / c')) /
          (c' * (1 - Real.exp (-4 * π * √(3 * t / c'))) ^ 2)) *
        lowerWeps ε (lowerY (√(3 * t / c'))) *
        Real.sin (lowerThetaEps Gout ε (lowerY (√(3 * t / c'))) -
          2 * π * c' * cumulN (√(3 * t / c'))))) (Ioi (c' * xiStar ^ 2 / 3)) := fun t _ => by ring
  have h2_congr : Set.EqOn
      (fun t' : ℝ => (g t' * Bessel.besselV (c' / 12) t' / M) *
        ((1 - virasoroV1 (√(3 * t' / c')) /
            (c' * (1 - Real.exp (-4 * π * √(3 * t' / c'))) ^ 2)) *
          virasoroKedgeEps c' ε (√(3 * t' / c')) +
          (3 / (16 * π * √(3 * t' / c') * c')) *
            virasoroKedge1Eps c' ε (√(3 * t' / c'))))
      (fun t' : ℝ => M⁻¹ * (g t' * Bessel.besselV (c' / 12) t' *
        ((1 - virasoroV1 (√(3 * t' / c')) /
            (c' * (1 - Real.exp (-4 * π * √(3 * t' / c'))) ^ 2)) *
          virasoroKedgeEps c' ε (√(3 * t' / c')) +
          (3 / (16 * π * √(3 * t' / c') * c')) *
            virasoroKedge1Eps c' ε (√(3 * t' / c')))))
      (Ioi (c' * (xiStar / 2) ^ 2 / 3)) := fun t' _ => by ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h1_congr, MeasureTheory.integral_const_mul,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h2_congr, MeasureTheory.integral_const_mul,
    ← mul_add, abs_mul, abs_of_pos (inv_pos.mpr hM_pos), ← div_eq_inv_mul, div_le_iff₀ hM_pos]
  exact (hu hc' hg hε).trans_eq (by ring)

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_dual_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_dual_id
