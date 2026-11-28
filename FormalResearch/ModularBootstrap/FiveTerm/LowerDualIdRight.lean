module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualIdLeft

/-!
# Cauchy Dual Identity — Right Edge (`cts:dual-id`, Part 2)

Bounds `∫_{0}^∞ W̃_ε(tanh(πτ/4)) dτ ≤ 7 log(2/ε)`, rewrites the right-edge integrand
`lowerDualPsi c' ε 0 g (1 - i τ)` via `gout_coupling`, `lowerMt_sigma`, `phaseLock_identity`,
and `edge_hankel_two_virasoro`, applies Fubini to produce `virasoroKedgeEps` and
`virasoroKedge1Eps`, and reduces the right-edge integral to `cts:dual-id` with error
`O(M[g] c'^{-3/2} log(2/ε))`.
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

/-! ### 1. Uniform-in-`ε` bound for `∫₀^∞ W̃_ε(tanh(πτ/4)) dτ` -/

lemma lowerWeps_tanh_le_exp {ε τ : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (hτ : 0 < τ) :
    lowerWeps ε (Real.tanh (π * τ / 4)) ≤ 1 ∧
      lowerWeps ε (Real.tanh (π * τ / 4)) ≤ 64 / ε ^ 2 * Real.exp (-(π * τ)) := by
  have hy_mem : Real.tanh (π * τ / 4) ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨?_, Real.tanh_lt_one _⟩
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])) (Real.cosh_pos _)
  have hx_gt : xiStar < xT τ := xT_gt_xiStar hτ
  have h1 : lowerWeps ε (Real.tanh (π * τ / 4)) ≤ 1 := by
    rw [← lowerY_xT hτ.le]
    exact (lowerWeps_mem_Icc hε.1.le hx_gt).2
  have h1y : 1 - Real.tanh (π * τ / 4) ^ 2 ≤ 4 * Real.exp (-(π * τ / 2)) := by
    rw [one_sub_tanh_sq, one_div]
    have hch : Real.exp (π * τ / 4) / 2 ≤ Real.cosh (π * τ / 4) := by
      rw [Real.cosh_eq]; have := Real.exp_pos (-(π * τ / 4)); linarith
    have hsq : Real.exp (π * τ / 2) / 4 ≤ Real.cosh (π * τ / 4) ^ 2 := by
      have : (Real.exp (π * τ / 4) / 2) ^ 2 ≤ Real.cosh (π * τ / 4) ^ 2 := by gcongr
      have heq : (Real.exp (π * τ / 4) / 2) ^ 2 = Real.exp (π * τ / 2) / 4 := by
        rw [div_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
      linarith
    rw [Real.exp_neg]
    calc (Real.cosh (π * τ / 4) ^ 2)⁻¹ ≤ (Real.exp (π * τ / 2) / 4)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 4 * (Real.exp (π * τ / 2))⁻¹ := by field_simp
  have hz_cl : Complex.I * (Real.tanh (π * τ / 4) : ℂ) ∈ closure halfDisc :=
    (slit_mem_diff hy_mem).1
  have hdec := norm_lowerMt_decay hε.1 hz_cl
  have h1z2 : (1 : ℂ) + (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2 =
      ((1 - Real.tanh (π * τ / 4) ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  have h1y_nn : 0 ≤ 1 - Real.tanh (π * τ / 4) ^ 2 := by nlinarith [hy_mem.1, hy_mem.2]
  rw [h1z2, Complex.norm_real, Real.norm_of_nonneg h1y_nn] at hdec
  have h2 : ‖lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ))‖ ≤
      (8 / ε) * Real.exp (-(π * τ / 2)) := by
    calc ‖lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ))‖
        ≤ ((1 + ε) / ε) * (1 - Real.tanh (π * τ / 4) ^ 2) := hdec
      _ ≤ (2 / ε) * (4 * Real.exp (-(π * τ / 2))) :=
          mul_le_mul (div_le_div_of_nonneg_right (by linarith [hε.2]) hε.1.le) h1y h1y_nn
            (div_nonneg zero_le_two hε.1.le)
      _ = (8 / ε) * Real.exp (-(π * τ / 2)) := by ring
  refine ⟨h1, ?_⟩
  unfold lowerWeps
  calc ‖lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ))‖ ^ 2
      ≤ ((8 / ε) * Real.exp (-(π * τ / 2))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = 64 / ε ^ 2 * Real.exp (-(π * τ)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2 <;> [ring; (push_cast; ring)]

lemma lowerWeps_tanh_Ioi_bound {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) :
    IntegrableOn (fun τ : ℝ => lowerWeps ε (Real.tanh (π * τ / 4))) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), lowerWeps ε (Real.tanh (π * τ / 4)) ≤ 7 * Real.log (2 / ε) := by
  have hpi := Real.pi_pos
  have htanh_c : Continuous fun τ : ℝ => Real.tanh (π * τ / 4) := by
    have : (fun τ : ℝ => Real.tanh (π * τ / 4)) =
        fun τ => Real.sinh (π * τ / 4) / Real.cosh (π * τ / 4) :=
      funext fun τ => Real.tanh_eq_sinh_div_cosh _
    rw [this]
    exact (Real.continuous_sinh.comp (by fun_prop)).div (Real.continuous_cosh.comp (by fun_prop))
      fun τ => (Real.cosh_pos _).ne'
  have hcont : Continuous (fun τ : ℝ => lowerWeps ε (Real.tanh (π * τ / 4))) := by
    unfold lowerWeps lowerMt
    refine (Continuous.norm ?_).pow 2
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
  have hint : IntegrableOn (fun τ : ℝ => lowerWeps ε (Real.tanh (π * τ / 4))) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul (64 / ε ^ 2)).mono'
      (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), neg_mul]
    exact (lowerWeps_tanh_le_exp hε (mem_Ioi.mp hτ)).2
  have hlog_gt : 1 < Real.log (2 / ε) := by
    have h4 : Real.exp 1 < 2 / ε := by
      have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h2e : 4 < 2 / ε := by rw [lt_div_iff₀ hε.1]; linarith [hε.2]
      linarith
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) h4
  set τ₀ : ℝ := (2 / π) * Real.log (2 / ε)
  have hτ₀_pos : 0 < τ₀ := by positivity
  have hsplit : Ioi (0 : ℝ) = Ioc 0 τ₀ ∪ Ioi τ₀ := (Ioc_union_Ioi_eq_Ioi hτ₀_pos.le).symm
  have h_Ioc : IntegrableOn (fun τ : ℝ => lowerWeps ε (Real.tanh (π * τ / 4))) (Ioc 0 τ₀) :=
    hint.mono_set Ioc_subset_Ioi_self
  have h_Ioi : IntegrableOn (fun τ : ℝ => lowerWeps ε (Real.tanh (π * τ / 4))) (Ioi τ₀) :=
    hint.mono_set (Ioi_subset_Ioi hτ₀_pos.le)
  have h1 : ∫ τ in Ioc (0 : ℝ) τ₀, lowerWeps ε (Real.tanh (π * τ / 4)) ≤ Real.log (2 / ε) := by
    calc ∫ τ in Ioc (0 : ℝ) τ₀, lowerWeps ε (Real.tanh (π * τ / 4))
        ≤ ∫ _τ in Ioc (0 : ℝ) τ₀, (1 : ℝ) := by
          refine setIntegral_mono_on h_Ioc (integrableOn_const (hs := measure_Ioc_lt_top.ne))
            measurableSet_Ioc fun τ hτ => ?_
          exact (lowerWeps_tanh_le_exp hε hτ.1).1
      _ = τ₀ := by simp [hτ₀_pos.le]
      _ ≤ 1 * Real.log (2 / ε) := by
          have : 2 / π ≤ 1 := (div_le_one hpi).mpr (by linarith [Real.pi_gt_three])
          exact mul_le_mul_of_nonneg_right this (by linarith)
      _ = Real.log (2 / ε) := one_mul _
  have h2_exp : ∫ τ in Ioi τ₀, Real.exp (-π * τ) = Real.exp (-π * τ₀) / π := by
    have hF : ∀ τ ∈ Ici τ₀, HasDerivAt (fun x : ℝ => -Real.exp (-π * x) / π) (Real.exp (-π * τ)) τ := fun τ _ => by
      have hd := (((hasDerivAt_id' τ).const_mul (-π)).exp.neg).div_const π
      refine hd.congr_deriv ?_
      field_simp [hpi.ne']
    have hT : Tendsto (fun x : ℝ => -Real.exp (-π * x) / π) atTop (𝓝 0) := by
      have h0 : Tendsto (fun x : ℝ => -(Real.exp (-π * x)) / π) atTop (𝓝 (-0 / π)) :=
        ((Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -π < 0))).neg).div_const π
      simpa using h0
    have h2_raw := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hF
      (integrableOn_exp_mul_Ioi (by linarith : -π < 0) τ₀) hT
    rw [h2_raw]; ring
  have h2 : ∫ τ in Ioi τ₀, lowerWeps ε (Real.tanh (π * τ / 4)) ≤ 6 * Real.log (2 / ε) := by
    have hexp_τ₀ : Real.exp (-π * τ₀) = ε ^ 2 / 4 := by
      have heq : -π * τ₀ = -2 * Real.log (2 / ε) := by dsimp [τ₀]; field_simp [hpi.ne']
      rw [heq, show -2 * Real.log (2 / ε) = Real.log ((2 / ε) ^ (-2 : ℝ)) by
        rw [Real.log_rpow (by positivity [hε.1])], Real.exp_log (by positivity [hε.1])]
      rw [Real.rpow_neg (by positivity [hε.1]), Real.rpow_two, div_pow, inv_div]
      norm_num
    calc ∫ τ in Ioi τ₀, lowerWeps ε (Real.tanh (π * τ / 4))
        ≤ ∫ τ in Ioi τ₀, (64 / ε ^ 2) * Real.exp (-π * τ) := by
          refine setIntegral_mono_on h_Ioi ((integrableOn_exp_mul_Ioi (by linarith : -π < 0) τ₀).const_mul _)
            measurableSet_Ioi fun τ hτ => ?_
          simpa [neg_mul] using (lowerWeps_tanh_le_exp hε (hτ₀_pos.trans (mem_Ioi.mp hτ))).2
      _ = (64 / ε ^ 2) * (Real.exp (-π * τ₀) / π) := by
          rw [MeasureTheory.integral_const_mul, h2_exp]
      _ = 16 / π := by rw [hexp_τ₀]; field_simp [hε.1.ne', hpi.ne']; ring
      _ ≤ 6 * 1 := by
          rw [div_le_iff₀ hpi]; linarith [Real.pi_gt_three]
      _ ≤ 6 * Real.log (2 / ε) := by gcongr
  refine ⟨hint, ?_⟩
  rw [hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc h_Ioi]
  linarith

/-! ### 2. `v = vT τ` coordinate rewrite for `K_edge^ε` and `K_{edge,1}^ε` -/

lemma kedgeEpsIntegrand_vT {c' ε x' τ : ℝ} (hτ : 0 ≤ τ) :
    kedgeEpsIntegrand c' ε x' (vT τ) =
      lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2 *
        Complex.exp (Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ)) *
        ((((1 - Real.exp (-(4 * π * xT τ))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
          √(edgeF' (vT τ)) : ℝ)) : ℂ) *
        Complex.exp (Complex.I * ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ)) := by
  unfold kedgeEpsIntegrand
  rw [edgeF_vT τ, lowerY_xT hτ, phiDual_eq (vT_nonneg hτ), edgeF_vT τ]

lemma continuousOn_kedgeEpsIntegrand (c' : ℝ) {ε : ℝ} (hε : 0 < ε) (x' : ℝ) :
    ContinuousOn (fun v : ℝ => kedgeEpsIntegrand c' ε x' v) (Ici 0) := by
  have hy_lt1 : ∀ v : ℝ, 0 ≤ v → lowerY (edgeF v) ∈ Ioo (-1 : ℝ) 1 := fun v hv => by
    have hx : xiStar ≤ edgeF v := by rw [← edgeF_zero]; exact edgeF_strictMonoOn.monotoneOn le_rfl hv hv
    have hch : √2 ≤ Real.cosh (π * edgeF v) := by
      rw [← cosh_pi_xiStar]
      exact Real.cosh_le_cosh.mpr (by
        rw [abs_of_pos (mul_pos Real.pi_pos xiStar_pos), abs_of_pos (mul_pos Real.pi_pos (xiStar_pos.trans_le hx))]
        exact mul_le_mul_of_nonneg_left hx Real.pi_pos.le)
    have hden_pos : 0 < Real.cosh (π * edgeF v) + √2 := by positivity [Real.cosh_pos (π * edgeF v)]
    have hy1 : lowerY (edgeF v) < 1 := by
      unfold lowerY
      rw [Real.sqrt_lt' zero_lt_one, one_pow, div_lt_one hden_pos]
      linarith [Real.sqrt_pos.mpr zero_lt_two]
    have hy0 : 0 ≤ lowerY (edgeF v) := by unfold lowerY; positivity
    exact ⟨by linarith, hy1⟩
  have hF_c : Continuous edgeF := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt
  have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
  have hy_c : ContinuousOn (fun v => lowerY (edgeF v)) (Ici 0) := by
    unfold lowerY
    exact (Real.continuous_sqrt.continuousOn.comp
      (((Real.continuous_cosh.comp (continuous_const.mul hF_c)).sub continuous_const).continuousOn.div
        ((Real.continuous_cosh.comp (continuous_const.mul hF_c)).add continuous_const).continuousOn
        fun _ _ => (add_pos (Real.cosh_pos _) (Real.sqrt_pos.mpr zero_lt_two)).ne')
      fun _ _ => mem_univ _)
  have hmt_c : ContinuousOn (fun v => lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2) (Ici 0) := by
    have hmt : ContinuousOn (fun y : ℝ => lowerMt ε (Complex.I * (y : ℂ)) ^ 2) (Ioo (-1) 1) := by
      refine ContinuousOn.pow ?_ 2
      unfold lowerMt
      refine (continuousOn_const.mul (continuousOn_const.add ((continuousOn_const.mul
        Complex.continuous_ofReal.continuousOn).pow 2))).div
        ((continuousOn_const.add ((continuousOn_const.mul Complex.continuous_ofReal.continuousOn).pow 2)).add
          (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul Complex.continuous_ofReal.continuousOn))))
        fun y hy => by
          intro h
          rw [show (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)) =
            ((1 - y ^ 2 + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ) by
            rw [mul_pow, Complex.I_sq]; push_cast; ring] at h
          have hre := congrArg Complex.re h
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hre
          have hy2 : y ^ 2 < 1 := by nlinarith [hy.1, hy.2]
          nlinarith
    exact hmt.comp hy_c hy_lt1
  have hth_c : ContinuousOn (fun v => Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ))) (Ici 0) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn.comp
      (thetaOut_soft.2.2.comp hy_c hy_lt1) fun _ _ => mem_univ _
  have hphi_c : Continuous fun v : ℝ => phiDual v x' := by
    unfold phiDual
    refine continuous_const.mul (intervalIntegral.continuous_primitive (fun a b => ?_) 0)
    exact ((hF_c.sub continuous_const).intervalIntegrable a b)
  have hreal_c : Continuous fun v : ℝ =>
      (1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' v) := by
    have h1 : Continuous fun v : ℝ => (1 - Real.exp (-(4 * π * edgeF v))) ^ 2 := by fun_prop
    have h2 : Continuous fun v : ℝ => √(edgeF' v) := Real.continuous_sqrt.comp hF'_c
    exact (h1.div_const _).mul h2
  have hexp_c : Continuous fun v : ℝ => Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := by
    have h1 : Continuous fun v : ℝ => c' * phiDual v x' := continuous_const.mul hphi_c
    have h2 : Continuous fun v : ℝ => Complex.I * ((c' * phiDual v x' : ℝ) : ℂ) :=
      continuous_const.mul (Complex.continuous_ofReal.comp h1)
    exact Complex.continuous_exp.comp h2
  unfold kedgeEpsIntegrand
  exact ((hmt_c.mul hth_c).mul (Complex.continuous_ofReal.comp hreal_c).continuousOn).mul hexp_c.continuousOn

lemma kedgeEps_integrable_and_tau_eq (c' : ℝ) {ε x' : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 2))
    (hx' : xiStar / 2 ≤ x') :
    IntegrableOn (fun v : ℝ => kedgeEpsIntegrand c' ε x' v) (Ioi 0) ∧
    IntegrableOn (fun v : ℝ => kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) (Ioi 0) ∧
    (∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v =
      ∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)) ∧
    (∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹ =
      ∫ τ in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' (vT τ) *
        ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)) := by
  have hpi := Real.pi_pos
  have hx1 : (1 : ℝ) / 10 ≤ x' := by linarith [Bessel.one_fifth_le_xiStar]
  have hq4 : 1 / 4 ≤ (1 - Real.exp (-(4 * π * x'))) ^ 2 := by
    have h4x : 1 ≤ 4 * π * x' := by nlinarith [Real.pi_gt_three]
    have hexp_le : Real.exp (-(4 * π * x')) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      calc (Real.exp (4 * π * x'))⁻¹ ≤ (1 + 4 * π * x')⁻¹ :=
            inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (4 * π * x')])
        _ ≤ 2⁻¹ := inv_anti₀ zero_lt_two (by linarith)
        _ = 1 / 2 := by norm_num
    nlinarith
  obtain ⟨hW_int, _⟩ := lowerWeps_tanh_Ioi_bound hε
  have hinv_le1 : ∀ v : ℝ, ‖((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹‖ ≤ 1 := fun v => by
    rw [norm_inv]
    have hge1 : 1 ≤ ‖(1 : ℂ) - 2 * Complex.I * (v : ℂ)‖ := by
      rw [show (1 : ℂ) - 2 * Complex.I * (v : ℂ) = (1 : ℝ) + ((-2 * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_add_mul_I]
      exact Real.one_le_sqrt.mpr (by nlinarith)
    exact inv_le_one_of_one_le₀ hge1
  have hτ_bd : ∀ τ : ℝ, 0 ≤ τ →
      ‖kedgeEpsIntegrand c' ε x' (vT τ)‖ ≤ 4 * lowerWeps ε (Real.tanh (π * τ / 4)) := fun τ hτ => by
    have hv_nn : 0 ≤ vT τ := vT_nonneg hτ
    have hF'_le1 : edgeF' (vT τ) ≤ 1 := by
      unfold edgeF'
      have hsq : Real.sinh (π * vT τ) ≤ √(1 + Real.cosh (π * vT τ) ^ 2) :=
        Real.le_sqrt_of_sq_le (by linarith [Real.cosh_sq (π * vT τ)])
      exact div_le_one_of_le₀ hsq (Real.sqrt_nonneg _)
    have hF'_nn : 0 ≤ edgeF' (vT τ) := edgeF'_nonneg hv_nn
    have hsub1 : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 ≤ 1 := by
      have : 0 ≤ Real.exp (-(4 * π * xT τ)) := (Real.exp_pos _).le
      have : Real.exp (-(4 * π * xT τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [(xT_pos τ).le])
      nlinarith
    have hmt_norm : ‖lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2‖ =
        lowerWeps ε (Real.tanh (π * τ / 4)) := by rw [norm_pow]; rfl
    rw [kedgeEpsIntegrand_vT hτ, norm_mul, norm_mul, norm_mul, hmt_norm]
    rw [show Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ) =
          (thetaOut (Real.tanh (π * τ / 4)) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one,
      show Complex.I * ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ) =
          ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hW_nn : 0 ≤ lowerWeps ε (Real.tanh (π * τ / 4)) := sq_nonneg _
    have hfrac : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
        √(edgeF' (vT τ)) ≤ 4 := by
      calc (1 - Real.exp (-(4 * π * xT τ))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
            √(edgeF' (vT τ))
          ≤ (1 / (1 / 4 : ℝ)) * 1 :=
            mul_le_mul (div_le_div₀ zero_le_one hsub1 (by norm_num) hq4)
              (Real.sqrt_le_one.mpr hF'_le1) (Real.sqrt_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    nlinarith
  have hτ_bd_vD : ∀ τ : ℝ, 0 ≤ τ →
      ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ ≤
        4 * lowerWeps ε (Real.tanh (π * τ / 4)) := fun τ hτ => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vD_pos τ).le]
    calc ‖kedgeEpsIntegrand c' ε x' (vT τ)‖ * vD τ
        ≤ (4 * lowerWeps ε (Real.tanh (π * τ / 4))) * 1 :=
          mul_le_mul (hτ_bd τ hτ) (vD_le_one τ) (vD_pos τ).le (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 4 * lowerWeps ε (Real.tanh (π * τ / 4)) := mul_one _
  have hτ1_bd_vD : ∀ τ : ℝ, 0 ≤ τ →
      ‖kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖ ≤
        4 * lowerWeps ε (Real.tanh (π * τ / 4)) := fun τ hτ => by
    calc ‖kedgeEpsIntegrand c' ε x' (vT τ) * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ * (vD τ : ℂ)‖
        = ‖kedgeEpsIntegrand c' ε x' (vT τ) * (vD τ : ℂ)‖ *
            ‖((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹‖ := by
          rw [mul_assoc (kedgeEpsIntegrand c' ε x' (vT τ)), mul_comm _ (vD τ : ℂ), ← mul_assoc, norm_mul]
      _ ≤ (4 * lowerWeps ε (Real.tanh (π * τ / 4))) * 1 :=
            mul_le_mul (hτ_bd_vD τ hτ) (hinv_le1 _) (norm_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 4 * lowerWeps ε (Real.tanh (π * τ / 4)) := mul_one _
  -- General change-of-variables helper on `Ioi 0` under `v = vT τ`
  have hcov_gen : ∀ (H : ℝ → ℂ), ContinuousOn H (Ici 0) →
      (∀ τ : ℝ, 0 ≤ τ → ‖H (vT τ) * (vD τ : ℂ)‖ ≤ 4 * lowerWeps ε (Real.tanh (π * τ / 4))) →
      IntegrableOn H (Ioi 0) ∧
        (∫ v in Ioi (0 : ℝ), H v = ∫ τ in Ioi (0 : ℝ), H (vT τ) * (vD τ : ℂ)) := by
    intro H hH_c hH_bd
    have hτ_int : IntegrableOn (fun τ => H (vT τ) * (vD τ : ℂ)) (Ioi 0) := by
      refine (hW_int.const_mul 4).mono' ?_ ?_
      · exact ((hH_c.comp continuous_vT.continuousOn fun τ hτ => vT_nonneg (mem_Ioi.mp hτ).le).mul
          (Complex.continuous_ofReal.comp continuous_vD).continuousOn).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
        exact hH_bd τ (mem_Ioi.mp hτ).le
    have hcov_R : ∀ R : ℝ, 0 ≤ R →
        ∫ v in (0 : ℝ)..(vT R), H v = ∫ τ in (0 : ℝ)..R, H (vT τ) * (vD τ : ℂ) := fun R hR => by
      have hd : ∀ τ ∈ uIcc (0 : ℝ) R, HasDerivAt vT (vD τ) τ := fun τ _ => hasDerivAt_vT τ
      have hcont_t : ContinuousOn H (vT '' uIcc 0 R) := by
        refine hH_c.mono ?_
        rintro v ⟨τ, hτ, rfl⟩
        rw [uIcc_of_le hR] at hτ
        exact vT_nonneg hτ.1
      have hiL : IntervalIntegrable H volume 0 (vT R) :=
        (hH_c.mono fun x hx => by rw [uIcc_of_le (vT_nonneg hR)] at hx; exact hx.1).intervalIntegrable
      have hiR : IntervalIntegrable (fun τ => H (vT τ) * (vD τ : ℂ)) volume 0 R :=
        ((hH_c.comp continuous_vT.continuousOn fun τ hτ => by
          rw [uIcc_of_le hR] at hτ; exact vT_nonneg hτ.1).mul
          (Complex.continuous_ofReal.comp continuous_vD).continuousOn).intervalIntegrable
      have hre := intervalIntegral.integral_comp_mul_deriv' hd continuous_vD.continuousOn
        (Complex.continuous_re.comp_continuousOn hcont_t)
      have him := intervalIntegral.integral_comp_mul_deriv' hd continuous_vD.continuousOn
        (Complex.continuous_im.comp_continuousOn hcont_t)
      dsimp only [Function.comp] at hre him
      rw [vT_zero] at hre him
      apply Complex.ext
      · rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hiL,
          ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hiR]
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        exact hre.symm
      · rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hiL,
          ← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hiR]
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_add]
        exact him.symm
    have hmax_tend : Tendsto (fun R : ℝ => vT (max R 0)) atTop atTop :=
      tendsto_vT_atTop.comp (tendsto_atTop_mono (fun R => le_max_left R 0) tendsto_id)
    have hV_int : IntegrableOn H (Ioi 0) := by
      refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (∫ τ in Ioi (0 : ℝ), 4 * lowerWeps ε (Real.tanh (π * τ / 4))) 0 ?_ hmax_tend ?_
      · intro R
        have hIcc : IntegrableOn H (Icc 0 (vT (max R 0))) :=
          (hH_c.mono Icc_subset_Ici_self).integrableOn_Icc
        exact hIcc.mono_set Ioc_subset_Icc_self
      · refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
        rw [max_eq_left hR]
        have hd : ∀ τ ∈ uIcc (0 : ℝ) R, HasDerivAt vT (vD τ) τ := fun τ _ => hasDerivAt_vT τ
        have hcont_n : ContinuousOn (fun v => ‖H v‖) (vT '' uIcc 0 R) := by
          refine (hH_c.norm).mono ?_
          rintro v ⟨τ, hτ, rfl⟩
          rw [uIcc_of_le hR] at hτ
          exact vT_nonneg hτ.1
        have hcov_n := intervalIntegral.integral_comp_mul_deriv' hd continuous_vD.continuousOn hcont_n
        dsimp only [Function.comp] at hcov_n
        rw [vT_zero] at hcov_n
        have hnorm_v : ∫ v in (0 : ℝ)..(vT R), ‖H v‖ =
            ∫ τ in (0 : ℝ)..R, ‖H (vT τ) * (vD τ : ℂ)‖ := by
          rw [← hcov_n]
          refine intervalIntegral.integral_congr fun τ _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vD_pos τ).le]
        rw [hnorm_v, intervalIntegral.integral_of_le hR]
        calc ∫ τ in Ioc (0 : ℝ) R, ‖H (vT τ) * (vD τ : ℂ)‖
            ≤ ∫ τ in Ioi (0 : ℝ), ‖H (vT τ) * (vD τ : ℂ)‖ :=
              setIntegral_mono_set (hτ_int.norm) (ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => norm_nonneg _)
                Ioc_subset_Ioi_self.eventuallySubset
          _ ≤ ∫ τ in Ioi (0 : ℝ), 4 * lowerWeps ε (Real.tanh (π * τ / 4)) :=
              setIntegral_mono_on (hτ_int.norm) (hW_int.const_mul 4) measurableSet_Ioi
                fun τ hτ => hH_bd τ (mem_Ioi.mp hτ).le
    refine ⟨hV_int, ?_⟩
    have hL : Tendsto (fun R : ℝ => ∫ v in (0 : ℝ)..(vT R), H v) atTop (𝓝 (∫ v in Ioi (0 : ℝ), H v)) :=
      (intervalIntegral_tendsto_integral_Ioi 0 hV_int tendsto_id).comp tendsto_vT_atTop
    have hR : Tendsto (fun R : ℝ => ∫ τ in (0 : ℝ)..R, H (vT τ) * (vD τ : ℂ)) atTop
        (𝓝 (∫ τ in Ioi (0 : ℝ), H (vT τ) * (vD τ : ℂ))) :=
      intervalIntegral_tendsto_integral_Ioi 0 hτ_int tendsto_id
    exact tendsto_nhds_unique (hL.congr' (eventually_ge_atTop 0 |>.mono hcov_R)) hR
  have hcont_k : ContinuousOn (fun v : ℝ => kedgeEpsIntegrand c' ε x' v) (Ici 0) :=
    continuousOn_kedgeEpsIntegrand c' hε.1 x'
  have hcont_k1 : ContinuousOn (fun v : ℝ => kedgeEpsIntegrand c' ε x' v *
      ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) (Ici 0) := by
    refine hcont_k.mul (ContinuousOn.inv₀ (by fun_prop) fun v _ => ?_)
    intro h; have hre := congrArg Complex.re h; simp at hre
  obtain ⟨h0_int, h0_eq⟩ := hcov_gen _ hcont_k hτ_bd_vD
  obtain ⟨h1_int, h1_eq⟩ := hcov_gen _ hcont_k1 hτ1_bd_vD
  exact ⟨h0_int, h1_int, h0_eq, h1_eq⟩

/-! ### 3. Right-edge integrand factorisation -/

def lowerDualRightCore (ε τ : ℝ) : ℂ :=
  ((π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2) *
    (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ : ℝ) : ℂ) *
    lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2 *
    Complex.exp (Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ))

private lemma edgeF'_vT_eq {τ : ℝ} (hτ : 0 < τ) :
    edgeF' (vT τ) = 2 * Real.tanh (π * τ / 4) / (1 + Real.tanh (π * τ / 4) ^ 2) := by
  have hpi := Real.pi_pos
  have hsh : Real.sinh (π * vT τ) = √2 * Real.sinh (π * τ / 2) := by
    unfold vT; rw [mul_div_cancel₀ _ hpi.ne', Real.sinh_arsinh]
  have hch : √(1 + Real.cosh (π * vT τ) ^ 2) = √2 * Real.cosh (π * τ / 2) := by
    rw [cosh_pi_mul_vT, Real.sq_sqrt (Real.cosh_pos _).le, one_add_cosh_eq,
      Real.sqrt_mul zero_le_two, Real.sqrt_sq (Real.cosh_pos _).le]
  unfold edgeF'
  rw [hsh, hch]
  have hs2 : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
  rw [show √2 * Real.sinh (π * τ / 2) / (√2 * Real.cosh (π * τ / 2)) =
      Real.tanh (π * τ / 2) by rw [Real.tanh_eq_sinh_div_cosh]; field_simp]
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    show π * τ / 2 = 2 * (π * τ / 4) by ring, Real.sinh_two_mul, Real.cosh_two_mul]
  have hc4 : Real.cosh (π * τ / 4) ≠ 0 := (Real.cosh_pos _).ne'
  have h1c : 1 ≤ Real.cosh (π * τ / 4) := Real.one_le_cosh _
  have h2c : 2 * Real.cosh (π * τ / 4) ^ 2 - 1 ≠ 0 := by nlinarith
  have hcs := Real.cosh_sq_sub_sinh_sq (π * τ / 4)
  field_simp

private lemma cpow_div_ofReal_half {a : ℂ} {r : ℝ} (ha_im : 0 < a.im) (hr : 0 < r) :
    (a / (r : ℂ)) ^ (1 / 2 : ℂ) = a ^ (1 / 2 : ℂ) / ((√r : ℝ) : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by rw [h, Complex.zero_im] at ha_im; exact lt_irrefl 0 ha_im
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hdiv0 : a / (r : ℂ) ≠ 0 := div_ne_zero ha0 hr0
  rw [Complex.cpow_def_of_ne_zero hdiv0, Complex.cpow_def_of_ne_zero ha0]
  have harg : (a / (r : ℂ)).arg = a.arg := by
    rw [div_eq_mul_inv, show ((r : ℂ)⁻¹) = (((r⁻¹ : ℝ) : ℝ) : ℂ) by push_cast; rfl, mul_comm]
    exact Complex.arg_real_mul a (inv_pos.mpr hr)
  have hnorm : ‖a / (r : ℂ)‖ = ‖a‖ / r := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hlog : Complex.log (a / (r : ℂ)) = Complex.log a - (Real.log r : ℂ) := by
    unfold Complex.log
    rw [hnorm, harg, Real.log_div (norm_ne_zero_iff.mpr ha0) hr.ne']
    push_cast; ring
  rw [hlog, sub_mul, Complex.exp_sub, show (Real.log r : ℂ) * (1 / 2 : ℂ) =
    ((Real.log r * (1 / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    ← Real.rpow_def_of_pos hr, ← Real.sqrt_eq_rpow]

lemma lowerDualPsi_right_factor_eq {c' ε τ : ℝ} (_hε : 0 ≤ ε)
    (g : ℝ → ℝ) (hτ : 0 < τ) :
    lowerDualPsi c' ε 0 g (1 - (τ : ℂ) * Complex.I) =
      lowerDualRightCore ε τ * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) *
        hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) *
        Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) := by
  let y : ℝ := Real.tanh (π * τ / 4)
  have hy_mem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨by dsimp [y]; rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])) (Real.cosh_pos _),
      Real.tanh_lt_one _⟩
  let z : ℂ := starRingEnd ℂ (wPt y)
  have hz_eq : sTan (1 - (τ : ℂ) * Complex.I) = z := by
    rw [show (1 - (τ : ℂ) * Complex.I) = starRingEnd ℂ (1 + (τ : ℂ) * Complex.I) by
      rw [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring,
      sTan_conj, sTan_one_add_eq_wPt]
  have hwz : wPt y * z = 1 := wPt_mul_conj y
  have hw_ne : wPt y ≠ 0 := left_ne_zero_of_mul_eq_one hwz
  have hz_ne : z ≠ 0 := right_ne_zero_of_mul_eq_one hwz
  have hzw : z * wPt y = 1 := by rw [mul_comm]; exact hwz
  have h1y_pos : 0 < 1 - y ^ 2 := by nlinarith [hy_mem.1, hy_mem.2]
  have h1y2_pos : 0 < 1 + y ^ 2 := by positivity
  have h1z2_eq : (1 : ℂ) + z ^ 2 = z * ((2 * (1 - y ^ 2) / (1 + y ^ 2) : ℝ) : ℂ) := by
    have hsum : wPt y + z = ((2 * (1 - y ^ 2) / (1 + y ^ 2) : ℝ) : ℂ) := by
      dsimp [z]
      rw [Complex.add_conj, re_wPt]
      push_cast; ring
    calc (1 : ℂ) + z ^ 2 = z * (wPt y + z) := by rw [mul_add, hzw, ← sq]
      _ = z * ((2 * (1 - y ^ 2) / (1 + y ^ 2) : ℝ) : ℂ) := by rw [hsum]
  have h1z2_ne : (1 : ℂ) + z ^ 2 ≠ 0 := by
    rw [h1z2_eq]
    exact mul_ne_zero hz_ne (Complex.ofReal_ne_zero.mpr (by positivity))
  have hm0 : lowerMt 0 z = 1 := by unfold lowerMt; simp [h1z2_ne]
  have hm_eq : lowerMt ε z = lowerMt ε (Complex.I * (y : ℂ)) := by
    dsimp [z]; rw [conj_wPt]; exact lowerMt_sigma ε (slit_mem_diff hy_mem).1
  have hGout_id : Gout z * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) =
      Gout (Complex.I * (y : ℂ)) * Kedge y := (gout_coupling hy_mem).symm
  have hzG : z * Gout z * (((π / 4 : ℝ) : ℂ) * (1 + z ^ 2)) =
      ((π / 4 * (1 - y ^ 2) / y ^ 2 : ℝ) : ℂ) * z ^ 3 * Gout (Complex.I * (y : ℂ)) * Kedge y := by
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_mem.1.ne'
    have h2y_ne : ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity [hy_mem.1])
    have h1y2c : (1 : ℂ) + (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h1y2_pos.ne'
    calc z * Gout z * (((π / 4 : ℝ) : ℂ) * (1 + z ^ 2))
        = (z * Gout z * (((π / 4 : ℝ) : ℂ) * (1 + z ^ 2))) * (wPt y * z) := by rw [hwz, mul_one]
      _ = (Gout z * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ)) * z ^ 3 *
            (((π / 4 : ℝ) : ℂ) * ((2 * (1 - y ^ 2) / (1 + y ^ 2) : ℝ) : ℂ)) /
            ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) := by
          rw [h1z2_eq]; field_simp [h2y_ne]
      _ = (Gout (Complex.I * (y : ℂ)) * Kedge y) * z ^ 3 *
            (((π / 4 : ℝ) : ℂ) * ((2 * (1 - y ^ 2) / (1 + y ^ 2) : ℝ) : ℂ)) /
            ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) := by rw [hGout_id]
      _ = ((π / 4 * (1 - y ^ 2) / y ^ 2 : ℝ) : ℂ) * z ^ 3 * Gout (Complex.I * (y : ℂ)) * Kedge y := by
          push_cast; field_simp [hy0, h1y2c]
  have hx_eq : xOf y = xT τ := xOf_tanh τ
  have hv_eq : vOf y = vT τ := vOf_tanh hτ.le
  have hF'_eq : edgeF' (vT τ) = 2 * y / (1 + y ^ 2) := edgeF'_vT_eq hτ
  have hKedge_eq : z ^ 3 * Kedge y =
      (((y ^ 3 / √(xT τ * edgeF' (vT τ)) : ℝ)) : ℂ) * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) := by
    unfold Kedge
    rw [hx_eq, hv_eq, ← hF'_eq]
    have hden_pos : 0 < xT τ * edgeF' (vT τ) := mul_pos (xT_pos τ) (edgeF'_pos (vT_pos hτ))
    have hcp := cpow_div_ofReal_half (a := (vT τ : ℂ) + Complex.I / 2) (r := xT τ * edgeF' (vT τ))
      (by simp) hden_pos
    rw [hcp]
    calc z ^ 3 * (((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) /
            ((√(xT τ * edgeF' (vT τ)) : ℝ) : ℂ) * (y : ℂ) ^ 3 * (wPt y) ^ 3)
        = (z * wPt y) ^ 3 * (((y : ℂ) ^ 3 / ((√(xT τ * edgeF' (vT τ)) : ℝ) : ℂ)) *
            ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) := by ring
      _ = (((y ^ 3 / √(xT τ * edgeF' (vT τ)) : ℝ)) : ℂ) * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ) := by
          rw [hzw, one_pow, one_mul]; push_cast; rfl
  have hjacob := wslit_xD_identity hτ
  change y * Wslit y * (1 - y ^ 2) * (π / 4) =
    (π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)) *
      √(xT τ) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * xD τ at hjacob
  have hsq_xf : √(xT τ * edgeF' (vT τ)) = √(xT τ) * √(edgeF' (vT τ)) :=
    Real.sqrt_mul (xT_pos τ).le _
  have hr_id : (π / 4 * (1 - y ^ 2) / y ^ 2) * Wslit y * (y ^ 3 / √(xT τ * edgeF' (vT τ))) =
      (π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2) *
        (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ) := by
    have hy0 : y ≠ 0 := hy_mem.1.ne'
    have hsqF0 : √(edgeF' (vT τ)) ≠ 0 := (Real.sqrt_pos.mpr (edgeF'_pos (vT_pos hτ))).ne'
    have hsqx0 : √(xT τ) ≠ 0 := (Real.sqrt_pos.mpr (xT_pos τ)).ne'
    calc (π / 4 * (1 - y ^ 2) / y ^ 2) * Wslit y * (y ^ 3 / √(xT τ * edgeF' (vT τ)))
        = (y * Wslit y * (1 - y ^ 2) * (π / 4)) / (√(xT τ) * √(edgeF' (vT τ))) := by
          rw [hsq_xf]; field_simp
      _ = ((π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)) *
            √(xT τ) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * (edgeF' (vT τ) * vD τ)) /
            (√(xT τ) * √(edgeF' (vT τ))) := by rw [hjacob, xD_eq_edgeF'_mul_vD]
      _ = π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2) *
            (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ := by
          field_simp; rw [Real.sq_sqrt (edgeF'_pos (vT_pos hτ)).le]; ring
  unfold lowerDualPsi lowerDualRightCore
  dsimp only
  rw [hz_eq, hm0, one_pow, mul_one, dualBStrip_one_add_imag_neg hτ,
    dualPhi0Strip_one_add_imag_neg hτ, hm_eq]
  calc z * hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) *
        Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) *
        Gout z * lowerMt ε (Complex.I * (y : ℂ)) ^ 2 *
        (((π / 4 : ℝ) : ℂ) * (1 + z ^ 2))
      = (z * Gout z * (((π / 4 : ℝ) : ℂ) * (1 + z ^ 2))) *
          lowerMt ε (Complex.I * (y : ℂ)) ^ 2 *
          hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) *
          Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) := by ring
    _ = (((π / 4 * (1 - y ^ 2) / y ^ 2 : ℝ) : ℂ) *
            Gout (Complex.I * (y : ℂ)) * (z ^ 3 * Kedge y)) *
          lowerMt ε (Complex.I * (y : ℂ)) ^ 2 *
          hankelContinuation c' g ((vT τ : ℂ) + Complex.I / 2) *
          Complex.exp (-((c' : ℂ) * edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2))) := by
          rw [hzG]; ring
    _ = _ := by
          rw [hKedge_eq, gout_polar hy_mem]
          have hcast : ((π / 4 * (1 - y ^ 2) / y ^ 2 : ℝ) : ℂ) *
              ((Wslit y : ℂ) * Complex.exp (Complex.I * (thetaOut y : ℂ))) *
              ((((y ^ 3 / √(xT τ * edgeF' (vT τ)) : ℝ)) : ℂ) * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) =
              (((π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2) *
                (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ : ℝ) : ℂ) *
                Complex.exp (Complex.I * (thetaOut y : ℂ)) * ((vT τ : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)) := by
            rw [← hr_id]; push_cast; ring
          rw [hcast]
          ring

/-! ### 4. Right-edge integral reduction via `edge_hankel_two_virasoro` and Fubini -/

lemma norm_cpow_half_v_add_half_I_le {v : ℝ} (hv : 0 ≤ v) :
    ‖((v : ℂ) + Complex.I / 2) ^ (1 / 2 : ℂ)‖ ≤ √(1 + v) := by
  set a : ℂ := (v : ℂ) + Complex.I / 2
  have ha0 : a ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp [a] at this
  have hnorm_a : ‖a‖ ≤ 1 + v := by
    rw [show a = (v : ℝ) + ((1 / 2 : ℝ) : ℂ) * Complex.I by dsimp [a]; push_cast; ring,
      Complex.norm_add_mul_I]
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hn : ‖a ^ (1 / 2 : ℂ)‖ = √‖a‖ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_of_ne_zero ha0 ((1 / 2 : ℝ) : ℂ)]
    simp [Real.sqrt_eq_rpow]
  rw [hn]
  exact Real.sqrt_le_sqrt hnorm_a

private def rightBaseK (c' ε x' τ : ℝ) : ℂ :=
  lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2 *
    Complex.exp (Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ)) *
    (((1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ))

lemma continuous_virasoroKedgeEps {c' ε : ℝ} (_hc' : 0 < c') (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) :
    ContinuousOn (virasoroKedgeEps c' ε) (Ici (xiStar / 2)) ∧
      ContinuousOn (virasoroKedge1Eps c' ε) (Ici (xiStar / 2)) := by
  have hpi := Real.pi_pos
  have hx1 : ∀ x' ∈ Ici (xiStar / 2), 1 / 4 ≤ (1 - Real.exp (-(4 * π * x'))) ^ 2 := fun x' hx' => by
    have hx'1 : (1 : ℝ) / 10 ≤ x' := by linarith [Bessel.one_fifth_le_xiStar, mem_Ici.mp hx']
    have h4x : 1 ≤ 4 * π * x' := by nlinarith [Real.pi_gt_three]
    have hexp_le : Real.exp (-(4 * π * x')) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      calc (Real.exp (4 * π * x'))⁻¹ ≤ (1 + 4 * π * x')⁻¹ :=
            inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (4 * π * x')])
        _ ≤ 2⁻¹ := inv_anti₀ zero_lt_two (by linarith)
        _ = 1 / 2 := by norm_num
    nlinarith
  obtain ⟨hW_int, _⟩ := lowerWeps_tanh_Ioi_bound hε
  let baseK : ℝ → ℝ → ℂ := rightBaseK c' ε
  have hbase_bd : ∀ x' : ℝ, ∀ τ ∈ Ioi (0 : ℝ), ‖baseK x' τ‖ ≤ lowerWeps ε (Real.tanh (π * τ / 4)) := fun x' τ hτ => by
    have hτ_nn : 0 ≤ τ := (mem_Ioi.mp hτ).le
    have hmt_n : ‖lowerMt ε (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) ^ 2‖ =
        lowerWeps ε (Real.tanh (π * τ / 4)) := by rw [norm_pow]; rfl
    have hF'_le1 : edgeF' (vT τ) ≤ 1 := by
      unfold edgeF'
      exact div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (by linarith [Real.cosh_sq (π * vT τ)])) (Real.sqrt_nonneg _)
    have hsub1 : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 ≤ 1 := by
      have : 0 ≤ Real.exp (-(4 * π * xT τ)) := (Real.exp_pos _).le
      have : Real.exp (-(4 * π * xT τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [(xT_pos τ).le])
      nlinarith
    dsimp [baseK, rightBaseK]
    rw [norm_mul, norm_mul, norm_mul, hmt_n,
      show Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ) =
        (thetaOut (Real.tanh (π * τ / 4)) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one,
      show Complex.I * ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ) =
        ((c' * (4 * π / 3 * (xT τ - x') * vT τ - 2 * π * cumulN (xT τ)) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity [(vD_pos τ).le])]
    have hW_nn : 0 ≤ lowerWeps ε (Real.tanh (π * τ / 4)) := sq_nonneg _
    have hfac : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * √(edgeF' (vT τ)) * vD τ ≤ 1 := by
      calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul hsub1 (Real.sqrt_le_one.mpr hF'_le1) (Real.sqrt_nonneg _) zero_le_one)
            (vD_le_one τ) (vD_pos τ).le (by norm_num)
        _ = 1 := by ring
    nlinarith
  have hbase_cont : Continuous fun (p : ℝ × ℝ) => baseK p.1 p.2 := by
    dsimp [baseK, rightBaseK]
    have hxT_c : Continuous xT := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_xT t).continuousAt
    have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt
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
    have hth_c : Continuous fun τ : ℝ => Complex.exp (Complex.I * (thetaOut (Real.tanh (π * τ / 4)) : ℂ)) := by
      refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
      exact thetaOut_soft.2.2.comp_continuous htanh_c fun τ =>
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
    have hN_c : ContinuousOn cumulN (Ici xiStar) := continuousOn_cumulN
    have hxN_c : Continuous fun τ : ℝ => cumulN (xT τ) := by
      refine hN_c.comp_continuous hxT_c fun τ => ?_
      rw [← xT_zero]
      by_cases hτ : 0 ≤ τ
      · rcases hτ.eq_or_lt with rfl | hp
        · exact le_rfl
        · exact (xT_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ) hp).le
      · have h_even : xT τ = xT (-τ) := by unfold xT; rw [mul_neg, Real.cosh_neg]
        rw [h_even]
        exact (xT_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)).le
    have h1_c : Continuous fun p : ℝ × ℝ => lowerMt ε (Complex.I * (Real.tanh (π * p.2 / 4) : ℂ)) ^ 2 :=
      hmt_c.comp continuous_snd
    have h2_c : Continuous fun p : ℝ × ℝ => Complex.exp (Complex.I * (thetaOut (Real.tanh (π * p.2 / 4)) : ℂ)) :=
      hth_c.comp continuous_snd
    have h3_c : Continuous fun p : ℝ × ℝ =>
        (((1 - Real.exp (-(4 * π * xT p.2))) ^ 2 * √(edgeF' (vT p.2)) * vD p.2 : ℝ) : ℂ) := by
      have hxT2 : Continuous fun p : ℝ × ℝ => xT p.2 := hxT_c.comp continuous_snd
      have hF'2 : Continuous fun p : ℝ × ℝ => edgeF' (vT p.2) := hF'_c.comp (continuous_vT.comp continuous_snd)
      have hvD2 : Continuous fun p : ℝ × ℝ => vD p.2 := continuous_vD.comp continuous_snd
      have hex2 : Continuous fun p : ℝ × ℝ => (1 - Real.exp (-(4 * π * xT p.2))) ^ 2 := by fun_prop
      have hsq2 : Continuous fun p : ℝ × ℝ => √(edgeF' (vT p.2)) := Real.continuous_sqrt.comp hF'2
      exact Complex.continuous_ofReal.comp ((hex2.mul hsq2).mul hvD2)
    have h4_c : Continuous fun p : ℝ × ℝ =>
        Complex.exp (Complex.I * ((c' * (4 * π / 3 * (xT p.2 - p.1) * vT p.2 - 2 * π * cumulN (xT p.2)) : ℝ) : ℂ)) := by
      have hxT2 : Continuous fun p : ℝ × ℝ => xT p.2 := hxT_c.comp continuous_snd
      have hvT2 : Continuous fun p : ℝ × ℝ => vT p.2 := continuous_vT.comp continuous_snd
      have hxN2 : Continuous fun p : ℝ × ℝ => cumulN (xT p.2) := hxN_c.comp continuous_snd
      have harg : Continuous fun p : ℝ × ℝ =>
          c' * (4 * π / 3 * (xT p.2 - p.1) * vT p.2 - 2 * π * cumulN (xT p.2)) := by fun_prop
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp harg))
    exact ((h1_c.mul h2_c).mul h3_c).mul h4_c
  have hbase_x : ∀ τ : ℝ, Continuous fun x' : ℝ => baseK x' τ := fun τ => by
    simpa only [Function.comp_def, id_eq] using
      hbase_cont.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => τ))
  have hI0_cont : Continuous fun x' : ℝ => ∫ τ in Ioi (0 : ℝ), baseK x' τ := by
    refine MeasureTheory.continuous_of_dominated (μ := volume.restrict (Ioi 0))
      (F := baseK) (bound := fun τ => lowerWeps ε (Real.tanh (π * τ / 4))) ?_ ?_ hW_int ?_
    · exact fun x' => (hbase_cont.comp (continuous_const.prodMk continuous_id : Continuous fun τ : ℝ => (x', τ))).continuousOn.aestronglyMeasurable
        measurableSet_Ioi
    · exact fun x' => ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => hbase_bd x' τ hτ
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun τ _ => hbase_x τ
  have hinv_le1 : ∀ τ : ℝ, ‖((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹‖ ≤ 1 := fun τ => by
    rw [norm_inv]
    have hge1 : 1 ≤ ‖(1 : ℂ) - 2 * Complex.I * (vT τ : ℂ)‖ := by
      rw [show (1 : ℂ) - 2 * Complex.I * (vT τ : ℂ) = (1 : ℝ) + ((-2 * vT τ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_add_mul_I]
      exact Real.one_le_sqrt.mpr (by nlinarith)
    exact inv_le_one_of_one_le₀ hge1
  have hI1_cont : Continuous fun x' : ℝ =>
      ∫ τ in Ioi (0 : ℝ), baseK x' τ * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ := by
    refine MeasureTheory.continuous_of_dominated (μ := volume.restrict (Ioi 0))
      (F := fun x' τ => baseK x' τ * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹)
      (bound := fun τ => lowerWeps ε (Real.tanh (π * τ / 4))) ?_ ?_ hW_int ?_
    · intro x'
      have hc1 : Continuous fun τ : ℝ => ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹ :=
        (continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp continuous_vT))).inv₀
          fun τ => by intro h; have := congrArg Complex.re h; simp at this
      exact ((hbase_cont.comp (continuous_const.prodMk continuous_id : Continuous fun τ : ℝ => (x', τ))).mul hc1).continuousOn.aestronglyMeasurable
        measurableSet_Ioi
    · intro x'
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      rw [norm_mul]
      calc ‖baseK x' τ‖ * ‖((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹‖
          ≤ lowerWeps ε (Real.tanh (π * τ / 4)) * 1 := mul_le_mul (hbase_bd x' τ hτ) (hinv_le1 τ) (norm_nonneg _) (sq_nonneg _)
        _ = lowerWeps ε (Real.tanh (π * τ / 4)) := mul_one _
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun τ _ => (hbase_x τ).mul continuous_const
  have hden_cont : ContinuousOn (fun x' : ℝ => (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹) (Ici (xiStar / 2)) := by
    have h0 : Continuous fun x' : ℝ => (1 - Real.exp (-(4 * π * x'))) ^ 2 := by fun_prop
    have h1 : Continuous fun x' : ℝ => (((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp h0
    exact h1.continuousOn.inv₀ fun x' hx' => by
      exact_mod_cast (by linarith [hx1 x' hx'] : (1 - Real.exp (-(4 * π * x'))) ^ 2 ≠ 0)
  have heq0 : ∀ x' ∈ Ici (xiStar / 2),
      virasoroKedgeEps c' ε x' = -(√(2 * c' / 3)) *
        (Complex.exp (Complex.I * (π : ℂ) / 4) *
          ((((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹ *
            ∫ τ in Ioi (0 : ℝ), baseK x' τ)).re := fun x' hx' => by
    obtain ⟨_, _, hcov0, _⟩ := kedgeEps_integrable_and_tau_eq c' hε (mem_Ici.mp hx')
    unfold virasoroKedgeEps
    rw [hcov0, ← MeasureTheory.integral_const_mul ((((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹)]
    congr 3
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    rw [kedgeEpsIntegrand_vT (mem_Ioi.mp hτ).le]
    dsimp [baseK, rightBaseK]; push_cast; ring
  have heq1 : ∀ x' ∈ Ici (xiStar / 2),
      virasoroKedge1Eps c' ε x' = -(√(2 * c' / 3)) *
        (Complex.exp (Complex.I * (π : ℂ) / 4) *
          ((((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹ *
            ∫ τ in Ioi (0 : ℝ), baseK x' τ * ((1 : ℂ) - 2 * Complex.I * (vT τ : ℂ))⁻¹)).re := fun x' hx' => by
    obtain ⟨_, _, _, hcov1⟩ := kedgeEps_integrable_and_tau_eq c' hε (mem_Ici.mp hx')
    unfold virasoroKedge1Eps
    rw [hcov1, ← MeasureTheory.integral_const_mul ((((1 - Real.exp (-(4 * π * x'))) ^ 2 : ℝ) : ℂ)⁻¹)]
    congr 3
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    rw [kedgeEpsIntegrand_vT (mem_Ioi.mp hτ).le]
    dsimp [baseK, rightBaseK]; push_cast; ring
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.congr (ContinuousOn.mul continuousOn_const
      (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul (hden_cont.mul hI0_cont.continuousOn)))) heq0
  · refine ContinuousOn.congr (ContinuousOn.mul continuousOn_const
      (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul (hden_cont.mul hI1_cont.continuousOn)))) heq1

lemma change_of_vars_Ioi_half {c' : ℝ} (hc' : 0 < c') (ha : 2 ≤ c' / 12)
    (g : ℝ → ℝ) (hg : TestClass virasoroProblem (c' / 12) g)
    (F : ℝ → ℝ) (hF_cont : ContinuousOn F (Ici (xiStar / 2)))
    (hF_bd : ∃ B : ℝ, ∀ x' : ℝ, xiStar / 2 < x' → |F x'| ≤ B)
    (h_int_x : IntegrableOn (fun x' : ℝ =>
      g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) *
        F x' * (2 * c' * x' / 3)) (Ioi (xiStar / 2))) :
    IntegrableOn (fun t' : ℝ =>
      g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c'))) (Ioi (c' * (xiStar / 2) ^ 2 / 3)) ∧
    (∫ x' in Ioi (xiStar / 2),
        g (c' * x' ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x' ^ 2 / 3) *
          F x' * (2 * c' * x' / 3) =
      ∫ t' in Ioi (c' * (xiStar / 2) ^ 2 / 3),
        g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c'))) := by
  obtain ⟨B, hB⟩ := hF_bd
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by rw [virasoroProblem_totalShift]; linarith
  have hV_int : IntegrableOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (Ioi 0) :=
    hg.int_cardy.congr_fun (fun t ht => by
      dsimp only; rw [Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]) measurableSet_Ioi
  have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
    (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
      (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
  let φ : ℝ → ℝ := fun x' => c' * x' ^ 2 / 3
  let φ' : ℝ → ℝ := fun x' => 2 * c' * x' / 3
  set t₀ : ℝ := φ (xiStar / 2) with ht₀_def
  have ht₀_val : t₀ = c' * (xiStar / 2) ^ 2 / 3 := rfl
  have ht₀_pos : 0 < t₀ := by dsimp [t₀, φ]; positivity [xiStar_pos]
  have h_int_t : IntegrableOn (fun t' => g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c'))) (Ioi t₀) := by
    refine ((hV_int.mono_set (Ioi_subset_Ioi ht₀_pos.le)).const_mul (max B 0)).mono' ?_ ?_
    · have hc : ContinuousOn (fun t' => g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c'))) (Ioi t₀) := by
        refine ((hg.cont.mono (Ioi_subset_Ici ht₀_pos.le)).mul (hV_cont.mono (Ioi_subset_Ici ht₀_pos.le))).mul ?_
        refine hF_cont.comp (Real.continuous_sqrt.continuousOn.comp
          ((continuousOn_const.mul continuousOn_id).div_const c') fun _ _ => mem_univ _) fun t' ht' => ?_
        have ht'_gt : c' * (xiStar / 2) ^ 2 / 3 < t' := mem_Ioi.mp ht'
        simpa [Real.sqrt_sq (by positivity [xiStar_pos] : 0 ≤ xiStar / 2)] using
          Real.sqrt_le_sqrt (show (xiStar / 2) ^ 2 ≤ 3 * t' / c' by rw [le_div_iff₀ hc']; linarith)
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t' ht'
      have ht'_gt : t₀ < t' := mem_Ioi.mp ht'
      have hx_lt : xiStar / 2 < √(3 * t' / c') := by
        rw [ht₀_val] at ht'_gt
        simpa [Real.sqrt_sq (by positivity [xiStar_pos] : 0 ≤ xiStar / 2)] using
          Real.sqrt_lt_sqrt (sq_nonneg _) (show (xiStar / 2) ^ 2 < 3 * t' / c' by rw [lt_div_iff₀ hc']; linarith)
      have hV_nn : 0 ≤ Bessel.besselV (c' / 12) t' := by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (ht₀_pos.le.trans ht'_gt.le)]
        exact virasoroProblem.cardyV_nonneg hshift (ht₀_pos.le.trans ht'_gt.le)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hV_nn]
      calc |g t'| * Bessel.besselV (c' / 12) t' * |F (√(3 * t' / c'))|
          ≤ |g t'| * Bessel.besselV (c' / 12) t' * max B 0 := by gcongr; exact (hB _ hx_lt).trans (le_max_left _ _)
        _ = max B 0 * (|g t'| * Bessel.besselV (c' / 12) t') := by ring
  refine ⟨h_int_t, ?_⟩
  have hL : Tendsto (fun R : ℝ => ∫ x' in (xiStar / 2)..R,
      g (φ x') * Bessel.besselV (c' / 12) (φ x') * F x' * φ' x') atTop
      (𝓝 (∫ x' in Ioi (xiStar / 2), g (φ x') * Bessel.besselV (c' / 12) (φ x') * F x' * φ' x')) :=
    intervalIntegral_tendsto_integral_Ioi (xiStar / 2) h_int_x tendsto_id
  have hφ_tend : Tendsto φ atTop atTop := by
    dsimp [φ]
    exact ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop hc').atTop_div_const (by norm_num)
  have hR : Tendsto (fun R : ℝ => ∫ t' in t₀..(φ R),
      g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c'))) atTop
      (𝓝 (∫ t' in Ioi t₀, g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c')))) :=
    (intervalIntegral_tendsto_integral_Ioi t₀ h_int_t tendsto_id).comp hφ_tend
  have heq : ∀ᶠ R : ℝ in atTop,
      (∫ x' in (xiStar / 2)..R, g (φ x') * Bessel.besselV (c' / 12) (φ x') * F x' * φ' x') =
        (∫ t' in t₀..(φ R), g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c'))) := by
    filter_upwards [eventually_gt_atTop (xiStar / 2)] with R hR_gt
    have hd : ∀ x' ∈ uIcc (xiStar / 2) R, HasDerivAt φ (φ' x') x' := fun x' _ => by
      dsimp [φ, φ']; exact ((((hasDerivAt_id' x').pow 2).const_mul c').div_const 3).congr_deriv (by dsimp; ring)
    have hφ'_cont : ContinuousOn φ' (uIcc (xiStar / 2) R) := (continuous_const.mul continuous_id |>.div_const 3).continuousOn
    have hcont_t : ContinuousOn (fun t' => g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c')))
        (φ '' uIcc (xiStar / 2) R) := by
      have himg : φ '' uIcc (xiStar / 2) R ⊆ Ici t₀ := by
        rintro t' ⟨x', hx', rfl⟩
        rw [uIcc_of_le hR_gt.le] at hx'
        have hx0 : 0 ≤ xiStar / 2 := by positivity [xiStar_pos]
        change t₀ ≤ c' * x' ^ 2 / 3
        dsimp [t₀, φ]; gcongr; exact hx'.1
      have h_all : ContinuousOn (fun t' => g t' * Bessel.besselV (c' / 12) t' * F (√(3 * t' / c'))) (Ici t₀) := by
        refine ((hg.cont.mono (Ici_subset_Ici.mpr ht₀_pos.le)).mul (hV_cont.mono (Ici_subset_Ici.mpr ht₀_pos.le))).mul ?_
        refine hF_cont.comp (Real.continuous_sqrt.continuousOn.comp
          ((continuousOn_const.mul continuousOn_id).div_const c') fun _ _ => mem_univ _) fun t' ht' => ?_
        have ht'_ge : c' * (xiStar / 2) ^ 2 / 3 ≤ t' := mem_Ici.mp ht'
        simpa [Real.sqrt_sq (by positivity [xiStar_pos] : 0 ≤ xiStar / 2)] using
          Real.sqrt_le_sqrt (show (xiStar / 2) ^ 2 ≤ 3 * t' / c' by rw [le_div_iff₀ hc']; linarith)
      exact h_all.mono himg
    have hcov := intervalIntegral.integral_comp_mul_deriv' hd hφ'_cont hcont_t
    dsimp only [Function.comp] at hcov
    rw [← ht₀_def] at hcov
    rw [← hcov]
    refine intervalIntegral.integral_congr fun x' hx' => ?_
    rw [uIcc_of_le hR_gt.le] at hx'
    have hx'_pos : 0 ≤ x' := by linarith [xiStar_pos, hx'.1]
    dsimp [φ, φ']
    rw [show 3 * (c' * x' ^ 2 / 3) / c' = x' ^ 2 by field_simp, Real.sqrt_sq hx'_pos]
  exact tendsto_nhds_unique (hL.congr' heq) hR

end

end FormalResearch.ModularBootstrap.FiveTerm
