module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeOuterAmp
public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeTailIBP
public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualIdRight
public import FormalResearch.SignUncertainty.CtOscIBP

/-!
# Outer Band Edge-Kernel Region & Phase Estimates (`LowerKedgeOuterRegions`)

Proves the uniform asymptotic for `virasoroKedgeEps` and uniform bound for `virasoroKedge1Eps`
for `x' ≥ xiStar + δ_hi` (`δ_hi > 0`) and `ε ∈ Ioo 0 (1 / 2)` (`virasoro_kedge_outer_of_delta`).

Uses:
* `kedgeAmp0_small_v_bounds` (`LowerKedgeOuterAmp`) for `(0, v_s]` and double-IBP on `[v_s, v₀]`.
* `kedgeAmp0_D2_of_ge` (`LowerKedgeOuterAmp`) + `CtOsc.ibp_twice` on `[v₀, v_L]` with
  `|φ'| ≥ c₀ (vstar - v)` giving an `x'`-uniform `O(c'⁻²)` IBP remainder.
* `CtOsc.stat_phase` (`CtOscStat`) near the saddle `vstar = vTip x'`.
* `virasoro_geps_deriv` + `phiDual_tail_ibp2` (`LowerKedgeTailIBP`) on `[v_R, ∞)`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.SignUncertainty.CtOsc

noncomputable section

/-! ### 1. Cutoff `D2` data and `vTip` / `phiDual` estimates -/

lemma cutoff_D2_global {θ : ℝ} (hθ : 0 < θ) :
    ∃ χ χ1 χ2 : ℝ → ℝ, ∃ Kχ : ℝ, 0 < Kχ ∧
      (∀ t, HasDerivAt χ (χ1 t) t) ∧
      (∀ t, HasDerivAt χ1 (χ2 t) t) ∧
      D2 (univ : Set ℝ) (fun t => (χ t : ℂ)) (fun t => (χ1 t : ℂ)) (fun t => (χ2 t : ℂ)) Kχ ∧
      (∀ t, |t| ≤ θ / 2 → χ t = 1) ∧
      (∀ t, θ ≤ |t| → χ t = 0 ∧ χ1 t = 0 ∧ χ2 t = 0) := by
  obtain ⟨χ, hcd, hsupp, h1, h0⟩ := exists_cutoff hθ
  let χ1 : ℝ → ℝ := deriv χ
  let χ2 : ℝ → ℝ := deriv χ1
  have hd1 : ∀ t, HasDerivAt χ (χ1 t) t := fun t => (hcd.differentiable (by simp) t).hasDerivAt
  have hcd1 : ContDiff ℝ 2 χ1 :=
    ((contDiff_succ_iff_deriv (n := (2 : ℕ∞))).mp (hcd.of_le (WithTop.coe_le_coe.mpr le_top))).2.2
  have hd2 : ∀ t, HasDerivAt χ1 (χ2 t) t := fun t => (hcd1.differentiable (by simp) t).hasDerivAt
  have hc0 : Continuous χ := hcd.continuous
  have hc1 : Continuous χ1 := hcd.continuous_deriv (by simp)
  have hc2 : Continuous χ2 := hcd1.continuous_deriv (by simp)
  have hout : ∀ t, θ ≤ |t| → χ t = 0 ∧ χ1 t = 0 ∧ χ2 t = 0 := fun t ht => by
    have hnot : t ∉ Ioo (-θ) θ := fun h => by
      have : |t| < θ := abs_lt.mpr h
      linarith
    have hnot_sup : t ∈ (tsupport χ)ᶜ := fun h => hnot (hsupp h)
    have hmem : (tsupport χ)ᶜ ∈ 𝓝 t :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds hnot_sup
    have hχ_ev : χ =ᶠ[𝓝 t] 0 :=
      Filter.eventually_of_mem hmem fun u hu => image_eq_zero_of_notMem_tsupport hu
    have hχ1_ev : χ1 =ᶠ[𝓝 t] 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.eventually_mem hnot_sup] with u hu
      have hmem_u : (tsupport χ)ᶜ ∈ 𝓝 u := (isClosed_tsupport χ).isOpen_compl.mem_nhds hu
      have hu_ev : χ =ᶠ[𝓝 u] 0 := Filter.eventually_of_mem hmem_u fun w hw => image_eq_zero_of_notMem_tsupport hw
      exact (hd1 u).congr_of_eventuallyEq hu_ev.symm |>.unique (hasDerivAt_const u 0)
    have hχ2_t : χ2 t = 0 := (hd2 t).congr_of_eventuallyEq hχ1_ev.symm |>.unique (hasDerivAt_const t 0)
    exact ⟨h0 t ht, hχ1_ev.self_of_nhds, hχ2_t⟩
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := -θ) (b := θ)).exists_bound_of_continuousOn hc0.continuousOn
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := -θ) (b := θ)).exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := -θ) (b := θ)).exists_bound_of_continuousOn hc2.continuousOn
  let Kχ : ℝ := max 1 (max M0 (max M1 M2))
  have hKχ : 0 < Kχ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbd : ∀ (f : ℝ → ℝ) (M : ℝ), (∀ t ∈ Icc (-θ) θ, ‖f t‖ ≤ M) →
      (∀ t, θ ≤ |t| → f t = 0) → M ≤ Kχ → ∀ t : ℝ, ‖(f t : ℂ)‖ ≤ Kχ := fun f M hM hf0 hMK t => by
    rw [Complex.norm_real]
    by_cases ht : |t| ≤ θ
    · exact (hM t (abs_le.mp ht)).trans hMK
    · rw [hf0 t (le_of_not_ge ht), norm_zero]; exact hKχ.le
  refine ⟨χ, χ1, χ2, Kχ, hKχ, hd1, hd2, {
    d1 := fun t _ => (hd1 t).ofReal_comp
    d2 := fun t _ => (hd2 t).ofReal_comp
    c2 := (Complex.continuous_ofReal.comp hc2).continuousOn
    K0 := hKχ.le
    b0 := fun t _ => hbd χ M0 hM0 (fun u hu => (hout u hu).1) ((le_max_left _ _).trans (le_max_right 1 _)) t
    b1 := fun t _ => hbd χ1 M1 hM1 (fun u hu => (hout u hu).2.1)
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right 1 _))) t
    b2 := fun t _ => hbd χ2 M2 hM2 (fun u hu => (hout u hu).2.2)
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right 1 _))) t
  }, h1, hout⟩

lemma vTip_ge_of_ge {x₁ x₂ : ℝ} (hx₁ : xiStar < x₁) (hx : x₁ ≤ x₂) :
    vTip x₁ ≤ vTip x₂ := by
  by_contra hlt
  have hlt' : vTip x₂ < vTip x₁ := lt_of_not_ge hlt
  have hv1 := (vTip_pos hx₁).le
  have hv2 := (vTip_pos (hx₁.trans_le hx)).le
  have hF : edgeF (vTip x₂) < edgeF (vTip x₁) := edgeF_strictMonoOn hv2 hv1 hlt'
  rw [edgeF_vTip hx₁.le, edgeF_vTip (hx₁.trans_le hx).le] at hF
  linarith

lemma phiDual_deriv (x' v : ℝ) :
    HasDerivAt (fun u => phiDual u x') ((4 * π / 3) * (edgeF v - x')) v := by
  have hFc : Continuous edgeF := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF t).continuousAt
  have hi : IntervalIntegrable (fun u => edgeF u - x') volume 0 v :=
    (hFc.sub continuous_const).intervalIntegrable 0 v
  unfold phiDual
  exact (intervalIntegral.integral_hasDerivAt_right hi
    ((hFc.sub continuous_const).stronglyMeasurableAtFilter _ _)
    (hFc.sub continuous_const).continuousAt).const_mul (4 * π / 3)

lemma edgeF'''_continuous : Continuous edgeF''' := by
  unfold edgeF'''
  have hpos : ∀ v : ℝ, (1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ) ≠ 0 :=
    fun v => (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)) _).ne'
  exact ((continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
    (continuous_const.sub (continuous_const.mul ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).pow 2)))).div
    ((continuous_const.add ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).pow 2)).rpow_const
      fun _ => Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)).ne') hpos

lemma phiDual_sub_edgeF_ge {v₀ vstar v : ℝ} (hv₀ : 0 < v₀) (hv_lo : v₀ ≤ v) (hv_hi : v ≤ vstar) :
    edgeF' v₀ * (vstar - v) ≤ edgeF vstar - edgeF v := by
  rcases hv_hi.eq_or_lt with rfl | hlt
  · simp
  · have hFc : Continuous edgeF := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF t).continuousAt
    obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope edgeF edgeF' hlt hFc.continuousOn fun t _ => hasDerivAt_edgeF t
    have hc_ge : v₀ ≤ c := hv_lo.trans hc.1.le
    have hf_ge : edgeF' v₀ ≤ edgeF' c := (edgeF_deriv_bounds_of_ge hv₀ hc_ge).1
    rw [eq_div_iff (sub_pos.mpr hlt).ne'] at hce
    rw [← hce]
    exact mul_le_mul_of_nonneg_right hf_ge (sub_nonneg.mpr hlt.le)

lemma phiDual_edgeF_sub_ge {v₀ vstar v : ℝ} (hv₀ : 0 < v₀) (hvstar : v₀ ≤ vstar) (hv : vstar ≤ v) :
    edgeF' v₀ * (v - vstar) ≤ edgeF v - edgeF vstar := by
  rcases hv.eq_or_lt with rfl | hlt
  · simp
  · have hFc : Continuous edgeF := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF t).continuousAt
    obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope edgeF edgeF' hlt hFc.continuousOn fun t _ => hasDerivAt_edgeF t
    have hc_ge : v₀ ≤ c := hvstar.trans hc.1.le
    have hf_ge : edgeF' v₀ ≤ edgeF' c := (edgeF_deriv_bounds_of_ge hv₀ hc_ge).1
    rw [eq_div_iff (sub_pos.mpr hlt).ne'] at hce
    rw [← hce]
    exact mul_le_mul_of_nonneg_right hf_ge (sub_nonneg.mpr hlt.le)

lemma phiDual_phase {v₀ δ_loc vstar x' : ℝ} (hv₀ : 0 < v₀) (hδ : 0 < δ_loc) (hδ1 : δ_loc ≤ 1)
    (hv_ge : v₀ ≤ vstar - δ_loc) (hx' : edgeF vstar = x') :
    let φ : ℝ → ℝ := fun t => (phiDual (vstar + δ_loc * t) x' - phiDual vstar x') / δ_loc ^ 2
    let φ1 : ℝ → ℝ := fun t => (4 * π / 3) * (edgeF (vstar + δ_loc * t) - x') / δ_loc
    let f : ℝ → ℝ := fun t => (4 * π / 3) * edgeF' (vstar + δ_loc * t)
    let f1 : ℝ → ℝ := fun t => δ_loc * (4 * π / 3) * edgeF'' (vstar + δ_loc * t)
    let f2 : ℝ → ℝ := fun t => δ_loc ^ 2 * (4 * π / 3) * edgeF''' (vstar + δ_loc * t)
    Phase ((4 * π / 3) * edgeF' v₀) ((4 * π / 3) * (1 + 8 * π + 16 * π ^ 2)) φ φ1 f f1 f2 := by
  intro φ φ1 f f1 f2
  have hpi := Real.pi_pos
  have hsc : ∀ t : ℝ, HasDerivAt (fun u => vstar + δ_loc * u) δ_loc t := fun t =>
    (((hasDerivAt_id t).const_mul δ_loc).const_add vstar).congr_deriv (by simp)
  have hmem : ∀ y ∈ Ioo (-1 : ℝ) 1, v₀ ≤ vstar + δ_loc * y := fun y hy => by
    nlinarith [hy.1, hv_ge, hδ]
  refine {
    d0 := fun y _ => by
      have hd := (((phiDual_deriv x' (vstar + δ_loc * y)).comp y (hsc y)).sub_const (phiDual vstar x')).div_const
        (δ_loc ^ 2)
      refine hd.congr_deriv ?_
      dsimp [φ1]; field_simp [hδ.ne']
    d1 := fun y _ => by
      have hd := ((((hasDerivAt_edgeF (vstar + δ_loc * y)).comp y (hsc y)).sub_const x').const_mul
        (4 * π / 3)).div_const δ_loc
      refine hd.congr_deriv ?_
      dsimp [f]; field_simp [hδ.ne']
    d2 := fun y _ => by
      have hd := ((hasDerivAt_edgeF' (vstar + δ_loc * y)).comp y (hsc y)).const_mul (4 * π / 3)
      exact hd.congr_deriv (by dsimp [f1]; ring)
    d3 := fun y _ => by
      have hd := ((hasDerivAt_edgeF'' (vstar + δ_loc * y)).comp y (hsc y)).const_mul (δ_loc * (4 * π / 3))
      exact hd.congr_deriv (by dsimp [f2]; ring)
    c2 := (continuous_const.mul (edgeF'''_continuous.comp (continuous_const.add
      (continuous_const.mul continuous_id)))).continuousOn
    z0 := by dsimp [φ]; simp
    z1 := by dsimp [φ1]; rw [mul_zero, add_zero, hx', sub_self, mul_zero, zero_div]
    lo := fun y hy => mul_le_mul_of_nonneg_left (edgeF_deriv_bounds_of_ge hv₀ (hmem y hy)).1 (by positivity)
    b0 := fun y hy => by
      have hb := edgeF_deriv_bounds_of_ge hv₀ (hmem y hy)
      dsimp [f]
      rw [abs_of_pos (mul_pos (by positivity) (edgeF'_pos (hv₀.trans_le (hmem y hy))))]
      have h1 : edgeF' (vstar + δ_loc * y) ≤ 1 + 8 * π + 16 * π ^ 2 := by nlinarith [sq_nonneg π]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    b1 := fun y hy => by
      have hb := edgeF_deriv_bounds_of_ge hv₀ (hmem y hy)
      dsimp [f1]
      rw [abs_mul, abs_of_pos (mul_pos hδ (by positivity)), abs_of_pos hb.2.2.1]
      have h1 : δ_loc * (4 * π / 3) * edgeF'' (vstar + δ_loc * y) ≤ 1 * (4 * π / 3) * (8 * π) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hδ1 (by positivity)) hb.2.2.2.1 hb.2.2.1.le (by positivity)
      nlinarith [sq_nonneg π]
    b2 := fun y hy => by
      have hb := edgeF_deriv_bounds_of_ge hv₀ (hmem y hy)
      dsimp [f2]
      rw [abs_mul, abs_of_pos (mul_pos (pow_pos hδ 2) (by positivity))]
      have hδ2 : δ_loc ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
      have h1 : δ_loc ^ 2 * (4 * π / 3) * |edgeF''' (vstar + δ_loc * y)| ≤
          1 * (4 * π / 3) * (16 * π ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hδ2 (by positivity)) hb.2.2.2.2 (abs_nonneg _) (by positivity)
      nlinarith }

/-! ### 2. Abstract region bounds -/

lemma kedge_small_region_bound {v_s M0 lam : ℝ} (hvs : 0 < v_s) (_hM0 : 0 ≤ M0)
    {B : ℝ → ℂ} {φ : ℝ → ℝ}
    (hB_bd : ∀ v ∈ Ioc (0 : ℝ) v_s, ‖B v‖ ≤ M0 * v ^ (1 / 2 : ℝ)) :
    ‖∫ v in Ioc (0 : ℝ) v_s, B v * Complex.exp (Complex.I * ((lam * φ v : ℝ) : ℂ))‖ ≤
      (2 / 3 : ℝ) * M0 * v_s ^ (3 / 2 : ℝ) := by
  have hint_m : IntegrableOn (fun v : ℝ => M0 * v ^ (1 / 2 : ℝ)) (Ioc 0 v_s) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hvs.le]
    exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1 / 2)).const_mul M0
  have hle_norm : ∀ v ∈ Ioc (0 : ℝ) v_s,
      ‖B v * Complex.exp (Complex.I * ((lam * φ v : ℝ) : ℂ))‖ ≤ M0 * v ^ (1 / 2 : ℝ) := fun v hv => by
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hB_bd v hv
  have h1 := norm_integral_le_of_norm_le hint_m ((ae_restrict_mem measurableSet_Ioc).mono hle_norm)
  have hval : ∫ v in Ioc (0 : ℝ) v_s, M0 * v ^ (1 / 2 : ℝ) = (2 / 3 : ℝ) * M0 * v_s ^ (3 / 2 : ℝ) := by
    rw [← intervalIntegral.integral_of_le hvs.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    rw [Real.zero_rpow (by norm_num), sub_zero]
    ring
  exact h1.trans_eq hval

lemma kedge_left_ibp_mid_bound {v_s v₀ M0 M1 M2 δ_mid c' x' : ℝ}
    (hvs : 0 < v_s) (hvs_le : v_s ≤ v₀) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hδ_pos : 0 < δ_mid) (hc' : 1 ≤ c') (hvs_eq : v_s = c'⁻¹)
    (hδ_mid : ∀ v ∈ Icc v_s v₀, δ_mid ≤ (4 * π / 3) * (x' - edgeF v))
    {B Bs1 Bs2 : ℝ → ℂ}
    (hd1 : ∀ v ∈ Ioc (0 : ℝ) v₀, HasDerivAt B (Bs1 v) v)
    (hd2 : ∀ v ∈ Ioc (0 : ℝ) v₀, HasDerivAt Bs1 (Bs2 v) v)
    (hc2 : ContinuousOn Bs2 (Ioc (0 : ℝ) v₀))
    (hB0 : ∀ v ∈ Ioc (0 : ℝ) v₀, ‖B v‖ ≤ M0 * v ^ (1 / 2 : ℝ))
    (hB1 : ∀ v ∈ Ioc (0 : ℝ) v₀, ‖Bs1 v‖ ≤ M1 * v ^ (-(1 / 2 : ℝ)))
    (hB2 : ∀ v ∈ Ioc (0 : ℝ) v₀, ‖Bs2 v‖ ≤ M2 * v ^ (-(3 / 2 : ℝ))) :
    let ϕ1 : ℝ → ℝ := fun v => (4 * π / 3) * (edgeF v - x')
    let ϕ2 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF' v
    let e : ℝ → ℂ := fun v => Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v x' : ℝ) : ℂ))
    ‖(∫ v in v_s..v₀, B v * e v) -
      ((1 / (Complex.I * (c' : ℂ))) * (B v₀ / (ϕ1 v₀ : ℂ) * e v₀) -
        (1 / (Complex.I * (c' : ℂ))) ^ 2 * (ibpH B Bs1 ϕ1 ϕ2 v₀ / (ϕ1 v₀ : ℂ) * e v₀))‖ ≤
      (M0 / δ_mid + M1 / δ_mid ^ 2 + M0 * (4 * π / 3) / δ_mid ^ 3 +
        2 * M2 / δ_mid ^ 2 + 6 * M1 * (4 * π / 3) * v₀ ^ (1 / 2 : ℝ) / δ_mid ^ 3 +
        (2 / 3) * M0 * v₀ ^ (3 / 2 : ℝ) * (32 * π ^ 2 / 3 / δ_mid ^ 3 +
          3 * (4 * π / 3) ^ 2 / δ_mid ^ 4)) * c' ^ (-(3 / 2 : ℝ)) := by
  intro ϕ1 ϕ2 e
  have hpi := Real.pi_pos
  have hc'_pos : 0 < c' := by linarith
  let ϕ3 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF'' v
  have hsub_ioc : Icc v_s v₀ ⊆ Ioc (0 : ℝ) v₀ := fun v hv => ⟨hvs.trans_le hv.1, hv.2⟩
  have hne : ∀ v ∈ Icc v_s v₀, ϕ1 v ≠ 0 := fun v hv => by
    have h1 := hδ_mid v hv
    dsimp [ϕ1]; linarith
  have hc3 : ContinuousOn ϕ3 (Icc v_s v₀) :=
    (continuous_const.mul (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF'' t).continuousAt)).continuousOn
  have hibp := ibp_twice hvs_le hc'_pos.ne'
    (ϕ := fun u => phiDual u x') (ϕ1 := ϕ1) (ϕ2 := ϕ2) (ϕ3 := ϕ3)
    (fun v _ => phiDual_deriv x' v)
    (fun v _ => ((hasDerivAt_edgeF v).sub_const x').const_mul (4 * π / 3))
    (fun v _ => (hasDerivAt_edgeF' v).const_mul (4 * π / 3))
    hne (fun v hv => hd1 v (hsub_ioc hv)) (fun v hv => hd2 v (hsub_ioc hv))
    (hc2.mono hsub_ioc) hc3
  have hexp_1 : ∀ v : ℝ, ‖e v‖ = 1 := fun v => by
    dsimp [e]; rw [mul_assoc, Complex.norm_exp]; simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have hlam_norm : ‖(1 : ℂ) / (Complex.I * (c' : ℂ))‖ = c'⁻¹ := by
    rw [one_div, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc'_pos]
  have hc_m12 : c'⁻¹ * c'⁻¹ ^ (1 / 2 : ℝ) = c' ^ (-(3 / 2 : ℝ)) := by
    rw [hvs_eq] at hvs
    rw [← Real.rpow_neg_one c', ← Real.rpow_mul hc'_pos.le, ← Real.rpow_add hc'_pos]
    norm_num
  have hc_m2_12 : c' ^ (-2 : ℝ) * c' ^ (1 / 2 : ℝ) = c' ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hc'_pos]; norm_num
  have hc_m2_le : c' ^ (-2 : ℝ) ≤ c' ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc' (by norm_num)
  have hc_1_le : (1 : ℝ) ≤ c' ^ (1 / 2 : ℝ) := Real.one_le_rpow hc' (by norm_num)
  have hvs_bd := hB0 v_s ⟨hvs, hvs_le⟩
  have hvs_d_bd := hB1 v_s ⟨hvs, hvs_le⟩
  have hϕ_ge : ∀ v ∈ Icc v_s v₀, δ_mid ≤ ‖(ϕ1 v : ℂ)‖ := fun v hv => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := hδ_mid v hv
    dsimp [ϕ1]
    rw [abs_of_neg (by linarith)]
    linarith
  have hv₀_pos : 0 < v₀ := hvs.trans_le hvs_le
  have hϕ_vs := hϕ_ge v_s ⟨le_rfl, hvs_le⟩
  have hbdy1 : ‖(1 / (Complex.I * (c' : ℂ))) * (B v_s / (ϕ1 v_s : ℂ) * e v_s)‖ ≤
      (M0 / δ_mid) * c' ^ (-(3 / 2 : ℝ)) := by
    rw [norm_mul, norm_mul, hlam_norm, norm_div, hexp_1, mul_one]
    calc c'⁻¹ * (‖B v_s‖ / ‖(ϕ1 v_s : ℂ)‖)
        ≤ c'⁻¹ * (M0 * c'⁻¹ ^ (1 / 2 : ℝ) / δ_mid) := by
          gcongr; rw [← hvs_eq]; exact hvs_bd
      _ = (M0 / δ_mid) * (c'⁻¹ * c'⁻¹ ^ (1 / 2 : ℝ)) := by ring
      _ = (M0 / δ_mid) * c' ^ (-(3 / 2 : ℝ)) := by rw [hc_m12]
  have hvs12 : v_s ^ (-(1 / 2 : ℝ)) = c' ^ (1 / 2 : ℝ) := by
    rw [hvs_eq, ← Real.rpow_neg_one c', ← Real.rpow_mul hc'_pos.le]; norm_num
  have hvs12' : v_s ^ (1 / 2 : ℝ) ≤ 1 := by
    rw [hvs_eq]
    exact Real.rpow_le_one (inv_nonneg.mpr hc'_pos.le) (inv_le_one_of_one_le₀ hc') (by norm_num)
  have hϕ2_le : ∀ v ∈ Icc v_s v₀, |ϕ2 v| ≤ 4 * π / 3 := fun v hv => by
    dsimp [ϕ2]
    have h1 := edgeF'_nonneg (hvs.le.trans hv.1)
    have h2 := edgeF'_le_one v
    rw [abs_of_nonneg (mul_nonneg (by positivity) h1)]
    exact (mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * π / 3)).trans_eq (mul_one _)
  have hbdy2 : ‖(1 / (Complex.I * (c' : ℂ))) ^ 2 *
      (ibpH B Bs1 ϕ1 ϕ2 v_s / (ϕ1 v_s : ℂ) * e v_s)‖ ≤
      (M1 / δ_mid ^ 2 + M0 * (4 * π / 3) / δ_mid ^ 3) * c' ^ (-(3 / 2 : ℝ)) := by
    rw [norm_mul, norm_pow, hlam_norm, norm_mul, hexp_1, mul_one]
    have hibp_s : ‖ibpH B Bs1 ϕ1 ϕ2 v_s / (ϕ1 v_s : ℂ)‖ ≤
        M1 * c' ^ (1 / 2 : ℝ) / δ_mid ^ 2 + M0 * (4 * π / 3) / δ_mid ^ 3 := by
      unfold ibpH
      have heq : (Bs1 v_s * (ϕ1 v_s : ℂ) - B v_s * (ϕ2 v_s : ℂ)) / (ϕ1 v_s : ℂ) ^ 2 / (ϕ1 v_s : ℂ) =
          Bs1 v_s / (ϕ1 v_s : ℂ) ^ 2 - B v_s * (ϕ2 v_s : ℂ) / (ϕ1 v_s : ℂ) ^ 3 := by
        have hne_s : (ϕ1 v_s : ℂ) ≠ 0 := by exact_mod_cast hne v_s ⟨le_rfl, hvs_le⟩
        field_simp [hne_s]
      rw [heq]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_div, norm_pow, norm_div, norm_mul, norm_pow]
      have hϕ_vs' : δ_mid ≤ |ϕ1 v_s| := by simpa [Complex.norm_real, Real.norm_eq_abs] using hϕ_vs
      have t1 : ‖Bs1 v_s‖ / ‖(ϕ1 v_s : ℂ)‖ ^ 2 ≤ M1 * c' ^ (1 / 2 : ℝ) / δ_mid ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        calc ‖Bs1 v_s‖ / |ϕ1 v_s| ^ 2
            ≤ (M1 * v_s ^ (-(1 / 2 : ℝ))) / δ_mid ^ 2 := div_le_div₀ (by positivity) hvs_d_bd (by positivity) (by gcongr)
          _ = M1 * c' ^ (1 / 2 : ℝ) / δ_mid ^ 2 := by rw [hvs12]
      have t2 : ‖B v_s‖ * ‖(ϕ2 v_s : ℂ)‖ / ‖(ϕ1 v_s : ℂ)‖ ^ 3 ≤ M0 * (4 * π / 3) / δ_mid ^ 3 := by
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
        have hB1' : ‖B v_s‖ ≤ M0 := hvs_bd.trans (mul_le_of_le_one_right hM0 hvs12')
        exact div_le_div₀ (by positivity) (mul_le_mul hB1' (hϕ2_le v_s ⟨le_rfl, hvs_le⟩)
          (abs_nonneg _) hM0) (by positivity) (by gcongr)
      exact add_le_add t1 t2
    have hci2 : (c'⁻¹) ^ 2 = c' ^ (-2 : ℝ) := by
      rw [← Real.rpow_neg_one c', ← Real.rpow_natCast, ← Real.rpow_mul hc'_pos.le]; norm_num
    rw [hci2]
    calc c' ^ (-2 : ℝ) * ‖ibpH B Bs1 ϕ1 ϕ2 v_s / (ϕ1 v_s : ℂ)‖
        ≤ c' ^ (-2 : ℝ) * (M1 * c' ^ (1 / 2 : ℝ) / δ_mid ^ 2 + M0 * (4 * π / 3) / δ_mid ^ 3) :=
          mul_le_mul_of_nonneg_left hibp_s (by positivity)
      _ = (M1 / δ_mid ^ 2) * (c' ^ (-2 : ℝ) * c' ^ (1 / 2 : ℝ)) +
            (M0 * (4 * π / 3) / δ_mid ^ 3) * c' ^ (-2 : ℝ) := by ring
      _ ≤ (M1 / δ_mid ^ 2) * c' ^ (-(3 / 2 : ℝ)) +
            (M0 * (4 * π / 3) / δ_mid ^ 3) * c' ^ (-(3 / 2 : ℝ)) := by
          rw [hc_m2_12]; gcongr
      _ = _ := by ring
  let C_i1 : ℝ := M2 / δ_mid ^ 2
  let C_i2 : ℝ := 3 * M1 * (4 * π / 3) / δ_mid ^ 3
  let C_i3 : ℝ := M0 * (32 * π ^ 2 / 3 / δ_mid ^ 3 + 3 * (4 * π / 3) ^ 2 / δ_mid ^ 4)
  have hu_n0 : (0 : ℝ) ∉ uIcc v_s v₀ := fun h => by
    rw [uIcc_of_le hvs_le] at h; linarith [h.1]
  have hint_fn : ∀ r : ℝ, IntervalIntegrable (fun v : ℝ => v ^ r) volume v_s v₀ := fun r =>
    intervalIntegral.intervalIntegrable_rpow (Or.inr hu_n0)
  have hint_maj : IntervalIntegrable
      (fun v : ℝ => C_i1 * v ^ (-(3 / 2 : ℝ)) + C_i2 * v ^ (-(1 / 2 : ℝ)) + C_i3 * v ^ (1 / 2 : ℝ))
      volume v_s v₀ :=
    (((hint_fn (-(3 / 2))).const_mul C_i1).add
      ((hint_fn (-(1 / 2))).const_mul C_i2)).add
      ((hint_fn (1 / 2)).const_mul C_i3)
  have hQ_bd : ∀ v ∈ Icc v_s v₀,
      ‖ibpQ B Bs1 Bs2 ϕ1 ϕ2 ϕ3 v * e v‖ ≤
        C_i1 * v ^ (-(3 / 2 : ℝ)) + C_i2 * v ^ (-(1 / 2 : ℝ)) + C_i3 * v ^ (1 / 2 : ℝ) := fun v hv => by
    rw [norm_mul, hexp_1, mul_one]
    have hv_pos : 0 < v := hvs.trans_le hv.1
    have hvi := hsub_ioc hv
    have hϕv := hϕ_ge v hv
    have hϕ2v := hϕ2_le v hv
    have hϕ3v : |ϕ3 v| ≤ 32 * π ^ 2 / 3 := by
      dsimp [ϕ3]
      have h0 : 0 ≤ v := hvs.le.trans hv.1
      have h3 := edgeF''_bound h0
      have hexp1 : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      rw [abs_of_pos (mul_pos (by positivity) h3.1)]
      nlinarith [h3.2, hexp1]
    unfold ibpQ
    have hvr1 : 0 ≤ v ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hv_pos.le _
    have hvr2 : 0 ≤ v ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hv_pos.le _
    have hvr3 : 0 ≤ v ^ (1 / 2 : ℝ) := Real.rpow_nonneg hv_pos.le _
    have t1 : ‖Bs2 v / (ϕ1 v : ℂ) ^ 2‖ ≤ C_i1 * v ^ (-(3 / 2 : ℝ)) := by
      rw [norm_div, norm_pow]
      exact (div_le_div₀ (mul_nonneg hM2 hvr1) (hB2 v hvi) (by positivity)
        (pow_le_pow_left₀ hδ_pos.le hϕv 2)).trans_eq (by dsimp [C_i1]; ring)
    have t2 : ‖3 * Bs1 v * (ϕ2 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ ≤ C_i2 * v ^ (-(1 / 2 : ℝ)) := by
      rw [norm_div, norm_mul, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, Complex.norm_real,
        Real.norm_eq_abs, norm_pow]
      calc 3 * ‖Bs1 v‖ * |ϕ2 v| / ‖(ϕ1 v : ℂ)‖ ^ 3
          ≤ 3 * (M1 * v ^ (-(1 / 2 : ℝ))) * (4 * π / 3) / δ_mid ^ 3 :=
            div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left (hB1 v hvi) (by norm_num))
              hϕ2v (abs_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg hM1 hvr2))) (by positivity)
              (pow_le_pow_left₀ hδ_pos.le hϕv 3)
        _ = C_i2 * v ^ (-(1 / 2 : ℝ)) := by dsimp [C_i2]; ring
    have t3 : ‖B v * (ϕ3 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ ≤
        (M0 * (32 * π ^ 2 / 3 / δ_mid ^ 3)) * v ^ (1 / 2 : ℝ) := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      calc ‖B v‖ * |ϕ3 v| / ‖(ϕ1 v : ℂ)‖ ^ 3
          ≤ (M0 * v ^ (1 / 2 : ℝ)) * (32 * π ^ 2 / 3) / δ_mid ^ 3 :=
            div_le_div₀ (by positivity) (mul_le_mul (hB0 v hvi) hϕ3v (abs_nonneg _) (mul_nonneg hM0 hvr3))
              (by positivity) (pow_le_pow_left₀ hδ_pos.le hϕv 3)
        _ = (M0 * (32 * π ^ 2 / 3 / δ_mid ^ 3)) * v ^ (1 / 2 : ℝ) := by ring
    have t4 : ‖3 * B v * (ϕ2 v : ℂ) ^ 2 / (ϕ1 v : ℂ) ^ 4‖ ≤
        (M0 * (3 * (4 * π / 3) ^ 2 / δ_mid ^ 4)) * v ^ (1 / 2 : ℝ) := by
      rw [norm_div, norm_mul, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, norm_pow]
      calc 3 * ‖B v‖ * |ϕ2 v| ^ 2 / ‖(ϕ1 v : ℂ)‖ ^ 4
          ≤ 3 * (M0 * v ^ (1 / 2 : ℝ)) * (4 * π / 3) ^ 2 / δ_mid ^ 4 :=
            div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left (hB0 v hvi) (by norm_num))
              (pow_le_pow_left₀ (abs_nonneg _) hϕ2v 2) (sq_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg hM0 hvr3)))
              (by positivity) (pow_le_pow_left₀ hδ_pos.le hϕv 4)
        _ = (M0 * (3 * (4 * π / 3) ^ 2 / δ_mid ^ 4)) * v ^ (1 / 2 : ℝ) := by ring
    have hsub1 := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)
    have hadd := (norm_add_le _ _).trans (add_le_add hsub1 t4)
    refine hadd.trans_eq ?_
    dsimp [C_i3]; ring
  have hrem_int : ‖(1 / (Complex.I * (c' : ℂ))) ^ 2 * ∫ v in v_s..v₀, ibpQ B Bs1 Bs2 ϕ1 ϕ2 ϕ3 v * e v‖ ≤
      (2 * M2 / δ_mid ^ 2 + 6 * M1 * (4 * π / 3) * v₀ ^ (1 / 2 : ℝ) / δ_mid ^ 3 +
        (2 / 3) * M0 * v₀ ^ (3 / 2 : ℝ) * (32 * π ^ 2 / 3 / δ_mid ^ 3 +
          3 * (4 * π / 3) ^ 2 / δ_mid ^ 4)) * c' ^ (-(3 / 2 : ℝ)) := by
    rw [norm_mul, norm_pow, hlam_norm]
    have hci2 : (c'⁻¹) ^ 2 = c' ^ (-2 : ℝ) := by
      rw [← Real.rpow_neg_one c', ← Real.rpow_natCast, ← Real.rpow_mul hc'_pos.le]; norm_num
    rw [hci2]
    have hnorm_le := intervalIntegral.norm_integral_le_of_norm_le hvs_le
      (Filter.Eventually.of_forall fun v hv => hQ_bd v ⟨hv.1.le, hv.2⟩) hint_maj
    have hi1 : ∫ v in v_s..v₀, v ^ (-(3 / 2 : ℝ)) ≤ 2 * c' ^ (1 / 2 : ℝ) := by
      rw [integral_rpow (Or.inr ⟨by norm_num, hu_n0⟩)]
      rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num, hvs12]
      have : 0 ≤ v₀ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hv₀_pos.le _
      linarith
    have hi2 : ∫ v in v_s..v₀, v ^ (-(1 / 2 : ℝ)) ≤ 2 * v₀ ^ (1 / 2 : ℝ) := by
      rw [integral_rpow (Or.inl (by norm_num))]
      rw [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by norm_num]
      have : 0 ≤ v_s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hvs.le _
      linarith
    have hi3 : ∫ v in v_s..v₀, v ^ (1 / 2 : ℝ) ≤ (2 / 3 : ℝ) * v₀ ^ (3 / 2 : ℝ) := by
      rw [integral_rpow (Or.inl (by norm_num))]
      rw [show (1 / 2 : ℝ) + 1 = (3 / 2 : ℝ) by norm_num]
      have : 0 ≤ v_s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hvs.le _
      linarith
    have hint_eval : ∫ v in v_s..v₀, C_i1 * v ^ (-(3 / 2 : ℝ)) + C_i2 * v ^ (-(1 / 2 : ℝ)) +
        C_i3 * v ^ (1 / 2 : ℝ) =
        C_i1 * (∫ v in v_s..v₀, v ^ (-(3 / 2 : ℝ))) + C_i2 * (∫ v in v_s..v₀, v ^ (-(1 / 2 : ℝ))) +
          C_i3 * (∫ v in v_s..v₀, v ^ (1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_add (((hint_fn _).const_mul _).add
          ((hint_fn _).const_mul _)) ((hint_fn _).const_mul _),
        intervalIntegral.integral_add ((hint_fn _).const_mul _) ((hint_fn _).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have htot_i : ‖∫ v in v_s..v₀, ibpQ B Bs1 Bs2 ϕ1 ϕ2 ϕ3 v * e v‖ ≤
        (2 * C_i1 + 2 * C_i2 * v₀ ^ (1 / 2 : ℝ) + (2 / 3) * C_i3 * v₀ ^ (3 / 2 : ℝ)) * c' ^ (1 / 2 : ℝ) := by
      have hc1 : C_i1 * (∫ v in v_s..v₀, v ^ (-(3 / 2 : ℝ))) ≤ (2 * C_i1) * c' ^ (1 / 2 : ℝ) := by
        calc C_i1 * (∫ v in v_s..v₀, v ^ (-(3 / 2 : ℝ))) ≤ C_i1 * (2 * c' ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hi1 (by dsimp [C_i1]; positivity)
          _ = _ := by ring
      have hc2 : C_i2 * (∫ v in v_s..v₀, v ^ (-(1 / 2 : ℝ))) ≤ (2 * C_i2 * v₀ ^ (1 / 2 : ℝ)) * c' ^ (1 / 2 : ℝ) := by
        calc C_i2 * (∫ v in v_s..v₀, v ^ (-(1 / 2 : ℝ))) ≤ C_i2 * (2 * v₀ ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hi2 (by dsimp [C_i2]; positivity)
          _ = (2 * C_i2 * v₀ ^ (1 / 2 : ℝ)) * 1 := by ring
          _ ≤ (2 * C_i2 * v₀ ^ (1 / 2 : ℝ)) * c' ^ (1 / 2 : ℝ) := by gcongr
      have hc3 : C_i3 * (∫ v in v_s..v₀, v ^ (1 / 2 : ℝ)) ≤ ((2 / 3) * C_i3 * v₀ ^ (3 / 2 : ℝ)) * c' ^ (1 / 2 : ℝ) := by
        calc C_i3 * (∫ v in v_s..v₀, v ^ (1 / 2 : ℝ)) ≤ C_i3 * ((2 / 3) * v₀ ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hi3 (by dsimp [C_i3]; positivity)
          _ = ((2 / 3) * C_i3 * v₀ ^ (3 / 2 : ℝ)) * 1 := by ring
          _ ≤ ((2 / 3) * C_i3 * v₀ ^ (3 / 2 : ℝ)) * c' ^ (1 / 2 : ℝ) := by gcongr
      refine hnorm_le.trans ?_
      rw [hint_eval]
      linarith
    calc c' ^ (-2 : ℝ) * ‖∫ v in v_s..v₀, ibpQ B Bs1 Bs2 ϕ1 ϕ2 ϕ3 v * e v‖
        ≤ c' ^ (-2 : ℝ) * ((2 * C_i1 + 2 * C_i2 * v₀ ^ (1 / 2 : ℝ) +
            (2 / 3) * C_i3 * v₀ ^ (3 / 2 : ℝ)) * c' ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left htot_i (by positivity)
      _ = (2 * C_i1 + 2 * C_i2 * v₀ ^ (1 / 2 : ℝ) + (2 / 3) * C_i3 * v₀ ^ (3 / 2 : ℝ)) *
            (c' ^ (-2 : ℝ) * c' ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hc_m2_12]; dsimp [C_i1, C_i2, C_i3]; ring
  have hdiff_eq : (∫ v in v_s..v₀, B v * e v) -
      ((1 / (Complex.I * (c' : ℂ))) * (B v₀ / (ϕ1 v₀ : ℂ) * e v₀) -
        (1 / (Complex.I * (c' : ℂ))) ^ 2 * (ibpH B Bs1 ϕ1 ϕ2 v₀ / (ϕ1 v₀ : ℂ) * e v₀)) =
      -((1 / (Complex.I * (c' : ℂ))) * (B v_s / (ϕ1 v_s : ℂ) * e v_s)) +
        (1 / (Complex.I * (c' : ℂ))) ^ 2 * (ibpH B Bs1 ϕ1 ϕ2 v_s / (ϕ1 v_s : ℂ) * e v_s) +
        (1 / (Complex.I * (c' : ℂ))) ^ 2 * ∫ v in v_s..v₀, ibpQ B Bs1 Bs2 ϕ1 ϕ2 ϕ3 v * e v := by
    change (∫ v in v_s..v₀, B v * Complex.exp (Complex.I * (c' : ℂ) * (phiDual v x' : ℂ))) - _ = _ at *
    rw [hibp]; ring
  rw [hdiff_eq]
  refine (norm_add_le _ _).trans ?_
  have hbdy1' : ‖-((1 / (Complex.I * (c' : ℂ))) * (B v_s / (ϕ1 v_s : ℂ) * e v_s))‖ ≤
      (M0 / δ_mid) * c' ^ (-(3 / 2 : ℝ)) := by rwa [norm_neg]
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add hbdy1' hbdy2)) hrem_int).trans_eq ?_
  ring

lemma kedge_left_ibp_outer_bound {v₀ vstar v_L δ_loc θ K_L c' x' : ℝ}
    (hv₀ : 0 < v₀) (hv₀_L : v₀ ≤ v_L) (hv_L_lt : v_L < vstar)
    (hδ : 0 < δ_loc) (hθ : 0 < θ) (hvL_eq : v_L = vstar - (θ / 4) * δ_loc)
    (hKL : 0 ≤ K_L) (hc' : 1 ≤ c') (hx' : edgeF vstar = x')
    {BL BL1 BL2 : ℝ → ℂ} (hBL : D2 (Icc v₀ v_L) BL BL1 BL2 K_L)
    (hL_zero : BL v_L = 0 ∧ BL1 v_L = 0) :
    let ϕ1 : ℝ → ℝ := fun v => (4 * π / 3) * (edgeF v - x')
    let ϕ2 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF' v
    let e : ℝ → ℂ := fun v => Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v x' : ℝ) : ℂ))
    let c0 : ℝ := (4 * π / 3) * edgeF' v₀
    let η : ℝ := (θ / 4) * δ_loc
    ‖(∫ v in v₀..v_L, BL v * e v) +
      ((1 / (Complex.I * (c' : ℂ))) * (BL v₀ / (ϕ1 v₀ : ℂ) * e v₀) -
        (1 / (Complex.I * (c' : ℂ))) ^ 2 * (ibpH BL BL1 ϕ1 ϕ2 v₀ / (ϕ1 v₀ : ℂ) * e v₀))‖ ≤
      (K_L * (1 / c0 ^ 2 + 3 * (4 * π / 3) / (c0 ^ 3 * η) + (32 * π ^ 2 / 3) / (c0 ^ 3 * η) +
        3 * (4 * π / 3) ^ 2 / (c0 ^ 4 * η ^ 2)) / η) * c' ^ (-2 : ℝ) := by
  intro ϕ1 ϕ2 e c0 η
  have hpi := Real.pi_pos
  have hc0_pos : 0 < c0 := mul_pos (by positivity) (edgeF'_pos hv₀)
  have hη_pos : 0 < η := by dsimp [η]; positivity
  have hc'_pos : 0 < c' := by linarith
  let ϕ3 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF'' v
  have hϕ_ge : ∀ v ∈ Icc v₀ v_L, c0 * (vstar - v) ≤ -ϕ1 v := fun v hv => by
    have hsub := phiDual_sub_edgeF_ge hv₀ hv.1 (hv.2.trans hv_L_lt.le)
    rw [hx'] at hsub
    dsimp [ϕ1, c0]
    linarith [mul_le_mul_of_nonneg_left hsub (by positivity : 0 ≤ 4 * π / 3)]
  have hne : ∀ v ∈ Icc v₀ v_L, ϕ1 v ≠ 0 := fun v hv => by
    have h1 := hϕ_ge v hv
    have h2 : 0 < vstar - v := by linarith [hv.2]
    have h3 : 0 < c0 * (vstar - v) := mul_pos hc0_pos h2
    linarith
  have hc3 : ContinuousOn ϕ3 (Icc v₀ v_L) :=
    (continuous_const.mul (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF'' t).continuousAt)).continuousOn
  have hibp := ibp_twice hv₀_L hc'_pos.ne'
    (ϕ := fun u => phiDual u x') (ϕ1 := ϕ1) (ϕ2 := ϕ2) (ϕ3 := ϕ3)
    (fun v _ => phiDual_deriv x' v)
    (fun v _ => ((hasDerivAt_edgeF v).sub_const x').const_mul (4 * π / 3))
    (fun v _ => (hasDerivAt_edgeF' v).const_mul (4 * π / 3))
    hne hBL.d1 hBL.d2 hBL.c2 hc3
  have hz1 : BL v_L / (ϕ1 v_L : ℂ) * e v_L = 0 := by rw [hL_zero.1]; simp
  have hz2 : ibpH BL BL1 ϕ1 ϕ2 v_L / (ϕ1 v_L : ℂ) * e v_L = 0 := by
    unfold ibpH; rw [hL_zero.1, hL_zero.2]; simp
  have hexp_1 : ∀ v : ℝ, ‖e v‖ = 1 := fun v => by
    dsimp [e]; rw [mul_assoc, Complex.norm_exp]; simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have hlam_norm : ‖(1 : ℂ) / (Complex.I * (c' : ℂ))‖ = c'⁻¹ := by
    rw [one_div, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc'_pos]
  let C_q : ℝ := K_L * (1 / c0 ^ 2 + 3 * (4 * π / 3) / (c0 ^ 3 * η) + (32 * π ^ 2 / 3) / (c0 ^ 3 * η) +
    3 * (4 * π / 3) ^ 2 / (c0 ^ 4 * η ^ 2))
  have hCQ_nn : 0 ≤ C_q := by positivity
  have hQ_bd : ∀ v ∈ Icc v₀ v_L, ‖ibpQ BL BL1 BL2 ϕ1 ϕ2 ϕ3 v * e v‖ ≤ C_q * (vstar - v) ^ (-2 : ℝ) := fun v hv => by
    rw [norm_mul, hexp_1, mul_one]
    have hvv : η ≤ vstar - v := by dsimp [η]; linarith [hv.2]
    have hvp : 0 < vstar - v := hη_pos.trans_le hvv
    have hϕv : c0 * (vstar - v) ≤ ‖(ϕ1 v : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [hϕ_ge v hv, mul_pos hc0_pos hvp])]
      exact hϕ_ge v hv
    have hϕv_pos : 0 < c0 * (vstar - v) := mul_pos hc0_pos hvp
    have h2 : (vstar - v) ^ (-2 : ℝ) = ((vstar - v) ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hvp.le, Real.rpow_natCast]
    have hϕ2v : |ϕ2 v| ≤ 4 * π / 3 := by
      dsimp [ϕ2]; rw [abs_of_nonneg (mul_nonneg (by positivity) (edgeF'_nonneg (hv₀.le.trans hv.1)))]
      exact (mul_le_mul_of_nonneg_left (edgeF'_le_one v) (by positivity : (0 : ℝ) ≤ 4 * π / 3)).trans_eq (mul_one _)
    have hϕ3v : |ϕ3 v| ≤ 32 * π ^ 2 / 3 := by
      dsimp [ϕ3]
      have h0 : 0 ≤ v := hv₀.le.trans hv.1
      have h3 := edgeF''_bound h0
      have hexp1 : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      rw [abs_of_pos (mul_pos (by positivity) h3.1)]
      nlinarith [h3.2, hexp1]
    unfold ibpQ
    have t1 : ‖BL2 v / (ϕ1 v : ℂ) ^ 2‖ ≤ (K_L / c0 ^ 2) * (vstar - v) ^ (-2 : ℝ) := by
      rw [norm_div, norm_pow, h2]
      calc ‖BL2 v‖ / ‖(ϕ1 v : ℂ)‖ ^ 2
          ≤ K_L / (c0 * (vstar - v)) ^ 2 := div_le_div₀ hKL (hBL.b2 v hv) (by positivity) (by gcongr)
        _ = (K_L / c0 ^ 2) * ((vstar - v) ^ 2)⁻¹ := by
            have hc2 : (c0 * (vstar - v)) ^ 2 = c0 ^ 2 * (vstar - v) ^ 2 := by ring
            rw [hc2]; field_simp [hc0_pos.ne', hvp.ne']
    have t2 : ‖3 * BL1 v * (ϕ2 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ ≤
        (K_L * (3 * (4 * π / 3) / (c0 ^ 3 * η))) * (vstar - v) ^ (-2 : ℝ) := by
      rw [norm_div, norm_mul, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, Complex.norm_real,
        Real.norm_eq_abs, norm_pow, h2]
      calc 3 * ‖BL1 v‖ * |ϕ2 v| / ‖(ϕ1 v : ℂ)‖ ^ 3
          ≤ 3 * K_L * (4 * π / 3) / (c0 * (vstar - v)) ^ 3 :=
            div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left (hBL.b1 v hv) (by norm_num))
              hϕ2v (abs_nonneg _) (by positivity)) (by positivity) (by gcongr)
        _ = (K_L * (3 * (4 * π / 3) / c0 ^ 3)) * ((vstar - v) ^ 2)⁻¹ / (vstar - v) := by
            have hc3 : (c0 * (vstar - v)) ^ 3 = c0 ^ 3 * (vstar - v) ^ 2 * (vstar - v) := by ring
            rw [hc3]; field_simp [hc0_pos.ne', hvp.ne']
        _ ≤ (K_L * (3 * (4 * π / 3) / c0 ^ 3)) * ((vstar - v) ^ 2)⁻¹ / η :=
            div_le_div_of_nonneg_left (by positivity) hη_pos hvv
        _ = (K_L * (3 * (4 * π / 3) / (c0 ^ 3 * η))) * ((vstar - v) ^ 2)⁻¹ := by ring
    have t3 : ‖BL v * (ϕ3 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ ≤
        (K_L * ((32 * π ^ 2 / 3) / (c0 ^ 3 * η))) * (vstar - v) ^ (-2 : ℝ) := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, h2]
      calc ‖BL v‖ * |ϕ3 v| / ‖(ϕ1 v : ℂ)‖ ^ 3
          ≤ K_L * (32 * π ^ 2 / 3) / (c0 * (vstar - v)) ^ 3 :=
            div_le_div₀ (by positivity) (mul_le_mul (hBL.b0 v hv) hϕ3v (abs_nonneg _) hKL)
              (by positivity) (by gcongr)
        _ = (K_L * ((32 * π ^ 2 / 3) / c0 ^ 3)) * ((vstar - v) ^ 2)⁻¹ / (vstar - v) := by
            have hc3 : (c0 * (vstar - v)) ^ 3 = c0 ^ 3 * (vstar - v) ^ 2 * (vstar - v) := by ring
            rw [hc3]; field_simp [hc0_pos.ne', hvp.ne']
        _ ≤ (K_L * ((32 * π ^ 2 / 3) / c0 ^ 3)) * ((vstar - v) ^ 2)⁻¹ / η :=
            div_le_div_of_nonneg_left (by positivity) hη_pos hvv
        _ = (K_L * ((32 * π ^ 2 / 3) / (c0 ^ 3 * η))) * ((vstar - v) ^ 2)⁻¹ := by ring
    have t4 : ‖3 * BL v * (ϕ2 v : ℂ) ^ 2 / (ϕ1 v : ℂ) ^ 4‖ ≤
        (K_L * (3 * (4 * π / 3) ^ 2 / (c0 ^ 4 * η ^ 2))) * (vstar - v) ^ (-2 : ℝ) := by
      rw [norm_div, norm_mul, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, norm_pow, h2]
      calc 3 * ‖BL v‖ * |ϕ2 v| ^ 2 / ‖(ϕ1 v : ℂ)‖ ^ 4
          ≤ 3 * K_L * (4 * π / 3) ^ 2 / (c0 * (vstar - v)) ^ 4 :=
            div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left (hBL.b0 v hv) (by norm_num))
              (pow_le_pow_left₀ (abs_nonneg _) hϕ2v 2) (sq_nonneg _) (by positivity))
              (by positivity) (by gcongr)
        _ = (K_L * (3 * (4 * π / 3) ^ 2 / c0 ^ 4)) * ((vstar - v) ^ 2)⁻¹ / (vstar - v) ^ 2 := by
            have hc4 : (c0 * (vstar - v)) ^ 4 = c0 ^ 4 * ((vstar - v) ^ 2) * (vstar - v) ^ 2 := by ring
            rw [hc4]; field_simp [hc0_pos.ne', hvp.ne']
        _ ≤ (K_L * (3 * (4 * π / 3) ^ 2 / c0 ^ 4)) * ((vstar - v) ^ 2)⁻¹ / η ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hη_pos.le hvv 2)
        _ = (K_L * (3 * (4 * π / 3) ^ 2 / (c0 ^ 4 * η ^ 2))) * ((vstar - v) ^ 2)⁻¹ := by ring
    have hsub1 := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)
    have hadd := (norm_add_le _ _).trans (add_le_add hsub1 t4)
    refine hadd.trans_eq ?_
    dsimp [C_q]; ring
  have hint_maj : IntervalIntegrable (fun v : ℝ => C_q * (vstar - v) ^ (-2 : ℝ)) volume v₀ v_L := by
    have hcomp : IntervalIntegrable (fun u : ℝ => C_q * u ^ (-2 : ℝ)) volume (vstar - v_L) (vstar - v₀) := by
      refine (intervalIntegral.intervalIntegrable_rpow (Or.inr fun h0 => ?_)).const_mul C_q
      rw [uIcc_of_le (sub_le_sub_left hv₀_L vstar)] at h0
      linarith [h0.1]
    simpa [sub_sub_cancel] using (hcomp.comp_sub_left vstar).symm
  have hnorm_le := intervalIntegral.norm_integral_le_of_norm_le hv₀_L
    (Filter.Eventually.of_forall fun v hv => hQ_bd v ⟨hv.1.le, hv.2⟩) hint_maj
  have hi_eval : ∫ v in v₀..v_L, C_q * (vstar - v) ^ (-2 : ℝ) ≤ C_q / η := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-2 : ℝ)) vstar]
    have hne0 : (0 : ℝ) ∉ uIcc (vstar - v_L) (vstar - v₀) := fun h => by
      rw [uIcc_of_le (sub_le_sub_left hv₀_L vstar)] at h
      linarith [h.1]
    rw [integral_rpow (Or.inr ⟨by norm_num, hne0⟩)]
    rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one,
      show vstar - v_L = η by dsimp [η]; linarith]
    have hnn : 0 ≤ (vstar - v₀)⁻¹ := inv_nonneg.mpr (by linarith)
    calc C_q * (((vstar - v₀)⁻¹ - η⁻¹) / -1) = C_q / η - C_q * (vstar - v₀)⁻¹ := by ring
      _ ≤ C_q / η := by linarith [mul_nonneg hCQ_nn hnn]
  have hadd_eq : (∫ v in v₀..v_L, BL v * e v) +
      ((1 / (Complex.I * (c' : ℂ))) * (BL v₀ / (ϕ1 v₀ : ℂ) * e v₀) -
        (1 / (Complex.I * (c' : ℂ))) ^ 2 * (ibpH BL BL1 ϕ1 ϕ2 v₀ / (ϕ1 v₀ : ℂ) * e v₀)) =
      (1 / (Complex.I * (c' : ℂ))) ^ 2 * ∫ v in v₀..v_L, ibpQ BL BL1 BL2 ϕ1 ϕ2 ϕ3 v * e v := by
    change (∫ v in v₀..v_L, BL v * Complex.exp (Complex.I * (c' : ℂ) * (phiDual v x' : ℂ))) + _ = _ at *
    rw [hibp, hz1, hz2]; ring
  rw [hadd_eq, norm_mul, norm_pow, hlam_norm]
  have hci2 : (c'⁻¹) ^ 2 = c' ^ (-2 : ℝ) := by
    rw [← Real.rpow_neg_one c', ← Real.rpow_natCast, ← Real.rpow_mul hc'_pos.le]; norm_num
  rw [hci2, mul_comm (c' ^ (-2 : ℝ))]
  exact mul_le_mul_of_nonneg_right (hnorm_le.trans hi_eval) (by positivity)

/-! ### 3. Abstract outer-band kernel theorem and `cts:Kedge-outer` -/


end

end FormalResearch.ModularBootstrap.FiveTerm
