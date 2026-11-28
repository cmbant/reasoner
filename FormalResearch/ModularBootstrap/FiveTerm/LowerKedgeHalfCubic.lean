module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeCfu
public import FormalResearch.SignUncertainty.CtWindowSignedSplit
public import FormalResearch.SignUncertainty.FineOrderSignedDiv

/-!
# Virasoro `HalfCubicData` Instances for Principal and Auxiliary Edge Kernels (`cts:Kedge-signed`)

Packages the holomorphic CFU amplitude on a fixed polydisc around `(0, 0)` into:
* `virPsi`, `virThetaOutC`, `virPhaseFactor`, `virQ`, `virEb`;
* `virasoroHalfCubic : HalfCubicData` via `mkHalfCubicOfCauchy`, with `‖E_n(-a, a) - 1‖ = O(n⁻¹)`
  and `‖O_n(-a, a)‖ = O(n⁻¹)` for `n ≥ 1`;
* `virasoroHalfCubicAux : HalfCubicData` for the auxiliary kernel `(1 - 2 i virV)⁻¹` with the same
  radius `s₁` and shift `virPsi`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FineOrderSigned

noncomputable section

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### 1. Analytic shift `virPsi`, complex `virThetaOutC`, and phase factor `virPhaseFactor` -/

/-- Rescaled Virasoro shift `ψ_n(a) = 2^{2/3} β_* virasoroPsiEps(n^{-2}, (2^{2/3} β_*)⁻¹ a)`. -/
def virPsi (n : ℝ) (a : ℂ) : ℂ :=
  (((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip : ℝ) : ℂ) *
    virasoroPsiEps (n ^ (-2 : ℝ)) (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a)

/-- Complexified odd edge outer phase `θ_out(y(F(v))) = yVirC(v) * Tout(yVirC(v)^2)`. -/
def virThetaOutC (v : ℂ) : ℂ :=
  yVirC v * psiBase.Tout (yVirC v ^ 2)

/-- Combined saddle-normalized geometric and outer-phase factor `G₀(s, a)`
satisfying `G₀(±√(-a), a) = 1` for real `a < 0` small. -/
def virPhaseFactor (s a : ℂ) : ℂ :=
  virMGeo s a * Complex.exp (Complex.I * (virThetaOutC (virV s a) - s * virPsi 0 a))

/-- `ε`-dependent edge-multiplier and shift perturbation factor `Eb_n(s, a) = 1 + O(n⁻²)`. -/
def virEb (n : ℝ) (s a : ℂ) : ℂ :=
  if 2 ≤ n then
    lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV s a)) ^ 2 *
      Complex.exp (-Complex.I * s * (virPsi n a - virPsi 0 a))
  else 1

lemma virPsi_scale_pos : 0 < (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip :=
  mul_pos (Real.rpow_pos_of_pos zero_lt_two _) betaTip_pos

lemma yVirC_zero : yVirC 0 = 0 := by
  unfold yVirC; simp

lemma virThetaOutC_neg (v : ℂ) : virThetaOutC (-v) = -virThetaOutC v := by
  unfold virThetaOutC
  rw [yVirC_neg, neg_sq]
  ring

lemma virThetaOutC_conj : ∀ᶠ v : ℂ in 𝓝 0,
    virThetaOutC (starRingEnd ℂ v) = starRingEnd ℂ (virThetaOutC v) := by
  have hcont : ContinuousAt yVirC 0 :=
    ((differentiableOn_yVirC 0 (by simp)).differentiableAt (isOpen_virStrip.mem_nhds (by simp))).continuousAt
  have hy_ball : ∀ᶠ v : ℂ in 𝓝 0, yVirC v ^ 2 ∈ ball (0 : ℂ) psiBase.rTout := by
    have hsq : Tendsto (fun v : ℂ => yVirC v ^ 2) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (fun v : ℂ => yVirC v ^ 2) 0 := hcont.pow 2
      simpa [yVirC_zero] using hc.tendsto
    exact hsq.eventually (Metric.ball_mem_nhds 0 psiBase.hrTout_pos)
  have hstrip : {v : ℂ | |v.im| < 1 / 2} ∈ 𝓝 (0 : ℂ) :=
    isOpen_virStrip.mem_nhds (by simp)
  filter_upwards [hstrip, hy_ball] with v hv hyb
  unfold virThetaOutC
  rw [yVirC_conj hv, map_mul]
  congr 1
  rw [show (starRingEnd ℂ (yVirC v)) ^ 2 = starRingEnd ℂ (yVirC v ^ 2) by simp,
    psiBase.hTout_conj _ hyb]

lemma virThetaOutC_analyticAt : AnalyticAt ℂ virThetaOutC 0 := by
  have hy_an : AnalyticAt ℂ yVirC 0 := analyticOnNhd_yVirC 0 (by simp)
  have hT_an : AnalyticAt ℂ psiBase.Tout 0 :=
    psiBase.hTout_diff.analyticOnNhd isOpen_ball 0 (mem_ball_self psiBase.hrTout_pos)
  have hsq_an : AnalyticAt ℂ (fun v : ℂ => psiBase.Tout (yVirC v ^ 2)) 0 :=
    hT_an.comp_of_eq (hy_an.pow 2) (by simp [yVirC_zero])
  exact hy_an.mul hsq_an

lemma virThetaOutC_ofReal_nonneg : ∀ᶠ v : ℝ in 𝓝 (0 : ℝ), 0 ≤ v →
    virThetaOutC (v : ℂ) = (thetaOut (lowerY (edgeF v)) : ℂ) := by
  have hcont_y : ContinuousAt (fun v : ℝ => (yVirC (v : ℂ)).re) 0 := by
    have h1 := ((differentiableOn_yVirC 0 (by simp)).differentiableAt
      (isOpen_virStrip.mem_nhds (by simp))).continuousAt.comp_of_eq
      (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))) Complex.ofReal_zero
    exact Complex.continuous_re.continuousAt.comp h1
  have hlt : ∀ᶠ v : ℝ in 𝓝 (0 : ℝ), (yVirC (v : ℂ)).re < psiBase.yTout := by
    have h0 : (yVirC ((0 : ℝ) : ℂ)).re < psiBase.yTout := by
      rw [Complex.ofReal_zero, yVirC_zero, Complex.zero_re]
      exact psiBase.hyTout_pos
    exact hcont_y.eventually (isOpen_Iio.mem_nhds h0)
  filter_upwards [hlt] with v hv_lt hv0
  rcases hv0.eq_or_lt with rfl | hv_pos
  · have hy0 : lowerY (edgeF 0) = 0 := by
      have := yVirC_ofReal_nonneg le_rfl
      rw [Complex.ofReal_zero, yVirC_zero] at this
      exact Complex.ofReal_eq_zero.mp this.symm
    unfold virThetaOutC
    rw [Complex.ofReal_zero, yVirC_zero, zero_mul, hy0, thetaOut_soft.1, Complex.ofReal_zero]
  · have hy_c : yVirC (v : ℂ) = (lowerY (edgeF v) : ℂ) := yVirC_ofReal_nonneg hv0
    have hy_re : lowerY (edgeF v) = (yVirC (v : ℂ)).re := by rw [hy_c, Complex.ofReal_re]
    have hx_gt : xiStar < edgeF v := by
      rw [← edgeF_zero]; exact edgeF_strictMonoOn le_rfl hv0 hv_pos
    have hy_pos : 0 < lowerY (edgeF v) := (yOfX_mem hx_gt).1
    have hy_lt : lowerY (edgeF v) < psiBase.yTout := by rwa [hy_re]
    have hy2_ball : (((lowerY (edgeF v) ^ 2 : ℝ)) : ℂ) ∈ ball (0 : ℂ) psiBase.rTout := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hsq : lowerY (edgeF v) ^ 2 < psiBase.yTout ^ 2 :=
        sq_lt_sq' (by linarith) hy_lt
      have h2 := psiBase.hy2_le
      have hrp := psiBase.hrTout_pos
      linarith
    have hTout_im : (psiBase.Tout (((lowerY (edgeF v) ^ 2 : ℝ)) : ℂ)).im = 0 := by
      have hc := psiBase.hTout_conj _ hy2_ball
      rw [Complex.conj_ofReal] at hc
      exact Complex.conj_eq_iff_im.mp hc.symm
    have hTout_c : psiBase.Tout (((lowerY (edgeF v) ^ 2 : ℝ)) : ℂ) =
        (((psiBase.Tout (((lowerY (edgeF v) ^ 2 : ℝ)) : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hTout_im
    have hreal := (psiBase.hTout_real (lowerY (edgeF v)) hy_pos hy_lt).1
    unfold virThetaOutC
    rw [hy_c, ← Complex.ofReal_pow, hTout_c, ← Complex.ofReal_mul, hreal]

private lemma inv_sq_le_quarter {n : ℝ} (hn : 2 ≤ n) : n ^ (-2 : ℝ) ≤ 1 / 4 := by
  have h1 : n ^ (-2 : ℝ) = (n ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith), Real.rpow_natCast]
  rw [h1, one_div, inv_le_inv₀ (by positivity) (by norm_num)]
  nlinarith

private lemma not_inv_sq_le_quarter {n : ℝ} (hn : 1 ≤ n) (h : ¬ 2 ≤ n) :
    ¬ (0 ≤ n ^ (-2 : ℝ) ∧ n ^ (-2 : ℝ) ≤ 1 / 4) := by
  intro ⟨_, hle⟩
  have h1 : n ^ (-2 : ℝ) = (n ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith), Real.rpow_natCast]
  rw [h1, one_div, inv_le_inv₀ (by positivity) (by norm_num)] at hle
  nlinarith

lemma virPsi_conj {n : ℝ} (hn : 1 ≤ n) :
    ∀ᶠ a : ℂ in 𝓝 0, virPsi n (starRingEnd ℂ a) = starRingEnd ℂ (virPsi n a) := by
  let K : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip
  by_cases hn2 : 2 ≤ n
  · have hε0 : 0 ≤ n ^ (-2 : ℝ) := by positivity
    have hε1 : n ^ (-2 : ℝ) ≤ 1 / 4 := inv_sq_le_quarter hn2
    have hspec := (chartParams.hψ_spec _ hε0 hε1).2.1
    have hρψ_pos : 0 < chartParams.ρ_ψ := lt_trans chartParams.hrψ_pos chartParams.hrψ_lt
    have hball : {a : ℂ | (((K⁻¹ : ℝ) : ℂ) * a) ∈ ball (0 : ℂ) chartParams.ρ_ψ} ∈ 𝓝 (0 : ℂ) := by
      have hc : ContinuousAt (fun a : ℂ => ((K⁻¹ : ℝ) : ℂ) * a) 0 := by fun_prop
      have hct : Tendsto (fun a : ℂ => ((K⁻¹ : ℝ) : ℂ) * a) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        simpa [mul_zero] using hc.tendsto
      exact hct.eventually (Metric.ball_mem_nhds (0 : ℂ) hρψ_pos)
    filter_upwards [hball] with a ha
    unfold virPsi
    change ((K : ℝ) : ℂ) * virasoroPsiEps (n ^ (-2 : ℝ)) (((K⁻¹ : ℝ) : ℂ) * starRingEnd ℂ a) =
      starRingEnd ℂ (((K : ℝ) : ℂ) * virasoroPsiEps (n ^ (-2 : ℝ)) (((K⁻¹ : ℝ) : ℂ) * a))
    rw [show ((K⁻¹ : ℝ) : ℂ) * starRingEnd ℂ a = starRingEnd ℂ (((K⁻¹ : ℝ) : ℂ) * a) by
      simp only [map_mul, Complex.conj_ofReal] ]
    rw [hspec _ ha, map_mul, Complex.conj_ofReal]
  · have hε_gt : ¬ (0 ≤ n ^ (-2 : ℝ) ∧ n ^ (-2 : ℝ) ≤ 1 / 4) := not_inv_sq_le_quarter hn hn2
    exact Filter.Eventually.of_forall fun a => by
      unfold virPsi virasoroPsiEps
      simp only [hε_gt, ↓reduceIte, mul_zero, map_zero]

lemma virPsi_conj_zero :
    ∀ᶠ a : ℂ in 𝓝 0, virPsi 0 (starRingEnd ℂ a) = starRingEnd ℂ (virPsi 0 a) := by
  let K : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip
  have hspec := (chartParams.hψ_spec 0 le_rfl (by norm_num)).2.1
  have hρψ_pos : 0 < chartParams.ρ_ψ := lt_trans chartParams.hrψ_pos chartParams.hrψ_lt
  have hball : {a : ℂ | (((K⁻¹ : ℝ) : ℂ) * a) ∈ ball (0 : ℂ) chartParams.ρ_ψ} ∈ 𝓝 (0 : ℂ) := by
    have hc : ContinuousAt (fun a : ℂ => ((K⁻¹ : ℝ) : ℂ) * a) 0 := by fun_prop
    have hct : Tendsto (fun a : ℂ => ((K⁻¹ : ℝ) : ℂ) * a) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa [mul_zero] using hc.tendsto
    exact hct.eventually (Metric.ball_mem_nhds (0 : ℂ) hρψ_pos)
  filter_upwards [hball] with a ha
  unfold virPsi
  change ((K : ℝ) : ℂ) * virasoroPsiEps (0 ^ (-2 : ℝ)) (((K⁻¹ : ℝ) : ℂ) * starRingEnd ℂ a) =
    starRingEnd ℂ (((K : ℝ) : ℂ) * virasoroPsiEps (0 ^ (-2 : ℝ)) (((K⁻¹ : ℝ) : ℂ) * a))
  have h0_exp : (0 : ℝ) ^ (-2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  rw [h0_exp, show ((K⁻¹ : ℝ) : ℂ) * starRingEnd ℂ a = starRingEnd ℂ (((K⁻¹ : ℝ) : ℂ) * a) by
    simp only [map_mul, Complex.conj_ofReal] ]
  rw [hspec _ ha, map_mul, Complex.conj_ofReal]

lemma virPhaseFactor_saddle_one : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), a < 0 →
    virPhaseFactor (√(-a) : ℂ) (a : ℂ) = 1 ∧ virPhaseFactor (-(√(-a) : ℂ)) (a : ℂ) = 1 := by
  have hts : Tendsto (fun a : ℝ => (√(max (-a) 0) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous fun a : ℝ => (√(max (-a) 0) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_neg.max continuous_const).sqrt)
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hta : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto
  have hpair : Tendsto (fun a : ℝ => ((√(max (-a) 0) : ℂ), (a : ℂ))) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    hts.prodMk_nhds hta
  have hV_real_to_0 : Tendsto (fun a : ℝ => √(max (virBetaOfA (a : ℂ)).re 0)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hcr : ContinuousAt (fun a : ℝ => (virBetaOfA (a : ℂ)).re) (0 : ℝ) :=
      Complex.continuous_re.continuousAt.comp
        (contDiffAt_virBetaOfA.continuousAt.comp_of_eq
          (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))) Complex.ofReal_zero)
    have hcm : ContinuousAt (fun a : ℝ => √(max (virBetaOfA (a : ℂ)).re 0)) (0 : ℝ) :=
      Real.continuous_sqrt.continuousAt.comp (hcr.max continuousAt_const)
    simpa [virBetaOfA_zero] using hcm.tendsto
  have hy_v0_lt : ∀ᶠ v : ℝ in 𝓝 (0 : ℝ), (yVirC (v : ℂ)).re < psiBase.yTout := by
    have hc_y : ContinuousAt (fun v : ℝ => (yVirC (v : ℂ)).re) 0 := by
      have h1 := ((differentiableOn_yVirC 0 (by simp)).differentiableAt
        (isOpen_virStrip.mem_nhds (by simp))).continuousAt.comp_of_eq
        (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))) Complex.ofReal_zero
      exact Complex.continuous_re.continuousAt.comp h1
    have h0 : (yVirC ((0 : ℝ) : ℂ)).re < psiBase.yTout := by
      rw [Complex.ofReal_zero, yVirC_zero, Complex.zero_re]
      exact psiBase.hyTout_pos
    exact hc_y.eventually (isOpen_Iio.mem_nhds h0)
  have htau_lt : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), -a / ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) < chartParams.r_ψ := by
    have h0 : -(0 : ℝ) / ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) < chartParams.r_ψ := by
      simpa using chartParams.hrψ_pos
    have hc : ContinuousAt (fun a : ℝ => -a / ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)) 0 := by fun_prop
    exact hc.eventually (isOpen_Iio.mem_nhds h0)
  filter_upwards [virV_saddle_real, virMGeo_saddle_one, hV_real_to_0.eventually virThetaOutC_ofReal_nonneg,
    htau_lt, hta.eventually virPsi_conj_zero, hV_real_to_0.eventually hy_v0_lt] with
    a hsad hmgeo hth hτ_lt hψ_c hy_lt ha0
  obtain ⟨hβ_pos, hV_val, hedge_val, htau_val⟩ := hsad ha0
  obtain ⟨hm_pos, hm_neg⟩ := hmgeo ha0
  have hβ_max : max (virBetaOfA (a : ℂ)).re 0 = (virBetaOfA (a : ℂ)).re := max_eq_left hβ_pos.le
  set v0 : ℝ := √(virBetaOfA (a : ℂ)).re
  have hv0_pos : 0 < v0 := Real.sqrt_pos.mpr hβ_pos
  have hth_v0 : virThetaOutC (v0 : ℂ) = (thetaOut (lowerY (edgeF v0)) : ℂ) := by
    have hth' := hth (Real.sqrt_nonneg _)
    simp only [hβ_max] at hth'
    exact hth'
  have hy_lt_yt : lowerY (edgeF v0) < psiBase.yTout := by
    have hy_c := yVirC_ofReal_nonneg hv0_pos.le
    have hy_re : lowerY (edgeF v0) = (yVirC (v0 : ℂ)).re := by rw [hy_c, Complex.ofReal_re]
    simp only [hβ_max] at hy_lt
    rw [hy_re]
    exact hy_lt
  set x' : ℝ := (virXPrime (a : ℂ)).re
  have hx'_eq : x' = edgeF v0 := by
    dsimp [x']
    rw [← hedge_val, virEdgeFC_ofReal, Complex.ofReal_re]
  have hx'_gt : xiStar < x' := by rw [hx'_eq, ← edgeF_zero]; exact edgeF_strictMonoOn le_rfl hv0_pos.le hv0_pos
  have hτ_eq : tauPhase x' = -a / ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) := htau_val
  have hτ_lt' : tauPhase x' < chartParams.r_ψ := by rwa [hτ_eq]
  obtain ⟨_, hyl, hψ_ph⟩ := chartParams.hψ_phase 0 le_rfl (by norm_num) x' hx'_gt hτ_lt'
  have hy_val_eq : lowerYVal x' = lowerY (edgeF v0) := by rw [hx'_eq]; rfl
  rw [hy_val_eq] at hyl hψ_ph
  have hψ_0_im : (virPsi 0 (a : ℂ)).im = 0 := by
    have hc := hψ_c
    rw [Complex.conj_ofReal] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hψ_0_eq : virPsi 0 (a : ℂ) = (((virPsi 0 (a : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hψ_0_im
  have hs0_psi_re : √(-a) * (virPsi 0 (a : ℂ)).re =
      2 * betaTip ^ (3 / 2 : ℝ) * √(tauPhase x') *
        (virasoroPsiEps 0 ((-(tauPhase x') : ℝ) : ℂ)).re := by
    have htau_pos : 0 < tauPhase x' := by rw [hτ_eq]; exact div_pos (neg_pos.mpr ha0) virPsi_scale_pos
    have ha_eq : -a = ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) * tauPhase x' := by
      rw [hτ_eq]; field_simp [betaTip_pos.ne']
    have hs0_eq : √(-a) = (2 : ℝ) ^ (1 / 3 : ℝ) * √betaTip * √(tauPhase x') := by
      rw [ha_eq, Real.sqrt_mul (mul_nonneg (Real.rpow_nonneg zero_le_two _) betaTip_pos.le),
        Real.sqrt_mul (Real.rpow_nonneg zero_le_two _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul zero_le_two]
      norm_num
    have hpsi_re : (virPsi 0 (a : ℂ)).re =
        ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) * (virasoroPsiEps 0 ((-(tauPhase x') : ℝ) : ℂ)).re := by
      unfold virPsi
      rw [Real.zero_rpow (by norm_num)]
      have harg : ((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * (a : ℂ) =
          ((-(tauPhase x') : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hτ_eq]; congr 1
        field_simp [betaTip_pos.ne']
      rw [harg, Complex.re_ofReal_mul]
    rw [hs0_eq, hpsi_re]
    have h2pow : (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) = 2 := by
      rw [← Real.rpow_add zero_lt_two]; norm_num
    have hbt : √betaTip * betaTip = betaTip ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      conv_lhs => rhs; rw [← Real.rpow_one betaTip]
      rw [← Real.rpow_add betaTip_pos]; norm_num
    calc ((2 : ℝ) ^ (1 / 3 : ℝ) * √betaTip * √(tauPhase x')) *
          (((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) * (virasoroPsiEps 0 ((-(tauPhase x') : ℝ) : ℂ)).re)
        = ((2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ)) * (√betaTip * betaTip) *
            √(tauPhase x') * (virasoroPsiEps 0 ((-(tauPhase x') : ℝ) : ℂ)).re := by ring
      _ = 2 * betaTip ^ (3 / 2 : ℝ) * √(tauPhase x') * (virasoroPsiEps 0 ((-(tauPhase x') : ℝ) : ℂ)).re := by
          rw [h2pow, hbt]
  have harg_1 : Complex.arg ((1 + ((0 : ℝ) : ℂ)) * (1 + (Complex.I * (lowerY (edgeF v0) : ℂ)) ^ 2) /
      (1 + (Complex.I * (lowerY (edgeF v0) : ℂ)) ^ 2 + ((0 : ℝ) : ℂ) * (1 + Complex.I * (lowerY (edgeF v0) : ℂ)))) = 0 := by
    have hden_ne : (1 + (Complex.I * (lowerY (edgeF v0) : ℂ)) ^ 2) ≠ 0 := by
      have hy2 : lowerY (edgeF v0) ^ 2 < 1 := by nlinarith [hyl.1, hyl.2]
      have he : 1 + (Complex.I * (lowerY (edgeF v0) : ℂ)) ^ 2 = ((1 - lowerY (edgeF v0) ^ 2 : ℝ) : ℂ) := by
        rw [mul_pow, Complex.I_sq]; push_cast; ring
      rw [he]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have he1 : (1 + ((0 : ℝ) : ℂ)) * (1 + (Complex.I * (lowerY (edgeF v0) : ℂ)) ^ 2) /
        (1 + (Complex.I * (lowerY (edgeF v0) : ℂ)) ^ 2 + ((0 : ℝ) : ℂ) * (1 + Complex.I * (lowerY (edgeF v0) : ℂ))) = 1 := by
      rw [Complex.ofReal_zero, add_zero, zero_mul, add_zero, one_mul, div_self hden_ne]
    rw [he1, Complex.arg_one]
  have hth_lt : |thetaOut (lowerY (edgeF v0))| < π :=
    (psiBase.hTout_real (lowerY (edgeF v0)) hyl.1 hy_lt_yt).2
  have harg_gout : Complex.arg (Gout (Complex.I * (lowerY (edgeF v0) : ℂ))) = thetaOut (lowerY (edgeF v0)) := by
    have hW_pos : 0 < Wslit (lowerY (edgeF v0)) := by
      have hy0 := hyl.1; have hy1 := hyl.2
      have hxOf_pos := xOf_pos hyl
      have h1 : 0 < 1 - lowerY (edgeF v0) ^ 2 := by nlinarith
      have h2 : 0 < 1 + 6 * lowerY (edgeF v0) ^ 2 + lowerY (edgeF v0) ^ 4 := by positivity
      have h3 : 0 < 1 - Real.exp (-(4 * π * xOf (lowerY (edgeF v0)))) := by
        rw [sub_pos, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, hxOf_pos])
      have h4 : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
        rw [sub_pos, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, xiStar_pos])
      have hsq1 : 0 < √(xOf (lowerY (edgeF v0)) / xiStar) := Real.sqrt_pos.mpr (div_pos hxOf_pos xiStar_pos)
      have hsq2 : 0 < ((1 - Real.exp (-(4 * π * xOf (lowerY (edgeF v0))))) /
          (1 - Real.exp (-(4 * π * xiStar)))) ^ 2 := sq_pos_of_pos (div_pos h3 h4)
      have hsq3 : 0 < √(1 + 6 * lowerY (edgeF v0) ^ 2 + lowerY (edgeF v0) ^ 4) := Real.sqrt_pos.mpr h2
      unfold Wslit
      exact div_pos (mul_pos hsq1 hsq2) (mul_pos h1 hsq3)
    rw [gout_polar hyl, Complex.arg_real_mul _ hW_pos, mul_comm Complex.I, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨(abs_lt.mp hth_lt).1, (abs_lt.mp hth_lt).2.le⟩
  have hs0_psi_eq : (√(-a) : ℂ) * virPsi 0 (a : ℂ) = (thetaOut (lowerY (edgeF v0)) : ℂ) := by
    rw [hψ_0_eq, ← Complex.ofReal_mul, hs0_psi_re, hψ_ph, harg_gout, harg_1]
    simp only [mul_zero, add_zero]
  have hdiff_pos : virThetaOutC (virV (√(-a) : ℂ) (a : ℂ)) - (√(-a) : ℂ) * virPsi 0 (a : ℂ) = 0 := by
    rw [hV_val, hth_v0, hs0_psi_eq, sub_self]
  have hpos : virPhaseFactor (√(-a) : ℂ) (a : ℂ) = 1 := by
    unfold virPhaseFactor
    rw [hm_pos, hdiff_pos, mul_zero, Complex.exp_zero, mul_one]
  have hneg : virPhaseFactor (-(√(-a) : ℂ)) (a : ℂ) = 1 := by
    unfold virPhaseFactor
    rw [hm_neg, virV_neg, hV_val, virThetaOutC_neg, neg_mul, hth_v0, hs0_psi_eq,
      sub_self, mul_zero, Complex.exp_zero, mul_one]
  exact ⟨hpos, hneg⟩

/-! ### 2. Polydisc packaging: `virRad`, `virQ`, `virEb`, `virasoroHalfCubic`, and `virasoroHalfCubicAux` -/

private lemma lowerMt_sq_sub_one_bound {ε : ℝ} {w : ℂ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 4)
    (hw : ‖w‖ ≤ 1 / 4) :
    ‖lowerMt ε w ^ 2 - 1‖ ≤ (3 / 2 : ℝ) * ε := by
  have hden_lb : (5 / 8 : ℝ) ≤ ‖1 + w ^ 2 + (ε : ℂ) * (1 + w)‖ := by
    have h1 : ‖(ε : ℂ) * (1 + w)‖ ≤ ε * (5 / 4) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
      exact mul_le_mul_of_nonneg_left ((norm_add_le 1 w).trans (by norm_num; linarith)) hε0
    have h2 : ‖1 + w ^ 2‖ ≥ 1 - 1 / 16 := by
      have hsq : ‖w ^ 2‖ ≤ 1 / 16 := by rw [norm_pow]; nlinarith [norm_nonneg w]
      have htri := norm_sub_norm_le (1 : ℂ) (-w ^ 2)
      rw [show (1 : ℂ) - (-w ^ 2) = 1 + w ^ 2 by ring, norm_neg, norm_one] at htri
      linarith
    have hsub := norm_sub_norm_le (1 + w ^ 2) (-((ε : ℂ) * (1 + w)))
    rw [show (1 + w ^ 2) - (-((ε : ℂ) * (1 + w))) = 1 + w ^ 2 + (ε : ℂ) * (1 + w) by ring, norm_neg] at hsub
    linarith
  have hden_ne : 1 + w ^ 2 + (ε : ℂ) * (1 + w) ≠ 0 :=
    norm_ne_zero_iff.mp (by linarith)
  have hdiff : lowerMt ε w - 1 = (ε : ℂ) * (w ^ 2 - w) / (1 + w ^ 2 + (ε : ℂ) * (1 + w)) := by
    unfold lowerMt
    field_simp [hden_ne]
    ring
  have hdiff_bd : ‖lowerMt ε w - 1‖ ≤ ε / 2 := by
    rw [hdiff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
    have hnum : ‖w ^ 2 - w‖ ≤ 5 / 16 := by
      calc ‖w ^ 2 - w‖ ≤ ‖w ^ 2‖ + ‖w‖ := norm_sub_le _ _
        _ = ‖w‖ ^ 2 + ‖w‖ := by rw [norm_pow]
        _ ≤ (1 / 4) ^ 2 + 1 / 4 := by gcongr
        _ = 5 / 16 := by norm_num
    calc ε * ‖w ^ 2 - w‖ / ‖1 + w ^ 2 + (ε : ℂ) * (1 + w)‖
        ≤ ε * (5 / 16) / (5 / 8) := div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left hnum hε0) (by norm_num) hden_lb
      _ = ε / 2 := by ring
  have hsum_bd : ‖lowerMt ε w + 1‖ ≤ 3 := by
    calc ‖lowerMt ε w + 1‖ = ‖(lowerMt ε w - 1) + 2‖ := by ring_nf
      _ ≤ ‖lowerMt ε w - 1‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ ε / 2 + 2 := by simpa using add_le_add_right hdiff_bd 2
      _ ≤ 3 := by linarith
  calc ‖lowerMt ε w ^ 2 - 1‖ = ‖(lowerMt ε w - 1) * (lowerMt ε w + 1)‖ := by ring_nf
    _ = ‖lowerMt ε w - 1‖ * ‖lowerMt ε w + 1‖ := norm_mul _ _
    _ ≤ (ε / 2) * 3 := mul_le_mul hdiff_bd hsum_bd (norm_nonneg _) (by positivity)
    _ = (3 / 2 : ℝ) * ε := by ring

private structure VirBallSpec where
  r_s : ℝ
  r_a : ℝ
  M_Y : ℝ
  M_ψ' : ℝ
  C_psi_diff : ℝ
  M_G0 : ℝ
  K_b : ℝ
  M_aux : ℝ
  R3 : ℝ
  hrs_pos : 0 < r_s
  hra_pos : 0 < r_a
  hR3_pos : 0 < R3
  hMY_nn : 0 ≤ M_Y
  hMψ'_nn : 0 ≤ M_ψ'
  hCpd_nn : 0 ≤ C_psi_diff
  hMG0_nn : 0 ≤ M_G0
  hKb_nn : 0 ≤ K_b
  hMaux_nn : 0 ≤ M_aux
  hs_le_one : r_s ≤ 1
  ha_le_R3 : r_a ≤ R3
  ha_le_psi : r_a ≤ min ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.ρ_ψ / 2)
    ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.r_ψ / 2)
  hM_G0_def : M_G0 = 2 * Real.exp (1 + 1 * M_ψ')
  hMψ'_def : M_ψ' = (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.M_ψ
  hCpd_def : C_psi_diff = M_Y / (2 * betaTip ^ (3 / 2 : ℝ)) * ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) * (32 / 3)
  hKb_def : K_b = 3 / 2 + 2 * (Real.exp (2 * M_ψ') + 2) * C_psi_diff
  ha_in : ∀ {a : ℂ}, a ∈ ball (0 : ℂ) r_a →
    (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a) ∈ closedBall (0 : ℂ) chartParams.r_ψ ∧
    (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a) ∈ ball (0 : ℂ) chartParams.ρ_ψ ∧
    ‖-((((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a)) *
      psiBase.Y0 (-(((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a))‖ ≤ 1 / 16 ∧
    ‖(psiBase.Y0 (-(((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a))) ^ ((1 / 2 : ℝ) : ℂ)‖ ≤ M_Y
  hV_an : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a →
    ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virV q.1 q.2) (ζ, a)
  hMG_an : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a →
    ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virMGeo q.1 q.2) (ζ, a)
  hV_bd : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → ‖virV ζ a‖ < 1 / 4
  hMG_bd : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → ‖virMGeo ζ a‖ ≤ 2
  hY_bd : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → ‖yVirC (virV ζ a)‖ < 1 / 4
  hVim : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → |(virV ζ a).im| < 1 / 2
  hT_an : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → AnalyticAt ℂ virThetaOutC (virV ζ a)
  hY_an : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → AnalyticAt ℂ yVirC (virV ζ a)
  hT_bd : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → ‖virThetaOutC (virV ζ a)‖ ≤ 1
  hV_conj : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a →
    virV (starRingEnd ℂ ζ) (starRingEnd ℂ a) = starRingEnd ℂ (virV ζ a)
  hMG_conj : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a →
    virMGeo (starRingEnd ℂ ζ) (starRingEnd ℂ a) = starRingEnd ℂ (virMGeo ζ a)
  hMG_neg : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a → virMGeo (-ζ) a = virMGeo ζ a
  hT_conj : ∀ {ζ a : ℂ}, ζ ∈ ball 0 r_s → a ∈ ball 0 r_a →
    virThetaOutC (starRingEnd ℂ (virV ζ a)) = starRingEnd ℂ (virThetaOutC (virV ζ a))
  hSaddle : ∀ a ∈ ball (0 : ℝ) R3, a < 0 →
    virPhaseFactor (√(-a) : ℂ) (a : ℂ) = 1 ∧ virPhaseFactor (-(√(-a) : ℂ)) (a : ℂ) = 1

private lemma exists_virBallSpec : Nonempty VirBallSpec := by
  let K : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip
  have hK : 0 < K := virPsi_scale_pos
  have hV_an : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)), ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virV q.1 q.2) p :=
    contDiffAt2_virV
  have hMG_an : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)), ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virMGeo q.1 q.2) p :=
    (contDiffAt_virMGeo.of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞')).eventually (by simp : (2 : WithTop ℕ∞) ≠ ∞')
  have hρψ_pos : 0 < chartParams.ρ_ψ := lt_trans chartParams.hrψ_pos chartParams.hrψ_lt
  have hV_norm : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)), ‖virV p.1 p.2‖ < 1 / 4 := by
    have ht : ‖virV ((0 : ℂ), (0 : ℂ)).1 ((0 : ℂ), (0 : ℂ)).2‖ < 1 / 4 := by
      dsimp; rw [virV_zero_zero, norm_zero]; norm_num
    exact contDiffAt_virV.continuousAt.norm.eventually (isOpen_Iio.mem_nhds ht)
  have hY_norm : ∀ᶠ v : ℂ in 𝓝 (0 : ℂ), ‖yVirC v‖ < 1 / 4 ∧ |v.im| < 1 / 2 := by
    have hc1 : ContinuousAt (fun v : ℂ => ‖yVirC v‖) 0 :=
      (((differentiableOn_yVirC 0 (by simp)).differentiableAt (isOpen_virStrip.mem_nhds (by simp))).continuousAt).norm
    have ht : ‖yVirC 0‖ < 1 / 4 := by rw [yVirC_zero, norm_zero]; norm_num
    exact (hc1.eventually (isOpen_Iio.mem_nhds ht)).and (isOpen_virStrip.mem_nhds (by simp))
  have hT_an : ∀ᶠ v : ℂ in 𝓝 (0 : ℂ), AnalyticAt ℂ virThetaOutC v := virThetaOutC_analyticAt.eventually_analyticAt
  have hY_an : ∀ᶠ v : ℂ in 𝓝 (0 : ℂ), AnalyticAt ℂ yVirC v :=
    (analyticOnNhd_yVirC 0 (by simp)).eventually_analyticAt
  have hT_0 : ContinuousAt virThetaOutC 0 := virThetaOutC_analyticAt.continuousAt
  have hTM_arg_small : ∀ᶠ w : ℂ in 𝓝 (0 : ℂ),
      -w ∈ ball (0 : ℂ) psiBase.rY ∧ ‖-w * psiBase.Y0 (-w)‖ ≤ 1 / 16 ∧
      ‖(psiBase.Y0 (-w)) ^ ((1 / 2 : ℝ) : ℂ)‖ ≤ ‖(psiBase.Y0 0) ^ ((1 / 2 : ℝ) : ℂ)‖ + 1 := by
    have hc_neg : Tendsto (fun w : ℂ => -w) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto
    have hY0c : ContinuousAt psiBase.Y0 0 :=
      ((psiBase.hY0_diff 0 (mem_ball_self psiBase.hrY_pos)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self psiBase.hrY_pos))).continuousAt
    have hsp : psiBase.Y0 0 ∈ Complex.slitPlane := (psiBase.hY0_pos 0 (mem_ball_self psiBase.hrY_pos)).2
    have hc_Y : ContinuousAt (fun w : ℂ => (psiBase.Y0 (-w)) ^ ((1 / 2 : ℝ) : ℂ)) 0 :=
      (analyticAt_id.cpow analyticAt_const hsp).continuousAt.comp_of_eq
        (hY0c.comp_of_eq (continuous_neg.continuousAt (x := (0 : ℂ))) neg_zero) (by rw [neg_zero])
    have harg_c : Tendsto (fun w : ℂ => -w * psiBase.Y0 (-w)) (𝓝 0) (𝓝 0) := by
      have hc : ContinuousAt (fun w : ℂ => -w * psiBase.Y0 (-w)) 0 :=
        (continuous_neg.continuousAt (x := (0 : ℂ))).mul
          (hY0c.comp_of_eq (continuous_neg.continuousAt (x := (0 : ℂ))) neg_zero)
      simpa using hc.tendsto
    have h1 := hc_neg.eventually (Metric.ball_mem_nhds (0 : ℂ) psiBase.hrY_pos)
    have h2 := harg_c.eventually (Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 16))
    have h3 : ∀ᶠ w : ℂ in 𝓝 0, dist ((psiBase.Y0 (-w)) ^ ((1 / 2 : ℝ) : ℂ))
        ((psiBase.Y0 0) ^ ((1 / 2 : ℝ) : ℂ)) ≤ 1 := by
      have hb : closedBall ((psiBase.Y0 0) ^ ((1 / 2 : ℝ) : ℂ)) 1 ∈
          𝓝 ((psiBase.Y0 (-0)) ^ ((1 / 2 : ℝ) : ℂ)) := by
        rw [neg_zero]; exact Metric.closedBall_mem_nhds _ zero_lt_one
      exact hc_Y.tendsto.eventually hb
    filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
    refine ⟨hw1, by simpa [Metric.mem_closedBall, dist_zero_right] using hw2, ?_⟩
    have htri := norm_sub_norm_le ((psiBase.Y0 (-w)) ^ ((1 / 2 : ℝ) : ℂ)) ((psiBase.Y0 0) ^ ((1 / 2 : ℝ) : ℂ))
    rw [← dist_eq_norm] at htri
    linarith
  have hMG_bd : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)), ‖virMGeo p.1 p.2‖ ≤ 2 := by
    have hb : closedBall (1 : ℂ) 1 ∈ 𝓝 (virMGeo (0 : ℂ) (0 : ℂ)) := by
      rw [virMGeo_zero_zero]; exact Metric.closedBall_mem_nhds 1 zero_lt_one
    filter_upwards [contDiffAt_virMGeo.continuousAt.tendsto.eventually hb] with p hp
    have hdist : dist (virMGeo p.1 p.2) 1 ≤ 1 := by simpa [Metric.mem_closedBall] using hp
    have htri := norm_sub_norm_le (virMGeo p.1 p.2) (1 : ℂ)
    rw [← dist_eq_norm, norm_one] at htri
    linarith
  have hV_tend : Tendsto (fun p : ℂ × ℂ => virV p.1 p.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := by
    simpa [virV_zero_zero] using contDiffAt_virV.continuousAt.tendsto
  have hTh_bd : ∀ᶠ v : ℂ in 𝓝 0, ‖virThetaOutC v‖ ≤ 1 := by
    have hv0 : virThetaOutC 0 = 0 := by unfold virThetaOutC; rw [yVirC_zero, zero_mul]
    have hb : closedBall (0 : ℂ) 1 ∈ 𝓝 (virThetaOutC 0) := by
      rw [hv0]; exact Metric.closedBall_mem_nhds 0 zero_lt_one
    filter_upwards [hT_0.tendsto.eventually hb] with v hv
    simpa [Metric.mem_closedBall, dist_zero_right] using hv
  have hV_prop := ((hV_an.and hMG_an).and (hV_norm.and hMG_bd)).and
    ((virV_conj.and virMGeo_conj).and (virMGeo_neg.and
      (hV_tend.eventually ((hY_norm.and hT_an).and (hY_an.and (virThetaOutC_conj.and hTh_bd))))))
  obtain ⟨R1, hR1, hBall1⟩ := Metric.eventually_nhds_iff_ball.mp hV_prop
  obtain ⟨R2, hR2, hBall2⟩ := Metric.eventually_nhds_iff_ball.mp hTM_arg_small
  obtain ⟨R3, hR3, hBall3⟩ := Metric.eventually_nhds_iff_ball.mp virPhaseFactor_saddle_one
  let r_s : ℝ := min (R1 / 2) 1
  let r_a : ℝ := min (R1 / 2) (min (K * chartParams.ρ_ψ / 2)
    (min (K * chartParams.r_ψ / 2) (min (K * R2 / 2) (min R3 1))))
  have hrs_pos : 0 < r_s := lt_min (half_pos hR1) one_pos
  have hra_pos : 0 < r_a := lt_min (half_pos hR1) (lt_min (div_pos (mul_pos hK hρψ_pos) zero_lt_two)
    (lt_min (div_pos (mul_pos hK chartParams.hrψ_pos) zero_lt_two)
      (lt_min (div_pos (mul_pos hK hR2) zero_lt_two) (lt_min hR3 one_pos))))
  let M_Y : ℝ := ‖(psiBase.Y0 0) ^ ((1 / 2 : ℝ) : ℂ)‖ + 1
  let C_psi_diff : ℝ := M_Y / (2 * betaTip ^ (3 / 2 : ℝ)) * K * (32 / 3)
  let M_ψ' : ℝ := K * chartParams.M_ψ
  let M_G0 : ℝ := 2 * Real.exp (1 + 1 * M_ψ')
  let K_b : ℝ := 3 / 2 + 2 * (Real.exp (2 * M_ψ') + 2) * C_psi_diff
  let M_aux : ℝ := M_G0 * 2 * (1 + K_b)
  have hMY_nn : 0 ≤ M_Y := by positivity
  have hCpd_nn : 0 ≤ C_psi_diff := by have := betaTip_pos; positivity
  have hMψ'_nn : 0 ≤ M_ψ' := mul_nonneg hK.le chartParams.hMψ_nn
  have hMG0_nn : 0 ≤ M_G0 := by positivity
  have hKb_nn : 0 ≤ K_b := by positivity
  have hMaux_nn : 0 ≤ M_aux := by positivity
  have hpair_mem : ∀ {ζ a : ℂ}, ζ ∈ ball (0 : ℂ) r_s → a ∈ ball (0 : ℂ) r_a →
      (ζ, a) ∈ ball ((0 : ℂ), (0 : ℂ)) R1 := fun {ζ a} hζ ha => by
    rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]
    rw [Metric.mem_ball, dist_zero_right] at hζ ha
    exact max_lt (hζ.trans_le ((min_le_left _ _).trans (half_lt_self hR1).le))
      (ha.trans_le ((min_le_left _ _).trans (half_lt_self hR1).le))
  refine ⟨⟨r_s, r_a, M_Y, M_ψ', C_psi_diff, M_G0, K_b, M_aux, R3,
    hrs_pos, hra_pos, hR3, hMY_nn, hMψ'_nn, hCpd_nn, hMG0_nn, hKb_nn, hMaux_nn,
    min_le_right _ _,
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))),
    (min_le_right _ _).trans (le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))),
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hBall3⟩⟩
  · intro a ha
    rw [Metric.mem_ball, dist_zero_right] at ha
    have ha_norm : ‖(((K⁻¹ : ℝ) : ℂ) * a)‖ = K⁻¹ * ‖a‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK)]
    have h1 : (((K⁻¹ : ℝ) : ℂ) * a) ∈ closedBall (0 : ℂ) chartParams.r_ψ := by
      rw [Metric.mem_closedBall, dist_zero_right, ha_norm]
      have hle : ‖a‖ ≤ K * chartParams.r_ψ / 2 :=
        ha.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      have h2 := mul_le_mul_of_nonneg_left hle (inv_pos.mpr hK).le
      rw [show K⁻¹ * (K * chartParams.r_ψ / 2) = chartParams.r_ψ / 2 by field_simp [hK.ne'] ] at h2
      linarith [chartParams.hrψ_pos]
    have h2 : (((K⁻¹ : ℝ) : ℂ) * a) ∈ ball (0 : ℂ) chartParams.ρ_ψ := by
      rw [Metric.mem_ball, dist_zero_right, ha_norm]
      have hlt : ‖a‖ < K * chartParams.ρ_ψ / 2 :=
        ha.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have h3 := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hK)
      rw [show K⁻¹ * (K * chartParams.ρ_ψ / 2) = chartParams.ρ_ψ / 2 by field_simp [hK.ne'] ] at h3
      linarith [hρψ_pos]
    have h3 : (((K⁻¹ : ℝ) : ℂ) * a) ∈ ball (0 : ℂ) R2 := by
      rw [Metric.mem_ball, dist_zero_right, ha_norm]
      have hlt : ‖a‖ < K * R2 / 2 :=
        ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
      have h4 := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hK)
      rw [show K⁻¹ * (K * R2 / 2) = R2 / 2 by field_simp [hK.ne'] ] at h4
      linarith
    obtain ⟨-, hw_arg, hw_Y⟩ := hBall2 _ h3
    exact ⟨h1, h2, hw_arg, hw_Y⟩
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).1.1.1
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).1.1.2
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).1.2.1
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).1.2.2
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.2.2.1.1.1
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.2.2.1.1.2
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.2.2.1.2
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.2.2.2.1
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.2.2.2.2.2
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.1.1
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.1.2
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.2.1
  · intro ζ a hζ ha; exact (hBall1 (ζ, a) (hpair_mem hζ ha)).2.2.2.2.2.1

private lemma virPsi_diff_0 (b : VirBallSpec) : DifferentiableOn ℂ (virPsi 0) (ball 0 b.r_a) := fun a ha => by
  have hspec := (chartParams.hψ_spec 0 le_rfl (by norm_num)).1
  have hd : DifferentiableAt ℂ (virasoroPsiEps 0)
      ((((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a)) :=
    hspec.differentiableAt (isOpen_ball.mem_nhds (b.ha_in ha).2.1)
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => (((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip : ℝ) : ℂ) *
      virasoroPsiEps 0 (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * z)) a :=
    (hd.comp a ((differentiableAt_const _).mul differentiableAt_id)).const_mul _
  have heq : virPsi 0 = fun z => (((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip : ℝ) : ℂ) *
      virasoroPsiEps 0 (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * z) := by
    ext z; unfold virPsi; rw [Real.zero_rpow (by norm_num)]
  exact (heq ▸ hcomp).differentiableWithinAt

private lemma virPsi_bd_n (b : VirBallSpec) {n : ℝ} (hε0 : 0 ≤ n ^ (-2 : ℝ)) (hε1 : n ^ (-2 : ℝ) ≤ 1 / 4)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) b.r_a) : ‖virPsi n a‖ ≤ b.M_ψ' := by
  have hK := virPsi_scale_pos
  have hspec := (chartParams.hψ_spec _ hε0 hε1).2.2.1
  unfold virPsi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK, b.hMψ'_def]
  exact mul_le_mul_of_nonneg_left (hspec _ (b.ha_in ha).1).1 hK.le

private lemma virPsi_bd_0 (b : VirBallSpec) {a : ℂ} (ha : a ∈ ball (0 : ℂ) b.r_a) :
    ‖virPsi 0 a‖ ≤ b.M_ψ' := by
  have hK := virPsi_scale_pos
  have hspec := (chartParams.hψ_spec 0 le_rfl (by norm_num)).2.2.1
  unfold virPsi
  rw [Real.zero_rpow (by norm_num), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK, b.hMψ'_def]
  exact mul_le_mul_of_nonneg_left (hspec _ (b.ha_in ha).1).1 hK.le

private lemma virPsi_diff_le (b : VirBallSpec) (n : ℝ) (hn : 2 ≤ n)
    (a : ℂ) (ha : a ∈ ball (0 : ℂ) b.r_a) :
    ‖virPsi n a - virPsi 0 a‖ ≤ b.C_psi_diff * n ^ (-2 : ℝ) := by
  have hK := virPsi_scale_pos
  have hε0 : 0 ≤ n ^ (-2 : ℝ) := by positivity
  have hε1 : n ^ (-2 : ℝ) ≤ 1 / 4 := inv_sq_le_quarter hn
  set w : ℂ := (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a)
  obtain ⟨-, -, hw_arg, hw_Y⟩ := b.ha_in ha
  have hTM0_spec := Classical.choose_spec (virasoro_TM_exists 0 le_rfl (by norm_num))
  have hTMn_spec := Classical.choose_spec (virasoro_TM_exists (n ^ (-2 : ℝ)) hε0 hε1)
  have hTM0_0 : virasoroTM 0 (-w * psiBase.Y0 (-w)) = 0 := by
    unfold virasoroTM
    simp only [le_rfl, (by norm_num : (0 : ℝ) ≤ 1 / 4), and_self, ↓reduceDIte]
    have hb := hTM0_spec.2.2.1 (-w * psiBase.Y0 (-w))
      (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hw_arg))
    exact norm_le_zero_iff.mp (hb.trans_eq (mul_zero _))
  have hTMn_bd : ‖virasoroTM (n ^ (-2 : ℝ)) (-w * psiBase.Y0 (-w))‖ ≤ 32 / 3 * n ^ (-2 : ℝ) := by
    unfold virasoroTM
    simp only [hε0, hε1, and_self, ↓reduceDIte]
    exact hTMn_spec.2.2.1 _ (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hw_arg))
  have hsub : virPsi n a - virPsi 0 a = (((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip : ℝ) : ℂ) *
      ((psiBase.Y0 (-w)) ^ ((1 / 2 : ℝ) : ℂ) / ((2 * betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        virasoroTM (n ^ (-2 : ℝ)) (-w * psiBase.Y0 (-w))) := by
    unfold virPsi virasoroPsiEps
    simp only [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0), hε0, hε1, le_rfl, (by norm_num : (0 : ℝ) ≤ 1 / 4),
      and_self, ↓reduceIte]
    rw [show (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a) = w from rfl, hTM0_0, add_zero]
    ring
  rw [hsub, norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hK, abs_of_pos (by have := betaTip_pos; positivity), b.hCpd_def]
  have hbt_pos : 0 < 2 * betaTip ^ (3 / 2 : ℝ) := by have := betaTip_pos; positivity
  have hMY_nn := b.hMY_nn
  calc ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) *
        (‖(psiBase.Y0 (-w)) ^ ((1 / 2 : ℝ) : ℂ)‖ / (2 * betaTip ^ (3 / 2 : ℝ)) *
          ‖virasoroTM (n ^ (-2 : ℝ)) (-w * psiBase.Y0 (-w))‖)
      ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) *
          (b.M_Y / (2 * betaTip ^ (3 / 2 : ℝ)) * (32 / 3 * n ^ (-2 : ℝ))) := by gcongr
    _ = b.M_Y / (2 * betaTip ^ (3 / 2 : ℝ)) * ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) * (32 / 3) * n ^ (-2 : ℝ) := by ring

private lemma virEb_den_ne (b : VirBallSpec) {n : ℝ} (hn2 : 2 ≤ n)
    {ζ a : ℂ} (hζ : ζ ∈ ball 0 b.r_s) (ha : a ∈ ball 0 b.r_a) :
    1 + (Complex.I * yVirC (virV ζ a)) ^ 2 +
      ((n ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * yVirC (virV ζ a)) ≠ 0 := by
  have hε0 : 0 ≤ n ^ (-2 : ℝ) := by positivity
  have hε1 : n ^ (-2 : ℝ) ≤ 1 / 4 := inv_sq_le_quarter hn2
  have hnorm_y : ‖Complex.I * yVirC (virV ζ a)‖ ≤ 1 / 4 := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact (b.hY_bd hζ ha).le
  have h1 : ‖((n ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * yVirC (virV ζ a))‖ ≤ 5 / 16 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
    calc n ^ (-2 : ℝ) * ‖1 + Complex.I * yVirC (virV ζ a)‖
        ≤ (1 / 4) * (1 + 1 / 4) := mul_le_mul hε1
            ((norm_add_le 1 _).trans (by simpa using add_le_add_left hnorm_y 1)) (norm_nonneg _) (by norm_num)
      _ = 5 / 16 := by norm_num
  have h2 : ‖1 + (Complex.I * yVirC (virV ζ a)) ^ 2‖ ≥ 15 / 16 := by
    have hsq : ‖(Complex.I * yVirC (virV ζ a)) ^ 2‖ ≤ 1 / 16 := by
      rw [norm_pow]; nlinarith [norm_nonneg (Complex.I * yVirC (virV ζ a))]
    have htri := norm_sub_norm_le (1 : ℂ) (-((Complex.I * yVirC (virV ζ a)) ^ 2))
    rw [show (1 : ℂ) - -((Complex.I * yVirC (virV ζ a)) ^ 2) = 1 + (Complex.I * yVirC (virV ζ a)) ^ 2 by ring,
      norm_neg, norm_one] at htri
    linarith
  have hsub := norm_sub_norm_le (1 + (Complex.I * yVirC (virV ζ a)) ^ 2)
    (-(((n ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * yVirC (virV ζ a))))
  rw [show (1 + (Complex.I * yVirC (virV ζ a)) ^ 2) -
      (-(((n ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * yVirC (virV ζ a)))) =
      1 + (Complex.I * yVirC (virV ζ a)) ^ 2 +
        ((n ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * yVirC (virV ζ a)) by ring, norm_neg] at hsub
  exact norm_ne_zero_iff.mp (by linarith)

private lemma virEb_sub_one_le (b : VirBallSpec) {n : ℝ} (hn : 1 ≤ n)
    {ζ a : ℂ} (hζ : ζ ∈ ball 0 b.r_s) (ha : a ∈ ball 0 b.r_a) :
    ‖virEb n ζ a - 1‖ ≤ b.K_b * n⁻¹ := by
  by_cases hn2 : 2 ≤ n
  · have hε0 : 0 ≤ n ^ (-2 : ℝ) := by positivity
    have hε1 : n ^ (-2 : ℝ) ≤ 1 / 4 := inv_sq_le_quarter hn2
    have hε_inv : n ^ (-2 : ℝ) ≤ n⁻¹ := by
      rw [← Real.rpow_neg_one n]
      exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    have hw_y : ‖Complex.I * yVirC (virV ζ a)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact (b.hY_bd hζ ha).le
    have hmt := lowerMt_sq_sub_one_bound hε0 hε1 hw_y
    have hmt_bd : ‖lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2‖ ≤ 2 := by
      calc ‖lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2‖
          = ‖(lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2 - 1) + 1‖ := by ring_nf
        _ ≤ ‖lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2 - 1‖ + ‖(1 : ℂ)‖ :=
            norm_add_le _ (1 : ℂ)
        _ ≤ 3 / 2 * n ^ (-2 : ℝ) + 1 := by rw [norm_one]; linarith
        _ ≤ 3 / 2 * (1 / 4) + 1 := by linarith
        _ ≤ 2 := by norm_num
    have hζ_le : ‖ζ‖ ≤ 1 := (mem_ball_zero_iff.mp hζ).le.trans b.hs_le_one
    have harg_bd : ‖-Complex.I * ζ * (virPsi n a - virPsi 0 a)‖ ≤ b.C_psi_diff * n ^ (-2 : ℝ) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
      simpa using mul_le_mul hζ_le (virPsi_diff_le b n hn2 a ha) (norm_nonneg _) (by positivity)
    have harg_M : ‖-Complex.I * ζ * (virPsi n a - virPsi 0 a)‖ ≤ 2 * b.M_ψ' := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
      calc ‖ζ‖ * ‖virPsi n a - virPsi 0 a‖
          ≤ 1 * (‖virPsi n a‖ + ‖virPsi 0 a‖) :=
            mul_le_mul hζ_le (norm_sub_le _ _) (norm_nonneg _) zero_le_one
        _ ≤ 1 * (b.M_ψ' + b.M_ψ') := by gcongr; exact virPsi_bd_n b hε0 hε1 ha; exact virPsi_bd_0 b ha
        _ = 2 * b.M_ψ' := by ring
    have hexp_sub : ‖Complex.exp (-Complex.I * ζ * (virPsi n a - virPsi 0 a)) - 1‖ ≤
        (Real.exp (2 * b.M_ψ') + 2) * (b.C_psi_diff * n ^ (-2 : ℝ)) := by
      set z := -Complex.I * ζ * (virPsi n a - virPsi 0 a)
      have hle : ‖Complex.exp z - 1‖ ≤ (Real.exp (2 * b.M_ψ') + 2) * ‖z‖ := by
        by_cases hz1 : ‖z‖ ≤ 1
        · have h2 : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hz1
          have hexp_nn : 0 ≤ Real.exp (2 * b.M_ψ') := (Real.exp_pos _).le
          nlinarith [norm_nonneg z]
        · push Not at hz1
          have h1 := Real.exp_le_exp.mpr (Complex.re_le_norm z)
          have h2 := Real.exp_le_exp.mpr harg_M
          have h3 : ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + 1 := by simpa using norm_sub_le _ (1 : ℂ)
          rw [Complex.norm_exp] at h3
          have htri : ‖Complex.exp z - 1‖ ≤ Real.exp (2 * b.M_ψ') + 1 := by linarith
          have hpos : 0 ≤ Real.exp (2 * b.M_ψ') + 1 := by positivity
          nlinarith [norm_nonneg z]
      exact hle.trans (mul_le_mul_of_nonneg_left harg_bd (by positivity))
    have hev_eq : virEb n ζ a - 1 =
        lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2 *
          (Complex.exp (-Complex.I * ζ * (virPsi n a - virPsi 0 a)) - 1) +
        (lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2 - 1) := by
      unfold virEb; simp only [hn2, ↓reduceIte]; ring
    calc ‖virEb n ζ a - 1‖
        ≤ ‖lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2‖ *
            ‖Complex.exp (-Complex.I * ζ * (virPsi n a - virPsi 0 a)) - 1‖ +
          ‖lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ a)) ^ 2 - 1‖ := by
            rw [hev_eq]; exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ 2 * ((Real.exp (2 * b.M_ψ') + 2) * (b.C_psi_diff * n ^ (-2 : ℝ))) + 3 / 2 * n ^ (-2 : ℝ) := by
          have := b.hMψ'_nn; have := b.hCpd_nn; gcongr
      _ = b.K_b * n ^ (-2 : ℝ) := by rw [b.hKb_def]; ring
      _ ≤ b.K_b * n⁻¹ := by gcongr; exact b.hKb_nn
  · have := b.hKb_nn; unfold virEb; simp [hn2]; positivity

private lemma virV_diff_zeta (b : VirBallSpec) {ζ a : ℂ} (hζ : ζ ∈ ball 0 b.r_s) (ha : a ∈ ball 0 b.r_a) :
    DifferentiableAt ℂ (fun w => virV w a) ζ :=
  ((b.hV_an hζ ha).differentiableAt (by simp)).comp (g := fun q : ℂ × ℂ => virV q.1 q.2)
    (f := fun w : ℂ => (w, a)) ζ (differentiableAt_id.prodMk (differentiableAt_const a))

private lemma virV_diff_a (b : VirBallSpec) {ζ a : ℂ} (hζ : ζ ∈ ball 0 b.r_s) (ha : a ∈ ball 0 b.r_a) :
    DifferentiableAt ℂ (fun w => virV ζ w) a :=
  ((b.hV_an hζ ha).differentiableAt (by simp)).comp (g := fun q : ℂ × ℂ => virV q.1 q.2)
    (f := fun w : ℂ => (ζ, w)) a ((differentiableAt_const ζ).prodMk differentiableAt_id)

private lemma virPhaseFactor_diff_zeta (b : VirBallSpec) :
    ∀ a ∈ ball (0 : ℂ) b.r_a, DifferentiableOn ℂ (fun ζ => virPhaseFactor ζ a) (ball 0 b.r_s) := by
  intro a ha ζ hζ
  have hMG_d : DifferentiableAt ℂ (fun w => virMGeo w a) ζ :=
    ((b.hMG_an hζ ha).differentiableAt (by simp)).comp (g := fun q : ℂ × ℂ => virMGeo q.1 q.2)
      (f := fun w : ℂ => (w, a)) ζ (differentiableAt_id.prodMk (differentiableAt_const a))
  have hTh_d : DifferentiableAt ℂ (fun w => virThetaOutC (virV w a)) ζ :=
    (b.hT_an hζ ha).differentiableAt.comp (g := virThetaOutC) ζ (virV_diff_zeta b hζ ha)
  have hArg_d : DifferentiableAt ℂ (fun w => Complex.I * (virThetaOutC (virV w a) - w * virPsi 0 a)) ζ :=
    (hTh_d.sub (differentiableAt_id.mul_const (virPsi 0 a))).const_mul Complex.I
  exact (hMG_d.mul (Complex.differentiableAt_exp.comp ζ hArg_d)).differentiableWithinAt

private lemma virPhaseFactor_diff_a (b : VirBallSpec) :
    ∀ ζ ∈ ball (0 : ℂ) b.r_s, DifferentiableOn ℂ (virPhaseFactor ζ) (ball 0 b.r_a) := by
  have hPsi_diff_0 := virPsi_diff_0 b
  intro ζ hζ a ha
  have hMG_d : DifferentiableAt ℂ (fun w => virMGeo ζ w) a :=
    ((b.hMG_an hζ ha).differentiableAt (by simp)).comp (g := fun q : ℂ × ℂ => virMGeo q.1 q.2)
      (f := fun w : ℂ => (ζ, w)) a ((differentiableAt_const ζ).prodMk differentiableAt_id)
  have hTh_d : DifferentiableAt ℂ (fun w => virThetaOutC (virV ζ w)) a :=
    (b.hT_an hζ ha).differentiableAt.comp a (virV_diff_a b hζ ha)
  have hPsi_d : DifferentiableAt ℂ (virPsi 0) a := (hPsi_diff_0 a ha).differentiableAt (isOpen_ball.mem_nhds ha)
  have hArg_d : DifferentiableAt ℂ (fun w => Complex.I * (virThetaOutC (virV ζ w) - ζ * virPsi 0 w)) a :=
    (hTh_d.sub (hPsi_d.const_mul ζ)).const_mul Complex.I
  exact (hMG_d.mul (Complex.differentiableAt_exp.comp a hArg_d)).differentiableWithinAt

private lemma virEb_diff_zeta (b : VirBallSpec) :
    ∀ n, 1 ≤ n → ∀ a ∈ ball (0 : ℂ) b.r_a, DifferentiableOn ℂ (fun ζ => virEb n ζ a) (ball 0 b.r_s) := by
  intro n _hn a ha ζ hζ
  by_cases hn2 : 2 ≤ n
  · have hY_d : DifferentiableAt ℂ (fun w => Complex.I * yVirC (virV w a)) ζ :=
      ((b.hY_an hζ ha).differentiableAt.comp (g := yVirC) ζ (virV_diff_zeta b hζ ha)).const_mul Complex.I
    have hnum_d : DifferentiableAt ℂ (fun w => (1 + ((n ^ (-2 : ℝ) : ℝ) : ℂ)) * (1 + (Complex.I * yVirC (virV w a)) ^ 2)) ζ :=
      ((hY_d.pow 2).const_add 1).const_mul _
    have hden_d : DifferentiableAt ℂ (fun w => 1 + (Complex.I * yVirC (virV w a)) ^ 2 +
        ((n ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * yVirC (virV w a))) ζ :=
      ((hY_d.pow 2).const_add 1).add ((hY_d.const_add 1).const_mul _)
    have hmt_d : DifferentiableAt ℂ (fun w => lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV w a)) ^ 2) ζ :=
      (hnum_d.div hden_d (virEb_den_ne b hn2 hζ ha)).pow 2
    have hexp_d : DifferentiableAt ℂ (fun w => Complex.exp (-Complex.I * w * (virPsi n a - virPsi 0 a))) ζ :=
      Complex.differentiableAt_exp.comp ζ
        ((differentiableAt_id.const_mul (-Complex.I)).mul_const (virPsi n a - virPsi 0 a))
    have hev : (fun w => virEb n w a) =ᶠ[𝓝 ζ] fun w =>
        lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV w a)) ^ 2 *
          Complex.exp (-Complex.I * w * (virPsi n a - virPsi 0 a)) := by
      filter_upwards with w; unfold virEb; simp only [hn2, ↓reduceIte]
    exact ((hmt_d.mul hexp_d).congr_of_eventuallyEq hev).differentiableWithinAt
  · have heq : (fun w => virEb n w a) = fun _ => 1 := by ext w; unfold virEb; simp [hn2]
    rw [heq]; exact differentiableWithinAt_const 1

private lemma virEb_diff_a (b : VirBallSpec) :
    ∀ n, 1 ≤ n → ∀ ζ ∈ ball (0 : ℂ) b.r_s, DifferentiableOn ℂ (virEb n ζ) (ball 0 b.r_a) := by
  have hPsi_diff_0 := virPsi_diff_0 b
  have hPsi_diff_n : ∀ n, 1 ≤ n → DifferentiableOn ℂ (virPsi n) (ball 0 b.r_a) := fun n hn => by
    by_cases hn2 : 2 ≤ n
    · have hspec := (chartParams.hψ_spec _ (by positivity) (inv_sq_le_quarter hn2)).1
      intro a ha
      have hd := hspec.differentiableAt (isOpen_ball.mem_nhds (b.ha_in ha).2.1)
      exact ((hd.comp a (differentiableAt_id.const_mul _)).const_mul _).differentiableWithinAt
    · have hε_gt : ¬ (0 ≤ n ^ (-2 : ℝ) ∧ n ^ (-2 : ℝ) ≤ 1 / 4) := not_inv_sq_le_quarter hn hn2
      have hzero : virPsi n = fun _ => 0 := by
        ext a; unfold virPsi virasoroPsiEps; simp only [hε_gt, ↓reduceIte, mul_zero]
      rw [hzero]; exact differentiableOn_const 0
  intro n hn ζ hζ a ha
  by_cases hn2 : 2 ≤ n
  · have hY_d : DifferentiableAt ℂ (fun w => Complex.I * yVirC (virV ζ w)) a :=
      ((b.hY_an hζ ha).differentiableAt.comp (g := yVirC) a (virV_diff_a b hζ ha)).const_mul Complex.I
    have hnum_d : DifferentiableAt ℂ (fun w => (1 + ((n ^ (-2 : ℝ) : ℝ) : ℂ)) * (1 + (Complex.I * yVirC (virV ζ w)) ^ 2)) a :=
      ((hY_d.pow 2).const_add 1).const_mul _
    have hden_d : DifferentiableAt ℂ (fun w => 1 + (Complex.I * yVirC (virV ζ w)) ^ 2 +
        ((n ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * yVirC (virV ζ w))) a :=
      ((hY_d.pow 2).const_add 1).add ((hY_d.const_add 1).const_mul _)
    have hmt_d : DifferentiableAt ℂ (fun w => lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ w)) ^ 2) a :=
      (hnum_d.div hden_d (virEb_den_ne b hn2 hζ ha)).pow 2
    have hPsi_dn : DifferentiableAt ℂ (virPsi n) a := (hPsi_diff_n n hn a ha).differentiableAt (isOpen_ball.mem_nhds ha)
    have hPsi_d0 : DifferentiableAt ℂ (virPsi 0) a := (hPsi_diff_0 a ha).differentiableAt (isOpen_ball.mem_nhds ha)
    have hexp_d : DifferentiableAt ℂ (fun w => Complex.exp (-Complex.I * ζ * (virPsi n w - virPsi 0 w))) a :=
      Complex.differentiableAt_exp.comp a ((hPsi_dn.sub hPsi_d0).const_mul (-Complex.I * ζ))
    have hev : (fun w => virEb n ζ w) =ᶠ[𝓝 a] fun w =>
        lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV ζ w)) ^ 2 *
          Complex.exp (-Complex.I * ζ * (virPsi n w - virPsi 0 w)) := by
      filter_upwards with w; unfold virEb; simp only [hn2, ↓reduceIte]
    exact ((hmt_d.mul hexp_d).congr_of_eventuallyEq hev).differentiableWithinAt
  · have heq : virEb n ζ = fun _ => 1 := by ext w; unfold virEb; simp [hn2]
    rw [heq]; exact differentiableWithinAt_const 1

lemma exists_virPolydisc : ∃ r_s r_a M_G0 M_aux K_b C_psi_diff : ℝ,
    0 < r_s ∧ 0 < r_a ∧ 0 ≤ M_G0 ∧ 0 ≤ M_aux ∧ 0 ≤ K_b ∧ 0 ≤ C_psi_diff ∧
    let K : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip
    r_a ≤ min (K * chartParams.ρ_ψ / 2) (K * chartParams.r_ψ / 2) ∧
    (∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => virPhaseFactor ζ a) (ball 0 r_s)) ∧
    (∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (virPhaseFactor ζ) (ball 0 r_a)) ∧
    (∀ ζ ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖virPhaseFactor ζ a‖ ≤ M_G0) ∧
    (∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => (1 - 2 * Complex.I * virV ζ a)⁻¹) (ball 0 r_s)) ∧
    (∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (fun a => (1 - 2 * Complex.I * virV ζ a)⁻¹) (ball 0 r_a)) ∧
    (∀ ζ ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖(1 - 2 * Complex.I * virV ζ a)⁻¹‖ ≤ 2) ∧
    (∀ ζ ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖virV ζ a‖ ≤ 1 / 4 ∧ ‖yVirC (virV ζ a)‖ ≤ 1 / 4) ∧
    (∀ n, 1 ≤ n → ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => virEb n ζ a) (ball 0 r_s)) ∧
    (∀ n, 1 ≤ n → ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (virEb n ζ) (ball 0 r_a)) ∧
    (∀ n ζ a, 1 ≤ n → ζ ∈ ball (0 : ℂ) r_s → a ∈ ball (0 : ℂ) r_a → ‖virEb n ζ a - 1‖ ≤ K_b * n⁻¹) ∧
    (∀ n, 2 ≤ n → ∀ a ∈ ball (0 : ℂ) r_a, ‖virPsi n a - virPsi 0 a‖ ≤ C_psi_diff * n ^ (-2 : ℝ)) ∧
    (∀ (x a : ℝ), |x| < r_s → |a| < r_a →
      (virV (x : ℂ) (a : ℂ)).im = 0 ∧ (virMGeo (x : ℂ) (a : ℂ)).im = 0 ∧
      (virThetaOutC (virV (x : ℂ) (a : ℂ))).im = 0 ∧
      virMGeo (-(x : ℂ)) (a : ℂ) = virMGeo (x : ℂ) (a : ℂ) ∧
      (yVirC (virV (x : ℂ) (a : ℂ))).im = 0 ∧
      (virPsi 0 (a : ℂ)).im = 0 ∧
      ∀ n, 1 ≤ n → (virPsi n (a : ℂ)).im = 0) ∧
    (∀ (a : ℝ), -r_a < a → a < 0 →
      virPhaseFactor (√(-a) : ℂ) (a : ℂ) = 1 ∧ virPhaseFactor (-(√(-a) : ℂ)) (a : ℂ) = 1) := by
  obtain ⟨b⟩ := exists_virBallSpec
  have hinv_ne : ∀ {ζ a : ℂ}, ζ ∈ ball 0 b.r_s → a ∈ ball 0 b.r_a →
      (1 : ℂ) - 2 * Complex.I * virV ζ a ≠ 0 := fun {ζ a} hζ ha => by
    have hn : ‖2 * Complex.I * virV ζ a‖ ≤ 1 / 2 := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one]; norm_num; linarith [b.hV_bd hζ ha]
    intro h0
    have : (1 : ℂ) = 2 * Complex.I * virV ζ a := sub_eq_zero.mp h0
    have hnm := congrArg norm this
    simp only [norm_one] at hnm
    linarith
  refine ⟨b.r_s, b.r_a, b.M_G0, b.M_aux, b.K_b, b.C_psi_diff,
    b.hrs_pos, b.hra_pos, b.hMG0_nn, b.hMaux_nn, b.hKb_nn, b.hCpd_nn, b.ha_le_psi,
    virPhaseFactor_diff_zeta b, virPhaseFactor_diff_a b, ?_, ?_, ?_, ?_, ?_,
    virEb_diff_zeta b, virEb_diff_a b, fun n ζ a hn hζ ha => virEb_sub_one_le b hn hζ ha,
    virPsi_diff_le b, ?_, ?_⟩
  · intro ζ hζ a ha
    have hζ_le : ‖ζ‖ ≤ 1 := (mem_ball_zero_iff.mp hζ).le.trans b.hs_le_one
    have hre_bd : (Complex.I * (virThetaOutC (virV ζ a) - ζ * virPsi 0 a)).re ≤ 1 + 1 * b.M_ψ' := by
      calc (Complex.I * (virThetaOutC (virV ζ a) - ζ * virPsi 0 a)).re
          ≤ ‖Complex.I * (virThetaOutC (virV ζ a) - ζ * virPsi 0 a)‖ := Complex.re_le_norm _
        _ = ‖virThetaOutC (virV ζ a) - ζ * virPsi 0 a‖ := by rw [norm_mul, Complex.norm_I, one_mul]
        _ ≤ ‖virThetaOutC (virV ζ a)‖ + ‖ζ‖ * ‖virPsi 0 a‖ := by
            simpa [norm_mul] using norm_sub_le (virThetaOutC (virV ζ a)) (ζ * virPsi 0 a)
        _ ≤ 1 + 1 * b.M_ψ' :=
            add_le_add (b.hT_bd hζ ha) (mul_le_mul hζ_le (virPsi_bd_0 b ha) (norm_nonneg _) zero_le_one)
    unfold virPhaseFactor
    rw [norm_mul, Complex.norm_exp, b.hM_G0_def]
    exact mul_le_mul (b.hMG_bd hζ ha) (Real.exp_le_exp.mpr hre_bd) (Real.exp_pos _).le (by norm_num)
  · intro a ha ζ hζ
    exact (((differentiableAt_const (1 : ℂ)).sub ((virV_diff_zeta b hζ ha).const_mul (2 * Complex.I))).inv
      (hinv_ne hζ ha)).differentiableWithinAt
  · intro ζ hζ a ha
    exact (((differentiableAt_const (1 : ℂ)).sub ((virV_diff_a b hζ ha).const_mul (2 * Complex.I))).inv
      (hinv_ne hζ ha)).differentiableWithinAt
  · intro ζ hζ a ha
    have hden_ge : 1 / 2 ≤ ‖(1 : ℂ) - 2 * Complex.I * virV ζ a‖ := by
      have hn : ‖2 * Complex.I * virV ζ a‖ ≤ 1 / 2 := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]; norm_num; linarith [b.hV_bd hζ ha]
      have htri := norm_sub_norm_le (1 : ℂ) (2 * Complex.I * virV ζ a)
      rw [norm_one] at htri
      linarith
    rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; exact hden_ge)
  · intro ζ hζ a ha; exact ⟨(b.hV_bd hζ ha).le, (b.hY_bd hζ ha).le⟩
  · intro x a hx ha
    have hxC : (x : ℂ) ∈ ball (0 : ℂ) b.r_s := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have haC : (a : ℂ) ∈ ball (0 : ℂ) b.r_a := by simpa [Metric.mem_ball, dist_zero_right] using ha
    have hV_im : (virV (x : ℂ) (a : ℂ)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]; simpa [Complex.conj_ofReal] using (b.hV_conj hxC haC).symm
    have hMG_im : (virMGeo (x : ℂ) (a : ℂ)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]; simpa [Complex.conj_ofReal] using (b.hMG_conj hxC haC).symm
    have hTh_im : (virThetaOutC (virV (x : ℂ) (a : ℂ))).im = 0 := by
      rw [← Complex.conj_eq_iff_im]
      have hconj := b.hT_conj hxC haC
      rw [Complex.conj_eq_iff_im.mpr hV_im] at hconj
      exact hconj.symm
    have hY_im : (yVirC (virV (x : ℂ) (a : ℂ))).im = 0 := by
      rw [← Complex.conj_eq_iff_im]
      have hconj := yVirC_conj (b.hVim hxC haC)
      rw [Complex.conj_eq_iff_im.mpr hV_im] at hconj
      exact hconj.symm
    have hPsi0_im : (virPsi 0 (a : ℂ)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]
      have hspec := (chartParams.hψ_spec 0 le_rfl (by norm_num)).2.1 _ (b.ha_in haC).2.1
      unfold virPsi; rw [Real.zero_rpow (by norm_num)]
      have harg_c : starRingEnd ℂ (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * (a : ℂ)) =
          (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * (a : ℂ)) := by simp [Complex.conj_ofReal]
      rw [harg_c] at hspec
      rw [map_mul, Complex.conj_ofReal, ← hspec]
    refine ⟨hV_im, hMG_im, hTh_im, b.hMG_neg hxC haC, hY_im, hPsi0_im, fun n hn => ?_⟩
    by_cases hn2 : 2 ≤ n
    · have hspec := (chartParams.hψ_spec _ (by positivity) (inv_sq_le_quarter hn2)).2.1 _ (b.ha_in haC).2.1
      rw [← Complex.conj_eq_iff_im]; unfold virPsi
      have harg_c : starRingEnd ℂ (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * (a : ℂ)) =
          (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * (a : ℂ)) := by simp [Complex.conj_ofReal]
      rw [harg_c] at hspec
      rw [map_mul, Complex.conj_ofReal, ← hspec]
    · have hε_gt : ¬ (0 ≤ n ^ (-2 : ℝ) ∧ n ^ (-2 : ℝ) ≤ 1 / 4) := not_inv_sq_le_quarter hn hn2
      have hzero : virPsi n (a : ℂ) = 0 := by
        unfold virPsi virasoroPsiEps; simp only [hε_gt, ↓reduceIte, mul_zero]
      rw [hzero, Complex.zero_im]
  · intro a hlo ha0
    exact b.hSaddle a (by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_neg ha0]
      exact (by linarith : -a < b.r_a).trans_le b.ha_le_R3) ha0

end
end FormalResearch.ModularBootstrap.FiveTerm
