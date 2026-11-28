module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs
public import FormalResearch.ModularBootstrap.FiveTerm.LowerChartMain
public import FormalResearch.ModularBootstrap.FiveTerm.LowerCorL
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasBandBridge
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds
public import FormalResearch.SignUncertainty.CtRoscAiry
public import FormalResearch.SignUncertainty.CtRoscEta
public import FormalResearch.SignUncertainty.CtWindowOrth
public import FormalResearch.SignUncertainty.FineOrderSigned
public import FormalResearch.Special.AiryCftZeros

/-!
# Virasoro Half-Disc Orthogonalities (`cts:rosc-uncond` (3)) and Coordinate Mass Expansion

Reuses Paper I's `airy_halfdisc_rosc`, `airyRplusComparison`, `ctEta_ge_half`, `fs_pairing_1`,
and `Special.airy_circleData` for the shifted Virasoro density
`f(u) = lowerF virasoroProblem virasoroPhi c g u`:

* `lowerF_virasoro_holo_real`: holomorphy, real-symmetry, and `L¹([-R, R]) ≤ 1` on `ball 0 R'` (`R < R'`).
* `virasoro_rosc`: `P_R(H) - I_R(H) = -2 ∫_0^R H(-v) sin((4/3) v^{3/2}) dv + O(c⁻¹ η_R)`.
* `virasoro_D_orth`: `|∫_{-R}^R (f x).re * fsK x dx| ≤ C c⁻¹ η_R`.
* `virasoro_rosc_mass_expansion`: positive-lobe decay `O(c^{-4/3})`, `∫_{-R}^R Re f + g_vac/(2π M)`
  vs `∫_{Δ(φ(-R))}^∞ g V / M`, and the transferred taper integral `∫_0^R w_R(v) f(-v) dv`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set intervalIntegral Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.FixedWeightBand
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FineOrderSigned

noncomputable section

private lemma log_mul_rpow_neg_le {c' α : ℝ} (hc' : 1 ≤ c') (hα : 0 < α) :
    c' ^ (-α) * Real.log c' ≤ (2 / α) * c' ^ (-(α / 2)) := by
  have hc'_pos : 0 < c' := by linarith
  have hlog : (α / 2) * Real.log c' ≤ c' ^ (α / 2) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (α / 2))
    rw [Real.log_rpow hc'_pos] at h
    linarith
  have hlog_bd : Real.log c' ≤ (2 / α) * c' ^ (α / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / α)
    have h1 : (2 / α) * ((α / 2) * Real.log c') = Real.log c' := by
      field_simp [hα.ne']
    linarith [hmul]
  calc c' ^ (-α) * Real.log c'
      ≤ c' ^ (-α) * ((2 / α) * c' ^ (α / 2)) :=
        mul_le_mul_of_nonneg_left hlog_bd (Real.rpow_nonneg hc'_pos.le _)
    _ = (2 / α) * (c' ^ (-α) * c' ^ (α / 2)) := by ring
    _ = (2 / α) * c' ^ (-(α / 2)) := by
        rw [← Real.rpow_add hc'_pos]; ring_nf

private lemma virasoro_rmax_lt_half_A2 {c : ℝ} (hc0 : 0 < c) :
    lowerRmax virasoroC1 c < virasoroAC c ^ 2 / 2 := by
  have hc1_bv : 10 * virasoroC1 ≤ virasoroBV := virasoroC1_small.trans virasoroBVChoice_le
  have hc1_pos := virasoroC1_pos
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hA2 : virasoroAC c ^ 2 = 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := virasoroAC_sq c hc0.le
  have hsq : 100 * virasoroC1 ^ 2 ≤ virasoroBV ^ 2 := by
    have h1 : (10 * virasoroC1) ^ 2 ≤ virasoroBV ^ 2 := pow_le_pow_left₀ (by positivity) hc1_bv 2
    linarith only [h1]
  have hmul : 100 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) ≤ virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right hsq hc23.le
  have hY : 0 < virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by positivity
  rw [hA2, lowerRmax]
  linarith only [hY, hmul]

private lemma deriv_ofReal_eq_re {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {x : ℝ} (hx : (x : ℂ) ∈ U)
    (hreal : ∃ δ > 0, ∀ y : ℝ, |y - x| < δ → (y : ℂ) ∈ U ∧ (F (y : ℂ)).im = 0) :
    HasDerivAt (fun y : ℝ => (F (y : ℂ)).re) (deriv F (x : ℂ)).re x ∧ (deriv F (x : ℂ)).im = 0 := by
  have hd : HasDerivAt F (deriv F (x : ℂ)) (x : ℂ) :=
    (hF.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hdR : HasDerivAt (fun y : ℝ => F (y : ℂ)) (deriv F (x : ℂ)) x :=
    hd.comp_ofReal
  have hdRe : HasDerivAt (fun y : ℝ => (F (y : ℂ)).re) (deriv F (x : ℂ)).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hdR
  obtain ⟨δ, hδ_pos, hδ⟩ := hreal
  have hdIm : HasDerivAt (fun y : ℝ => (F (y : ℂ)).im) (deriv F (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hdR
  have him_eq : (fun y : ℝ => (F (y : ℂ)).im) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x hδ_pos] with y hy
    exact (hδ y (by simpa [Real.dist_eq] using hy)).2
  have hd0 : HasDerivAt (fun y : ℝ => (F (y : ℂ)).im) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq him_eq
  exact ⟨hdRe, hdIm.unique hd0⟩

private lemma hasDerivAt_conj_conj_rosc {F : ℂ → ℂ} {z d : ℂ}
    (hF : HasDerivAt F d (starRingEnd ℂ z)) :
    HasDerivAt (fun w : ℂ => starRingEnd ℂ (F (starRingEnd ℂ w))) (starRingEnd ℂ d) z := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hF ⊢
  have hcont : Continuous fun t : ℂ => starRingEnd ℂ t := Complex.continuous_conj
  have htend : Tendsto (fun t : ℂ => starRingEnd ℂ t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, map_eq_zero] using ht
  have hlim := (hcont.tendsto d).comp (hF.comp htend)
  refine hlim.congr' (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [map_mul, map_inv₀, Complex.conj_conj, map_sub, map_add]

private lemma conj_symm_ofReal_ball {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (ball 0 r))
    (hreal : ∀ x : ℝ, |x| < r → (F (x : ℂ)).im = 0) :
    ∀ z ∈ ball (0 : ℂ) r, F (starRingEnd ℂ z) = starRingEnd ℂ (F z) := by
  let Fc : ℂ → ℂ := fun z => starRingEnd ℂ (F (starRingEnd ℂ z))
  have hFc : DifferentiableOn ℂ Fc (ball 0 r) := fun z hz => by
    have hz' : starRingEnd ℂ z ∈ ball (0 : ℂ) r := by
      simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
    have hd := (hF.differentiableAt (isOpen_ball.mem_nhds hz')).hasDerivAt
    exact (hasDerivAt_conj_conj_rosc hd).differentiableAt.differentiableWithinAt
  have hanF : AnalyticOnNhd ℂ F (ball 0 r) := hF.analyticOnNhd isOpen_ball
  have hanFc : AnalyticOnNhd ℂ Fc (ball 0 r) := hFc.analyticOnNhd isOpen_ball
  have heq : EqOn F Fc (ball 0 r) := by
    refine hanF.eqOn_of_preconnected_of_frequently_eq hanFc (convex_ball _ _).isPreconnected
      (mem_ball_self hr) ?_
    rw [frequently_iff]
    intro U hU
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp isOpen_ball (0 : ℂ) (mem_ball_self hr)
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, h0V, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδball⟩ := Metric.isOpen_iff.mp hV_open (0 : ℂ) h0V
    set t : ℝ := min (r / 2) (δ / 2)
    have ht_pos : 0 < t := lt_min (half_pos hr) (half_pos hδ_pos)
    have ht_mem : (t : ℂ) ∈ V ∩ ({(0 : ℂ)}ᶜ) := by
      refine ⟨hδball ?_, by simp [ht_pos.ne']⟩
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact (min_le_right _ _).trans_lt (half_lt_self hδ_pos)
    refine ⟨(t : ℂ), hVU ht_mem, ?_⟩
    have htr : |t| < r := by
      rw [abs_of_pos ht_pos]; exact (min_le_left _ _).trans_lt (half_lt_self hr)
    have him := hreal t htr
    have hFt : F (t : ℂ) = ((F (t : ℂ)).re : ℂ) := Complex.ext rfl him
    simp only [Fc, Complex.conj_ofReal]
    rw [hFt, Complex.conj_ofReal]
  intro z hz
  have h1 := heq hz
  dsimp [Fc] at h1
  calc F (starRingEnd ℂ z) = starRingEnd ℂ (starRingEnd ℂ (F (starRingEnd ℂ z))) :=
        (Complex.conj_conj _).symm
    _ = starRingEnd ℂ (F z) := by rw [← h1]

/-- Holomorphy, real-symmetry, `L¹([-R, R]) ≤ 1`, and derivative bounds for
`lowerF virasoroProblem virasoroPhi c g` on a disc `ball 0 R'` (`R < R'`). -/
theorem lowerF_virasoro_holo_real :
    ∃ cc Cφ : ℝ, virasoroCQEnv ≤ cc ∧ 0 ≤ Cφ ∧
      ∀ {c T R : ℝ} {g : ℝ → ℝ}, cc ≤ c →
        virasoroProblem.IsWeaklyFeasible (c / 12) T g →
        LowerRadiusRange virasoroC1 c R →
        (∃ R' : ℝ, R < R' ∧
          DifferentiableOn ℂ (lowerF virasoroProblem virasoroPhi c g) (ball 0 R') ∧
          (∀ z ∈ ball (0 : ℂ) R',
            lowerF virasoroProblem virasoroPhi c g (starRingEnd ℂ z) =
              starRingEnd ℂ (lowerF virasoroProblem virasoroPhi c g z)) ∧
          (∀ x : ℝ, |x| ≤ R → (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).im = 0) ∧
          (∀ u ∈ ball (0 : ℂ) R', ‖virasoroPhi c u‖ < virasoroAC c ^ 2) ∧
          (∀ x : ℝ, |x| ≤ R →
            |(virasoroPhi c (x : ℂ)).re - x| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧
            |(virasoroPhi c (x : ℂ)).re| ≤ virasoroAC c ^ 2 * (3 / 4) ∧
            1 / 2 ≤ (deriv (virasoroPhi c) (x : ℂ)).re ∧
            ‖deriv (virasoroPhi c) (x : ℂ) - 1‖ ≤ Cφ * c ^ (-1 : ℝ) ∧
            (deriv (virasoroPhi c) (x : ℂ)).im = 0)) ∧
        (∫ x in (-R)..R, ‖lowerF virasoroProblem virasoroPhi c g (x : ℂ)‖ ≤ 1) := by
  obtain ⟨cc_ch, Cφ, hCφ_nn, hch⟩ := virasoroChart_holds
  obtain ⟨c_Q1, _, _, hcQ1, _, _, hQ1⟩ := lemmaQ_part1
  let cc : ℝ := max (max cc_ch c_Q1) (max (max (2 * Cφ + 1) ((2 * Cφ + 1) ^ 3)) (max ((2 / virasoroBV) ^ 3 + 1) 10000))
  have hcc_Q : virasoroCQEnv ≤ cc :=
    hcQ1.trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨cc, Cφ, hcc_Q, hCφ_nn, fun {c T R g} hc hwf hR => ?_⟩
  have hcc_ch : cc_ch ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcc_Q1 : c_Q1 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcc_2c : 2 * Cφ + 1 ≤ c := by
    dsimp [cc] at hc
    exact le_trans (le_max_left (2 * Cφ + 1) ((2 * Cφ + 1) ^ 3))
      (le_trans (le_max_left _ _) (le_trans (le_max_right (max cc_ch c_Q1) _) hc))
  have hcc_bv : (2 / virasoroBV) ^ 3 + 1 ≤ c := by
    dsimp [cc] at hc
    exact le_trans (le_max_left _ 10000) (le_trans (le_max_right _ _) (le_trans (le_max_right (max cc_ch c_Q1) _) hc))
  have hc10000 : 10000 ≤ c := by
    dsimp [cc] at hc
    exact le_trans (le_max_right _ 10000) (le_trans (le_max_right _ _) (le_trans (le_max_right (max cc_ch c_Q1) _) hc))
  have hc0 : 0 < c := by linarith only [hc10000]
  have hc_Q : virasoroCQEnv ≤ c := hcQ1.trans hcc_Q1
  obtain ⟨⟨ρ, hρ_gt, hφ_diff⟩, hφ_im, hφ_bd, _, _⟩ := hch c hcc_ch
  obtain ⟨hM_pos, _, _, _⟩ := hQ1 hcc_Q1 hwf
  have hRmax_pos : 0 < lowerRmax virasoroC1 c := by
    unfold lowerRmax; have := virasoroC1_pos; positivity
  have hR_nn : 0 ≤ R := by
    have : 0 ≤ lowerRmin virasoroC1 c := by unfold lowerRmin; positivity
    linarith only [hR.1, this]
  have hR_le_max : R ≤ lowerRmax virasoroC1 c := hR.2
  have hA2_pos : 0 < virasoroAC c ^ 2 := by
    rw [virasoroAC_sq c hc0.le]; have := virasoroBV_pos; positivity
  have hA2_ge2 : 2 ≤ virasoroAC c ^ 2 := by
    have hbv := virasoroBV_pos
    have hbase : ((2 / virasoroBV : ℝ) ^ (3 : ℕ)) ≤ c := by linarith only [hcc_bv]
    have h1 := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at h1
    norm_num at h1
    have h2 : 1 ≤ virasoroBV * c ^ (1 / 3 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left h1 hbv.le
      have hdv : virasoroBV * (2 / virasoroBV) = 2 := by field_simp [hbv.ne']
      linarith only [hm, hdv]
    have hsq := pow_le_pow_left₀ zero_le_one h2 2
    rw [virasoroAC_sq c hc0.le]
    have heq : (virasoroBV * c ^ (1 / 3 : ℝ)) ^ 2 = virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le]; norm_num
    nlinarith only [hsq, heq]
  -- On `closedBall 0 (lowerRmax virasoroC1 c)`, `‖φ c u‖ < virasoroAC c ^ 2`
  have hCφ_c13 : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 := by
    have h23 : ((2 * Cφ + 1 : ℝ) ^ (3 : ℕ)) ≤ c := by
      dsimp [cc] at hc
      exact le_trans (le_max_right (2 * Cφ + 1) ((2 * Cφ + 1) ^ 3))
        (le_trans (le_max_left _ _) (le_trans (le_max_right (max cc_ch c_Q1) _) hc))
    have hc13_ge : 2 * Cφ + 1 ≤ c ^ (1 / 3 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) h23 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at h1
      norm_num at h1; exact h1
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith only [hc13_ge]
  have hφ_cb_lt : ∀ u ∈ closedBall (0 : ℂ) (lowerRmax virasoroC1 c),
      ‖virasoroPhi c u‖ < virasoroAC c ^ 2 := by
    intro u hu
    rw [mem_closedBall_zero_iff] at hu
    have h1 := (hφ_bd u hu).1
    have h2 : ‖virasoroPhi c u‖ ≤ ‖u‖ + Cφ * c ^ (-(1 / 3 : ℝ)) := by
      calc ‖virasoroPhi c u‖ = ‖u + (virasoroPhi c u - u)‖ := by ring_nf
        _ ≤ ‖u‖ + ‖virasoroPhi c u - u‖ := norm_add_le _ _
        _ ≤ ‖u‖ + Cφ * c ^ (-(1 / 3 : ℝ)) := by gcongr
    have h3 : virasoroAC c ^ 2 / 2 + 1 / 2 < virasoroAC c ^ 2 := by linarith only [hA2_ge2]
    have hrm := virasoro_rmax_lt_half_A2 hc0
    linarith only [hu, h2, hCφ_c13, hrm, h3]
  -- By compactness of `closedBall 0 (lowerRmax)`, `∃ R' ∈ (R, ρ)` mapping into `ball 0 (virasoroAC c^2)`
  have hsub_rho : closedBall (0 : ℂ) (lowerRmax virasoroC1 c) ⊆ ball (0 : ℂ) ρ := fun u hu => by
    rw [mem_closedBall_zero_iff] at hu; exact mem_ball_zero_iff.mpr (hu.trans_lt hρ_gt)
  have hcont_φ : ContinuousOn (virasoroPhi c) (ball (0 : ℂ) ρ) := hφ_diff.continuousOn
  have hK_open : IsOpen {u : ℂ | u ∈ ball (0 : ℂ) ρ ∧ ‖virasoroPhi c u‖ < virasoroAC c ^ 2} := by
    have hpre : {u : ℂ | u ∈ ball (0 : ℂ) ρ ∧ ‖virasoroPhi c u‖ < virasoroAC c ^ 2} =
        ball (0 : ℂ) ρ ∩ (fun u => ‖virasoroPhi c u‖) ⁻¹' Iio (virasoroAC c ^ 2) := rfl
    rw [hpre]
    exact hcont_φ.norm.isOpen_inter_preimage isOpen_ball isOpen_Iio
  have hK_sub : closedBall (0 : ℂ) (lowerRmax virasoroC1 c) ⊆
      {u : ℂ | u ∈ ball (0 : ℂ) ρ ∧ ‖virasoroPhi c u‖ < virasoroAC c ^ 2} := fun u hu =>
    ⟨hsub_rho hu, hφ_cb_lt u hu⟩
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := (isCompact_closedBall (0 : ℂ) (lowerRmax virasoroC1 c)).exists_thickening_subset_open
    hK_open hK_sub
  let R' : ℝ := lowerRmax virasoroC1 c + δ / 2
  have hR_lt_R' : R < R' := by dsimp [R']; linarith only [hR_le_max, hδ_pos]
  have hR'_ball_sub : ball (0 : ℂ) R' ⊆ {u : ℂ | u ∈ ball (0 : ℂ) ρ ∧ ‖virasoroPhi c u‖ < virasoroAC c ^ 2} := by
    intro u hu
    apply hδ_sub
    rw [Metric.mem_thickening_iff]
    by_cases hu_max : ‖u‖ ≤ lowerRmax virasoroC1 c
    · refine ⟨u, mem_closedBall_zero_iff.mpr hu_max, ?_⟩
      simpa using hδ_pos
    · have hu_gt : lowerRmax virasoroC1 c < ‖u‖ := lt_of_not_ge hu_max
      have hu_ne : u ≠ 0 := fun h0 => by rw [h0, norm_zero] at hu_gt; linarith only [hRmax_pos, hu_gt]
      set v : ℂ := ((lowerRmax virasoroC1 c / ‖u‖ : ℝ) : ℂ) * u
      refine ⟨v, mem_closedBall_zero_iff.mpr ?_, ?_⟩
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hRmax_pos (norm_pos_iff.mpr hu_ne)),
          div_mul_cancel₀ _ (norm_pos_iff.mpr hu_ne).ne']
      · rw [dist_eq_norm]
        have hsub : u - v = ((1 - lowerRmax virasoroC1 c / ‖u‖ : ℝ) : ℂ) * u := by
          dsimp [v]; push_cast; ring
        rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1pos : 0 ≤ 1 - lowerRmax virasoroC1 c / ‖u‖ := by
          rw [sub_nonneg, div_le_one (norm_pos_iff.mpr hu_ne)]; exact hu_gt.le
        rw [abs_of_nonneg h1pos, sub_mul, one_mul, div_mul_cancel₀ _ (norm_pos_iff.mpr hu_ne).ne']
        have huR' : ‖u‖ < R' := by simpa [mem_ball_zero_iff] using hu
        dsimp [R'] at huR'
        linarith only [huR', hδ_pos]
  have hR'_rho : ball (0 : ℂ) R' ⊆ ball (0 : ℂ) ρ := fun u hu => (hR'_ball_sub hu).1
  have hR'_A2 : ∀ u ∈ ball (0 : ℂ) R', ‖virasoroPhi c u‖ < virasoroAC c ^ 2 := fun u hu =>
    (hR'_ball_sub hu).2
  have hψ_an : AnalyticOnNhd ℂ (psiTilde virasoroProblem c g) (ball 0 (virasoroAC c ^ 2)) := by
    have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
      funext (psiTilde_virasoroProblem hc0.le g)
    rw [heq]
    have hc1000 : 1000 ≤ c := by linarith only [hc10000]
    exact (virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).mono
      (fun u hu => virasoro_closedBall_subset_psiDom hc0 (ball_subset_closedBall hu))
  have hψ_diff : DifferentiableOn ℂ (psiTilde virasoroProblem c g) (ball 0 (virasoroAC c ^ 2)) :=
    hψ_an.differentiableOn
  have hf_diff : DifferentiableOn ℂ (lowerF virasoroProblem virasoroPhi c g) (ball 0 R') := by
    intro u hu
    have hφ_at : DifferentiableAt ℂ (virasoroPhi c) u :=
      (hφ_diff.differentiableAt (isOpen_ball.mem_nhds (hR'_rho hu)))
    have hdφ_an : AnalyticOnNhd ℂ (deriv (virasoroPhi c)) (ball 0 R') :=
      ((hφ_diff.mono hR'_rho).analyticOnNhd isOpen_ball).deriv
    have hdφ_at : DifferentiableAt ℂ (deriv (virasoroPhi c)) u :=
      (hdφ_an u hu).differentiableAt
    have hψ_at : DifferentiableAt ℂ (psiTilde virasoroProblem c g) (virasoroPhi c u) :=
      hψ_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (hR'_A2 u hu)))
    exact ((hψ_at.comp u hφ_at).mul hdφ_at).differentiableWithinAt
  -- Real-axis values of `φ_c`, `φ_c'`, and `lowerF`
  have hφ_real_R' : ∀ x : ℝ, |x| ≤ lowerRmax virasoroC1 c →
      (virasoroPhi c (x : ℂ)).im = 0 ∧
      |(virasoroPhi c (x : ℂ)).re - x| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧
      |(virasoroPhi c (x : ℂ)).re| ≤ virasoroAC c ^ 2 * (3 / 4) ∧
      1 / 2 ≤ (deriv (virasoroPhi c) (x : ℂ)).re ∧
      ‖deriv (virasoroPhi c) (x : ℂ) - 1‖ ≤ Cφ * c ^ (-1 : ℝ) ∧
      (deriv (virasoroPhi c) (x : ℂ)).im = 0 := by
    intro x hx
    have hnorm : ‖(x : ℂ)‖ ≤ lowerRmax virasoroC1 c := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hx
    obtain ⟨h1, h2⟩ := hφ_bd (x : ℂ) hnorm
    have him : (virasoroPhi c (x : ℂ)).im = 0 := hφ_im x hx
    have hre_sub : |(virasoroPhi c (x : ℂ)).re - x| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) := by
      have heq : (virasoroPhi c (x : ℂ)).re - x = (virasoroPhi c (x : ℂ) - (x : ℂ)).re := by simp
      rw [heq]
      exact (Complex.abs_re_le_norm _).trans h1
    have hre_A2 : |(virasoroPhi c (x : ℂ)).re| ≤ virasoroAC c ^ 2 * (3 / 4) := by
      have hrm := virasoro_rmax_lt_half_A2 hc0
      have hsum : |(virasoroPhi c (x : ℂ)).re| ≤ |x| + Cφ * c ^ (-(1 / 3 : ℝ)) := by
        linarith only [abs_sub_abs_le_abs_sub (virasoroPhi c (x : ℂ)).re x, hre_sub]
      have : |x| + Cφ * c ^ (-(1 / 3 : ℝ)) ≤ virasoroAC c ^ 2 / 2 + 1 / 2 := by linarith only [hx, hrm, hCφ_c13]
      have hhalf : virasoroAC c ^ 2 / 2 + 1 / 2 ≤ virasoroAC c ^ 2 * (3 / 4) := by linarith only [hA2_ge2]
      linarith only [hsum, this, hhalf]
    have hderiv_re_bd : |(deriv (virasoroPhi c) (x : ℂ)).re - 1| ≤ Cφ * c ^ (-1 : ℝ) := by
      have heq : (deriv (virasoroPhi c) (x : ℂ)).re - 1 = (deriv (virasoroPhi c) (x : ℂ) - 1).re := by simp
      rw [heq]
      exact (Complex.abs_re_le_norm _).trans h2
    have hCφ_c1 : Cφ * c ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hc0]
      linarith only [hcc_2c]
    have hderiv_re_ge : 1 / 2 ≤ (deriv (virasoroPhi c) (x : ℂ)).re := by
      linarith only [(abs_le.mp hderiv_re_bd).1, hCφ_c1]
    have hconj_rm : ∀ z ∈ ball (0 : ℂ) (lowerRmax virasoroC1 c),
        virasoroPhi c (starRingEnd ℂ z) = starRingEnd ℂ (virasoroPhi c z) :=
      conj_symm_ofReal_ball hRmax_pos (hφ_diff.mono (ball_subset_ball hρ_gt.le))
        fun y hy => hφ_im y hy.le
    have hderiv_im : (deriv (virasoroPhi c) (x : ℂ)).im = 0 := by
      have hd_cont : ContinuousOn (deriv (virasoroPhi c)) (ball 0 ρ) :=
        ((hφ_diff.analyticOnNhd isOpen_ball).deriv).continuousOn
      have hx_rho : (x : ℂ) ∈ ball (0 : ℂ) ρ := hsub_rho (mem_closedBall_zero_iff.mpr hnorm)
      have htend : Tendsto (fun t : ℝ => (deriv (virasoroPhi c) ((t * x : ℝ) : ℂ)).im) (𝓝[<] 1)
          (𝓝 (deriv (virasoroPhi c) (x : ℂ)).im) := by
        have ht1 : Tendsto (fun t : ℝ => ((t * x : ℝ) : ℂ)) (𝓝[<] 1) (𝓝 (x : ℂ)) := by
          have : (fun t : ℝ => ((t * x : ℝ) : ℂ)) = fun t : ℝ => ((t : ℂ) * (x : ℂ)) := by
            ext t; push_cast; ring
          rw [this]
          have hc1 : Tendsto (fun t : ℝ => (t : ℂ) * (x : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 ((1 : ℂ) * (x : ℂ))) :=
            ((Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds).mul_const (x : ℂ)
          simpa using hc1
        exact Complex.continuous_im.continuousAt.tendsto.comp ((hd_cont.continuousAt (isOpen_ball.mem_nhds hx_rho)).tendsto.comp ht1)
      have hev0 : ∀ᶠ t : ℝ in 𝓝[<] 1, (deriv (virasoroPhi c) ((t * x : ℝ) : ℂ)).im = 0 := by
        filter_upwards [Ioo_mem_nhdsLT (zero_lt_one)] with t ht
        have htx_lt : |t * x| < lowerRmax virasoroC1 c := by
          rw [abs_mul, abs_of_pos ht.1]
          rcases eq_or_ne x 0 with rfl | hx0
          · simp [hRmax_pos]
          · have : t * |x| < 1 * |x| := mul_lt_mul_of_pos_right ht.2 (abs_pos.mpr hx0)
            linarith only [this, hx]
        have htx_mem : ((t * x : ℝ) : ℂ) ∈ ball (0 : ℂ) (lowerRmax virasoroC1 c) := by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact htx_lt
        have h_im0 := (deriv_ofReal_eq_re isOpen_ball (hφ_diff.mono (ball_subset_ball hρ_gt.le)) htx_mem
          ⟨lowerRmax virasoroC1 c - |t * x|, by linarith only [htx_lt], fun y hy =>
            ⟨mem_ball_zero_iff.mpr (by
              rw [Complex.norm_real, Real.norm_eq_abs]
              have hy_add : |y| ≤ |y - t * x| + |t * x| := by
                calc |y| = |(y - t * x) + t * x| := by ring_nf
                  _ ≤ |y - t * x| + |t * x| := abs_add_le _ _
              linarith only [hy, hy_add]),
              hφ_im y (by
                have hy_add : |y| ≤ |y - t * x| + |t * x| := by
                  calc |y| = |(y - t * x) + t * x| := by ring_nf
                    _ ≤ |y - t * x| + |t * x| := abs_add_le _ _
                linarith only [hy, hy_add])⟩⟩).2
        exact h_im0
      exact tendsto_nhds_unique (htend.congr' (hev0.mono fun _ h => h)) tendsto_const_nhds
    exact ⟨him, hre_sub, hre_A2, hderiv_re_ge, h2, hderiv_im⟩
  have hf_real : ∀ x : ℝ, |x| ≤ R → (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).im = 0 := by
    intro x hx
    obtain ⟨himφ, _, _, _, _, himdφ⟩ := hφ_real_R' x (hx.trans hR_le_max)
    have hψ_im : (psiTilde virasoroProblem c g (virasoroPhi c (x : ℂ))).im = 0 := by
      have hre_A2 := (hφ_real_R' x (hx.trans hR_le_max)).2.2.1
      have h1 := psiTilde_im_ofReal virasoroProblem hc0 hwf.1
        (u := (virasoroPhi c (x : ℂ)).re) (by linarith only [hre_A2, hA2_pos])
      have heq : (((virasoroPhi c (x : ℂ)).re : ℝ) : ℂ) = virasoroPhi c (x : ℂ) :=
        Complex.ext rfl himφ.symm
      rwa [heq] at h1
    unfold lowerF
    rw [Complex.mul_im, hψ_im, himdφ, mul_zero, zero_mul, add_zero]
  -- Conjugation symmetry on `ball 0 R'`
  have hf_conj : ∀ z ∈ ball (0 : ℂ) R',
      lowerF virasoroProblem virasoroPhi c g (starRingEnd ℂ z) =
        starRingEnd ℂ (lowerF virasoroProblem virasoroPhi c g z) := by
    have hconj_all := conj_symm_ofReal_ball hRmax_pos
      (hf_diff.mono (ball_subset_ball (by dsimp [R']; linarith only [hδ_pos])))
      fun y hy => by
        obtain ⟨himφ, _, _, _, _, himdφ⟩ := hφ_real_R' y hy.le
        have hψ_im : (psiTilde virasoroProblem c g (virasoroPhi c (y : ℂ))).im = 0 := by
          have hre_A2 := (hφ_real_R' y hy.le).2.2.1
          have h1 := psiTilde_im_ofReal virasoroProblem hc0 hwf.1
            (u := (virasoroPhi c (y : ℂ)).re) (by linarith only [hre_A2, hA2_pos])
          have heq : (((virasoroPhi c (y : ℂ)).re : ℝ) : ℂ) = virasoroPhi c (y : ℂ) :=
            Complex.ext rfl himφ.symm
          rwa [heq] at h1
        unfold lowerF
        rw [Complex.mul_im, hψ_im, himdφ, mul_zero, zero_mul, add_zero]
    -- Analytic continuation from `ball 0 (lowerRmax)` to `ball 0 R'`!
    let Fc : ℂ → ℂ := fun z => starRingEnd ℂ (lowerF virasoroProblem virasoroPhi c g (starRingEnd ℂ z))
    have hFc : DifferentiableOn ℂ Fc (ball 0 R') := fun z hz => by
      have hz' : starRingEnd ℂ z ∈ ball (0 : ℂ) R' := by
        simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
      have hd := (hf_diff.differentiableAt (isOpen_ball.mem_nhds hz')).hasDerivAt
      exact (hasDerivAt_conj_conj_rosc hd).differentiableAt.differentiableWithinAt
    have hanF : AnalyticOnNhd ℂ (lowerF virasoroProblem virasoroPhi c g) (ball 0 R') :=
      hf_diff.analyticOnNhd isOpen_ball
    have hanFc : AnalyticOnNhd ℂ Fc (ball 0 R') := hFc.analyticOnNhd isOpen_ball
    have hR'_pos : 0 < R' := lt_of_le_of_lt hR_nn hR_lt_R'
    have heq : EqOn (lowerF virasoroProblem virasoroPhi c g) Fc (ball 0 R') := by
      refine hanF.eqOn_of_preconnected_of_frequently_eq hanFc (convex_ball _ _).isPreconnected
        (mem_ball_self hR'_pos) ?_
      rw [frequently_iff]
      intro U hU
      rw [mem_nhdsWithin] at hU
      obtain ⟨V, hV_open, h0V, hVU⟩ := hU
      obtain ⟨δv, hδv_pos, hδv_ball⟩ := Metric.isOpen_iff.mp hV_open (0 : ℂ) h0V
      set t : ℝ := min (lowerRmax virasoroC1 c / 2) (δv / 2)
      have ht_pos : 0 < t := lt_min (half_pos hRmax_pos) (half_pos hδv_pos)
      have ht_V : (t : ℂ) ∈ V ∩ ({(0 : ℂ)}ᶜ) := by
        refine ⟨hδv_ball ?_, by simp [ht_pos.ne']⟩
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact (min_le_right _ _).trans_lt (half_lt_self hδv_pos)
      refine ⟨(t : ℂ), hVU ht_V, ?_⟩
      have ht_rm : (t : ℂ) ∈ ball (0 : ℂ) (lowerRmax virasoroC1 c) := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
        exact (min_le_left _ _).trans_lt (half_lt_self hRmax_pos)
      have h1 := hconj_all (t : ℂ) ht_rm
      simp only [Complex.conj_ofReal] at h1
      dsimp [Fc]
      simp only [Complex.conj_ofReal]
      exact h1
    intro z hz
    have h1 := heq hz
    dsimp [Fc] at h1
    calc lowerF virasoroProblem virasoroPhi c g (starRingEnd ℂ z)
        = starRingEnd ℂ (starRingEnd ℂ (lowerF virasoroProblem virasoroPhi c g (starRingEnd ℂ z))) :=
          (Complex.conj_conj _).symm
      _ = starRingEnd ℂ (lowerF virasoroProblem virasoroPhi c g z) := by rw [← h1]
  -- `L¹([-R, R]) ≤ 1` by change of variables `ut = Re φ_c x`
  have hL1 : ∫ x in (-R)..R, ‖lowerF virasoroProblem virasoroPhi c g (x : ℂ)‖ ≤ 1 := by
    let phiR : ℝ → ℝ := fun x => (virasoroPhi c (x : ℂ)).re
    have hderiv_pos : ∀ x ∈ Icc (-R) R,
        HasDerivAt phiR (deriv (virasoroPhi c) (x : ℂ)).re x ∧ 0 < (deriv (virasoroPhi c) (x : ℂ)).re := by
      intro x hx
      have hx_abs : |x| ≤ R := abs_le.mpr hx
      have hx_rm : |x| ≤ lowerRmax virasoroC1 c := hx_abs.trans hR_le_max
      have hd := (hφ_diff.differentiableAt (isOpen_ball.mem_nhds
        (hsub_rho (mem_closedBall_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx_rm))))).hasDerivAt
      have hdR : HasDerivAt phiR (deriv (virasoroPhi c) (x : ℂ)).re x :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd.comp_ofReal
      obtain ⟨_, _, _, hge, _, _⟩ := hφ_real_R' x hx_rm
      exact ⟨hdR, by linarith only [hge]⟩
    have hderiv_cont : ContinuousOn (fun x : ℝ => (deriv (virasoroPhi c) (x : ℂ)).re) (Icc (-R) R) :=
      Complex.continuous_re.comp_continuousOn
        (((hφ_diff.mono hR'_rho).analyticOnNhd isOpen_ball).deriv.continuousOn.comp
          Complex.continuous_ofReal.continuousOn fun x hx =>
            mem_ball_zero_iff.mpr (by
              rw [Complex.norm_real, Real.norm_eq_abs]
              exact (abs_le.mpr hx).trans_lt hR_lt_R'))
    have hcont_psi_norm : ContinuousOn (fun ut : ℝ => ‖psiTilde virasoroProblem c g (ut : ℂ)‖)
        (phiR '' uIcc (-R) R) := by
      refine continuous_norm.comp_continuousOn (hψ_diff.continuousOn.comp Complex.continuous_ofReal.continuousOn ?_)
      rintro ut ⟨x, hx, rfl⟩
      rw [uIcc_of_le (by linarith only [hR_nn])] at hx
      obtain ⟨him, _, hA2, _, _, _⟩ := hφ_real_R' x ((abs_le.mpr hx).trans hR_le_max)
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      linarith only [hA2, hA2_pos]
    have hnorm_eq : ∀ x ∈ uIcc (-R) R,
        ‖lowerF virasoroProblem virasoroPhi c g (x : ℂ)‖ =
          ‖psiTilde virasoroProblem c g ((phiR x : ℝ) : ℂ)‖ * (deriv (virasoroPhi c) (x : ℂ)).re := by
      intro x hx
      rw [uIcc_of_le (by linarith only [hR_nn])] at hx
      obtain ⟨him, _, _, hge, _, himd⟩ := hφ_real_R' x ((abs_le.mpr hx).trans hR_le_max)
      have heq_phi : virasoroPhi c (x : ℂ) = ((phiR x : ℝ) : ℂ) := Complex.ext rfl him
      have heq_d : deriv (virasoroPhi c) (x : ℂ) = (((deriv (virasoroPhi c) (x : ℂ)).re : ℝ) : ℂ) :=
        Complex.ext rfl himd
      unfold lowerF
      conv_lhs => rw [heq_phi, heq_d]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hge])]
    have hcov : ∫ x in (-R)..R, ‖lowerF virasoroProblem virasoroPhi c g (x : ℂ)‖ =
        ∫ ut in (phiR (-R))..(phiR R), ‖psiTilde virasoroProblem c g (ut : ℂ)‖ := by
      rw [intervalIntegral.integral_congr hnorm_eq]
      refine intervalIntegral.integral_comp_mul_deriv' (fun x hx => ?_)
        (by rwa [uIcc_of_le (by linarith only [hR_nn])]) hcont_psi_norm
      rw [uIcc_of_le (by linarith only [hR_nn])] at hx
      exact (hderiv_pos x hx).1
    have hphi_le : phiR (-R) ≤ phiR R := by
      have hmono : MonotoneOn phiR (Icc (-R) R) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-R) R)
          (Complex.continuous_re.comp_continuousOn
            ((hφ_diff.mono hR'_rho).continuousOn.comp Complex.continuous_ofReal.continuousOn
              fun x hx => mem_ball_zero_iff.mpr (by
                rw [Complex.norm_real, Real.norm_eq_abs]
                exact (abs_le.mpr hx).trans_lt hR_lt_R')))
          (fun x hx => ((hderiv_pos x (interior_subset hx)).1).hasDerivWithinAt)
          (fun x hx => (hderiv_pos x (interior_subset hx)).2.le)
      exact hmono ⟨by linarith only [hR_nn], by linarith only [hR_nn]⟩
        ⟨by linarith only [hR_nn], by linarith only [hR_nn]⟩ (by linarith only [hR_nn])
    have hlo_A2 : -(virasoroAC c ^ 2) ≤ phiR (-R) := by
      have h1 := (hφ_real_R' (-R) (by rw [abs_neg, abs_of_nonneg hR_nn]; exact hR_le_max)).2.2.1
      linarith only [(abs_le.mp h1).1, hA2_pos]
    have hhi_A2 : phiR R ≤ virasoroAC c ^ 2 := by
      have h1 := (hφ_real_R' R (by rw [abs_of_nonneg hR_nn]; exact hR_le_max)).2.2.1
      linarith only [(abs_le.mp h1).2, hA2_pos]
    have hQ3_L1 : ∫ ut in (-(virasoroAC c ^ 2))..(virasoroAC c ^ 2),
        ‖psiTilde virasoroProblem c g (ut : ℂ)‖ ≤ 1 := by
      have h1 := (lemmaQ_part3 hc_Q hwf).2.1
      have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
        funext (psiTilde_virasoroProblem hc0.le g)
      rwa [heq]
    have h_int_A2 : IntervalIntegrable (fun ut : ℝ => ‖psiTilde virasoroProblem c g (ut : ℂ)‖)
        volume (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) := by
      have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
        funext (psiTilde_virasoroProblem hc0.le g)
      rw [heq]
      have hc1000 : 1000 ≤ c := by linarith only [hc10000]
      have hcont : ContinuousOn (fun ut : ℝ => ‖virasoroPsiTilde c g (ut : ℂ)‖)
          (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)) :=
        continuous_norm.comp_continuousOn
          ((virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).continuousOn.comp
            Complex.continuous_ofReal.continuousOn fun ut hut =>
              virasoro_closedBall_subset_psiDom hc0 (mem_closedBall_zero_iff.mpr (by
                rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hut)))
      exact hcont.intervalIntegrable_of_Icc (by linarith only [hA2_pos])
    rw [hcov, intervalIntegral.integral_of_le hphi_le]
    have hle_A2 : ∫ ut in Ioc (phiR (-R)) (phiR R), ‖psiTilde virasoroProblem c g (ut : ℂ)‖ ≤
        ∫ ut in Ioc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2),
          ‖psiTilde virasoroProblem c g (ut : ℂ)‖ := by
      refine setIntegral_mono_set
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only [hA2_pos])).mp h_int_A2)
        (ae_of_all _ fun _ => norm_nonneg _)
        (Eventually.of_forall fun ut hut => ⟨lt_of_le_of_lt hlo_A2 hut.1, hut.2.trans hhi_A2⟩)
    rw [← intervalIntegral.integral_of_le (show -(virasoroAC c ^ 2) ≤ virasoroAC c ^ 2 by linarith only [hA2_pos])] at hle_A2
    exact hle_A2.trans hQ3_L1
  refine ⟨⟨R', hR_lt_R', hf_diff, hf_conj, hf_real, hR'_A2, fun x hx => ?_⟩, hL1⟩
  obtain ⟨_, h1, h2, h3, h4, h5⟩ := hφ_real_R' x (hx.trans hR_le_max)
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **`cts:rosc-uncond` (3), first equation (`cts:rosc`)**:
`|P_R(H) - I_R(H) + 2 ∫_0^R H(-v) sin((4/3) v^{3/2}) dv| ≤ C c⁻¹ η_R`. -/
theorem virasoro_rosc :
    ∃ cc C : ℝ, virasoroCQEnv ≤ cc ∧ 0 ≤ C ∧
      ∀ {c T R : ℝ} {N : ℕ} {g : ℝ → ℝ}, cc ≤ c →
        virasoroProblem.IsWeaklyFeasible (c / 12) T g →
        LowerGoodCircle N R → LowerRadiusRange virasoroC1 c R →
          |lowerPNodes N (lowerH virasoroProblem virasoroPhi c g R) -
              (∫ x in (-R)..R, lowerH virasoroProblem virasoroPhi c g R x) +
              2 * ∫ v in (0 : ℝ)..R,
                lowerH virasoroProblem virasoroPhi c g R (-v) * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))| ≤
            C * c ^ (-1 : ℝ) * lowerEta virasoroProblem virasoroPhi c g R := by
  obtain ⟨cc_h, Cφ, hcc_Q, hCφ, hHolo⟩ := lowerF_virasoro_holo_real
  obtain ⟨Ccmp, R₀, hCcmp, hcmp⟩ := airyRplusComparison
  let cc_r : ℝ := (max R₀ 4 / virasoroC1 ^ 2) ^ (3 / 2 : ℝ) + 1
  let cc : ℝ := max cc_h (max cc_r 10000)
  have hcc_Q' : virasoroCQEnv ≤ cc := hcc_Q.trans (le_max_left _ _)
  let C_rosc : ℝ := Ccmp * (virasoroC1 ^ 3)⁻¹
  have hC1p := virasoroC1_pos
  refine ⟨cc, C_rosc, hcc_Q', by dsimp [C_rosc]; positivity, fun {c T R N g} hc hwf hgood hR => ?_⟩
  have hcc_h : cc_h ≤ c := (le_max_left _ _).trans hc
  have hcc_r : cc_r ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc10000 : 10000 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith only [hc10000]
  have hc1_pos := virasoroC1_pos
  have hR_lo : R₀ ≤ R ∧ 4 ≤ R := by
    have hpow : (max R₀ 4 / virasoroC1 ^ 2) ^ (3 / 2 : ℝ) ≤ c := by
      dsimp [cc_r] at hcc_r; linarith only [hcc_r]
    have h1 : max R₀ 4 / virasoroC1 ^ 2 ≤ c ^ (2 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rw [← Real.rpow_mul (by positivity)] at h
      norm_num at h; exact h
    have h2 : max R₀ 4 ≤ lowerRmin virasoroC1 c := by
      unfold lowerRmin
      calc max R₀ 4 = (max R₀ 4 / virasoroC1 ^ 2) * virasoroC1 ^ 2 := by field_simp [hc1_pos.ne']
        _ ≤ c ^ (2 / 3 : ℝ) * virasoroC1 ^ 2 := by gcongr
        _ = virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by ring
    have hm := h2.trans hR.1
    exact ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩
  have hR0 : 0 < R := by linarith only [hR_lo.2]
  obtain ⟨⟨R', hRR', hf_diff, hf_conj, hf_real, hR'_A2, hφ_real⟩, _⟩ := hHolo hcc_h hwf hR
  have hAi_ne : ∀ u : ℂ, ‖u‖ = R → airyAiC u ≠ 0 := fun u hu h0 => by
    have hlb := hgood.1 u hu
    rw [h0, norm_zero, zero_pow two_ne_zero] at hlb
    have hpos : 0 < 1 / (25 * π) * (1 + R) ^ (-(1 / 2 : ℝ)) * airyEnv u := by
      have := airyEnv_pos u
      positivity
    linarith only [hlb, hpos]
  obtain ⟨N', hN', hD'⟩ := airy_circleData hR0 hAi_ne
  have hNN' : N' = N := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := (hgood.2 (N' + 1) (by omega)).mp (by omega)
      rw [abs_of_neg (airyZero_neg (N' + 1))] at h1
      have h2 := (hN' (N' + 1) (by omega)).mpr h1
      omega
    · have h1 := (hN' (N + 1) (by omega)).mp (by omega)
      rw [← abs_of_neg (airyZero_neg (N + 1))] at h1
      have h2 := (hgood.2 (N + 1) (by omega)).mpr h1
      omega
  have hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R :=
    hNN' ▸ hD'
  have hgood_ct : ctGoodRadius R := hgood.1
  have hcmpR : ∀ θ ∈ Icc (0 : ℝ) π, ‖ctW6 R (circleMap 0 R θ)‖ *
      ‖airyRplus (circleMap 0 R θ) - 2 * airyUpE (circleMap 0 R θ)‖ ≤
        (Ccmp * R ^ (-(3 / 2 : ℝ))) * ‖airyUpE (circleMap 0 R θ)‖ := fun θ hθ =>
    hcmp R hR_lo.1 hgood_ct θ hθ
  have hrosc := airy_halfdisc_rosc hD hRR' (ctW6_diff R).differentiableOn hf_diff
    (fun z hz => by rw [ctW6_conj, hf_conj z hz, ← map_mul]) hcmpR
  -- Match `hrosc`'s LHS with `lowerPNodes` and `lowerH`
  have hlhs_eq : ((∑ n ∈ Finset.Icc 1 N, (ctW6 R (airyZero n : ℂ) *
        lowerF virasoroProblem virasoroPhi c g (airyZero n : ℂ)) /
        (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        (∫ x in (-R)..R, ctW6 R (x : ℂ) * lowerF virasoroProblem virasoroPhi c g (x : ℂ))) +
        2 * ((∫ v in (0 : ℝ)..R,
          (ctW6 R (-(v : ℂ)) * lowerF virasoroProblem virasoroPhi c g (-(v : ℂ))).re *
            Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) : ℝ) : ℂ) =
      (((lowerPNodes N (lowerH virasoroProblem virasoroPhi c g R) -
          (∫ x in (-R)..R, lowerH virasoroProblem virasoroPhi c g R x)) +
          2 * ∫ v in (0 : ℝ)..R,
            lowerH virasoroProblem virasoroPhi c g R (-v) * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
    have hW_real : ∀ x : ℝ, ctW6 R (x : ℂ) = ((lowerW6 R x : ℝ) : ℂ) := fun x => by
      unfold ctW6 lowerW6; push_cast; ring
    have hnode : ∑ n ∈ Finset.Icc 1 N, (ctW6 R (airyZero n : ℂ) *
          lowerF virasoroProblem virasoroPhi c g (airyZero n : ℂ)) /
          (deriv airyAiC (airyZero n : ℂ)) ^ 2 =
        ((lowerPNodes N (lowerH virasoroProblem virasoroPhi c g R) : ℝ) : ℂ) := by
      unfold lowerPNodes lowerH
      push_cast
      refine Finset.sum_congr rfl fun n hn => ?_
      have han_lt : |airyZero n| < R := (hgood.2 n (Finset.mem_Icc.mp hn).1).mp (Finset.mem_Icc.mp hn).2
      have hfn_im := hf_real (airyZero n) han_lt.le
      have hfn_eq : lowerF virasoroProblem virasoroPhi c g (airyZero n : ℂ) =
          (((lowerF virasoroProblem virasoroPhi c g (airyZero n : ℂ)).re : ℝ) : ℂ) :=
        Complex.ext rfl hfn_im
      have hderiv_ai : deriv airyAiC (airyZero n : ℂ) = ((airyAi' (airyZero n) : ℝ) : ℂ) :=
        deriv_airyAiC_ofReal (airyZero n)
      rw [hW_real, hderiv_ai]
      conv_lhs => rw [hfn_eq]
    have hintR : ∫ x in (-R)..R, ctW6 R (x : ℂ) * lowerF virasoroProblem virasoroPhi c g (x : ℂ) =
        ((∫ x in (-R)..R, lowerH virasoroProblem virasoroPhi c g R x : ℝ) : ℂ) := by
      have hfun : EqOn (fun x : ℝ => ctW6 R (x : ℂ) * lowerF virasoroProblem virasoroPhi c g (x : ℂ))
          (fun x : ℝ => ((lowerH virasoroProblem virasoroPhi c g R x : ℝ) : ℂ)) (uIcc (-R) R) := by
        intro x hx
        rw [uIcc_of_le (by linarith only [hR0])] at hx
        have hfim := hf_real x (abs_le.mpr hx)
        have hfeq : lowerF virasoroProblem virasoroPhi c g (x : ℂ) =
            (((lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re : ℝ) : ℂ) :=
          Complex.ext rfl hfim
        unfold lowerH
        dsimp only
        rw [hW_real]
        conv_lhs => rw [hfeq]
        rw [← Complex.ofReal_mul]
      rw [intervalIntegral.integral_congr hfun, intervalIntegral.integral_ofReal]
    have hosc_in : ∫ v in (0 : ℝ)..R,
          (ctW6 R (-(v : ℂ)) * lowerF virasoroProblem virasoroPhi c g (-(v : ℂ))).re *
            Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) =
        ∫ v in (0 : ℝ)..R,
          lowerH virasoroProblem virasoroPhi c g R (-v) * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) := by
      refine intervalIntegral.integral_congr fun v _ => ?_
      rw [show -(v : ℂ) = ((-v : ℝ) : ℂ) by push_cast; ring, hW_real]
      simp [lowerH]
    rw [hnode, hintR, hosc_in]
    push_cast; ring
  rw [hlhs_eq, Complex.norm_real, Real.norm_eq_abs] at hrosc
  -- Match RHS with `C_rosc * c⁻¹ * lowerEta` via `ctEta_ge_half`
  have hψ_cont : ContinuousOn (psiTilde virasoroProblem c g) (sphere 0 R) := by
    have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
      funext (psiTilde_virasoroProblem hc0.le g)
    rw [heq]
    have hc1000 : 1000 ≤ c := by linarith only [hc10000]
    refine (virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).continuousOn.mono fun z hz => ?_
    refine virasoro_closedBall_subset_psiDom hc0 (mem_closedBall_zero_iff.mpr ?_)
    rw [mem_sphere_zero_iff_norm] at hz
    have hzr : ‖z‖ ≤ lowerRmax virasoroC1 c := by linarith only [hz, hR.2]
    have hrm := virasoro_rmax_lt_half_A2 hc0
    linarith only [hzr, hrm, show 0 < virasoroAC c ^ 2 by rw [virasoroAC_sq c hc0.le]; have := virasoroBV_pos; positivity]
  have hf_cont_sph : ContinuousOn (lowerF virasoroProblem virasoroPhi c g) (sphere 0 R) :=
    hf_diff.continuousOn.mono (fun z hz => mem_ball_zero_iff.mpr (by
      rw [mem_sphere_zero_iff_norm] at hz; linarith only [hz, hRR']))
  have heta_half := ctEta_ge_half hR0 hψ_cont hf_cont_sph
  have heta_eq : (∫ θ in (0 : ℝ)..(2 * π),
        R * (‖psiTilde virasoroProblem c g (circleMap 0 R θ)‖ +
          ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖) / airyEnv (circleMap 0 R θ)) =
      lowerEta virasoroProblem virasoroPhi c g R := rfl
  rw [heta_eq] at heta_half
  have hR_pow_le : R ^ (-(3 / 2 : ℝ)) ≤ (virasoroC1 ^ 3)⁻¹ * c ^ (-1 : ℝ) := by
    have hrmin_pos : 0 < lowerRmin virasoroC1 c := by unfold lowerRmin; positivity
    have hpow_min : (lowerRmin virasoroC1 c) ^ (-(3 / 2 : ℝ)) = (virasoroC1 ^ 3)⁻¹ * c ^ (-1 : ℝ) := by
      unfold lowerRmin
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast virasoroC1 2, ← Real.rpow_mul hc1_pos.le,
        ← Real.rpow_mul hc0.le]
      norm_num
    rw [← hpow_min]
    exact Real.rpow_le_rpow_of_nonpos hrmin_pos hR.1 (by norm_num)
  have heta_nn : 0 ≤ lowerEta virasoroProblem virasoroPhi c g R :=
    intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
      div_nonneg (mul_nonneg hR0.le (add_nonneg (norm_nonneg _) (norm_nonneg _))) (airyEnv_pos _).le
  have h1 : R * (Ccmp * R ^ (-(3 / 2 : ℝ))) *
        ∫ θ in (0 : ℝ)..π, ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
          ‖airyUpE (circleMap 0 R θ)‖ =
      Ccmp * R ^ (-(3 / 2 : ℝ)) *
        ∫ θ in (0 : ℝ)..π, R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
          ‖airyUpE (circleMap 0 R θ)‖ := by
    have hrw : (fun θ => R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
          ‖airyUpE (circleMap 0 R θ)‖) =
        fun θ => R * (‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
          ‖airyUpE (circleMap 0 R θ)‖) := by ext θ; ring
    rw [hrw, intervalIntegral.integral_const_mul]; ring
  calc |lowerPNodes N (lowerH virasoroProblem virasoroPhi c g R) -
          (∫ x in (-R)..R, lowerH virasoroProblem virasoroPhi c g R x) +
          2 * ∫ v in (0 : ℝ)..R,
            lowerH virasoroProblem virasoroPhi c g R (-v) * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))|
      ≤ R * (Ccmp * R ^ (-(3 / 2 : ℝ))) *
          ∫ θ in (0 : ℝ)..π, ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
            ‖airyUpE (circleMap 0 R θ)‖ := hrosc
    _ = Ccmp * R ^ (-(3 / 2 : ℝ)) *
          ∫ θ in (0 : ℝ)..π, R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
            ‖airyUpE (circleMap 0 R θ)‖ := h1
    _ ≤ Ccmp * ((virasoroC1 ^ 3)⁻¹ * c ^ (-1 : ℝ)) *
          lowerEta virasoroProblem virasoroPhi c g R := by
        have hpos_int : 0 ≤ ∫ θ in (0 : ℝ)..π, R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
            ‖airyUpE (circleMap 0 R θ)‖ :=
          intervalIntegral.integral_nonneg Real.pi_pos.le fun θ _ =>
            mul_nonneg (mul_nonneg hR0.le (norm_nonneg _)) (norm_nonneg _)
        gcongr
    _ = C_rosc * c ^ (-1 : ℝ) * lowerEta virasoroProblem virasoroPhi c g R := by
        dsimp [C_rosc]; ring

/-- **`cts:rosc-uncond` (3), second equation (`cts:D-orth`) and `|X| ≤ η_R`**:
`|∫_{-R}^R (f(x)).re * D(x) dx| ≤ C c⁻¹ η_R` where `D(x) = (calD_up (x : ℂ)).im = fsK x + 1_{x<0} sin((4/3)(-x)^{3/2})`,
and `|∫_0^R (f(-v)).re * sin((4/3) v^{3/2}) dv| ≤ η_R`. -/
theorem virasoro_D_orth :
    ∃ cc C : ℝ, virasoroCQEnv ≤ cc ∧ 0 ≤ C ∧
      ∀ {c T R : ℝ} {g : ℝ → ℝ}, cc ≤ c →
        virasoroProblem.IsWeaklyFeasible (c / 12) T g →
        LowerRadiusRange virasoroC1 c R →
          |∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re *
              (calD_up (x : ℂ)).im| ≤
            C * c ^ (-1 : ℝ) * lowerEta virasoroProblem virasoroPhi c g R ∧
          |∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
              Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))| ≤
            lowerEta virasoroProblem virasoroPhi c g R := by
  obtain ⟨cc_h, _, hcc_Q, _, hHolo⟩ := lowerF_virasoro_holo_real
  let cc_r : ℝ := (2 / virasoroC1 ^ 2) ^ (3 / 2 : ℝ) + 1
  let cc : ℝ := max cc_h (max cc_r 10000)
  have hcc_Q' : virasoroCQEnv ≤ cc := hcc_Q.trans (le_max_left _ _)
  let C_D : ℝ := 11 * virasoroC1 ^ (-(3 : ℝ))
  have hC1p := virasoroC1_pos
  refine ⟨cc, C_D, hcc_Q', by dsimp [C_D]; positivity, fun {c T R g} hc hwf hR => ?_⟩
  have hcc_h : cc_h ≤ c := (le_max_left _ _).trans hc
  have hcc_r : cc_r ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc10000 : 10000 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith only [hc10000]
  have hc1_pos := virasoroC1_pos
  have hR_ge2 : 2 ≤ R := by
    have hpow : (2 / virasoroC1 ^ 2) ^ (3 / 2 : ℝ) ≤ c := by dsimp [cc_r] at hcc_r; linarith only [hcc_r]
    have h1 : 2 / virasoroC1 ^ 2 ≤ c ^ (2 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rw [← Real.rpow_mul (by positivity)] at h
      norm_num at h; exact h
    have h2 : 2 ≤ lowerRmin virasoroC1 c := by
      unfold lowerRmin
      calc 2 = (2 / virasoroC1 ^ 2) * virasoroC1 ^ 2 := by field_simp [hc1_pos.ne']
        _ ≤ c ^ (2 / 3 : ℝ) * virasoroC1 ^ 2 := by gcongr
        _ = virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by ring
    exact h2.trans hR.1
  have hR0 : 0 < R := by linarith only [hR_ge2]
  obtain ⟨⟨R', hRR', hf_diff, _, hf_real, _, _⟩, _⟩ := hHolo hcc_h hwf hR
  have hψ_cont : ContinuousOn (psiTilde virasoroProblem c g) (sphere 0 R) := by
    have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
      funext (psiTilde_virasoroProblem hc0.le g)
    rw [heq]
    have hc1000 : 1000 ≤ c := by linarith only [hc10000]
    refine (virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).continuousOn.mono fun z hz => ?_
    refine virasoro_closedBall_subset_psiDom hc0 (mem_closedBall_zero_iff.mpr ?_)
    rw [mem_sphere_zero_iff_norm] at hz
    have hzr : ‖z‖ ≤ lowerRmax virasoroC1 c := by linarith only [hz, hR.2]
    have hrm := virasoro_rmax_lt_half_A2 hc0
    linarith only [hzr, hrm, show 0 < virasoroAC c ^ 2 by rw [virasoroAC_sq c hc0.le]; have := virasoroBV_pos; positivity]
  have hf_cont_sph : ContinuousOn (lowerF virasoroProblem virasoroPhi c g) (sphere 0 R) :=
    hf_diff.continuousOn.mono (fun z hz => mem_ball_zero_iff.mpr (by
      rw [mem_sphere_zero_iff_norm] at hz; linarith only [hz, hRR']))
  have heta_half := ctEta_ge_half hR0 hψ_cont hf_cont_sph
  have heta_nn : 0 ≤ lowerEta virasoroProblem virasoroPhi c g R :=
    intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
      div_nonneg (mul_nonneg hR0.le (add_nonneg (norm_nonneg _) (norm_nonneg _))) (airyEnv_pos _).le
  have hK_bd : ∀ θ ∈ Icc (0 : ℝ) π,
      ‖calD_up (circleMap 0 R θ)‖ ≤ (11 * R ^ (-(3 / 2 : ℝ))) * ‖airyUpE (circleMap 0 R θ)‖ := by
    intro θ hθ
    have hu0 : circleMap 0 R θ ≠ 0 := by simp [circleMap, hR0.ne']
    have huim : 0 ≤ (circleMap 0 R θ).im := by
      rw [cftDef_im_circleMap]; exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
    have hun : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR0]
    rw [calD_up_eq_calD huim hu0]
    have hcb := CtAiryHplus.calD_bound huim hu0 (by linarith only [hun, hR_ge2])
    rw [hun] at hcb
    have hexp : Real.exp ((4 / 3) * (circleMap 0 R θ ^ (3 / 2 : ℂ)).re) =
        ‖airyUpE (circleMap 0 R θ)‖ := by
      rw [airyUpE_eq_cexp huim hu0, Complex.norm_exp]; simp [Complex.mul_re]
    rwa [hexp] at hcb
  have hD_bound := halfDisc_im_bound (F := lowerF virasoroProblem virasoroPhi c g) (K := calD_up)
    hR0 hRR' (by positivity) hf_diff hf_real continuousOn_calD_up differentiableOn_calD_up hK_bd
  have hR_pow_le : R ^ (-(3 / 2 : ℝ)) ≤ (virasoroC1 ^ (-(3 : ℝ))) * c ^ (-1 : ℝ) := by
    have hrmin_pos : 0 < lowerRmin virasoroC1 c := by unfold lowerRmin; positivity
    have hpow_min : (lowerRmin virasoroC1 c) ^ (-(3 / 2 : ℝ)) = virasoroC1 ^ (-(3 : ℝ)) * c ^ (-1 : ℝ) := by
      unfold lowerRmin
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast virasoroC1 2, ← Real.rpow_mul hc1_pos.le,
        ← Real.rpow_mul hc0.le]
      norm_num
    rw [← hpow_min]
    exact Real.rpow_le_rpow_of_nonpos hrmin_pos hR.1 (by norm_num)
  have hD_fin : |∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re *
        (calD_up (x : ℂ)).im| ≤
      C_D * c ^ (-1 : ℝ) * lowerEta virasoroProblem virasoroPhi c g R := by
    calc |∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re *
          (calD_up (x : ℂ)).im|
        ≤ (11 * R ^ (-(3 / 2 : ℝ))) *
            ∫ θ in (0 : ℝ)..π, R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
              ‖airyUpE (circleMap 0 R θ)‖ := hD_bound
      _ ≤ (11 * (virasoroC1 ^ (-(3 : ℝ)) * c ^ (-1 : ℝ))) *
            lowerEta virasoroProblem virasoroPhi c g R := by
          have hpos_int : 0 ≤ ∫ θ in (0 : ℝ)..π,
              R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ :=
            intervalIntegral.integral_nonneg Real.pi_pos.le fun θ _ =>
              mul_nonneg (mul_nonneg hR0.le (norm_nonneg _)) (norm_nonneg _)
          have heta' : ∫ θ in (0 : ℝ)..π,
                R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ ≤
              lowerEta virasoroProblem virasoroPhi c g R := by
            unfold lowerEta; exact heta_half
          exact mul_le_mul (by gcongr) heta' hpos_int (by positivity)
      _ = C_D * c ^ (-1 : ℝ) * lowerEta virasoroProblem virasoroPhi c g R := by
          dsimp [C_D]; ring
  have hE_cont : ContinuousOn airyUpE (FormalResearch.HalfDiscCauchy.closedHalfDisc R) :=
    continuousOn_airyUpE.mono fun _ hu => hu.2
  have hE_diff : DifferentiableOn ℂ airyUpE (FormalResearch.HalfDiscCauchy.openHalfDisc R) := fun _ hu =>
    (differentiableAt_airyUpE hu.2).differentiableWithinAt
  have hE_bound := halfDisc_im_bound (F := lowerF virasoroProblem virasoroPhi c g) (K := airyUpE)
    hR0 hRR' zero_le_one hf_diff hf_real hE_cont hE_diff (fun θ _ => by rw [one_mul])
  rw [one_mul] at hE_bound
  have hX_eq : ∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re *
        (airyUpE (x : ℂ)).im =
      -(∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
        Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))) := by
    set F : ℝ → ℝ := fun x => (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re
    have hFc : ContinuousOn F (Icc (-R) R) := Complex.continuous_re.comp_continuousOn
      (hf_diff.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx =>
        mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.mpr hx).trans_lt hRR'))
    have hS : Continuous fun x : ℝ => Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) :=
      Real.continuous_sin.comp (continuous_const.mul (continuous_neg.rpow_const fun _ => Or.inr (by norm_num)))
    have h1 : IntervalIntegrable (fun x => F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0))
        volume (-R) 0 := by
      have hcont1 : ContinuousOn (fun x => F x * Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ))) (uIcc (-R) 0) := by
        rw [uIcc_of_le (by linarith only [hR0])]; exact (hFc.mono (Icc_subset_Icc_right hR0.le)).mul hS.continuousOn
      refine hcont1.intervalIntegrable.congr fun x hx => ?_
      rw [uIoc_of_le (by linarith only [hR0])] at hx
      rcases hx.2.eq_or_lt with rfl | hlt
      · simp [Real.zero_rpow (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
      · simp [hlt]
    have h2 : IntervalIntegrable (fun x => F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0))
        volume 0 R := by
      refine (intervalIntegrable_const (c := (0 : ℝ))).congr fun x hx => ?_
      rw [uIoc_of_le hR0.le] at hx
      simp only [not_lt.mpr hx.1.le, ite_false, mul_zero]
    have hneg_eq : ∫ x in (-R)..R, F x * (airyUpE (x : ℂ)).im =
        -(∫ x in (-R)..R, F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0)) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [airyUpE_im_real]
      split_ifs <;> ring
    rw [hneg_eq, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have hzero : ∫ x in (0 : ℝ)..R, F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0) = 0 := by
      rw [intervalIntegral.integral_congr (fun x hx => by
        rw [uIcc_of_le hR0.le] at hx; simp [not_lt.mpr hx.1] :
        EqOn (fun x => F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0)) (fun _ => 0) (uIcc 0 R)),
        intervalIntegral.integral_zero]
    have hleft : ∫ x in (-R)..0, F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0) =
        ∫ x in (-R)..0, F x * Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by linarith only [hR0])] at hx
      rcases hx.2.eq_or_lt with rfl | hlt
      · simp [Real.zero_rpow (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
      · simp [hlt]
    have hcomp := intervalIntegral.integral_comp_neg (a := 0) (b := R)
      (fun x : ℝ => F x * Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)))
    simp only [neg_zero, neg_neg] at hcomp
    rw [hzero, add_zero, hleft, ← hcomp]
  rw [hX_eq, abs_neg] at hE_bound
  exact ⟨hD_fin, hE_bound.trans heta_half⟩

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerF_virasoro_holo_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerF_virasoro_holo_real

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_rosc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_rosc

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_D_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_D_orth

end

end FormalResearch.ModularBootstrap.FiveTerm
