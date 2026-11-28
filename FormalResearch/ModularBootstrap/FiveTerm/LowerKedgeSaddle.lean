module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeHalfCubicData
public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeGepsDeriv
public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeTailIBP
public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualIdRight
public import FormalResearch.SignUncertainty.CtSdHead
public import FormalResearch.SignUncertainty.CtSdCauchy
public import FormalResearch.SignUncertainty.CtSdSegRem
public import FormalResearch.SignUncertainty.CtSdJoin
public import FormalResearch.SignUncertainty.FineOrderSigned

/-!
# Virasoro Edge Saddle Deformation and Tail Join (`cts:Kedge-signed`)

Connects the real oscillatory integrals `virasoroKedgeEps c' (c' ^ (-2)) x'` and
`virasoroKedge1Eps c' (c' ^ (-2)) x'` at `x' = (virXPrime (a : ℂ)).re` (`|a| < a_cut`) to the
half-cubic Airy contour operators `fsOpCh (fsChain hR1 hRR hUR) (d.uReal c' a) (fun w => d.B c' a (lam * w))`
for `d = virasoroHalfCubic` and `d = virasoroHalfCubicAux`, up to `O(c' ^ (-3 / 2))`:

* `virSaddleSetup`: fixed local box `[0, 2 * s_cut] × (-a_cut, a_cut)` on which the CFU map
  `T(s) = (virV s a).re` is strictly increasing with `0 < T1_lo ≤ T'(s) ≤ T1_hi`, real-valued,
  and pulls back `phiDual` and `kedgeAmp0` / `kedgeAmp0Aux` identically to `virPhaseFactor * W * virEb`.
* `fsOpCh_ray_tail_le`: ray truncation difference between `R_cut = s_cut / lam` and `R_c = d.s₁ / lam`.
* `virasoro_kedge_saddle` and `virasoro_kedge1_saddle`: `O(c' ^ (-3 / 2))` saddle match.
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
open FormalResearch.SignUncertainty.CtSd
open FormalResearch.SignUncertainty.CtOsc
open FormalResearch.SignUncertainty.FineOrderSigned
open FormalResearch.SignUncertainty.FineOrderSigned.HalfCubicInternal

noncomputable section

/-! ### 1. Local real saddle box `VirSaddlePack` -/

/-- Fixed `c'`-independent local CFU box `[0, 2 * s_cut] × (-a_cut, a_cut)`. -/
structure VirSaddlePack where
  s_cut : ℝ
  a_cut : ℝ
  v_lo : ℝ
  T1_lo : ℝ
  T1_hi : ℝ
  δ_lo : ℝ
  M_ψ : ℝ
  hs_pos : 0 < s_cut
  ha_pos : 0 < a_cut
  hv_pos : 0 < v_lo
  hT1_lo : 0 < T1_lo
  hT1_hi : T1_lo ≤ T1_hi
  hδ_pos : 0 < δ_lo
  hMψ_nn : 0 ≤ M_ψ
  hs_lt_s1 : s_cut ≤ virasoroHalfCubic.s₁ / 2
  h3s_lt : 3 * s_cut < virRsIn / 2
  h3s_poly : 3 * s_cut < virPoly.r_s
  ha_shrunk : a_cut ≤ virasoroHalfCubic.rAShrunk
  ha_poly : a_cut ≤ virPoly.r_a
  ha_sq : a_cut ≤ s_cut ^ 2 / 32
  hx'_min : ∀ {a : ℝ}, |a| < a_cut →
    xiStar / 2 ≤ (virXPrime (a : ℂ)).re ∧ (virXPrime (a : ℂ)).im = 0
  hψ_bd : ∀ {c' a : ℝ}, 1 ≤ c' → |a| < a_cut →
    (virPsi c' (a : ℂ)).im = 0 ∧ ‖virPsi c' (a : ℂ)‖ ≤ M_ψ
  hT_props : ∀ {a : ℝ}, |a| < a_cut →
    let T : ℝ → ℝ := fun s => (virV (s : ℂ) (a : ℂ)).re
    let T1 : ℝ → ℝ := fun s => (deriv (fun σ => virV σ (a : ℂ)) (s : ℂ)).re
    T 0 = 0 ∧
    (∀ s ∈ Icc 0 (2 * s_cut), HasDerivAt T (T1 s) s ∧ T1_lo ≤ T1 s ∧ T1 s ≤ T1_hi ∧
      (virV (s : ℂ) (a : ℂ)).im = 0 ∧ (deriv (fun σ => virV σ (a : ℂ)) (s : ℂ)).im = 0) ∧
    (∀ s ∈ Ioc 0 (2 * s_cut), 0 < T s) ∧
    v_lo ≤ T s_cut ∧
    (∀ s ∈ Icc 0 (2 * s_cut), phiDual (T s) (virXPrime (a : ℂ)).re = a * s + s ^ 3 / 3) ∧
    δ_lo ≤ (4 * π / 3) * (edgeF (T s_cut) - (virXPrime (a : ℂ)).re) ∧
    (∀ s ∈ Ioc 0 (2 * s_cut),
      virThetaOutC (T s : ℂ) = (thetaOut (lowerY (edgeF (T s))) : ℂ) ∧
      virMGeo (s : ℂ) (a : ℂ) =
        (((√(2 * π / 3) * √(edgeF' (T s) / s) * T1 s *
          ((1 - Real.exp (-4 * π * edgeF (T s))) /
            (1 - Real.exp (-4 * π * (virXPrime (a : ℂ)).re))) ^ 2 : ℝ) : ℂ)))

private lemma virSaddleSetup : Nonempty VirSaddlePack := by
  have hd_s1 : virasoroHalfCubic.s₁ = virRsIn / 4 := virasoroHalfCubic_spec.2.1
  have hd_ra : virasoroHalfCubic.r_a = min virRaIn ((virRsIn / 2) ^ 2 / 4) := virasoroHalfCubic_spec.1
  have hd_ra_lt : virasoroHalfCubic.rAShrunk < virasoroHalfCubic.r_a := virasoroHalfCubic.rAShrunk_lt
  have hd_ra_poly : virasoroHalfCubic.r_a ≤ virPoly.r_a := by
    rw [hd_ra]; exact (min_le_left _ _).trans virRaIn_le_poly
  have hmgeo_ev := virMGeo_ofReal_pos
  have hth_ev := virThetaOutC_ofReal_nonneg
  have hphi_ev := virPhiDualC_virV_eq
  have hv_cd : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      ContDiffAt ℂ 2 (fun q : ℂ × ℂ => virV q.1 q.2) p ∧
      ContDiffAt ℂ 1 (fun q : ℂ × ℂ => deriv (fun σ => virV σ q.2) q.1) p ∧
      virV (starRingEnd ℂ p.1) (starRingEnd ℂ p.2) = starRingEnd ℂ (virV p.1 p.2) := by
    have hcd1 : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
        ContDiffAt ℂ 1 (fun q : ℂ × ℂ => deriv (fun σ => virV σ q.2) q.1) p :=
      (contDiffAt_virDerivS.of_le (by simp : (1 : WithTop ℕ∞) ≤ _)).eventually (by simp)
    exact contDiffAt2_virV.and (hcd1.and virV_conj)
  have hd_bounds : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      (virD0⁻¹ / 2 : ℝ) ≤ (deriv (fun σ => virV σ p.2) p.1).re ∧
      (deriv (fun σ => virV σ p.2) p.1).re ≤ 2 * virD0⁻¹ := by
    have hc : ContinuousAt (fun q : ℂ × ℂ => (deriv (fun σ => virV σ q.2) q.1).re) ((0 : ℂ), (0 : ℂ)) :=
      Complex.continuous_re.continuousAt.comp contDiffAt_virDerivS.continuousAt
    have h0 : (deriv (fun σ => virV σ 0) 0).re = virD0⁻¹ := by
      rw [virDerivS_zero_zero, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
    have hlo : (virD0⁻¹ / 2 : ℝ) < (deriv (fun σ => virV σ 0) 0).re := by
      rw [h0]; have := inv_pos.mpr virD0_pos; linarith
    have hhi : (deriv (fun σ => virV σ 0) 0).re < 2 * virD0⁻¹ := by
      rw [h0]; have := inv_pos.mpr virD0_pos; linarith
    exact (hc.eventually (isOpen_Ioi.mem_nhds hlo)).and (hc.eventually (isOpen_Iio.mem_nhds hhi)) |>.mono
      fun _ h => ⟨h.1.le, h.2.le⟩
  have hx_bounds : ∀ᶠ a : ℂ in 𝓝 (0 : ℂ),
      xiStar / 2 ≤ (virXPrime a).re ∧ virXPrime (starRingEnd ℂ a) = starRingEnd ℂ (virXPrime a) := by
    have hc : ContinuousAt (fun a : ℂ => (virXPrime a).re) 0 :=
      Complex.continuous_re.continuousAt.comp contDiffAt_virXPrime.continuousAt
    have h0 : xiStar / 2 < (virXPrime 0).re := by
      rw [virXPrime_zero, Complex.ofReal_re]; linarith [xiStar_pos]
    exact (hc.eventually (isOpen_Ioi.mem_nhds h0)).and virXPrime_conj |>.mono fun _ h => ⟨h.1.le, h.2⟩
  obtain ⟨r1, hr1, hr1_spec⟩ := Metric.eventually_nhds_iff_ball.mp hmgeo_ev
  obtain ⟨r2, hr2, hr2_spec⟩ := Metric.eventually_nhds_iff_ball.mp hth_ev
  obtain ⟨r3, hr3, hr3_spec⟩ := Metric.eventually_nhds_iff_ball.mp (hphi_ev.and (hv_cd.and hd_bounds))
  obtain ⟨r4, hr4, hr4_spec⟩ := Metric.eventually_nhds_iff_ball.mp hx_bounds
  have hv_tend : Tendsto (fun p : ℂ × ℂ => (virV p.1 p.2).re) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := by
    have h0 : (virV ((0 : ℂ), (0 : ℂ)).1 ((0 : ℂ), (0 : ℂ)).2).re = 0 := by rw [virV_zero_zero, Complex.zero_re]
    have h1 : Tendsto (fun p : ℂ × ℂ => (virV p.1 p.2).re) (𝓝 ((0 : ℂ), (0 : ℂ)))
        (𝓝 (virV ((0 : ℂ), (0 : ℂ)).1 ((0 : ℂ), (0 : ℂ)).2).re) :=
      (Complex.continuous_re.continuousAt.comp contDiffAt_virV.continuousAt).tendsto
    simpa [h0] using h1
  obtain ⟨r5, hr5, hr5_spec⟩ := Metric.eventually_nhds_iff_ball.mp
    (hv_tend.eventually (Metric.ball_mem_nhds 0 hr2))
  let R_box : ℝ := min r1 (min r3 (min r5 (min (virRsIn / 2) virPoly.r_s)))
  have hR_pos : 0 < R_box :=
    lt_min hr1 (lt_min hr3 (lt_min hr5 (lt_min (half_pos virRsIn_pos) virPoly.hrs)))
  let s_cut : ℝ := min (virasoroHalfCubic.s₁ / 2) (R_box / 4)
  have hs_pos : 0 < s_cut := lt_min (half_pos virasoroHalfCubic.hs₁) (by positivity)
  let a_cut : ℝ := min virasoroHalfCubic.rAShrunk (min r4 (min (R_box / 4) (s_cut ^ 2 / 32)))
  have ha_pos : 0 < a_cut := lt_min virasoroHalfCubic.rAShrunk_pos
    (lt_min hr4 (lt_min (by positivity) (by positivity)))
  have hs_le_s1 : s_cut ≤ virasoroHalfCubic.s₁ / 2 := min_le_left _ _
  have h3s_lt : 3 * s_cut < virRsIn / 2 := by
    rw [hd_s1] at hs_le_s1; linarith [virRsIn_pos]
  have h2s_lt : 2 * s_cut < R_box := by
    have : s_cut ≤ R_box / 4 := min_le_right _ _; linarith
  have h3s_poly : 3 * s_cut < virPoly.r_s := by
    have h1 : s_cut ≤ R_box / 4 := min_le_right _ _
    have h2 : R_box ≤ virPoly.r_s :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith [hR_pos]
  have ha_shrunk : a_cut ≤ virasoroHalfCubic.rAShrunk := min_le_left _ _
  have ha_poly : a_cut ≤ virPoly.r_a := ha_shrunk.trans (hd_ra_lt.le.trans hd_ra_poly)
  have ha_sq : a_cut ≤ s_cut ^ 2 / 32 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha_lt_R : a_cut < R_box := by
    have : a_cut ≤ R_box / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have ha_lt_r4 : a_cut ≤ r4 := (min_le_right _ _).trans (min_le_left _ _)
  let T1_lo : ℝ := virD0⁻¹ / 2
  let T1_hi : ℝ := 2 * virD0⁻¹
  have hT1_lo : 0 < T1_lo := by have := virD0_pos; positivity
  have hT1_hi : T1_lo ≤ T1_hi := by have := virD0_pos; dsimp [T1_lo, T1_hi]; linarith [inv_pos.mpr virD0_pos]
  let v_lo : ℝ := T1_lo * s_cut
  let δ_lo : ℝ := (3 / 4) * s_cut ^ 2 / T1_hi
  have hv_pos : 0 < v_lo := mul_pos hT1_lo hs_pos
  have hδ_pos : 0 < δ_lo := div_pos (mul_pos (by norm_num) (sq_pos_of_pos hs_pos)) (hT1_lo.trans_le hT1_hi)
  refine ⟨⟨s_cut, a_cut, v_lo, T1_lo, T1_hi, δ_lo, virasoroHalfCubic.M_ψ,
    hs_pos, ha_pos, hv_pos, hT1_lo, hT1_hi, hδ_pos, virasoroHalfCubic.hM_ψ,
    hs_le_s1, h3s_lt, h3s_poly, ha_shrunk, ha_poly, ha_sq, ?_, ?_, ?_⟩⟩
  · intro a ha
    have ha4 : (a : ℂ) ∈ ball (0 : ℂ) r4 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha.trans_le ha_lt_r4
    obtain ⟨hx_lo, hx_conj⟩ := hr4_spec _ ha4
    have him : (virXPrime (a : ℂ)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]; simpa [Complex.conj_ofReal] using hx_conj.symm
    exact ⟨hx_lo, him⟩
  · intro c' a hc' ha
    have ha_in : (a : ℂ) ∈ ball (0 : ℂ) virasoroHalfCubic.r_a := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact ha.trans_le (ha_shrunk.trans hd_ra_lt.le)
    have him : (virPsi c' (a : ℂ)).im = 0 := by
      have hre := virasoroHalfCubic.hψ_real c' a hc' (by simpa [mem_ball_zero_iff] using ha_in)
      simpa [virasoroHalfCubic_spec.2.2.2.1] using hre
    have hbd : ‖virPsi c' (a : ℂ)‖ ≤ virasoroHalfCubic.M_ψ := by
      have h := virasoroHalfCubic.hψ_bd c' (a : ℂ) hc' ha_in
      simpa [virasoroHalfCubic_spec.2.2.2.1] using h
    exact ⟨him, hbd⟩
  · intro a ha
    let T : ℝ → ℝ := fun s => (virV (s : ℂ) (a : ℂ)).re
    let T1 : ℝ → ℝ := fun s => (deriv (fun σ => virV σ (a : ℂ)) (s : ℂ)).re
    have hmem_pairC : ∀ s ∈ Icc (0 : ℝ) (2 * s_cut), ((s : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) R_box := by
      intro s hs
      rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact max_lt (hs.2.trans_lt h2s_lt) (ha.trans ha_lt_R)
    have hmem_pairR : ∀ s ∈ Icc (0 : ℝ) (2 * s_cut), (s, a) ∈ ball ((0 : ℝ), (0 : ℝ)) r1 := by
      intro s hs
      rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hs.1]
      have hR_r1 : R_box ≤ r1 := min_le_left _ _
      exact max_lt (hs.2.trans_lt (h2s_lt.trans_le hR_r1)) (ha.trans (ha_lt_R.trans_le hR_r1))
    have hR_r3 : R_box ≤ r3 := (min_le_right _ _).trans (min_le_left _ _)
    have hR_r5 : R_box ≤ r5 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hT0 : T 0 = 0 := by
      dsimp [T]; simp [virV_eq_mul_virU]
    have hT_props_s : ∀ s ∈ Icc (0 : ℝ) (2 * s_cut), HasDerivAt T (T1 s) s ∧ T1_lo ≤ T1 s ∧ T1 s ≤ T1_hi ∧
        (virV (s : ℂ) (a : ℂ)).im = 0 ∧ (deriv (fun σ => virV σ (a : ℂ)) (s : ℂ)).im = 0 := by
      intro s hs
      have hp3 : ((s : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) r3 := ball_subset_ball hR_r3 (hmem_pairC s hs)
      obtain ⟨_, ⟨hcd2, hcd1, hconj⟩, hd_lo, hd_hi⟩ := hr3_spec _ hp3
      have hV_im : (virV (s : ℂ) (a : ℂ)).im = 0 := by
        rw [← Complex.conj_eq_iff_im]; simpa [Complex.conj_ofReal] using hconj.symm
      have hd_r : HasDerivAt (fun σ : ℝ => virV (σ : ℂ) (a : ℂ))
          (deriv (fun σ : ℂ => virV σ (a : ℂ)) (s : ℂ)) s :=
        ((contDiffAt2_virV_slice hcd2).differentiableAt (by simp)).hasDerivAt.comp_ofReal
      have hT_d : HasDerivAt T (T1 s) s := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd_r
      have hd_im : (deriv (fun σ => virV σ (a : ℂ)) (s : ℂ)).im = 0 := by
        have him_d : HasDerivAt (fun σ : ℝ => (virV (σ : ℂ) (a : ℂ)).im)
            (deriv (fun σ : ℂ => virV σ (a : ℂ)) (s : ℂ)).im s :=
          Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hd_r
        have him_ev : (fun σ : ℝ => (virV (σ : ℂ) (a : ℂ)).im) =ᶠ[𝓝 s] fun _ => 0 := by
          have hball_s : ∀ᶠ σ : ℝ in 𝓝 s, ((σ : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) r3 := by
            have hts : ContinuousAt (fun σ : ℝ => ((σ : ℂ), (a : ℂ))) s := by fun_prop
            exact hts.tendsto.eventually (isOpen_ball.mem_nhds hp3)
          filter_upwards [hball_s] with σ hσ
          have hc := (hr3_spec _ hσ).2.1.2.2
          rw [← Complex.conj_eq_iff_im]; simpa [Complex.conj_ofReal] using hc.symm
        exact him_d.unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq him_ev)
      exact ⟨hT_d, hd_lo, hd_hi, hV_im, hd_im⟩
    have hT_pos : ∀ s ∈ Ioc 0 (2 * s_cut), 0 < T s := by
      intro s hs
      have h1 : ∀ t ∈ Icc (0 : ℝ) s, HasDerivAt T (T1 t) t := fun t ht =>
        (hT_props_s t ⟨ht.1, ht.2.trans hs.2⟩).1
      have h2 : ∀ t ∈ Icc (0 : ℝ) s, T1_lo ≤ T1 t := fun t ht =>
        (hT_props_s t ⟨ht.1, ht.2.trans hs.2⟩).2.1
      have hmv := exists_hasDerivAt_eq_slope T T1 hs.1
        (fun t ht => (h1 t ht).continuousAt.continuousWithinAt)
        (fun t ht => h1 t ⟨ht.1.le, ht.2.le⟩)
      obtain ⟨c, hc, hslope⟩ := hmv
      have hT1c : 0 < T1 c := hT1_lo.trans_le (h2 c ⟨hc.1.le, hc.2.le⟩)
      simp only [hT0, sub_zero] at hslope
      rw [eq_div_iff hs.1.ne'] at hslope
      rw [← hslope]
      exact mul_pos hT1c hs.1
    have hv_lo_cut : v_lo ≤ T s_cut := by
      have hs : s_cut ∈ Icc (0 : ℝ) (2 * s_cut) := ⟨hs_pos.le, by linarith⟩
      have h1 : ∀ t ∈ Icc (0 : ℝ) s_cut, HasDerivAt T (T1 t) t := fun t ht =>
        (hT_props_s t ⟨ht.1, ht.2.trans hs.2⟩).1
      have hmv := exists_hasDerivAt_eq_slope T T1 hs_pos
        (fun t ht => (h1 t ht).continuousAt.continuousWithinAt)
        (fun t ht => h1 t ⟨ht.1.le, ht.2.le⟩)
      obtain ⟨c, hc, hslope⟩ := hmv
      have hcT : T1_lo ≤ T1 c := (hT_props_s c ⟨hc.1.le, hc.2.le.trans hs.2⟩).2.1
      simp only [hT0, sub_zero] at hslope
      rw [eq_div_iff hs_pos.ne'] at hslope
      nlinarith
    have hx4 : (a : ℂ) ∈ ball (0 : ℂ) r4 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha.trans_le ha_lt_r4
    have hx_im : (virXPrime (a : ℂ)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]; simpa [Complex.conj_ofReal] using (hr4_spec _ hx4).2.symm
    have hphi_real : ∀ s ∈ Icc (0 : ℝ) (2 * s_cut),
        phiDual (T s) (virXPrime (a : ℂ)).re = a * s + s ^ 3 / 3 := by
      intro s hs
      have hp3 : ((s : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) r3 := ball_subset_ball hR_r3 (hmem_pairC s hs)
      have hph := (hr3_spec _ hp3).1
      have hV_im := (hT_props_s s hs).2.2.2.1
      have hV_c : virV (s : ℂ) (a : ℂ) = (T s : ℂ) := Complex.ext rfl hV_im
      have hX_c : virXPrime (a : ℂ) = ((virXPrime (a : ℂ)).re : ℂ) := Complex.ext rfl hx_im
      rw [hV_c, hX_c, virPhiDualC_ofReal] at hph
      have hre := congrArg Complex.re hph
      simpa only [Complex.ofReal_re, show ((a : ℂ) * (s : ℂ) + (s : ℂ) ^ 3 / 3).re = a * s + s ^ 3 / 3 by norm_cast]
        using hre
    have hδ_at_cut : δ_lo ≤ (4 * π / 3) * (edgeF (T s_cut) - (virXPrime (a : ℂ)).re) := by
      have hsI : s_cut ∈ Icc (0 : ℝ) (2 * s_cut) := ⟨hs_pos.le, by linarith⟩
      have hT_ev : (fun s : ℝ => phiDual (T s) (virXPrime (a : ℂ)).re) =ᶠ[𝓝 s_cut]
          fun s : ℝ => a * s + s ^ 3 / 3 := by
        have hopen : Ioo (0 : ℝ) (2 * s_cut) ∈ 𝓝 s_cut := Ioo_mem_nhds hs_pos (by linarith)
        filter_upwards [hopen] with s hs_o
        exact hphi_real s ⟨hs_o.1.le, hs_o.2.le⟩
      have hcF : Continuous (fun u : ℝ => edgeF u - (virXPrime (a : ℂ)).re) :=
        (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_edgeF u).continuousAt).sub continuous_const
      have hphi_d : HasDerivAt (fun w : ℝ => phiDual w (virXPrime (a : ℂ)).re)
          ((4 * π / 3) * (edgeF (T s_cut) - (virXPrime (a : ℂ)).re)) (T s_cut) := by
        unfold phiDual
        exact (intervalIntegral.integral_hasDerivAt_right (hcF.intervalIntegrable 0 _)
          (hcF.stronglyMeasurableAtFilter _ _) hcF.continuousAt).const_mul (4 * π / 3)
      have hd1 : HasDerivAt (fun s : ℝ => phiDual (T s) (virXPrime (a : ℂ)).re)
          (((4 * π / 3) * (edgeF (T s_cut) - (virXPrime (a : ℂ)).re)) * T1 s_cut) s_cut :=
        hphi_d.comp s_cut (hT_props_s s_cut hsI).1
      have hd2 : HasDerivAt (fun s : ℝ => a * s + s ^ 3 / 3) (a + s_cut ^ 2) s_cut := by
        have h1 := ((hasDerivAt_id s_cut).const_mul a).add ((hasDerivAt_pow 3 s_cut).div_const 3)
        refine h1.congr_deriv ?_; norm_num
      have heq := (hd1.congr_of_eventuallyEq hT_ev.symm).unique hd2
      have ha_bd : (3 / 4) * s_cut ^ 2 ≤ a + s_cut ^ 2 := by
        have := (abs_lt.mp ha).1; linarith [ha_sq]
      have hT1_le : T1 s_cut ≤ T1_hi := (hT_props_s s_cut hsI).2.2.1
      have hT1_p : 0 < T1 s_cut := hT1_lo.trans_le (hT_props_s s_cut hsI).2.1
      have hfac_pos : 0 ≤ (4 * π / 3) * (edgeF (T s_cut) - (virXPrime (a : ℂ)).re) := by nlinarith
      rw [← heq] at ha_bd
      calc δ_lo = ((3 / 4) * s_cut ^ 2) / T1_hi := rfl
        _ ≤ (((4 * π / 3) * (edgeF (T s_cut) - (virXPrime (a : ℂ)).re)) * T1 s_cut) / T1_hi :=
            div_le_div_of_nonneg_right ha_bd (hT1_lo.trans_le hT1_hi).le
        _ ≤ (4 * π / 3) * (edgeF (T s_cut) - (virXPrime (a : ℂ)).re) := by
            rw [div_le_iff₀ (hT1_lo.trans_le hT1_hi)]; exact mul_le_mul_of_nonneg_left hT1_le hfac_pos
    have hm_th : ∀ s ∈ Ioc 0 (2 * s_cut),
        virThetaOutC (T s : ℂ) = (thetaOut (lowerY (edgeF (T s))) : ℂ) ∧
        virMGeo (s : ℂ) (a : ℂ) =
          (((√(2 * π / 3) * √(edgeF' (T s) / s) * T1 s *
            ((1 - Real.exp (-4 * π * edgeF (T s))) /
              (1 - Real.exp (-4 * π * (virXPrime (a : ℂ)).re))) ^ 2 : ℝ) : ℂ)) := by
      intro s hs
      have hsI : s ∈ Icc (0 : ℝ) (2 * s_cut) := ⟨hs.1.le, hs.2⟩
      have hp5 : ((s : ℂ), (a : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) r5 := ball_subset_ball hR_r5 (hmem_pairC s hsI)
      have hTr2 : T s ∈ ball (0 : ℝ) r2 := by
        simpa [T, Real.dist_eq] using hr5_spec _ hp5
      have hth := hr2_spec (T s) hTr2 (hT_pos s hs).le
      have hm := hr1_spec (s, a) (hmem_pairR s hsI) hs.1
      exact ⟨hth, hm.2.2.2.2.2⟩
    exact ⟨hT0, hT_props_s, hT_pos, hv_lo_cut, hphi_real, hδ_at_cut, hm_th⟩

/-! ### 2. Ray tail between `R_cut = s_cut / lam` and `R_c = d.s₁ / lam` -/

private lemma exp_neg_Rcut_cube_div_four_le {s_cut c' lam : ℝ}
    (hs_cut : 0 < s_cut) (hcpos : 0 < c') (hlam : 0 < lam) (hlc : c' * lam ^ 3 = 1)
    (hRcut1 : 1 ≤ s_cut / lam) :
    Real.exp (-((s_cut / lam) ^ 3 / 4)) ≤ 32 / s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ)) := by
  let R_cut : ℝ := s_cut / lam
  have hx_pos : 0 < R_cut ^ 3 / 4 := by positivity
  have hexp_sq : (R_cut ^ 3 / 4) ^ 2 / 2 < Real.exp (R_cut ^ 3 / 4) := by
    have h2 := Real.sum_le_exp_of_nonneg hx_pos.le 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, pow_one, Nat.factorial_one, Nat.factorial_two] at h2
    norm_num at h2
    linarith
  have hsq_inv : Real.exp (-(R_cut ^ 3 / 4)) ≤ 32 / R_cut ^ 6 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have h1 : (R_cut ^ 3 / 4) ^ 2 / 2 * (32 / R_cut ^ 6) = 1 := by
      have : R_cut ≠ 0 := by positivity
      field_simp; ring
    have h2 := mul_le_mul_of_nonneg_right hexp_sq.le (by positivity : 0 ≤ 32 / R_cut ^ 6)
    linarith
  have hR9 : R_cut ^ (9 / 2 : ℝ) ≤ R_cut ^ 6 := by
    have hle := Real.rpow_le_rpow_of_exponent_le hRcut1 (by norm_num : (9 / 2 : ℝ) ≤ (6 : ℝ))
    rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hle
  have h32 : 32 / R_cut ^ 6 ≤ 32 / R_cut ^ (9 / 2 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hR9
  have hRcut_pow : R_cut ^ (9 / 2 : ℝ) = s_cut ^ (9 / 2 : ℝ) * c' ^ (3 / 2 : ℝ) := by
    have hlam_eq : lam ^ (-1 : ℝ) = c' ^ (1 / 3 : ℝ) := by
      have h1 : (c' ^ (1 / 3 : ℝ)) ^ 3 = c' := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]; norm_num
      have h2 : (lam⁻¹) ^ 3 = c' := by rw [inv_pow]; field_simp [hlam.ne']; linarith
      have h3 : lam⁻¹ = c' ^ (1 / 3 : ℝ) :=
        (pow_left_inj₀ (inv_nonneg.2 hlam.le) (by positivity) (by norm_num : 3 ≠ 0)).mp (h2.trans h1.symm)
      rw [Real.rpow_neg_one]; exact h3
    have hrc_eq : R_cut = s_cut * c' ^ (1 / 3 : ℝ) := by
      dsimp [R_cut]; rw [div_eq_mul_inv, ← Real.rpow_neg_one lam, hlam_eq]
    rw [hrc_eq, Real.mul_rpow hs_cut.le (by positivity), ← Real.rpow_mul hcpos.le]
    congr 1; ring_nf
  rw [hRcut_pow] at h32
  have hdiv : 32 / (s_cut ^ (9 / 2 : ℝ) * c' ^ (3 / 2 : ℝ)) =
      32 / s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_neg hcpos.le]; ring
  linarith [hsq_inv, h32, hdiv]

private lemma fsOpCh_ray_tail_le {d : HalfCubicData} {s_cut c' lam U M_f : ℝ}
    (hs_cut : 0 < s_cut) (hs_le : s_cut ≤ d.s₁) (_hc' : 1 ≤ c') (hlam : 0 < lam) (hlc : c' * lam ^ 3 = 1)
    (hRcut1 : 1 ≤ s_cut / lam) (hRcutR : s_cut / lam < Rs d / lam) (hUcut : CtSd.kap * |U| ≤ (s_cut / lam) ^ 2 / 16)
    (hRc1 : 1 ≤ d.s₁ / lam) (hRcR : d.s₁ / lam < Rs d / lam) (hURc : CtSd.kap * |U| ≤ (d.s₁ / lam) ^ 2 / 16)
    (hMf : 0 ≤ M_f) {f : ℂ → ℂ}
    (hf_c : ContinuousOn f (ball 0 (Rs d / lam)))
    (hf_bd : ∀ w ∈ ball (0 : ℂ) (Rs d / lam), ‖f w‖ ≤ M_f) :
    |fsOpCh (fsChain hRc1 hRcR hURc) U f - fsOpCh (fsChain hRcut1 hRcutR hUcut) U f| ≤
      (128 / (3 * √π * s_cut ^ (9 / 2 : ℝ))) * M_f * c' ^ (-(3 / 2 : ℝ)) := by
  let R_cut : ℝ := s_cut / lam
  let R_c : ℝ := d.s₁ / lam
  let R₀ : ℝ := Rs d / lam
  have hR_le : R_cut ≤ R_c := div_le_div_of_nonneg_right hs_le hlam.le
  let g : ℂ → ℂ := fun w => csr w * f w * Complex.exp (Complex.I * PhU U w)
  have hray_diff : (fsChain hRc1 hRcR hURc).intE U (fun w => csr w * f w) -
      (fsChain hRcut1 hRcutR hUcut).intE U (fun w => csr w * f w) = lineInt 0 d6 R_cut R_c g := by
    unfold Chain3.intE fsChain
    have heq_f : (fun w => csr w * f w * Complex.exp (Complex.I * PhU U w)) = g := rfl
    rw [heq_f]
    by_cases hU : -1 ≤ U
    · simp only [hU, ↓reduceDIte, Chain3.int, chainA, lineInt, Piece.z0, Piece.d, Piece.a, Piece.b,
        intervalIntegral.integral_same, add_zero]
      have hcont_ray : ContinuousOn (fun t : ℝ => g (0 + (t : ℂ) * d6) * d6) (Icc 0 R_c) := by
        have hok := (pieceA_ok (by linarith : (0 : ℝ) ≤ R_c) hRcR).2.1
        have hc_csr : ContinuousOn (fun t : ℝ => csr (0 + (t : ℂ) * d6)) (Icc 0 R_c) := fun t ht =>
          ContinuousAt.comp (f := fun τ : ℝ => (0 : ℂ) + (τ : ℂ) * d6)
            (continuousAt_csr (Or.inl (hok t ht).2)) (by fun_prop) |>.continuousWithinAt
        have hc_f : ContinuousOn (fun t : ℝ => f (0 + (t : ℂ) * d6)) (Icc 0 R_c) :=
          hf_c.comp (by fun_prop) fun t ht => (hok t ht).1
        have hc_exp : ContinuousOn (fun t : ℝ => Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6))) (Icc 0 R_c) := by
          refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
          unfold PhU; fun_prop
        exact ((hc_csr.mul hc_f).mul hc_exp).mul continuousOn_const
      have hi1 : IntervalIntegrable (fun t : ℝ => g (0 + (t : ℂ) * d6) * d6) volume 0 R_cut :=
        (hcont_ray.mono (Icc_subset_Icc_right hR_le)).intervalIntegrable_of_Icc (by linarith)
      have hi2 : IntervalIntegrable (fun t : ℝ => g (0 + (t : ℂ) * d6) * d6) volume R_cut R_c :=
        (hcont_ray.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc hR_le
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      linear_combination -hsplit
    · simp only [hU, ↓reduceDIte, Chain3.int, chainB, lineInt, Piece.z0, Piece.d, Piece.a, Piece.b]
      have hU' : ¬ (-1 ≤ U) := hU
      have hv_eq := fs_chain_v_facts hU' hRc1 hRcR hURc
      have hv_eq2 := fs_chain_v_facts hU' hRcut1 hRcutR hUcut
      have hJv : (1 + Real.sqrt 3) * Real.sqrt (-CtSd.kap * U) ≤ R_cut := hv_eq2.2.2.1
      have hcont_ray : ContinuousOn (fun t : ℝ => g (0 + (t : ℂ) * d6) * d6)
          (Icc ((1 + Real.sqrt 3) * Real.sqrt (-CtSd.kap * U)) R_c) := by
        have hok := (pieceB3_ok hv_eq.1 hv_eq.2.2.1 hRcR).2.1
        have hc_csr : ContinuousOn (fun t : ℝ => csr (0 + (t : ℂ) * d6))
            (Icc ((1 + Real.sqrt 3) * Real.sqrt (-CtSd.kap * U)) R_c) := fun t ht =>
          ContinuousAt.comp (f := fun τ : ℝ => (0 : ℂ) + (τ : ℂ) * d6)
            (continuousAt_csr (Or.inl (hok t ht).2)) (by fun_prop) |>.continuousWithinAt
        have hc_f : ContinuousOn (fun t : ℝ => f (0 + (t : ℂ) * d6))
            (Icc ((1 + Real.sqrt 3) * Real.sqrt (-CtSd.kap * U)) R_c) :=
          hf_c.comp (by fun_prop) fun t ht => (hok t ht).1
        have hc_exp : ContinuousOn (fun t : ℝ => Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6)))
            (Icc ((1 + Real.sqrt 3) * Real.sqrt (-CtSd.kap * U)) R_c) := by
          refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
          unfold PhU; fun_prop
        exact ((hc_csr.mul hc_f).mul hc_exp).mul continuousOn_const
      have hi1 : IntervalIntegrable (fun t : ℝ => g (0 + (t : ℂ) * d6) * d6) volume
          ((1 + Real.sqrt 3) * Real.sqrt (-CtSd.kap * U)) R_cut :=
        (hcont_ray.mono (Icc_subset_Icc_right hR_le)).intervalIntegrable_of_Icc hJv
      have hi2 : IntervalIntegrable (fun t : ℝ => g (0 + (t : ℂ) * d6) * d6) volume R_cut R_c :=
        (hcont_ray.mono (Icc_subset_Icc_left hJv)).intervalIntegrable_of_Icc hR_le
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      linear_combination -hsplit
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hdiff_le : |fsOpCh (fsChain hRc1 hRcR hURc) U f - fsOpCh (fsChain hRcut1 hRcutR hUcut) U f| ≤
      (1 / √π) * ‖lineInt 0 d6 R_cut R_c g‖ := by
    unfold fsOpCh
    have heq : -(1 / √π) * (Complex.exp (Complex.I * (π / 4 : ℝ)) *
          (fsChain hRc1 hRcR hURc).intE U (fun w => csr w * f w)).re -
        -(1 / √π) * (Complex.exp (Complex.I * (π / 4 : ℝ)) *
          (fsChain hRcut1 hRcutR hUcut).intE U (fun w => csr w * f w)).re =
        -(1 / √π) * (Complex.exp (Complex.I * (π / 4 : ℝ)) * lineInt 0 d6 R_cut R_c g).re := by
      rw [← hray_diff, mul_sub, Complex.sub_re]; ring
    rw [heq, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hpi)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |(Complex.exp (Complex.I * (π / 4 : ℝ)) * lineInt 0 d6 R_cut R_c g).re|
        ≤ ‖Complex.exp (Complex.I * (π / 4 : ℝ)) * lineInt 0 d6 R_cut R_c g‖ := Complex.abs_re_le_norm _
      _ = ‖lineInt 0 d6 R_cut R_c g‖ := by
          rw [norm_mul, mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnorm_line : ‖lineInt 0 d6 R_cut R_c g‖ ≤ M_f * ∫ t in R_cut..R_c, t ^ 2 * Real.exp (-(t ^ 3 / 4)) := by
    unfold lineInt
    have hint_rhs : IntervalIntegrable (fun t : ℝ => M_f * (t ^ 2 * Real.exp (-(t ^ 3 / 4)))) volume R_cut R_c :=
      (by fun_prop : Continuous fun t : ℝ => M_f * (t ^ 2 * Real.exp (-(t ^ 3 / 4)))).intervalIntegrable _ _
    refine (intervalIntegral.norm_integral_le_of_norm_le hR_le ?_ hint_rhs).trans_eq (intervalIntegral.integral_const_mul _ _)
    refine Eventually.of_forall fun t ht => ?_
    have ht1 : 1 ≤ t := hRcut1.trans ht.1.le
    have ht0 : 0 ≤ t := by linarith
    have ht_lt_R0 : t < R₀ := ht.2.trans_lt hRcR
    have hpt_ball : 0 + (t : ℂ) * d6 ∈ ball (0 : ℂ) R₀ := by
      rw [mem_ball_zero_iff, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0,
        norm_d6, mul_one]; exact ht_lt_R0
    have hnorm_csr : ‖csr (0 + (t : ℂ) * d6)‖ ≤ t ^ 2 := by
      rw [norm_csr, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, norm_d6, mul_one]
      have : t ^ (1 / 2 : ℝ) ≤ t ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      rwa [← Real.sqrt_eq_rpow, show (t ^ (2 : ℝ)) = t ^ (2 : ℕ) from Real.rpow_natCast t 2] at this
    have him : (PhU U (0 + (t : ℂ) * d6)).im ≥ t ^ 3 / 4 := by
      have h1 : nu * U * t + t ^ 3 / 3 ≤ (PhU U (0 + (t : ℂ) * d6)).im := (im_ray U t).symm.le
      have hU_t : CtSd.kap * |U| ≤ t ^ 2 / 16 := hUcut.trans (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) ht.1.le 2) (by norm_num))
      have hkap_half : -(nu * U * t) ≤ t ^ 3 / 16 := by
        have hnu0 := nu_pos; have hnu1 := nu_le_one; have hk1 := kap_ge_one
        have h1' : -U ≤ |U| := neg_le_abs U
        calc -(nu * U * t) = nu * (-U) * t := by ring
          _ ≤ nu * |U| * t := by gcongr
          _ ≤ 1 * |U| * t := by gcongr
          _ = |U| * t := by ring
          _ ≤ (CtSd.kap * |U|) * t := by
              gcongr; exact le_mul_of_one_le_left (abs_nonneg U) hk1
          _ ≤ (t ^ 2 / 16) * t := mul_le_mul_of_nonneg_right hU_t ht0
          _ = t ^ 3 / 16 := by ring
      linarith [h1, hkap_half, pow_pos (by linarith : 0 < t) 3]
    have hnorm_exp : ‖Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6))‖ ≤ Real.exp (-(t ^ 3 / 4)) := by
      rw [norm_exp_I_mul]; exact Real.exp_le_exp.mpr (by linarith)
    simp only [g, norm_mul, norm_d6, mul_one]
    calc ‖csr (0 + (t : ℂ) * d6)‖ * ‖f (0 + (t : ℂ) * d6)‖ *
          ‖Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6))‖
        ≤ t ^ 2 * M_f * Real.exp (-(t ^ 3 / 4)) := by
          gcongr; exact hf_bd _ hpt_ball
      _ = M_f * (t ^ 2 * Real.exp (-(t ^ 3 / 4))) := by ring
  have hint_exp : ∫ t in R_cut..R_c, t ^ 2 * Real.exp (-(t ^ 3 / 4)) ≤ (4 / 3) * Real.exp (-(R_cut ^ 3 / 4)) := by
    let F : ℝ → ℝ := fun t => -(4 / 3) * Real.exp (-(t ^ 3 / 4))
    have hF_d : ∀ t ∈ uIcc R_cut R_c, HasDerivAt F (t ^ 2 * Real.exp (-(t ^ 3 / 4))) t := fun t _ => by
      have hp : HasDerivAt (fun x : ℝ => -(x ^ 3 / 4)) (-(3 * t ^ 2 / 4)) t :=
        ((hasDerivAt_pow 3 t).div_const 4).neg
      exact ((hp.exp).const_mul (-(4 / 3))).congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF_d
      ((by fun_prop : Continuous fun t : ℝ => t ^ 2 * Real.exp (-(t ^ 3 / 4))).intervalIntegrable R_cut R_c)]
    dsimp [F]
    have hpos : 0 ≤ (4 / 3 : ℝ) * Real.exp (-(R_c ^ 3 / 4)) := by positivity
    linarith
  have hexp_poly : Real.exp (-(R_cut ^ 3 / 4)) ≤ 32 / s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ)) :=
    exp_neg_Rcut_cube_div_four_le hs_cut (by linarith) hlam hlc hRcut1
  calc |fsOpCh (fsChain hRc1 hRcR hURc) U f - fsOpCh (fsChain hRcut1 hRcutR hUcut) U f|
      ≤ (1 / √π) * ‖lineInt 0 d6 R_cut R_c g‖ := hdiff_le
    _ ≤ (1 / √π) * (M_f * ∫ t in R_cut..R_c, t ^ 2 * Real.exp (-(t ^ 3 / 4))) := by gcongr
    _ ≤ (1 / √π) * (M_f * ((4 / 3) * Real.exp (-(R_cut ^ 3 / 4)))) := by gcongr
    _ ≤ (1 / √π) * (M_f * ((4 / 3) * (32 / s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ))))) := by gcongr
    _ = (128 / (3 * √π * s_cut ^ (9 / 2 : ℝ))) * M_f * c' ^ (-(3 / 2 : ℝ)) := by ring

/-! ### 3. Core head-segment-tail saddle match for `virasoroKedgeEps` and `virasoroKedge1Eps` -/

private lemma virSaddle_head_seg_join (p : VirSaddlePack)
    {d_hc : HalfCubicData} {W_fac : ℂ → ℂ} {Bamp : ℝ → ℝ → ℂ}
    {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hd_psi : d_hc.ψ = virasoroHalfCubic.ψ)
    (hd_B : ∀ n a s, 1 ≤ n → a ∈ ball (0 : ℂ) d_hc.r_a → ‖s‖ < virRsIn / 2 →
      d_hc.B n a s = virPhaseFactor s a * W_fac (virV s a) * virEb n s a)
    (hBamp_eq : ∀ ε v, 0 ≤ v → Bamp ε v = kedgeAmp0 ε v * W_fac (v : ℂ))
    (hBamp_d : ∀ {ε : ℝ}, ε ∈ Ioo 0 (1 / 2) → ∀ v : ℝ, 0 < v → DifferentiableAt ℝ (Bamp ε) v)
    {c' a : ℝ} (hc1 : 1 ≤ c') (hc2 : 2 ≤ c') (ha : |a| < p.a_cut)
    (ha_hc_mem : (a : ℂ) ∈ ball (0 : ℂ) d_hc.r_a)
    {rr : ℝ} (hrr : 0 < rr) (_hrr1 : 1 ≤ rr)
    (hlam_pos : 0 < c' ^ (-(1 / 3 : ℝ)))
    (hlam2 : (c' ^ (-(1 / 3 : ℝ))) ^ 2 = c' ^ (-(2 / 3 : ℝ)))
    (hlam3 : (c' ^ (-(1 / 3 : ℝ))) ^ 3 = c'⁻¹)
    (hlc : c' * (c' ^ (-(1 / 3 : ℝ))) ^ 3 = 1)
    (hRcut1 : 1 ≤ p.s_cut / c' ^ (-(1 / 3 : ℝ)))
    (hrr2 : rr ^ 2 = p.s_cut / c' ^ (-(1 / 3 : ℝ)))
    (hsR : p.s_cut = c' ^ (-(1 / 3 : ℝ)) * rr ^ 2)
    (hRcut_lt : rr ^ 2 < 2 * rr ^ 2) (hRcut1_rr : 1 ≤ rr ^ 2)
    (hRcut_pow9 : 1 / rr ^ 9 = p.s_cut ^ (-(9 / 2 : ℝ)) * c' ^ (-(3 / 2 : ℝ)))
    (hRcut_pow3 : 1 / rr ^ 3 ≤ p.s_cut ^ (-(3 / 2 : ℝ)))
    {Ua : ℝ} (hUa_eq : a = CtSd.kap * Ua * (c' ^ (-(1 / 3 : ℝ))) ^ 2)
    (hUa_cut : CtSd.kap * |Ua| ≤ (rr ^ 2) ^ 2 / 16)
    (hu_cut : CtSd.kap * |d_hc.uReal c' a| ≤ (rr ^ 2) ^ 2 / 16)
    {gs : ℂ → ℂ}
    (hgs_eq : ∀ z : ℂ, gs z = virPhaseFactor z (a : ℂ) * W_fac (virV z (a : ℂ)) * virEb c' z (a : ℂ) *
      Complex.exp (Complex.I * z * d_hc.ψ c' (a : ℂ)))
    (hgs_diff : DifferentiableOn ℂ gs (ball 0 (3 * p.s_cut)))
    (hgs_bd : ∀ z ∈ ball (0 : ℂ) (3 * p.s_cut), ‖gs z‖ ≤ Cb)
    {C_scale : ℂ}
    (hCscale_eq : C_scale = Complex.exp (Complex.I * (π : ℂ) / 4) *
      (((√(2 * c' / 3) * (1 - Real.exp (-(4 * π * (virXPrime (a : ℂ)).re))) ^ (-2 : ℝ) : ℝ)) : ℂ))
    (h1exp_pos : 0 < 1 - Real.exp (-(4 * π * (virXPrime (a : ℂ)).re)))
    (hε_mem : c' ^ (-2 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2))
    {F1 F2 : ℝ → ℂ}
    (hOscB : OscAmpBound p.v_lo (Bamp (c' ^ (-2 : ℝ))) F1 F2)
    (hint_Ioc : IntegrableOn (fun v => (C_scale * Bamp (c' ^ (-2 : ℝ)) v) *
      Complex.exp (Complex.I * ((c' * phiDual v (virXPrime (a : ℂ)).re : ℝ) : ℂ)))
      (Ioc 0 (virV (p.s_cut : ℂ) (a : ℂ)).re)) :
    ∃ R_head : ℂ,
      (∫ τ in (0 : ℝ)..(virV (p.s_cut : ℂ) (a : ℂ)).re,
        (C_scale * Bamp (c' ^ (-2 : ℝ)) τ) *
          Complex.exp (Complex.I * ((c' * phiDual τ (virXPrime (a : ℂ)).re : ℝ) : ℂ))) +
      (-(1 / (Complex.I * (c' : ℂ))) * ((C_scale * Bamp (c' ^ (-2 : ℝ)) (virV (p.s_cut : ℂ) (a : ℂ)).re) /
          (((4 * π / 3) * (edgeF (virV (p.s_cut : ℂ) (a : ℂ)).re - (virXPrime (a : ℂ)).re) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((c' * phiDual (virV (p.s_cut : ℂ) (a : ℂ)).re (virXPrime (a : ℂ)).re : ℝ) : ℂ))) +
        (1 / (Complex.I * (c' : ℂ))) ^ 2 *
          (ibpH (fun τ => C_scale * Bamp (c' ^ (-2 : ℝ)) τ) (fun τ => C_scale * F1 τ)
            (fun v => (4 * π / 3) * (edgeF v - (virXPrime (a : ℂ)).re))
            (fun v => (4 * π / 3) * edgeF' v) (virV (p.s_cut : ℂ) (a : ℂ)).re /
            (((4 * π / 3) * (edgeF (virV (p.s_cut : ℂ) (a : ℂ)).re - (virXPrime (a : ℂ)).re) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((c' * phiDual (virV (p.s_cut : ℂ) (a : ℂ)).re (virXPrime (a : ℂ)).re : ℝ) : ℂ)))) =
      (((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ))) *
        (fsChain hRcut1_rr hRcut_lt hu_cut).intE (d_hc.uReal c' a)
          (fun w => csr w * d_hc.B c' a (((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * w)) + R_head ∧
      ‖R_head‖ ≤ (1 / √π) * ((16 * (2 * Cb) / p.s_cut ^ (3 / 2 : ℝ) +
        1024 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ)) * (32 / p.s_cut ^ (9 / 2 : ℝ)) +
        320000 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ)) * c' ^ (-(3 / 2 : ℝ)) := by
  let lam := c' ^ (-(1 / 3 : ℝ))
  let u := d_hc.uReal c' a
  let x' := (virXPrime (a : ℂ)).re
  let T : ℝ → ℝ := fun s => (virV (s : ℂ) (a : ℂ)).re
  let T1 : ℝ → ℝ := fun s => (deriv (fun σ => virV σ (a : ℂ)) (s : ℂ)).re
  let v₁ := T p.s_cut
  let B_τ : ℝ → ℂ := fun v => C_scale * Bamp (c' ^ (-2 : ℝ)) v
  let B_τ' : ℝ → ℂ := fun v => C_scale * F1 v
  let ϕ1 : ℝ → ℝ := fun v => (4 * π / 3) * (edgeF v - x')
  let ϕ2 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF' v
  let ch_cut : Chain3 (2 * rr ^ 2) (((rr ^ 2 : ℝ) : ℂ) * d6) := fsChain hRcut1_rr hRcut_lt hu_cut
  have hcpos : 0 < c' := by linarith only [hc1]
  obtain ⟨hT0, hT_s, hTpos, hv_lo_cut, hphi_real, _, hm_th⟩ := p.hT_props ha
  let Nc : ℂ := ((√(c' / π) : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ))
  let N1 : ℂ := ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ))
  have hNc : Nc * ((lam * Real.sqrt lam : ℝ) : ℂ) = N1 := by
    have hsq : Real.sqrt c' * (lam * Real.sqrt lam) = 1 := by
      have h1 : lam * Real.sqrt lam = Real.sqrt (lam ^ 3) := by
        rw [show lam ^ 3 = lam ^ 2 * lam by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hlam_pos.le]
      rw [h1, ← Real.sqrt_mul hcpos.le, hlc, Real.sqrt_one]
    have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
    have hre_id : (√(c' / π)) * (lam * √lam) = 1 / √π := by
      rw [Real.sqrt_div hcpos.le, div_mul_eq_mul_div, mul_comm (√c'), mul_assoc]
      field_simp [hpi.ne']; linarith [hsq]
    dsimp [Nc, N1]
    calc ((√(c' / π) : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) * ((lam * √lam : ℝ) : ℂ)
        = (((√(c' / π) * (lam * √lam) : ℝ)) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by push_cast; ring
      _ = _ := by rw [hre_id]
  have hBT : ∀ s ∈ Ioc (0 : ℝ) (2 * p.s_cut), B_τ (T s) * ((T1 s : ℝ) : ℂ) = Nc * csr (s : ℂ) * gs (s : ℂ) := by
    intro s hs
    have hs_box : s ∈ Ioc 0 (2 * p.s_cut) := hs
    have hsI : s ∈ Icc 0 (2 * p.s_cut) := ⟨hs_box.1.le, hs_box.2⟩
    have hTs_pos : 0 < T s := hTpos s hs_box
    have hV_im := (hT_s s hsI).2.2.2.1
    have hT1_lo := (hT_s s hsI).2.1
    have hT1_pos : 0 < T1 s := p.hT1_lo.trans_le hT1_lo
    obtain ⟨hth_eq, hmgeo_eq⟩ := hm_th s hs_box
    have hV_c : virV (s : ℂ) (a : ℂ) = (T s : ℂ) := Complex.ext rfl hV_im
    have hy_c : yVirC (virV (s : ℂ) (a : ℂ)) = (lowerY (edgeF (T s)) : ℂ) := by
      rw [hV_c]; exact yVirC_ofReal_nonneg hTs_pos.le
    have hψ_im : (d_hc.ψ c' (a : ℂ)).im = 0 := by
      rw [hd_psi, virasoroHalfCubic_spec.2.2.2.1]; exact (p.hψ_bd hc1 ha).1
    have hExp_cancel : Complex.exp (Complex.I * (virThetaOutC (virV (s : ℂ) (a : ℂ)) - (s : ℂ) * virPsi 0 (a : ℂ))) *
        Complex.exp (-Complex.I * (s : ℂ) * (virPsi c' (a : ℂ) - virPsi 0 (a : ℂ))) *
        Complex.exp (Complex.I * (s : ℂ) * d_hc.ψ c' (a : ℂ)) =
        Complex.exp (Complex.I * (thetaOut (lowerY (edgeF (T s))) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, hV_c, hth_eq, hd_psi, virasoroHalfCubic_spec.2.2.2.1]
      congr 1; ring
    have hcsr_s : csr (s : ℂ) = (√s : ℂ) := by
      unfold csr
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hs.1.le, Real.sqrt_eq_rpow]
    have hsqrt_F' : √s * √(edgeF' (T s) / s) = √(edgeF' (T s)) := by
      rw [Real.sqrt_div (edgeF'_pos hTs_pos).le, mul_comm, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hs.1).ne']
    have hsqrt_c : √(c' / π) * √(2 * π / 3) = √(2 * c' / 3) := by
      rw [← Real.sqrt_mul (div_nonneg hcpos.le Real.pi_pos.le)]
      congr 1; field_simp [Real.pi_pos.ne']
    have hgs_eq_s : gs (s : ℂ) = virMGeo (s : ℂ) (a : ℂ) * W_fac (T s : ℂ) *
        lowerMt (c' ^ (-2 : ℝ)) (Complex.I * (lowerY (edgeF (T s)) : ℂ)) ^ 2 *
        Complex.exp (Complex.I * (thetaOut (lowerY (edgeF (T s))) : ℂ)) := by
      rw [hgs_eq (s : ℂ)]
      unfold virPhaseFactor virEb
      simp only [hc2, ↓reduceIte]
      rw [hy_c, hV_c]
      calc (virMGeo (s : ℂ) (a : ℂ) * Complex.exp (Complex.I * (virThetaOutC (T s : ℂ) - (s : ℂ) * virPsi 0 (a : ℂ)))) *
            W_fac (T s : ℂ) *
            (lowerMt (c' ^ (-2 : ℝ)) (Complex.I * (lowerY (edgeF (T s)) : ℂ)) ^ 2 *
              Complex.exp (-Complex.I * (s : ℂ) * (virPsi c' (a : ℂ) - virPsi 0 (a : ℂ)))) *
            Complex.exp (Complex.I * (s : ℂ) * d_hc.ψ c' (a : ℂ))
          = virMGeo (s : ℂ) (a : ℂ) * W_fac (T s : ℂ) *
              lowerMt (c' ^ (-2 : ℝ)) (Complex.I * (lowerY (edgeF (T s)) : ℂ)) ^ 2 *
              (Complex.exp (Complex.I * (virThetaOutC (virV (s : ℂ) (a : ℂ)) - (s : ℂ) * virPsi 0 (a : ℂ))) *
                Complex.exp (-Complex.I * (s : ℂ) * (virPsi c' (a : ℂ) - virPsi 0 (a : ℂ))) *
                Complex.exp (Complex.I * (s : ℂ) * d_hc.ψ c' (a : ℂ))) := by rw [hV_c]; ring
        _ = _ := by rw [hExp_cancel]
    rw [hgs_eq_s, hmgeo_eq, hcsr_s]
    dsimp [Nc, B_τ]
    rw [hBamp_eq _ (T s) hTs_pos.le, hCscale_eq]
    unfold kedgeAmp0
    have hpow : (1 - Real.exp (-(4 * π * x'))) ^ (-2 : ℝ) = ((1 - Real.exp (-(4 * π * x'))) ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1exp_pos.le, Real.rpow_natCast]
    have hpi4 : Complex.I * (π : ℂ) / 4 = Complex.I * ((π / 4 : ℝ) : ℂ) := by push_cast; ring
    have hreal_id : √(2 * c' / 3) * ((1 - Real.exp (-(4 * π * x'))) ^ 2)⁻¹ *
        (1 - Real.exp (-(4 * π * edgeF (T s)))) ^ 2 * √(edgeF' (T s)) * T1 s =
        √(c' / π) * √s * (√(2 * π / 3) * √(edgeF' (T s) / s) * T1 s *
          ((1 - Real.exp (-(4 * π * edgeF (T s)))) / (1 - Real.exp (-(4 * π * x')))) ^ 2) := by
      rw [div_pow, ← hsqrt_c, ← hsqrt_F']; ring
    have hpow_neg_num : -4 * π * edgeF (T s) = -(4 * π * edgeF (T s)) := by ring
    have hpow_neg_den : -4 * π * x' = -(4 * π * x') := by ring
    calc (Complex.exp (Complex.I * (π : ℂ) / 4) *
            (((√(2 * c' / 3) * (1 - Real.exp (-(4 * π * x'))) ^ (-2 : ℝ) : ℝ)) : ℂ)) *
            (lowerMt (c' ^ (-2 : ℝ)) (Complex.I * (lowerY (edgeF (T s)) : ℂ)) ^ 2 *
            Complex.exp (Complex.I * (thetaOut (lowerY (edgeF (T s))) : ℂ)) *
            ((((1 - Real.exp (-(4 * π * edgeF (T s)))) ^ 2 * √(edgeF' (T s)) : ℝ) : ℂ)) *
            W_fac (T s : ℂ)) * ((T1 s : ℝ) : ℂ)
        = (Complex.exp (Complex.I * ((π / 4 : ℝ) : ℂ)) *
            (((√(2 * c' / 3) * ((1 - Real.exp (-(4 * π * x'))) ^ 2)⁻¹ *
              (1 - Real.exp (-(4 * π * edgeF (T s)))) ^ 2 * √(edgeF' (T s)) * T1 s : ℝ) : ℂ))) *
            W_fac (T s : ℂ) * lowerMt (c' ^ (-2 : ℝ)) (Complex.I * (lowerY (edgeF (T s)) : ℂ)) ^ 2 *
            Complex.exp (Complex.I * (thetaOut (lowerY (edgeF (T s))) : ℂ)) := by
          dsimp [x']; rw [hpi4, hpow]; push_cast; ring
      _ = (((√(c' / π) : ℝ) : ℂ) * Complex.exp (Complex.I * ((π / 4 : ℝ) : ℂ))) * (√s : ℂ) *
            ((((√(2 * π / 3) * √(edgeF' (T s) / s) * T1 s *
              ((1 - Real.exp (-4 * π * edgeF (T s))) / (1 - Real.exp (-4 * π * x'))) ^ 2 : ℝ) : ℂ)) *
              W_fac (T s : ℂ) * lowerMt (c' ^ (-2 : ℝ)) (Complex.I * (lowerY (edgeF (T s)) : ℂ)) ^ 2 *
              Complex.exp (Complex.I * (thetaOut (lowerY (edgeF (T s))) : ℂ))) := by
          rw [hpow_neg_num, hpow_neg_den, hreal_id]; push_cast; ring
  have hT_c : ContinuousOn T (Icc 0 p.s_cut) := fun s hs =>
    (hT_s s ⟨hs.1, hs.2.trans (by linarith only [p.hs_pos])⟩).1.continuousAt.continuousWithinAt
  have hgsc : ContinuousOn (fun s : ℝ => gs (s : ℂ)) (Icc 0 p.s_cut) := by
    intro s hs
    have hmem : (s : ℂ) ∈ ball (0 : ℂ) (3 * p.s_cut) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      linarith only [hs.2, p.hs_pos]
    exact ((hgs_diff.continuousOn.continuousAt (isOpen_ball.mem_nhds hmem)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  let F_s : ℝ → ℂ := fun s =>
    Nc * csr (s : ℂ) * gs (s : ℂ) * Complex.exp (Complex.I * c' * ((a * s + s ^ 3 / 3 : ℝ) : ℂ))
  have hpt : ∀ s ∈ Ioc (0 : ℝ) p.s_cut, ((T1 s : ℝ) : ℂ) *
      (B_τ (T s) * Complex.exp (Complex.I * ((c' * phiDual (T s) x' : ℝ) : ℂ))) = F_s s := by
    intro s hs
    have hsI : s ∈ Icc 0 (2 * p.s_cut) := ⟨hs.1.le, hs.2.trans (by linarith only [p.hs_pos])⟩
    have hs2 : s ∈ Ioc (0 : ℝ) (2 * p.s_cut) := ⟨hs.1, hs.2.trans (by linarith only [p.hs_pos])⟩
    dsimp [F_s]
    rw [hphi_real s hsI, ← hBT s hs2]
    push_cast; ring
  have hFs_c : ContinuousOn F_s (Icc 0 p.s_cut) := by
    refine ((continuousOn_const.mul ?_).mul hgsc).mul ?_
    · intro s hs
      exact ((continuousAt_csr (Or.inl (by simpa using hs.1))).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · exact Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn (by fun_prop)))
  have hhead_g_c : ContinuousOn (fun τ : ℝ => B_τ τ * Complex.exp (Complex.I * ((c' * phiDual τ x' : ℝ) : ℂ))) (Ioi 0) := by
    have hphi_c : Continuous (fun τ : ℝ => phiDual τ x') := by
      have hcF : Continuous (fun u : ℝ => edgeF u - x') :=
        (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_edgeF u).continuousAt).sub continuous_const
      unfold phiDual
      exact continuous_const.mul (intervalIntegral.continuous_primitive (fun a b => hcF.intervalIntegrable a b) 0)
    have hBc : ContinuousOn (Bamp (c' ^ (-2 : ℝ))) (Ioi 0) := fun v hv =>
      (hBamp_d hε_mem v hv).continuousAt.continuousWithinAt
    have hexp_c : Continuous fun τ : ℝ => Complex.exp (Complex.I * ((c' * phiDual τ x' : ℝ) : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul hphi_c)))
    exact (continuousOn_const.mul hBc).mul hexp_c.continuousOn
  have hF_subst_int : IntegrableOn (fun s => ((T1 s : ℝ) : ℂ) *
      (B_τ (T s) * Complex.exp (Complex.I * ((c' * phiDual (T s) x' : ℝ) : ℂ)))) (Icc 0 p.s_cut) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc (by exact eNorm_ne_top)]
    exact (hFs_c.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      (fun s hs => (hpt s hs).symm) measurableSet_Ioc
  have hsubst := subst_head p.hs_pos
    (fun s hs => (hT_s s ⟨hs.1, hs.2.trans (by linarith only [p.hs_pos])⟩).1)
    (fun s hs => p.hT1_lo.trans_le (hT_s s ⟨hs.1, hs.2.trans (by linarith only [p.hs_pos])⟩).2.1)
    hT0 hhead_g_c hint_Ioc hF_subst_int
  have hhead_int_Fs : ∫ τ in (0 : ℝ)..v₁, B_τ τ * Complex.exp (Complex.I * ((c' * phiDual τ x' : ℝ) : ℂ)) =
      N1 * lineInt 0 1 0 (rr ^ 2) (fun w => csr w * gs ((lam : ℂ) * w) * Complex.exp (Complex.I * PhU Ua w)) := by
    have h1 : ∫ s in (0 : ℝ)..p.s_cut, ((T1 s : ℝ) : ℂ) *
        (B_τ (T s) * Complex.exp (Complex.I * ((c' * phiDual (T s) x' : ℝ) : ℂ))) =
        ∫ s in (0 : ℝ)..p.s_cut, F_s s := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
      rw [uIoc_of_le p.hs_pos.le] at hs; exact hpt s hs
    have h4 : ∫ s in (0 : ℝ)..p.s_cut, F_s s = (lam : ℂ) * ∫ w in (0 : ℝ)..(rr ^ 2), F_s (lam * w) := by
      have h3 := intervalIntegral.integral_comp_mul_left (c := lam) (a := 0) (b := rr ^ 2) F_s hlam_pos.ne'
      rw [mul_zero, ← hsR, Complex.real_smul] at h3
      rw [h3, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam_pos.ne', Complex.ofReal_one, one_mul]
    rw [← hsubst, h1, h4]
    unfold lineInt
    have hlcC : (c' : ℂ) * (lam : ℂ) ^ 3 = 1 := by exact_mod_cast hlc
    have h5 : ∀ w ∈ Set.uIcc (0 : ℝ) (rr ^ 2), (lam : ℂ) * F_s (lam * w) =
        N1 * (csr (0 + (w : ℂ) * 1) * gs ((lam : ℂ) * (0 + (w : ℂ) * 1)) *
          Complex.exp (Complex.I * PhU Ua (0 + (w : ℂ) * 1)) * 1) := by
      intro w hw
      rw [uIcc_of_le (sq_nonneg rr)] at hw
      simp only [F_s, zero_add, mul_one]
      rw [csr_mul_ofReal hlam_pos.le hw.1, Complex.ofReal_mul, ← hNc]
      have hexp : Complex.I * (c' : ℂ) * (((a * (lam * w) + (lam * w) ^ 3 / 3 : ℝ)) : ℂ) =
          Complex.I * PhU Ua (w : ℂ) := by
        unfold PhU; rw [hUa_eq]; push_cast
        linear_combination (Complex.I * ((CtSd.kap : ℂ) * Ua * w + (w : ℂ) ^ 3 / 3)) * hlcC
      rw [hexp]; push_cast; ring
    calc (lam : ℂ) * ∫ w in (0 : ℝ)..(rr ^ 2), F_s (lam * w)
        = ∫ w in (0 : ℝ)..(rr ^ 2), (lam : ℂ) * F_s (lam * w) := (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ w in (0 : ℝ)..(rr ^ 2), N1 * (csr (0 + (w : ℂ) * 1) * gs ((lam : ℂ) * (0 + (w : ℂ) * 1)) *
          Complex.exp (Complex.I * PhU Ua (0 + (w : ℂ) * 1)) * 1) := intervalIntegral.integral_congr h5
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hRcut_pos : 0 < rr ^ 2 := by positivity
  have hR₀cut_pos : 0 < 2 * rr ^ 2 := by positivity
  have hdiffG : DifferentiableOn ℂ (fun w => gs ((lam : ℂ) * w) * Complex.exp (Complex.I * PhU Ua w))
      (ball 0 (2 * rr ^ 2)) := by
    intro w hw
    have hwn : ‖w‖ < 2 * rr ^ 2 := by simpa using hw
    have hmem : (lam : ℂ) * w ∈ ball (0 : ℂ) (3 * p.s_cut) := by
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos]
      calc lam * ‖w‖ < lam * (2 * rr ^ 2) := mul_lt_mul_of_pos_left hwn hlam_pos
        _ = 2 * p.s_cut := by rw [hsR]; ring
        _ < 3 * p.s_cut := by linarith only [p.hs_pos]
    have h1 : DifferentiableAt ℂ gs ((lam : ℂ) * w) := (hgs_diff _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => gs ((lam : ℂ) * w)) w := h1.comp w (by fun_prop)
    have h3 : DifferentiableAt ℂ (fun w => Complex.exp (Complex.I * PhU Ua w)) w := by unfold PhU; fun_prop
    exact (h2.mul h3).differentiableWithinAt
  have hdef := deform_real hR₀cut_pos hRcut_lt hRcut_pos hdiffG ch_cut
  let gW : ℂ → ℂ := fun w => gs ((lam : ℂ) * w)
  let gW1 : ℂ → ℂ := fun w => (lam : ℂ) * deriv gs ((lam : ℂ) * w)
  let gW2 : ℂ → ℂ := fun w => (lam : ℂ) ^ 2 * deriv (deriv gs) ((lam : ℂ) * w)
  have hgdat := fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
    gW_data p.hs_pos hlam_pos hsR hgs_diff hgs_bd (norm_segPt_le hRcut_pos.le ht.1 ht.2)
  have hdd2 : ContinuousOn (deriv (deriv gs)) (ball 0 (3 * p.s_cut)) :=
    ((hgs_diff.deriv isOpen_ball).deriv isOpen_ball).continuousOn
  have hc2seg : ContinuousOn (fun t : ℝ => gW2 (segPt (rr ^ 2) t)) (Icc 0 1) := by
    have hpt : Continuous fun t : ℝ => (lam : ℂ) * segPt (rr ^ 2) t := by simp only [segPt_eq]; fun_prop
    refine continuousOn_const.mul (hdd2.comp hpt.continuousOn fun t ht => ?_)
    have hpt_bd := norm_segPt_le hRcut_pos.le ht.1 ht.2
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos]
    calc lam * ‖segPt (rr ^ 2) t‖ ≤ lam * (rr ^ 2) := mul_le_mul_of_nonneg_left hpt_bd hlam_pos.le
      _ = p.s_cut := hsR.symm
      _ < 3 * p.s_cut := by linarith only [p.hs_pos]
  have hCb_le2 : Cb ≤ 2 * Cb := by linarith only [hCb]
  have hrr4 : (rr ^ 2) ^ 2 = rr ^ 4 := by rw [← pow_mul]
  obtain ⟨hsegEq, hsegNorm⟩ := seg_rem (U := Ua) (ρ := rr) (Cg := 2 * Cb) (gW := gW) (gW1 := gW1) (gW2 := gW2)
    hrr (by linarith only [hCb] : 0 ≤ 2 * Cb) hUa_cut (fun t ht => (hgdat t ht).1) (fun t ht => (hgdat t ht).2.1) hc2seg
    (fun t ht => (hgdat t ht).2.2.1.trans hCb_le2) (fun t ht => (hgdat t ht).2.2.2.1)
    (fun t ht => by have := (hgdat t ht).2.2.2.2; rwa [hrr4] at this)
  rw [segZ0_add_segD] at hsegEq
  have hs_in_box : p.s_cut ∈ Icc 0 (2 * p.s_cut) := ⟨p.hs_pos.le, by linarith only [p.hs_pos]⟩
  have hs_in_Ioo : p.s_cut ∈ Ioo (p.s_cut / 2) (2 * p.s_cut) := ⟨by linarith only [p.hs_pos], by linarith only [p.hs_pos]⟩
  have hne_Ioo : ∀ s ∈ Ioo (p.s_cut / 2) (2 * p.s_cut), a + s ^ 2 ≠ 0 := fun s hs => by
    have h1 : (p.s_cut / 2) ^ 2 < s ^ 2 := pow_lt_pow_left₀ hs.1 (half_pos p.hs_pos).le (by norm_num)
    have h2 := (abs_lt.mp ha).1
    have h3 := p.ha_sq
    nlinarith only [h1, h2, h3]
  have hgs_d1 : HasDerivAt gs (deriv gs (p.s_cut : ℂ)) (p.s_cut : ℂ) := by
    have hmem : (p.s_cut : ℂ) ∈ ball (0 : ℂ) (3 * p.s_cut) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos p.hs_pos]
      linarith only [p.hs_pos]
    exact ((hgs_diff _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
  obtain ⟨hba, hbb⟩ := head_bdry (c := c') (lam := lam) (R := rr ^ 2) (s1 := p.s_cut) (a := a) (U := Ua)
    (Nc := Nc) (N1 := N1) (g' := deriv gs (p.s_cut : ℂ)) (gs := gs) (gW := gW) (gW1 := gW1)
    hcpos hlam_pos hlc hRcut_pos hsR hUa_eq hNc (hne_Ioo p.s_cut hs_in_Ioo)
    (by change gs ((lam : ℂ) * ((rr ^ 2 : ℝ) : ℂ)) = gs (p.s_cut : ℂ); congr 1; rw [hsR]; push_cast; ring)
    (by change (lam : ℂ) * deriv gs ((lam : ℂ) * ((rr ^ 2 : ℝ) : ℂ)) = (lam : ℂ) * deriv gs (p.s_cut : ℂ)
        congr 3; rw [hsR]; push_cast; ring)
  have hrho := hasDerivAt_rhoS (Nc := Nc) p.hs_pos (hne_Ioo p.s_cut hs_in_Ioo) hgs_d1
  have hϕ_v : ∀ τ : ℝ, 0 < τ → HasDerivAt (fun w : ℝ => phiDual w x') (ϕ1 τ) τ := fun τ _ => by
    have hcF : Continuous (fun w : ℝ => edgeF w - x') :=
      (continuous_iff_continuousAt.mpr fun w => (hasDerivAt_edgeF w).continuousAt).sub continuous_const
    unfold phiDual; dsimp [ϕ1]
    exact (intervalIntegral.integral_hasDerivAt_right (hcF.intervalIntegrable 0 τ)
      (hcF.stronglyMeasurableAtFilter _ _) hcF.continuousAt).const_mul (4 * π / 3)
  have hϕ1_v : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ1 (ϕ2 τ) τ := fun τ _ => by
    dsimp [ϕ1, ϕ2]; exact ((hasDerivAt_edgeF τ).sub_const x').const_mul (4 * π / 3)
  obtain ⟨B1_ext, hB1_ext_v1, hB_tau_d⟩ :
      ∃ B1_ext : ℝ → ℂ, B1_ext v₁ = B_τ' v₁ ∧ ∀ τ : ℝ, 0 < τ → HasDerivAt B_τ (B1_ext τ) τ := by
    refine ⟨fun τ => if p.v_lo ≤ τ then B_τ' τ else deriv B_τ τ, ?_, fun τ hτ => ?_⟩
    · dsimp only
      split_ifs with h
      · rfl
      · exact False.elim (h hv_lo_cut)
    · by_cases hle : p.v_lo ≤ τ
      · simp only [hle, ↓reduceIte]
        exact (hOscB.hd1 τ hle).const_mul C_scale
      · simp only [hle, ↓reduceIte]
        exact ((hBamp_d hε_mem τ hτ).const_mul C_scale).hasDerivAt
  have htb := tail_bdry (a := a) (sl := p.s_cut / 2) (s1 := p.s_cut) (s1' := 2 * p.s_cut)
    (T := T) (T1 := T1) (B := B_τ) (B1 := B1_ext)
    (Φ := fun s : ℝ => Nc * csr (s : ℂ) * gs (s : ℂ)) (ρ := rhoS Nc gs a)
    (ϕ := fun w => phiDual w x') (ϕ1 := ϕ1) (ϕ2 := ϕ2)
    (ρ' := rhoS' Nc gs (deriv gs (p.s_cut : ℂ)) a p.s_cut) hs_in_Ioo
    (fun s hs => (hT_s s ⟨by linarith only [hs.1, p.hs_pos], hs.2.le⟩).1)
    (fun s hs => p.hT1_lo.trans_le (hT_s s ⟨by linarith only [hs.1, p.hs_pos], hs.2.le⟩).2.1)
    (fun s hs => hTpos s ⟨by linarith only [hs.1, p.hs_pos], hs.2.le⟩)
    hϕ_v hB_tau_d hϕ1_v
    (fun s hs => hBT s ⟨by linarith only [hs.1, p.hs_pos], hs.2.le⟩)
    (fun s hs => hphi_real s ⟨by linarith only [hs.1, p.hs_pos], hs.2.le⟩) hne_Ioo
    (fun s hs => by
      show Nc * csr (s : ℂ) * gs (s : ℂ) = rhoS Nc gs a s * ((a + s ^ 2 : ℝ) : ℂ)
      unfold rhoS; have hneC : ((a + s ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne_Ioo s hs)
      field_simp) hrho
  obtain ⟨htb1, htb2⟩ := htb
  have hibpH_v1 : ibpH B_τ B1_ext ϕ1 ϕ2 v₁ = ibpH B_τ B_τ' ϕ1 ϕ2 v₁ := by
    unfold ibpH; rw [hB1_ext_v1]
  rw [hibpH_v1] at htb2
  have hlcC : (c' : ℂ) * (lam : ℂ) ^ 3 = 1 := by exact_mod_cast hlc
  have hexp1 : Complex.exp (Complex.I * PhU Ua ((rr ^ 2 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ)) := by
    congr 1; dsimp [v₁]; rw [hphi_real p.s_cut hs_in_box]; unfold PhU; rw [hUa_eq, hsR]; push_cast
    linear_combination (-(Complex.I * ((CtSd.kap : ℂ) * (Ua : ℂ) * (rr : ℂ) ^ 2 + ((rr : ℂ) ^ 2) ^ 3 / 3))) * hlcC
  have hexpU : ∀ w ∈ ball (0 : ℂ) (3 * p.s_cut / lam),
      gs ((lam : ℂ) * w) * Complex.exp (Complex.I * PhU Ua w) =
      d_hc.B c' a ((lam : ℂ) * w) * Complex.exp (Complex.I * PhU u w) := by
    intro w hw
    have hw_lt : ‖(lam : ℂ) * w‖ < virRsIn / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos]
      have h1 : ‖w‖ < 3 * p.s_cut / lam := mem_ball_zero_iff.mp hw
      have h2 := mul_lt_mul_of_pos_left h1 hlam_pos
      rw [mul_div_cancel₀ _ hlam_pos.ne'] at h2
      exact h2.trans p.h3s_lt
    rw [hd_B c' (a : ℂ) ((lam : ℂ) * w) hc1 ha_hc_mem hw_lt, hgs_eq ((lam : ℂ) * w)]
    have hPh : Complex.I * ((lam : ℂ) * w) * d_hc.ψ c' (a : ℂ) + Complex.I * PhU Ua w = Complex.I * PhU u w := by
      unfold PhU
      have hψ_im : (d_hc.ψ c' (a : ℂ)).im = 0 := by
        rw [hd_psi, virasoroHalfCubic_spec.2.2.2.1]; exact (p.hψ_bd hc1 ha).1
      have hψ_eq : d_hc.ψ c' (a : ℂ) = (((d_hc.ψ c' (a : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hψ_im
      have hu_rel : CtSd.kap * u * lam ^ 2 = a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re := by
        dsimp [u, HalfCubicData.uReal, HalfCubicData.aHat]
        rw [hlam2]
        simp only [CtSd.kap, CtAiry.kap, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
        have h2eq : (2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) = 1 := by
          rw [← Real.rpow_add zero_lt_two]; norm_num
        have hceq : c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = 1 := by
          rw [← Real.rpow_add hcpos]; norm_num
        calc (2 : ℝ) ^ (2 / 3 : ℝ) * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c' ^ (2 / 3 : ℝ) *
              (a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re)) * c' ^ (-(2 / 3 : ℝ))
            = ((2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ))) * (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) *
                (a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re) := by ring
          _ = a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re := by rw [h2eq, hceq, one_mul, one_mul]
      have hsub : ((CtSd.kap : ℂ) * (u : ℂ) - (CtSd.kap : ℂ) * (Ua : ℂ)) = (lam : ℂ) * d_hc.ψ c' (a : ℂ) := by
        rw [hψ_eq]
        have h1 : lam ^ 2 * (CtSd.kap * u - CtSd.kap * Ua - lam * (d_hc.ψ c' (a : ℂ)).re) = 0 := by
          have h3 : lam ^ 3 = c'⁻¹ := hlam3
          have hUa_eq' : a = CtSd.kap * Ua * lam ^ 2 := hUa_eq
          linear_combination hu_rel + hUa_eq' - (d_hc.ψ c' (a : ℂ)).re * h3
        have h2 : CtSd.kap * u - CtSd.kap * Ua = lam * (d_hc.ψ c' (a : ℂ)).re := by
          have := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hlam_pos.ne')
          linarith only [this]
        exact_mod_cast h2
      linear_combination (Complex.I * w) * (-hsub)
    rw [mul_assoc (virPhaseFactor _ _ * _ * _), ← Complex.exp_add, hPh]
  have hpiece_congr : ∀ (q : Piece), q.Ok (2 * rr ^ 2) →
      lineInt q.z0 q.d q.a q.b (fun w => csr w * gW w * Complex.exp (Complex.I * PhU Ua w)) =
        lineInt q.z0 q.d q.a q.b (fun w => csr w * d_hc.B c' a ((lam : ℂ) * w) * Complex.exp (Complex.I * PhU u w)) := by
    intro q hq
    unfold lineInt
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hq.1] at ht
    have hm : q.z0 + (t : ℂ) * q.d ∈ ball (0 : ℂ) (3 * p.s_cut / lam) := by
      have h1 : ‖q.z0 + (t : ℂ) * q.d‖ < 2 * rr ^ 2 := mem_ball_zero_iff.mp (hq.2.1 t ht).1
      have h2 : 2 * rr ^ 2 < 3 * p.s_cut / lam := by
        rw [hrr2]
        change 2 * (p.s_cut / lam) < 3 * p.s_cut / lam
        rw [← mul_div_assoc]
        exact div_lt_div_of_pos_right (by linarith only [p.hs_pos]) hlam_pos
      exact mem_ball_zero_iff.mpr (h1.trans h2)
    have he := hexpU (q.z0 + (t : ℂ) * q.d) hm
    dsimp [gW]; rw [mul_assoc (csr _), he]; ring
  have hch_eq : ch_cut.int (fun w => csr w * gW w * Complex.exp (Complex.I * PhU Ua w)) =
      ch_cut.intE u (fun w => csr w * d_hc.B c' a ((lam : ℂ) * w)) := by
    dsimp only [Chain3.int, Chain3.intE]
    simp only [hpiece_congr ch_cut.q1 ch_cut.ok1, hpiece_congr ch_cut.q2 ch_cut.ok2,
      hpiece_congr ch_cut.q3 ch_cut.ok3]
  set chint := ch_cut.intE u (fun w => csr w * d_hc.B c' a ((lam : ℂ) * w))
  set e1 := Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))
  set P1 := csrF gW ((rr ^ 2 : ℝ) : ℂ) / (Complex.I * CtSd.GG Ua ((rr ^ 2 : ℝ) : ℂ))
  set Hq1 := segH (csrF gW) (csrF1 gW gW1) (CtSd.GG Ua) GG1 ((rr ^ 2 : ℝ) : ℂ) /
    (Complex.I * CtSd.GG Ua ((rr ^ 2 : ℝ) : ℂ))
  set z0 : ℂ := segZ0 (rr ^ 2) + ((0 : ℝ) : ℂ) * segD (rr ^ 2)
  set P0 := csrF gW z0 / (Complex.I * CtSd.GG Ua z0)
  set Hq0 := segH (csrF gW) (csrF1 gW gW1) (CtSd.GG Ua) GG1 z0 / (Complex.I * CtSd.GG Ua z0)
  set e0 := Complex.exp (Complex.I * PhU Ua z0)
  set Qseg := lineInt (segZ0 (rr ^ 2)) (segD (rr ^ 2)) 0 1 (fun z => segQ (csrF gW) (csrF1 gW gW1)
    (csrF2 gW gW1 gW2) (CtSd.GG Ua) GG1 GG2 z * Complex.exp (Complex.I * PhU Ua z))
  have hhead_full : ∫ τ in (0 : ℝ)..v₁, B_τ τ * Complex.exp (Complex.I * ((c' * phiDual τ x' : ℝ) : ℂ)) =
      N1 * (chint + ((P1 * e1 - P0 * e0) - 1 / Complex.I * (Hq1 * e1 - Hq0 * e0) +
        (1 / Complex.I) ^ 2 * Qseg)) := by
    have hdef' : lineInt 0 1 0 (rr ^ 2) (fun w => csr w * gW w * Complex.exp (Complex.I * PhU Ua w)) =
        chint + ((P1 * e1 - P0 * e0) - 1 / Complex.I * (Hq1 * e1 - Hq0 * e0) + (1 / Complex.I) ^ 2 * Qseg) := by
      have h1 : lineInt 0 1 0 (rr ^ 2) (fun w => csr w * gW w * Complex.exp (Complex.I * PhU Ua w)) =
          ch_cut.int (fun w => csr w * gW w * Complex.exp (Complex.I * PhU Ua w)) +
            lineInt (segZ0 (rr ^ 2)) (segD (rr ^ 2)) 0 1
              (fun w => csr w * gW w * Complex.exp (Complex.I * PhU Ua w)) := by
        have hdef' := hdef
        simp only [gW, mul_assoc] at hdef' ⊢
        exact hdef'
      rw [h1, hch_eq, hsegEq, hexp1]
    exact hhead_int_Fs.trans (by rw [← hdef'])
  let R_head : ℂ := -(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qseg)
  refine ⟨R_head, ?_, ?_⟩
  · rw [hhead_full]
    linear_combination e1 * hba - e1 * hbb - (1 / (Complex.I * (c' : ℂ))) * e1 * htb1 +
      (1 / (Complex.I * (c' : ℂ))) ^ 2 * e1 * htb2
  · have hN1n : ‖N1‖ = 1 / √π := by
      dsimp [N1]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_I_mul_ofReal,
        mul_one, abs_of_pos (by positivity)]
    have hI1 : ‖(1 : ℂ) / Complex.I‖ = 1 := by simp
    have hCg0 : 0 ≤ 2 * Cb := by linarith only [hCb]
    obtain ⟨hd1, hd2, hd3, hd4, _⟩ := hgdat 0 ⟨le_rfl, zero_le_one⟩
    have hbd0 := norm_seg_bdry_le (U := Ua) (ρ := rr) (t := 0) (gW := gW) (gW1 := gW1) hrr le_rfl zero_le_one
      hCg0 hUa_cut (hd3.trans (by linarith only [hCb])) hd4
    have he0_exp : ‖e0‖ ≤ 32 / p.s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ)) := by
      have hIm := im_PhU_segPt (U := Ua) (R := rr ^ 2) (t := 0) hRcut_pos.le le_rfl zero_le_one hUa_cut
      have hseg0 : segPt (rr ^ 2) 0 = z0 := rfl
      rw [hseg0] at hIm
      have he : ‖e0‖ = Real.exp (-(PhU Ua z0).im) := norm_exp_I_mul _
      rw [he]
      have hRcut1' : 1 ≤ p.s_cut / lam := hRcut1
      have h_im_le : -(PhU Ua z0).im ≤ -((rr ^ 2) ^ 3 / 4) := by
        have h1 : (rr ^ 2) ^ 3 / 4 ≤ rr ^ 2 / 2 * (29 * (rr ^ 2) ^ 2 / 48) * (1 - 0) := by
          have : 0 ≤ (rr ^ 2) ^ 3 := by positivity
          nlinarith only [this]
        linarith only [h1, hIm]
      have hexp_cut : Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ 32 / p.s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ)) := by
        rw [hrr2]; exact exp_neg_Rcut_cube_div_four_le p.hs_pos hcpos hlam_pos hlc hRcut1'
      exact (Real.exp_le_exp.mpr h_im_le).trans hexp_cut
    have ht1 : ‖-(N1 * (P0 * e0))‖ ≤ (1 / √π) * ((16 * (2 * Cb) / p.s_cut ^ (3 / 2 : ℝ)) *
        (32 / p.s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ)))) := by
      rw [norm_neg, norm_mul, hN1n, norm_mul]
      have hP0' : ‖P0‖ ≤ 16 * (2 * Cb) / p.s_cut ^ (3 / 2 : ℝ) := by
        calc ‖P0‖ ≤ 16 * (2 * Cb) / rr ^ 3 := hbd0.1
          _ = 16 * (2 * Cb) * (1 / rr ^ 3) := by ring
          _ ≤ 16 * (2 * Cb) * p.s_cut ^ (-(3 / 2 : ℝ)) := by gcongr
          _ = 16 * (2 * Cb) / p.s_cut ^ (3 / 2 : ℝ) := by rw [Real.rpow_neg p.hs_pos.le, ← div_eq_mul_inv]
      have hP0_nn : 0 ≤ 16 * (2 * Cb) / p.s_cut ^ (3 / 2 : ℝ) :=
        div_nonneg (mul_nonneg (by norm_num) hCg0) (Real.rpow_nonneg p.hs_pos.le _)
      exact mul_le_mul_of_nonneg_left (mul_le_mul hP0' he0_exp (norm_nonneg _) hP0_nn) (by positivity)
    have ht2 : ‖N1 * (1 / Complex.I * (Hq0 * e0))‖ ≤ (1 / √π) * ((1024 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ)) *
        (32 / p.s_cut ^ (9 / 2 : ℝ) * c' ^ (-(3 / 2 : ℝ)))) := by
      rw [norm_mul, hN1n, norm_mul, norm_mul, hI1, one_mul]
      have hHq0' : ‖Hq0‖ ≤ 1024 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ) := by
        have hc_le : c' ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
        have h9nn : 0 ≤ p.s_cut ^ (-(9 / 2 : ℝ)) := Real.rpow_nonneg p.hs_pos.le _
        calc ‖Hq0‖ ≤ 1024 * (2 * Cb) / rr ^ 9 := hbd0.2
          _ = 1024 * (2 * Cb) * (1 / rr ^ 9) := by ring
          _ = 1024 * (2 * Cb) * (p.s_cut ^ (-(9 / 2 : ℝ)) * c' ^ (-(3 / 2 : ℝ))) := by rw [hRcut_pow9]
          _ ≤ 1024 * (2 * Cb) * (p.s_cut ^ (-(9 / 2 : ℝ)) * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc_le h9nn) (mul_nonneg (by norm_num) hCg0)
          _ = 1024 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ) := by
              rw [mul_one, Real.rpow_neg p.hs_pos.le, ← div_eq_mul_inv]
      have hHq0_nn : 0 ≤ 1024 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ) :=
        div_nonneg (mul_nonneg (by norm_num) hCg0) (Real.rpow_nonneg p.hs_pos.le _)
      exact mul_le_mul_of_nonneg_left (mul_le_mul hHq0' he0_exp (norm_nonneg _) hHq0_nn) (by positivity)
    have ht3 : ‖N1 * ((1 / Complex.I) ^ 2 * Qseg)‖ ≤
        (1 / √π) * (320000 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ)) * c' ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul, hN1n, norm_mul, norm_pow, hI1, one_pow, one_mul]
      calc (1 / √π) * ‖Qseg‖ ≤ (1 / √π) * (320000 * (2 * Cb) / rr ^ 9) := by gcongr
        _ = (1 / √π) * (320000 * (2 * Cb) * (1 / rr ^ 9)) := by ring
        _ = (1 / √π) * (320000 * (2 * Cb) * (p.s_cut ^ (-(9 / 2 : ℝ)) * c' ^ (-(3 / 2 : ℝ)))) := by rw [hRcut_pow9]
        _ = (1 / √π) * (320000 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ)) * c' ^ (-(3 / 2 : ℝ)) := by
            rw [Real.rpow_neg p.hs_pos.le, div_eq_mul_inv]; ring
    dsimp [R_head]
    refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
    linarith only [ht1, ht2, ht3]

private lemma virasoro_kedge_saddle_core (p : VirSaddlePack)
    {d_hc : HalfCubicData} {W_fac : ℂ → ℂ} {Bamp : ℝ → ℝ → ℂ} {M_W : ℝ}
    (hM_W : 0 ≤ M_W)
    (hd_ra : d_hc.r_a = virasoroHalfCubic.r_a)
    (hd_s1 : d_hc.s₁ = virasoroHalfCubic.s₁)
    (hd_psi : d_hc.ψ = virasoroHalfCubic.ψ)
    (hd_B : ∀ n a s, 1 ≤ n → a ∈ ball (0 : ℂ) d_hc.r_a → ‖s‖ < virRsIn / 2 →
      d_hc.B n a s = virPhaseFactor s a * W_fac (virV s a) * virEb n s a)
    (hBamp_eq : ∀ ε v, 0 ≤ v → Bamp ε v = kedgeAmp0 ε v * W_fac (v : ℂ))
    (hW_s : ∀ a ∈ ball (0 : ℂ) virPoly.r_a, DifferentiableOn ℂ (fun ζ => W_fac (virV ζ a)) (ball 0 virPoly.r_s))
    (hW_bd : ∀ ζ ∈ ball (0 : ℂ) virPoly.r_s, ∀ a ∈ ball (0 : ℂ) virPoly.r_a, ‖W_fac (virV ζ a)‖ ≤ M_W)
    (hBamp_d : ∀ {ε : ℝ}, ε ∈ Ioo 0 (1 / 2) → ∀ v : ℝ, 0 < v → DifferentiableAt ℝ (Bamp ε) v)
    (hOsc : ∃ K0 K1 K2 L1 L2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      ∀ {ε : ℝ}, ε ∈ Ioo 0 (1 / 2) → ∃ F1 F2 : ℝ → ℂ, ∃ h : OscAmpBound p.v_lo (Bamp ε) F1 F2,
        h.HasConsts K0 K1 K2 L1 L2)
    (hInt_real : ∀ {c' ε x' : ℝ}, 0 < c' → ε ∈ Ioo 0 (1 / 2) → xiStar / 2 ≤ x' →
      IntegrableOn (fun v => kedgeEpsIntegrand c' ε x' v * W_fac (v : ℂ)) (Ioi 0)) :
    ∃ c₀ C_ext : ℝ, 2 ≤ c₀ ∧ d_hc.n₀ ≤ c₀ ∧ 0 ≤ C_ext ∧
      ∀ {c' a : ℝ}, c₀ ≤ c' → |a| < p.a_cut →
        let lam := c' ^ (-(1 / 3 : ℝ))
        let R_c := d_hc.s₁ / lam
        let R₀ := Rs d_hc / lam
        let u := d_hc.uReal c' a
        ∀ (hR1 : 1 ≤ R_c) (hRR : R_c < R₀) (hUR : CtSd.kap * |u| ≤ R_c ^ 2 / 16),
        |-(√(2 * c' / 3)) * (Complex.exp (Complex.I * (π : ℂ) / 4) *
              ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) (virXPrime (a : ℂ)).re v *
                W_fac (v : ℂ)).re -
          fsOpCh (fsChain hR1 hRR hUR) u (fun w => d_hc.B c' a ((lam : ℂ) * w))| ≤
          C_ext * c' ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨K0, K1, K2, L1, L2, hK0, hK1, hK2, hL1, hL2, hOsc_spec⟩ := hOsc
  let c₀ : ℝ := max 2 (max d_hc.n₀ (max (p.s_cut⁻¹ ^ 3) (32 * p.M_ψ / p.s_cut ^ 2 + 1)))
  have hc₀2 : 2 ≤ c₀ := le_max_left _ _
  have hc₀n : d_hc.n₀ ≤ c₀ := (le_max_left d_hc.n₀ _).trans (le_max_right (2 : ℝ) _)
  let Cb : ℝ := virPoly.M_G0 * M_W * (1 + virPoly.K_b) * Real.exp (3 * p.s_cut * p.M_ψ)
  have hCb : 0 ≤ Cb := by
    have := virPoly.hMG0; have := virPoly.hKb; positivity
  let denomMin : ℝ := 1 - Real.exp (-(4 * π * (xiStar / 2)))
  have hdenom_pos : 0 < denomMin := by
    dsimp [denomMin]; rw [sub_pos, Real.exp_lt_one_iff]
    have := Real.pi_pos; have := xiStar_pos; nlinarith
  let scaleMax : ℝ := √(2 / 3) * denomMin ^ (-2 : ℝ)
  let tailQ : ℝ := L2 / p.δ_lo ^ 2 + (3 / 2 : ℝ) * K1 / p.δ_lo ^ 2 +
    (1 / 2 : ℝ) * K0 * ((2 * π) / edgeF' p.v_lo) / p.δ_lo ^ 2 +
    (4 * π / 3) * K0 / p.δ_lo ^ 3
  have hF'v0 : 0 < edgeF' p.v_lo := edgeF'_pos p.hv_pos
  have htailQ_nn : 0 ≤ tailQ := by have := p.hδ_pos; dsimp [tailQ]; positivity
  let C_seg : ℝ := (1 / √π) * ((16 * (2 * Cb) / p.s_cut ^ (3 / 2 : ℝ) +
    1024 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ)) * (32 / p.s_cut ^ (9 / 2 : ℝ)) +
    320000 * (2 * Cb) / p.s_cut ^ (9 / 2 : ℝ))
  let C_tail : ℝ := scaleMax * tailQ
  let M_B : ℝ := d_hc.M_E + Rs d_hc * d_hc.M_O
  have hMB_nn : 0 ≤ M_B := add_nonneg d_hc.hM_E (mul_nonneg (Real.sqrt_nonneg _) d_hc.hM_O)
  let C_ray : ℝ := (128 / (3 * √π * p.s_cut ^ (9 / 2 : ℝ))) * M_B
  refine ⟨c₀, C_seg + C_tail + C_ray, hc₀2, hc₀n, by
    have := p.hs_pos; have := Real.sqrt_pos.mpr Real.pi_pos; dsimp [C_seg, C_tail, C_ray, scaleMax]; positivity, ?_⟩
  intro c' a hc' ha lam R_c R₀ u hRc1 hRcR hURc
  have hc2 : 2 ≤ c' := hc₀2.trans hc'
  have hc1 : 1 ≤ c' := by linarith
  have hcpos : 0 < c' := by linarith
  have hcn0 : d_hc.n₀ ≤ c' := hc₀n.trans hc'
  have hε_pos : 0 < c' ^ (-2 : ℝ) := Real.rpow_pos_of_pos hcpos _
  have hε_le : c' ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hcpos.le, Real.rpow_natCast,
      one_div, inv_le_inv₀ (by positivity) (by norm_num)]
    nlinarith
  have hε_mem : c' ^ (-2 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hε_pos, by linarith⟩
  obtain ⟨hlam_pos, hlam_le1, hlam2, hlam3, _, _, _⟩ := rpow_lam_rels hc1
  have hlc : c' * lam ^ 3 = 1 := by
    dsimp [lam]; rw [hlam3, mul_inv_cancel₀ hcpos.ne']
  have hcs : p.s_cut⁻¹ ^ 3 ≤ c' :=
    ((le_max_left (p.s_cut⁻¹ ^ 3) _).trans ((le_max_right d_hc.n₀ _).trans (le_max_right (2 : ℝ) _))).trans hc'
  have hRcut1 : 1 ≤ p.s_cut / lam := by
    rw [le_div_iff₀ hlam_pos, one_mul]
    have h1 : lam ^ 3 ≤ p.s_cut ^ 3 := by
      rw [hlam3]
      have hinv := (inv_le_inv₀ hcpos (pow_pos (inv_pos.mpr p.hs_pos) 3)).mpr hcs
      simpa [inv_pow] using hinv
    exact (pow_le_pow_iff_left₀ hlam_pos.le p.hs_pos.le (by norm_num : 3 ≠ 0)).mp h1
  let rr : ℝ := Real.sqrt (p.s_cut / lam)
  have hrr : 0 < rr := Real.sqrt_pos.mpr (by linarith)
  have hrr1 : 1 ≤ rr := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hRcut1
  have hrr2 : rr ^ 2 = p.s_cut / lam := Real.sq_sqrt (by positivity)
  have hsR : p.s_cut = lam * rr ^ 2 := by rw [hrr2, mul_div_cancel₀ _ hlam_pos.ne']
  have hRcut_lt : rr ^ 2 < 2 * rr ^ 2 := by linarith [pow_pos hrr 2]
  have hs_le_d : p.s_cut ≤ d_hc.s₁ := by rw [hd_s1]; linarith [p.hs_lt_s1, virasoroHalfCubic.hs₁]
  have hRcut_Rc : rr ^ 2 ≤ R_c := by rw [hrr2]; exact div_le_div_of_nonneg_right hs_le_d hlam_pos.le
  have hRcut_R₀ : rr ^ 2 < R₀ := hRcut_Rc.trans_lt hRcR
  have hRcut_pow9 : 1 / rr ^ 9 = p.s_cut ^ (-(9 / 2 : ℝ)) * c' ^ (-(3 / 2 : ℝ)) := by
    have hrc_eq : rr ^ 2 = p.s_cut * c' ^ (1 / 3 : ℝ) := by
      have hl : lam⁻¹ = c' ^ (1 / 3 : ℝ) := by
        have h1 : (c' ^ (1 / 3 : ℝ)) ^ 3 = c' := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]; norm_num
        have h2 : (lam⁻¹) ^ 3 = c' := by
          rw [inv_pow, inv_eq_iff_eq_inv]
          have h1' : c' * lam ^ 3 = 1 := hlc
          exact eq_inv_of_mul_eq_one_right h1'
        exact (pow_left_inj₀ (inv_nonneg.2 hlam_pos.le) (by positivity) (by norm_num : 3 ≠ 0)).mp (h2.trans h1.symm)
      rw [hrr2, div_eq_mul_inv, hl]
    have hrr9 : rr ^ 9 = (rr ^ 2) ^ (9 / 2 : ℝ) := by
      rw [← Real.rpow_natCast rr 2, ← Real.rpow_mul hrr.le]; norm_num
    rw [hrr9, hrc_eq, Real.mul_rpow p.hs_pos.le (by positivity), ← Real.rpow_mul hcpos.le]
    rw [show (1 / 3 : ℝ) * (9 / 2 : ℝ) = 3 / 2 by norm_num]
    rw [one_div, mul_inv, ← Real.rpow_neg p.hs_pos.le, ← Real.rpow_neg hcpos.le]
  have hRcut_pow3 : 1 / rr ^ 3 ≤ p.s_cut ^ (-(3 / 2 : ℝ)) := by
    have hrr3 : rr ^ 3 = (rr ^ 2) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast rr 2, ← Real.rpow_mul hrr.le]; norm_num
    have h1 : p.s_cut ^ (3 / 2 : ℝ) ≤ (rr ^ 2) ^ (3 / 2 : ℝ) := by
      refine Real.rpow_le_rpow p.hs_pos.le ?_ (by norm_num)
      rw [hrr2, le_div_iff₀ hlam_pos]
      calc p.s_cut * lam ≤ p.s_cut * 1 := mul_le_mul_of_nonneg_left hlam_le1 p.hs_pos.le
        _ = p.s_cut := mul_one _
    rw [hrr3, one_div, Real.rpow_neg p.hs_pos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos p.hs_pos _) h1
  have hk0 : 0 < CtSd.kap := kap_pos
  let Ua : ℝ := a / (CtSd.kap * lam ^ 2)
  have hUa_eq : a = CtSd.kap * Ua * lam ^ 2 := by
    dsimp [Ua]
    have hden_ne : CtSd.kap * lam ^ 2 ≠ 0 := mul_ne_zero hk0.ne' (pow_ne_zero 2 hlam_pos.ne')
    calc a = (a / (CtSd.kap * lam ^ 2)) * (CtSd.kap * lam ^ 2) := (div_mul_cancel₀ a hden_ne).symm
      _ = CtSd.kap * (a / (CtSd.kap * lam ^ 2)) * lam ^ 2 := by ring
  have hMψ_cut : c'⁻¹ * p.M_ψ ≤ p.s_cut ^ 2 / 32 := by
    have hcψ : 32 * p.M_ψ / p.s_cut ^ 2 + 1 ≤ c' :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
    have h1 : 32 * p.M_ψ / p.s_cut ^ 2 ≤ c' := by linarith only [hcψ]
    rw [div_le_iff₀ (sq_pos_of_pos p.hs_pos)] at h1
    rw [inv_mul_eq_div, div_le_div_iff₀ hcpos (by norm_num : (0 : ℝ) < 32)]
    nlinarith only [h1]
  have hUa_cut : CtSd.kap * |Ua| ≤ (rr ^ 2) ^ 2 / 16 := by
    have hden : 0 < CtSd.kap * lam ^ 2 := mul_pos hk0 (pow_pos hlam_pos 2)
    have h1 : CtSd.kap * |Ua| * lam ^ 2 = |a| := by
      dsimp [Ua]; rw [abs_div, abs_of_pos hden]
      calc CtSd.kap * (|a| / (CtSd.kap * lam ^ 2)) * lam ^ 2
          = (|a| / (CtSd.kap * lam ^ 2)) * (CtSd.kap * lam ^ 2) := by ring
        _ = |a| := div_mul_cancel₀ _ hden.ne'
    have ha16 : |a| ≤ p.s_cut ^ 2 / 16 := by linarith only [p.ha_sq, ha.le, sq_nonneg p.s_cut]
    rw [hsR] at ha16
    have h2 : (CtSd.kap * |Ua|) * lam ^ 2 ≤ ((rr ^ 2) ^ 2 / 16) * lam ^ 2 := by
      rw [h1]
      calc |a| ≤ (lam * rr ^ 2) ^ 2 / 16 := ha16
        _ = ((rr ^ 2) ^ 2 / 16) * lam ^ 2 := by ring
    exact le_of_mul_le_mul_right h2 (pow_pos hlam_pos 2)
  have hu_cut : CtSd.kap * |u| ≤ (rr ^ 2) ^ 2 / 16 := by
    have hψ_im : (d_hc.ψ c' (a : ℂ)).im = 0 := by
      rw [hd_psi, virasoroHalfCubic_spec.2.2.2.1]; exact (p.hψ_bd hc1 ha).1
    have hψ_nm : ‖d_hc.ψ c' (a : ℂ)‖ ≤ p.M_ψ := by
      rw [hd_psi, virasoroHalfCubic_spec.2.2.2.1]; exact (p.hψ_bd hc1 ha).2
    have hu_rel : CtSd.kap * u * lam ^ 2 = a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re := by
      dsimp [u, HalfCubicData.uReal, HalfCubicData.aHat]
      rw [hlam2]
      simp only [CtSd.kap, CtAiry.kap, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
      have h2eq : (2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add zero_lt_two]; norm_num
      have hceq : c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add hcpos]; norm_num
      calc (2 : ℝ) ^ (2 / 3 : ℝ) * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c' ^ (2 / 3 : ℝ) * (a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re)) *
            c' ^ (-(2 / 3 : ℝ))
          = ((2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (-(2 / 3 : ℝ))) * (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) *
              (a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re) := by ring
        _ = a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re := by rw [h2eq, hceq, one_mul, one_mul]
    have h1 : CtSd.kap * |u| * lam ^ 2 = |a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re| := by
      have h2 := congrArg abs hu_rel
      rw [abs_mul, abs_mul, abs_of_pos hk0, abs_of_pos (sq_pos_of_pos hlam_pos)] at h2
      exact h2
    have h2 : |a + c'⁻¹ * (d_hc.ψ c' (a : ℂ)).re| ≤ p.s_cut ^ 2 / 16 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
      have hre : |(d_hc.ψ c' (a : ℂ)).re| ≤ p.M_ψ := (Complex.abs_re_le_norm _).trans hψ_nm
      have ha32 : |a| ≤ p.s_cut ^ 2 / 32 := ha.le.trans p.ha_sq
      have hpm : c'⁻¹ * |(d_hc.ψ c' (a : ℂ)).re| ≤ p.s_cut ^ 2 / 32 :=
        (mul_le_mul_of_nonneg_left hre (inv_nonneg.mpr hcpos.le)).trans hMψ_cut
      linarith
    rw [hsR] at h2; rw [← h1] at h2
    have h3 : (CtSd.kap * |u|) * lam ^ 2 ≤ ((rr ^ 2) ^ 2 / 16) * lam ^ 2 := by
      calc CtSd.kap * |u| * lam ^ 2 ≤ (lam * rr ^ 2) ^ 2 / 16 := h2
        _ = ((rr ^ 2) ^ 2 / 16) * lam ^ 2 := by ring
    exact le_of_mul_le_mul_right h3 (pow_pos hlam_pos 2)
  have hRcut1_rr : 1 ≤ rr ^ 2 := by rwa [hrr2]
  have hu_cut_d : CtSd.kap * |u| ≤ (p.s_cut / lam) ^ 2 / 16 := by rwa [← hrr2]
  have hRcut_R0_d : p.s_cut / lam < Rs d_hc / lam := by rwa [← hrr2]
  -- Define `ch_cut` in `ball 0 (2 * rr^2)` (where `lam * 2 * rr^2 = 2 * s_cut`) and `ch_cut_d` in `ball 0 R₀`
  let ch_cut : Chain3 (2 * rr ^ 2) (((rr ^ 2 : ℝ) : ℂ) * d6) := fsChain hRcut1_rr hRcut_lt hu_cut
  let ch_cut_d : Chain3 R₀ (((p.s_cut / lam : ℝ) : ℂ) * d6) := fsChain hRcut1 hRcut_R0_d hu_cut_d
  have hch_congr : fsOpCh ch_cut u (fun w => d_hc.B c' a ((lam : ℂ) * w)) =
      fsOpCh ch_cut_d u (fun w => d_hc.B c' a ((lam : ℂ) * w)) := by
    dsimp [ch_cut, ch_cut_d]
    unfold fsOpCh Chain3.intE fsChain
    split_ifs <;> simp [Chain3.int, chainA, chainB, lineInt, hrr2]
  -- Complex symbol `gs` on `ball 0 (3 * p.s_cut)`
  let gs : ℂ → ℂ := fun z =>
    virPhaseFactor z (a : ℂ) * W_fac (virV z (a : ℂ)) * virEb c' z (a : ℂ) *
      Complex.exp (Complex.I * z * d_hc.ψ c' (a : ℂ))
  have ha_poly_mem : (a : ℂ) ∈ ball (0 : ℂ) virPoly.r_a := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ha.trans_le p.ha_poly
  have ha_hc_mem : (a : ℂ) ∈ ball (0 : ℂ) d_hc.r_a := by
    rw [hd_ra, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact ha.trans_le (p.ha_shrunk.trans virasoroHalfCubic.rAShrunk_lt.le)
  have hgs_diff : DifferentiableOn ℂ gs (ball 0 (3 * p.s_cut)) := by
    have hsub : ball (0 : ℂ) (3 * p.s_cut) ⊆ ball (0 : ℂ) virPoly.r_s := ball_subset_ball p.h3s_poly.le
    refine ((((virPoly.hG_s _ ha_poly_mem).mono hsub).mul ((hW_s _ ha_poly_mem).mono hsub)).mul
      ((virPoly.hEb_s c' hc1 _ ha_poly_mem).mono hsub)).mul ?_
    exact Complex.differentiable_exp.comp_differentiableOn
      ((differentiableOn_id.const_mul Complex.I).mul_const _)
  have hgs_bd : ∀ z ∈ ball (0 : ℂ) (3 * p.s_cut), ‖gs z‖ ≤ Cb := by
    intro z hz
    have hz_poly : z ∈ ball (0 : ℂ) virPoly.r_s := ball_subset_ball p.h3s_poly.le hz
    have hG := virPoly.hG_bd z hz_poly (a : ℂ) ha_poly_mem
    have hW := hW_bd z hz_poly (a : ℂ) ha_poly_mem
    have hEb : ‖virEb c' z (a : ℂ)‖ ≤ 1 + virPoly.K_b := by
      have h1 := virPoly.hEb_bd c' z (a : ℂ) hc1 hz_poly ha_poly_mem
      have hcinv : c'⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      have hkb : virPoly.K_b * c'⁻¹ ≤ virPoly.K_b := by
        simpa using mul_le_mul_of_nonneg_left hcinv virPoly.hKb
      have htri := norm_sub_norm_le (virEb c' z (a : ℂ)) (1 : ℂ)
      rw [norm_one] at htri
      linarith only [h1, hkb, htri]
    have hE_ψ : ‖Complex.exp (Complex.I * z * d_hc.ψ c' (a : ℂ))‖ ≤ Real.exp (3 * p.s_cut * p.M_ψ) := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.2
      calc (Complex.I * z * d_hc.ψ c' (a : ℂ)).re ≤ ‖Complex.I * z * d_hc.ψ c' (a : ℂ)‖ := Complex.re_le_norm _
        _ = ‖z‖ * ‖d_hc.ψ c' (a : ℂ)‖ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        _ ≤ (3 * p.s_cut) * p.M_ψ := by
            have hzn := (mem_ball_zero_iff.mp hz).le
            have hψ : ‖d_hc.ψ c' (a : ℂ)‖ ≤ p.M_ψ := by
              rw [hd_psi, virasoroHalfCubic_spec.2.2.2.1]; exact (p.hψ_bd hc1 ha).2
            exact mul_le_mul hzn hψ (norm_nonneg _) (mul_pos (by norm_num) p.hs_pos).le
    show ‖virPhaseFactor z (a : ℂ) * W_fac (virV z (a : ℂ)) * virEb c' z (a : ℂ) *
        Complex.exp (Complex.I * z * d_hc.ψ c' (a : ℂ))‖ ≤
        virPoly.M_G0 * M_W * (1 + virPoly.K_b) * Real.exp (3 * p.s_cut * p.M_ψ)
    rw [norm_mul, norm_mul, norm_mul]
    have h0 := mul_le_mul hG hW (norm_nonneg _) virPoly.hMG0
    have h1 := mul_le_mul h0 hEb (norm_nonneg _) (mul_nonneg virPoly.hMG0 hM_W)
    have h2 : 0 ≤ 1 + virPoly.K_b := add_nonneg zero_le_one virPoly.hKb
    exact mul_le_mul h1 hE_ψ (norm_nonneg _) (mul_nonneg (mul_nonneg virPoly.hMG0 hM_W) h2)
  -- Scale `C_scale`, real amplitude `B_τ`, and `T` properties
  obtain ⟨hx'_lo, hx'_im⟩ := p.hx'_min ha
  have hx'_pi : -(4 * π * (virXPrime (a : ℂ)).re) ≤ -(4 * π * (xiStar / 2)) :=
    neg_le_neg (mul_le_mul_of_nonneg_left hx'_lo (mul_nonneg (by norm_num) Real.pi_pos.le))
  have h1exp_pos : 0 < 1 - Real.exp (-(4 * π * (virXPrime (a : ℂ)).re)) := by
    have h1 : Real.exp (-(4 * π * (virXPrime (a : ℂ)).re)) ≤ Real.exp (-(4 * π * (xiStar / 2))) :=
      Real.exp_le_exp.mpr hx'_pi
    linarith only [hdenom_pos, h1]
  let C_scale : ℂ := Complex.exp (Complex.I * (π : ℂ) / 4) *
    (((√(2 * c' / 3) * (1 - Real.exp (-(4 * π * (virXPrime (a : ℂ)).re))) ^ (-2 : ℝ) : ℝ)) : ℂ)
  have hCscale_norm : ‖C_scale‖ ≤ scaleMax * c' ^ (1 / 2 : ℝ) := by
    have hexp_n : ‖Complex.exp (Complex.I * (π : ℂ) / 4)‖ = 1 := by
      rw [show Complex.I * (π : ℂ) / 4 = (((π / 4 : ℝ) : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hrpow_le : (1 - Real.exp (-(4 * π * (virXPrime (a : ℂ)).re))) ^ (-2 : ℝ) ≤ denomMin ^ (-2 : ℝ) := by
      rw [Real.rpow_neg h1exp_pos.le, Real.rpow_neg hdenom_pos.le]
      refine inv_anti₀ (Real.rpow_pos_of_pos hdenom_pos 2) (Real.rpow_le_rpow hdenom_pos.le ?_ (by norm_num))
      dsimp [denomMin]; linarith only [Real.exp_le_exp.mpr hx'_pi]
    have hsq_eq : √(2 * c' / 3) = √(2 / 3) * c' ^ (1 / 2 : ℝ) := by
      rw [show 2 * c' / 3 = (2 / 3) * c' by ring, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow c']
    dsimp [C_scale, scaleMax]
    rw [norm_mul, hexp_n, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hsq_eq]
    calc √(2 / 3) * c' ^ (1 / 2 : ℝ) * (1 - Real.exp (-(4 * π * (virXPrime (a : ℂ)).re))) ^ (-2 : ℝ)
        ≤ √(2 / 3) * c' ^ (1 / 2 : ℝ) * denomMin ^ (-2 : ℝ) := by gcongr
      _ = √(2 / 3) * denomMin ^ (-2 : ℝ) * c' ^ (1 / 2 : ℝ) := by ring
  let x' : ℝ := (virXPrime (a : ℂ)).re
  let T : ℝ → ℝ := fun s => (virV (s : ℂ) (a : ℂ)).re
  let T1 : ℝ → ℝ := fun s => (deriv (fun σ => virV σ (a : ℂ)) (s : ℂ)).re
  obtain ⟨hT0, hT_s, hTpos, hv_lo_cut, hphi_real, hδ_at_cut, hm_th⟩ := p.hT_props ha
  let v₁ : ℝ := T p.s_cut
  have hv₁_pos : 0 < v₁ := hTpos p.s_cut ⟨p.hs_pos, by linarith only [p.hs_pos]⟩
  have hx'_lt_v1 : x' < edgeF v₁ := by
    have hpos_d : 0 < (4 * π / 3) * (edgeF v₁ - x') := p.hδ_pos.trans_le hδ_at_cut
    have h4pi : 0 < 4 * π / 3 := div_pos (mul_pos (by norm_num) Real.pi_pos) (by norm_num)
    have : 0 < edgeF v₁ - x' := (mul_pos_iff_of_pos_left h4pi).mp hpos_d
    linarith only [this]
  -- Real integral rewrite and split at `v₁`
  let B_τ : ℝ → ℂ := fun v => C_scale * Bamp (c' ^ (-2 : ℝ)) v
  have hint_real : IntegrableOn (fun v => B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi 0) := by
    have h0 : IntegrableOn (fun v => Complex.exp (Complex.I * (π : ℂ) / 4) * ((√(2 * c' / 3) : ℝ) : ℂ) *
        (kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ))) (Ioi 0) :=
      (hInt_real hcpos hε_mem hx'_lo).const_mul _
    refine h0.congr_fun (fun v hv => ?_) measurableSet_Ioi
    have hv0 : 0 ≤ v := (mem_Ioi.mp hv).le
    have hpow_inv : ((1 - Real.exp (-(4 * π * x'))) ^ 2)⁻¹ =
        (1 - Real.exp (-(4 * π * x'))) ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1exp_pos.le, Real.rpow_natCast]
    have hreal_amp : (1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' v) =
        (1 - Real.exp (-(4 * π * x'))) ^ (-2 : ℝ) * ((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v)) := by
      rw [div_eq_mul_inv, hpow_inv]; ring
    dsimp [B_τ, C_scale]
    rw [hBamp_eq _ v hv0]
    unfold kedgeEpsIntegrand kedgeAmp0
    simp only [x'] at hreal_amp ⊢
    rw [hreal_amp]
    push_cast
    ring
  have hint_Ioc : IntegrableOn (fun v => B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioc 0 v₁) :=
    hint_real.mono_set Ioc_subset_Ioi_self
  have hint_Ioi : IntegrableOn (fun v => B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi v₁) :=
    hint_real.mono_set (Ioi_subset_Ioi hv₁_pos.le)
  have hsplit_int :
      Complex.exp (Complex.I * (π : ℂ) / 4) * ((√(2 * c' / 3) : ℝ) : ℂ) *
        ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ) =
      (∫ v in (0 : ℝ)..v₁, B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) +
        ∫ v in Ioi v₁, B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := by
    have heq_Ioi : Complex.exp (Complex.I * (π : ℂ) / 4) * ((√(2 * c' / 3) : ℝ) : ℂ) *
        ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ) =
        ∫ v in Ioi (0 : ℝ), B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      have hv0 : 0 ≤ v := (mem_Ioi.mp hv).le
      have hpow_inv : ((1 - Real.exp (-(4 * π * x'))) ^ 2)⁻¹ =
          (1 - Real.exp (-(4 * π * x'))) ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1exp_pos.le, Real.rpow_natCast]
      have hreal_amp : (1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' v) =
          (1 - Real.exp (-(4 * π * x'))) ^ (-2 : ℝ) * ((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v)) := by
        rw [div_eq_mul_inv, hpow_inv]; ring
      dsimp [B_τ, C_scale]
      rw [hBamp_eq _ v hv0]
      unfold kedgeEpsIntegrand kedgeAmp0
      simp only [x'] at hreal_amp ⊢
      rw [hreal_amp]
      push_cast
      ring
    have huni : Ioi (0 : ℝ) = Ioc 0 v₁ ∪ Ioi v₁ := by
      ext v; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
      · intro hv; exact le_or_gt v v₁ |>.imp (fun h => ⟨hv, h⟩) id
      · rintro (⟨h, _⟩ | h); exact h; exact hv₁_pos.trans h
    rw [heq_Ioi, huni, MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_Ioc hint_Ioi,
      intervalIntegral.integral_of_le hv₁_pos.le]
  -- Tail double-IBP on `Bamp` then scale by `C_scale`
  obtain ⟨F1, F2, hOscB, hK0_bd, hK1_bd, hK2_bd, hL1_bd, hL2_bd⟩ := hOsc_spec hε_mem
  have hint_Bamp_Ioi : IntegrableOn (fun v => Bamp (c' ^ (-2 : ℝ)) v *
      Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi v₁) := by
    have hCne : C_scale ≠ 0 := by
      refine mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr (by positivity))
    have hi : IntegrableOn (fun v => C_scale⁻¹ * (B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))) (Ioi v₁) :=
      hint_Ioi.const_mul C_scale⁻¹
    refine hi.congr_fun (fun v _ => ?_) measurableSet_Ioi
    dsimp [B_τ]; rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hCne, one_mul]
  have hibp := phiDual_tail_ibp2 p.hv_pos hv_lo_cut hcpos hx'_lt_v1 hOscB hint_Bamp_Ioi
  obtain ⟨hibp_eq, _, hibp_norm⟩ := hibp
  let ϕ1 : ℝ → ℝ := fun v => (4 * π / 3) * (edgeF v - x')
  let ϕ2 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF' v
  let ϕ3 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF'' v
  let B_τ' : ℝ → ℂ := fun v => C_scale * F1 v
  have htail_Bτ : ∫ v in Ioi v₁, B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) =
      -(1 / (Complex.I * (c' : ℂ))) *
        (B_τ v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
      (1 / (Complex.I * (c' : ℂ))) ^ 2 *
        (ibpH B_τ B_τ' ϕ1 ϕ2 v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
      (1 / (Complex.I * (c' : ℂ))) ^ 2 * (C_scale *
        ∫ v in Ioi v₁, ibpQ (Bamp (c' ^ (-2 : ℝ))) F1 F2 ϕ1 ϕ2 ϕ3 v *
          Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) := by
    have hsc : ∫ v in Ioi v₁, B_τ v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) =
        C_scale * ∫ v in Ioi v₁, Bamp (c' ^ (-2 : ℝ)) v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_; dsimp [B_τ]; ring
    rw [hsc, hibp_eq]
    dsimp [B_τ, B_τ', ibpH]; ring
  -- Call `virSaddle_head_seg_join` for the head integral + tail boundary join + segment remainder
  have hgs_eq_all : ∀ z : ℂ, gs z = virPhaseFactor z (a : ℂ) * W_fac (virV z (a : ℂ)) * virEb c' z (a : ℂ) *
      Complex.exp (Complex.I * z * d_hc.ψ c' (a : ℂ)) := fun _ => rfl
  obtain ⟨R_head, hjoin_head, hRhead_bd⟩ := virSaddle_head_seg_join p hCb hd_psi hd_B hBamp_eq hBamp_d
    hc1 hc2 ha ha_hc_mem hrr hrr1 hlam_pos hlam2 hlam3 hlc hRcut1 hrr2 hsR hRcut_lt hRcut1_rr
    hRcut_pow9 hRcut_pow3 hUa_eq hUa_cut hu_cut hgs_eq_all hgs_diff hgs_bd rfl h1exp_pos hε_mem
    hOscB hint_Ioc
  set chint := ch_cut.intE u (fun w => csr w * d_hc.B c' a ((lam : ℂ) * w))
  let N1 : ℂ := ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ))
  set Qtail := ∫ v in Ioi v₁, ibpQ (Bamp (c' ^ (-2 : ℝ))) F1 F2 ϕ1 ϕ2 ϕ3 v *
    Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))
  have hjoin : Complex.exp (Complex.I * (π : ℂ) / 4) * ((√(2 * c' / 3) : ℝ) : ℂ) *
      ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ) =
      N1 * chint + (R_head + (1 / (Complex.I * (c' : ℂ))) ^ 2 * (C_scale * Qtail)) := by
    rw [hsplit_int, htail_Bτ]
    have h1 : (∫ τ in (0 : ℝ)..v₁, B_τ τ * Complex.exp (Complex.I * ((c' * phiDual τ x' : ℝ) : ℂ))) +
        (-(1 / (Complex.I * (c' : ℂ))) * (B_τ v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
          (1 / (Complex.I * (c' : ℂ))) ^ 2 * (ibpH B_τ B_τ' ϕ1 ϕ2 v₁ / (ϕ1 v₁ : ℂ) *
            Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ)))) =
        N1 * chint + R_head := hjoin_head
    linear_combination h1
  have hfsOp : -(N1 * chint).re = fsOpCh ch_cut u (fun w => d_hc.B c' a ((lam : ℂ) * w)) := by
    unfold fsOpCh; dsimp [N1, chint]; rw [mul_assoc, Complex.re_ofReal_mul]; ring
  set Rest := R_head + (1 / (Complex.I * (c' : ℂ))) ^ 2 * (C_scale * Qtail)
  have hdiff1 : -(√(2 * c' / 3)) * (Complex.exp (Complex.I * (π : ℂ) / 4) *
        ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ)).re -
      fsOpCh ch_cut u (fun w => d_hc.B c' a ((lam : ℂ) * w)) = -Rest.re := by
    have hre_lhs : -(√(2 * c' / 3)) * (Complex.exp (Complex.I * (π : ℂ) / 4) *
          ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ)).re =
        -(Complex.exp (Complex.I * (π : ℂ) / 4) * ((√(2 * c' / 3) : ℝ) : ℂ) *
          ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ)).re := by
      have he : Complex.exp (Complex.I * (π : ℂ) / 4) * ((√(2 * c' / 3) : ℝ) : ℂ) *
          ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ) =
          ((√(2 * c' / 3) : ℝ) : ℂ) * (Complex.exp (Complex.I * (π : ℂ) / 4) *
          ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ)) := by ring
      rw [he, Complex.re_ofReal_mul]; ring
    rw [hre_lhs, hjoin, Complex.add_re, ← hfsOp]; ring
  have hRest_bd : ‖Rest‖ ≤ (C_seg + C_tail) * c' ^ (-(3 / 2 : ℝ)) := by
    have hIc2 : ‖(1 / (Complex.I * (c' : ℂ))) ^ 2‖ = c' ^ (-2 : ℝ) := by
      rw [norm_pow, norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hcpos, one_div, inv_pow,
        show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hcpos.le, Real.rpow_natCast]
    have hQtail_bd : ‖Qtail‖ ≤ tailQ := by
      refine hibp_norm.trans ?_
      have hδ_le : p.δ_lo ≤ ϕ1 v₁ := hδ_at_cut
      have hδ1 : 0 < ϕ1 v₁ := p.hδ_pos.trans_le hδ_le
      have h1 : hOscB.L2 / ϕ1 v₁ ^ 2 ≤ L2 / p.δ_lo ^ 2 :=
        div_le_div₀ hL2 hL2_bd (sq_pos_of_pos p.hδ_pos) (pow_le_pow_left₀ p.hδ_pos.le hδ_le 2)
      have h2 : (3 / 2 : ℝ) * hOscB.K1 / ϕ1 v₁ ^ 2 ≤ (3 / 2 : ℝ) * K1 / p.δ_lo ^ 2 :=
        div_le_div₀ (by positivity) (by linarith only [hK1_bd]) (sq_pos_of_pos p.hδ_pos) (pow_le_pow_left₀ p.hδ_pos.le hδ_le 2)
      have h3 : (1 / 2 : ℝ) * hOscB.K0 * (2 * π / edgeF' p.v_lo) / ϕ1 v₁ ^ 2 ≤
          (1 / 2 : ℝ) * K0 * (2 * π / edgeF' p.v_lo) / p.δ_lo ^ 2 :=
        div_le_div₀ (by positivity) (by
          have hpi : 0 < 2 * π / edgeF' p.v_lo := div_pos (mul_pos (by norm_num) Real.pi_pos) hF'v0
          nlinarith only [hpi, hK0_bd]) (sq_pos_of_pos p.hδ_pos) (pow_le_pow_left₀ p.hδ_pos.le hδ_le 2)
      have h4 : (4 * π / 3) * hOscB.K0 / ϕ1 v₁ ^ 3 ≤ (4 * π / 3) * K0 / p.δ_lo ^ 3 :=
        div_le_div₀ (by positivity) (by nlinarith only [Real.pi_pos, hK0_bd]) (pow_pos p.hδ_pos 3)
          (pow_le_pow_left₀ p.hδ_pos.le hδ_le 3)
      dsimp [tailQ]; linarith only [h1, h2, h3, h4]
    have hc_mul_pow : c' ^ (-2 : ℝ) * c' ^ (1 / 2 : ℝ) = c' ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; norm_num
    have ht4 : ‖(1 / (Complex.I * (c' : ℂ))) ^ 2 * (C_scale * Qtail)‖ ≤ C_tail * c' ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul, norm_mul, hIc2]
      calc c' ^ (-2 : ℝ) * (‖C_scale‖ * ‖Qtail‖)
          ≤ c' ^ (-2 : ℝ) * (scaleMax * c' ^ (1 / 2 : ℝ) * tailQ) := by gcongr
        _ = (scaleMax * tailQ) * (c' ^ (-2 : ℝ) * c' ^ (1 / 2 : ℝ)) := by ring
        _ = C_tail * c' ^ (-(3 / 2 : ℝ)) := by rw [hc_mul_pow]
    dsimp [Rest, C_seg]
    exact (norm_add_le _ _).trans (by linarith only [hRhead_bd, ht4])
  have hB_c : ContinuousOn (fun w : ℂ => d_hc.B c' a ((lam : ℂ) * w)) (ball 0 R₀) := by
    intro w hw
    have hwn : ‖(lam : ℂ) * w‖ ^ 2 < d_hc.r_q := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos]
      have h1 : lam * ‖w‖ < Rs d_hc := by
        have hlt : ‖w‖ < Rs d_hc / lam := mem_ball_zero_iff.mp hw
        calc lam * ‖w‖ < lam * (Rs d_hc / lam) := mul_lt_mul_of_pos_left hlt hlam_pos
          _ = Rs d_hc := mul_div_cancel₀ _ hlam_pos.ne'
      calc (lam * ‖w‖) ^ 2 < Rs d_hc ^ 2 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
        _ = rsSq d_hc := (radii_chain d_hc).2.2.2.2.2.2.2.2.2.2
        _ < d_hc.r_q := by
            have := radii_chain d_hc; linarith [this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1,
              this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1]
    have hq_mem : ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) d_hc.r_q := by
      simpa [mem_ball_zero_iff, norm_pow] using hwn
    have hdE := ((d_hc.hE_q c' (a : ℂ) hc1 ha_hc_mem _ hq_mem).differentiableAt
      (isOpen_ball.mem_nhds hq_mem)).continuousAt
    have hdO := ((d_hc.hO_q c' (a : ℂ) hc1 ha_hc_mem _ hq_mem).differentiableAt
      (isOpen_ball.mem_nhds hq_mem)).continuousAt
    have hsq : ContinuousAt (fun z : ℂ => ((lam : ℂ) * z) ^ 2) w := by fun_prop
    refine ((hdE.comp_of_eq hsq rfl).add ((by fun_prop : ContinuousAt (fun z : ℂ => Complex.I * ((lam : ℂ) * z)) w).mul
      (hdO.comp_of_eq hsq rfl))).continuousWithinAt
  have hB_bd : ∀ w ∈ ball (0 : ℂ) R₀, ‖d_hc.B c' a ((lam : ℂ) * w)‖ ≤ M_B := fun w hw => by
    have hlt : ‖(lam : ℂ) * w‖ < Rs d_hc := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos]
      have hwlt : ‖w‖ < Rs d_hc / lam := mem_ball_zero_iff.mp hw
      have := mul_lt_mul_of_pos_left hwlt hlam_pos
      rwa [mul_div_cancel₀ _ hlam_pos.ne'] at this
    have hwn : ‖(lam : ℂ) * w‖ ^ 2 < d_hc.r_q :=
      (pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)).trans
        (by rw [(radii_chain d_hc).2.2.2.2.2.2.2.2.2.2]; have rc := radii_chain d_hc
            linarith [rc.2.2.2.2.1, rc.2.2.2.2.2.1, rc.2.2.2.2.2.2.1, rc.2.2.2.2.2.2.2.1, rc.2.2.2.2.2.2.2.2.1])
    have hq_mem : ((lam : ℂ) * w) ^ 2 ∈ ball (0 : ℂ) d_hc.r_q := by
      simpa [mem_ball_zero_iff, norm_pow] using hwn
    have hE := d_hc.hE_bd c' (((lam : ℂ) * w) ^ 2) (a : ℂ) hc1 hq_mem ha_hc_mem
    have hO := d_hc.hO_bd c' (((lam : ℂ) * w) ^ 2) (a : ℂ) hc1 hq_mem ha_hc_mem
    unfold HalfCubicData.B
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    have : ‖(lam : ℂ) * w‖ * ‖d_hc.O c' (((lam : ℂ) * w) ^ 2) (a : ℂ)‖ ≤ Rs d_hc * d_hc.M_O :=
      mul_le_mul hlt.le hO (norm_nonneg _) (Real.sqrt_nonneg _)
    dsimp [M_B]; linarith
  have hray := fsOpCh_ray_tail_le p.hs_pos hs_le_d hc1 hlam_pos hlc hRcut1 hRcut_R0_d hu_cut_d
    hRc1 hRcR hURc hMB_nn hB_c hB_bd
  rw [← hch_congr] at hray
  have h1 : |-(√(2 * c' / 3)) * (Complex.exp (Complex.I * (π : ℂ) / 4) *
        ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ)).re -
      fsOpCh ch_cut u (fun w => d_hc.B c' a ((lam : ℂ) * w))| ≤ (C_seg + C_tail) * c' ^ (-(3 / 2 : ℝ)) := by
    rw [hdiff1, abs_neg]
    exact (Complex.abs_re_le_norm Rest).trans hRest_bd
  have htri : |-(√(2 * c' / 3)) * (Complex.exp (Complex.I * (π : ℂ) / 4) *
        ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ)).re -
      fsOpCh (fsChain hRc1 hRcR hURc) u (fun w => d_hc.B c' a ((lam : ℂ) * w))| ≤
      |-(√(2 * c' / 3)) * (Complex.exp (Complex.I * (π : ℂ) / 4) *
        ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' (c' ^ (-2 : ℝ)) x' v * W_fac (v : ℂ)).re -
        fsOpCh ch_cut u (fun w => d_hc.B c' a ((lam : ℂ) * w))| +
      |fsOpCh (fsChain hRc1 hRcR hURc) u (fun w => d_hc.B c' a ((lam : ℂ) * w)) -
        fsOpCh ch_cut u (fun w => d_hc.B c' a ((lam : ℂ) * w))| := by
    refine (abs_sub_le _ (fsOpCh ch_cut u (fun w => d_hc.B c' a ((lam : ℂ) * w))) _).trans_eq ?_
    congr 1
    exact abs_sub_comm _ _
  calc _ ≤ (C_seg + C_tail) * c' ^ (-(3 / 2 : ℝ)) + C_ray * c' ^ (-(3 / 2 : ℝ)) :=
        htri.trans (add_le_add h1 (by simpa [C_ray] using hray))
    _ = (C_seg + C_tail + C_ray) * c' ^ (-(3 / 2 : ℝ)) := by ring

private lemma kedgeAmp0_differentiableAt {ε v : ℝ} (hε : ε ∈ Ioo 0 (1 / 2)) (hv : 0 < v) :
    DifferentiableAt ℝ (kedgeAmp0 ε) v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hspec⟩ := (virasoro_geps_deriv (half_pos hv)).1
  obtain ⟨F1, _, h, _⟩ := hspec hε
  exact (h.hd1 v (half_le_self hv.le)).differentiableAt

private lemma kedgeAmp0Aux_differentiableAt {ε v : ℝ} (hε : ε ∈ Ioo 0 (1 / 2)) (hv : 0 < v) :
    DifferentiableAt ℝ (kedgeAmp0Aux ε) v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hspec⟩ := (virasoro_geps_deriv (half_pos hv)).2
  obtain ⟨F1, _, h, _⟩ := hspec hε
  exact (h.hd1 v (half_le_self hv.le)).differentiableAt

/-- **`virasoro_kedge_saddle`**: `O(c' ^ (-3 / 2))` saddle equivalence between
`virasoroKedgeEps c' (c' ^ (-2)) (virXPrime a).re` and `fsOpCh (fsChain hR1 hRR hUR) u B_lam`. -/
theorem virasoro_kedge_saddle :
    ∃ a_cut c₀ C_ext : ℝ, 0 < a_cut ∧ a_cut ≤ virasoroHalfCubic.rAShrunk ∧ 2 ≤ c₀ ∧
      virasoroHalfCubic.n₀ ≤ c₀ ∧ 0 ≤ C_ext ∧
      ∀ {c' a : ℝ}, c₀ ≤ c' → |a| < a_cut →
        let lam := c' ^ (-(1 / 3 : ℝ))
        let R_c := virasoroHalfCubic.s₁ / lam
        let R₀ := Rs virasoroHalfCubic / lam
        let u := virasoroHalfCubic.uReal c' a
        ∀ (hR1 : 1 ≤ R_c) (hRR : R_c < R₀) (hUR : CtSd.kap * |u| ≤ R_c ^ 2 / 16),
        |virasoroKedgeEps c' (c' ^ (-2 : ℝ)) (virXPrime (a : ℂ)).re -
          fsOpCh (fsChain hR1 hRR hUR) u (fun w => virasoroHalfCubic.B c' a ((lam : ℂ) * w))| ≤
          C_ext * c' ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨p⟩ := virSaddleSetup
  obtain ⟨c₀, C_ext, hc₀2, hc₀n, hC, hcore⟩ := virasoro_kedge_saddle_core p (W_fac := fun _ => (1 : ℂ)) zero_le_one
    rfl rfl rfl (fun n a s hn ha hs => by simpa using virasoroHalfCubic_spec.2.2.2.2.1 n a s hn ha hs)
    (fun _ _ _ => by simp) (fun _ _ => differentiableOn_const _) (fun _ _ _ _ => by simp)
    (fun hε _ hv => kedgeAmp0_differentiableAt hε hv)
    (virasoro_geps_deriv p.hv_pos).1
    (fun {c' _ _} _ hε hx' => (kedgeEps_integrable_and_tau_eq c' hε hx').1.congr_fun
      (fun _ _ => by simp) measurableSet_Ioi)
  refine ⟨p.a_cut, c₀, C_ext, p.ha_pos, p.ha_shrunk, hc₀2, hc₀n, hC, fun hc' ha hR1 hRR hUR => ?_⟩
  simpa [virasoroKedgeEps] using hcore hc' ha hR1 hRR hUR

/-- **`virasoro_kedge1_saddle`**: `O(c' ^ (-3 / 2))` saddle equivalence between
`virasoroKedge1Eps c' (c' ^ (-2)) (virXPrime a).re` and `fsOpCh (fsChain hR1 hRR hUR) u B_aux_lam`. -/
theorem virasoro_kedge1_saddle :
    ∃ a_cut c₀ C_ext : ℝ, 0 < a_cut ∧ a_cut ≤ virasoroHalfCubicAux.rAShrunk ∧ 2 ≤ c₀ ∧
      virasoroHalfCubicAux.n₀ ≤ c₀ ∧ 0 ≤ C_ext ∧
      ∀ {c' a : ℝ}, c₀ ≤ c' → |a| < a_cut →
        let lam := c' ^ (-(1 / 3 : ℝ))
        let R_c := virasoroHalfCubicAux.s₁ / lam
        let R₀ := Rs virasoroHalfCubicAux / lam
        let u := virasoroHalfCubicAux.uReal c' a
        ∀ (hR1 : 1 ≤ R_c) (hRR : R_c < R₀) (hUR : CtSd.kap * |u| ≤ R_c ^ 2 / 16),
        |virasoroKedge1Eps c' (c' ^ (-2 : ℝ)) (virXPrime (a : ℂ)).re -
          fsOpCh (fsChain hR1 hRR hUR) u (fun w => virasoroHalfCubicAux.B c' a ((lam : ℂ) * w))| ≤
          C_ext * c' ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨p⟩ := virSaddleSetup
  have hAux := virasoroHalfCubicAux_spec
  have hrAShrunk_eq : virasoroHalfCubicAux.rAShrunk = virasoroHalfCubic.rAShrunk := by
    unfold HalfCubicData.rAShrunk; rw [hAux.1, hAux.2.1]
  obtain ⟨c₀, C_ext, hc₀2, hc₀n, hC, hcore⟩ :=
    virasoro_kedge_saddle_core p (W_fac := fun v => (1 - 2 * Complex.I * v)⁻¹) (by norm_num : (0 : ℝ) ≤ 2)
      hAux.1 hAux.2.1 hAux.2.2.1
      (fun n a s hn ha hs => by
        rw [hAux.2.2.2 n a s hn ha hs]; unfold virBaux; ring)
      (fun _ _ _ => rfl) virPoly.hW_s virPoly.hW_bd
      (fun hε _ hv => kedgeAmp0Aux_differentiableAt hε hv)
      (virasoro_geps_deriv p.hv_pos).2
      (fun {c' _ _} _ hε hx' => (kedgeEps_integrable_and_tau_eq c' hε hx').2.1)
  refine ⟨p.a_cut, c₀, C_ext, p.ha_pos, by rw [hrAShrunk_eq]; exact p.ha_shrunk, hc₀2, hc₀n, hC,
    fun hc' ha hR1 hRR hUR => ?_⟩
  simpa [virasoroKedge1Eps] using hcore hc' ha hR1 hRR hUR

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_kedge_saddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_kedge_saddle

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_kedge1_saddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_kedge1_saddle

end
end FormalResearch.ModularBootstrap.FiveTerm
