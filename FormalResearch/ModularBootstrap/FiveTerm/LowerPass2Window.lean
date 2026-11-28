module

public import FormalResearch.ModularBootstrap.Contour.WindowEnvelope
public import FormalResearch.ModularBootstrap.StripMultiplier.BandBound
public import FormalResearch.ModularBootstrap.Contour.VirasoroScaleChoice

/-!
# Top-Scale Logarithmic-Angle Window Lemma (`ctl:pass2` / `cts:rosc-uncond` (1))

Adapts `VirasoroBridge.virasoro_uniform_band_boundFor` and `WindowEnvelope.lemma_Z` to the logarithmic
covered-arc cutoff `sin φ ≥ C_ang * R^{-3/4} * √(log c')` needed by Paper II's Lemma C7b (`ctl:pass2`):

* `virasoro_uniform_band_boundFor_pos`: uses `StripBand.teb_band_reduction_pos` for all `ζ ∈ stripClosed`
  in the annulus with `0 < ζ.re` (no `c'^{-1/12}` sector restriction).
* `lemma_Z_log`: for `0 < b_lo ≤ b_hi` with `b_hi^2 ≤ zScaleCap`, an interior multiplier bound on
  `0 < ζ.re` implies the covered-arc Airy envelope on `0 ≤ u.im`, `R - 1 ≤ ‖u‖ ≤ R + 1`,
  `pass2AngleC2 * R^{-3/4} * √(log c') * √‖u‖ ≤ (u^{1/2}).re`.
* `virasoro_cov_window_log`: combines the two at any scale `b_lo^2 c'^{2/3} ≤ R`, `R + 1 ≤ b_hi^2 c'^{2/3}`
  inside `[virasoroAThr, 2 * virasoroBVChoice^2 * c'^{2/3}]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripBand
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour

/-! ### 1. Uniform band reduction on the full half-strip `0 < ζ.re` -/

noncomputable def pass2P0 : BandReductionParams :=
  yvBandParams langerChartSpec_virasoro virasoroAThr

private noncomputable def pass2BandParamsAt (b_R : ℝ) (hb_R : 0 < b_R) : BandReductionParams :=
  { pass2P0 with
    b := b_R
    hb := hb_R }

noncomputable def pass2UniformBandConst (b_lo b_hi : ℝ) : ℝ :=
  let P := pass2P0
  let ρ_min_lo := kappaV * b_lo / 3
  let C_pf_lo := ρ_min_lo ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  let C_gauss5 := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
  let C_core := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  let C_sub := P.C_a * C_gauss5 / P.κ_sub
  let C_tail := C_core + C_sub + 2 * tebBandOscConst P
  let C_band_hi := tebBandOscConst P * max (P.C_τ * (b_hi ^ 2 + 1)) 1
  max C_tail C_band_hi / (C_pf_lo * ρ_min_lo)

private lemma tebBandConst_pass2BandParamsAt_le {b_lo b_hi b_R : ℝ}
    (hb_lo_pos : 0 < b_lo) (hb_R : 0 < b_R) (hb_lo : b_lo ≤ b_R) (hb_hi : b_R ≤ b_hi) :
    tebBandConst (pass2BandParamsAt b_R hb_R) ≤ pass2UniformBandConst b_lo b_hi := by
  let P := pass2P0
  have hosc_pos : 0 < tebBandOscConst P := by
    unfold tebBandOscConst
    have hb₀ : 0 < min P.c_1 (P.c_2 / 16) := lt_min P.hc_1 (div_pos P.hc_2 (by norm_num))
    have := TwoEdgeBootstrap.tebOscConst_pos hb₀ (P.M + 11 / 2)
    have := P.hC_a; have := P.hC_ν
    positivity
  set ρ_min_lo : ℝ := kappaV * b_lo / 3
  set ρ_min_R : ℝ := kappaV * b_R / 3
  have hρ_lo_pos : 0 < ρ_min_lo := by dsimp [ρ_min_lo]; have := kappaV_pos; positivity
  have hρ_le : ρ_min_lo ≤ ρ_min_R := by dsimp [ρ_min_lo, ρ_min_R]; have := kappaV_pos; gcongr
  have hρ_R_pos : 0 < ρ_min_R := lt_of_lt_of_le hρ_lo_pos hρ_le
  set C_pf_lo : ℝ := ρ_min_lo ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  set C_pf_R : ℝ := ρ_min_R ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  have hden_lo_pos : 0 < C_pf_lo * ρ_min_lo := by dsimp [C_pf_lo]; positivity
  have hden_R_pos : 0 < C_pf_R * ρ_min_R := by dsimp [C_pf_R]; positivity
  have hden_le : C_pf_lo * ρ_min_lo ≤ C_pf_R * ρ_min_R := by
    dsimp [C_pf_lo, C_pf_R]
    have hpow : ρ_min_lo ^ (5 / 2 : ℝ) ≤ ρ_min_R ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow hρ_lo_pos.le hρ_le (by norm_num)
    gcongr
  set C_gauss5 : ℝ := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
  set C_core : ℝ := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  set C_sub : ℝ := P.C_a * C_gauss5 / P.κ_sub
  set C_tail : ℝ := C_core + C_sub + 2 * tebBandOscConst P
  set C_band_R : ℝ := tebBandOscConst P * max (P.C_τ * (b_R ^ 2 + 1)) 1
  set C_band_hi : ℝ := tebBandOscConst P * max (P.C_τ * (b_hi ^ 2 + 1)) 1
  have hband_hi_pos : 0 < C_band_hi :=
    mul_pos hosc_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hnum_hi_pos : 0 < max C_tail C_band_hi :=
    lt_of_lt_of_le hband_hi_pos (le_max_right _ _)
  have hsq_le : b_R ^ 2 ≤ b_hi ^ 2 := pow_le_pow_left₀ hb_R.le hb_hi 2
  have hband_le : C_band_R ≤ C_band_hi := by
    dsimp [C_band_R, C_band_hi]
    refine mul_le_mul_of_nonneg_left (max_le_max_right 1 ?_) hosc_pos.le
    exact mul_le_mul_of_nonneg_left (by linarith only [hsq_le]) P.hC_τ.le
  have hnum_le : max C_tail C_band_R ≤ max C_tail C_band_hi :=
    max_le_max_left C_tail hband_le
  have hlhs_eq : tebBandConst (pass2BandParamsAt b_R hb_R) =
      max C_tail C_band_R / (C_pf_R * ρ_min_R) := rfl
  have hrhs_eq : pass2UniformBandConst b_lo b_hi =
      max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) := rfl
  rw [hlhs_eq, hrhs_eq]
  calc max C_tail C_band_R / (C_pf_R * ρ_min_R)
      ≤ max C_tail C_band_hi / (C_pf_R * ρ_min_R) :=
        div_le_div_of_nonneg_right hnum_le hden_R_pos.le
    _ ≤ max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) :=
        div_le_div_of_nonneg_left hnum_hi_pos.le hden_lo_pos hden_le

/-- Uniform band reduction on the full positive half-annulus `0 < ζ.re` for any compact scale
range `[b_lo, b_hi]` with `b_hi^2 ≤ virasoroScaleThresh` and `b_hi ≤ √2 * virasoroBV`. -/
lemma virasoro_uniform_band_boundFor_pos {b_lo b_hi : ℝ}
    (hb_lo_pos : 0 < b_lo) (hb_le : b_lo ≤ b_hi)
    (hb_scale : b_hi ^ 2 ≤ virasoroScaleThresh) (hb_bv : b_hi ≤ Real.sqrt 2 * virasoroBV)
    {c' R T : ℝ}
    (hc'_yv : yvThresh langerChartSpec_virasoro virasoroAThr ≤ c')
    (hc'_cq : virasoroCQEnv ≤ c')
    (hR_thr : virasoroAThr ≤ R)
    (hR_lo : b_lo ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_hi : R + 1 ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ))
    {g : ℝ → ℝ} (hg_wf : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    let M := virasoroProblem.cardyNorm (c' / 12) g
    let B₁ := virasoroBandB1 c' R T g
    let B₂ := virasoroBandB2 c' R g
    ∀ ζ ∈ stripClosed,
      kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
      ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
      0 < ζ.re →
      ‖tildeWV c' g ζ‖ ≤ M *
        (max (pass2UniformBandConst b_lo b_hi) 1 * (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
  dsimp only
  let pg := langerChartSpec_virasoro
  let A_thr := virasoroAThr
  let w := yvWitness pg
  have hb_hi_pos : 0 < b_hi := lt_of_lt_of_le hb_lo_pos hb_le
  have hc'_10000 : 10000 ≤ c' := (yvThresh_ge pg A_thr).trans hc'_yv
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith only [hc'_10000]
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  have hg : TestClass virasoroProblem (c' / 12) g := hg_wf.1
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero hshift hg_wf.1 hg_wf.2.1
  have hg_nn : ∀ t ∈ Ici T, 0 ≤ g t := hg_wf.2.2.2
  have hb_hi_c0 : b_hi ^ 2 ≤ w.c₀ / 2 := hb_scale.trans (min_le_left _ _)
  have hb_hi_bv : b_hi ^ 2 ≤ 2 * virasoroBV ^ 2 := by
    have h1 := pow_le_pow_left₀ hb_hi_pos.le hb_bv 2
    rwa [mul_pow, Real.sq_sqrt zero_le_two] at h1
  have hR_le_AC : R ≤ virasoroAC c' ^ 2 := by
    rw [virasoroAC_sq c' hc'_pos.le]
    have h1 : R ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) := by linarith only [hR_hi]
    exact h1.trans (mul_le_mul_of_nonneg_right hb_hi_bv (Real.rpow_nonneg hc'_pos.le _))
  have hA_pos : 0 < A_thr := virasoroAThr_pos
  have hR_pos : 0 < R := lt_of_lt_of_le hA_pos hR_thr
  have hΔ0_eq : langerDelta pg c' 0 = virasoroDeltaChart c' 0 :=
    langerDelta_virasoro_eq hc'_pos (by rw [abs_zero]; exact sq_nonneg _)
  have hΔA_eq : langerDelta pg c' (-A_thr) = virasoroDeltaChart c' (-A_thr) :=
    langerDelta_virasoro_eq hc'_pos (by rw [abs_neg, abs_of_pos hA_pos]; exact hR_thr.trans hR_le_AC)
  have hΔR_eq : langerDelta pg c' (-R) = virasoroDeltaChart c' (-R) :=
    langerDelta_virasoro_eq hc'_pos (by rw [abs_neg, abs_of_pos hR_pos]; exact hR_le_AC)
  have hT_lo' : langerDelta pg c' 0 ≤ T := by rw [hΔ0_eq]; exact hT_lo
  have hT_hi' : T ≤ langerDelta pg c' (-A_thr) := by rw [hΔA_eq]; exact hT_hi
  let R_star : ℝ := pass2P0.b ^ 2 * c' ^ (2 / 3 : ℝ)
  have hP0_b_sq : pass2P0.b ^ 2 = w.c₀ / 2 := by
    dsimp [pass2P0, yvBandParams]
    exact Real.sq_sqrt (div_nonneg w.hc₀_pos.le zero_lt_two.le)
  have hR_le_Rstar : R ≤ R_star := by
    dsimp [R_star]
    rw [hP0_b_sq]
    calc R ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) := by linarith only [hR_hi]
      _ ≤ (w.c₀ / 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hb_hi_c0 (Real.rpow_nonneg hc'_pos.le _)
  have hRstar_ub : R_star ≤ pass2P0.b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := by
    dsimp [R_star]; linarith only []
  let I₀ := yvBandInstance pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hmom₀ := yvBandInstance_moments pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hProps₀ := langerDelta_props hc'_yv (R := R_star) le_rfl hRstar_ub
  have hDelta_le : langerDelta pg c' (-R) ≤ langerDelta pg c' (-R_star) :=
    hProps₀.2.2.2.2.1.monotoneOn ⟨hR_pos.le, hR_le_Rstar⟩ ⟨hProps₀.1.le, le_rfl⟩ hR_le_Rstar
  set b_R : ℝ := Real.sqrt (R * c' ^ (-(2 / 3 : ℝ)))
  have hb_R_sq : b_R ^ 2 = R * c' ^ (-(2 / 3 : ℝ)) :=
    Real.sq_sqrt (mul_nonneg hR_pos.le (Real.rpow_nonneg hc'_pos.le _))
  have hb_R_lo : b_lo ≤ b_R := by
    refine Real.le_sqrt_of_sq_le ?_
    calc b_lo ^ 2
        = (b_lo ^ 2 * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ R * c' ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hR_lo (Real.rpow_nonneg hc'_pos.le _)
  have hb_R_pos : 0 < b_R := lt_of_lt_of_le hb_lo_pos hb_R_lo
  have hb_R_hi : b_R ≤ b_hi := by
    rw [show b_R = Real.sqrt (R * c' ^ (-(2 / 3 : ℝ))) from rfl]
    refine Real.sqrt_le_iff.mpr ⟨hb_hi_pos.le, ?_⟩
    calc R * c' ^ (-(2 / 3 : ℝ))
        ≤ (b_hi ^ 2 * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hR_hi]) (Real.rpow_nonneg hc'_pos.le _)
      _ = b_hi ^ 2 := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  have hb_R_R : b_R ^ 2 * c' ^ (2 / 3 : ℝ) = R := by
    rw [hb_R_sq, mul_assoc, ← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
  let P_R : BandReductionParams := pass2BandParamsAt b_R hb_R_pos
  have hρR_ub : 2 * rhoR P_R c' R ≤ 0.035 := by
    have hle : rhoR P_R c' R ≤ rhoR pass2P0 c' R_star := by
      unfold rhoR
      change kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R ≤
        kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R_star
      have := kappaV_pos
      gcongr
    have h0_ub : 2 * rhoR pass2P0 c' R_star ≤ 0.035 := I₀.hρR_ub
    linarith only [hle, h0_ub]
  let I_R : BandReductionInstance P_R :=
    { c := I₀.c, ε := I₀.ε, R := R, hc := I₀.hc, hε := I₀.hε
      hR_lb := by change b_R ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R; exact hb_R_R.le
      hR_ub := by change R ≤ b_R ^ 2 * c' ^ (2 / 3 : ℝ) + 1; linarith only [hb_R_R]
      hρR_ub := hρR_ub, W_tilde := I₀.W_tilde, hW_cont := I₀.hW_cont, hW_holo := I₀.hW_holo
      hW_symm := I₀.hW_symm, hW_bound := I₀.hW_bound, dmPos := I₀.dmPos, dmNeg := I₀.dmNeg
      hdmPos_fin := I₀.hdmPos_fin, hdmNeg_fin := I₀.hdmNeg_fin, hdmPos_supp := I₀.hdmPos_supp
      hdmNeg_supp := I₀.hdmNeg_supp, hdm_tv := I₀.hdm_tv, T := I₀.T
      hdm_nonneg_tail := I₀.hdm_nonneg_tail, E_sub := I₀.E_sub, hE_sub_meas := I₀.hE_sub_meas
      hE_sub_sub := I₀.hE_sub_sub, K_edge := I₀.K_edge, hK_meas := I₀.hK_meas
      hW_edge := I₀.hW_edge, hK_sub := I₀.hK_sub, a_0 := I₀.a_0, a_0' := I₀.a_0'
      a_2 := I₀.a_2, R_0 := I₀.R_0, Phi := I₀.Phi, hK_factor := I₀.hK_factor
      ha_2_bd := I₀.ha_2_bd, ha_0_deriv := I₀.ha_0_deriv, ha_0_bd := I₀.ha_0_bd
      hR_0_nonpos := I₀.hR_0_nonpos, hR_0_cont := I₀.hR_0_cont, hR_0_even := I₀.hR_0_even
      hR_0_unimodal := I₀.hR_0_unimodal, hPhi_odd := I₀.hPhi_odd, ν := I₀.ν, ν' := I₀.ν'
      invNu' := I₀.invNu', hν_deriv := I₀.hν_deriv, hν'_cont := I₀.hν'_cont
      hν'_inv_pos := I₀.hν'_inv_pos, hν'_inv_deriv := I₀.hν'_inv_deriv
      hinvNu'_cont := I₀.hinvNu'_cont, hinvNu'_int := I₀.hinvNu'_int
      hinvNu'_integrable := I₀.hinvNu'_integrable, μ := I₀.μ, m := I₀.m, m' := I₀.m'
      hPhi_deriv := I₀.hPhi_deriv, hm_0 := I₀.hm_0, hm_cont := I₀.hm_cont
      hm_strictMono := I₀.hm_strictMono, hm_deriv := I₀.hm_deriv, hm_step := I₀.hm_step
      hm_slope := I₀.hm_slope, τ_0 := I₀.τ_0, hτ_0_nn := I₀.hτ_0_nn
      hτ_0_eq_zero := I₀.hτ_0_eq_zero, hτ_0_root := I₀.hτ_0_root, u_tilde := I₀.u_tilde
      Delta := I₀.Delta, hτ_0_below := I₀.hτ_0_below
      hτ_0_band := fun ξ hξ => I₀.hτ_0_band ξ ⟨hξ.1, hξ.2.trans hDelta_le⟩
      hu_tilde_int := I₀.hu_tilde_int.mono_set (Icc_subset_Icc_right hDelta_le) }
  set M := virasoroProblem.cardyNorm (c' / 12) g
  let fPos : ℝ → ℝ := fun t => max (g t) 0 * virasoroProblem.cardyV (c' / 12) t / M
  have hT_pos : 0 < T := by
    have h0 : 0 < langerDelta pg c' 0 := by rw [langerDelta_zero]; have := xiStar_pos; positivity
    exact lt_of_lt_of_le h0 hT_lo'
  have hV_cont : Continuous (fun t => virasoroProblem.cardyV (c' / 12) t) :=
    continuous_cardyV virasoroProblem (c' / 12)
  have hg_cont : ContinuousOn g (Ioi 0) := hg.cont.mono Ioi_subset_Ici_self
  have hfPos_meas : AEMeasurable fPos (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn fPos (Ioi 0) := fun t ht =>
      (((hg_cont t ht).sup continuousWithinAt_const).mul hV_cont.continuousWithinAt).div_const M
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hfPos_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ fPos t := fun t ht => by
    dsimp [fPos]
    exact div_nonneg (mul_nonneg (le_max_right _ _)
      (virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)) hM_pos.le
  have hfPos_int : IntegrableOn fPos (Ioi 0) :=
    (hg.int_cardy.div_const M).mono' hfPos_meas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (hfPos_nn t ht)]
        dsimp [fPos]
        have hV_nn := virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le
        have hmax_le : max (g t) 0 ≤ |g t| := max_le (le_abs_self _) (abs_nonneg _)
        gcongr)
  have hT_le_ΔR : T ≤ virasoroDeltaChart c' (-R) := by
    have hRm : -R ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
      ⟨by linarith only [hR_le_AC], by linarith only [hR_pos, sq_nonneg (virasoroAC c')]⟩
    have hAm : -A_thr ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
      ⟨by linarith only [hR_thr, hR_le_AC], by linarith only [hA_pos, sq_nonneg (virasoroAC c')]⟩
    exact hT_hi.trans ((virasoroDeltaChart_strictAnti hc'_pos).antitoneOn hRm hAm
      (by linarith only [hR_thr]))
  have hB1_eq : bandB1 I_R = virasoroBandB1 c' R T g := by
    have hsub_Icc : Icc T (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) :=
      fun t ht => lt_of_lt_of_le hT_pos ht.1
    have h1 : bandB1 I_R = R⁻¹ * ∫ ξ in Icc T (langerDelta pg c' (-R)),
        (-I₀.u_tilde ξ) ∂((volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (fPos t))) := by
      dsimp only [bandB1, I_R, I₀, yvBandInstance]
    rw [h1, setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hfPos_meas.ennreal_ofReal.restrict
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun t => -I₀.u_tilde t) measurableSet_Icc]
    have h_meas_eq : (volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R))) =
        volume.restrict (Icc T (langerDelta pg c' (-R))) := by
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub_Icc]
    change R⁻¹ * ∫ t, (ENNReal.ofReal (fPos t)).toReal • (-I₀.u_tilde t)
        ∂((volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R)))) = _
    rw [h_meas_eq, hΔR_eq]
    have hcongr : EqOn
        (fun t => (ENNReal.ofReal (fPos t)).toReal • (-I₀.u_tilde t))
        (fun t => M⁻¹ * ((-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t)))
        (Icc T (virasoroDeltaChart c' (-R))) := fun t ht => by
      have ht_pos : t ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (lt_of_lt_of_le hT_pos ht.1)
      dsimp only
      rw [ENNReal.toReal_ofReal (hfPos_nn t ht_pos), smul_eq_mul]
      dsimp [fPos]
      rw [max_eq_left (hg_nn t ht.1)]
      have hu_t := virasoroUT_between hc'_pos (by linarith only [hR_le_AC] : -(virasoroAC c' ^ 2) ≤ -R)
        (sq_nonneg _) (by linarith only [hR_pos] : -R ≤ 0) (hT_lo.trans ht.1) ht.2
      have hu_abs : |virasoroUT c' t| ≤ virasoroAC c' ^ 2 :=
        abs_le.mpr ⟨by linarith only [hu_t.1.1, hR_le_AC], hu_t.1.2.trans (sq_nonneg _)⟩
      have hld_eq : langerDelta pg c' (virasoroUT c' t) = t :=
        (langerDelta_virasoro_eq hc'_pos hu_abs).trans hu_t.2
      have hu_star : virasoroUT c' t ∈ Icc (-R_star) 0 :=
        ⟨by linarith only [hu_t.1.1, hR_le_Rstar], hu_t.1.2⟩
      have hut_eq : I₀.u_tilde t = virasoroUT c' t := by
        have hm := hmom₀.2.1 (virasoroUT c' t) hu_star
        rwa [hld_eq] at hm
      rw [hut_eq]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcongr, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT_le_ΔR, ← mul_assoc]
    rfl
  have hB2_eq : bandB2 I_R = virasoroBandB2 c' R g := by
    have h1 : bandB2 I_R = (((volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (fPos s))) (Ici (langerDelta pg c' (-R)))).toReal := by
      dsimp only [bandB2, I_R, I₀, yvBandInstance]
    rw [h1, withDensity_apply _ (measurableSet_Ici : MeasurableSet (Ici (langerDelta pg c' (-R))))]
    have hsub : Ici (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) := fun t ht => by
      have ht' : virasoroDeltaChart c' (-R) ≤ t := by rw [← hΔR_eq]; exact ht
      exact lt_of_lt_of_le hT_pos (hT_le_ΔR.trans ht')
    have hfPos_tail : IntegrableOn fPos (Ici (langerDelta pg c' (-R))) := hfPos_int.mono_set hsub
    have hl_eq : ∫⁻ a in Ici (langerDelta pg c' (-R)), ENNReal.ofReal (fPos a) ∂(volume.restrict (Ioi 0)) =
        ∫⁻ a in Ici (langerDelta pg c' (-R)), ENNReal.ofReal (fPos a) := by
      rw [Measure.restrict_restrict measurableSet_Ici, inter_eq_left.mpr hsub]
    rw [hl_eq, ← ofReal_integral_eq_lintegral_ofReal hfPos_tail
        (ae_restrict_of_forall_mem measurableSet_Ici fun t ht => hfPos_nn t (hsub ht)),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ici fun t ht => hfPos_nn t (hsub ht)),
      hΔR_eq]
    have hcongr : EqOn fPos
        (fun t => M⁻¹ * (g t * virasoroProblem.cardyV (c' / 12) t))
        (Ici (virasoroDeltaChart c' (-R))) := fun t ht => by
      dsimp [fPos]
      rw [max_eq_left (hg_nn t (hT_le_ΔR.trans ht))]
      ring
    rw [setIntegral_congr_fun measurableSet_Ici hcongr, integral_const_mul]
    rfl
  intro ζ _ hlo hhi hζ_re_pos
  have hζ_pos : 0 < ‖ζ‖ :=
    lt_of_lt_of_le (by have := kappaV_pos; positivity) hlo
  have hdiv_le1 : ζ.re / ‖ζ‖ ≤ 1 :=
    (div_le_one hζ_pos).mpr (Complex.re_le_norm ζ)
  have hdiv_ge_neg1 : -1 ≤ ζ.re / ‖ζ‖ := by
    have hnn : 0 ≤ ζ.re / ‖ζ‖ := div_nonneg hζ_re_pos.le hζ_pos.le
    linarith only [hnn]
  set ψ : ℝ := Real.arccos (ζ.re / ‖ζ‖)
  have hcos_eq_div : Real.cos ψ = ζ.re / ‖ζ‖ :=
    Real.cos_arccos hdiv_ge_neg1 hdiv_le1
  have hcos_pos : 0 < Real.cos ψ := by rw [hcos_eq_div]; positivity
  have hcos_eq : ζ.re = ‖ζ‖ * Real.cos ψ := by
    rw [hcos_eq_div, mul_div_cancel₀ _ hζ_pos.ne']
  have hlo' : rhoR P_R I_R.c I_R.R / 3 ≤ ‖ζ‖ := hlo
  have hhi' : ‖ζ‖ ≤ 2 * rhoR P_R I_R.c I_R.R := hhi
  have hred := teb_band_reduction_pos I_R hlo' hhi' hcos_eq hcos_pos
  have hW_eq : ‖I_R.W_tilde ζ‖ = M⁻¹ * ‖tildeWV c' g ζ‖ := by
    have h1 : I_R.W_tilde ζ = ((M⁻¹ : ℝ) : ℂ) * tildeWV c' g ζ := hmom₀.1 ζ
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM_pos.le)]
  change ‖I_R.W_tilde ζ‖ ≤
    tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
      (c' ^ (1 / 3 : ℝ) * (bandB1 I_R + bandB2 I_R) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ at hred
  rw [hW_eq, hB1_eq, hB2_eq] at hred
  have hmul_M := mul_le_mul_of_nonneg_left hred hM_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at hmul_M
  have hCY_le : tebBandConst P_R ≤ max (pass2UniformBandConst b_lo b_hi) 1 :=
    (tebBandConst_pass2BandParamsAt_le hb_lo_pos hb_R_pos hb_R_lo hb_R_hi).trans (le_max_left _ _)
  have hc16_le1 : c' ^ (-(1 / 6 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc'_ge1 (by norm_num)
  have hB1_nn := virasoroBandB1_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_lo hT_hi
  have hB2_nn := virasoroBandB2_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_hi
  have hCY_nn : 0 ≤ tebBandConst P_R := (tebBandConst_pos P_R).le
  calc ‖tildeWV c' g ζ‖
      ≤ M * (tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) +
            c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) := hmul_M
    _ ≤ M * (max (pass2UniformBandConst b_lo b_hi) 1 * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) /
          Real.cos ψ) := by
        gcongr
    _ = M * (max (pass2UniformBandConst b_lo b_hi) 1 *
          (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
        rw [hcos_eq_div]
        field_simp [hζ_pos.ne', hζ_re_pos.ne']

/-! ### 2. Logarithmic-angle Lemma Z (`lemma_Z_log`) -/

private lemma cpow_half_re_eq_sqrt_mul_sin' {u : ℂ} (hu : u ≠ 0) :
    (u ^ (1 / 2 : ℂ)).re = Real.sqrt ‖u‖ * Real.sin ((Real.pi - u.arg) / 2) := by
  have hn_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  rw [Complex.cpow_def_of_ne_zero hu, Complex.exp_re]
  have hre : (Complex.log u * (1 / 2 : ℂ)).re = Real.log ‖u‖ / 2 := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im]; norm_num; ring
  have him : (Complex.log u * (1 / 2 : ℂ)).im = u.arg / 2 := by
    rw [Complex.mul_im, Complex.log_re, Complex.log_im]; norm_num; ring
  have hexp_sqrt : Real.exp (Real.log ‖u‖ / 2) = Real.sqrt ‖u‖ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos]; congr 1; ring
  have hcos_sin : Real.cos (u.arg / 2) = Real.sin ((Real.pi - u.arg) / 2) := by
    have heq : u.arg / 2 = Real.pi / 2 - (Real.pi - u.arg) / 2 := by ring
    rw [heq, Real.cos_pi_div_two_sub]
  rw [hre, him, hexp_sqrt, hcos_sin]

private lemma exp_neg_le_inv_one_add' {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (1 + x)⁻¹ := by
  have h1 : 1 + x ≤ Real.exp x := by have h := Real.add_one_le_exp x; linarith only [h]
  rw [Real.exp_neg]
  exact inv_anti₀ (by linarith only [hx]) h1

private lemma exp_neg_kappa_le_inv_sq {κ c' : ℝ} (hκ : 0 < κ) (hc' : 0 < c') :
    Real.exp (-κ * c') ≤ (2 / κ ^ 2) * c' ^ (-2 : ℝ) := by
  have hx : 0 ≤ κ * c' := mul_nonneg hκ.le hc'.le
  have hsum := Real.sum_le_exp_of_nonneg hx 3
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.factorial_one, zero_add] at hsum
  have hquad : (κ * c') ^ 2 / 2 ≤ Real.exp (κ * c') := by
    have h1 : 0 ≤ 1 + κ * c' := by linarith only [hx]
    norm_num at hsum
    linarith only [hsum, h1]
  have hpos_q : 0 < (κ * c') ^ 2 / 2 := by positivity
  rw [show -κ * c' = -(κ * c') by ring, Real.exp_neg]
  have hinv := inv_anti₀ hpos_q hquad
  refine hinv.trans_eq ?_
  rw [Real.rpow_neg hc'.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by rfl, Real.rpow_natCast]
  field_simp [hκ.ne', hc'.ne']

private lemma integral_exp_neg_mul_sq_le' {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
    ∫ t in (0 : ℝ)..L, Real.exp (-α * t ^ 2) ≤ (Real.pi / 2) / Real.sqrt α := by
  set s : ℝ := Real.sqrt α
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hα
  have hs_sq : s ^ 2 = α := Real.sq_sqrt hα.le
  set F : ℝ → ℝ := fun t => s⁻¹ * Real.arctan (s * t)
  have hF_deriv : ∀ t ∈ uIcc 0 L, HasDerivAt F ((1 + α * t ^ 2)⁻¹) t := fun t _ => by
    have h1 : HasDerivAt (fun x : ℝ => s * x) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    have h2 := (Real.hasDerivAt_arctan (s * t)).comp t h1
    refine (h2.const_mul s⁻¹).congr_deriv ?_
    have hden : 1 + (s * t) ^ 2 = 1 + α * t ^ 2 := by rw [mul_pow, hs_sq]
    rw [hden]; field_simp [hs_pos.ne']
  have hcont_r : ContinuousOn (fun t : ℝ => (1 + α * t ^ 2)⁻¹) (Icc 0 L) :=
    (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.pow 2))).inv₀
      fun t _ => (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hα.le (sq_nonneg t))).ne'
  have hcont_l : ContinuousOn (fun t : ℝ => Real.exp (-α * t ^ 2)) (Icc 0 L) := by fun_prop
  have hmono : ∫ t in (0 : ℝ)..L, Real.exp (-α * t ^ 2) ≤
      ∫ t in (0 : ℝ)..L, (1 + α * t ^ 2)⁻¹ := by
    refine intervalIntegral.integral_mono_on hL (hcont_l.intervalIntegrable_of_Icc hL)
      (hcont_r.intervalIntegrable_of_Icc hL) fun t _ => ?_
    rw [show -α * t ^ 2 = -(α * t ^ 2) by ring]
    exact exp_neg_le_inv_one_add' (by positivity)
  have heval : ∫ t in (0 : ℝ)..L, (1 + α * t ^ 2)⁻¹ = F L - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv (hcont_r.intervalIntegrable_of_Icc hL)
  have hF0 : F 0 = 0 := by dsimp [F]; simp [mul_zero, Real.arctan_zero]
  have hFL : F L ≤ (Real.pi / 2) / s := by
    dsimp [F]
    have harctan : Real.arctan (s * L) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two (s * L)).le
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right harctan hs_pos.le
  linarith only [hmono, heval, hF0, hFL]

private lemma integral_exp_neg_mul_sub_sq_le' {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
    ∫ t in (0 : ℝ)..L, Real.exp (-α * (L - t) ^ 2) ≤ (Real.pi / 2) / Real.sqrt α := by
  have hrev := intervalIntegral.integral_comp_sub_left (fun t => Real.exp (-α * t ^ 2)) L (a := 0) (b := L)
  simp only [sub_self, sub_zero] at hrev
  rw [hrev]
  exact integral_exp_neg_mul_sq_le' hα hL

private lemma norm_contourIntegral_le_of_seg_bound' (f : ℂ → ℂ) (segs : List ContourSeg)
    {B : ℝ} (_hB : 0 ≤ B)
    (hseg : ∀ S ∈ segs, ‖∫ t in S.a..S.b, f (S.ω t) * S.ω' t‖ ≤ B) :
    ‖contourIntegral f segs‖ ≤ (segs.length : ℝ) * B := by
  induction segs with
  | nil => simp [contourIntegral]
  | cons S rest ih =>
    have hS : ‖∫ t in S.a..S.b, f (S.ω t) * S.ω' t‖ ≤ B := hseg S List.mem_cons_self
    have hrest := ih (fun S' hS' => hseg S' (List.mem_cons_of_mem _ hS'))
    change ‖(∫ t in S.a..S.b, f (S.ω t) * S.ω' t) + contourIntegral f rest‖ ≤
      (((rest.length + 1 : ℕ) : ℝ)) * B
    calc ‖(∫ t in S.a..S.b, f (S.ω t) * S.ω' t) + contourIntegral f rest‖
        ≤ ‖∫ t in S.a..S.b, f (S.ω t) * S.ω' t‖ + ‖contourIntegral f rest‖ := norm_add_le _ _
      _ ≤ B + (rest.length : ℝ) * B := add_le_add hS hrest
      _ = (((rest.length + 1 : ℕ) : ℝ)) * B := by push_cast; ring

private lemma const_seg_integral_le' {f : ℝ → ℂ} {a b K C_tail B_unit : ℝ}
    (hab : a ≤ b) (hba : b - a ≤ 1) (hK_nn : 0 ≤ K) (hC_nn : 0 ≤ C_tail)
    (hC_le : C_tail ≤ B_unit)
    (hf_cont : ContinuousOn (fun τ => ‖f τ‖) (Icc a b))
    (hpt : ∀ τ ∈ Icc a b, ‖f τ‖ ≤ K * C_tail) :
    ‖∫ τ in a..b, f τ‖ ≤ K * B_unit := by
  have hKC_nn : 0 ≤ K * C_tail := mul_nonneg hK_nn hC_nn
  have h1 : ‖∫ τ in a..b, f τ‖ ≤ ∫ τ in a..b, K * C_tail :=
    (intervalIntegral.norm_integral_le_integral_norm hab).trans
      (intervalIntegral.integral_mono_on hab (hf_cont.intervalIntegrable_of_Icc hab)
        intervalIntegrable_const hpt)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  calc ‖∫ τ in a..b, f τ‖ ≤ (b - a) * (K * C_tail) := h1
    _ ≤ 1 * (K * C_tail) := mul_le_mul_of_nonneg_right hba hKC_nn
    _ = K * C_tail := one_mul _
    _ ≤ K * B_unit := mul_le_mul_of_nonneg_left hC_le hK_nn

private lemma ray_seg_integral_le' {f : ℝ → ℂ} {d : ℝ → ℝ} {a b t_max α_g K W_pt C_tail : ℝ}
    (ha : a = 0) (hb : b = t_max) (ht_nn : 0 ≤ t_max) (ht_le1 : t_max ≤ 1)
    (_hα : 0 < α_g) (hK_nn : 0 ≤ K) (hW_nn : 0 ≤ W_pt) (hC_nn : 0 ≤ C_tail)
    (hd_cont : Continuous d)
    (hf_cont : ContinuousOn (fun τ => ‖f τ‖) (Icc 0 t_max))
    (hgauss : ∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2) ≤
      (Real.pi / 2) / Real.sqrt α_g)
    (hpt : ∀ τ ∈ Icc (0 : ℝ) t_max,
      ‖f τ‖ ≤ (K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) :
    ‖∫ τ in a..b, f τ‖ ≤ K * (W_pt * ((Real.pi / 2) / Real.sqrt α_g) + C_tail) := by
  rw [ha, hb]
  have hg_cont : ContinuousOn (fun τ : ℝ => (K * W_pt) * Real.exp (-α_g * d τ ^ 2))
      (Icc 0 t_max) := by fun_prop
  have hrhs_cont : ContinuousOn
      (fun τ : ℝ => (K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail)
      (Icc 0 t_max) := hg_cont.add continuousOn_const
  have hint_le : ‖∫ τ in (0 : ℝ)..t_max, f τ‖ ≤
      ∫ τ in (0 : ℝ)..t_max, ((K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) :=
    (intervalIntegral.norm_integral_le_integral_norm ht_nn).trans
      (intervalIntegral.integral_mono_on ht_nn (hf_cont.intervalIntegrable_of_Icc ht_nn)
        (hrhs_cont.intervalIntegrable_of_Icc ht_nn) hpt)
  have hint_split : ∫ τ in (0 : ℝ)..t_max,
        ((K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) =
      (K * W_pt) * (∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2)) +
        t_max * (K * C_tail) := by
    rw [intervalIntegral.integral_add (hg_cont.intervalIntegrable_of_Icc ht_nn) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  calc ‖∫ τ in (0 : ℝ)..t_max, f τ‖
      ≤ (K * W_pt) * (∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2)) +
          t_max * (K * C_tail) := hint_le.trans_eq hint_split
    _ ≤ (K * W_pt) * ((Real.pi / 2) / Real.sqrt α_g) + 1 * (K * C_tail) :=
        add_le_add (mul_le_mul_of_nonneg_left hgauss (mul_nonneg hK_nn hW_nn))
          (mul_le_mul_of_nonneg_right ht_le1 (mul_nonneg hK_nn hC_nn))
    _ = K * (W_pt * ((Real.pi / 2) / Real.sqrt α_g) + C_tail) := by ring

private lemma lemma_Z_log_seg_bound (W : ZWitness) (P : ZPConfig)
    {c' Λ φ ρ κ_exp ρ_min_Z tail_Z M_g K_seg B_seg_unit : ℝ}
    {g : ℝ → ℝ} {s b t u : ℂ} (S : ContourSeg)
    (hc'_pos : 0 < c') (hc'_24 : 24 ≤ c') (hc'_48 : 48 / P.c_Γ ≤ c') (hc'_S4 : W.c_S4 ≤ c')
    (hΛ_nn : 0 ≤ Λ) (hsin_pos : 0 < Real.sin φ) (hρ_pos : 0 < ρ) (hs_re_pos : 0 < s.re)
    (hρ_min_pos : 0 < ρ_min_Z) (hρ_ge_min : ρ_min_Z ≤ ρ)
    (hc_ρ_sre_sq : 2 * Real.log c' ≤ (P.c_γ / 16) * (c' * ρ * s.re ^ 2))
    (_hlog_nn : 0 ≤ Real.log c')
    (hκ_exp_pos : 0 < κ_exp)
    (hκ_arc : κ_exp ≤ P.κ_arc * ρ_min_Z ^ 3)
    (hκ_strip : κ_exp ≤ P.κ_strip)
    (htail_ge1 : 1 ≤ tail_Z) (htail_ge2 : 2 / κ_exp ^ 2 ≤ tail_Z)
    (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < M_g) (hM_eq : M_g = virasoroProblem.cardyNorm (c' / 12) g)
    (hb_re_pos : 0 < b.re) (ht_re_pos : 0 < t.re) (ht_eq : t = (c' : ℂ) * b ^ 2 / 3)
    (ht_half_ub : ‖t ^ (-(1 / 2 : ℂ))‖ ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)))
    (hair_eq : Real.exp (c' * (chartPhiV s b).re) = airyEnv u)
    (hK_seg_eq : K_seg = (4 * Real.sqrt 3 / xiStar) * P.C_d * M_g *
      c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv u)
    (hB_seg_eq : B_seg_unit =
      (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
        ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) +
      max W.C_S4 W.C_S2 * (tail_Z * c' ^ (-2 : ℝ)))
    (hwin_wv : ∀ ζ ∈ stripClosed, ‖ζ - s‖ ≤ s.re / 4 →
      ‖tildeWV c' g ζ‖ ≤ M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ))
    (hS2_P : ∀ {ω : ℂ}, P.μ₀ ≤ ω.re →
      ‖mellinMG g (1 / 2 + (c' : ℂ) * ω)‖ ≤
        W.C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB ω) * M_g)
    (hba : S.b - S.a ≤ 1)
    (hω_bd : ∀ τ ∈ Icc S.a S.b,
      0 ≤ (S.ω τ).re ∧ P.c_Γ ≤ ‖S.ω τ‖ ∧ ‖S.ω τ‖ ≤ P.C_Γ ∧ ‖S.ω' τ‖ ≤ P.C_d)
    (h_ur : S.isStrip = true → S.kind = .upperRay →
      ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
        ∀ τ ∈ Icc 0 t_max, ‖S.ζ τ - s‖ = t_max - τ ∧ ‖S.ζ' τ‖ = 1 ∧
          (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * (t_max - τ) ^ 2)
    (h_lr : S.isStrip = true → S.kind = .lowerRay →
      ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
        ∀ τ ∈ Icc 0 t_max, ‖S.ζ τ - s‖ = τ ∧ ‖S.ζ' τ‖ = 1 ∧
          (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * τ ^ 2)
    (h_ar : S.isStrip = true → S.kind = .arcRadial →
      ∀ τ ∈ Icc S.a S.b, (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.κ_arc * ρ ^ 3)
    (h_fs : S.isStrip = true → S.kind = .fixedStrip →
      ∀ τ ∈ Icc S.a S.b, (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.κ_strip)
    (hnonstrip : S.isStrip = false → ∀ τ ∈ Icc S.a S.b,
      P.μ₀ ≤ (S.ω τ).re ∧ crudeExponentEc (S.ω τ) b ≤ (chartPhiV s b).re - P.c_γ * ρ * s.re ^ 2)
    (h_no_crude : S.isStrip = true → S.kind ≠ .crudeEdge) :
    ‖∫ τ in S.a..S.b, mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤ K_seg * B_seg_unit := by
  have hK_seg_pos : 0 < K_seg := by
    rw [hK_seg_eq]
    have := xiStar_pos; have := P.hC_d_pos; have := airyEnv_pos u; positivity
  have hKM_nn : 0 ≤ K_seg / M_g := div_nonneg hK_seg_pos.le hM_pos.le
  have hCS_max_pos : 0 < max W.C_S4 W.C_S2 := lt_of_lt_of_le W.hCS4 (le_max_left _ _)
  set C_tail_u : ℝ := max W.C_S4 W.C_S2 * (tail_Z * c' ^ (-2 : ℝ))
  have hC_tail_nn : 0 ≤ C_tail_u := by dsimp [C_tail_u]; positivity
  set W_pt : ℝ := 2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ
  have hW_pt_nn : 0 ≤ W_pt := by dsimp [W_pt]; positivity
  have hwin_term_nn : 0 ≤ W_pt * ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) := by
    have := P.hc_γ_pos; positivity
  have hC_tail_le_B : C_tail_u ≤ B_seg_unit := by
    rw [hB_seg_eq]; dsimp [W_pt, C_tail_u]; linarith only [hwin_term_nn]
  have hc_m2_eq : Real.exp (-2 * Real.log c') = c' ^ (-2 : ℝ) := by
    rw [Real.rpow_def_of_pos hc'_pos]; congr 1; ring
  have hlog_tail : Real.exp (-((P.c_γ / 16) * (c' * ρ * s.re ^ 2))) ≤ tail_Z * c' ^ (-2 : ℝ) := by
    calc Real.exp (-((P.c_γ / 16) * (c' * ρ * s.re ^ 2)))
        ≤ Real.exp (-2 * Real.log c') := Real.exp_le_exp.mpr (by linarith only [hc_ρ_sre_sq])
      _ = 1 * c' ^ (-2 : ℝ) := by rw [hc_m2_eq, one_mul]
      _ ≤ tail_Z * c' ^ (-2 : ℝ) := by gcongr
  have hexp_tail_κ : ∀ {κ : ℝ}, κ_exp ≤ κ → Real.exp (-κ * c') ≤ tail_Z * c' ^ (-2 : ℝ) := by
    intro κ hκ
    have h1 : Real.exp (-κ * c') ≤ Real.exp (-κ_exp * c') :=
      Real.exp_le_exp.mpr (by nlinarith only [hκ, hc'_pos])
    have h2 := exp_neg_kappa_le_inv_sq hκ_exp_pos hc'_pos
    calc Real.exp (-κ * c') ≤ (2 / κ_exp ^ 2) * c' ^ (-2 : ℝ) := h1.trans h2
      _ ≤ tail_Z * c' ^ (-2 : ℝ) := by gcongr
  have hstrip_mul_le : ∀ {A B E₁ E₂ : ℝ}, 0 ≤ B → A ≤ B → 0 ≤ E₁ → E₁ ≤ E₂ →
      (K_seg / M_g) * A * E₁ ≤ (K_seg / M_g) * B * E₂ := fun hB hAB hE1 hE =>
    mul_le_mul (mul_le_mul_of_nonneg_left hAB hKM_nn) hE hE1 (mul_nonneg hKM_nn hB)
  have hcont_seg : ContinuousOn (fun τ => mellinDensityIntegrand c' g t (S.ω τ)) (Icc S.a S.b) := by
    intro τ hτ
    have hω_re_nn := (hω_bd τ hτ).1
    have hz_re : 0 < (1 / 2 + (c' : ℂ) * S.ω τ).re := by
      have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      simp only [Complex.add_re, h12, Complex.re_ofReal_mul]
      have hcw := mul_nonneg hc'_pos.le hω_re_nn
      linarith only [hcw]
    have hGam_d : DifferentiableAt ℂ Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) :=
      Complex.differentiableAt_Gamma _ (fun m hm => by
        have hrm := congrArg Complex.re hm
        simp only [Complex.neg_re, Complex.natCast_re] at hrm
        linarith only [hz_re, hrm, Nat.cast_nonneg (α := ℝ) m])
    have h_an_w : DifferentiableAt ℂ (mellinDensityIntegrand c' g t) (S.ω τ) := by
      have hm_d := (differentiable_mellinMGEntire (by linarith only [hc'_24] : 2 ≤ c' / 12) hg).differentiableAt
        (x := 1 / 2 + (c' : ℂ) * S.ω τ)
      have ht_ne : (2 * (Real.pi : ℂ) * t) ≠ 0 := by
        have ht0 : t ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at ht_re_pos; exact lt_irrefl 0 ht_re_pos
        exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ht0
      have hlin : DifferentiableAt ℂ (fun ω : ℂ => 1 / 2 + (c' : ℂ) * ω) (S.ω τ) := by fun_prop
      have hp_d : DifferentiableAt ℂ (fun ω : ℂ =>
          (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * ω))) (S.ω τ) := by
        have hex : (fun ω : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * ω))) =
            fun ω => Complex.exp (Complex.log (2 * (Real.pi : ℂ) * t) * (-(1 / 2 + (c' : ℂ) * ω))) := by
          ext ω; rw [Complex.cpow_def_of_ne_zero ht_ne]
        rw [hex]; fun_prop
      exact ((DifferentiableAt.comp (g := Complex.Gamma) (S.ω τ) hGam_d hlin).mul hp_d).mul
        (DifferentiableAt.comp (g := mellinMGEntire g) (S.ω τ) hm_d hlin)
    exact h_an_w.continuousAt.comp_continuousWithinAt (S.hω_cont τ hτ)
  have hf_cont : ContinuousOn
      (fun τ => ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖) (Icc S.a S.b) :=
    (hcont_seg.mul S.hω'_cont).norm
  have hpt_stirling : ∀ τ ∈ Icc S.a S.b,
      let ω := S.ω τ
      0 < (1 / 2 + (c' : ℂ) * ω).re ∧
      ‖stirlingS c' ω‖ ≤ 2 ∧
      mellinDensityIntegrand c' g t ω =
        t ^ (-(1 / 2 : ℂ)) * stirlingS c' ω *
          Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ ω b) *
          mellinMG g (1 / 2 + (c' : ℂ) * ω) := fun τ hτ => by
    obtain ⟨hω_re, hω_lb, _, _⟩ := hω_bd τ hτ
    have hcω_48 : 48 ≤ c' * ‖S.ω τ‖ :=
      ((div_le_iff₀ P.hc_Γ_pos).mp hc'_48).trans (mul_le_mul_of_nonneg_left hω_lb hc'_pos.le)
    have hω_ne : S.ω τ ≠ 0 := by intro h0; rw [h0, norm_zero, mul_zero] at hcω_48; linarith only [hcω_48]
    have hS_bd : ‖stirlingS c' (S.ω τ)‖ ≤ 2 := by
      have h1 : 1 ≤ c' * ‖S.ω τ‖ := by linarith only [hcω_48]
      have hsub := norm_stirlingS_sub_one_le hc'_pos hω_re h1
      have hle : 24 / (c' * ‖S.ω τ‖) ≤ 1 / 2 := by
        calc 24 / (c' * ‖S.ω τ‖) ≤ 24 / 48 := by gcongr
          _ = 1 / 2 := by norm_num
      have htr : ‖stirlingS c' (S.ω τ)‖ ≤ ‖stirlingS c' (S.ω τ) - 1‖ + ‖(1 : ℂ)‖ := by
        calc ‖stirlingS c' (S.ω τ)‖ = ‖(stirlingS c' (S.ω τ) - 1) + 1‖ := by ring_nf
          _ ≤ ‖stirlingS c' (S.ω τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      rw [norm_one] at htr; linarith only [htr, hsub, hle]
    have hz_re : 0 < (1 / 2 + (c' : ℂ) * S.ω τ).re := by
      have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      simp only [Complex.add_re, h12, Complex.re_ofReal_mul]
      have hcw := mul_nonneg hc'_pos.le hω_re
      linarith only [hcw]
    have h_st := gamma_mul_two_pi_t_cpow_neg hc'_pos (ω := S.ω τ) (b := b) hω_re hω_ne hb_re_pos
    rw [← ht_eq] at h_st
    refine ⟨hz_re, hS_bd, ?_⟩
    unfold mellinDensityIntegrand
    dsimp only
    rw [mellinMGEntire_of_re_pos g hz_re]
    calc Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) *
          (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * S.ω τ)) *
          mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ)
        = (Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) *
            (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * S.ω τ))) *
            mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ) := rfl
      _ = _ := by rw [h_st]; ring
  have hpt_strip_prod : ∀ (hstr : S.isStrip = true), ∀ τ ∈ Icc S.a S.b,
      ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤
        (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
          Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
    intro hstr τ hτ
    obtain ⟨hz_re, hS_bd, hmel_eq⟩ := hpt_stirling τ hτ
    have hω'_bd := (hω_bd τ hτ).2.2.2
    have hω_ζ := (S.hζ_strip hstr τ hτ).2.2.1
    have hstrip_id : mellinDensityIntegrand c' g t (S.ω τ) =
        t ^ (-(1 / 2 : ℂ)) * stirlingS c' (S.ω τ) *
          Complex.exp ((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b) *
          tildeWV c' g (S.ζ τ) := by
      rw [hmel_eq, ← mellinMGEntire_of_re_pos g hz_re]
      unfold tildeWV chartPhiV
      rw [← hω_ζ]
      have hex : Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ (S.ω τ) b) =
          Complex.exp ((c' : ℂ) * (chartUpsilon (S.ζ τ) +
              ComplexBessel.stirlingJ (S.ω τ) b + tipL b) - (c' : ℂ) * tipL b) *
            Complex.exp (-(c' : ℂ) * chartUpsilon (S.ζ τ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [hex]; ring
    rw [norm_mul, hstrip_id, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
    have hexp_eq : Real.exp (((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b).re) =
        Real.exp (-(c' * (tipL b).re)) * airyEnv u *
          Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
      rw [← hair_eq, ← Real.exp_add, ← Real.exp_add]
      congr 1; simp only [Complex.sub_re, Complex.re_ofReal_mul]; ring
    rw [hexp_eq]
    calc ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingS c' (S.ω τ)‖ *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))) *
            ‖tildeWV c' g (S.ζ τ)‖ * ‖S.ω' τ‖
        ≤ ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))) *
            ‖tildeWV c' g (S.ζ τ)‖ * P.C_d := by
          have := xiStar_pos; have := airyEnv_pos u; gcongr
      _ = (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
            Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
          rw [hK_seg_eq]; field_simp [hM_pos.ne']; ring
  have hray_unified : ∀ (hstr : S.isStrip = true) (t_max : ℝ) (ht_nn : 0 ≤ t_max)
      (ha_eq : S.a = 0) (hb_eq_t : S.b = t_max) (d : ℝ → ℝ),
      Continuous d →
      (∫ τ in (0 : ℝ)..t_max, Real.exp (-(c' * P.c_γ * ρ) * d τ ^ 2) ≤
        (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) →
      (∀ τ ∈ Icc (0 : ℝ) t_max, ‖S.ζ τ - s‖ = d τ ∧
        (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * d τ ^ 2) →
      ‖∫ τ in S.a..S.b, mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤ K_seg * B_seg_unit := by
    intro hstr t_max ht_nn ha_eq hb_eq_t d hd_cont hgauss hray_d
    set α_g : ℝ := c' * P.c_γ * ρ
    have hα_g_pos : 0 < α_g := mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos
    have hpt_ray : ∀ τ ∈ Icc (0 : ℝ) t_max,
        ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤
          (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) + K_seg * C_tail_u := by
      intro τ hτ
      have hτ' : τ ∈ Icc S.a S.b := by rwa [ha_eq, hb_eq_t]
      have hbase := hpt_strip_prod hstr τ hτ'
      obtain ⟨hdist_eq, hphi_bd⟩ := hray_d τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ'
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hexp_gauss : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          Real.exp (-α_g * d τ ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤ -P.c_γ * ρ * d τ ^ 2 := by
          linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        dsimp [α_g]; linarith only [hm]
      by_cases hwin : d τ ≤ s.re / 4
      · have hdist_win : ‖S.ζ τ - s‖ ≤ s.re / 4 := hdist_eq.trans_le hwin
        have hwv := hwin_wv (S.ζ τ) hζ_cl hdist_win
        have h1 : (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) := by
          calc (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
                  Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))
              ≤ (K_seg / M_g) * (M_g * W_pt) * Real.exp (-α_g * d τ ^ 2) :=
                hstrip_mul_le (mul_nonneg hM_pos.le hW_pt_nn) hwv (Real.exp_pos _).le hexp_gauss
            _ = (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) := by field_simp [hM_pos.ne']
        have hct_nn : 0 ≤ K_seg * C_tail_u := mul_nonneg hK_seg_pos.le hC_tail_nn
        linarith only [hbase, h1, hct_nn]
      · have hgt : s.re / 4 ≤ d τ := le_of_not_ge hwin
        have hsq_ge : (s.re / 4) ^ 2 ≤ d τ ^ 2 :=
          pow_le_pow_left₀ (div_nonneg hs_re_pos.le (by norm_num)) hgt 2
        have hexp_tail : Real.exp (-α_g * d τ ^ 2) ≤ tail_Z * c' ^ (-2 : ℝ) := by
          have h1 : (P.c_γ / 16) * (c' * ρ * s.re ^ 2) ≤ α_g * d τ ^ 2 := by
            have h16 : (P.c_γ / 16) * (c' * ρ * s.re ^ 2) = α_g * (s.re / 4) ^ 2 := by
              dsimp [α_g]; ring
            rw [h16]
            exact mul_le_mul_of_nonneg_left hsq_ge hα_g_pos.le
          exact (Real.exp_le_exp.mpr (by linarith only [h1])).trans hlog_tail
        have hwv_s4 : ‖tildeWV c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
          have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
          rw [← hM_eq] at h0
          exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
        have h1 : (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            K_seg * C_tail_u := by
          calc (K_seg / M_g) * ‖tildeWV c' g (S.ζ τ)‖ *
                  Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))
              ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) * (tail_Z * c' ^ (-2 : ℝ)) :=
                hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
                  (Real.exp_pos _).le (hexp_gauss.trans hexp_tail)
            _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']
        have hcw_nn : 0 ≤ (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) :=
          mul_nonneg (mul_nonneg hK_seg_pos.le hW_pt_nn) (Real.exp_pos _).le
        linarith only [hbase, h1, hcw_nn]
    have hf_cont0 : ContinuousOn
        (fun τ => ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖) (Icc 0 t_max) := by
      rwa [← ha_eq, ← hb_eq_t]
    have ht_le1 : t_max ≤ 1 := by have h1 := hba; rw [ha_eq, hb_eq_t, sub_zero] at h1; exact h1
    have hres := ray_seg_integral_le' ha_eq hb_eq_t ht_nn ht_le1 hα_g_pos
      hK_seg_pos.le hW_pt_nn hC_tail_nn hd_cont hf_cont0 hgauss hpt_ray
    rwa [← hB_seg_eq] at hres
  cases hstr : S.isStrip
  · refine const_seg_integral_le' S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
    intro τ hτ
    obtain ⟨_, hS_bd, hmel_eq⟩ := hpt_stirling τ hτ
    have hω'_bd := (hω_bd τ hτ).2.2.2
    obtain ⟨hμ₀_le, hEc_le⟩ := hnonstrip hstr τ hτ
    have hS2_bd := hS2_P hμ₀_le
    rw [norm_mul, hmel_eq, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    have hexp_ec : Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
        Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) ≤
        Real.exp (-(c' * (tipL b).re)) * airyEnv u * (tail_Z * c' ^ (-2 : ℝ)) := by
      have hexp1 : Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
          Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) ≤
          Real.exp (-(c' * (tipL b).re)) * airyEnv u *
            Real.exp (-((P.c_γ / 16) * (c' * ρ * s.re ^ 2))) := by
        rw [← hair_eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hEc_def : crudeExponentEc (S.ω τ) b =
            ComplexBessel.crudeExponentB (S.ω τ) + (ComplexBessel.stirlingJ (S.ω τ) b).re +
              (tipL b).re := rfl
        have h1 : c' * crudeExponentEc (S.ω τ) b ≤
            c' * (chartPhiV s b).re - c' * P.c_γ * ρ * s.re ^ 2 := by
          have hm := mul_le_mul_of_nonneg_left hEc_le hc'_pos.le
          linarith only [hm]
        have h16 : (P.c_γ / 16) * (c' * ρ * s.re ^ 2) ≤ c' * P.c_γ * ρ * s.re ^ 2 := by
          have hnn : 0 ≤ P.c_γ * (c' * ρ * s.re ^ 2) :=
            mul_nonneg P.hc_γ_pos.le (mul_nonneg (mul_nonneg hc'_pos.le hρ_pos.le) (sq_nonneg _))
          linarith only [hnn]
        rw [hEc_def, mul_add, mul_add] at h1
        linarith only [h1, h16]
      have hpre_nn : 0 ≤ Real.exp (-(c' * (tipL b).re)) * airyEnv u := by
        have := airyEnv_pos u; positivity
      exact hexp1.trans (mul_le_mul_of_nonneg_left hlog_tail hpre_nn)
    have hCS2_max : W.C_S2 ≤ max W.C_S4 W.C_S2 := le_max_right _ _
    have hK_pref_nn : 0 ≤ (4 * Real.sqrt 3 / xiStar) * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) := by
      have := xiStar_pos; have := P.hC_d_pos; positivity
    calc ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingS c' (S.ω τ)‖ *
            Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
            ‖mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ)‖ * ‖S.ω' τ‖
        ≤ ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
            Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
            (W.C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) * M_g) * P.C_d := by
          have := xiStar_pos; have := W.hCS2; gcongr
      _ = ((4 * Real.sqrt 3 / xiStar) * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) * W.C_S2) *
            (Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
              Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ))) := by ring
      _ ≤ ((4 * Real.sqrt 3 / xiStar) * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) * max W.C_S4 W.C_S2) *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u * (tail_Z * c' ^ (-2 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hCS2_max hK_pref_nn) hexp_ec
            (by positivity) (mul_nonneg hK_pref_nn hCS_max_pos.le)
      _ = K_seg * C_tail_u := by rw [hK_seg_eq]; dsimp [C_tail_u]; ring
  · cases hkind : S.kind
    · obtain ⟨t_max, ht_max_nn, ha_eq, hb_eq_t, _, hray⟩ := h_ur hstr hkind
      exact hray_unified hstr t_max ht_max_nn ha_eq hb_eq_t (fun τ => t_max - τ)
        (continuous_const.sub continuous_id)
        (integral_exp_neg_mul_sub_sq_le' (mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos) ht_max_nn)
        (fun τ hτ => ⟨(hray τ hτ).1, (hray τ hτ).2.2⟩)
    · obtain ⟨t_max, ht_max_nn, ha_eq, hb_eq_t, _, hray⟩ := h_lr hstr hkind
      exact hray_unified hstr t_max ht_max_nn ha_eq hb_eq_t (fun τ => τ)
        continuous_id
        (integral_exp_neg_mul_sq_le' (mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos) ht_max_nn)
        (fun τ hτ => ⟨(hray τ hτ).1, (hray τ hτ).2.2⟩)
    · refine const_seg_integral_le' S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
      intro τ hτ
      have hbase := hpt_strip_prod hstr τ hτ
      have hphi_bd := h_ar hstr hkind τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hwv_s4 : ‖tildeWV c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
        have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
        rw [← hM_eq] at h0
        exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
      have hexp_arc : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          tail_Z * c' ^ (-2 : ℝ) := by
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤ -P.κ_arc * ρ ^ 3 := by
          linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        have hρ_cube : ρ_min_Z ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hρ_min_pos.le hρ_ge_min 3
        have hκ : κ_exp ≤ P.κ_arc * ρ ^ 3 :=
          hκ_arc.trans (mul_le_mul_of_nonneg_left hρ_cube P.hκ_arc_pos.le)
        have hexp_1 : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            Real.exp (-(P.κ_arc * ρ ^ 3) * c') :=
          Real.exp_le_exp.mpr (by linarith only [hm])
        exact hexp_1.trans (hexp_tail_κ hκ)
      calc ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖
          ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) * (tail_Z * c' ^ (-2 : ℝ)) :=
            hbase.trans (hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
              (Real.exp_pos _).le hexp_arc)
        _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']
    · exact absurd hkind (h_no_crude hstr)
    · refine const_seg_integral_le' S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
      intro τ hτ
      have hbase := hpt_strip_prod hstr τ hτ
      have hphi_bd := h_fs hstr hkind τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hwv_s4 : ‖tildeWV c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
        have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
        rw [← hM_eq] at h0
        exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
      have hexp_fs : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          tail_Z * c' ^ (-2 : ℝ) := by
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤ -P.κ_strip := by
          linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        have hexp_1 : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            Real.exp (-P.κ_strip * c') :=
          Real.exp_le_exp.mpr (by linarith only [hm])
        exact hexp_1.trans (hexp_tail_κ hκ_strip)
      calc ‖mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖
          ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) * (tail_Z * c' ^ (-2 : ℝ)) :=
            hbase.trans (hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
              (Real.exp_pos _).le hexp_fs)
        _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']

private lemma lemma_Z_log_combine_envelope (W : ZWitness) (P : ZPConfig)
    {b_hi c' Λ φ ρ κ_exp tail_Z C_pref B_seg_unit C_B : ℝ}
    {g : ℝ → ℝ} {u : ℂ}
    (hb_hi_pos : 0 < b_hi) (hc'_pos : 0 < c') (hc'_ge1 : 1 ≤ c')
    (hΛ : 1 ≤ Λ) (hκ_exp_pos : 0 < κ_exp) (hκ_le_D : κ_exp ≤ W.d_D)
    (htail_ge2 : 2 / κ_exp ^ 2 ≤ tail_Z)
    (hC_pref_pos : 0 < C_pref)
    (hu_pos : 0 < ‖u‖) (hu_bhi : ‖u‖ ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ))
    (hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re)
    (hu_re_eq : (u ^ (1 / 2 : ℂ)).re = Real.sqrt ‖u‖ * Real.sin φ)
    (hsin_pos : 0 < Real.sin φ) (hsin_le1 : Real.sin φ ≤ 1)
    (_hρ_pos : 0 < ρ)
    (hρ_lo : (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt ‖u‖) ≤ ρ)
    (hB_seg_eq : B_seg_unit =
      (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
        ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) +
      max W.C_S4 W.C_S2 * (tail_Z * c' ^ (-2 : ℝ)))
    (hCB_ge : 12 * C_pref * Real.pi / Real.sqrt ((9 / 10 : ℝ) * P.c_γ * kappaV) *
        b_hi ^ (5 / 2 : ℝ) +
      (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * tail_Z * b_hi ^ 3 ≤ C_B)
    (hP_norm : ‖truncatedMellinP c' dpT0 g u‖ ≤
      12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u)
    (hDp_u : ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ ≤
      W.C_D * Real.exp (-W.d_D * c') * airyEnv u) :
    ‖virasoroPsiTilde c' g u‖ ≤
      C_B * Λ * airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
  have htail_nn : 0 ≤ tail_Z := le_trans (by positivity) htail_ge2
  set a' : ℝ := Real.sqrt ‖u‖
  have ha'_pos : 0 < a' := Real.sqrt_pos.mpr hu_pos
  set c_γ_kap : ℝ := (9 / 10 : ℝ) * P.c_γ * kappaV
  have hc_γ_kap_pos : 0 < c_γ_kap := by have := P.hc_γ_pos; have := kappaV_pos; positivity
  set C_win_tot : ℝ := 12 * C_pref * Real.pi / Real.sqrt c_γ_kap * b_hi ^ (5 / 2 : ℝ)
  set C_tail_tot : ℝ := (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * tail_Z * b_hi ^ 3
  have hDp_exp_le : Real.exp (-W.d_D * c') ≤ tail_Z * c' ^ (-2 : ℝ) := by
    have h1 : Real.exp (-W.d_D * c') ≤ Real.exp (-κ_exp * c') :=
      Real.exp_le_exp.mpr (by nlinarith only [hκ_le_D, hc'_pos])
    exact (h1.trans (exp_neg_kappa_le_inv_sq hκ_exp_pos hc'_pos)).trans (by gcongr)
  have hDp_c13 : W.C_D * Real.exp (-W.d_D * c') * airyEnv u ≤
      W.C_D * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ)) * airyEnv u := by
    have hc13_ge1 : 1 ≤ c' ^ (1 / 3 : ℝ) := Real.one_le_rpow hc'_ge1 (by norm_num)
    have hair_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
    calc W.C_D * Real.exp (-W.d_D * c') * airyEnv u
        ≤ W.C_D * (tail_Z * c' ^ (-2 : ℝ)) * airyEnv u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDp_exp_le W.hC_D.le) hair_nn
      _ = W.C_D * 1 * (tail_Z * c' ^ (-2 : ℝ)) * airyEnv u := by ring
      _ ≤ W.C_D * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ)) * airyEnv u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc13_ge1 W.hC_D.le) (by positivity [htail_nn])) hair_nn
  set u_re : ℝ := (u ^ (1 / 2 : ℂ)).re
  set u_n : ℝ := ‖u‖
  have hu_re_ub : u_re ≤ u_n ^ (1 / 2 : ℝ) := by
    rw [hu_re_eq, ← Real.sqrt_eq_rpow]
    exact mul_le_of_le_one_right ha'_pos.le hsin_le1
  have hfac_pos : 0 < u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by positivity
  have hwin_prod_le :
      (12 * C_pref * c' ^ (1 / 3 : ℝ) *
          ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
            ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)))) *
        (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤ C_win_tot * Λ := by
    have hsqrt_ρ_lb : Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ) ≤
        Real.sqrt (c' * P.c_γ * ρ) := by
      have h1 : c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ) ≤ c' * P.c_γ * ρ := by
        have hc23 : c' * c' ^ (-(1 / 3 : ℝ)) = c' ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_one_add' hc'_pos.le (by norm_num : (1 : ℝ) + -(1 / 3 : ℝ) ≠ 0)]; norm_num
        have ha_rpow : a' = u_n ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow u_n
        calc c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ)
            = c' * P.c_γ * ((9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a')) := by
              rw [← hc23, ← ha_rpow]; dsimp [c_γ_kap]; ring
          _ ≤ c' * P.c_γ * ρ := mul_le_mul_of_nonneg_left hρ_lo (mul_nonneg hc'_pos.le P.hc_γ_pos.le)
      have hrt := Real.sqrt_le_sqrt h1
      have hlhs : Real.sqrt (c_γ_kap * c' ^ (2 / 3 : ℝ) * u_n ^ (1 / 2 : ℝ)) =
          Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc_γ_kap_pos.le,
          Real.sqrt_eq_rpow (c' ^ (2 / 3 : ℝ)), Real.sqrt_eq_rpow (u_n ^ (1 / 2 : ℝ)),
          ← Real.rpow_mul hc'_pos.le, ← Real.rpow_mul hu_pos.le]
        norm_num
      rwa [hlhs] at hrt
    have hinv_sqrt : (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ) ≤
        (Real.pi / (2 * Real.sqrt c_γ_kap)) * c' ^ (-(1 / 3 : ℝ)) * u_n ^ (-(1 / 4 : ℝ)) := by
      have h1 : (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ) ≤
          (Real.pi / 2) / (Real.sqrt c_γ_kap * c' ^ (1 / 3 : ℝ) * u_n ^ (1 / 4 : ℝ)) := by gcongr
      refine h1.trans_eq ?_
      rw [Real.rpow_neg hc'_pos.le, Real.rpow_neg hu_pos.le]
      field_simp [hc_γ_kap_pos.ne']
    have hure_sin : (u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ) ≤ u_n ^ (3 / 2 : ℝ) := by
      have hsplit : u_re ^ (3 / 2 : ℝ) = u_re * u_re ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hu_re_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]; norm_num
      have hdiv_sin : u_re / Real.sin φ = u_n ^ (1 / 2 : ℝ) := by
        rw [show u_re = a' * Real.sin φ from hu_re_eq, mul_div_cancel_right₀ _ hsin_pos.ne']
        exact Real.sqrt_eq_rpow u_n
      have hure_14 : u_re ^ (1 / 2 : ℝ) ≤ u_n ^ (1 / 4 : ℝ) := by
        calc u_re ^ (1 / 2 : ℝ) ≤ (u_n ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_re_pos.le hu_re_ub (by norm_num)
          _ = u_n ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hu_pos.le]; norm_num
      calc (u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ)
          = (u_re / Real.sin φ) * u_re ^ (1 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by rw [hsplit]; ring
        _ = u_n ^ (1 / 2 : ℝ) * u_re ^ (1 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) := by rw [hdiv_sin]
        _ ≤ u_n ^ (1 / 2 : ℝ) * u_n ^ (1 / 4 : ℝ) * u_n ^ (3 / 4 : ℝ) := by gcongr
        _ = u_n ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]; norm_num
    have hun_54 : c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ)) ≤
        b_hi ^ (5 / 2 : ℝ) := by
      have hsum : u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ) = u_n ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_add hu_pos]; norm_num
      have hub : u_n ^ (5 / 4 : ℝ) ≤ b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ) := by
        calc u_n ^ (5 / 4 : ℝ) ≤ (b_hi ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (5 / 4 : ℝ) :=
              Real.rpow_le_rpow hu_pos.le hu_bhi (by norm_num)
          _ = b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ) := by
              rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hc'_pos.le _),
                ← Real.rpow_natCast b_hi 2, ← Real.rpow_mul hb_hi_pos.le,
                ← Real.rpow_mul hc'_pos.le]; norm_num
      rw [hsum]
      calc c' ^ (-(5 / 6 : ℝ)) * u_n ^ (5 / 4 : ℝ)
          ≤ c' ^ (-(5 / 6 : ℝ)) * (b_hi ^ (5 / 2 : ℝ) * c' ^ (5 / 6 : ℝ)) := by gcongr
        _ = b_hi ^ (5 / 2 : ℝ) * (c' ^ (-(5 / 6 : ℝ)) * c' ^ (5 / 6 : ℝ)) := by ring
        _ = b_hi ^ (5 / 2 : ℝ) := by
            rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
    have hc13_cancel : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero]
    calc (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ (12 * C_pref * c' ^ (1 / 3 : ℝ) *
            ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
              ((Real.pi / (2 * Real.sqrt c_γ_kap)) * c' ^ (-(1 / 3 : ℝ)) * u_n ^ (-(1 / 4 : ℝ))))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) := by gcongr
      _ = (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ *
            (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) *
            (c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) *
              ((u_re ^ (3 / 2 : ℝ) / Real.sin φ) * u_n ^ (3 / 4 : ℝ)))) := by ring
      _ ≤ (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ * 1 *
            (c' ^ (-(5 / 6 : ℝ)) * (u_n ^ (-(1 / 4 : ℝ)) * u_n ^ (3 / 2 : ℝ))) := by
          rw [hc13_cancel]; gcongr
      _ ≤ (12 * C_pref * Real.pi / Real.sqrt c_γ_kap) * Λ * 1 * b_hi ^ (5 / 2 : ℝ) := by gcongr
      _ = C_win_tot * Λ := by dsimp [C_win_tot]; ring
  have htail_prod_le :
      ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ))) *
        (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤ C_tail_tot * Λ := by
    have hfac_ub : u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ) ≤ b_hi ^ 3 * c' := by
      have h1 : u_re ^ (3 / 2 : ℝ) ≤ u_n ^ (3 / 4 : ℝ) := by
        calc u_re ^ (3 / 2 : ℝ) ≤ (u_n ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_re_pos.le hu_re_ub (by norm_num)
          _ = u_n ^ (3 / 4 : ℝ) := by rw [← Real.rpow_mul hu_pos.le]; norm_num
      have h2 : u_n ^ (3 / 2 : ℝ) ≤ b_hi ^ 3 * c' := by
        calc u_n ^ (3 / 2 : ℝ) ≤ (b_hi ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow hu_pos.le hu_bhi (by norm_num)
          _ = b_hi ^ 3 * c' := by
              rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hc'_pos.le _),
                ← Real.rpow_natCast b_hi 2, ← Real.rpow_mul hb_hi_pos.le,
                ← Real.rpow_mul hc'_pos.le]; norm_num
      calc u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)
          ≤ u_n ^ (3 / 4 : ℝ) * u_n ^ (3 / 4 : ℝ) := by gcongr
        _ = u_n ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hu_pos]; norm_num
        _ ≤ b_hi ^ 3 * c' := h2
    have hc_pow : c' ^ (1 / 3 : ℝ) * c' ^ (-2 : ℝ) * c' = c' ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc'_pos, ← Real.rpow_add_one hc'_pos.ne']; norm_num
    have hc_m23_le1 : c' ^ (-(2 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc'_ge1 (by norm_num)
    have hC_pos : 0 < W.C_D + 12 * C_pref * max W.C_S4 W.C_S2 := by
      have := W.hC_D; have := W.hCS4; positivity
    have h1 : c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ)) * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤
        tail_Z * b_hi ^ 3 := by
      calc c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ)) * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
          ≤ c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ)) * (b_hi ^ 3 * c') := by
            gcongr
        _ = tail_Z * b_hi ^ 3 * (c' ^ (1 / 3 : ℝ) * c' ^ (-2 : ℝ) * c') := by ring
        _ = tail_Z * b_hi ^ 3 * c' ^ (-(2 / 3 : ℝ)) := by rw [hc_pow]
        _ ≤ tail_Z * b_hi ^ 3 * 1 := by
            gcongr
        _ = tail_Z * b_hi ^ 3 := mul_one _
    calc ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ))) *
          (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        = (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) *
            (c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ)) * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))) := by ring
      _ ≤ (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * (tail_Z * b_hi ^ 3) := by gcongr
      _ = C_tail_tot * 1 := by dsimp [C_tail_tot]; ring
      _ ≤ C_tail_tot * Λ := by
          have : 0 ≤ C_tail_tot := by dsimp [C_tail_tot]; positivity [htail_nn]
          gcongr
  have hPsi_le_prod : ‖virasoroPsiTilde c' g u‖ ≤
      (12 * C_pref * c' ^ (1 / 3 : ℝ) *
          ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
            ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) +
        (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ))) *
        airyEnv u := by
    have htri : ‖virasoroPsiTilde c' g u‖ ≤
        ‖truncatedMellinP c' dpT0 g u‖ + ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ := by
      calc ‖virasoroPsiTilde c' g u‖
          = ‖truncatedMellinP c' dpT0 g u - (truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u)‖ := by
            ring_nf
        _ ≤ ‖truncatedMellinP c' dpT0 g u‖ + ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ :=
            norm_sub_le _ _
    have hsum_bd : ‖truncatedMellinP c' dpT0 g u‖ + ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ ≤
        12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u +
        W.C_D * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ)) * airyEnv u :=
      add_le_add hP_norm (hDp_u.trans hDp_c13)
    refine htri.trans (hsum_bd.trans_eq ?_)
    rw [hB_seg_eq]
    ring
  have hPsi_prod_le : ‖virasoroPsiTilde c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) ≤
      (C_B * Λ) * airyEnv u := by
    have hair_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
    calc ‖virasoroPsiTilde c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))
        ≤ ((12 * C_pref * c' ^ (1 / 3 : ℝ) *
              ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
                ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ))) +
            (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ))) *
            airyEnv u) * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hPsi_le_prod hfac_pos.le
      _ = ((12 * C_pref * c' ^ (1 / 3 : ℝ) *
              ((2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
                ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)))) * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) +
            ((W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * c' ^ (1 / 3 : ℝ) * (tail_Z * c' ^ (-2 : ℝ))) *
              (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))) * airyEnv u := by ring
      _ ≤ (C_win_tot * Λ + C_tail_tot * Λ) * airyEnv u := by gcongr
      _ = (C_win_tot + C_tail_tot) * Λ * airyEnv u := by ring
      _ ≤ (C_B * Λ) * airyEnv u := by gcongr
  have hinv_cancel : (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
      (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) = 1 := by
    calc (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
          (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)))
        = (u_re ^ (3 / 2 : ℝ) * u_re ^ (-(3 / 2 : ℝ))) *
            (u_n ^ (3 / 4 : ℝ) * u_n ^ (-(3 / 4 : ℝ))) := by ring
      _ = 1 := by
          rw [← Real.rpow_add hu_re_pos, ← Real.rpow_add hu_pos,
            add_neg_cancel, add_neg_cancel, Real.rpow_zero, Real.rpow_zero, mul_one]
  have hinv_nn : 0 ≤ u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)) := by positivity
  calc ‖virasoroPsiTilde c' g u‖
      = ‖virasoroPsiTilde c' g u‖ *
          ((u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ)) *
            (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)))) := by rw [hinv_cancel, mul_one]
    _ = (‖virasoroPsiTilde c' g u‖ * (u_re ^ (3 / 2 : ℝ) * u_n ^ (3 / 4 : ℝ))) *
          (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) := by ring
    _ ≤ ((C_B * Λ) * airyEnv u) * (u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_right hPsi_prod_le hinv_nn
    _ = C_B * Λ * airyEnv u * u_re ^ (-(3 / 2 : ℝ)) * u_n ^ (-(3 / 4 : ℝ)) := by ring

/-- Uniform logarithmic-angle constant `C_ang > 0` for `lemma_Z_log` (`ctl:pass2`). -/
noncomputable def pass2AngleC2 : ℝ :=
  Real.sqrt (2 / ((dpConfig.c_γ / 16) * (25 / 36 : ℝ) * ((18 / 25 : ℝ) * kappaV) ^ 3)) + 1

lemma pass2AngleC2_pos : 0 < pass2AngleC2 := by
  unfold pass2AngleC2; positivity

private lemma pass2AngleC2_decay_ge_two :
    2 ≤ (dpConfig.c_γ / 16) * (25 / 36 : ℝ) * ((18 / 25 : ℝ) * kappaV) ^ 3 * pass2AngleC2 ^ 2 := by
  set d := (dpConfig.c_γ / 16) * (25 / 36 : ℝ) * ((18 / 25 : ℝ) * kappaV) ^ 3
  have hd_pos : 0 < d := by have := dpConfig.hc_γ_pos; have := kappaV_pos; positivity
  have hle : Real.sqrt (2 / d) ≤ pass2AngleC2 := by unfold pass2AngleC2; linarith
  have hsq : 2 / d ≤ pass2AngleC2 ^ 2 := by
    calc 2 / d = (Real.sqrt (2 / d)) ^ 2 := (Real.sq_sqrt (div_nonneg zero_le_two hd_pos.le)).symm
      _ ≤ pass2AngleC2 ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  calc 2 = d * (2 / d) := by field_simp [hd_pos.ne']
    _ ≤ d * pass2AngleC2 ^ 2 := mul_le_mul_of_nonneg_left hsq hd_pos.le

/-- **Logarithmic-angle Lemma Z (`ctl:pass2`, Step 2)**:
for any compact scale band `0 < b_lo ≤ b_hi` with `b_hi^2 ≤ zScaleCap`, an interior multiplier bound
`‖tildeWV c' g ζ‖ ≤ M[g] * (Λ * c'^{-5/6} * ‖ζ‖ / ζ.re)` on the full half-annulus `0 < ζ.re` implies the
covered-arc Airy envelope on `0 ≤ u.im`, `R - 1 ≤ ‖u‖ ≤ R + 1`,
`pass2AngleC2 * R^{-3/4} * √(log c') * √‖u‖ ≤ (u^{1/2}).re`. -/
theorem lemma_Z_log {b_lo b_hi : ℝ} (hb_lo : 0 < b_lo) (hb_le : b_lo ≤ b_hi)
    (hb_cap : b_hi ^ 2 ≤ zScaleCap) :
    ∃ c_Z C_B : ℝ, 10000 ≤ c_Z ∧ 1 ≤ C_B ∧
      ∀ {c' R Λ : ℝ}, c_Z ≤ c' → 1 ≤ Λ →
        b_lo ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
        R + 1 ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) →
        ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          (∀ ζ ∈ stripClosed,
            kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
            ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
            0 < ζ.re →
            ‖tildeWV c' g ζ‖ ≤
              virasoroProblem.cardyNorm (c' / 12) g *
                (Λ * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re)) →
          ∀ {u : ℂ}, 0 ≤ u.im → R - 1 ≤ ‖u‖ → ‖u‖ ≤ R + 1 →
            pass2AngleC2 * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c') * Real.sqrt ‖u‖ ≤
              (u ^ (1 / 2 : ℂ)).re →
            ‖virasoroPsiTilde c' g u‖ ≤
              C_B * Λ * airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨W, hW_eq⟩ : ∃ x : ZWitness, x = zWitness := ⟨_, rfl⟩
  have hb_cap' : b_hi ^ 2 ≤ W.c₀_Z := by rw [hW_eq]; exact hb_cap
  have hb_hi_pos : 0 < b_hi := lt_of_lt_of_le hb_lo hb_le
  set ρ_min_Z : ℝ := (18 / 25 : ℝ) * kappaV * b_lo
  have hρ_min_pos : 0 < ρ_min_Z := mul_pos (mul_pos (by norm_num) kappaV_pos) hb_lo
  set κ_arc_Z : ℝ := dpConfig.κ_arc * ρ_min_Z ^ 3
  have hκ_arc_pos : 0 < κ_arc_Z := mul_pos dpConfig.hκ_arc_pos (pow_pos hρ_min_pos 3)
  set κ_exp : ℝ := min (min κ_arc_Z dpConfig.κ_strip) W.d_D
  have hκ_exp_pos : 0 < κ_exp := lt_min (lt_min hκ_arc_pos dpConfig.hκ_strip_pos) W.hd_D
  set tail_Z : ℝ := max 1 (2 / κ_exp ^ 2)
  set C_pref : ℝ := (innerCDxi * W.C_V / (2 * Real.pi)) * (4 * Real.sqrt 3 / xiStar) * dpConfig.C_d
  have hC_pref_pos : 0 < C_pref :=
    mul_pos (mul_pos (div_pos (mul_pos innerCDxi_pos W.hC_V) (mul_pos two_pos Real.pi_pos))
      (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) xiStar_pos))
      dpConfig.hC_d_pos
  set c_γ_kap : ℝ := (9 / 10 : ℝ) * dpConfig.c_γ * kappaV
  set C_win_tot : ℝ := 12 * C_pref * Real.pi / Real.sqrt c_γ_kap * b_hi ^ (5 / 2 : ℝ)
  set C_tail_tot : ℝ := (W.C_D + 12 * C_pref * max W.C_S4 W.C_S2) * tail_Z * b_hi ^ 3
  obtain ⟨c_Z, hc_Z_eq⟩ : ∃ x : ℝ, x = max (max W.c_D (max W.c_S4 W.c_S2))
      (max W.c_V (max 10000 (max (48 / dpConfig.c_Γ) ((9 / b_lo ^ 2) ^ (3 / 2 : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨C_B, hC_B_eq⟩ : ∃ x : ℝ, x = max 1 (C_win_tot + C_tail_tot) := ⟨_, rfl⟩
  refine ⟨c_Z, C_B, ?_, hC_B_eq ▸ le_max_left _ _, ?_⟩
  · rw [hc_Z_eq]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  intro c' R Λ hc' hΛ hR_lo hR_hi g hg hM_pos hsec u hu_im hu_lo hu_hi hsin_hyp
  have hc'_D : W.c_D ≤ c' := (hc_Z_eq ▸ (le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc'_S4 : W.c_S4 ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc'
  have hc'_S2 : W.c_S2 ≤ c' :=
    (hc_Z_eq ▸ (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc'
  have hc'_V : W.c_V ≤ c' := (hc_Z_eq ▸ (le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_10000 : 10000 ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_48 : 48 / dpConfig.c_Γ ≤ c' :=
    (hc_Z_eq ▸ (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
  have hc'_R9 : (9 / b_lo ^ 2) ^ (3 / 2 : ℝ) ≤ c' :=
    (hc_Z_eq ▸ (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
  have hc'_24 : 24 ≤ c' := by linarith only [hc'_10000]
  have hlog_pos : 0 < Real.log c' := Real.log_pos (by linarith only [hc'_10000])
  have hR_ge9 : 9 ≤ R := by
    have h1 : 9 / b_lo ^ 2 ≤ c' ^ (2 / 3 : ℝ) := by
      calc 9 / b_lo ^ 2 = ((9 / b_lo ^ 2) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hc'_R9 (by norm_num)
    exact ((div_le_iff₀' (sq_pos_of_pos hb_lo)).mp h1).trans hR_lo
  have hR_pos : 0 < R := by linarith only [hR_ge9]
  have hu_ge8 : 8 ≤ ‖u‖ := by linarith only [hR_ge9, hu_lo]
  have hu_pos : 0 < ‖u‖ := by linarith only [hu_ge8]
  have hu_ne : u ≠ 0 := norm_pos_iff.mp hu_pos
  have hu_bhi : ‖u‖ ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) := hu_hi.trans hR_hi
  have hu_Z : ‖u‖ ≤ W.c₀_Z * c' ^ (2 / 3 : ℝ) :=
    hu_bhi.trans (mul_le_mul_of_nonneg_right hb_cap' (Real.rpow_nonneg hc'_pos.le _))
  have hu_cb_D : u ∈ closedBall (0 : ℂ) (W.c₀_D * c' ^ (2 / 3 : ℝ)) :=
    mem_closedBall_zero_iff.mpr
      (hu_Z.trans (mul_le_mul_of_nonneg_right W.hc₀_Z_le_D (Real.rpow_nonneg hc'_pos.le _)))
  have hu_cb_in : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    have hin_pos := innerChartRadius_pos
    have hle_in : W.c₀_D ≤ innerChartRadius := W.hc₀_D_le4.trans (by linarith only [hin_pos])
    exact closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right hle_in (Real.rpow_nonneg hc'_pos.le _)) hu_cb_D
  have hsqrt_u_lo : (4 / 5 : ℝ) * Real.sqrt R ≤ Real.sqrt ‖u‖ := by
    have h89 : (8 / 9 : ℝ) * R ≤ ‖u‖ := by linarith only [hR_ge9, hu_lo]
    have hsq : ((4 / 5 : ℝ) * Real.sqrt R) ^ 2 ≤ ‖u‖ := by
      rw [mul_pow, Real.sq_sqrt hR_pos.le]; linarith only [h89, hR_pos]
    exact Real.le_sqrt_of_sq_le hsq
  have hsqrt_u_hi : Real.sqrt ‖u‖ ≤ (6 / 5 : ℝ) * Real.sqrt R := by
    have h109 : ‖u‖ ≤ (10 / 9 : ℝ) * R := by linarith only [hR_ge9, hu_hi]
    have hsq : ‖u‖ ≤ ((6 / 5 : ℝ) * Real.sqrt R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR_pos.le]; linarith only [h109, hR_pos]
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))
  set a' : ℝ := Real.sqrt ‖u‖
  have ha'_pos : 0 < a' := Real.sqrt_pos.mpr hu_pos
  have ha'_sq : a' ^ 2 = ‖u‖ := Real.sq_sqrt hu_pos.le
  set φ : ℝ := (Real.pi - u.arg) / 2
  have hu_re_eq : (u ^ (1 / 2 : ℂ)).re = a' * Real.sin φ := cpow_half_re_eq_sqrt_mul_sin' hu_ne
  have hsin_lb : pass2AngleC2 * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c') ≤ Real.sin φ := by
    have h1 : a' * (pass2AngleC2 * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c')) ≤ a' * Real.sin φ := by
      linarith only [hsin_hyp, hu_re_eq]
    exact le_of_mul_le_mul_left h1 ha'_pos
  have hsin_pos : 0 < Real.sin φ := by
    have := pass2AngleC2_pos
    exact lt_of_lt_of_le (by positivity) hsin_lb
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by rw [hu_re_eq]; exact mul_pos ha'_pos hsin_pos
  have hsin_le1 : Real.sin φ ≤ 1 := Real.sin_le_one φ
  have hu_arg_nn : 0 ≤ u.arg := Complex.arg_nonneg_iff.mpr hu_im
  have hu_arg_lt : u.arg < Real.pi := by
    rcases lt_or_ge u.arg Real.pi with hlt | hge
    · exact hlt
    · exfalso
      have hpi : u.arg = Real.pi := le_antisymm (Complex.arg_le_pi u) hge
      have hφ0 : φ = 0 := by dsimp [φ]; rw [hpi, sub_self, zero_div]
      rw [hφ0, Real.sin_zero] at hsin_pos
      exact lt_irrefl 0 hsin_pos
  have hu_cut : ¬ (u.im = 0 ∧ u.re ≤ 0) := by
    rintro ⟨him0, hre_np⟩
    rcases eq_or_lt_of_le hre_np with hre0 | hre_neg
    · exact hu_ne (Complex.ext hre0 him0)
    · exact hu_arg_lt.ne (Complex.arg_eq_pi_iff.mpr ⟨hre_neg, him0⟩)
  have hφ_pos : 0 < φ := by dsimp [φ]; linarith only [hu_arg_lt]
  have hφ_le : φ ≤ Real.pi / 2 := by dsimp [φ]; linarith only [hu_arg_nn]
  have hu_polar : u = ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * φ : ℝ) : ℂ)) := by
    have hp := (Complex.norm_mul_exp_arg_mul_I u).symm
    rw [← ha'_sq] at hp
    conv_lhs => rw [hp]
    congr 1; congr 1; dsimp [φ]; push_cast; ring
  have ha'_Z : a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ W.c₀_Z := by
    rw [ha'_sq]
    calc ‖u‖ * c' ^ (-(2 / 3 : ℝ))
        ≤ (W.c₀_Z * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by gcongr
      _ = W.c₀_Z := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  have hsad := W.h_saddle hc'_pos ha'_pos.le hφ_pos.le hφ_le ha'_Z
  dsimp only at hsad
  rw [← hu_polar] at hsad
  set z_u : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
  set s : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * W.q_V z_u
  set ρ : ℝ := ‖s‖
  obtain ⟨hb_eq_chartB, _hs_re_nn, hs_im_nn, hρ_ρ₀, hρ_rφ, _, hρ_lo, hρ_hi, hs_re_lb⟩ := hsad
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (by have := kappaV_pos; positivity) hρ_lo
  have hs_re_pos : 0 < s.re := by
    have h1 : 0 < (5 / 6 : ℝ) * (ρ * Real.sin φ) := by positivity
    linarith only [h1, hs_re_lb]
  set ρ_R : ℝ := kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R
  have hρ_lo_R : (18 / 25 : ℝ) * ρ_R ≤ ρ := by
    have h1 : (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((4 / 5 : ℝ) * Real.sqrt R)) ≤
        (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') := by gcongr; have := kappaV_pos; positivity
    calc (18 / 25 : ℝ) * ρ_R
        = (9 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((4 / 5 : ℝ) * Real.sqrt R)) := by
          dsimp [ρ_R]; ring
      _ ≤ ρ := h1.trans hρ_lo
  have hρ_hi_R : ρ ≤ (33 / 25 : ℝ) * ρ_R := by
    have h1 : (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ≤
        (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((6 / 5 : ℝ) * Real.sqrt R)) := by
      gcongr; have := kappaV_pos; positivity
    calc ρ ≤ (11 / 10 : ℝ) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * ((6 / 5 : ℝ) * Real.sqrt R)) := hρ_hi.trans h1
      _ = (33 / 25 : ℝ) * ρ_R := by dsimp [ρ_R]; ring
  have hρ_ge_min : ρ_min_Z ≤ ρ := by
    have hsqrt_R_lb : b_lo * c' ^ (1 / 3 : ℝ) ≤ Real.sqrt R := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [mul_pow, ← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]
      calc b_lo ^ 2 * c' ^ ((1 / 3 : ℝ) * (2 : ℕ)) = b_lo ^ 2 * c' ^ (2 / 3 : ℝ) := by
            push_cast; rw [show (1 / 3 : ℝ) * 2 = (2 / 3 : ℝ) by norm_num]
        _ ≤ R := hR_lo
    have hρR_lb : kappaV * b_lo ≤ ρ_R := by
      dsimp [ρ_R]
      calc kappaV * b_lo
          = kappaV * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) * b_lo := by
            rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
        _ = kappaV * c' ^ (-(1 / 3 : ℝ)) * (b_lo * c' ^ (1 / 3 : ℝ)) := by ring
        _ ≤ kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R := by gcongr; have := kappaV_pos; positivity
    calc ρ_min_Z = (18 / 25 : ℝ) * (kappaV * b_lo) := by dsimp [ρ_min_Z]; ring
      _ ≤ (18 / 25 : ℝ) * ρ_R := by gcongr
      _ ≤ ρ := hρ_lo_R
  have hc_ρ_sre_sq : 2 * Real.log c' ≤ (dpConfig.c_γ / 16) * (c' * ρ * s.re ^ 2) := by
    have hsin_sq : pass2AngleC2 ^ 2 * R ^ (-(3 / 2 : ℝ)) * Real.log c' ≤ Real.sin φ ^ 2 := by
      have h1 : (pass2AngleC2 * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c')) ^ 2 ≤ Real.sin φ ^ 2 :=
        pow_le_pow_left₀ (by have := pass2AngleC2_pos; positivity) hsin_lb 2
      have hR32 : (R ^ (-(3 / 4 : ℝ))) ^ 2 = R ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR_pos.le]; norm_num
      have hsqeq : (pass2AngleC2 * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c')) ^ 2 =
          pass2AngleC2 ^ 2 * R ^ (-(3 / 2 : ℝ)) * Real.log c' := by
        rw [mul_pow, mul_pow, hR32, Real.sq_sqrt hlog_pos.le]
      rwa [hsqeq] at h1
    have hsre_sq : (25 / 36 : ℝ) * ρ ^ 2 * Real.sin φ ^ 2 ≤ s.re ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hs_re_lb 2
      linarith only [h1]
    have hρ3_lb : ((18 / 25 : ℝ) * kappaV) ^ 3 * c' ^ (-1 : ℝ) * R ^ (3 / 2 : ℝ) ≤ ρ ^ 3 := by
      have h1 : ((18 / 25 : ℝ) * ρ_R) ^ 3 ≤ ρ ^ 3 :=
        pow_le_pow_left₀ (by dsimp [ρ_R]; have := kappaV_pos; positivity) hρ_lo_R 3
      have hpow_c : (c' ^ (-(1 / 3 : ℝ))) ^ 3 = c' ^ (-1 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc'_pos.le]; norm_num
      have hpow_R : (Real.sqrt R) ^ 3 = R ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR_pos.le]; norm_num
      have heq : ((18 / 25 : ℝ) * ρ_R) ^ 3 =
          ((18 / 25 : ℝ) * kappaV) ^ 3 * c' ^ (-1 : ℝ) * R ^ (3 / 2 : ℝ) := by
        dsimp [ρ_R]; rw [mul_pow, mul_pow, mul_pow, hpow_c, hpow_R]; ring
      rwa [← heq]
    have hc_cancel : c' * c' ^ (-1 : ℝ) = 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne']
    have hR_cancel : R ^ (3 / 2 : ℝ) * R ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hR_pos, add_neg_cancel, Real.rpow_zero]
    have hprod : ((18 / 25 : ℝ) * kappaV) ^ 3 * (25 / 36 : ℝ) * pass2AngleC2 ^ 2 * Real.log c' ≤
        c' * ρ * s.re ^ 2 := by
      have hsin_nn : 0 ≤ pass2AngleC2 ^ 2 * R ^ (-(3 / 2 : ℝ)) * Real.log c' := by
        have := pass2AngleC2_pos; positivity
      have h25 : 0 ≤ (25 / 36 : ℝ) * ρ ^ 2 := by positivity
      calc ((18 / 25 : ℝ) * kappaV) ^ 3 * (25 / 36 : ℝ) * pass2AngleC2 ^ 2 * Real.log c'
          = (25 / 36 : ℝ) * (((18 / 25 : ℝ) * kappaV) ^ 3 * c' ^ (-1 : ℝ) * R ^ (3 / 2 : ℝ)) *
              c' * (pass2AngleC2 ^ 2 * R ^ (-(3 / 2 : ℝ)) * Real.log c') := by
            calc _ = (25 / 36 : ℝ) * ((18 / 25 : ℝ) * kappaV) ^ 3 * (c' * c' ^ (-1 : ℝ)) *
                    (R ^ (3 / 2 : ℝ) * R ^ (-(3 / 2 : ℝ))) * pass2AngleC2 ^ 2 * Real.log c' := by
                  rw [hc_cancel, hR_cancel]; ring
              _ = _ := by ring
        _ ≤ (25 / 36 : ℝ) * ρ ^ 3 * c' * Real.sin φ ^ 2 := by
            have hA : ((18 / 25 : ℝ) * kappaV) ^ 3 * c' ^ (-1 : ℝ) * R ^ (3 / 2 : ℝ) ≤ ρ ^ 3 := hρ3_lb
            have hB : pass2AngleC2 ^ 2 * R ^ (-(3 / 2 : ℝ)) * Real.log c' ≤ Real.sin φ ^ 2 := hsin_sq
            have hC1 : (25 / 36 : ℝ) * (((18 / 25 : ℝ) * kappaV) ^ 3 * c' ^ (-1 : ℝ) * R ^ (3 / 2 : ℝ)) * c' ≤
                (25 / 36 : ℝ) * ρ ^ 3 * c' := by gcongr
            exact mul_le_mul hC1 hB hsin_nn (by positivity)
        _ = c' * ρ * ((25 / 36 : ℝ) * ρ ^ 2 * Real.sin φ ^ 2) := by ring
        _ ≤ c' * ρ * s.re ^ 2 := by gcongr
    have hcγ_nn := (div_pos dpConfig.hc_γ_pos (by norm_num : (0 : ℝ) < 16)).le
    calc 2 * Real.log c'
        ≤ ((dpConfig.c_γ / 16) * (25 / 36 : ℝ) * ((18 / 25 : ℝ) * kappaV) ^ 3 * pass2AngleC2 ^ 2) *
            Real.log c' := mul_le_mul_of_nonneg_right pass2AngleC2_decay_ge_two hlog_pos.le
      _ = (dpConfig.c_γ / 16) * (((18 / 25 : ℝ) * kappaV) ^ 3 * (25 / 36 : ℝ) * pass2AngleC2 ^ 2 *
            Real.log c') := by ring
      _ ≤ (dpConfig.c_γ / 16) * (c' * ρ * s.re ^ 2) := mul_le_mul_of_nonneg_left hprod hcγ_nn
  set φ' : ℝ := Real.pi / 2 - s.arg
  have hs_arg_nn : 0 ≤ s.arg := Complex.arg_nonneg_iff.mpr hs_im_nn
  have hs_arg_le : s.arg ≤ Real.pi / 2 := by
    rcases eq_or_lt_of_le hs_im_nn with him0 | him_pos
    · rw [Complex.arg_eq_zero_iff.mpr ⟨hs_re_pos.le, him0.symm⟩]; positivity [Real.pi_pos]
    · exact (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hs_re_pos)).le
  have hφ'_nn : 0 ≤ φ' := by dsimp [φ']; linarith only [hs_arg_le]
  have hφ'_le : φ' ≤ Real.pi / 2 := by dsimp [φ']; linarith only [hs_arg_nn]
  have hs_polar : s = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)) := by
    have hp := (Complex.norm_mul_exp_arg_mul_I s).symm
    have harg_eq : Real.pi / 2 - φ' = s.arg := by dsimp [φ']; ring
    rw [harg_eq]
    simpa [ρ, mul_comm (s.arg : ℂ) Complex.I] using hp
  obtain ⟨_, _, _, segs, hchain, _, hω_bd, hstrip_gen, h_ur, h_lr, h_ar, h_fs, hnonstrip,
      hcnt_segs, hba_segs, h_no_crude⟩ := dpConfig_spec hρ_pos.le hρ_ρ₀ hφ'_nn hφ'_le
  rw [← hs_polar, hb_eq_chartB] at hstrip_gen h_ur h_lr h_ar h_fs hnonstrip
  have hP_deform := truncatedMellinP_eq_contourIntegral hc'_24 hg hu_cb_in hchain hω_bd
  set b : ℂ := virasoroBChart c' u
  set t : ℂ := virasoroDeltaChartC c' u
  have hair_eq : Real.exp (c' * (chartPhiV s b).re) = airyEnv u := by
    have hs_ball : s ∈ ball (0 : ℂ) W.r_φ := by rwa [mem_ball_zero_iff]
    have hpot1 := W.hφ_pot s hs_ball hs_re_pos
    rw [hb_eq_chartB] at hpot1
    have hpot2 := virasoro_inner_potential_eq hc'_pos hu_cb_in hu_cut
    have hc_phi : c' * (chartPhiV s b).re = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
      rw [hpot1]; simpa [add_comm] using hpot2
    rw [hc_phi]; rfl
  set M_g : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  have hbd_in := virasoroBChart_inner_bounds hc'_pos hu_cb_in
  have hb_re_pos : 0 < b.re := lt_of_lt_of_le (half_pos xiStar_pos) hbd_in.2.2.1
  have ht_eq : t = (c' : ℂ) * b ^ 2 / 3 := virasoroDeltaChartC_eq_bChart_sq u
  have ht_half_ub : ‖t ^ (-(1 / 2 : ℂ))‖ ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
    have ht_lb : c' * (xiStar / 2) ^ 2 / 3 ≤ ‖t‖ := by
      rw [ht_eq, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le,
        Complex.norm_ofNat]
      have h1 : xiStar / 2 ≤ ‖b‖ := hbd_in.2.2.1.trans (Complex.re_le_norm _)
      have h2 : (xiStar / 2) ^ 2 ≤ ‖b‖ ^ 2 :=
        pow_le_pow_left₀ (by have := xiStar_pos; positivity) h1 2
      gcongr
    have ht_pos : 0 < ‖t‖ := lt_of_lt_of_le (by have := xiStar_pos; positivity) ht_lb
    have ht_ne : t ≠ 0 := norm_pos_iff.mp ht_pos
    have hnorm_cp : ‖t ^ (-(1 / 2 : ℂ))‖ = ‖t‖ ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
      have hre : (Complex.log t * (-(1 / 2 : ℂ))).re = -(1 / 2 : ℝ) * Real.log ‖t‖ := by
        rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
          mul_comm, Complex.re_ofReal_mul, Complex.log_re]
      rw [hre, Real.rpow_def_of_pos ht_pos]; congr 1; ring
    rw [hnorm_cp]
    have hpow_le : ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by have := xiStar_pos; positivity) ht_lb (by norm_num)
    have hrhs_eq : (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) =
        (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
      have hxi := xiStar_pos
      have hsub : ((xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt 3 / xiStar := by
        rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
        field_simp [hxi.ne']
      rw [show c' * (xiStar / 2) ^ 2 / 3 = ((xiStar / 2) ^ 2 / 3) * c' by ring,
        Real.mul_rpow (by positivity) hc'_pos.le, hsub]
    exact hpow_le.trans_eq hrhs_eq
  have hwin_wv : ∀ ζ ∈ stripClosed, ‖ζ - s‖ ≤ s.re / 4 →
      ‖tildeWV c' g ζ‖ ≤ M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) := by
    intro ζ hζ_cl hdist
    have hdist_ρ : ‖ζ - s‖ ≤ ρ / 4 := by
      have hs_re_le : s.re ≤ ρ := Complex.re_le_norm s
      linarith only [hdist, hs_re_le]
    have hζ_lo : ρ_R / 3 ≤ ‖ζ‖ := by
      have htri := norm_sub_norm_le s (s - ζ)
      rw [sub_sub_cancel, norm_sub_rev] at htri
      have htri' : ρ - ‖ζ - s‖ ≤ ‖ζ‖ := htri
      have h34 : (3 / 4 : ℝ) * ρ ≤ ‖ζ‖ := by linarith only [htri', hdist_ρ]
      have hR_nn : 0 ≤ ρ_R := by dsimp [ρ_R]; have := kappaV_pos; positivity
      calc ρ_R / 3 ≤ (27 / 50 : ℝ) * ρ_R := by linarith only [hR_nn]
        _ = (3 / 4 : ℝ) * ((18 / 25 : ℝ) * ρ_R) := by ring
        _ ≤ (3 / 4 : ℝ) * ρ := by gcongr
        _ ≤ ‖ζ‖ := h34
    have hζ_hi : ‖ζ‖ ≤ 2 * ρ_R := by
      have htri : ‖ζ‖ ≤ ρ + ‖ζ - s‖ := by
        calc ‖ζ‖ = ‖s + (ζ - s)‖ := by ring_nf
          _ ≤ ‖s‖ + ‖ζ - s‖ := norm_add_le _ _
      have h54 : ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := by linarith only [htri, hdist_ρ]
      have hR_nn : 0 ≤ ρ_R := by dsimp [ρ_R]; have := kappaV_pos; positivity
      calc ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := h54
        _ ≤ (5 / 4 : ℝ) * ((33 / 25 : ℝ) * ρ_R) := by gcongr
        _ = (33 / 20 : ℝ) * ρ_R := by ring
        _ ≤ 2 * ρ_R := by linarith only [hR_nn]
    have hζ_re_lb : (3 / 4 : ℝ) * s.re ≤ ζ.re := by
      have hre_sub := (abs_le.mp ((Complex.abs_re_le_norm (ζ - s)).trans hdist)).1
      rw [Complex.sub_re] at hre_sub
      linarith only [hre_sub]
    have hζ_re_pos : 0 < ζ.re := lt_of_lt_of_le (by positivity) hζ_re_lb
    have hζ_ang : (1 / 2 : ℝ) * Real.sin φ * ‖ζ‖ ≤ ζ.re := by
      have h54 : ‖ζ‖ ≤ (5 / 4 : ℝ) * ρ := by
        have htri : ‖ζ‖ ≤ ρ + ‖ζ - s‖ := by
          calc ‖ζ‖ = ‖s + (ζ - s)‖ := by ring_nf
            _ ≤ ‖s‖ + ‖ζ - s‖ := norm_add_le _ _
        linarith only [htri, hdist_ρ]
      calc (1 / 2 : ℝ) * Real.sin φ * ‖ζ‖
          ≤ (1 / 2 : ℝ) * Real.sin φ * ((5 / 4 : ℝ) * ρ) := by gcongr
        _ = (3 / 4 : ℝ) * ((5 / 6 : ℝ) * (ρ * Real.sin φ)) := by ring
        _ ≤ (3 / 4 : ℝ) * s.re := by gcongr
        _ ≤ ζ.re := hζ_re_lb
    have h_wv := hsec ζ hζ_cl hζ_lo hζ_hi hζ_re_pos
    have h_rat : ‖ζ‖ / ζ.re ≤ 2 / Real.sin φ := by
      rw [div_le_div_iff₀ hζ_re_pos hsin_pos]
      linarith only [hζ_ang]
    calc ‖tildeWV c' g ζ‖
        ≤ M_g * (Λ * c' ^ (-(5 / 6 : ℝ)) * (‖ζ‖ / ζ.re)) := by
          simpa only [mul_div_assoc] using h_wv
      _ ≤ M_g * (Λ * c' ^ (-(5 / 6 : ℝ)) * (2 / Real.sin φ)) := by gcongr
      _ = M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) := by ring
  set K_seg : ℝ := (4 * Real.sqrt 3 / xiStar) * dpConfig.C_d * M_g *
    c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv u
  have hK_seg_pos : 0 < K_seg :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
      (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) xiStar_pos)
      dpConfig.hC_d_pos) hM_pos) (Real.rpow_pos_of_pos hc'_pos _)) (Real.exp_pos _))
      (airyEnv_pos u)
  set B_seg_unit : ℝ :=
    (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
      ((Real.pi / 2) / Real.sqrt (c' * dpConfig.c_γ * ρ)) +
    max W.C_S4 W.C_S2 * (tail_Z * c' ^ (-2 : ℝ))
  have hB_seg_nn : 0 ≤ K_seg * B_seg_unit := by
    refine mul_nonneg hK_seg_pos.le (add_nonneg ?_ ?_)
    · exact mul_nonneg (div_nonneg (by positivity) hsin_pos.le)
        (div_nonneg (by positivity) (Real.sqrt_nonneg _))
    · have := W.hCS4; positivity
  have hseg_bound : ∀ S ∈ segs,
      ‖∫ τ in S.a..S.b, mellinDensityIntegrand c' g t (S.ω τ) * S.ω' τ‖ ≤ K_seg * B_seg_unit :=
    fun S hS =>
    lemma_Z_log_seg_bound W dpConfig S hc'_pos hc'_24 hc'_48 hc'_S4
      (by linarith only [hΛ]) hsin_pos hρ_pos hs_re_pos hρ_min_pos hρ_ge_min hc_ρ_sre_sq
      hlog_pos.le hκ_exp_pos ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _))
      (le_max_left _ _) (le_max_right _ _)
      hg hM_pos rfl hb_re_pos hbd_in.2.2.2.2.2 ht_eq ht_half_ub hair_eq rfl rfl
      hwin_wv (fun hμ => W.hS2 hc'_S2 hμ hg)
      (hba_segs S hS) (hω_bd S hS) (h_ur S hS) (h_lr S hS) (h_ar S hS) (h_fs S hS)
      (hnonstrip S hS) (h_no_crude S hS)
  have hcont_tot : ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖ ≤
      12 * (K_seg * B_seg_unit) :=
    (norm_contourIntegral_le_of_seg_bound' _ segs hB_seg_nn hseg_bound).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt_segs) hB_seg_nn)
  have hP_norm : ‖truncatedMellinP c' dpT0 g u‖ ≤
      12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u := by
    have hV_u := W.hV_bd hc'_V hu_cb_in
    have hd_u := virasoroDeltaChartC_inner_deriv_bound hc'_pos hu_cb_in
    rw [hP_deform, norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_div]
    have hM_norm : ‖(M_g : ℂ)‖ = M_g := by
      rw [Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
    have hc_2pi : ‖(c' : ℂ)‖ / ‖2 * (Real.pi : ℂ) * Complex.I‖ = c' / (2 * Real.pi) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hc'_pos.le, norm_mul, norm_mul,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_I, mul_one]
    change (‖deriv (virasoroDeltaChartC c') u‖ / ‖(M_g : ℂ)‖) *
        ‖V_C (c' : ℂ) t‖ * (‖(c' : ℂ)‖ / ‖2 * (Real.pi : ℂ) * Complex.I‖) *
        ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖ ≤ _
    rw [hM_norm, hc_2pi]
    have hexp_cancel : Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hc_pow_eq : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ)) =
        c' ^ (1 / 3 : ℝ) := by
      calc c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))
          = c' ^ (1 / 3 : ℝ) * (c' * (c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)))) := by ring
        _ = c' ^ (1 / 3 : ℝ) * (c' * c' ^ (-1 : ℝ)) := by rw [← Real.rpow_add hc'_pos]; norm_num
        _ = c' ^ (1 / 3 : ℝ) * 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne']
        _ = c' ^ (1 / 3 : ℝ) := mul_one _
    calc (‖deriv (virasoroDeltaChartC c') u‖ / M_g) * ‖V_C (c' : ℂ) t‖ *
            (c' / (2 * Real.pi)) * ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖
        ≤ ((innerCDxi * c' ^ (1 / 3 : ℝ)) / M_g) *
            (W.C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL b).re)) *
            (c' / (2 * Real.pi)) * (12 * (K_seg * B_seg_unit)) := by
          have := innerCDxi_pos; have := W.hC_V; gcongr
      _ = 12 * C_pref * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))) *
            (Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re))) *
            B_seg_unit * airyEnv u := by
          dsimp [C_pref, K_seg]; field_simp [hM_pos.ne', Real.pi_pos.ne']
      _ = 12 * C_pref * c' ^ (1 / 3 : ℝ) * B_seg_unit * airyEnv u := by
          rw [hc_pow_eq, hexp_cancel, mul_one]
  exact lemma_Z_log_combine_envelope W dpConfig hb_hi_pos hc'_pos hc'_ge1 hΛ
    hκ_exp_pos (min_le_right _ _) (le_max_right _ _) hC_pref_pos
    hu_pos hu_bhi hu_re_pos hu_re_eq hsin_pos hsin_le1 hρ_pos hρ_lo rfl
    (hC_B_eq ▸ le_max_right _ _) hP_norm (W.hDp hc'_D hg hM_pos hu_cb_D)

/-! ### 3. Combined covered-arc Virasoro window (`virasoro_cov_window_log`) -/

/-- **Combined covered-arc Virasoro window bound (`ctl:pass2`)**:
for any compact scale band `0 < b_lo ≤ b_hi` inside `√2 * virasoroBVChoice`, there exist
`c₀ ≥ virasoroCQEnv` and `C_cov ≥ 1` such that for all `c' ≥ c₀`, `b_lo^2 c'^{2/3} ≤ R`,
`R + 1 ≤ b_hi^2 c'^{2/3}`, `virasoroAThr ≤ R`, weakly feasible `g` with `Δ(0) ≤ T ≤ Δ(-A_thr)`, and
`u` with `0 ≤ u.im`, `‖u‖ = R`, `pass2AngleC2 * R^{-3/4} * √(log c') * √‖u‖ ≤ (u^{1/2}).re`:
`‖virasoroPsiTilde c' g u‖ ≤ C_cov * (c'^{1/3} * (B₁ + B₂) + 1) * airyEnv u * (Re u^{1/2})^{-3/2} * ‖u‖^{-3/4}`. -/
theorem virasoro_cov_window_log {b_lo b_hi : ℝ} (hb_lo : 0 < b_lo) (hb_le : b_lo ≤ b_hi)
    (hb_hi_choice : b_hi ≤ Real.sqrt 2 * virasoroBVChoice) :
    ∃ c₀ C_cov : ℝ, virasoroCQEnv ≤ c₀ ∧ 1 ≤ C_cov ∧
      ∀ {c' R T : ℝ}, c₀ ≤ c' →
        b_lo ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
        R + 1 ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) →
        virasoroAThr ≤ R →
        ∀ {g : ℝ → ℝ}, virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
          virasoroDeltaChart c' 0 ≤ T →
          T ≤ virasoroDeltaChart c' (-virasoroAThr) →
          ∀ {u : ℂ}, 0 ≤ u.im → ‖u‖ = R →
            pass2AngleC2 * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c') * Real.sqrt ‖u‖ ≤
              (u ^ (1 / 2 : ℂ)).re →
            ‖virasoroPsiTilde c' g u‖ ≤
              C_cov * (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) *
                airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
  have hb_hi_pos : 0 < b_hi := lt_of_lt_of_le hb_lo hb_le
  have hb_scale : b_hi ^ 2 ≤ virasoroScaleThresh := by
    have h1 := pow_le_pow_left₀ hb_hi_pos.le hb_hi_choice 2
    rw [mul_pow, Real.sq_sqrt zero_le_two] at h1
    exact h1.trans virasoroBVChoice_scaleCompat
  have hb_cap : b_hi ^ 2 ≤ zScaleCap := hb_scale.trans (min_le_right _ _)
  have hb_bv : b_hi ≤ Real.sqrt 2 * virasoroBV :=
    hb_hi_choice.trans (mul_le_mul_of_nonneg_left virasoroBVChoice_le (Real.sqrt_nonneg _))
  obtain ⟨c_Z, C_B, hc_Z_ge, hC_B_ge1, hZ⟩ := lemma_Z_log hb_lo hb_le hb_cap
  set C_Y1 : ℝ := max (pass2UniformBandConst b_lo b_hi) 1
  have hCY1_ge1 : 1 ≤ C_Y1 := le_max_right _ _
  refine ⟨max virasoroCQEnv (max (yvThresh langerChartSpec_virasoro virasoroAThr) c_Z),
    C_B * C_Y1, le_max_left _ _, by nlinarith only [hC_B_ge1, hCY1_ge1], ?_⟩
  intro c' R T hc' hR_lo hR_hi hR_thr g hg_wf hT_lo hT_hi u hu_im hu_norm hu_ang
  have hc'_cq : virasoroCQEnv ≤ c' := (le_max_left _ _).trans hc'
  have hc'_yv : yvThresh langerChartSpec_virasoro virasoroAThr ≤ c' :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_Z : c_Z ≤ c' := ((le_max_right _ _).trans (le_max_right _ _)).trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith only [this]) hc'_cq
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]
    have := virasoroCQEnv_ge; linarith only [this, hc'_cq]
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero hshift hg_wf.1 hg_wf.2.1
  have hb_hi_bv2 : b_hi ^ 2 ≤ 2 * virasoroBV ^ 2 := by
    have h1 := pow_le_pow_left₀ hb_hi_pos.le hb_bv 2
    rwa [mul_pow, Real.sq_sqrt zero_le_two] at h1
  have hR_le_AC : R ≤ virasoroAC c' ^ 2 := by
    rw [virasoroAC_sq c' hc'_pos.le]
    have h1 : R ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) := by linarith only [hR_hi]
    exact h1.trans (mul_le_mul_of_nonneg_right hb_hi_bv2 (Real.rpow_nonneg hc'_pos.le _))
  have hB1_nn := virasoroBandB1_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_lo hT_hi
  have hB2_nn := virasoroBandB2_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_hi
  set Λ : ℝ := C_Y1 * (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1)
  have hΛ_ge1 : 1 ≤ Λ := by
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1 := by
      have hnn : 0 ≤ c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) := by
        positivity
      linarith only [hnn]
    dsimp [Λ]; nlinarith only [hCY1_ge1, h1]
  have hband := virasoro_uniform_band_boundFor_pos hb_lo hb_le hb_scale hb_bv hc'_yv hc'_cq
    hR_thr hR_lo hR_hi hg_wf hT_lo hT_hi
  have henv := hZ hc'_Z hΛ_ge1 hR_lo hR_hi hg_wf.1 hM_pos hband hu_im
    (by linarith only [hu_norm]) (by linarith only [hu_norm]) hu_ang
  have hL_eq : C_B * Λ =
      C_B * C_Y1 * (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) := by
    dsimp [Λ]; ring
  rwa [← hL_eq]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_uniform_band_boundFor_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_uniform_band_boundFor_pos

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lemma_Z_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lemma_Z_log

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_cov_window_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_cov_window_log

end FormalResearch.ModularBootstrap.FiveTerm
