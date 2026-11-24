module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWMain
public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWBridge
public import FormalResearch.ModularBootstrap.FixedWeightBand.BandBoundWBridge

/-!
# Uniform Band Bound across the Bootstrap Annulus at Weight `w` (Proposition `Y_V`, `vlo:YV`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4 and §J8 (Proposition `Y_V` `vlo:YV`).

The `BandReductionInstance` of `ywBandInstance` lives on the thin annulus
`R ∈ [b₀² c'^{2/3}, b₀² c'^{2/3} + 1]`.  For a scale `0 < b ≤ b_V` with `2 b² ≤ b₀²`
(`b₀² = c₀/2`, `c₀` the weight-free Langer cap) it is rescaled across `R ∈ [b² c'^{2/3}, A_{c'}(b)² - 1]`
(`b_R = √(R c'^{-2/3}) ∈ [b, √2 b]`, same data, parameters `yvBandParamsAt b_R`) and the band bound reads
`‖W̃_V(ζ)‖ ≤ M C_Y c'^{-5/6}(c'^{1/3}(B₁+B₂)+1) ‖ζ‖/Re ζ` with `C_Y` depending on `b` only.

* `uniformBandConstWThr prob A_thr b` (`uniformBandConstW prob b` at `A_thr = virasoroAThr`), `bandParamsAtWThr`,
  `ywP0Thr`;
* `uniform_band_boundForW_thr`: the uniform band bound at every cutoff radius `A_thr > 0`, with the constant
  `uniformBandConstWThr prob A_thr b`; `uniform_band_boundForW` is the case `A_thr = virasoroAThr` (the Virasoro
  `virasoro_uniform_band_boundFor`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip
open FormalResearch.ModularBootstrap.Chart FormalResearch.ModularBootstrap.StripBand
open FormalResearch.ModularBootstrap.StripMultiplier

variable {prob : FixedWeightProblem}

namespace LemmaQData

variable (Q : LemmaQData prob)

/-- Combined inner-chart scale cap `min (c₀ / 2) (zScaleCapW D)` within which Proposition `Y_V` and Lemma `Z`
apply across the bootstrap annulus (the Virasoro `virasoroScaleThresh`). -/
noncomputable abbrev scaleThresh : ℝ :=
  min ((yvWitness langerChartSpec_virasoro).c₀ / 2) (zScaleCapW Q.D)

lemma scaleThresh_pos : 0 < Q.scaleThresh :=
  lt_min (half_pos (yvWitness langerChartSpec_virasoro).hc₀_pos) (zScaleCapW_pos Q.D)

lemma langerDelta_eq {c' u : ℝ} (hc' : 0 < c') (hu : |u| ≤ Q.AC c' ^ 2) :
    langerDelta langerChartSpec_virasoro c' u = virasoroDeltaChart c' u :=
  langerDelta_virasoro_eq hc' (Q.abs_le_virasoro hc'.le hu)

end LemmaQData

/-- The reference band-reduction parameters of Proposition `Y_V` at cutoff radius `A_thr`. -/
noncomputable def ywP0Thr (prob : FixedWeightProblem) (A_thr : ℝ) : BandReductionParams :=
  ywBandParams prob langerChartSpec_virasoro A_thr

/-- The level-one reference parameters (`A_thr = virasoroAThr`). -/
noncomputable def ywP0 (prob : FixedWeightProblem) : BandReductionParams :=
  ywP0Thr prob virasoroAThr

/-- The rescaled band-reduction parameters at cutoff radius `A_thr` and scale `b_R`. -/
noncomputable def bandParamsAtWThr (prob : FixedWeightProblem) (A_thr : ℝ) (b_R : ℝ)
    (hb_R : 0 < b_R) : BandReductionParams :=
  { ywP0Thr prob A_thr with
    b := b_R
    hb := hb_R }

noncomputable def bandParamsAtW (prob : FixedWeightProblem) (b_R : ℝ) (hb_R : 0 < b_R) :
    BandReductionParams :=
  bandParamsAtWThr prob virasoroAThr b_R hb_R

/-- The uniform band constant `C_Y(b)` of Proposition `Y_V` at cutoff radius `A_thr`. -/
noncomputable def uniformBandConstWThr (prob : FixedWeightProblem) (A_thr : ℝ) (b : ℝ) : ℝ :=
  let P := (ywP0Thr prob A_thr)
  let ρ_min_lo := kappaV * b / 3
  let C_pf_lo := ρ_min_lo ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  let C_gauss5 := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
  let C_core := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  let C_sub := P.C_a * C_gauss5 / P.κ_sub
  let C_tail := C_core + C_sub + 2 * tebBandOscConst P
  let C_band_hi := tebBandOscConst P * max (P.C_τ * (2 * b ^ 2 + 1)) 1
  max C_tail C_band_hi / (C_pf_lo * ρ_min_lo)

noncomputable def uniformBandConstW (prob : FixedWeightProblem) (b : ℝ) : ℝ :=
  uniformBandConstWThr prob virasoroAThr b

private lemma tebBandConst_yvBandParamsAt_leFor_thr {A_thr b b_R : ℝ} (hb_pos : 0 < b)
    (hb_R : 0 < b_R)
    (hb_lo : b ≤ b_R) (hb_sq_hi : b_R ^ 2 ≤ 2 * b ^ 2) :
    tebBandConst (bandParamsAtWThr prob A_thr b_R hb_R) ≤ uniformBandConstWThr prob A_thr b := by
  let P := (ywP0Thr prob A_thr)
  have hosc_pos : 0 < tebBandOscConst P := by
    unfold tebBandOscConst
    have hb₀ : 0 < min P.c_1 (P.c_2 / 16) := lt_min P.hc_1 (div_pos P.hc_2 (by norm_num))
    have := tebOscConst_pos hb₀ (P.M + 11 / 2)
    have := P.hC_a; have := P.hC_ν
    positivity
  set ρ_min_lo : ℝ := kappaV * b / 3
  set ρ_min_R : ℝ := kappaV * b_R / 3
  have hρ_lo_pos : 0 < ρ_min_lo := by
    dsimp [ρ_min_lo]; have := kappaV_pos; positivity
  have hρ_le : ρ_min_lo ≤ ρ_min_R := by
    dsimp [ρ_min_lo, ρ_min_R]; have := kappaV_pos; gcongr
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
  set C_band_hi : ℝ := tebBandOscConst P * max (P.C_τ * (2 * b ^ 2 + 1)) 1
  have hband_hi_pos : 0 < C_band_hi := by
    dsimp [C_band_hi]
    exact mul_pos hosc_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hnum_hi_pos : 0 < max C_tail C_band_hi :=
    lt_of_lt_of_le hband_hi_pos (le_max_right _ _)
  have hband_le : C_band_R ≤ C_band_hi := by
    dsimp [C_band_R, C_band_hi]
    refine mul_le_mul_of_nonneg_left (max_le_max_right 1 ?_) hosc_pos.le
    exact mul_le_mul_of_nonneg_left (by linarith only [hb_sq_hi]) P.hC_τ.le
  have hnum_le : max C_tail C_band_R ≤ max C_tail C_band_hi :=
    max_le_max_left C_tail hband_le
  have hlhs_eq : tebBandConst (bandParamsAtWThr prob A_thr b_R hb_R) =
      max C_tail C_band_R / (C_pf_R * ρ_min_R) := rfl
  have hrhs_eq : uniformBandConstWThr prob A_thr b =
      max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) := rfl
  rw [hlhs_eq, hrhs_eq]
  calc max C_tail C_band_R / (C_pf_R * ρ_min_R)
      ≤ max C_tail C_band_hi / (C_pf_R * ρ_min_R) :=
        div_le_div_of_nonneg_right hnum_le hden_R_pos.le
    _ ≤ max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) :=
        div_le_div_of_nonneg_left hnum_hi_pos.le hden_lo_pos hden_le

/-! ### 3. Rescaled `BandReductionInstance` and moment bridge across `[b^2 c'^{2/3}, A_{c'}(b)^2 - 1]` -/

variable [Q : LemmaQData prob]


lemma uniform_band_boundForW_thr {A_thr b : ℝ} (hA_pos : 0 < A_thr) (hb_pos : 0 < b) (hb_le : b ≤ Q.bV)
    (hScale : 2 * b ^ 2 ≤ Q.scaleThresh)
    {c' R T : ℝ}
    (hc'_yv : ywThresh prob langerChartSpec_virasoro A_thr ≤ c')
    (hc'_cq : Q.cQ ≤ c')
    (hR_thr : A_thr ≤ R)
    (hR_lo : b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_hi : R + 1 ≤ chartACAt b c' ^ 2)
    {g : ℝ → ℝ} (hg_wf : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-A_thr)) :
    let M := prob.cardyNorm (c' / 12) g
    let B₁ := bandB1W prob c' R T g
    let B₂ := bandB2W prob c' R g
    ∀ ζ ∈ stripClosed,
      kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
      ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
      c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
      ‖tildeWW prob.w c' g ζ‖ ≤ M *
        (max (uniformBandConstWThr prob A_thr b) 1 * (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
  dsimp only
  let pg := langerChartSpec_virasoro
  let w := yvWitness pg
  have hc'_10000 : 10000 ≤ c' := (ywThresh_ge prob pg A_thr).trans hc'_yv
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith only [hc'_10000]
  have hshift : prob.totalShift ≤ c' / 12 := Q.totalShift_le hc'_cq
  have hg : TestClass prob (c' / 12) g := hg_wf.1
  have hM_pos : 0 < prob.cardyNorm (c' / 12) g :=
    Q.cardyNorm_pos hc'_cq hg_wf
  have hg_nn : ∀ t ∈ Ici T, 0 ≤ g t := hg_wf.2.2.2
  have h2bV_c0 : 2 * b ^ 2 ≤ w.c₀ / 2 :=
    hScale.trans (min_le_left _ _)
  have hACb_sq : chartACAt b c' ^ 2 = 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) :=
    chartACAt_sq b c' hc'_pos.le
  have hACb_le_AC : chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 :=
    Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hR_le_ACb : R ≤ chartACAt b c' ^ 2 := by linarith only [hR_hi]
  have hR_le_AC : R ≤ Q.AC c' ^ 2 := hR_le_ACb.trans hACb_le_AC
  have hR_pos : 0 < R := lt_of_lt_of_le hA_pos hR_thr
  -- Compatibility of `langerDelta pg c'` with `virasoroDeltaChart c'` at `0`, `-A_thr`, `-R`
  have hΔ0_eq : langerDelta pg c' 0 = virasoroDeltaChart c' 0 :=
    Q.langerDelta_eq hc'_pos (by rw [abs_zero]; exact sq_nonneg _)
  have hΔA_eq : langerDelta pg c' (-A_thr) = virasoroDeltaChart c' (-A_thr) :=
    Q.langerDelta_eq hc'_pos (by rw [abs_neg, abs_of_pos hA_pos]; exact hR_thr.trans hR_le_AC)
  have hΔR_eq : langerDelta pg c' (-R) = virasoroDeltaChart c' (-R) :=
    Q.langerDelta_eq hc'_pos (by rw [abs_neg, abs_of_pos hR_pos]; exact hR_le_AC)
  have hT_lo' : langerDelta pg c' 0 ≤ T := by rw [hΔ0_eq]; exact hT_lo
  have hT_hi' : T ≤ langerDelta pg c' (-A_thr) := by rw [hΔA_eq]; exact hT_hi
  -- Reference `BandReductionInstance` at `R_star := (ywP0Thr prob A_thr).b^2 * c'^(2/3) = (w.c₀ / 2) * c'^(2/3)`
  let R_star : ℝ := (ywP0Thr prob A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ)
  have hP0_b_sq : (ywP0Thr prob A_thr).b ^ 2 = w.c₀ / 2 := by
    dsimp [ywP0Thr, ywBandParams, yvBandParams]
    exact Real.sq_sqrt (div_nonneg w.hc₀_pos.le zero_lt_two.le)
  have hR_le_Rstar : R ≤ R_star := by
    dsimp [R_star]
    rw [hP0_b_sq]
    calc R ≤ chartACAt b c' ^ 2 := hR_le_ACb
      _ = 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := hACb_sq
      _ ≤ (w.c₀ / 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right h2bV_c0 (Real.rpow_nonneg hc'_pos.le _)
  have hRstar_ub : R_star ≤ (ywP0Thr prob A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := by
    dsimp [R_star]; linarith only []
  let I₀ := ywBandInstance prob pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hmom₀ := ywBandInstance_moments prob pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hProps₀ := langerDelta_props (ywThresh_ge_yv hc'_yv) (R := R_star) le_rfl hRstar_ub
  have hDelta_le : langerDelta pg c' (-R) ≤ langerDelta pg c' (-R_star) :=
    hProps₀.2.2.2.2.1.monotoneOn ⟨hR_pos.le, hR_le_Rstar⟩ ⟨hProps₀.1.le, le_rfl⟩ hR_le_Rstar
  -- Rescaled `b_R := √(R * c'^(-2/3))` in `[b, √2 * b]`
  set b_R : ℝ := Real.sqrt (R * c' ^ (-(2 / 3 : ℝ)))
  have hb_R_sq : b_R ^ 2 = R * c' ^ (-(2 / 3 : ℝ)) :=
    Real.sq_sqrt (mul_nonneg hR_pos.le (Real.rpow_nonneg hc'_pos.le _))
  have hb_R_lo : b ≤ b_R := by
    refine Real.le_sqrt_of_sq_le ?_
    calc b ^ 2
        = (b ^ 2 * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ R * c' ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hR_lo (Real.rpow_nonneg hc'_pos.le _)
  have hb_R_pos : 0 < b_R := lt_of_lt_of_le hb_pos hb_R_lo
  have hb_R_sq_hi : b_R ^ 2 ≤ 2 * b ^ 2 := by
    rw [hb_R_sq]
    calc R * c' ^ (-(2 / 3 : ℝ))
        ≤ (2 * b ^ 2 * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hR_le_ACb, hACb_sq])
            (Real.rpow_nonneg hc'_pos.le _)
      _ = 2 * b ^ 2 := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  have hb_R_R : b_R ^ 2 * c' ^ (2 / 3 : ℝ) = R := by
    rw [hb_R_sq, mul_assoc, ← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
  let P_R : BandReductionParams := bandParamsAtWThr prob A_thr b_R hb_R_pos
  have hρR_ub : 2 * rhoR P_R c' R ≤ 0.035 := by
    have hle : rhoR P_R c' R ≤ rhoR (ywP0Thr prob A_thr) c' R_star := by
      unfold rhoR
      change kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R ≤
        kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R_star
      have := kappaV_pos
      gcongr
    have h0_ub : 2 * rhoR (ywP0Thr prob A_thr) c' R_star ≤ 0.035 := I₀.hρR_ub
    linarith only [hle, h0_ub]
  let I_R : BandReductionInstance P_R :=
    { c := I₀.c
      ε := I₀.ε
      R := R
      hc := I₀.hc
      hε := I₀.hε
      hR_lb := by change b_R ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R; exact hb_R_R.le
      hR_ub := by change R ≤ b_R ^ 2 * c' ^ (2 / 3 : ℝ) + 1; linarith only [hb_R_R]
      hρR_ub := hρR_ub
      W_tilde := I₀.W_tilde
      hW_cont := I₀.hW_cont
      hW_holo := I₀.hW_holo
      hW_symm := I₀.hW_symm
      hW_bound := I₀.hW_bound
      dmPos := I₀.dmPos
      dmNeg := I₀.dmNeg
      hdmPos_fin := I₀.hdmPos_fin
      hdmNeg_fin := I₀.hdmNeg_fin
      hdmPos_supp := I₀.hdmPos_supp
      hdmNeg_supp := I₀.hdmNeg_supp
      hdm_tv := I₀.hdm_tv
      T := I₀.T
      hdm_nonneg_tail := I₀.hdm_nonneg_tail
      E_sub := I₀.E_sub
      hE_sub_meas := I₀.hE_sub_meas
      hE_sub_sub := I₀.hE_sub_sub
      K_edge := I₀.K_edge
      hK_meas := I₀.hK_meas
      hW_edge := I₀.hW_edge
      hK_sub := I₀.hK_sub
      a_0 := I₀.a_0
      a_0' := I₀.a_0'
      a_2 := I₀.a_2
      R_0 := I₀.R_0
      Phi := I₀.Phi
      hK_factor := I₀.hK_factor
      ha_2_bd := I₀.ha_2_bd
      ha_0_deriv := I₀.ha_0_deriv
      ha_0_bd := I₀.ha_0_bd
      hR_0_nonpos := I₀.hR_0_nonpos
      hR_0_cont := I₀.hR_0_cont
      hR_0_even := I₀.hR_0_even
      hR_0_unimodal := I₀.hR_0_unimodal
      hPhi_odd := I₀.hPhi_odd
      ν := I₀.ν
      ν' := I₀.ν'
      invNu' := I₀.invNu'
      hν_deriv := I₀.hν_deriv
      hν'_cont := I₀.hν'_cont
      hν'_inv_pos := I₀.hν'_inv_pos
      hν'_inv_deriv := I₀.hν'_inv_deriv
      hinvNu'_cont := I₀.hinvNu'_cont
      hinvNu'_int := I₀.hinvNu'_int
      hinvNu'_integrable := I₀.hinvNu'_integrable
      μ := I₀.μ
      m := I₀.m
      m' := I₀.m'
      hPhi_deriv := I₀.hPhi_deriv
      hm_0 := I₀.hm_0
      hm_cont := I₀.hm_cont
      hm_strictMono := I₀.hm_strictMono
      hm_deriv := I₀.hm_deriv
      hm_step := I₀.hm_step
      hm_slope := I₀.hm_slope
      τ_0 := I₀.τ_0
      hτ_0_nn := I₀.hτ_0_nn
      hτ_0_eq_zero := I₀.hτ_0_eq_zero
      hτ_0_root := I₀.hτ_0_root
      u_tilde := I₀.u_tilde
      Delta := I₀.Delta
      hτ_0_below := I₀.hτ_0_below
      hτ_0_band := fun ξ hξ => I₀.hτ_0_band ξ ⟨hξ.1, hξ.2.trans hDelta_le⟩
      hu_tilde_int := I₀.hu_tilde_int.mono_set (Icc_subset_Icc_right hDelta_le) }
  -- Identify `bandB1 I_R = bandB1W prob c' R T g` and `bandB2 I_R = bandB2W prob c' R g`
  set M := prob.cardyNorm (c' / 12) g
  let fPos : ℝ → ℝ := fun t => max (g t) 0 * prob.cardyV (c' / 12) t / M
  have hT_pos : 0 < T := by
    have h0 : 0 < langerDelta pg c' 0 := by rw [langerDelta_zero]; have := xiStar_pos; positivity
    exact lt_of_lt_of_le h0 hT_lo'
  have hV_cont : Continuous (fun t => prob.cardyV (c' / 12) t) :=
    continuous_cardyV prob (c' / 12)
  have hg_cont : ContinuousOn g (Ioi 0) := hg.cont.mono Ioi_subset_Ici_self
  have hfPos_meas : AEMeasurable fPos (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn fPos (Ioi 0) := fun t ht =>
      (((hg_cont t ht).sup continuousWithinAt_const).mul hV_cont.continuousWithinAt).div_const M
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hfPos_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ fPos t := fun t ht => by
    dsimp [fPos]
    exact div_nonneg (mul_nonneg (le_max_right _ _)
      (prob.cardyV_nonneg hshift (mem_Ioi.mp ht).le)) hM_pos.le
  have hfPos_int : IntegrableOn fPos (Ioi 0) :=
    (hg.int_cardy.div_const M).mono' hfPos_meas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (hfPos_nn t ht)]
        dsimp [fPos]
        have hV_nn := prob.cardyV_nonneg hshift (mem_Ioi.mp ht).le
        have hmax_le : max (g t) 0 ≤ |g t| := max_le (le_abs_self _) (abs_nonneg _)
        gcongr)
  have hT_le_ΔR : T ≤ virasoroDeltaChart c' (-R) := by
    have hRm : -R ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
      ⟨by linarith only [hR_le_AC], by linarith only [hR_pos, sq_nonneg (Q.AC c')]⟩
    have hAm : -A_thr ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
      ⟨by linarith only [hR_thr, hR_le_AC], by linarith only [hA_pos, sq_nonneg (Q.AC c')]⟩
    exact hT_hi.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn hRm hAm
      (by linarith only [hR_thr]))
  have hB1_eq : bandB1 I_R = bandB1W prob c' R T g := by
    have hsub_Icc : Icc T (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) :=
      fun t ht => lt_of_lt_of_le hT_pos ht.1
    have h1 : bandB1 I_R = R⁻¹ * ∫ ξ in Icc T (langerDelta pg c' (-R)),
        (-I₀.u_tilde ξ) ∂((volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (fPos t))) := by
      dsimp only [bandB1, I_R, I₀, ywBandInstance, bandMeasPos, bandPos]
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
        (fun t => M⁻¹ * ((-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t)))
        (Icc T (virasoroDeltaChart c' (-R))) := fun t ht => by
      have ht_pos : t ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (lt_of_lt_of_le hT_pos ht.1)
      dsimp only
      rw [ENNReal.toReal_ofReal (hfPos_nn t ht_pos), smul_eq_mul]
      dsimp [fPos]
      rw [max_eq_left (hg_nn t ht.1)]
      have hu_t := Q.UT_between hc'_pos (by linarith only [hR_le_AC] : -(Q.AC c' ^ 2) ≤ -R)
        (sq_nonneg _) (by linarith only [hR_pos] : -R ≤ 0) (hT_lo.trans ht.1) ht.2
      have hu_abs : |virasoroUT c' t| ≤ Q.AC c' ^ 2 :=
        abs_le.mpr ⟨by linarith only [hu_t.1.1, hR_le_AC],
          hu_t.1.2.trans (sq_nonneg _)⟩
      have hld_eq : langerDelta pg c' (virasoroUT c' t) = t :=
        (Q.langerDelta_eq hc'_pos hu_abs).trans hu_t.2
      have hu_star : virasoroUT c' t ∈ Icc (-R_star) 0 :=
        ⟨by linarith only [hu_t.1.1, hR_le_Rstar], hu_t.1.2⟩
      have hut_eq : I₀.u_tilde t = virasoroUT c' t := by
        have hm := hmom₀.2.1 (virasoroUT c' t) hu_star
        rwa [hld_eq] at hm
      rw [hut_eq]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcongr, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT_le_ΔR, ← mul_assoc]
    rfl
  have hB2_eq : bandB2 I_R = bandB2W prob c' R g := by
    have h1 : bandB2 I_R = (((volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (fPos s))) (Ici (langerDelta pg c' (-R)))).toReal := by
      dsimp only [bandB2, I_R, I₀, ywBandInstance, bandMeasPos, bandPos]
    rw [h1, withDensity_apply _ (measurableSet_Ici : MeasurableSet (Ici (langerDelta pg c' (-R))))]
    have hsub : Ici (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) := fun t ht => by
      have ht' : virasoroDeltaChart c' (-R) ≤ t := by
        rw [← hΔR_eq]; exact ht
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
        (fun t => M⁻¹ * (g t * prob.cardyV (c' / 12) t))
        (Ici (virasoroDeltaChart c' (-R))) := fun t ht => by
      dsimp [fPos]
      rw [max_eq_left (hg_nn t (hT_le_ΔR.trans ht))]
      ring
    rw [setIntegral_congr_fun measurableSet_Ici hcongr, integral_const_mul]
    rfl
  -- Apply `teb_band_reduction I_R` on the sector `S`
  intro ζ _ hlo hhi hre_lb
  have hζ_pos : 0 < ‖ζ‖ :=
    lt_of_lt_of_le (by have := kappaV_pos; positivity) hlo
  have hζ_re_pos : 0 < ζ.re :=
    lt_of_lt_of_le (by positivity) hre_lb
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
  have hcos_lb : I_R.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ := by
    change c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ
    rw [hcos_eq_div, le_div_iff₀ hζ_pos]
    exact hre_lb
  have hlo' : rhoR P_R I_R.c I_R.R / 3 ≤ ‖ζ‖ := hlo
  have hhi' : ‖ζ‖ ≤ 2 * rhoR P_R I_R.c I_R.R := hhi
  have hred := (teb_band_reduction I_R hlo' hhi' hcos_eq hcos_lb).1
  have hW_eq : ‖I_R.W_tilde ζ‖ = M⁻¹ * ‖tildeWW prob.w c' g ζ‖ := by
    have h1 : I_R.W_tilde ζ = ((M⁻¹ : ℝ) : ℂ) * tildeWW prob.w c' g ζ := hmom₀.1 ζ
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM_pos.le)]
  change ‖I_R.W_tilde ζ‖ ≤
    tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
      (c' ^ (1 / 3 : ℝ) * (bandB1 I_R + bandB2 I_R) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ at hred
  rw [hW_eq, hB1_eq, hB2_eq] at hred
  have hmul_M := mul_le_mul_of_nonneg_left hred hM_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at hmul_M
  have hCY_le : tebBandConst P_R ≤ max (uniformBandConstWThr prob A_thr b) 1 :=
    (tebBandConst_yvBandParamsAt_leFor_thr hb_pos hb_R_pos hb_R_lo hb_R_sq_hi).trans (le_max_left _ _)
  have hc16_le1 : c' ^ (-(1 / 6 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc'_ge1 (by norm_num)
  have hB1_nn := bandB1W_nonneg_thr hA_pos hc'_cq hR_thr hR_le_AC hg_wf hT_lo hT_hi
  have hB2_nn := bandB2W_nonneg_thr hA_pos hc'_cq hR_thr hR_le_AC hg_wf hT_hi
  have hCY_nn : 0 ≤ tebBandConst P_R := (tebBandConst_pos P_R).le
  calc ‖tildeWW prob.w c' g ζ‖
      ≤ M * (tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) +
            c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) := hmul_M
    _ ≤ M * (max (uniformBandConstWThr prob A_thr b) 1 * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1) /
          Real.cos ψ) := by
        gcongr
    _ = M * (max (uniformBandConstWThr prob A_thr b) 1 *
          (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
        rw [hcos_eq_div]
        field_simp [hζ_pos.ne', hζ_re_pos.ne']

lemma uniform_band_boundForW {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ Q.bV)
    (hScale : 2 * b ^ 2 ≤ Q.scaleThresh)
    {c' R T : ℝ}
    (hc'_yv : ywThresh prob langerChartSpec_virasoro virasoroAThr ≤ c')
    (hc'_cq : Q.cQ ≤ c')
    (hR_thr : virasoroAThr ≤ R)
    (hR_lo : b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_hi : R + 1 ≤ chartACAt b c' ^ 2)
    {g : ℝ → ℝ} (hg_wf : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    let M := prob.cardyNorm (c' / 12) g
    let B₁ := bandB1W prob c' R T g
    let B₂ := bandB2W prob c' R g
    ∀ ζ ∈ stripClosed,
      kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
      ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
      c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
      ‖tildeWW prob.w c' g ζ‖ ≤ M *
        (max (uniformBandConstW prob b) 1 * (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) :=
  uniform_band_boundForW_thr virasoroAThr_pos hb_pos hb_le hScale hc'_yv hc'_cq hR_thr hR_lo hR_hi
    hg_wf hT_lo hT_hi

/-! ### 4. Proof of `YVInputForW prob` / `YVInput` and Theorem J Corollaries -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.uniform_band_boundForW_thr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_band_boundForW_thr

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.uniform_band_boundForW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_band_boundForW

end FormalResearch.ModularBootstrap.FixedWeightBand
