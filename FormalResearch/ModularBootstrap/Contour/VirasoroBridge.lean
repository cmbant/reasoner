module

public import FormalResearch.ModularBootstrap.Contour.WindowEnvelope
public import FormalResearch.ModularBootstrap.StripMultiplier.BandBound
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.TheoremJ

/-!
# Virasoro Band-Feedback Bridge (`YVInput`) and Theorem J Corollaries

Closes the Theorem J loop (`lower_o1_two_edge.tex`, §J4, §J8, §J9: Proposition `Y_V` `vlo:YV`,
Lemma `Z` `vlo:Z`, Proposition `L` `vlo:L`, Theorem `FT-L.FW` `wone:ftlfw`, and Theorem `J`
`vlo:J`) by combining:
1. Unconditional `langerChartSpec_virasoro : LangerChartSpec` and `StripMultiplier.yvBandInstance`
   (`StripMultiplier/BandBound.lean`), rescaled across the full Virasoro bootstrap annulus
   `R ∈ [b_V^2 c'^{2/3}, 2 b_V^2 c'^{2/3} - 1]`;
2. **Lemma Z** (`lemma_Z`, `Contour/WindowEnvelope.lean`), which builds upon **Lemma Z'**
   (`lemma_Zp`) and **Lemma D'** (`lemma_Dp`).

## Scale compatibility hypothesis `VirasoroBVScaleCompat`
In `lower_o1_two_edge.tex` (§J2, §J4, §J8), the dimensionless bootstrap width `b_V > 0`
(`A_{c'} = √2 b_V c'^{1/3}`, `A_{c'}^2 = 2 b_V^2 c'^{2/3}`) is chosen small enough after
Proposition `Y_V`, Lemma `D'`, and Lemma `Z` so that `2 b_V^2` lies inside their inner Langer
radii. In Lean, `ConcreteBootstrap.virasoroBV` was fixed earlier via `Classical.choice` in
`ConcreteBootstrap/LangerChart.lean` before `StripMultiplier/BandBound.lean` and `Contour/*`.
We isolate that single scalar parameter constraint as `VirasoroBVScaleCompat`:
`2 * virasoroBV ^ 2 ≤ virasoroScaleThresh` (with `virasoroScaleThresh_pos` and non-vacuity
`virasoroBVScaleCompat_nonvacuous`), prove `yvInput_of_scaleCompat : VirasoroBVScaleCompat → YVInput`,
and deduce `theoremJ_of_scaleCompat`, `theoremJ_T_weak_of_scaleCompat`,
`theoremJ_T_V_of_scaleCompat`, and `theoremJ_Delta_best_of_scaleCompat`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Contour

open FormalResearch.Special
open FormalResearch.TwoEdgeBootstrap
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.StripBand
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Crossing

/-! ### 1. Inner-chart scale threshold and `VirasoroBVScaleCompat` -/

/-- Unconditional Virasoro saddle/Langer comparability (`lower_o1_two_edge.tex`, Lemma S6
`vlo:S6`), discharging `LangerChartSpec` via `langerChartSpec_virasoro`. -/
theorem lemma_S6_virasoro :
    (∃ r_b > 0, ∃ C_b ≥ 0,
      r_b ≤ rB0 / 2 ∧
      (∀ k : ℕ, (iteratedDeriv k bEven 0).im = 0) ∧
      (∀ ζ ∈ ball (0 : ℂ) r_b,
        ‖chartB ζ - (xiStar : ℂ) - (-(((Real.pi / (4 * √2) : ℝ) : ℂ))) * ζ ^ 2‖ ≤
          C_b * ‖ζ‖ ^ 4)) ∧
    (∃ q_V : ℂ → ℂ, ∃ c₀_max > 0, ∃ C₁ ≥ 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      AnalyticOnNhd ℂ q_V (ball (0 : ℂ) c₀_max) ∧
      q_V 0 = 1 ∧
      (∀ k : ℕ, (iteratedDeriv k q_V 0).im = 0) ∧
      (∀ x : ℝ, |x| < c₀_max → (q_V (x : ℂ)).im = 0 ∧ 0 < (q_V (x : ℂ)).re) ∧
      (∀ c₀ ∈ Ioo (0 : ℝ) c₀_max,
        ∀ (c' a' phi : ℝ), 0 < c' → 0 ≤ a' → 0 ≤ phi → phi ≤ Real.pi / 2 →
          a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ →
          let u : ℂ := ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * phi : ℝ) : ℂ))
          let z : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
          let ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * q_V z
          let σp := ζp.re
          let τp := ζp.im
          let ρ := ‖ζp‖
          ζp ^ 2 = ((kappaV ^ 2 : ℝ) : ℂ) * z * q_V z ^ 2 ∧
          chartB ζp = langerChartSpec_virasoro.bL z ∧
          0 ≤ σp ∧ 0 ≤ τp ∧
          |ρ - kappaV * c' ^ (-(1 / 3 : ℝ)) * a'| ≤ C₁ * c₀ * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') ∧
          |σp - ρ * Real.sin phi| ≤ C₂ * ρ ^ 2 * (ρ * Real.sin phi) ∧
          |(chartB ζp).im - (-(Real.pi / (2 * √2)) * σp * τp)| ≤
            C₃ * ρ ^ 2 * (Real.pi / (2 * √2) * σp * τp) ∧
          (chartB ζp).im ≤ 0) ∧
      (∀ c₀ ∈ Ioo (0 : ℝ) c₀_max,
        ∀ (c' v : ℝ), 0 < c' → 0 ≤ v → v * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ →
          let u : ℂ := -(v : ℂ)
          let z : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
          let ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * u ^ (1 / 2 : ℂ) * q_V z
          let τ₀ := ζp.im
          0 ≤ τ₀ ∧ ζp = Complex.I * (τ₀ : ℂ) ∧
          |c' ^ (1 / 3 : ℝ) * τ₀ - kappaV * √v| ≤ C₁ * c₀ * (kappaV * √v) ∧
          chartB ζp = (edgeX0 τ₀ : ℂ))) :=
  Chart.lemma_S6 langerChartSpec_virasoro

/-- Combined inner-chart scale cap `min (c_{0, YV} / 2) zScaleCap > 0` within which
Proposition `Y_V` (`yvBandInstance`), Lemma `D'` (`lemma_Dp`), and Lemma `Z` (`lemma_Z`)
simultaneously apply across `R ∈ [b_V^2 c'^{2/3}, 2 b_V^2 c'^{2/3} - 1]`. -/
noncomputable def virasoroScaleThresh : ℝ :=
  min ((yvWitness langerChartSpec_virasoro).c₀ / 2) zScaleCap

lemma virasoroScaleThresh_pos : 0 < virasoroScaleThresh := by
  unfold virasoroScaleThresh
  exact lt_min (half_pos (yvWitness langerChartSpec_virasoro).hc₀_pos) zScaleCap_pos

/-- **Scale compatibility for `virasoroBV`** (`lower_o1_two_edge.tex`, §J2, §J4, §J8):
`2 * virasoroBV ^ 2 ≤ virasoroScaleThresh`.

Records that the dimensionless chart parameter `b_V = virasoroBV > 0` (`A_{c'}^2 = 2 b_V^2 c'^{2/3}`)
lies within the inner Langer radius `min (c_{0, YV} / 2) zScaleCap` of Proposition `Y_V`,
Lemma `D'`, and Lemma `Z`. -/
def VirasoroBVScaleCompat : Prop :=
  2 * virasoroBV ^ 2 ≤ virasoroScaleThresh

/-- Non-vacuity of the `VirasoroBVScaleCompat` scale constraint: there exist positive parameters
`b > 0` satisfying `2 * b ^ 2 ≤ virasoroScaleThresh`. -/
theorem virasoroBVScaleCompat_nonvacuous :
    ∃ b : ℝ, 0 < b ∧ 2 * b ^ 2 ≤ virasoroScaleThresh := by
  refine ⟨Real.sqrt (virasoroScaleThresh / 4), ?_, ?_⟩
  · exact Real.sqrt_pos.mpr (div_pos virasoroScaleThresh_pos (by norm_num))
  · have hpos := virasoroScaleThresh_pos
    rw [Real.sq_sqrt (div_nonneg hpos.le (by norm_num))]
    linarith only [hpos]

/-! ### 2. Parametric `BandReductionParams` and uniform `tebBandConst` bound across `[b_V, √2 b_V]` -/

private noncomputable def yvP0 : BandReductionParams :=
  yvBandParams langerChartSpec_virasoro virasoroAThr

private noncomputable def yvBandParamsAt (b_R : ℝ) (hb_R : 0 < b_R) : BandReductionParams :=
  { yvP0 with
    b := b_R
    hb := hb_R }

private noncomputable def yvUniformBandConst : ℝ :=
  let P := yvP0
  let ρ_min_lo := kappaV * virasoroBV / 3
  let C_pf_lo := ρ_min_lo ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  let C_gauss5 := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
  let C_core := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  let C_sub := P.C_a * C_gauss5 / P.κ_sub
  let C_tail := C_core + C_sub + 2 * tebBandOscConst P
  let C_band_hi := tebBandOscConst P * max (P.C_τ * (2 * virasoroBV ^ 2 + 1)) 1
  max C_tail C_band_hi / (C_pf_lo * ρ_min_lo)

private lemma tebBandConst_yvBandParamsAt_le {b_R : ℝ} (hb_R : 0 < b_R)
    (hb_lo : virasoroBV ≤ b_R) (hb_sq_hi : b_R ^ 2 ≤ 2 * virasoroBV ^ 2) :
    tebBandConst (yvBandParamsAt b_R hb_R) ≤ yvUniformBandConst := by
  let P := yvP0
  have hosc_pos : 0 < tebBandOscConst P := by
    unfold tebBandOscConst
    have hb₀ : 0 < min P.c_1 (P.c_2 / 16) := lt_min P.hc_1 (div_pos P.hc_2 (by norm_num))
    have := tebOscConst_pos hb₀ (P.M + 11 / 2)
    have := P.hC_a; have := P.hC_ν
    positivity
  set ρ_min_lo : ℝ := kappaV * virasoroBV / 3
  set ρ_min_R : ℝ := kappaV * b_R / 3
  have hρ_lo_pos : 0 < ρ_min_lo := by
    dsimp [ρ_min_lo]; have := kappaV_pos; have := virasoroBV_pos; positivity
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
  set C_band_hi : ℝ := tebBandOscConst P * max (P.C_τ * (2 * virasoroBV ^ 2 + 1)) 1
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
  have hlhs_eq : tebBandConst (yvBandParamsAt b_R hb_R) =
      max C_tail C_band_R / (C_pf_R * ρ_min_R) := rfl
  have hrhs_eq : yvUniformBandConst =
      max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) := rfl
  rw [hlhs_eq, hrhs_eq]
  calc max C_tail C_band_R / (C_pf_R * ρ_min_R)
      ≤ max C_tail C_band_hi / (C_pf_R * ρ_min_R) :=
        div_le_div_of_nonneg_right hnum_le hden_R_pos.le
    _ ≤ max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) :=
        div_le_div_of_nonneg_left hnum_hi_pos.le hden_lo_pos hden_le

/-! ### 3. Rescaled `BandReductionInstance` and moment bridge across `[b_V^2 c'^{2/3}, A_{c'}^2 - 1]` -/

private lemma virasoro_uniform_band_bound (hScale : VirasoroBVScaleCompat)
    {c' R T : ℝ}
    (hc'_yv : yvThresh langerChartSpec_virasoro virasoroAThr ≤ c')
    (hc'_cq : virasoroCQEnv ≤ c')
    (hR_thr : virasoroAThr ≤ R)
    (hR_lo : virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_hi : R + 1 ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg_wf : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    let M := virasoroProblem.cardyNorm (c' / 12) g
    let B₁ := virasoroBandB1 c' R T g
    let B₂ := virasoroBandB2 c' R g
    ∀ ζ ∈ stripClosed,
      kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
      ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
      c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
      ‖tildeWV c' g ζ‖ ≤ M *
        (max yvUniformBandConst 1 * (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
  dsimp only
  let pg := langerChartSpec_virasoro
  let A_thr := virasoroAThr
  let w := yvWitness pg
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
  have h2bV_c0 : 2 * virasoroBV ^ 2 ≤ w.c₀ / 2 :=
    hScale.trans (min_le_left _ _)
  have hAC_sq : virasoroAC c' ^ 2 = 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) :=
    virasoroAC_sq c' hc'_pos.le
  have hR_le_AC : R ≤ virasoroAC c' ^ 2 := by linarith only [hR_hi]
  have hA_pos : 0 < A_thr := virasoroAThr_pos
  have hR_pos : 0 < R := lt_of_lt_of_le hA_pos hR_thr
  -- Compatibility of `langerDelta pg c'` with `virasoroDeltaChart c'` at `0`, `-A_thr`, `-R`
  have hΔ0_eq : langerDelta pg c' 0 = virasoroDeltaChart c' 0 :=
    langerDelta_virasoro_eq hc'_pos (by rw [abs_zero]; exact sq_nonneg _)
  have hΔA_eq : langerDelta pg c' (-A_thr) = virasoroDeltaChart c' (-A_thr) :=
    langerDelta_virasoro_eq hc'_pos (by rw [abs_neg, abs_of_pos hA_pos]; exact hR_thr.trans hR_le_AC)
  have hΔR_eq : langerDelta pg c' (-R) = virasoroDeltaChart c' (-R) :=
    langerDelta_virasoro_eq hc'_pos (by rw [abs_neg, abs_of_pos hR_pos]; exact hR_le_AC)
  have hT_lo' : langerDelta pg c' 0 ≤ T := by rw [hΔ0_eq]; exact hT_lo
  have hT_hi' : T ≤ langerDelta pg c' (-A_thr) := by rw [hΔA_eq]; exact hT_hi
  -- Reference `BandReductionInstance` at `R_star := yvP0.b^2 * c'^(2/3) = (w.c₀ / 2) * c'^(2/3)`
  let R_star : ℝ := yvP0.b ^ 2 * c' ^ (2 / 3 : ℝ)
  have hP0_b_sq : yvP0.b ^ 2 = w.c₀ / 2 := by
    dsimp [yvP0, yvBandParams]
    exact Real.sq_sqrt (div_nonneg w.hc₀_pos.le zero_lt_two.le)
  have hR_le_Rstar : R ≤ R_star := by
    dsimp [R_star]
    rw [hP0_b_sq]
    calc R ≤ virasoroAC c' ^ 2 := hR_le_AC
      _ = 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) := hAC_sq
      _ ≤ (w.c₀ / 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right h2bV_c0 (Real.rpow_nonneg hc'_pos.le _)
  have hRstar_ub : R_star ≤ yvP0.b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := by
    dsimp [R_star]; linarith only []
  let I₀ := yvBandInstance pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hmom₀ := yvBandInstance_moments pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hProps₀ := langerDelta_props hc'_yv (R := R_star) le_rfl hRstar_ub
  have hDelta_le : langerDelta pg c' (-R) ≤ langerDelta pg c' (-R_star) :=
    hProps₀.2.2.2.2.1.monotoneOn ⟨hR_pos.le, hR_le_Rstar⟩ ⟨hProps₀.1.le, le_rfl⟩ hR_le_Rstar
  -- Rescaled `b_R := √(R * c'^(-2/3))` in `[virasoroBV, √2 * virasoroBV]`
  set b_R : ℝ := Real.sqrt (R * c' ^ (-(2 / 3 : ℝ)))
  have hb_R_sq : b_R ^ 2 = R * c' ^ (-(2 / 3 : ℝ)) :=
    Real.sq_sqrt (mul_nonneg hR_pos.le (Real.rpow_nonneg hc'_pos.le _))
  have hb_R_lo : virasoroBV ≤ b_R := by
    refine Real.le_sqrt_of_sq_le ?_
    calc virasoroBV ^ 2
        = (virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ R * c' ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hR_lo (Real.rpow_nonneg hc'_pos.le _)
  have hb_R_pos : 0 < b_R := lt_of_lt_of_le virasoroBV_pos hb_R_lo
  have hb_R_sq_hi : b_R ^ 2 ≤ 2 * virasoroBV ^ 2 := by
    rw [hb_R_sq]
    calc R * c' ^ (-(2 / 3 : ℝ))
        ≤ (2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hR_le_AC, hAC_sq])
            (Real.rpow_nonneg hc'_pos.le _)
      _ = 2 * virasoroBV ^ 2 := by
          rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  have hb_R_R : b_R ^ 2 * c' ^ (2 / 3 : ℝ) = R := by
    rw [hb_R_sq, mul_assoc, ← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, mul_one]
  let P_R : BandReductionParams := yvBandParamsAt b_R hb_R_pos
  have hρR_ub : 2 * rhoR P_R c' R ≤ 0.035 := by
    have hle : rhoR P_R c' R ≤ rhoR yvP0 c' R_star := by
      unfold rhoR
      change kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R ≤
        kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R_star
      have := kappaV_pos
      gcongr
    have h0_ub : 2 * rhoR yvP0 c' R_star ≤ 0.035 := I₀.hρR_ub
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
  -- Identify `bandB1 I_R = virasoroBandB1 c' R T g` and `bandB2 I_R = virasoroBandB2 c' R g`
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
        abs_le.mpr ⟨by linarith only [hu_t.1.1, hR_le_AC],
          hu_t.1.2.trans (sq_nonneg _)⟩
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
        (fun t => M⁻¹ * (g t * virasoroProblem.cardyV (c' / 12) t))
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
  have hW_eq : ‖I_R.W_tilde ζ‖ = M⁻¹ * ‖tildeWV c' g ζ‖ := by
    have h1 : I_R.W_tilde ζ = ((M⁻¹ : ℝ) : ℂ) * tildeWV c' g ζ := hmom₀.1 ζ
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM_pos.le)]
  change ‖I_R.W_tilde ζ‖ ≤
    tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
      (c' ^ (1 / 3 : ℝ) * (bandB1 I_R + bandB2 I_R) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ at hred
  rw [hW_eq, hB1_eq, hB2_eq] at hred
  have hmul_M := mul_le_mul_of_nonneg_left hred hM_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at hmul_M
  have hCY_le : tebBandConst P_R ≤ max yvUniformBandConst 1 :=
    (tebBandConst_yvBandParamsAt_le hb_R_pos hb_R_lo hb_R_sq_hi).trans (le_max_left _ _)
  have hc16_le1 : c' ^ (-(1 / 6 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc'_ge1 (by norm_num)
  have hB1_nn := virasoroBandB1_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_lo hT_hi
  have hB2_nn := virasoroBandB2_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_hi
  have hCY_nn : 0 ≤ tebBandConst P_R := (tebBandConst_pos P_R).le
  calc ‖tildeWV c' g ζ‖
      ≤ M * (tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) +
            c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) := hmul_M
    _ ≤ M * (max yvUniformBandConst 1 * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) /
          Real.cos ψ) := by
        gcongr
    _ = M * (max yvUniformBandConst 1 *
          (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
        rw [hcos_eq_div]
        field_simp [hζ_pos.ne', hζ_re_pos.ne']

/-! ### 4. Proof of `YVInput` and Theorem J Corollaries -/

/-- **Proposition `Y_V` + Lemma `Z` ⇒ `YVInput`** (`lower_o1_two_edge.tex`, `vlo:YV`, `vlo:Z`,
`vlo:L`): under `VirasoroBVScaleCompat`, the ConcreteBootstrap band-feedback input `YVInput` holds
with `C_fb = C_B * max C_{Y, unif} 1 ≥ 1`. -/
theorem yvInput_of_scaleCompat (hScale : VirasoroBVScaleCompat) : YVInput := by
  have hb_lo : 0 < virasoroBV := virasoroBV_pos
  have hb_le : virasoroBV ≤ Real.sqrt 2 * virasoroBV :=
    le_mul_of_one_le_left hb_lo.le (by rw [Real.one_le_sqrt]; norm_num)
  have hb_hi_sq : (Real.sqrt 2 * virasoroBV) ^ 2 = 2 * virasoroBV ^ 2 := by
    rw [mul_pow, Real.sq_sqrt zero_le_two]
  have hb_cap : (Real.sqrt 2 * virasoroBV) ^ 2 ≤ zScaleCap :=
    hb_hi_sq.le.trans (hScale.trans (min_le_right _ _))
  obtain ⟨c_Z, C_B, _hc_Z_ge, hC_B_ge1, hZ⟩ := lemma_Z hb_lo hb_le hb_cap
  set C_Y1 : ℝ := max yvUniformBandConst 1
  have hCY1_ge1 : 1 ≤ C_Y1 := le_max_right _ _
  obtain ⟨C_fb, hC_fb_eq⟩ : ∃ x : ℝ, x = C_B * C_Y1 := ⟨_, rfl⟩
  obtain ⟨c_YV, hc_YV_eq⟩ : ∃ x : ℝ,
    x = max virasoroCQEnv (max (yvThresh langerChartSpec_virasoro virasoroAThr) c_Z) := ⟨_, rfl⟩
  have hC_fb_ge1 : 1 ≤ C_fb := by rw [hC_fb_eq]; nlinarith only [hC_B_ge1, hCY1_ge1]
  have hc_YV_cq : virasoroCQEnv ≤ c_YV := hc_YV_eq ▸ le_max_left _ _
  refine ⟨C_fb, c_YV, hC_fb_ge1, hc_YV_cq, ?_⟩
  intro c' T R hc' hR_thr hR_lo hR_hi g hg_wf hT_lo hT_hi
  have hc'_cq : virasoroCQEnv ≤ c' := hc_YV_cq.trans hc'
  have hc'_yv : yvThresh langerChartSpec_virasoro virasoroAThr ≤ c' :=
    (hc_YV_eq ▸ (le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_Z : c_Z ≤ c' :=
    (hc_YV_eq ▸ (le_max_right _ _).trans (le_max_right _ _)).trans hc'
  have hc'_pos : 0 < c' :=
    lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith only [this]) hc'_cq
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]
    have := virasoroCQEnv_ge
    linarith only [this, hc'_cq]
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero hshift hg_wf.1 hg_wf.2.1
  have hR_hi_Z : R + 1 ≤ (Real.sqrt 2 * virasoroBV) ^ 2 * c' ^ (2 / 3 : ℝ) := by
    rwa [hb_hi_sq, ← virasoroAC_sq c' hc'_pos.le]
  have hR_le_AC : R ≤ virasoroAC c' ^ 2 := by linarith only [hR_hi]
  have hB1_nn := virasoroBandB1_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_lo hT_hi
  have hB2_nn := virasoroBandB2_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_hi
  set Λ : ℝ := C_Y1 * (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1)
  have hΛ_ge1 : 1 ≤ Λ := by
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1 := by
      have hnn : 0 ≤ c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) := by
        positivity
      linarith only [hnn]
    dsimp [Λ]
    nlinarith only [hCY1_ge1, h1]
  have hband := virasoro_uniform_band_bound hScale hc'_yv hc'_cq hR_thr hR_lo hR_hi
    hg_wf hT_lo hT_hi
  have henv := hZ hc'_Z hΛ_ge1 hR_lo hR_hi_Z hg_wf.1 hM_pos hband
  have hL_eq : C_B * Λ =
      C_fb * (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) := by
    rw [hC_fb_eq]; dsimp [Λ]; ring
  rwa [← hL_eq]

/-- **Theorem `J` / Theorem `W1'(1)` for weakly feasible nonzero Virasoro tests**
(`lower_o1_two_edge.tex`, `vlo:J` & `wone:genlower(1)`), with `YVInput` discharged via
`yvInput_of_scaleCompat`. -/
theorem theoremJ_of_scaleCompat (hScale : VirasoroBVScaleCompat) :
    ∃ c_2 C : ℝ, virasoroCQEnv + 1 ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c T : ℝ}, c_2 ≤ c → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible ((c - 1) / 12) T g →
        xiBar * (c - 1) + Aopt * (c - 1) ^ (1 / 3 : ℝ) - C ≤ T :=
  theoremJ_of_YV (yvInput_of_scaleCompat hScale)

/-- **Theorem `J` for `T_weak`** (`lower_o1_two_edge.tex`, `vlo:J`), with `YVInput` discharged via
`yvInput_of_scaleCompat`. -/
theorem theoremJ_T_weak_of_scaleCompat (hScale : VirasoroBVScaleCompat) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_weak c' :=
  theoremJ_T_weak (yvInput_of_scaleCompat hScale)

/-- **Theorem `J` for `T_V`** (`lower_o1_two_edge.tex`, `vlo:J`), with `YVInput` discharged via
`yvInput_of_scaleCompat`. -/
theorem theoremJ_T_V_of_scaleCompat (hScale : VirasoroBVScaleCompat) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_V c' :=
  theoremJ_T_V (yvInput_of_scaleCompat hScale)

/-- **Theorem `J` for the optimal primary gap `Δ_best`** (`lower_o1_two_edge.tex`, `vlo:J`;
`Δ_best(c') = c'/12 + T_V(c')`), with `YVInput` discharged via `yvInput_of_scaleCompat`:
`Δ_best(c') ≥ c' / Λ_V + A_opt c'^{1/3} - C` for all `c' ≥ c_2`. -/
theorem theoremJ_Delta_best_of_scaleCompat (hScale : VirasoroBVScaleCompat) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        c' / lambdaV + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.Delta_best c' :=
  theoremJ_Delta_best (yvInput_of_scaleCompat hScale)

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Contour.lemma_S6_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S6_virasoro

/-- info: 'FormalResearch.ModularBootstrap.Contour.virasoroBVScaleCompat_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroBVScaleCompat_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.Contour.yvInput_of_scaleCompat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yvInput_of_scaleCompat

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_of_scaleCompat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_of_scaleCompat

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_T_weak_of_scaleCompat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_T_weak_of_scaleCompat

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_T_V_of_scaleCompat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_T_V_of_scaleCompat

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_Delta_best_of_scaleCompat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_Delta_best_of_scaleCompat

end FormalResearch.ModularBootstrap.Contour
