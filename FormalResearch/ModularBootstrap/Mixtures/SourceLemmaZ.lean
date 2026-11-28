module

public import FormalResearch.ModularBootstrap.Mixtures.SourceLemmaQ
public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWBridge

/-!
# Proposition `Y_V` Uniform Band Bound and Lemma `Z` Transfer for Signed Common Sources

Adapts `FixedWeightBand.BootstrapWYVBand` and `FixedWeightBand.BootstrapWYV` to
`C : CommonSource` (`C.src`) with `Q : LemmaQSrcData C`:
* `bandB1Src`, `bandB2Src`, `YVInputAtForSrcThr`, `YVInputForSrc`.
* `uniform_band_boundFor_src_thr`: uniform sector bound on `tildeWW C.src.w c' g` over
  `R ∈ [b² c'^{2/3}, A_{c'}(b)² - 1]`, rescaling `ywBandInstanceSrc` from `SourceBandBound`.
* `yvInputForSrc_of_scaleCompat_thr`, `yvInputForSrc_bvChoice`: proves `YVInputForSrc C.src Q.bvChoice`
  by calling `lemma_Z_W_band Q.D` with `Λ' := max 1 (M_src / M₀) * Λ_src` and transferring via
  `(M₀ / M_src) * max 1 (M_src / M₀) ≤ max 1 C.F.d⁻¹` and `‖C.src.cardyVC / cardyVC C.F.prob‖ ≤ Q.C_rat`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.Special FormalResearch.TwoEdgeBootstrap
open Crossing PoissonJensen TipFront ConcreteBootstrap FixedWeightTip FixedWeightBand WeightAxioms
open FormalResearch.ModularBootstrap.Chart FormalResearch.ModularBootstrap.StripBand
open FormalResearch.ModularBootstrap.StripMultiplier

/-! ### Section 1: Signed-source band moments and `YVInputForSrc` -/

/-- Band moment `B_1` for `ShiftSource`. -/
noncomputable def bandB1Src (src : ShiftSource) (c' R T : ℝ) (g : ℝ → ℝ) : ℝ :=
  R⁻¹ * (src.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in T..(virasoroDeltaChart c' (-R)),
      (-virasoroUT c' t) * (g t * src.cardyV (c' / 12) t)

/-- Band moment `B_2` for `ShiftSource`. -/
noncomputable def bandB2Src (src : ShiftSource) (c' R : ℝ) (g : ℝ → ℝ) : ℝ :=
  (src.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in Ici (virasoroDeltaChart c' (-R)),
      g t * src.cardyV (c' / 12) t

/-- Band-feedback input predicate at cutoff radius `A_thr` and scale `b` for `ShiftSource`. -/
def YVInputAtForSrcThr (src : ShiftSource) (A_thr b : ℝ)
    (Ψ : ℝ → (ℝ → ℝ) → ℂ → ℂ) (C_fb c_YV : ℝ) : Prop :=
  ∀ ⦃c' T R : ℝ⦄,
    c_YV ≤ c' →
      A_thr ≤ R →
      b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
      R + 1 ≤ chartACAt b c' ^ 2 →
      ∀ ⦃g : ℝ → ℝ⦄,
        src.IsWeaklyFeasible (c' / 12) T g →
        virasoroDeltaChart c' 0 ≤ T →
        T ≤ virasoroDeltaChart c' (-A_thr) →
        YVEnvBound (Ψ c' g) c' R
          (C_fb * (c' ^ (1 / 3 : ℝ) * (bandB1Src src c' R T g + bandB2Src src c' R g) + 1))

/-- Full level-one band-feedback input predicate (`A_thr = virasoroAThr`) for `ShiftSource`. -/
def YVInputForSrc (src : ShiftSource) (b : ℝ) : Prop :=
  ∃ C_fb c_YV : ℝ, 1 ≤ C_fb ∧ 10000 ≤ c_YV ∧
    YVInputAtForSrcThr src virasoroAThr b (psiTildeSrc src) C_fb c_YV

section BandHelpers

variable {C : CommonSource} (Q : LemmaQSrcData C)

lemma LemmaQSrcData.langerDelta_eq {c' u : ℝ} (hc' : 0 < c') (hu : |u| ≤ Q.AC c' ^ 2) :
    langerDelta langerChartSpec_virasoro c' u = virasoroDeltaChart c' u :=
  langerDelta_virasoro_eq hc' (Q.abs_le_virasoro hc'.le hu)

lemma LemmaQSrcData.totalShift_prob_le {c' : ℝ} (hc' : Q.cQ ≤ c') :
    C.F.prob.totalShift ≤ c' / 12 := by
  have := Q.hcQ_prob_shift.trans hc'
  have := Q.hcQ_10000.trans hc'
  linarith

lemma LemmaQSrcData.a0_le {c' : ℝ} (hc' : Q.cQ ≤ c') : C.a₀ ≤ c' / 12 := by
  have := Q.hcQ_src_shift.trans hc'
  have := Q.hcQ_10000.trans hc'
  linarith

/-- Combined inner-chart scale cap `min (c₀ / 2) (zScaleCapW Q.D)`. -/
noncomputable abbrev LemmaQSrcData.scaleThresh : ℝ :=
  min ((yvWitness langerChartSpec_virasoro).c₀ / 2) (zScaleCapW Q.D)

lemma LemmaQSrcData.scaleThresh_pos : 0 < Q.scaleThresh :=
  lt_min (half_pos (yvWitness langerChartSpec_virasoro).hc₀_pos) (zScaleCapW_pos Q.D)

/-- Dimensionless bootstrap scale chosen last for `CommonSource`. -/
noncomputable def LemmaQSrcData.bvChoice : ℝ :=
  min Q.bV (Real.sqrt (Q.scaleThresh / 4))

lemma LemmaQSrcData.bvChoice_pos : 0 < Q.bvChoice :=
  lt_min Q.bV_pos (Real.sqrt_pos.mpr (div_pos Q.scaleThresh_pos (by norm_num)))

lemma LemmaQSrcData.bvChoice_le : Q.bvChoice ≤ Q.bV := min_le_left _ _

lemma LemmaQSrcData.bvChoice_scaleCompat : 2 * Q.bvChoice ^ 2 ≤ Q.scaleThresh := by
  have hpos := Q.scaleThresh_pos
  have hle : Q.bvChoice ≤ Real.sqrt (Q.scaleThresh / 4) := min_le_right _ _
  have hsq : Q.bvChoice ^ 2 ≤ Q.scaleThresh / 4 := by
    calc Q.bvChoice ^ 2 ≤ (Real.sqrt (Q.scaleThresh / 4)) ^ 2 :=
          pow_le_pow_left₀ Q.bvChoice_pos.le hle 2
      _ = Q.scaleThresh / 4 := Real.sq_sqrt (div_nonneg hpos.le (by norm_num))
  linarith only [hsq, hpos]

lemma bandB1Src_nonneg_thr {A_thr c' R T : ℝ} (hA : 0 ≤ A_thr) (hc' : Q.cQ ≤ c')
    (hR_thr : A_thr ≤ R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : C.src.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) :
    0 ≤ bandB1Src C.src c' R T g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have ha := Q.a0_le hc'
  have hM_pos := Q.cardyNorm_pos hc' hg
  have hR_nn : 0 ≤ R := hA.trans hR_thr
  have hA2_nn : 0 ≤ Q.AC c' ^ 2 := sq_nonneg _
  have hu_mem := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R) hA2_nn
    (by linarith : -R ≤ 0) hT_lo hT_hi
  unfold bandB1Src
  refine mul_nonneg (mul_nonneg (inv_nonneg.mpr hR_nn) (inv_nonneg.mpr hM_pos.le)) ?_
  refine intervalIntegral.integral_nonneg hT_hi fun t ht => ?_
  have hΔ0 : virasoroDeltaChart c' 0 ≤ t := hT_lo.trans ht.1
  have hu_t := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R) hA2_nn
    (by linarith : -R ≤ 0) hΔ0 ht.2
  have hΔ_pos : 0 ≤ t :=
    (Q.deltaChart_pos hc'_pos (by rw [abs_zero]; exact hA2_nn)).le.trans hΔ0
  have hV_nn := (C.at_ ha).nonneg_V hΔ_pos
  exact mul_nonneg (by linarith [hu_t.1.2]) (mul_nonneg (hg.2.2.2 t ht.1) hV_nn)

lemma bandB2Src_nonneg_thr {A_thr c' R T : ℝ} (hA : 0 < A_thr) (hc' : Q.cQ ≤ c')
    (hR_thr : A_thr ≤ R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : C.src.IsWeaklyFeasible (c' / 12) T g)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) :
    0 ≤ bandB2Src C.src c' R g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have ha := Q.a0_le hc'
  have hM_pos := Q.cardyNorm_pos hc' hg
  have hR_pos : 0 < R := lt_of_lt_of_le hA hR_thr
  have hΔR_pos : 0 ≤ virasoroDeltaChart c' (-R) :=
    (Q.deltaChart_pos hc'_pos (by rw [abs_neg, abs_of_pos hR_pos]; exact hR_ub)).le
  unfold bandB2Src
  refine mul_nonneg (inv_nonneg.mpr hM_pos.le) ?_
  refine setIntegral_nonneg measurableSet_Ici fun t ht => ?_
  exact mul_nonneg (hg.2.2.2 t (hT_hi.trans ht)) ((C.at_ ha).nonneg_V (hΔR_pos.trans ht))

end BandHelpers

/-! ### Section 2: Uniform band bound for `C.src` -/

noncomputable def ywP0SrcThr (C : CommonSource) (A_thr : ℝ) : BandReductionParams :=
  ywBandParamsSrc C langerChartSpec_virasoro A_thr

noncomputable def bandParamsAtSrcThr (C : CommonSource) (A_thr b_R : ℝ)
    (hb_R : 0 < b_R) : BandReductionParams :=
  { ywP0SrcThr C A_thr with b := b_R, hb := hb_R }

noncomputable def uniformBandConstSrcThr (C : CommonSource) (A_thr b : ℝ) : ℝ :=
  let P := ywP0SrcThr C A_thr
  let ρ_min_lo := kappaV * b / 3
  let C_pf_lo := ρ_min_lo ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  let C_gauss5 := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
  let C_core := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  let C_sub := P.C_a * C_gauss5 / P.κ_sub
  let C_tail := C_core + C_sub + 2 * tebBandOscConst P
  let C_band_hi := tebBandOscConst P * max (P.C_τ * (2 * b ^ 2 + 1)) 1
  max C_tail C_band_hi / (C_pf_lo * ρ_min_lo)

private lemma tebBandConst_bandParamsAtSrc_le {C : CommonSource} {A_thr b b_R : ℝ}
    (hb_pos : 0 < b) (hb_R : 0 < b_R) (hb_lo : b ≤ b_R) (hb_sq_hi : b_R ^ 2 ≤ 2 * b ^ 2) :
    tebBandConst (bandParamsAtSrcThr C A_thr b_R hb_R) ≤ uniformBandConstSrcThr C A_thr b := by
  let P := ywP0SrcThr C A_thr
  have hosc_pos : 0 < tebBandOscConst P := by
    unfold tebBandOscConst
    have hb₀ : 0 < min P.c_1 (P.c_2 / 16) := lt_min P.hc_1 (div_pos P.hc_2 (by norm_num))
    have := tebOscConst_pos hb₀ (P.M + 11 / 2)
    have := P.hC_a; have := P.hC_ν
    positivity
  set ρ_min_lo : ℝ := kappaV * b / 3
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
  set C_band_hi : ℝ := tebBandOscConst P * max (P.C_τ * (2 * b ^ 2 + 1)) 1
  have hband_hi_pos : 0 < C_band_hi := by
    dsimp [C_band_hi]; exact mul_pos hosc_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hnum_hi_pos : 0 < max C_tail C_band_hi := lt_of_lt_of_le hband_hi_pos (le_max_right _ _)
  have hband_le : C_band_R ≤ C_band_hi := by
    dsimp [C_band_R, C_band_hi]
    refine mul_le_mul_of_nonneg_left (max_le_max_right 1 ?_) hosc_pos.le
    exact mul_le_mul_of_nonneg_left (by linarith only [hb_sq_hi]) P.hC_τ.le
  have hnum_le : max C_tail C_band_R ≤ max C_tail C_band_hi := max_le_max_left C_tail hband_le
  have hlhs_eq : tebBandConst (bandParamsAtSrcThr C A_thr b_R hb_R) =
      max C_tail C_band_R / (C_pf_R * ρ_min_R) := rfl
  have hrhs_eq : uniformBandConstSrcThr C A_thr b =
      max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) := rfl
  rw [hlhs_eq, hrhs_eq]
  calc max C_tail C_band_R / (C_pf_R * ρ_min_R)
      ≤ max C_tail C_band_hi / (C_pf_R * ρ_min_R) := div_le_div_of_nonneg_right hnum_le hden_R_pos.le
    _ ≤ max C_tail C_band_hi / (C_pf_lo * ρ_min_lo) := div_le_div_of_nonneg_left hnum_hi_pos.le hden_lo_pos hden_le

lemma uniform_band_boundFor_src_thr {C : CommonSource} (Q : LemmaQSrcData C)
    {A_thr b : ℝ} (hA_pos : 0 < A_thr) (hb_pos : 0 < b) (hb_le : b ≤ Q.bV)
    (hScale : 2 * b ^ 2 ≤ Q.scaleThresh)
    {c' R T : ℝ}
    (hc'_yv : ywThreshSrc C langerChartSpec_virasoro A_thr ≤ c')
    (hc'_cq : Q.cQ ≤ c')
    (hR_thr : A_thr ≤ R)
    (hR_lo : b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_hi : R + 1 ≤ chartACAt b c' ^ 2)
    {g : ℝ → ℝ} (hg_wf : C.src.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-A_thr)) :
    let M := C.src.cardyNorm (c' / 12) g
    let B₁ := bandB1Src C.src c' R T g
    let B₂ := bandB2Src C.src c' R g
    ∀ ζ ∈ stripClosed,
      kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
      ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
      c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
      ‖tildeWW C.src.w c' g ζ‖ ≤ M *
        (max (uniformBandConstSrcThr C A_thr b) 1 * (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
  dsimp only
  let pg := langerChartSpec_virasoro
  let w := yvWitness pg
  have hc'_10000 : 10000 ≤ c' := (ywThreshSrc_ge C pg A_thr).trans hc'_yv
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
  have ha := Q.a0_le hc'_cq
  have hc'_yv_base : yvThresh pg A_thr ≤ c' :=
    ywThresh_ge_yv ((le_max_left _ _).trans hc'_yv)
  have hg : TestClass C.src (c' / 12) g := hg_wf.1
  have hM_pos : 0 < C.src.cardyNorm (c' / 12) g := Q.cardyNorm_pos hc'_cq hg_wf
  have hg_nn : ∀ t ∈ Ici T, 0 ≤ g t := hg_wf.2.2.2
  have h2bV_c0 : 2 * b ^ 2 ≤ w.c₀ / 2 := hScale.trans (min_le_left _ _)
  have hACb_sq : chartACAt b c' ^ 2 = 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := chartACAt_sq b c' hc'_pos.le
  have hACb_le_AC : chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 := Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hR_le_ACb : R ≤ chartACAt b c' ^ 2 := by linarith only [hR_hi]
  have hR_le_AC : R ≤ Q.AC c' ^ 2 := hR_le_ACb.trans hACb_le_AC
  have hR_pos : 0 < R := lt_of_lt_of_le hA_pos hR_thr
  have hΔ0_eq : langerDelta pg c' 0 = virasoroDeltaChart c' 0 :=
    Q.langerDelta_eq hc'_pos (by rw [abs_zero]; exact sq_nonneg _)
  have hΔA_eq : langerDelta pg c' (-A_thr) = virasoroDeltaChart c' (-A_thr) :=
    Q.langerDelta_eq hc'_pos (by rw [abs_neg, abs_of_pos hA_pos]; exact hR_thr.trans hR_le_AC)
  have hΔR_eq : langerDelta pg c' (-R) = virasoroDeltaChart c' (-R) :=
    Q.langerDelta_eq hc'_pos (by rw [abs_neg, abs_of_pos hR_pos]; exact hR_le_AC)
  have hT_lo' : langerDelta pg c' 0 ≤ T := by rw [hΔ0_eq]; exact hT_lo
  have hT_hi' : T ≤ langerDelta pg c' (-A_thr) := by rw [hΔA_eq]; exact hT_hi
  let R_star : ℝ := (ywP0SrcThr C A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ)
  have hP0_b_sq : (ywP0SrcThr C A_thr).b ^ 2 = w.c₀ / 2 := by
    dsimp [ywP0SrcThr, ywBandParamsSrc, ywBandParams, yvBandParams]
    exact Real.sq_sqrt (div_nonneg w.hc₀_pos.le zero_lt_two.le)
  have hR_le_Rstar : R ≤ R_star := by
    dsimp [R_star]; rw [hP0_b_sq]
    calc R ≤ chartACAt b c' ^ 2 := hR_le_ACb
      _ = 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := hACb_sq
      _ ≤ (w.c₀ / 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right h2bV_c0 (Real.rpow_nonneg hc'_pos.le _)
  have hRstar_ub : R_star ≤ (ywP0SrcThr C A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := by
    dsimp [R_star]; linarith only []
  let I₀ := ywBandInstanceSrc C pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hmom₀ := ywBandInstanceSrc_moments C pg hA_pos.le hc'_yv (R := R_star) le_rfl hRstar_ub
    hT_lo' hT_hi' hg hM_pos hg_nn
  have hProps₀ := langerDelta_props hc'_yv_base (R := R_star) le_rfl hRstar_ub
  have hDelta_le : langerDelta pg c' (-R) ≤ langerDelta pg c' (-R_star) :=
    hProps₀.2.2.2.2.1.monotoneOn ⟨hR_pos.le, hR_le_Rstar⟩ ⟨hProps₀.1.le, le_rfl⟩ hR_le_Rstar
  set b_R : ℝ := Real.sqrt (R * c' ^ (-(2 / 3 : ℝ)))
  have hb_R_sq : b_R ^ 2 = R * c' ^ (-(2 / 3 : ℝ)) :=
    Real.sq_sqrt (mul_nonneg hR_pos.le (Real.rpow_nonneg hc'_pos.le _))
  have hb_R_lo : b ≤ b_R := by
    refine Real.le_sqrt_of_sq_le ?_
    calc b ^ 2 = (b ^ 2 * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
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
  let P_R : BandReductionParams := bandParamsAtSrcThr C A_thr b_R hb_R_pos
  have hρR_ub : 2 * rhoR P_R c' R ≤ 0.035 := by
    have hle : rhoR P_R c' R ≤ rhoR (ywP0SrcThr C A_thr) c' R_star := by
      unfold rhoR
      change kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R ≤
        kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R_star
      have := kappaV_pos; gcongr
    have h0_ub : 2 * rhoR (ywP0SrcThr C A_thr) c' R_star ≤ 0.035 := I₀.hρR_ub
    linarith only [hle, h0_ub]
  let I_R : BandReductionInstance P_R :=
    { c := I₀.c, ε := I₀.ε, R := R, hc := I₀.hc, hε := I₀.hε,
      hR_lb := by change b_R ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R; exact hb_R_R.le,
      hR_ub := by change R ≤ b_R ^ 2 * c' ^ (2 / 3 : ℝ) + 1; linarith only [hb_R_R],
      hρR_ub := hρR_ub,
      W_tilde := I₀.W_tilde, hW_cont := I₀.hW_cont, hW_holo := I₀.hW_holo,
      hW_symm := I₀.hW_symm, hW_bound := I₀.hW_bound,
      dmPos := I₀.dmPos, dmNeg := I₀.dmNeg,
      hdmPos_fin := I₀.hdmPos_fin, hdmNeg_fin := I₀.hdmNeg_fin,
      hdmPos_supp := I₀.hdmPos_supp, hdmNeg_supp := I₀.hdmNeg_supp, hdm_tv := I₀.hdm_tv,
      T := I₀.T, hdm_nonneg_tail := I₀.hdm_nonneg_tail,
      E_sub := I₀.E_sub, hE_sub_meas := I₀.hE_sub_meas, hE_sub_sub := I₀.hE_sub_sub,
      K_edge := I₀.K_edge, hK_meas := I₀.hK_meas, hW_edge := I₀.hW_edge, hK_sub := I₀.hK_sub,
      a_0 := I₀.a_0, a_0' := I₀.a_0', a_2 := I₀.a_2, R_0 := I₀.R_0, Phi := I₀.Phi,
      hK_factor := I₀.hK_factor, ha_2_bd := I₀.ha_2_bd, ha_0_deriv := I₀.ha_0_deriv,
      ha_0_bd := I₀.ha_0_bd, hR_0_nonpos := I₀.hR_0_nonpos, hR_0_cont := I₀.hR_0_cont,
      hR_0_even := I₀.hR_0_even, hR_0_unimodal := I₀.hR_0_unimodal, hPhi_odd := I₀.hPhi_odd,
      ν := I₀.ν, ν' := I₀.ν', invNu' := I₀.invNu',
      hν_deriv := I₀.hν_deriv, hν'_cont := I₀.hν'_cont, hν'_inv_pos := I₀.hν'_inv_pos,
      hν'_inv_deriv := I₀.hν'_inv_deriv, hinvNu'_cont := I₀.hinvNu'_cont,
      hinvNu'_int := I₀.hinvNu'_int, hinvNu'_integrable := I₀.hinvNu'_integrable,
      μ := I₀.μ, m := I₀.m, m' := I₀.m', hPhi_deriv := I₀.hPhi_deriv,
      hm_0 := I₀.hm_0, hm_cont := I₀.hm_cont, hm_strictMono := I₀.hm_strictMono,
      hm_deriv := I₀.hm_deriv, hm_step := I₀.hm_step, hm_slope := I₀.hm_slope,
      τ_0 := I₀.τ_0, hτ_0_nn := I₀.hτ_0_nn, hτ_0_eq_zero := I₀.hτ_0_eq_zero,
      hτ_0_root := I₀.hτ_0_root, u_tilde := I₀.u_tilde, Delta := I₀.Delta,
      hτ_0_below := I₀.hτ_0_below,
      hτ_0_band := fun ξ hξ => I₀.hτ_0_band ξ ⟨hξ.1, hξ.2.trans hDelta_le⟩,
      hu_tilde_int := I₀.hu_tilde_int.mono_set (Icc_subset_Icc_right hDelta_le) }
  set M := C.src.cardyNorm (c' / 12) g
  let fPos : ℝ → ℝ := fun t => max (g t) 0 * C.src.cardyV (c' / 12) t / M
  have hT_pos : 0 < T := by
    have h0 : 0 < langerDelta pg c' 0 := by rw [langerDelta_zero]; have := xiStar_pos; positivity
    exact lt_of_lt_of_le h0 hT_lo'
  have hfPos_meas : AEMeasurable fPos (volume.restrict (Ioi 0)) := bandPosSrc_aemeasurable hg
  have hfPos_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ fPos t := fun t ht => bandPosSrc_nonneg ha g (mem_Ioi.mp ht).le
  have hfPos_int : IntegrableOn fPos (Ioi 0) := bandPosSrc_integrableOn ha hg
  have hT_le_ΔR : T ≤ virasoroDeltaChart c' (-R) := by
    have hRm : -R ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
      ⟨by linarith only [hR_le_AC], by linarith only [hR_pos, sq_nonneg (Q.AC c')]⟩
    have hAm : -A_thr ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
      ⟨by linarith only [hR_thr, hR_le_AC], by linarith only [hA_pos, sq_nonneg (Q.AC c')]⟩
    exact hT_hi.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn hRm hAm (by linarith only [hR_thr]))
  have hB1_eq : bandB1 I_R = bandB1Src C.src c' R T g := by
    have hsub_Icc : Icc T (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hT_pos ht.1
    have h1 : bandB1 I_R = R⁻¹ * ∫ ξ in Icc T (langerDelta pg c' (-R)),
        (-I₀.u_tilde ξ) ∂((volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (fPos t))) := rfl
    rw [h1, setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hfPos_meas.ennreal_ofReal.restrict
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun t => -I₀.u_tilde t) measurableSet_Icc]
    change R⁻¹ * ∫ t, (ENNReal.ofReal (fPos t)).toReal • (-I₀.u_tilde t)
        ∂((volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R)))) = _
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub_Icc, hΔR_eq]
    have hcongr : EqOn (fun t => (ENNReal.ofReal (fPos t)).toReal • (-I₀.u_tilde t))
        (fun t => M⁻¹ * ((-virasoroUT c' t) * (g t * C.src.cardyV (c' / 12) t)))
        (Icc T (virasoroDeltaChart c' (-R))) := fun t ht => by
      have ht_pos : t ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (lt_of_lt_of_le hT_pos ht.1)
      dsimp only
      rw [ENNReal.toReal_ofReal (hfPos_nn t ht_pos), smul_eq_mul]
      dsimp [fPos]; rw [max_eq_left (hg_nn t ht.1)]
      have hu_t := Q.UT_between hc'_pos (by linarith only [hR_le_AC] : -(Q.AC c' ^ 2) ≤ -R)
        (sq_nonneg _) (by linarith only [hR_pos] : -R ≤ 0) (hT_lo.trans ht.1) ht.2
      have hu_abs : |virasoroUT c' t| ≤ Q.AC c' ^ 2 :=
        abs_le.mpr ⟨by linarith only [hu_t.1.1, hR_le_AC], hu_t.1.2.trans (sq_nonneg _)⟩
      have hld_eq : langerDelta pg c' (virasoroUT c' t) = t := (Q.langerDelta_eq hc'_pos hu_abs).trans hu_t.2
      have hu_star : virasoroUT c' t ∈ Icc (-R_star) 0 :=
        ⟨by linarith only [hu_t.1.1, hR_le_Rstar], hu_t.1.2⟩
      have hut_eq : I₀.u_tilde t = virasoroUT c' t := by
        have hm := hmom₀.2.1 (virasoroUT c' t) hu_star; rwa [hld_eq] at hm
      rw [hut_eq]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcongr, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT_le_ΔR, ← mul_assoc]
    rfl
  have hB2_eq : bandB2 I_R = bandB2Src C.src c' R g := by
    have h1 : bandB2 I_R = (((volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (fPos s))) (Ici (langerDelta pg c' (-R)))).toReal := rfl
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
    have hcongr : EqOn fPos (fun t => M⁻¹ * (g t * C.src.cardyV (c' / 12) t))
        (Ici (virasoroDeltaChart c' (-R))) := fun t ht => by
      dsimp [fPos]; rw [max_eq_left (hg_nn t (hT_le_ΔR.trans ht))]; ring
    rw [setIntegral_congr_fun measurableSet_Ici hcongr, integral_const_mul]; rfl
  intro ζ _ hlo hhi hre_lb
  have hζ_pos : 0 < ‖ζ‖ := lt_of_lt_of_le (by have := kappaV_pos; positivity) hlo
  have hζ_re_pos : 0 < ζ.re := lt_of_lt_of_le (by positivity) hre_lb
  have hdiv_le1 : ζ.re / ‖ζ‖ ≤ 1 := (div_le_one hζ_pos).mpr (Complex.re_le_norm ζ)
  have hdiv_ge_neg1 : -1 ≤ ζ.re / ‖ζ‖ := by
    have hnn : 0 ≤ ζ.re / ‖ζ‖ := div_nonneg hζ_re_pos.le hζ_pos.le
    linarith only [hnn]
  set ψ : ℝ := Real.arccos (ζ.re / ‖ζ‖)
  have hcos_eq_div : Real.cos ψ = ζ.re / ‖ζ‖ := Real.cos_arccos hdiv_ge_neg1 hdiv_le1
  have hcos_pos : 0 < Real.cos ψ := by rw [hcos_eq_div]; positivity
  have hcos_eq : ζ.re = ‖ζ‖ * Real.cos ψ := by rw [hcos_eq_div, mul_div_cancel₀ _ hζ_pos.ne']
  have hcos_lb : I_R.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ := by
    change c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ
    rw [hcos_eq_div, le_div_iff₀ hζ_pos]; exact hre_lb
  have hred := (teb_band_reduction I_R hlo hhi hcos_eq hcos_lb).1
  have hW_eq : ‖I_R.W_tilde ζ‖ = M⁻¹ * ‖tildeWW C.src.w c' g ζ‖ := by
    have h1 := hmom₀.1 ζ
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM_pos.le)]
  change ‖I_R.W_tilde ζ‖ ≤ tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
      (c' ^ (1 / 3 : ℝ) * (bandB1 I_R + bandB2 I_R) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ at hred
  rw [hW_eq, hB1_eq, hB2_eq] at hred
  have hmul_M := mul_le_mul_of_nonneg_left hred hM_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at hmul_M
  have hCY_le : tebBandConst P_R ≤ max (uniformBandConstSrcThr C A_thr b) 1 :=
    (tebBandConst_bandParamsAtSrc_le hb_pos hb_R_pos hb_R_lo hb_R_sq_hi).trans (le_max_left _ _)
  have hc16_le1 : c' ^ (-(1 / 6 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc'_ge1 (by norm_num)
  have hT_hi_R : T ≤ virasoroDeltaChart c' (-R) := hT_le_ΔR
  have hB1_nn := bandB1Src_nonneg_thr Q hA_pos.le hc'_cq hR_thr hR_le_AC hg_wf hT_lo hT_hi_R
  have hB2_nn := bandB2Src_nonneg_thr Q hA_pos hc'_cq hR_thr hR_le_AC hg_wf hT_le_ΔR
  have hCY_nn : 0 ≤ tebBandConst P_R := (tebBandConst_pos P_R).le
  calc ‖tildeWW C.src.w c' g ζ‖
      ≤ M * (tebBandConst P_R * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (bandB1Src C.src c' R T g + bandB2Src C.src c' R g) +
            c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) := hmul_M
    _ ≤ M * (max (uniformBandConstSrcThr C A_thr b) 1 * c' ^ (-(5 / 6 : ℝ)) *
          (c' ^ (1 / 3 : ℝ) * (bandB1Src C.src c' R T g + bandB2Src C.src c' R g) + 1) /
          Real.cos ψ) := by gcongr
    _ = M * (max (uniformBandConstSrcThr C A_thr b) 1 *
          (c' ^ (1 / 3 : ℝ) * (bandB1Src C.src c' R T g + bandB2Src C.src c' R g) + 1) *
          c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
        rw [hcos_eq_div]; field_simp [hζ_pos.ne', hζ_re_pos.ne']

/-! ### Section 3: Lemma `Z` transfer to `psiTildeSrc` (`yvInputForSrc_bvChoice`) -/

theorem yvInputForSrc_of_scaleCompat_thr {C : CommonSource} (Q : LemmaQSrcData C)
    {A_thr b : ℝ} (hA : 0 < A_thr) (hb_pos : 0 < b) (hb_le : b ≤ Q.bV)
    (hScale : 2 * b ^ 2 ≤ Q.scaleThresh) :
    ∃ C_fb c_YV : ℝ, 1 ≤ C_fb ∧ 10000 ≤ c_YV ∧
      YVInputAtForSrcThr C.src A_thr b (psiTildeSrc C.src) C_fb c_YV := by
  obtain ⟨c_Z, C_B, _, hCB_ge1, hZ⟩ :=
    lemma_Z_W_band Q.D hb_pos (hScale.trans (min_le_right _ _))
  let C_band := max (uniformBandConstSrcThr C A_thr b) 1
  let C_fac : ℝ := max 1 C.F.d⁻¹ * Q.C_rat
  let C_fb : ℝ := max 1 (C_fac * C_B * C_band)
  let c_YV : ℝ := max 10000 (max Q.cQ (max (ywThreshSrc C langerChartSpec_virasoro A_thr) c_Z))
  refine ⟨C_fb, c_YV, le_max_left _ _, le_max_left _ _, fun {c' T R} hc' hR_thr hR_lo hR_hi {g} hg hT_lo hT_hi => ?_⟩
  have hc'_10000 : 10000 ≤ c' := (le_max_left _ _).trans hc'
  have hc'_cQ : Q.cQ ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_yv : ywThreshSrc C langerChartSpec_virasoro A_thr ≤ c' :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_Z : c_Z ≤ c' :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have ha := Q.a0_le hc'_cQ
  have hAt := C.at_ ha
  have hg0 := hAt.testClass_prob hg.1
  have hM_pos : 0 < C.src.cardyNorm (c' / 12) g := Q.cardyNorm_pos hc'_cQ hg
  have hc'_prob : max 1 (max (24 * C.F.prob.totalShift) (24 * C.a₀)) ≤ c' :=
    max_le (by linarith) (max_le (Q.hcQ_prob_shift.trans hc'_cQ) (Q.hcQ_src_shift.trans hc'_cQ))
  have hM0_pos : 0 < C.F.prob.cardyNorm (c' / 12) g :=
    cardyNorm_prob_pos_of_src_pos C hc'_prob hg.1 hM_pos
  set M₀ := C.F.prob.cardyNorm (c' / 12) g
  set M_src := C.src.cardyNorm (c' / 12) g
  have hACb_le : chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 := Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hR_le_AC : R ≤ Q.AC c' ^ 2 := by linarith only [hR_hi, hACb_le]
  have hR_pos : 0 < R := lt_of_lt_of_le hA hR_thr
  have hT_le_ΔR : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [hA]⟩ (by linarith))
  have hB1_nn := bandB1Src_nonneg_thr Q hA.le hc'_cQ hR_thr hR_le_AC hg hT_lo hT_le_ΔR
  have hB2_nn := bandB2Src_nonneg_thr Q hA hc'_cQ hR_thr hR_le_AC hg hT_le_ΔR
  set B_src := bandB1Src C.src c' R T g + bandB2Src C.src c' R g
  set Λ_src : ℝ := C_band * (c' ^ (1 / 3 : ℝ) * B_src + 1)
  have hΛ_src_ge1 : 1 ≤ Λ_src := by
    have hc13 : 0 ≤ c' ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc'_pos.le _
    have hB_nn : 0 ≤ B_src := add_nonneg hB1_nn hB2_nn
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * B_src + 1 := by nlinarith [mul_nonneg hc13 hB_nn]
    exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) h1
  set fac_M : ℝ := max 1 (M_src / M₀)
  have hfac_M_ge1 : 1 ≤ fac_M := le_max_left _ _
  have hΛ'_ge1 : 1 ≤ fac_M * Λ_src := one_le_mul_of_one_le_of_one_le hfac_M_ge1 hΛ_src_ge1
  have hR_ub_Z : R + 1 ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    rwa [chartACAt_sq b c' hc'_pos.le] at hR_hi
  have h_band_prob : ∀ ζ ∈ stripClosed,
      kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
      ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
      c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
      ‖tildeWW C.F.prob.w c' g ζ‖ ≤
        M₀ * (fac_M * Λ_src * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by
    intro ζ hζ hlo hhi hre_lb
    have hsrc_bd := uniform_band_boundFor_src_thr Q hA hb_pos hb_le hScale hc'_yv hc'_cQ
      hR_thr hR_lo hR_hi hg hT_lo hT_hi ζ hζ hlo hhi hre_lb
    rw [C.F.prob_w]
    have hM_fac : M_src ≤ M₀ * fac_M := by
      have : M_src / M₀ ≤ fac_M := le_max_right _ _
      rwa [div_le_iff₀ hM0_pos, mul_comm] at this
    have hζ_pos : 0 < ‖ζ‖ := lt_of_lt_of_le (by have := kappaV_pos; positivity) hlo
    have hζ_re_pos : 0 < ζ.re := lt_of_lt_of_le (by positivity) hre_lb
    have htail_nn : 0 ≤ Λ_src * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re := by positivity
    calc ‖tildeWW C.src.w c' g ζ‖
        ≤ M_src * (Λ_src * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := hsrc_bd
      _ ≤ (M₀ * fac_M) * (Λ_src * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) :=
          mul_le_mul_of_nonneg_right hM_fac htail_nn
      _ = M₀ * (fac_M * Λ_src * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re) := by ring
  have hYV_prob := hZ hc'_Z hΛ'_ge1 hR_lo hR_ub_Z hg0 hM0_pos h_band_prob
  intro u hu_im hu_lo hu_hi hu_re
  have h_env_prob := hYV_prob u hu_im hu_lo hu_hi hu_re
  have hu_mem : u ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
    rw [mem_closedBall_zero_iff]
    exact hu_hi.trans hR_hi |>.trans hACb_le
  have hb_mem : virasoroBChart c' u ∈ closedBall (xiStar : ℂ) Q.r_1 := by
    rw [mem_closedBall_iff_norm]
    exact virasoroBChart_sub_xiStar_le_r1 Q.hr1_pos hc'_pos hu_mem
  obtain ⟨hV0_ne, hrat_u⟩ := Q.hrat_bd hc'_cQ (virasoroBChart c' u) hb_mem
  rw [← virasoroDeltaChartC_eq_b_sq u] at hV0_ne hrat_u
  have hmul := psiTildeSrc_eq_mul_prob C hV0_ne hM_pos.ne' hM0_pos.ne'
  have hM0_div_src : M₀ / M_src ≤ max 1 C.F.d⁻¹ := by
    rw [div_le_iff₀ hM_pos]
    have hge := hAt.cardyNorm_ge hg.1
    calc M₀ = C.F.d⁻¹ * (C.F.d * M₀) := by rw [← mul_assoc, inv_mul_cancel₀ C.F.hd.ne', one_mul]
      _ ≤ C.F.d⁻¹ * M_src := mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr C.F.hd.le)
      _ ≤ max 1 C.F.d⁻¹ * M_src := mul_le_mul_of_nonneg_right (le_max_right _ _) hM_pos.le
  have hcancel_M : (M₀ / M_src) * fac_M ≤ max 1 C.F.d⁻¹ := by
    rcases le_total (M_src / M₀) 1 with hle | hle
    · rw [show fac_M = 1 from max_eq_left hle, mul_one]
      exact hM0_div_src
    · calc (M₀ / M_src) * fac_M
          = (M₀ / M_src) * (M_src / M₀) := by rw [show fac_M = M_src / M₀ from max_eq_right hle]
        _ = 1 := by field_simp [hM0_pos.ne', hM_pos.ne']
        _ ≤ max 1 C.F.d⁻¹ := le_max_left _ _
  have hconst_le : (M₀ / M_src) * Q.C_rat * (C_B * (fac_M * Λ_src)) ≤
      C_fb * (c' ^ (1 / 3 : ℝ) * B_src + 1) := by
    calc (M₀ / M_src) * Q.C_rat * (C_B * (fac_M * Λ_src))
        = ((M₀ / M_src) * fac_M) * Q.C_rat * C_B * Λ_src := by ring
      _ ≤ max 1 C.F.d⁻¹ * Q.C_rat * C_B * Λ_src := by gcongr; exact Q.hC_rat.le
      _ = (C_fac * C_B * C_band) * (c' ^ (1 / 3 : ℝ) * B_src + 1) := by
          dsimp [C_fac, Λ_src]; ring
      _ ≤ C_fb * (c' ^ (1 / 3 : ℝ) * B_src + 1) := by
          gcongr
          exact le_max_right _ _
  have hre_nn : 0 ≤ (u ^ (1 / 2 : ℂ)).re := by
    have : 0 ≤ 2 * c' ^ (-(1 / 12 : ℝ)) * Real.sqrt ‖u‖ := by positivity
    linarith [hu_re]
  have h_env_nn : 0 ≤ airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) :=
    mul_nonneg (mul_nonneg (airyEnv_pos u).le (Real.rpow_nonneg hre_nn _)) (Real.rpow_nonneg (norm_nonneg _) _)
  calc ‖psiTildeSrc C.src c' g u‖
      = (M₀ / M_src) * ‖C.src.cardyVC (c' / 12) (virasoroDeltaChartC c' u) /
            cardyVC C.F.prob (c' / 12) (virasoroDeltaChartC c' u)‖ *
          ‖psiTilde C.F.prob c' g u‖ := by
        rw [hmul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hM0_pos.le hM_pos.le)]
    _ ≤ ((M₀ / M_src) * Q.C_rat) *
          (C_B * (fac_M * Λ_src) * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrat_u (div_nonneg hM0_pos.le hM_pos.le))
          h_env_prob (norm_nonneg _) (mul_nonneg (div_nonneg hM0_pos.le hM_pos.le) Q.hC_rat.le)
    _ = ((M₀ / M_src) * Q.C_rat * (C_B * (fac_M * Λ_src))) *
          (airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) := by ring
    _ ≤ (C_fb * (c' ^ (1 / 3 : ℝ) * B_src + 1)) *
          (airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_right hconst_le h_env_nn
    _ = C_fb * (c' ^ (1 / 3 : ℝ) * B_src + 1) *
          airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by ring

theorem yvInputForSrc_bvChoice {C : CommonSource} (Q : LemmaQSrcData C) :
    YVInputForSrc C.src Q.bvChoice :=
  yvInputForSrc_of_scaleCompat_thr Q virasoroAThr_pos Q.bvChoice_pos Q.bvChoice_le Q.bvChoice_scaleCompat

end FormalResearch.ModularBootstrap.Mixtures
