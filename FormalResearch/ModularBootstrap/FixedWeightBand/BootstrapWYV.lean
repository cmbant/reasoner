module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWYVBand

/-!
# Band-Feedback Input at Weight `w` from Proposition `Y_V` and Lemma `Z` (`vlo:YV`, `vlo:Z`, `vlo:L`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, §J8, §J9.

* `LemmaQData.yvInputForW_of_scaleCompat`: for `0 < b ≤ b_V` with `2 b² ≤ scaleThresh`
  (`min (c₀/2) (zScaleCapW D)`), the band-feedback input `YVInputForW prob b` holds with
  `C_fb = C_B max(C_{Y,unif}(b), 1)`: the uniform band bound (`uniform_band_boundForW`, from
  `proposition_YV_W`'s instance `ywBandInstance`) feeds Lemma `Z` at weight `w`
  (`lemma_Z_W_band`, from Lemma `D'` at weight `w`); no hypothesis remains.
* `LemmaQData.bvChoice`: the scale `min b_V √(scaleThresh/4)` chosen last (`vlo:order`), and
  `LemmaQData.yvInputForW_bvChoice`.
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

theorem LemmaQData.yvInputForW_of_scaleCompat (Q : LemmaQData prob) {b : ℝ} (hb_pos : 0 < b)
    (hb_le : b ≤ Q.bV) (hScale : 2 * b ^ 2 ≤ Q.scaleThresh) : YVInputForW prob b := by
  obtain ⟨c_Z, C_B, _hc_Z_ge, hC_B_ge1, hZ⟩ :=
    lemma_Z_W_band Q.D hb_pos (hScale.trans (min_le_right _ _))
  set C_Y1 : ℝ := max (uniformBandConstW prob b) 1
  have hCY1_ge1 : 1 ≤ C_Y1 := le_max_right _ _
  obtain ⟨C_fb, hC_fb_eq⟩ : ∃ x : ℝ, x = C_B * C_Y1 := ⟨_, rfl⟩
  obtain ⟨c_YV, hc_YV_eq⟩ : ∃ x : ℝ,
    x = max Q.cQ (max (ywThresh prob langerChartSpec_virasoro virasoroAThr) c_Z) := ⟨_, rfl⟩
  have hC_fb_ge1 : 1 ≤ C_fb := by rw [hC_fb_eq]; nlinarith only [hC_B_ge1, hCY1_ge1]
  have hc_YV_cq : Q.cQ ≤ c_YV := hc_YV_eq ▸ le_max_left _ _
  refine ⟨C_fb, c_YV, hC_fb_ge1, Q.hcQ_10000.trans hc_YV_cq, ?_⟩
  intro c' T R hc' hR_thr hR_lo hR_hi g hg_wf hT_lo hT_hi
  have hc'_cq : Q.cQ ≤ c' := hc_YV_cq.trans hc'
  have hc'_yv : ywThresh prob langerChartSpec_virasoro virasoroAThr ≤ c' :=
    (hc_YV_eq ▸ (le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_Z : c_Z ≤ c' :=
    (hc_YV_eq ▸ (le_max_right _ _).trans (le_max_right _ _)).trans hc'
  have hc'_pos : 0 < c' :=
    lt_of_lt_of_le (by have := Q.hcQ_10000; linarith only [this]) hc'_cq
  have hM_pos : 0 < prob.cardyNorm (c' / 12) g := Q.cardyNorm_pos hc'_cq hg_wf
  have hR_hi_Z : R + 1 ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    rwa [← chartACAt_sq b c' hc'_pos.le]
  have hR_le_AC : R ≤ Q.AC c' ^ 2 :=
    (by linarith only [hR_hi] : R ≤ chartACAt b c' ^ 2).trans
      (Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le)
  have hB1_nn := bandB1W_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_lo hT_hi
  have hB2_nn := bandB2W_nonneg hc'_cq hR_thr hR_le_AC hg_wf hT_hi
  set Λ : ℝ := C_Y1 * (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1)
  have hΛ_ge1 : 1 ≤ Λ := by
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1 := by
      have hnn : 0 ≤ c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) := by
        positivity
      linarith only [hnn]
    dsimp [Λ]
    nlinarith only [hCY1_ge1, h1]
  have hband := uniform_band_boundForW hb_pos hb_le hScale hc'_yv hc'_cq hR_thr hR_lo hR_hi
    hg_wf hT_lo hT_hi
  have henv := hZ hc'_Z hΛ_ge1 hR_lo hR_hi_Z hg_wf.1 hM_pos hband
  have hL_eq : C_B * Λ =
      C_fb * (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1) := by
    rw [hC_fb_eq]; dsimp [Λ]; ring
  rwa [← hL_eq]

namespace LemmaQData

variable (Q : LemmaQData prob)

/-- The dimensionless bootstrap scale chosen last (`vlo:order`): inside the chart cap `b_V` and the
strip/contour cap `scaleThresh` (the Virasoro `virasoroBVChoice`). -/
noncomputable def bvChoice : ℝ := min Q.bV (Real.sqrt (Q.scaleThresh / 4))

lemma bvChoice_pos : 0 < Q.bvChoice :=
  lt_min Q.bV_pos (Real.sqrt_pos.mpr (div_pos Q.scaleThresh_pos (by norm_num)))

lemma bvChoice_le : Q.bvChoice ≤ Q.bV := min_le_left _ _

lemma bvChoice_scaleCompat : 2 * Q.bvChoice ^ 2 ≤ Q.scaleThresh := by
  have hpos := Q.scaleThresh_pos
  have hle : Q.bvChoice ≤ Real.sqrt (Q.scaleThresh / 4) := min_le_right _ _
  have hsq : Q.bvChoice ^ 2 ≤ Q.scaleThresh / 4 := by
    calc Q.bvChoice ^ 2 ≤ (Real.sqrt (Q.scaleThresh / 4)) ^ 2 :=
          pow_le_pow_left₀ Q.bvChoice_pos.le hle 2
      _ = Q.scaleThresh / 4 := Real.sq_sqrt (div_nonneg hpos.le (by norm_num))
  linarith only [hsq, hpos]

/-- **Unconditional band-feedback input at weight `w`** (`vlo:YV`, `vlo:Z`, `vlo:L`) at the scale
`bvChoice`. -/
theorem yvInputForW_bvChoice : YVInputForW prob Q.bvChoice :=
  Q.yvInputForW_of_scaleCompat Q.bvChoice_pos Q.bvChoice_le Q.bvChoice_scaleCompat

end LemmaQData

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.yvInputForW_bvChoice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.yvInputForW_bvChoice

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.yvInputForW_of_scaleCompat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.yvInputForW_of_scaleCompat

end FormalResearch.ModularBootstrap.FixedWeightBand
