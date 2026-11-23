module

public import FormalResearch.ModularBootstrap.Upper.Assembly.TipExpansion
public import FormalResearch.ModularBootstrap.FixedWeight.LittleOUpper
public import FormalResearch.ModularBootstrap.Upper.Window.Quadrature

/-!
# FW-C: feasibility of the designs and the `o(c^{1/3})` upper threshold at Virasoro

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (FW-C, the proof of Theorem `Σ₀`: the
`f = 1` designs with `d` down to `0`, instead of Theorems C15/C4), `upper_transfer.tex`
(`ut:III`, `ut:V`, `ut:E`).

* `designG_isFeasible`: if `η_* ∈ (0, 1/4]` and `V_D < 0`, then for large `c` the comb functional
  `g = designG N η d c` is feasible at the gap `t_f + 1` (`IsFeasible`): `g ∈ Ā` (K7), `g_vac > 0`
  (Proposition V (ii)), `g ≥ 0` on `[t_f + 1, ∞)` (Propositions I, II);
* `threshold_le_designTf`: hence `T_V(c) ≤ t_f + 1` for large `c`;
* `exists_design_negative`: for every `d' ∈ (0, |a_1 - a_2|)` there are `N`, `η_* ∈ (0, 1/4]` with
  `V_D < 0` at shift `d'`: Lemma V/E, `V_D ≤ -d' R_1 + E_0`, `R_1 ≥ 1/2`, `E_0 ≤ C(η_*² + N^{-1/3})`;
* **`virasoro_thresholdUpperLittleO`**: `ThresholdUpperLittleOAt virasoroProblem.T_V
  virasoroProblem.totalShift` (`T_V(c) ≤ T_*(c) + δ c^{1/3}`), proved from the designs;
  `virasoro_corollary_E1_littleO_unconditional` is `virasoro_corollary_E1_littleO` with this input
  discharged.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Positivity

/-- **Feasibility of the designs at the gap `t_f + 1`.** -/
theorem designG_isFeasible (prob : FixedWeightProblem) (hw : prob.w = 1) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    (hV : windowIntegralVD N η d < 0) :
    ∀ᶠ c in atTop, 0 < designTf d c + 1 ∧
      prob.IsFeasible (c / 12) (designTf d c + 1) (designG N η d c) := by
  filter_upwards [designGood_eventually prob hw N hN hη0.le hη1 d, designG_nonneg N hN hη0 hη1 d,
    designG_gVac_pos prob hw N hN hη0.le hη1 d hV] with c hgood hpos hvac
  have htf : 0 ≤ designTf d c := by
    have := hgood.1
    unfold designTf; positivity
  exact ⟨by linarith, hgood.testClass, hvac, fun t ht => (hpos.2 t ht).le⟩

/-- `T_V(c) ≤ t_f + 1` for large `c`. -/
theorem threshold_le_designTf (prob : FixedWeightProblem) (hw : prob.w = 1) (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (d : ℝ)
    (hV : windowIntegralVD N η d < 0) :
    ∀ᶠ c in atTop, prob.T_V c ≤ designTf d c + 1 := by
  filter_upwards [designG_isFeasible prob hw N hN hη0 hη1 d hV] with c ⟨hT, hfeas⟩
  exact csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT, designG N η d c, hfeas⟩

/-- For `d ∈ (0, |a_1 - a_2|)` there is a design `D(N, η_*, d)`, `η_* ∈ (0, 1/4]`, with `V_D < 0`:
`V_D ≤ -d R_1 + E_0 ≤ -d/2 + d/4` (`lemma_V_identity`, `lemma_E`). -/
theorem exists_design_negative {d : ℝ} (hd0 : 0 < d) (hd1 : d < |airyZero 1 - airyZero 2|) :
    ∃ (N : ℕ) (η : ℝ), 1 ≤ N ∧ 0 < η ∧ η ≤ 1 / 4 ∧ windowIntegralVD N η d < 0 := by
  obtain ⟨C, hC, N₀, hN₀, hE⟩ := lemma_E
  set η : ℝ := min (1 / 4) (√(d / (8 * C))) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hη1 : η ≤ 1 / 4 := min_le_left _ _
  have hη2 : η ^ 2 ≤ d / (8 * C) := by
    have h1 : η ≤ √(d / (8 * C)) := min_le_right _ _
    calc η ^ 2 ≤ (√(d / (8 * C))) ^ 2 := pow_le_pow_left₀ hη0.le h1 2
      _ = d / (8 * C) := Real.sq_sqrt (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_ge ((8 * C / d) ^ 3)
  set N : ℕ := max N₀ M with hNdef
  have hN1 : 1 ≤ N := hN₀.trans (le_max_left _ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN3 : (8 * C / d) ^ 3 ≤ (N : ℝ) :=
    hM.trans (by exact_mod_cast le_max_right N₀ M)
  have hN13 : 8 * C / d ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have h : 8 * C / d = ((8 * C / d) ^ 3) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h]
    exact Real.rpow_le_rpow (by positivity) hN3 (by norm_num)
  have hNinv : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ d / (8 * C) := by
    rw [Real.rpow_neg hNpos.le]
    have hp : 0 < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hNpos _
    rw [← one_div, div_le_div_iff₀ hp (by positivity)]
    have := (div_le_iff₀ hd0).mp hN13
    linarith
  obtain ⟨-, -, hE0, hR1⟩ := (hE N (le_max_left _ _) η hη0.le hη1)
  obtain ⟨-, -, -, -, hVle⟩ := lemma_V_identity N η d hd0.le hd1
  refine ⟨N, η, hN1, hη0, hη1, ?_⟩
  have hE0' : designE0 N η ≤ d / 4 := by
    calc designE0 N η ≤ C * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) := hE0
      _ ≤ C * (d / (8 * C) + d / (8 * C)) := by gcongr
      _ = d / 4 := by field_simp; ring
  have hR : 1 / 2 ≤ designR1 N η := hR1.1
  unfold windowIntegralVD
  nlinarith

/-- **FW-C for every weight-one problem**: `T_V(c) ≤ T_*(c) + δ c^{1/3}` for every `δ > 0` and `c` large
(`ThresholdUpperLittleOAt`), from the `f = 1` designs `D(N, η_*, d)` with `d` small, `V_D < 0`. -/
theorem thresholdUpperLittleO_prob (prob : FixedWeightProblem) (hw : prob.w = 1) :
    ThresholdUpperLittleOAt prob.T_V prob.totalShift := by
  intro δ hδ
  have hcs := cStar_pos
  have hgap : 0 < |airyZero 1 - airyZero 2| :=
    abs_pos.mpr (sub_ne_zero.mpr (airyZero_strictAnti le_rfl).ne')
  set d : ℝ := min (δ / (2 * cStar)) (|airyZero 1 - airyZero 2| / 2) with hddef
  have hd0 : 0 < d := lt_min (by positivity) (by positivity)
  have hd1 : d < |airyZero 1 - airyZero 2| := (min_le_right _ _).trans_lt (by linarith)
  have hdc : cStar * d ≤ δ / 2 := by
    have : d ≤ δ / (2 * cStar) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨N, η, hN, hη0, hη1, hV⟩ := exists_design_negative hd0 hd1
  set R : ℝ := 1 + (kTip ^ (-(2 / 3 : ℝ))) ^ 2 * designSigma1 d 1 ^ 2 / 3 with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  obtain ⟨c₃, hc₃⟩ := eventually_atTop.1 (threshold_le_designTf prob hw N hN hη0 hη1 d hV)
  refine ⟨max (max c₃ (max 1 (12 * prob.totalShift))) ((2 * R / δ) ^ 3 + 1), ?_, fun {c} hc => ?_⟩
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · have hc3 : c₃ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
    have hc1 : 1 ≤ c := by
      have := ((le_max_left 1 (12 * prob.totalShift)).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
      linarith
    have hc4 : (2 * R / δ) ^ 3 ≤ c := by
      have := (le_max_right _ _).trans hc
      linarith
    have hc0 : 0 ≤ c := by linarith
    have ha0 : 0 ≤ c ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hc0 _
    have hcube : 2 * R / δ ≤ c ^ ((1 : ℝ) / 3) := by
      by_contra hlt
      push Not at hlt
      have h3 : (c ^ ((1 : ℝ) / 3)) ^ 3 < (2 * R / δ) ^ 3 :=
        pow_lt_pow_left₀ hlt ha0 (by norm_num)
      rw [rpow_third_cube (by linarith)] at h3
      linarith
    have hRle : R ≤ δ / 2 * c ^ ((1 : ℝ) / 3) := by
      have := (div_le_iff₀ hδ).mp hcube
      linarith
    have h1 := hc₃ c hc3
    have h2 := designTf_add_one_le hc1 d
    have h3 : cStar * d * c ^ ((1 : ℝ) / 3) ≤ δ / 2 * c ^ ((1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hdc ha0
    linarith

/-- **FW-C at Virasoro**: `T_V(c) ≤ T_*(c) + δ c^{1/3}` for every `δ > 0` and `c` large
(`ThresholdUpperLittleOAt`), from the `f = 1` designs `D(N, η_*, d)` with `d` small, `V_D < 0`. -/
theorem virasoro_thresholdUpperLittleO :
    ThresholdUpperLittleOAt virasoroProblem.T_V virasoroProblem.totalShift :=
  thresholdUpperLittleO_prob virasoroProblem rfl

/-- **Virasoro, Corollary E1 with the `o(c^{1/3})` upper bound, unconditional**: the input
`ThresholdUpperLittleOAt` of `virasoro_corollary_E1_littleO` is discharged by the designs. -/
theorem virasoro_corollary_E1_littleO_unconditional :
    ∃ c₀ D : ℝ, 24 ≤ c₀ ∧ 0 ≤ D ∧
      (∀ {c' : ℝ}, c₀ ≤ c' →
        0 < virasoroProblem.T_V c' ∧
        ∃ meas : AdmissibleCrossingMeasure virasoroProblem (c' / 12),
          meas.ν (Iio (virasoroProblem.T_V c')) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V c' + ε))) ∧
          virasoroProblem.Delta_best c' = c' / 12 + virasoroProblem.T_V c') ∧
      (∀ δ : ℝ, 0 < δ → ∃ c₁ : ℝ, ∀ {c' : ℝ}, c₁ ≤ c' →
        |virasoroProblem.T_V c' - TStar c'| ≤ D + δ * c' ^ ((1 : ℝ) / 3) ∧
        |virasoroProblem.Delta_best c' - (c' / lambdaV + Aopt * c' ^ ((1 : ℝ) / 3))| ≤
          D + δ * c' ^ ((1 : ℝ) / 3)) ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (virasoroProblem.T_V (cSeq j) - TStar (cSeq j)) /
          (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) :=
  virasoro_corollary_E1_littleO virasoro_thresholdUpperLittleO

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designG_isFeasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designG_isFeasible

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.threshold_le_designTf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threshold_le_designTf

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.exists_design_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_design_negative

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.thresholdUpperLittleO_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thresholdUpperLittleO_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_thresholdUpperLittleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_thresholdUpperLittleO

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_corollary_E1_littleO_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_corollary_E1_littleO_unconditional

end FormalResearch.ModularBootstrap.Upper.Assembly
